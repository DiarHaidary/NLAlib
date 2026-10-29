/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Exact
public import NLAlibScaffold.Krylov.LinearSystems.CGTridiagonal

/-!
# The conjugate gradient program

The Hestenes–Stiefel conjugate gradient method from $\mathbf{x}_0 = \mathbf{0}$ as a program, in
the order of `NLAlib.cgStep`: from $\mathbf{x}$, $\mathbf{r}$, $\mathbf{p}$ and
$\nu = \|\mathbf{r}\|^2$ (computed),
$$\mathbf{s} \leftarrow \mathbf{A}\mathbf{p},\quad \mu \leftarrow \mathbf{p}^{\mathsf{H}}\mathbf{s}\
(\texttt{dot}),\quad \gamma \leftarrow \nu/\mu,\quad
\mathbf{x} \leftarrow \mathbf{x} + \gamma\mathbf{p},\quad
\mathbf{r} \leftarrow \mathbf{r} - \gamma\mathbf{s}\ (\texttt{axpy}),$$
$$\nu' \leftarrow \mathbf{r}^{\mathsf{H}}\mathbf{r}\ (\texttt{dot}),\quad
\delta \leftarrow \nu'/\nu,\quad
\mathbf{p}' \leftarrow \mathbf{r};\ \mathbf{p}' \leftarrow \delta\mathbf{p} + \mathbf{p}'\
(\texttt{copy}, \texttt{axpy}),\quad \nu \leftarrow \nu' .$$
The stopping test is the exact comparison $\nu = 0$ before each step: the run stops when the
computed squared residual norm is exactly zero, and the remaining output cells are written $0$
(the junk values $0^{-1} = 0$ of `NLAlib.cgStep`). There is no test on $\mu$: in the standard
model $\mu > 0$ at every step taken is a theorem under a smallness hypothesis
(`NLAlib.CGRun.norm_r_le_two_mul_norm_p`, `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`).
The product is a parameter `mv`, an oracle call (`NLAlib.cgProg`) or `gemv` on a stored matrix
(`NLAlib.cgDenseProg`). Memory: five slots of length $N$ ($\mathbf{x}$, $\mathbf{r}$,
$\mathbf{s}$ and two rotating direction slots) and seven scalars.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§1).

## Main definitions

* `NLAlib.cgStepWith`, `NLAlib.cgProgWith`, `NLAlib.cgProg`, `NLAlib.cgDenseProg`.

## Main results

* `NLAlib.exec_cgProg_exactInterp`: in exact arithmetic the program computes `NLAlib.cgState`.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

open Computation Builder

variable {P ι VB VI : Type}

/-- **One conjugate gradient step** with the product `mv W src dst`: slots of `W` at $0$
($\mathbf{x}$), $N$ ($\mathbf{r}$), $2N$ ($\mathbf{s}$), `pc` (the current direction) and `pn`
(the next one); scalars `sc[0]` $= \nu$, `sc[1]` $= \mu$, `sc[2]` $= \gamma$, `sc[4]` $= \nu'$,
`sc[5]` $= \delta$, `sc[6]` $= -\gamma$. Writes $\gamma$, $\delta$, $\nu'$ into the three output
cells. -/
def cgStepWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N : IExp VI) (W : VB) (pc pn : IExp VI) (sc : VB)
    (gamCell delCell nuCell : Cell VB VI) : Builder P ι VB VI Unit := do
  mv W pc (2 * N)
  dot p ⟨sc, 1⟩ W pc W (2 * N) N
  ins (.bin p .div ⟨sc, 2⟩ ⟨sc, 0⟩ ⟨sc, 1⟩)
  ins (.copy p gamCell ⟨sc, 2⟩)
  axpy p ⟨sc, 2⟩ W pc W 0 N
  ins (.un p .neg ⟨sc, 6⟩ ⟨sc, 2⟩)
  axpy p ⟨sc, 6⟩ W (2 * N) W N N
  dot p ⟨sc, 4⟩ W N W N N
  ins (.bin p .div ⟨sc, 5⟩ ⟨sc, 4⟩ ⟨sc, 0⟩)
  ins (.copy p delCell ⟨sc, 5⟩)
  copyv p W N W pn N
  axpy p ⟨sc, 5⟩ W pc W pn N
  ins (.copy p ⟨sc, 0⟩ ⟨sc, 4⟩)
  ins (.copy p nuCell ⟨sc, 0⟩)

/-- **Conjugate gradients**, $q$ steps from $\mathbf{x}_0 = \mathbf{0}$, product `mv`: input
$\mathbf{b}$ (buffer `b`), outputs $\mathbf{x}_k$ (`X`), $\gamma_0, \dots, \gamma_{q-1}$ (`gam`),
$\delta_0, \dots, \delta_{q-1}$ (`del`) and $\nu_0, \dots, \nu_q$ (`nu`). A step whose computed
$\nu$ is exactly $0$ is skipped and writes zeros. -/
def cgProgWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N q : IExp VI) (b X gam del nu : VB) : Builder P ι VB VI Unit := do
  let W ← alloc p (5 * N)
  let sc ← alloc p 7
  ins (.lit p ⟨sc, 3⟩ 0)
  forRange N fun i => ins (.lit p ⟨W, .var i⟩ 0)
  copyv p b 0 W N N
  copyv p b 0 W (3 * N) N
  dot p ⟨sc, 0⟩ b 0 b 0 N
  ins (.copy p ⟨nu, 0⟩ ⟨sc, 0⟩)
  forRange q fun j =>
    ifThenElse p .eq ⟨sc, 0⟩ ⟨sc, 3⟩
      (do
        ins (.lit p ⟨gam, .var j⟩ 0)
        ins (.lit p ⟨del, .var j⟩ 0)
        ins (.lit p ⟨nu, .var j + 1⟩ 0))
      (cgStepWith mv p N W (3 * N + N * (.var j % 2)) (3 * N + N * ((.var j + 1) % 2)) sc
        ⟨gam, .var j⟩ ⟨del, .var j⟩ ⟨nu, .var j + 1⟩)
  copyv p W 0 X 0 N

/-- **Matrix-free conjugate gradients**: the product is one oracle call of `o`. -/
def cgProg (p : P) (o : ι) (N q : IExp VI) (b X gam del nu : VB) : Builder P ι VB VI Unit :=
  cgProgWith (fun W src dst => stmt (.apply o p W dst W src 1)) p N q b X gam del nu

/-- **Dense conjugate gradients**: the product is `gemv` on the $N \times N$ matrix stored
column-major in buffer `A`. -/
def cgDenseProg (p : P) (N q : IExp VI) (A b X gam del nu : VB) : Builder P ι VB VI Unit :=
  cgProgWith (fun W src dst => gemv p N N A 0 W src W dst) p N q b X gam del nu

variable [DecidableEq P] {𝕜 : Type} [RCLike 𝕜]

/-- **The conjugate gradient program computes the Hestenes–Stiefel recurrence** in exact
arithmetic: for positive definite $\mathbf{A}$ and every $\mathbf{b}$, the run succeeds,
`X` holds $\mathbf{x}_q$ of `NLAlib.cgState A b 0` (which is `NLAlib.cgIterate A b 0 q`,
`Matrix.PosDef.cgState_x_eq`), `gam[j]` $= \gamma_j$ (`NLAlib.cgAlpha`), `del[j]` $=
\|\mathbf{r}_{j+1}\|^2/\|\mathbf{r}_j\|^2$ and `nu[j]` $= \|\mathbf{r}_j\|^2$. Past the grade the
recurrence is frozen at the solution and the program skips, both writing $0$.
[HestenesStiefel1952, (3:1)].
Proof: loop invariant over the five slots (the rotation of the direction slots as in
`NLAlib.exec_lanczosBasisProg_exactInterp`); the division by $\mu = \mathbf{p}^{\mathsf{H}}
\mathbf{A}\mathbf{p} > 0$ succeeds because $\mathbf{p}_j \ne \mathbf{0}$ whenever
$\mathbf{r}_j \ne \mathbf{0}$ (`CGRecurrence.lean`, private `r_eq_zero_of_p_eq_zero`).
Difficulty: moderate (about 600 lines, mostly store bookkeeping). -/
theorem exec_cgProg_exactInterp (p : P) (o : ι) {N : ℕ} (q : ℕ)
    {A : Matrix (Fin N) (Fin N) 𝕜} (hA : A.PosDef) (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (cgProg p o (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
          Array.replicate q none, Array.replicate q none, Array.replicate (q + 1) none]) =
        some st' ∧
      (∀ i : Fin N, st'.store.read p 1 i = some ((cgState A b 0 q).x i)) ∧
      (∀ j < q, st'.store.read p 2 j = some (cgAlpha A (cgState A b 0 j) : 𝕜)) ∧
      (∀ j < q, st'.store.read p 3 j =
        some ((‖WithLp.toLp 2 (cgState A b 0 (j + 1)).r‖ ^ 2 /
          ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 : ℝ) : 𝕜)) ∧
      (∀ j ≤ q, st'.store.read p 4 j =
        some ((‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 : ℝ) : 𝕜)) := by
  sorry

end NLAlib
