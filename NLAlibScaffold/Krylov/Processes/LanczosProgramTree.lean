/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS
public import NLAlib.Computation.Exact
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# The Lanczos program

The symmetric Lanczos process as a program, in Paige's ordering A(1) [Paige1976], the order of
`NLAlib.lanczosStep`: from $\mathbf{v}_j$ (slot `cur`), $\mathbf{v}_{j-1}$ (slot `prev`) and
$\beta_{j-1}$,
$$\mathbf{u} \leftarrow \mathbf{H}\mathbf{v}_j,\quad
\mathbf{w} \leftarrow \mathbf{u} - \beta_{j-1}\mathbf{v}_{j-1}\ (\texttt{axpy}),\quad
\alpha_j \leftarrow \mathbf{v}_j^{\mathsf{H}}\mathbf{w}\ (\texttt{dot}),\quad
\mathbf{z} \leftarrow \mathbf{w} - \alpha_j\mathbf{v}_j\ (\texttt{axpy}),$$
$$s \leftarrow \mathbf{z}^{\mathsf{H}}\mathbf{z}\ (\texttt{dot}),\quad \beta_j \leftarrow \sqrt{s},
\quad \mathbf{v}_{j+1} \leftarrow \mathbf{z}/\beta_j\ (\texttt{rscl, one division per entry})
\text{ unless } \beta_j = 0 .$$
All of $\mathbf{u}, \mathbf{w}, \mathbf{z}, \mathbf{v}_{j+1}$ live in one slot; three slots of
length $N$ rotate ($j \bmod 3$). The breakdown test is the exact comparison $\beta_j = 0$ (the
test `if z_j = 0` of [Chen, Algorithm 1]); on breakdown
the slot keeps $\mathbf{z}$ (which is then $\mathbf{0}$ in exact and in standard-model
arithmetic) and the loop continues, so every later output is $0$, as in the library's total
recursion `NLAlib.lanczosState` (junk value $0^{-1} = 0$). The matrix-vector product is a
parameter `mv`: an oracle call (`NLAlib.lanczosBasisProg`, the matrix-free model) or the `gemv`
kernel on a stored matrix (`NLAlib.lanczosBasisDenseProg`).

The program body is the one of `docs/design/Computation.md` §5 (D15), with the product
abstracted and the basis written to $N(q+1)$ cells (the next vector too, which the stability
analysis needs). Design: `docs/design/Krylov-LanczosRounding.md` (§1).

## Main definitions

* `NLAlib.lanczosStepWith`, `NLAlib.lanczosInit`, `NLAlib.lanczosBasisProgWith`.
* `NLAlib.lanczosBasisProg`, `NLAlib.lanczosBasisDenseProg`.

## Main results

* `NLAlib.exec_lanczosBasisProg_exactInterp`: in exact arithmetic the program computes
  `NLAlib.lanczosState`.
-/

@[expose] public section

namespace NLAlib

open Computation Builder

variable {P ι VB VI : Type}

/-- **One Lanczos step** from slot `cur` (the previous vector in slot `prev`, $\beta_{j-1}$ in
`s[1]`, a literal zero in `s[3]`) into slot `nxt`, with the matrix-vector product `mv W src dst`:
writes $\alpha_j$ into `alphaCell`, $\beta_j$ into `betaCell` and into `s[1]`, and
$\mathbf{v}_{j+1}$ into slot `nxt` (left unnormalised when $\beta_j$ computes to $0$). -/
def lanczosStepWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N : IExp VI) (W : VB) (cur prev nxt : IExp VI) (s : VB) (alphaCell betaCell : Cell VB VI) :
    Builder P ι VB VI Unit := do
  mv W cur nxt
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 1⟩)
  axpy p ⟨s, 0⟩ W prev W nxt N
  dot p ⟨s, 0⟩ W cur W nxt N
  ins (.un p .re ⟨s, 0⟩ ⟨s, 0⟩)
  ins (.copy p alphaCell ⟨s, 0⟩)
  ins (.un p .neg ⟨s, 0⟩ ⟨s, 0⟩)
  axpy p ⟨s, 0⟩ W cur W nxt N
  dot p ⟨s, 2⟩ W nxt W nxt N
  ins (.un p .sqrt ⟨s, 1⟩ ⟨s, 2⟩)
  ins (.copy p betaCell ⟨s, 1⟩)
  ifThenElse p .eq ⟨s, 1⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 1⟩ W nxt N)

/-- **The start**: slot 0 holds $\mathbf{b}/\|\mathbf{b}\|$ (computed as `dot`, `sqrt`, `rscl`;
$\mathbf{b}$ itself if $\|\mathbf{b}\|$ computes to $0$), slot 2 holds zero,
`s[1]` $= \beta_0 = 0$ and `s[3]` $= 0$. -/
def lanczosInit (p : P) (N : IExp VI) (b : VB) (W s : VB) : Builder P ι VB VI Unit := do
  ins (.lit p ⟨s, 3⟩ 0)
  forRange N fun i => ins (.lit p ⟨W, 2 * N + .var i⟩ 0)
  copyv p b 0 W 0 N
  dot p ⟨s, 2⟩ b 0 b 0 N
  ins (.un p .sqrt ⟨s, 2⟩ ⟨s, 2⟩)
  ifThenElse p .eq ⟨s, 2⟩ ⟨s, 3⟩ (pure ()) (rscl p ⟨s, 2⟩ W 0 N)
  ins (.lit p ⟨s, 1⟩ 0)

/-- **Lanczos with the basis**, $q$ steps, product `mv`: inputs $\mathbf{b}$ (buffer `b`),
outputs $\alpha_1, \dots, \alpha_q$ (`alpha`), $\beta_1, \dots, \beta_q$ (`beta`) and
$\mathbf{v}_1, \dots, \mathbf{v}_{q+1}$ (`Q`, $N \times (q + 1)$ column-major); memory $3N + 4$
besides the inputs and outputs. -/
def lanczosBasisProgWith (mv : VB → IExp VI → IExp VI → Builder P ι VB VI Unit) (p : P)
    (N q : IExp VI) (b alpha beta Q : VB) : Builder P ι VB VI Unit := do
  let W ← alloc p (3 * N)
  let s ← alloc p 4
  lanczosInit p N b W s
  forRange q fun j => do
    copyv p W (N * (.var j % 3)) Q (N * .var j) N
    lanczosStepWith mv p N W (N * (.var j % 3)) (N * ((.var j + 2) % 3))
      (N * ((.var j + 1) % 3)) s ⟨alpha, .var j⟩ ⟨beta, .var j⟩
  copyv p W (N * (q % 3)) Q (N * q) N

/-- **Matrix-free Lanczos with the basis**: the product is one oracle call of `o`. -/
def lanczosBasisProg (p : P) (o : ι) (N q : IExp VI) (b alpha beta Q : VB) :
    Builder P ι VB VI Unit :=
  lanczosBasisProgWith (fun W src dst => stmt (.apply o p W dst W src 1)) p N q b alpha beta Q

/-- **Dense Lanczos with the basis**: the product is `gemv` on the $N \times N$ matrix stored
column-major in buffer `H`. -/
def lanczosBasisDenseProg (p : P) (N q : IExp VI) (H b alpha beta Q : VB) :
    Builder P ι VB VI Unit :=
  lanczosBasisProgWith (fun W src dst => gemv p N N H 0 W src W dst) p N q b alpha beta Q

variable {𝕜 : Type} [RCLike 𝕜] [DecidableEq P]

/-- **The Lanczos program computes the Lanczos recurrence** in exact arithmetic, for every
square $\mathbf{A}$ and $\mathbf{b}$ (no symmetry, no breakdown hypothesis): the run succeeds,
`alpha[j]` $= \alpha_j$ and `beta[j]` $= \beta_{j+1}$ of `NLAlib.lanczosState` (0-based, as the
library indexes it), and `Q` holds `NLAlib.lanczosMatrix A b (q + 1)`. With
`Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix` this is the Krylov basis. The counts and
memory (`docs/design/Computation.md` §6) join when the statement becomes a registered
`MatrixFree` target. [Paige1976], [Saad2011, §6.6]. -/
theorem exec_lanczosBasisProg_exactInterp (p : P) (o : ι) {N : ℕ} (q : ℕ)
    (A : Matrix (Fin N) (Fin N) 𝕜) (b : Fin N → 𝕜) (ξ : Dist → ℕ → ℝ) :
    ∃ st', exec (exactInterp (fun _ => A) ξ)
        (lanczosBasisProg p o (.const N) (.const q) 0 1 2 3).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate q none,
          Array.replicate q none, Array.replicate (N * (q + 1)) none]) = some st' ∧
      (∀ j < q, st'.store.read p 1 j = some (lanczosAlpha A (lanczosState A b j) : 𝕜)) ∧
      (∀ j < q, st'.store.read p 2 j = some ((lanczosState A b (j + 1)).beta : 𝕜)) ∧
      Holds st'.store p 3 0 (lanczosMatrix A b (q + 1)) := by
  sorry

end NLAlib
