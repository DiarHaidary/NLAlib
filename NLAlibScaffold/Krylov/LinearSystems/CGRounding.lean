/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Matrix.Norms.Compare
public import NLAlibScaffold.Krylov.FinitePrecision.CGBackward
public import NLAlibScaffold.Krylov.LinearSystems.CGProgramTree

/-!
# Rounding errors of the conjugate gradient program

A run of `NLAlib.cgProg` (matrix-free) or `NLAlib.cgDenseProg` (stored matrix) in the standard
model, for a symmetric $\mathbf{A}$ with spectrum in $[a, a']$, $a > 0$, $\kappa = a'/a$, and
$q^3\varepsilon\kappa^2 \le 10^{-5}$, **succeeds**, and its outputs are those of an
`NLAlib.CGRun` with accuracy parameter $\varepsilon = \max(\varepsilon_{\mathrm{mv}},
\gamma_{N+2}(u))$; the number of steps $k$ is read off the outputs (the first $j$ with
$\nu_j = 0$, else $q$). The only partial operations are the two divisions: by $\nu_j$, which is
tested, and by $\mu_j$, which is positive at every step taken by the a priori analysis
(`NLAlib.CGRun.norm_r_le_two_mul_norm_p` on the prefix run and
`NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`). So the bridge is proved by induction over
the iterations, interleaved with the analysis of the prefix.

The kernels give the clauses of `NLAlib.CGRun`: the product from `NLAlib.Computation.IsMatvecErr`
(oracle) or `gemv` and `NLAlib.norm_toLp_map_abs_mulVec_abs_le` (dense,
$\varepsilon_{\mathrm{mv}} = \sqrt{N}\gamma_N$), $\nu_j$ from the product form of `dot`
($\gamma_N$), $\mu_j$ from `dot` and Cauchy–Schwarz ($\gamma_N$), the two divisions ($u$), the
three updates from `axpy` ($\gamma_2$; the direction update as `copy` then `axpy`).

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§2).

## Main definitions

* `NLAlib.cgSteps`, `NLAlib.cgRoundingEps`, `NLAlib.CGOutputs`, `NLAlib.HasCGRunOutputs`,
  `NLAlib.HasCGBackwardModel`.

## Main results

* `NLAlib.Computation.IsRelErrSem.exists_cgRun_of_cgProg`: the matrix-free bridge.
* `NLAlib.cgProg_matrixFreeRounded`: the same in the access model.
* `NLAlib.Computation.IsRelErrSem.exists_cgRun_of_cgDenseProg`: the dense bridge.
* `NLAlib.Computation.IsRelErrSem.exists_cgBackwardModel_of_cgDenseProg`: end to end.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Builder

/-- **The number of steps taken**, from the computed squared residual norms $\nu_0, \dots,
\nu_q$: the first $j < q$ with $\nu_j = 0$, else $q$. -/
noncomputable def cgSteps (ν : ℕ → ℝ) (q : ℕ) : ℕ := by
  classical
  exact if h : ∃ j, j < q ∧ ν j = 0 then Nat.find h else q

/-- **The accuracy parameter of the conjugate gradient program**:
$\varepsilon = \max(\varepsilon_{\mathrm{mv}}, \gamma_{N+2}(u))$, the matvec accuracy and the bound
of the other kernels ($u$, $\gamma_2$, $\gamma_N$). -/
noncomputable def cgRoundingEps (N : ℕ) (u εmv : ℝ) : ℝ :=
  max εmv (roundingFactor (N + 2) u)

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- **The outputs of the conjugate gradient program**: buffer `X` holds $N$ words decoding to
$\mathbf{x}$, `gam`, `del` hold $\gamma_j$, $\delta_j$ ($j < q$) and `nu` holds $\nu_j$
($j \le q$). -/
def CGOutputs (st : St P K C) (p : P) (dec : P → K → ℝ) (X gam del nu : ℕ) {N : ℕ} (q : ℕ)
    (x : Fin N → ℝ) (γ δ ν : ℕ → ℝ) : Prop :=
  (∀ i : Fin N, ∃ w, st.store.read p X i = some w ∧ dec p w = x i) ∧
  (∀ j < q, ∃ w, st.store.read p gam j = some w ∧ dec p w = γ j) ∧
  (∀ j < q, ∃ w, st.store.read p del j = some w ∧ dec p w = δ j) ∧
  (∀ j ≤ q, ∃ w, st.store.read p nu j = some w ∧ dec p w = ν j)

/-- **The outputs of a conjugate gradient run form a `NLAlib.CGRun`**: the outputs decode to
$\mathbf{x}, \gamma, \delta, \nu$; with $k$ = `NLAlib.cgSteps ν q`, the outputs after the stop
are $0$; and there is a run `C : NLAlib.CGRun N k` with matrix $\mathbf{A}$, right-hand side
$\mathbf{b}$, accuracy parameter $\varepsilon$, the computed coefficients and squared residual
norms, the output iterate $\mathbf{x} = \mathbf{x}_k$, and $\mathbf{r}_k = \mathbf{0}$ if the run
stopped. -/
def HasCGRunOutputs (st : St P K C) (p : P) (dec : P → K → ℝ) (ε : ℝ) (X gam del nu : ℕ)
    {N : ℕ} (q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) : Prop :=
  ∃ (x : Fin N → ℝ) (γ δ ν : ℕ → ℝ), CGOutputs st p dec X gam del nu q x γ δ ν ∧
    (∀ j, cgSteps ν q ≤ j → j < q → γ j = 0 ∧ δ j = 0 ∧ ν (j + 1) = 0) ∧
    ∃ R : CGRun N (cgSteps ν q), R.A = A ∧ R.b = b ∧ R.ε = ε ∧
      (∀ j < cgSteps ν q, R.γ j = γ j ∧ R.δ j = δ j) ∧
      (∀ j ≤ cgSteps ν q, R.ν j = ν j) ∧ R.x (cgSteps ν q) = x ∧
      (cgSteps ν q < q → R.r (cgSteps ν q) = 0)

/-- **The matrix-free conjugate gradient program in the standard model**: under
`NLAlib.Computation.IsRelErrSem` (every value in range) and adding zero exactly, an oracle
accurate to $\varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2$, $\mathbf{A}$ symmetric with spectrum in
$[a, a']$, $a > 0$, $\mathbf{b} \ne \mathbf{0}$ (decoded), $q \ge 1$, $(N + 2)u_p < 1$ and
$q^3\varepsilon\kappa^2 \le 10^{-5}$ for $\varepsilon = \max(\varepsilon_{\mathrm{mv}},
\gamma_{N+2})$, the run of $q$ steps **succeeds** and its outputs form a run
`C : NLAlib.CGRun N k` (`NLAlib.HasCGRunOutputs`); in particular every computed curvature
$\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j$ is positive.
[HestenesStiefel1952, (3:1)]; [Higham2002, §§2.2, 3.1, Lemma 3.3].
Proof: loop invariant "after $m$ iterations the state decodes to `C.take (min m k)`"; the step
lemma is the analogue of `NLAlib.exec_lanczosStepWith` (`dot`, `bin .div`, `axpy`, `copyv`;
`NLAlib.LanczosMvSpec` is reused for the product); before the division by $\mu_m$,
`NLAlib.CGRun.norm_r_le_two_mul_norm_p` on the prefix with the a priori certificates of
`NLAlib/…/CGBackward.lean` gives $\mathbf{p}_m \ne \mathbf{0}$, and
`NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc` gives $\mu_m > 0$. Difficulty: hard
(about 900 lines, the Lanczos bridge as template). -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_cgRun_of_cgProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P) (o : ι)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {εmv : ℝ}
    (hmv : IsMatvecErr I o dec p A (εmv * specNorm A)) (b : Fin N → K)
    (hb : (fun i => dec p (b i)) ≠ 0) (hq : 0 < q) (hu : ((N + 2 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) ^ 3 * cgRoundingEps N (u p) εmv * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    ∃ st', exec I (cgProg p o (.const N) (.const q) 0 1 2 3 4).run
        (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
          Array.replicate q none, Array.replicate q none, Array.replicate (q + 1) none]) =
        some st' ∧
      HasCGRunOutputs st' p dec (cgRoundingEps N (u p) εmv) 1 2 3 4 q A fun i => dec p (b i) := by
  sorry

/-- **The matrix-free conjugate gradient program in the access model**: the bridge
`NLAlib.Computation.IsRelErrSem.exists_cgRun_of_cgProg` as an instance of
`NLAlib.Computation.MatrixFreeRounded`, with the spectral bounds $a$, $a'$ as parameters of the
precondition. Proof: a wrap of the bridge, as `NLAlib.lanczosBasisProg_matrixFreeRounded`.
Difficulty: easy. -/
theorem cgProg_matrixFreeRounded (p : P) (o : ι) (u : P → ℝ) (dec : P → K → ℝ)
    (εmv a a' : ℝ) :
    MatrixFreeRounded (C := C) (r := 1) (b := 5) p
      (fun N n => (cgProg p o (.const N) (.const (n 0)) 0 1 2 3 4).run)
      (fun _ n => 0 < n 0) (fun N _ => Fin N → K)
      (fun N n b => ![(List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
        Array.replicate (n 0) none, Array.replicate (n 0) none,
        Array.replicate (n 0 + 1) none])
      u dec (fun _ _ A => εmv * specNorm A)
      (fun N n b A => Aᵀ = A ∧ 0 < a ∧ spectrum ℝ A ⊆ Set.Icc a a' ∧
        (fun i => dec p (b i)) ≠ 0 ∧ ((N + 2 : ℕ) : ℝ) * u p < 1 ∧
        (n 0 : ℝ) ^ 3 * cgRoundingEps N (u p) εmv * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
      (fun N n b A st => HasCGRunOutputs st p dec (cgRoundingEps N (u p) εmv) 1 2 3 4 (n 0) A
        fun i => dec p (b i)) := by
  sorry

/-- **The dense conjugate gradient program in the standard model**: as
`NLAlib.Computation.IsRelErrSem.exists_cgRun_of_cgProg`, with the product computed by `gemv`
from the $N \times N$ words `Aw` (buffer 0) decoding to a symmetric $\mathbf{A}$ with spectrum in
$[a, a']$ and $\varepsilon = \max(\sqrt{N}\gamma_N, \gamma_{N+2})$: every hypothesis is on the
data, the sizes and $u_p$. Proof: the same induction with `NLAlib.lanczosMvSpec_gemv`.
Difficulty: easy given the matrix-free proof (shared body). -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_cgRun_of_cgDenseProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (Aw : Fin N → Fin N → K)
    (hA : (Matrix.of fun i j => dec p (Aw i j))ᵀ = Matrix.of fun i j => dec p (Aw i j))
    {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ (Matrix.of fun i j => dec p (Aw i j)) ⊆ Set.Icc a a')
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0) (hq : 0 < q)
    (hu : ((N + 2 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) ^ 3 * cgRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) *
      (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    ∃ st', exec I (cgDenseProg p (.const N) (.const q) 0 1 2 3 4 5).run
        (inputState p [(List.ofFn fun t : Fin (N * N) =>
            some (Aw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right
              (Nat.zero_lt_of_lt t.2))⟩ ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
          (List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
          Array.replicate q none, Array.replicate q none, Array.replicate (q + 1) none]) =
        some st' ∧
      HasCGRunOutputs st' p dec (cgRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)))
        2 3 4 5 q (Matrix.of fun i j => dec p (Aw i j)) fun i => dec p (b i) := by
  sorry

/-- **The outputs of a conjugate gradient run have a backward model**: the outputs decode to
$\mathbf{x}, \gamma, \delta, \nu$, and with $k$ = `NLAlib.cgSteps ν q` there is a symmetric
$\tilde{\mathbf{H}}$ of dimension $N(k+1)$ with spectrum in $[a/2, a' + a/2]$ and
$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
4 \cdot 10^4k^3\varepsilon\kappa a'$, on which exact CG from $\mathbf{0}$ with right-hand side
$(\mathbf{b}, \mathbf{0}, \dots, \mathbf{0})$ computes the output step lengths $\gamma_j$
($j < k$) and residuals $\tilde{\mathbf{r}}_j$ with
$\lvert\|\tilde{\mathbf{r}}_j\|^2 - \nu_j\rvert \le \varepsilon\|\tilde{\mathbf{r}}_j\|^2$
($j \le k$). -/
def HasCGBackwardModel (st : St P K C) (p : P) (dec : P → K → ℝ) (ε a a' : ℝ)
    (X gam del nu : ℕ) {N : ℕ} (q : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) : Prop :=
  ∃ (x : Fin N → ℝ) (γ δ ν : ℕ → ℝ), CGOutputs st p dec X gam del nu q x γ δ ν ∧
    ∃ Ht : Matrix (Fin N × Fin (cgSteps ν q + 1)) (Fin N × Fin (cgSteps ν q + 1)) ℝ,
      Htᵀ = Ht ∧ spectrum ℝ Ht ⊆ Set.Icc (a / 2) (a' + a / 2) ∧
      frobNorm (Ht - Matrix.blockDiagonal fun _ => A) ≤
        40000 * (cgSteps ν q : ℝ) ^ 3 * ε * (a' / a) * a' ∧
      (∀ j < cgSteps ν q, cgAlpha Ht (cgState Ht (fun y => if (y.2 : ℕ) = 0 then b y.1 else 0)
        0 j) = γ j) ∧
      ∀ j ≤ cgSteps ν q,
        |‖WithLp.toLp 2 (cgState Ht (fun y => if (y.2 : ℕ) = 0 then b y.1 else 0) 0 j).r‖ ^ 2 -
            ν j| ≤
          ε * ‖WithLp.toLp 2 (cgState Ht (fun y => if (y.2 : ℕ) = 0 then b y.1 else 0) 0 j).r‖ ^ 2

/-- **The dense conjugate gradient program has a backward model** (end to end): under the
hypotheses of `NLAlib.Computation.IsRelErrSem.exists_cgRun_of_cgDenseProg` the run of $q$ steps
succeeds, and exact CG on a positive definite $\tilde{\mathbf{H}}$ with
$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
4 \cdot 10^4k^3\varepsilon\kappa a'$ computes the output step lengths and, to relative accuracy
$\varepsilon$, the output squared residual norms (`NLAlib.HasCGBackwardModel`). Every hypothesis
is on the data, the sizes and $u_p$.
Proof: the dense bridge, then `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le`,
`NLAlib.CGRun.spectrum_backwardH_subset_Icc`, `NLAlib.CGRun.cgAlpha_backwardH`,
`NLAlib.CGRun.norm_cgState_backwardH_r` and `C.ν_eq`. Difficulty: easy. -/
theorem _root_.NLAlib.Computation.IsRelErrSem.exists_cgBackwardModel_of_cgDenseProg
    {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    {N : ℕ} (q : ℕ) (Aw : Fin N → Fin N → K)
    (hA : (Matrix.of fun i j => dec p (Aw i j))ᵀ = Matrix.of fun i j => dec p (Aw i j))
    {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ (Matrix.of fun i j => dec p (Aw i j)) ⊆ Set.Icc a a')
    (b : Fin N → K) (hb : (fun i => dec p (b i)) ≠ 0) (hq : 0 < q)
    (hu : ((N + 2 : ℕ) : ℝ) * u p < 1)
    (hsmall : (q : ℝ) ^ 3 * cgRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) *
      (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    ∃ st', exec I (cgDenseProg p (.const N) (.const q) 0 1 2 3 4 5).run
        (inputState p [(List.ofFn fun t : Fin (N * N) =>
            some (Aw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right
              (Nat.zero_lt_of_lt t.2))⟩ ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
          (List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
          Array.replicate q none, Array.replicate q none, Array.replicate (q + 1) none]) =
        some st' ∧
      HasCGBackwardModel st' p dec (cgRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)))
        a a' 2 3 4 5 q (Matrix.of fun i j => dec p (Aw i j)) fun i => dec p (b i) := by
  sorry

end NLAlib
