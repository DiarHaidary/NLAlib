/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Matrix.Norms.Compare
public import NLAlibScaffold.Krylov.FinitePrecision.CGBackward
public import NLAlibScaffold.Krylov.LinearSystems.CGProgramRun
public import NLAlibScaffold.Krylov.Processes.LanczosRounding

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

/-! ### The assembly of the run -/

/-- **The smallness facts of the bridge** from $q^3\varepsilon\kappa^2 \le 10^{-5}$, $q \ge 1$,
$0 < a \le a'$, $\varepsilon \ge 0$: for every $m \le q$, $m^3\varepsilon\kappa^2 \le 10^{-5}$,
$m\varepsilon \le 1/100$ and $20m\varepsilon(1 + 2\kappa + 1.05\kappa) \le 1$; and
$3\varepsilon a' \le a$. -/
private theorem cg_smallness {q : ℕ} (hq : 0 < q) {ε a a' : ℝ} (hε : 0 ≤ ε) (ha : 0 < a)
    (hκ : a ≤ a') (hsmall : (q : ℝ) ^ 3 * ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    (∀ m ≤ q, (m : ℝ) ^ 3 * ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) ∧
      (∀ m ≤ q, (m : ℝ) * ε ≤ 1 / 100) ∧ 3 * ε * a' ≤ a ∧
      ∀ m ≤ q, 20 * m * ε * (1 + 2 * (a' / a) + 21 / 20 * (a' / a)) ≤ 1 := by
  set κ := a' / a with hκdef
  have hκ1 : 1 ≤ κ := (one_le_div ha).mpr hκ
  have hsm : ∀ m ≤ q, (m : ℝ) ^ 3 * ε * κ ^ 2 ≤ 1 / 10 ^ 5 := fun m hm => by
    have : (m : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hm) 3
    have h0 : 0 ≤ ε * κ ^ 2 := by positivity
    nlinarith
  have hm1 : ∀ m ≤ q, (m : ℝ) * ε * κ ≤ 1 / 10 ^ 5 := fun m hm => by
    have h1 := hsm m hm
    rcases Nat.eq_zero_or_pos m with rfl | hm0
    · simp
    have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm0
    have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
    have hmm : (m : ℝ) ≤ (m : ℝ) ^ 3 := by nlinarith
    have hκκ : κ ≤ κ ^ 2 := by nlinarith
    have : (m : ℝ) * ε * κ ≤ (m : ℝ) ^ 3 * ε * κ ^ 2 := by
      have h2 : 0 ≤ ε * κ := by positivity
      calc (m : ℝ) * ε * κ ≤ (m : ℝ) ^ 3 * (ε * κ) := by nlinarith
        _ ≤ (m : ℝ) ^ 3 * (ε * κ ^ 2) := by gcongr
        _ = _ := by ring
    linarith
  refine ⟨hsm, fun m hm => ?_, ?_, fun m hm => ?_⟩
  · have := hm1 m hm
    have : (m : ℝ) * ε ≤ (m : ℝ) * ε * κ := by
      have : 0 ≤ (m : ℝ) * ε := by positivity
      nlinarith
    linarith
  · have h1 := hm1 q le_rfl
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have h2 : ε * κ ≤ (q : ℝ) * ε * κ := by
      have : 0 ≤ ε * κ := by positivity
      nlinarith
    have h3 : ε * a' = ε * κ * a := by rw [hκdef]; field_simp
    nlinarith
  · have h1 := hm1 m hm
    have : (0 : ℝ) ≤ m * ε := by positivity
    have h2 : 1 + 2 * κ + 21 / 20 * κ ≤ 5 * κ := by linarith
    nlinarith

/-- The number of steps is at most $q$. -/
theorem cgSteps_le (ν : ℕ → ℝ) (q : ℕ) : cgSteps ν q ≤ q := by
  classical
  unfold cgSteps
  split_ifs with h
  · exact (Nat.find_spec h).1.le
  · exact le_rfl

/-- **The number of steps is the stop of the sequences**: if $\nu_j > 0$ for $j < k$, $k \le q$,
and $\nu_k = 0$ when $k < q$, then `NLAlib.cgSteps ν q` $= k$. -/
private theorem cgSteps_eq {ν : ℕ → ℝ} {q k : ℕ} (hkq : k ≤ q) (hpos : ∀ j < k, 0 < ν j)
    (hstop : k < q → ν k = 0) : cgSteps ν q = k := by
  classical
  unfold cgSteps
  rcases lt_or_eq_of_le hkq with hk | rfl
  · have hex : ∃ j, j < q ∧ ν j = 0 := ⟨k, hk, hstop hk⟩
    rw [dif_pos hex]
    refine (Nat.find_eq_iff hex).mpr ⟨⟨hk, hstop hk⟩, fun n hn h' => (hpos n hn).ne' h'.2⟩
  · rw [dif_neg]
    rintro ⟨j, hj, h0⟩
    exact (hpos j hj).ne' h0

omit [AddMonoid C] in
/-- **The facts of a run of the program give a `NLAlib.CGRun`** on the outputs. -/
private theorem hasCGRunOutputs_of_cgRunFacts {st : St P K C} {p : P} {dec : P → K → ℝ}
    {ε : ℝ} {X G D Nu q N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {bv : Fin N → ℝ} (hA : Aᵀ = A)
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hmε : ∀ m ≤ q, (m : ℝ) * ε ≤ 1 / 100)
    (hF : CGRunFacts p dec X G D Nu q A ε bv st.store) :
    HasCGRunOutputs st p dec ε X G D Nu q A bv := by
  classical
  obtain ⟨k, T, hk, hkq, hv, hstop, hX, hout, hnu, hzo⟩ := hF
  set νo : ℕ → ℝ := fun i => if i ≤ k then T.ν i else 0 with hνo
  have hsteps : cgSteps νo q = k := cgSteps_eq hkq
    (fun j hj => by simpa [hνo, hj.le] using hv.ν_pos j hj)
    (fun h => by simpa [hνo] using hstop h)
  refine ⟨T.x k, fun i => if i < k then T.γ i else 0, fun i => if i < k then T.δ i else 0, νo,
    ⟨fun i => ?_, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩, ?_, ?_⟩
  · obtain ⟨w, hw, hd⟩ := hX i
    exact ⟨w, by simpa using hw, hd⟩
  · by_cases hjk : j < k
    · obtain ⟨w, hw, hd⟩ := (hout j hjk).1
      exact ⟨w, hw, by simpa [hjk] using hd⟩
    · obtain ⟨w, hw, hd⟩ := (hzo j (not_lt.mp hjk) hj).1
      exact ⟨w, hw, by simpa [hjk] using hd⟩
  · by_cases hjk : j < k
    · obtain ⟨w, hw, hd⟩ := (hout j hjk).2
      exact ⟨w, hw, by simpa [hjk] using hd⟩
    · obtain ⟨w, hw, hd⟩ := (hzo j (not_lt.mp hjk) hj).2.1
      exact ⟨w, hw, by simpa [hjk] using hd⟩
  · by_cases hjk : j ≤ k
    · obtain ⟨w, hw, hd⟩ := hnu j hjk
      exact ⟨w, hw, by simpa [hνo, hjk] using hd⟩
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      obtain ⟨w, hw, hd⟩ := (hzo i (by omega) (by omega)).2.2
      exact ⟨w, hw, by simpa [hνo, hjk] using hd⟩
  · intro j hkj hjq
    rw [hsteps] at hkj
    exact ⟨by simp [show ¬ j < k by omega], by simp [show ¬ j < k by omega],
      by simp [hνo, show ¬ j + 1 ≤ k by omega]⟩
  · rw [hsteps]
    refine ⟨hv.toCGRun hA hε hk (hmε k hkq), rfl, rfl, rfl, fun j hj =>
      ⟨by change T.γ j = _; simp [hj], by change T.δ j = _; simp [hj]⟩,
      fun j hj => by change T.ν j = νo j; simp [hνo, hj], rfl, fun h => ?_⟩
    exact hv.r_eq_zero_of_ν_eq_zero hε1 le_rfl (hstop h)

/-- **The matrix-free conjugate gradient program in the standard model**: under
`NLAlib.Computation.IsRelErrSem` (every value in range) and adding zero exactly, an oracle
accurate to $\varepsilon_{\mathrm{mv}}\|\mathbf{A}\|_2$, $\mathbf{A}$ symmetric with spectrum in
$[a, a']$, $a > 0$, $\mathbf{b} \ne \mathbf{0}$ (decoded), $q \ge 1$, $(N + 2)u_p < 1$ and
$q^3\varepsilon\kappa^2 \le 10^{-5}$ for $\varepsilon = \max(\varepsilon_{\mathrm{mv}},
\gamma_{N+2})$, the run of $q$ steps **succeeds** and its outputs form a run
`C : NLAlib.CGRun N k` (`NLAlib.HasCGRunOutputs`); in particular every computed curvature
$\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j$ is positive.
[HestenesStiefel1952, (3:1)]; [Higham2002, §§2.2, 3.1, Lemma 3.3].
The stop test $\nu_j = 0$ detects $\mathbf{r}_j = \mathbf{0}$ exactly in this model of
computation (`NLAlib.CGRun.ν_eq_zero_iff`; no underflow: in IEEE arithmetic
$\mathrm{fl}(\|\mathbf{r}\|^2)$ can be $0$ with $\mathbf{r} \ne \mathbf{0}$).
Proof: loop invariant on the iterations $m \le q$, built forward (it does not presuppose the
final run): for $m = 0$ the decoded state is $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{p}_0 = \mathbf{b}$, $\nu_0 = \|\mathbf{b}\|^2(1 + \theta_0)$ (there is
no `NLAlib.CGRun` of $0$ steps); for $m \ge 1$ there is `R : NLAlib.CGRun N (min m k)` whose
data decode the state (and the outputs so far), extended at each iteration by re-packaging its
fields with the step-$m$ data and re-proving `k_mul_ε_le`. The step lemma is the analogue of
`NLAlib.exec_lanczosStepWith` (`dot`, `bin .div`, `axpy`, `copyv`; `NLAlib.LanczosMvSpec` is
reused for the product). Before the division by $\mu_m$ ($\nu_m \ne 0$): for $m = 0$,
$\mathbf{p}_0 = \mathbf{b} \ne \mathbf{0}$; for $m \ge 1$,
`NLAlib.CGRun.norm_r_le_two_mul_norm_p` on `R` with its a priori certificates
(`NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`; its smallness
from $m^3 \le q^3$) gives $\mathbf{p}_m \ne \mathbf{0}$; in both cases
`NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc` gives $\mu_m > 0$. Fallback (decision CG1 (b),
design note §1.3): a guard `μ ≤ 0 → stop` decouples the bridge from the analysis.
Difficulty: hard (about 1200 lines, the Lanczos bridge as template). -/
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
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact absurd (funext fun i => i.elim0) hb
    · exact hN
  have hε : roundingFactor (N + 2) (u p) ≤ cgRoundingEps N (u p) εmv := le_max_right _ _
  have hε0 : 0 ≤ cgRoundingEps N (u p) εmv := (roundingFactor_nonneg hu0 hu).trans hε
  have hκ := le_of_spectrum_subset_Icc hN0 hA hs
  obtain ⟨hsm, hmε, h3a, h20⟩ := cg_smallness hq hε0 ha hκ hsmall
  have hε1 : cgRoundingEps N (u p) εmv < 1 := by
    have := hmε 1 hq; simp at this; linarith
  obtain ⟨st', he, hF⟩ := IsRelErrSem.exists_cgRunFacts_of_cgProgWith I h hz hu (q := q)
    (inputState p [(List.ofFn fun i => some (b i)).toArray, Array.replicate N none,
      Array.replicate q none, Array.replicate q none, Array.replicate (q + 1) none])
    (lanczosMvSpec_apply I p o dec 0 _ (b ⟨0, hN0⟩) hmv)
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (specNorm_nonneg _)) hε hA ha hs hκ hq hsm
    hmε h3a h20 (B := 0) (X := 1) (G := 2) (D := 3) (Nu := 4) (bv := fun i => dec p (b i))
    (fun i => ⟨b i, by simp [inputState, Store.read], rfl⟩) hb (by simp [inputState])
    (by simp [inputState]) (by simp [inputState, Store.shape]) (by simp [inputState, Store.shape])
    (by simp [inputState, Store.shape]) (by simp [inputState, Store.shape]) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  exact ⟨st', he, hasCGRunOutputs_of_cgRunFacts hA hε0 hε1 hmε hF⟩

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
  intro N n hn b A I h hz hmv ⟨hA, ha, hs, hb, hu, hsmall⟩
  simpa [List.ofFn_succ] using
    IsRelErrSem.exists_cgRun_of_cgProg I p o h hz (n 0) A hA ha hs (hmv o) b hb hn hu hsmall

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
  have hu0 : 0 ≤ u p := h.nonneg trivial
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · exact absurd (funext fun i => i.elim0) hb
    · exact hN
  have huN : (N : ℝ) * u p < 1 := cast_mul_lt_one_of_le hu0 (by omega) hu
  set ε := cgRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p))
  have hε : roundingFactor (N + 2) (u p) ≤ ε := le_max_right _ _
  have hε0 : 0 ≤ ε := (roundingFactor_nonneg hu0 hu).trans hε
  have hκ := le_of_spectrum_subset_Icc hN0 hA hs
  obtain ⟨hsm, hmε, h3a, h20⟩ := cg_smallness hq hε0 ha hκ hsmall
  have hε1 : ε < 1 := by
    have := hmε 1 hq; simp at this; linarith
  set st₀ : St P K C := inputState p [(List.ofFn fun t : Fin (N * N) =>
      some (Aw ⟨t % N, Nat.mod_lt _ (Nat.pos_of_mul_pos_right (Nat.zero_lt_of_lt t.2))⟩
        ⟨t / N, Nat.div_lt_of_lt_mul t.2⟩)).toArray,
    (List.ofFn fun i => some (b i)).toArray, Array.replicate N none, Array.replicate q none,
    Array.replicate q none, Array.replicate (q + 1) none] with hst₀
  have hM : HoldsDecoded st₀.store dec p 0 0 (Matrix.of fun i j => dec p (Aw i j)) := by
    intro i j
    have hlt : (i : ℕ) + N * j < N * N := by nlinarith [i.2, j.2]
    refine ⟨Aw i j, ?_, rfl⟩
    simp only [hst₀, inputState, Store.read]
    suffices Aw ⟨(i + N * j) % N, Nat.mod_lt _ hN0⟩ ⟨(i + N * j) / N, Nat.div_lt_of_lt_mul hlt⟩ =
        Aw i j by simpa [hlt] using this
    congr 1 <;> apply Fin.ext
    · simp [Nat.mod_eq_of_lt i.2]
    · simp [Nat.add_mul_div_left _ _ hN0, Nat.div_eq_of_lt i.2]
  obtain ⟨st', he, hF⟩ := IsRelErrSem.exists_cgRunFacts_of_cgProgWith I h hz hu (q := q) st₀
    (lanczosMvSpec_gemv I h hz p st₀.store _ hM huN)
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (specNorm_nonneg _)) hε hA ha hs hκ hq hsm
    hmε h3a h20 (B := 1) (X := 2) (G := 3) (D := 4) (Nu := 5) (bv := fun i => dec p (b i))
    (fun i => ⟨b i, by simp [hst₀, inputState, Store.read], rfl⟩) hb
    (by simp [hst₀, inputState]) (by simp [hst₀, inputState])
    (by simp [hst₀, inputState, Store.shape]) (by simp [hst₀, inputState, Store.shape])
    (by simp [hst₀, inputState, Store.shape]) (by simp [hst₀, inputState, Store.shape])
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega)
  exact ⟨st', he, hasCGRunOutputs_of_cgRunFacts hA hε0 hε1 hmε hF⟩

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
  obtain ⟨st', he, x, γ, δ, ν, hout, -, R, hRA, hRb, hRε, hγ, hν, -, -⟩ :=
    IsRelErrSem.exists_cgRun_of_cgDenseProg I p h hz q Aw hA ha hs b hb hq hu hsmall
  have hkq : cgSteps ν q ≤ q := cgSteps_le ν q
  have hsR : spectrum ℝ R.A ⊆ Set.Icc a a' := hRA ▸ hs
  have hsmallR : ((cgSteps ν q : ℕ) : ℝ) ^ 3 * R.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5 := by
    rw [hRε]
    refine le_trans ?_ hsmall
    have hε0 : 0 ≤ cgRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) :=
      (roundingFactor_nonneg (h.nonneg trivial) hu).trans (le_max_right _ _)
    have : ((cgSteps ν q : ℕ) : ℝ) ^ 3 ≤ (q : ℝ) ^ 3 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hkq) 3
    have h0 : 0 ≤ cgRoundingEps N (u p) (√(N : ℝ) * roundingFactor N (u p)) * (a' / a) ^ 2 := by
      positivity
    nlinarith
  have hrhs : R.dilatedRhs = fun y => if (y.2 : ℕ) = 0 then dec p (b y.1) else 0 := by
    funext y; simp [CGRun.dilatedRhs, hRb]
  refine ⟨st', he, x, γ, δ, ν, hout, R.backwardH, R.toNormalizedLanczosData.transpose_backwardH,
    R.spectrum_backwardH_subset_Icc ha hsR hsmallR, ?_, fun j hj => ?_, fun j hj => ?_⟩
  · have := R.frobNorm_backwardH_sub_dilatedH_le ha hsR hsmallR
    rw [hRε] at this
    simpa [CGRun.dilatedH, hRA] using this
  · rw [← hrhs, R.cgAlpha_backwardH ha hsR hsmallR hj, (hγ j hj).1]
  · rw [← hrhs, R.norm_cgState_backwardH_r ha hsR hsmallR hj, ← hν j hj, R.ν_eq j hj, ← hRε]
    have hθ := R.abs_θ_le j hj
    have hρ : 0 ≤ R.ρ j ^ 2 := sq_nonneg _
    rw [show R.ρ j ^ 2 - ‖WithLp.toLp 2 (R.r j)‖ ^ 2 * (1 + R.θ j) = -(R.ρ j ^ 2 * R.θ j) by
      rw [CGRun.ρ]; ring, abs_neg, abs_mul, abs_of_nonneg hρ]
    nlinarith [abs_nonneg (R.θ j)]

end NLAlib
