/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.NormalizedBackward
public import NLAlibScaffold.Krylov.LinearSystems.CGTridiagonal

/-!
# A conjugate gradient run with bounded local errors

`NLAlib.CGRun n k` is $k$ steps of the Hestenes–Stiefel recurrence from $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{p}_0 = \mathbf{b}$, for a real symmetric $\mathbf{A}$, with a local error
in each operation bounded relative to its operands by one accuracy parameter $\varepsilon$
(0-based, step $j < k$):
$$\nu_j = \|\mathbf{r}_j\|^2(1 + \theta_j),\quad
\mathbf{s}_j = \mathbf{A}\mathbf{p}_j + \mathbf{e}^s_j,\quad
\mu_j = \mathbf{p}_j^{\mathsf{T}}\mathbf{s}_j + e^\mu_j,\quad
\gamma_j = \frac{\nu_j}{\mu_j}(1 + \eta^\gamma_j),$$
$$\mathbf{x}_{j+1} = \mathbf{x}_j + \gamma_j\mathbf{p}_j + \mathbf{e}^x_j,\quad
\mathbf{r}_{j+1} = \mathbf{r}_j - \gamma_j\mathbf{s}_j + \mathbf{e}^r_j,\quad
\delta_j = \frac{\nu_{j+1}}{\nu_j}(1 + \eta^\delta_j),\quad
\mathbf{p}_{j+1} = \mathbf{r}_{j+1} + \delta_j\mathbf{p}_j + \mathbf{e}^p_j .$$
It is the interface between the rounding-error analysis of the conjugate gradient program
(`NLAlibScaffold/Krylov/LinearSystems/CGRounding.lean`) and the stability analysis.

The **Lanczos data of the run** (`NLAlib.CGRun.toNormalizedLanczosData`) are the normalised
residuals $\bar{\mathbf{v}}_{j+1} = (-1)^j\mathbf{r}_j/\|\mathbf{r}_j\|$ with the tridiagonal
matrix `NLAlib.cgTridiagonal` of the computed $\gamma_j$ and the norms $\rho_j =
\|\mathbf{r}_j\|$ of the computed residuals. The local errors of this datum (Lemmas A and B of the
design note) are bounded a posteriori in terms of three run certificates: $\Pi \ge
\|\mathbf{p}_j\|/\|\mathbf{r}_j\|$, $K \ge \|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2/
\|\mathbf{r}_j\|^2$, and $B$ bounding the coefficients $\beta_{j+1} =
\rho_{j+1}/(\gamma_j\rho_j)$ and $\delta_j/\gamma_j$ for $j + 1 < k$ (the last pair,
$\beta_k$ and $\delta_{k-1}/\gamma_{k-1}$, does not enter the local errors of $k$ steps). The
a priori bounds on the certificates are in
`NLAlibScaffold/Krylov/FinitePrecision/CGBackward.lean`.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§3, §6).
Constants are unoptimised and carry a margin over the hand derivation of the research note
`docs/design/research/HSCG-FiniteP.md` §§2.4–2.5; they are to be re-derived in the proofs.

## Main definitions

* `NLAlib.CGRun`: a run of $k$ steps with accuracy parameter $\varepsilon$.
* `NLAlib.CGRun.toLanczosData`, `NLAlib.CGRun.toNormalizedLanczosData`: its Lanczos data.
* `NLAlib.CGRun.backwardH`: the backward model of the run.

## Main results

* `NLAlib.CGRun.tridiagonal_toLanczosData`: the tridiagonal matrix is `NLAlib.cgTridiagonal`.
* `NLAlib.CGRun.norm_recurrenceError_le` (Lemma A),
  `NLAlib.CGRun.abs_adjacentInner_le` (Lemma B): the local errors.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates`: the a posteriori model.
* `NLAlib.CGRun.norm_r_le_two_mul_norm_p`, `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`:
  the next division succeeds.
* `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le`: the residual gap.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

/-- **A conjugate gradient run with bounded local errors**: $k \ge 1$ steps of the
Hestenes–Stiefel recurrence from $\mathbf{x}_0 = \mathbf{0}$ for a real symmetric $\mathbf{A}$,
every operation exact up to an error bounded by $\varepsilon$ times its operands (the normwise
standard model), $\nu_j > 0$ and $\mu_j > 0$ at every step taken, and $k\varepsilon \le 1/100$.
The computed $\nu_k$ after the last step may be $0$ (the program stops there). -/
structure CGRun (n k : ℕ) where
  /-- The matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The right-hand side. -/
  b : Fin n → ℝ
  /-- The iterates $\mathbf{x}_j$. -/
  x : ℕ → Fin n → ℝ
  /-- The updated residuals $\mathbf{r}_j$. -/
  r : ℕ → Fin n → ℝ
  /-- The search directions $\mathbf{p}_j$. -/
  p : ℕ → Fin n → ℝ
  /-- The products $\mathbf{s}_j$. -/
  s : ℕ → Fin n → ℝ
  /-- The computed squared residual norms $\nu_j$. -/
  ν : ℕ → ℝ
  /-- The computed curvatures $\mu_j$. -/
  μ : ℕ → ℝ
  /-- The step lengths $\gamma_j$. -/
  γ : ℕ → ℝ
  /-- The direction coefficients $\delta_j$. -/
  δ : ℕ → ℝ
  /-- The error of the product. -/
  es : ℕ → Fin n → ℝ
  /-- The relative error of the squared residual norm. -/
  θ : ℕ → ℝ
  /-- The error of the curvature. -/
  eμ : ℕ → ℝ
  /-- The relative error of the step length. -/
  eγ : ℕ → ℝ
  /-- The error of the iterate update. -/
  ex : ℕ → Fin n → ℝ
  /-- The error of the residual update. -/
  er : ℕ → Fin n → ℝ
  /-- The relative error of the direction coefficient. -/
  eδ : ℕ → ℝ
  /-- The error of the direction update. -/
  ep : ℕ → Fin n → ℝ
  /-- The accuracy parameter. -/
  ε : ℝ
  /-- The matrix is symmetric. -/
  transpose_A : Aᵀ = A
  /-- The accuracy parameter is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- At least one step. -/
  k_pos : 0 < k
  /-- Small accuracy parameter. -/
  k_mul_ε_le : (k : ℝ) * ε ≤ 1 / 100
  /-- $\mathbf{x}_0 = \mathbf{0}$. -/
  x_zero : x 0 = 0
  /-- $\mathbf{r}_0 = \mathbf{b}$. -/
  r_zero : r 0 = b
  /-- $\mathbf{p}_0 = \mathbf{b}$. -/
  p_zero : p 0 = b
  /-- The computed squared residual norm. -/
  ν_eq : ∀ j ≤ k, ν j = ‖WithLp.toLp 2 (r j)‖ ^ 2 * (1 + θ j)
  /-- Its relative error. -/
  abs_θ_le : ∀ j ≤ k, |θ j| ≤ ε
  /-- No stop before the last step. -/
  ν_pos : ∀ j < k, 0 < ν j
  /-- The computed product. -/
  s_eq : ∀ j < k, s j = A *ᵥ p j + es j
  /-- The product error. -/
  norm_es_le : ∀ j < k,
    ‖WithLp.toLp 2 (es j)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 (p j)‖
  /-- The computed curvature. -/
  μ_eq : ∀ j < k, μ j = p j ⬝ᵥ s j + eμ j
  /-- The curvature error. -/
  abs_eμ_le : ∀ j < k, |eμ j| ≤ ε * ‖WithLp.toLp 2 (p j)‖ * ‖WithLp.toLp 2 (s j)‖
  /-- The curvature is positive at every step taken (the division succeeded). -/
  μ_pos : ∀ j < k, 0 < μ j
  /-- The step length. -/
  γ_eq : ∀ j < k, γ j = ν j / μ j * (1 + eγ j)
  /-- Its relative error. -/
  abs_eγ_le : ∀ j < k, |eγ j| ≤ ε
  /-- The iterate update. -/
  x_succ : ∀ j < k, x (j + 1) = x j + γ j • p j + ex j
  /-- The iterate update error. -/
  norm_ex_le : ∀ j < k, ‖WithLp.toLp 2 (ex j)‖ ≤
    ε * (‖WithLp.toLp 2 (x j)‖ + |γ j| * ‖WithLp.toLp 2 (p j)‖)
  /-- The residual update. -/
  r_succ : ∀ j < k, r (j + 1) = r j - γ j • s j + er j
  /-- The residual update error. -/
  norm_er_le : ∀ j < k, ‖WithLp.toLp 2 (er j)‖ ≤
    ε * (‖WithLp.toLp 2 (r j)‖ + |γ j| * ‖WithLp.toLp 2 (s j)‖)
  /-- The direction coefficient. -/
  δ_eq : ∀ j < k, δ j = ν (j + 1) / ν j * (1 + eδ j)
  /-- Its relative error. -/
  abs_eδ_le : ∀ j < k, |eδ j| ≤ ε
  /-- The direction update. -/
  p_succ : ∀ j < k, p (j + 1) = r (j + 1) + δ j • p j + ep j
  /-- The direction update error. -/
  norm_ep_le : ∀ j < k, ‖WithLp.toLp 2 (ep j)‖ ≤
    ε * (‖WithLp.toLp 2 (r (j + 1))‖ + |δ j| * ‖WithLp.toLp 2 (p j)‖)

/-! ### Vector norms -/

private theorem norm_toLp_add_le {m : ℕ} (x y : Fin m → ℝ) :
    ‖WithLp.toLp 2 (x + y)‖ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := by
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

private theorem norm_toLp_sub_le {m : ℕ} (x y : Fin m → ℝ) :
    ‖WithLp.toLp 2 (x - y)‖ ≤ ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖ := by
  rw [WithLp.toLp_sub]
  exact norm_sub_le _ _

private theorem norm_toLp_smul {m : ℕ} (c : ℝ) (x : Fin m → ℝ) :
    ‖WithLp.toLp 2 (c • x)‖ = |c| * ‖WithLp.toLp 2 x‖ := by
  rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]

private theorem abs_dotProduct_le {m : ℕ} (x y : Fin m → ℝ) :
    |x ⬝ᵥ y| ≤ ‖WithLp.toLp 2 x‖ * ‖WithLp.toLp 2 y‖ := by
  have := abs_real_inner_le_norm (WithLp.toLp 2 y) (WithLp.toLp 2 x)
  rwa [EuclideanSpace.inner_toLp_toLp, star_trivial, mul_comm ‖WithLp.toLp 2 y‖] at this

private theorem norm_toLp_sq {m : ℕ} (x : Fin m → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = x ⬝ᵥ x := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]

/-- The two spectral facts used for a symmetric matrix with spectrum in $[a, a']$, $a \ge 0$:
$\|\mathbf{A}\|_2 \le a'$ and $a\|\mathbf{p}\|^2 \le \mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$,
for a nonzero $\mathbf{p}$ (which makes the spectrum nonempty). -/
private theorem specNorm_le_and_le_dotProduct {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {a a' : ℝ} (ha : 0 ≤ a) (hs : spectrum ℝ A ⊆ Set.Icc a a') {p : Fin n → ℝ}
    (hp : p ≠ 0) :
    a ≤ a' ∧ specNorm A ≤ a' ∧ a * ‖WithLp.toLp 2 p‖ ^ 2 ≤ p ⬝ᵥ (A *ᵥ p) := by
  have hH : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  have h₁ : a • (1 : Matrix (Fin n) (Fin n) ℝ) ≤ A :=
    (hH.smul_one_le_iff_spectrum_subset_Ici a).2 fun x hx => (hs hx).1
  have h₂ : A ≤ a' • (1 : Matrix (Fin n) (Fin n) ℝ) :=
    (hH.le_smul_one_iff_spectrum_subset_Iic a').2 fun x hx => (hs hx).2
  have hq : ∀ x : Fin n → ℝ, a * ‖WithLp.toLp 2 x‖ ^ 2 ≤ x ⬝ᵥ (A *ᵥ x) ∧
      x ⬝ᵥ (A *ᵥ x) ≤ a' * ‖WithLp.toLp 2 x‖ ^ 2 := by
    intro x
    have e1 := re_quadForm_le_re_quadForm_of_le h₁ x
    have e2 := re_quadForm_le_re_quadForm_of_le h₂ x
    rw [re_quadForm_real_smul_one] at e1 e2
    simp only [quadForm_def, star_trivial, RCLike.re_to_real] at e1 e2
    exact ⟨e1, e2⟩
  have hp0 : 0 < ‖WithLp.toLp 2 p‖ := by
    rw [norm_pos_iff]
    exact fun h => hp (by simpa using congrArg WithLp.ofLp h)
  have haa : a ≤ a' := by
    have := (hq p).1.trans (hq p).2
    exact le_of_mul_le_mul_right this (by positivity)
  refine ⟨haa, ?_, (hq p).1⟩
  refine (hH.specNorm_le_iff_abs_re_quadForm_le (ha.trans haa)).2 fun x => ?_
  simp only [quadForm_def, star_trivial, RCLike.re_to_real]
  have h1 := (hq x).1
  have h2 := (hq x).2
  rw [abs_of_nonneg (le_trans (by positivity) h1)]
  exact h2

/-- **The computed curvature is positive** for a nonzero direction: if the spectrum of the
symmetric $\mathbf{A}$ lies in $[a, a']$, $a > 0$, $\mathbf{s} = \mathbf{A}\mathbf{p} +
\mathbf{e}$ with $\|\mathbf{e}\| \le \varepsilon\|\mathbf{A}\|_2\|\mathbf{p}\|$ and
$\lvert e'\rvert \le \varepsilon\|\mathbf{p}\|\|\mathbf{s}\|$, and $3\varepsilon a' \le a$, then
$\mathbf{p}^{\mathsf{T}}\mathbf{s} + e' > 0$. So the division by the computed
$\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$ succeeds. [StrakosTichy2002, (7.14)].
Proof: $\mathbf{p}^{\mathsf{T}}\mathbf{s} + e' \ge (a - \varepsilon a' -
\varepsilon(1+\varepsilon)a')\|\mathbf{p}\|^2$, with $\|\mathbf{A}\|_2 \le a'$ and
$\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p} \ge a\|\mathbf{p}\|^2$ from the spectrum.
Difficulty: easy. -/
theorem dotProduct_add_pos_of_spectrum_subset_Icc {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {a a' ε : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hε : 0 ≤ ε)
    (hsmall : 3 * ε * a' ≤ a) {p e : Fin n → ℝ} {e' : ℝ} (hp : p ≠ 0)
    (he : ‖WithLp.toLp 2 e‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 p‖)
    (he' : |e'| ≤ ε * ‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 (A *ᵥ p + e)‖) :
    0 < p ⬝ᵥ (A *ᵥ p + e) + e' := by
  obtain ⟨haa, hN, hq⟩ := specNorm_le_and_le_dotProduct hA ha.le hs hp
  have hp0 : 0 < ‖WithLp.toLp 2 p‖ := by
    rw [norm_pos_iff]
    exact fun h => hp (by simpa using congrArg WithLp.ofLp h)
  have hN0 := specNorm_nonneg A
  set P := ‖WithLp.toLp 2 p‖
  have hAp := norm_toLp_mulVec_le A p
  have hs' : ‖WithLp.toLp 2 (A *ᵥ p + e)‖ ≤ (1 + ε) * specNorm A * P := by
    have := norm_toLp_add_le (A *ᵥ p) e
    nlinarith
  have hpe := abs_dotProduct_le p e
  have hε3 : 3 * ε ≤ 1 := by
    by_contra h
    push Not at h
    nlinarith
  rw [dotProduct_add]
  have hE : ε * specNorm A ≤ a / 3 := by nlinarith
  have h1 : |p ⬝ᵥ e| ≤ ε * specNorm A * P ^ 2 := by nlinarith
  have h2 : |e'| ≤ ε * (1 + ε) * specNorm A * P ^ 2 := by
    have := mul_le_mul_of_nonneg_left hs' (by positivity : 0 ≤ ε * P)
    nlinarith
  have h3 : ε * (1 + ε) * specNorm A ≤ 4 / 9 * a := by nlinarith
  have hP2 : 0 < P ^ 2 := by positivity
  nlinarith [abs_le.mp h1, abs_le.mp h2, mul_le_mul_of_nonneg_right h3 hP2.le,
    mul_le_mul_of_nonneg_right hE hP2.le]

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The norms of the computed residuals, $\rho_j = \|\mathbf{r}_j\|$. -/
noncomputable def ρ (j : ℕ) : ℝ :=
  ‖WithLp.toLp 2 (C.r j)‖

/-! ### Elementary consequences of the interface -/

private theorem ε_le : C.ε ≤ 1 / 100 := by
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast C.k_pos
  nlinarith [C.k_mul_ε_le, C.ε_nonneg]

private theorem mul_ε_le' {j : ℕ} (hj : j ≤ k) : (j : ℝ) * C.ε ≤ 1 / 100 :=
  (mul_le_mul_of_nonneg_right (by exact_mod_cast hj) C.ε_nonneg).trans C.k_mul_ε_le

private theorem ρ_nonneg (j : ℕ) : 0 ≤ C.ρ j := norm_nonneg _

private theorem toLp_eq_zero_iff {m : ℕ} (x : Fin m → ℝ) : WithLp.toLp 2 x = 0 ↔ x = 0 := by
  constructor
  · intro h
    simpa using congrArg WithLp.ofLp h
  · rintro rfl
    rfl

private theorem ν_eq' {j : ℕ} (hj : j ≤ k) : C.ν j = C.ρ j ^ 2 * (1 + C.θ j) := C.ν_eq j hj

private theorem one_add_θ_pos {j : ℕ} (hj : j ≤ k) : 0 < 1 + C.θ j := by
  have := (abs_le.mp (C.abs_θ_le j hj)).1
  linarith [C.ε_le]

private theorem ρ_pos {j : ℕ} (hj : j < k) : 0 < C.ρ j := by
  have h := C.ν_pos j hj
  rw [C.ν_eq' hj.le] at h
  rcases (C.ρ_nonneg j).lt_or_eq with h' | h'
  · exact h'
  · rw [← h'] at h
    simp at h

private theorem norm_s_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.s j)‖ ≤ (1 + C.ε) * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖ := by
  rw [C.s_eq j hj]
  have h1 := norm_toLp_add_le (C.A *ᵥ C.p j) (C.es j)
  have h2 := norm_toLp_mulVec_le C.A (C.p j)
  have h3 := C.norm_es_le j hj
  nlinarith

private theorem μ_le {j : ℕ} (hj : j < k) :
    C.μ j ≤ (1 + C.ε) ^ 2 * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 := by
  rw [C.μ_eq j hj]
  have h1 := (abs_le.mp (abs_dotProduct_le (C.p j) (C.s j))).2
  have h2 := (abs_le.mp (C.abs_eμ_le j hj)).2
  have h3 := C.norm_s_le hj
  have hp := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hε := C.ε_nonneg
  have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : 0 ≤ (1 + C.ε) * ‖WithLp.toLp 2 (C.p j)‖)
  nlinarith

private theorem γ_mul_μ {j : ℕ} (hj : j < k) : C.γ j * C.μ j = C.ν j * (1 + C.eγ j) := by
  rw [C.γ_eq j hj]
  field_simp [(C.μ_pos j hj).ne']

/-- The **Lanczos vectors of the run**, 1-based as `NLAlib.LanczosData`:
$\bar{\mathbf{v}}_0 = \mathbf{0}$,
$\bar{\mathbf{v}}_{j+1} = (-1)^j\mathbf{r}_j/\|\mathbf{r}_j\|$, and
$\bar{\mathbf{v}}_{j+1} = \mathbf{b}/\|\mathbf{b}\|$ if $\mathbf{r}_j = \mathbf{0}$ (only at the
last index, where it is multiplied by $\beta_k = 0$). -/
noncomputable def lanczosV (j : ℕ) : Fin n → ℝ :=
  if j = 0 then 0
  else if C.r (j - 1) = 0 then (‖WithLp.toLp 2 C.b‖⁻¹ : ℝ) • C.b
  else ((-1 : ℝ) ^ (j - 1) * (C.ρ (j - 1))⁻¹) • C.r (j - 1)

/-- The diagonal coefficients of the run's Lanczos data, 1-based: $\alpha_{j+1}$ is the
$(j, j)$ entry of `NLAlib.cgTridiagonal C.γ C.ρ k`. -/
noncomputable def lanczosα (j : ℕ) : ℝ :=
  (C.γ (j - 1))⁻¹ + if j ≤ 1 then 0 else (C.ρ (j - 1) / C.ρ (j - 2)) ^ 2 / C.γ (j - 2)

/-- The off-diagonal coefficients of the run's Lanczos data, 1-based:
$\beta_0 = 0$, $\beta_{j+1} = \rho_{j+1}/(\gamma_j\rho_j)$. -/
noncomputable def lanczosβ (j : ℕ) : ℝ :=
  if j = 0 then 0 else C.ρ j / (C.γ (j - 1) * C.ρ (j - 1))

/-- **The Lanczos data of a conjugate gradient run**: the normalised residuals with the
coefficients of `NLAlib.cgTridiagonal`. -/
noncomputable def toLanczosData : LanczosData n k where
  H := C.A
  v := C.lanczosV
  α := C.lanczosα
  β := C.lanczosβ
  transpose_H := C.transpose_A
  k_pos := C.k_pos
  v_zero := by simp [lanczosV]
  β_zero := by simp [lanczosβ]

/-- **The computed squared residual norm vanishes exactly with the residual**:
$\nu_j = 0 \iff \mathbf{r}_j = \mathbf{0}$, $j \le k$. This is a statement about the model
of computation without underflow (`NLAlib.CGRun.ν_eq`); in IEEE arithmetic
$\mathrm{fl}(\|\mathbf{r}\|^2)$ can underflow to $0$ with $\mathbf{r} \ne \mathbf{0}$.
Proof: `C.ν_eq` and $1 + \theta_j \ge 1 - \varepsilon > 0$. Difficulty: easy. -/
theorem ν_eq_zero_iff {j : ℕ} (hj : j ≤ k) : C.ν j = 0 ↔ C.r j = 0 := by
  rw [C.ν_eq' hj, mul_eq_zero, or_iff_left (C.one_add_θ_pos hj).ne', ρ, sq_eq_zero_iff,
    norm_eq_zero, toLp_eq_zero_iff]

/-- The step lengths are positive. Proof: `C.γ_eq`, `C.ν_pos`, `C.μ_pos`, $\varepsilon < 1$.
Difficulty: easy. -/
theorem γ_pos {j : ℕ} (hj : j < k) : 0 < C.γ j := by
  rw [C.γ_eq j hj]
  have := (abs_le.mp (C.abs_eγ_le j hj)).1
  have := C.ε_le
  exact mul_pos (div_pos (C.ν_pos j hj) (C.μ_pos j hj)) (by linarith)

/-- The Lanczos vectors of the run are unit vectors. Proof: `C.ν_eq_zero_iff` and `C.ν_pos` give
$\mathbf{r}_0 = \mathbf{b} \ne \mathbf{0}$; each branch of `NLAlib.CGRun.lanczosV` is normalised.
Difficulty: easy. -/
theorem norm_lanczosV {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k + 1) :
    ‖WithLp.toLp 2 (C.lanczosV j)‖ = 1 := by
  have _ : j ≤ k + 1 := h2
  have hb : C.b ≠ 0 := by
    rw [← C.r_zero, Ne, ← C.ν_eq_zero_iff (Nat.zero_le k)]
    exact (C.ν_pos 0 C.k_pos).ne'
  have hb' : ‖WithLp.toLp 2 C.b‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact fun h => hb ((toLp_eq_zero_iff _).1 h)
  unfold lanczosV
  rw [if_neg (by omega)]
  split_ifs with h
  · rw [norm_toLp_smul, abs_inv, abs_norm, inv_mul_cancel₀ hb']
  · have hρ : C.ρ (j - 1) ≠ 0 := by
      rw [ρ, norm_ne_zero_iff]
      exact fun h' => h ((toLp_eq_zero_iff _).1 h')
    rw [norm_toLp_smul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_inv,
      abs_of_nonneg (C.ρ_nonneg _), ← ρ, inv_mul_cancel₀ hρ]

/-- The coefficients $\beta_j$ of the run are nonnegative. Proof: `C.γ_pos`. Difficulty: easy. -/
theorem lanczosβ_nonneg {j : ℕ} (hj : j ≤ k) : 0 ≤ C.lanczosβ j := by
  unfold lanczosβ
  split_ifs with h
  · exact le_rfl
  · have := C.γ_pos (j := j - 1) (by omega)
    exact div_nonneg (C.ρ_nonneg j) (mul_nonneg this.le (C.ρ_nonneg _))

/-- The coefficients $\beta_j$, $1 \le j < k$, are positive. Proof: `C.γ_pos` and
$\mathbf{r}_j \ne \mathbf{0}$ (`C.ν_pos`, `C.ν_eq_zero_iff`). Difficulty: easy. -/
theorem lanczosβ_pos {j : ℕ} (h1 : 1 ≤ j) (h2 : j < k) : 0 < C.lanczosβ j := by
  unfold lanczosβ
  rw [if_neg (by omega)]
  exact div_pos (C.ρ_pos h2) (mul_pos (C.γ_pos (by omega)) (C.ρ_pos (by omega)))

/-- **The run as normalised Lanczos data** (`NLAlib.NormalizedLanczosData`). -/
noncomputable def toNormalizedLanczosData : NormalizedLanczosData n k :=
  { C.toLanczosData with
    norm_v := fun _ h1 h2 => C.norm_lanczosV h1 h2
    β_nonneg := fun _ hj => C.lanczosβ_nonneg hj
    β_pos := fun _ h1 h2 => C.lanczosβ_pos h1 h2 }

/-- The **backward model of the run**: `NLAlib.NormalizedLanczosData.backwardH` of its Lanczos
data. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  C.toNormalizedLanczosData.backwardH

/-- The dilated matrix $\mathbf{I}_{k+1} \otimes \mathbf{A}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => C.A

/-- The **dilated right-hand side** $(\mathbf{b}, \mathbf{0}, \dots, \mathbf{0})$: the start of
exact CG on the model, $\|\mathbf{b}\|$ times the dilated Lanczos start. -/
def dilatedRhs : Fin n × Fin (k + 1) → ℝ :=
  fun x => if (x.2 : ℕ) = 0 then C.b x.1 else 0

/-- **The tridiagonal matrix of the run is the CG tridiagonal matrix** of the computed step
lengths and residual norms. Proof: unfold; the cases of `NLAlib.cgTridiagonal` and
`NLAlib.LanczosData.tridiagonal` match entry by entry. Difficulty: easy. -/
theorem tridiagonal_toLanczosData : C.toLanczosData.tridiagonal = cgTridiagonal C.γ C.ρ k := by
  ext i j
  simp only [LanczosData.tridiagonal, cgTridiagonal, toLanczosData, Matrix.of_apply, lanczosα,
    lanczosβ]
  split_ifs <;> first
    | rfl
    | (exfalso; omega)
    | (rw [show (i : ℕ) - 1 = j by omega])
    | (rw [show (j : ℕ) - 1 = i by omega])

/-- The direction coefficient against the exact residual ratio:
$\lvert\delta_j - \rho_{j+1}^2/\rho_j^2\rvert \le 4\varepsilon\rho_{j+1}^2/\rho_j^2$, $j < k$.
Proof: `C.δ_eq`, `C.ν_eq` at $j$ and $j + 1$, $\varepsilon \le 1/100$. Difficulty: easy. -/
theorem abs_δ_sub_le {j : ℕ} (hj : j < k) :
    |C.δ j - C.ρ (j + 1) ^ 2 / C.ρ j ^ 2| ≤ 4 * C.ε * (C.ρ (j + 1) ^ 2 / C.ρ j ^ 2) := by
  have hρ := C.ρ_pos hj
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have hθ' := abs_le.mp (C.abs_θ_le (j + 1) hj)
  have he := abs_le.mp (C.abs_eδ_le j hj)
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  set R := C.ρ (j + 1) ^ 2 / C.ρ j ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have h1 := C.one_add_θ_pos hj.le
  have hδ : C.δ j = R * ((1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j)) := by
    rw [C.δ_eq j hj, C.ν_eq' hj, C.ν_eq' hj.le, hR]
    field_simp
  have hu : |(1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j) - 1| ≤ 4 * C.ε := by
    rw [div_sub_one h1.ne', abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
    constructor <;> nlinarith
  rw [hδ, ← mul_sub_one, abs_mul, abs_of_nonneg hR0, mul_comm]
  exact mul_le_mul_of_nonneg_right hu hR0

/-- **The step length against the direction** (the computed Rayleigh quotient):
$\rho_j^2 \le \tfrac{21}{20}\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2$, $j < k$, i.e.
$\gamma_j^{-1} \le 1.05\|\mathbf{A}\|_2\pi_j^2$.
Proof: $\mu_j \le (1+\varepsilon)^2\|\mathbf{A}\|_2\|\mathbf{p}_j\|^2$ and
$\nu_j \ge (1-\varepsilon)\rho_j^2$. Difficulty: easy. -/
theorem ρ_sq_le {j : ℕ} (hj : j < k) :
    C.ρ j ^ 2 ≤ 21 / 20 * specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 := by
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have he := abs_le.mp (C.abs_eγ_le j hj)
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hγ := C.γ_pos hj
  have hμ := C.μ_le hj
  have hgm := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le] at hgm
  have hX : 0 ≤ specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 := by
    have := specNorm_nonneg C.A
    positivity
  have hρ2 : 0 ≤ C.ρ j ^ 2 := by positivity
  have h1 : C.ρ j ^ 2 * (1 - C.ε) ^ 2 ≤ C.γ j * C.μ j := by
    rw [hgm]
    have : (1 - C.ε) ^ 2 ≤ (1 + C.θ j) * (1 + C.eγ j) := by nlinarith
    exact mul_le_mul_of_nonneg_left this hρ2 |>.trans (le_of_eq (by ring))
  have h2 := mul_le_mul_of_nonneg_left hμ hγ.le
  have h3 : (1 + C.ε) ^ 2 ≤ 21 / 20 * (1 - C.ε) ^ 2 := by nlinarith
  have h4 := mul_le_mul_of_nonneg_left h3 (mul_nonneg hγ.le hX)
  have h5 : C.ρ j ^ 2 * (1 - C.ε) ^ 2 ≤
      21 / 20 * specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 * (1 - C.ε) ^ 2 := by
    nlinarith
  exact le_of_mul_le_mul_right h5 (by nlinarith)

/-! ### Step relations used by Lemmas A and B -/

/-- The sharper form of `NLAlib.CGRun.abs_δ_sub_le`:
$\lvert\delta_j - \rho_{j+1}^2/\rho_j^2\rvert \le 3.1\varepsilon\rho_{j+1}^2/\rho_j^2$. -/
private theorem abs_δ_sub_le' {j : ℕ} (hj : j < k) :
    |C.δ j - C.ρ (j + 1) ^ 2 / C.ρ j ^ 2| ≤ 31 / 10 * C.ε * (C.ρ (j + 1) ^ 2 / C.ρ j ^ 2) := by
  have hρ := C.ρ_pos hj
  have hθ := abs_le.mp (C.abs_θ_le j hj.le)
  have hθ' := abs_le.mp (C.abs_θ_le (j + 1) hj)
  have he := abs_le.mp (C.abs_eδ_le j hj)
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  set R := C.ρ (j + 1) ^ 2 / C.ρ j ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have h1 := C.one_add_θ_pos hj.le
  have hδ : C.δ j = R * ((1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j)) := by
    rw [C.δ_eq j hj, C.ν_eq' hj, C.ν_eq' hj.le, hR]
    field_simp
  have hu : |(1 + C.θ (j + 1)) * (1 + C.eδ j) / (1 + C.θ j) - 1| ≤ 31 / 10 * C.ε := by
    rw [div_sub_one h1.ne', abs_div, abs_of_pos h1, div_le_iff₀ h1, abs_le]
    constructor <;> nlinarith
  rw [hδ, ← mul_sub_one, abs_mul, abs_of_nonneg hR0, mul_comm]
  exact mul_le_mul_of_nonneg_right hu hR0

/-- The bounds on $\delta_j$ that follow: $\delta_j \ge 0$,
$\delta_j\rho_j^2 \le (1 + 3.1\varepsilon)\rho_{j+1}^2$ and
$\rho_{j+1}^2 \le (1 + 3.2\varepsilon)\delta_j\rho_j^2$. -/
private theorem δ_bounds {j : ℕ} (hj : j < k) :
    0 ≤ C.δ j ∧ C.δ j * C.ρ j ^ 2 ≤ (1 + 31 / 10 * C.ε) * C.ρ (j + 1) ^ 2 ∧
      C.ρ (j + 1) ^ 2 ≤ (1 + 16 / 5 * C.ε) * (C.δ j * C.ρ j ^ 2) := by
  have h := abs_le.mp (C.abs_δ_sub_le' hj)
  have hρ := C.ρ_pos hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hρ2 : 0 < C.ρ j ^ 2 := by positivity
  set R := C.ρ (j + 1) ^ 2 / C.ρ j ^ 2 with hR
  have hR0 : 0 ≤ R := by positivity
  have hRe : R * C.ρ j ^ 2 = C.ρ (j + 1) ^ 2 := by
    rw [hR]
    field_simp
  refine ⟨by nlinarith, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_right (by linarith : C.δ j ≤ (1 + 31 / 10 * C.ε) * R) hρ2.le
    nlinarith
  · have h2 : R ≤ (1 + 16 / 5 * C.ε) * C.δ j := by nlinarith
    have := mul_le_mul_of_nonneg_right h2 hρ2.le
    nlinarith

private theorem norm_er_le' {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.er j)‖ ≤ C.ε * (C.ρ j + C.γ j * ‖WithLp.toLp 2 (C.s j)‖) := by
  have := C.norm_er_le j hj
  rwa [abs_of_pos (C.γ_pos hj)] at this

private theorem norm_ep_le' {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.ep j)‖ ≤ C.ε * (C.ρ (j + 1) + C.δ j * ‖WithLp.toLp 2 (C.p j)‖) := by
  have := C.norm_ep_le j hj
  rwa [abs_of_nonneg (C.δ_bounds hj).1] at this

/-- The previous direction, scaled, is controlled by the current one:
$\delta_j\|\mathbf{p}_j\| \le 1.05(\|\mathbf{p}_{j+1}\| + \rho_{j+1})$ (from the direction update),
so no residual ratio is needed. -/
private theorem δ_mul_norm_p_le {j : ℕ} (hj : j < k) :
    C.δ j * ‖WithLp.toLp 2 (C.p j)‖ ≤
      21 / 20 * (‖WithLp.toLp 2 (C.p (j + 1))‖ + C.ρ (j + 1)) := by
  have hid : C.δ j • C.p j = C.p (j + 1) - C.r (j + 1) - C.ep j := by
    rw [C.p_succ j hj]
    abel
  have h1 : C.δ j * ‖WithLp.toLp 2 (C.p j)‖ ≤
      ‖WithLp.toLp 2 (C.p (j + 1))‖ + C.ρ (j + 1) + ‖WithLp.toLp 2 (C.ep j)‖ := by
    have := norm_toLp_sub_le (C.p (j + 1) - C.r (j + 1)) (C.ep j)
    have h2 := norm_toLp_sub_le (C.p (j + 1)) (C.r (j + 1))
    rw [← hid, norm_toLp_smul, abs_of_nonneg (C.δ_bounds hj).1] at this
    simp only [ρ]
    linarith
  have h3 := C.norm_ep_le' hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hp := norm_nonneg (WithLp.toLp 2 (C.p (j + 1)))
  have hρ := C.ρ_nonneg (j + 1)
  have hD : 0 ≤ C.δ j * ‖WithLp.toLp 2 (C.p j)‖ :=
    mul_nonneg (C.δ_bounds hj).1 (norm_nonneg _)
  nlinarith

/-- The Lanczos vector of the run at a step taken. -/
private theorem lanczosV_succ {j : ℕ} (hj : j < k) :
    C.lanczosV (j + 1) = ((-1 : ℝ) ^ j * (C.ρ j)⁻¹) • C.r j := by
  have hr : C.r j ≠ 0 := by
    rw [Ne, ← C.ν_eq_zero_iff hj.le]
    exact (C.ν_pos j hj).ne'
  simp only [lanczosV, Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero j), if_neg hr]

/-- The normalisation step is exact:
$\beta_{j+1}\bar{\mathbf{v}}_{j+2} = (-1)^{j+1}\mathbf{r}_{j+1}/(\gamma_j\rho_j)$, also when
$\mathbf{r}_{j+1} = \mathbf{0}$. -/
private theorem lanczosβ_smul_lanczosV {j : ℕ} (hj : j < k) :
    C.lanczosβ (j + 1) • C.lanczosV (j + 2) =
      (-((-1 : ℝ) ^ j * (C.γ j * C.ρ j)⁻¹)) • C.r (j + 1) := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  by_cases hr : C.r (j + 1) = 0
  · have h0 : C.ρ (j + 1) = 0 := by rw [ρ, hr, WithLp.toLp_zero, norm_zero]
    rw [hr, smul_zero, lanczosβ, if_neg (Nat.succ_ne_zero j), h0, zero_div, zero_smul]
  · have hρ' : C.ρ (j + 1) ≠ 0 := by
      rw [ρ, norm_ne_zero_iff]
      exact fun h => hr ((toLp_eq_zero_iff _).1 h)
    simp only [lanczosV, lanczosβ, show j + 2 - 1 = j + 1 by omega, Nat.add_sub_cancel,
      if_neg (show j + 2 ≠ 0 by omega), if_neg (Nat.succ_ne_zero j), if_neg hr, smul_smul]
    congr 1
    field_simp
    ring

/-- The backward term $\beta_j\bar{\mathbf{v}}_j$, $1 \le j < k$. -/
private theorem lanczosβ_smul_lanczosV_self {i : ℕ} (hi : i + 1 < k) :
    C.lanczosβ (i + 1) • C.lanczosV (i + 1) =
      ((-1 : ℝ) ^ i * (C.ρ (i + 1) / (C.γ i * C.ρ i ^ 2))) • C.r i := by
  have hγ := C.γ_pos (by omega : i < k)
  have hρ := C.ρ_pos (by omega : i < k)
  rw [C.lanczosV_succ (by omega), smul_smul, lanczosβ, if_neg (Nat.succ_ne_zero i),
    Nat.add_sub_cancel]
  congr 1
  field_simp

/-- The matrix–direction product of a step taken, solved from the residual update:
$\mathbf{A}\mathbf{p}_j = \gamma_j^{-1}(\mathbf{r}_j - \mathbf{r}_{j+1} + \mathbf{e}^r_j) -
\mathbf{e}^s_j$. -/
private theorem mulVec_p_eq {j : ℕ} (hj : j < k) :
    C.A *ᵥ C.p j = (C.γ j)⁻¹ • (C.r j - C.r (j + 1) + C.er j) - C.es j := by
  have hγ := (C.γ_pos hj).ne'
  rw [C.r_succ j hj, C.s_eq j hj]
  match_scalars <;> field_simp <;> ring

/-- **The recurrence error at the first step**:
$\rho_0\bar{\mathbf{f}}_0 = -\mathbf{e}^s_0 + \gamma_0^{-1}\mathbf{e}^r_0$. -/
private theorem recurrenceError_zero :
    C.toLanczosData.recurrenceError 0 =
      (C.ρ 0)⁻¹ • (-C.es 0 + (C.γ 0)⁻¹ • C.er 0) := by
  have hk := C.k_pos
  have hγ := (C.γ_pos hk).ne'
  have hρ := (C.ρ_pos hk).ne'
  have h1 := C.lanczosV_succ hk
  have h2 := C.lanczosβ_smul_lanczosV hk
  simp only [pow_zero, one_mul] at h1 h2
  simp only [LanczosData.recurrenceError, toLanczosData, zero_add]
  rw [show (2 : ℕ) = 0 + 2 from rfl, h2, h1, show C.lanczosβ 0 = 0 by simp [lanczosβ], zero_smul,
    sub_zero, show C.lanczosα 1 = (C.γ 0)⁻¹ by simp [lanczosα]]
  rw [C.r_succ 0 hk, C.s_eq 0 hk, C.p_zero, ← C.r_zero]
  simp only [Matrix.mulVec_smul]
  match_scalars <;> field_simp <;> ring

/-- **The recurrence error at a later step** $j = i + 1 < k$, with
$c = \rho_j^2/(\rho_i^2\gamma_i)$ the diagonal convention of `NLAlib.cgTridiagonal`:
$(-1)^j\rho_j\bar{\mathbf{f}}_j = -\mathbf{e}^s_j + \gamma_j^{-1}\mathbf{e}^r_j -
\mathbf{A}\mathbf{e}^p_i + \delta_i\mathbf{e}^s_i - (\delta_i/\gamma_i)\mathbf{e}^r_i +
(c - \delta_i/\gamma_i)(\mathbf{r}_i - \mathbf{r}_j)$. -/
private theorem recurrenceError_succ {i : ℕ} (hi : i + 1 < k) :
    C.toLanczosData.recurrenceError (i + 1) =
      ((-1 : ℝ) ^ (i + 1) * (C.ρ (i + 1))⁻¹) • (-C.es (i + 1) + (C.γ (i + 1))⁻¹ • C.er (i + 1) -
        C.A *ᵥ C.ep i + C.δ i • C.es i - (C.δ i / C.γ i) • C.er i +
        (C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i) • (C.r i - C.r (i + 1))) := by
  have hi' : i < k := by omega
  have hγ := (C.γ_pos hi).ne'
  have hγ' := (C.γ_pos hi').ne'
  have hρ := (C.ρ_pos hi).ne'
  have hρ' := (C.ρ_pos hi').ne'
  simp only [LanczosData.recurrenceError, toLanczosData]
  rw [C.lanczosβ_smul_lanczosV hi, C.lanczosβ_smul_lanczosV_self hi, C.lanczosV_succ hi]
  rw [show C.lanczosα (i + 1 + 1) = (C.γ (i + 1))⁻¹ + (C.ρ (i + 1) / C.ρ i) ^ 2 / C.γ i by
    simp [lanczosα]]
  rw [C.r_succ (i + 1) hi, C.s_eq (i + 1) hi, C.p_succ i hi']
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [C.mulVec_p_eq hi']
  match_scalars <;> field_simp <;> ring

/-- The inverse step length against a direction certificate: $\gamma_j^{-1} \le
1.05\|\mathbf{A}\|_2\Pi^2$ when $\|\mathbf{p}_j\| \le \Pi\rho_j$ (from `NLAlib.CGRun.ρ_sq_le`). -/
private theorem inv_γ_le {P : ℝ} {j : ℕ} (hj : j < k)
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j) :
    (C.γ j)⁻¹ ≤ 21 / 20 * specNorm C.A * P ^ 2 := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  have h1 := C.ρ_sq_le hj
  have hN := specNorm_nonneg C.A
  have hp2 : ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ P ^ 2 * C.ρ j ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hP 2
  have h2 : C.ρ j ^ 2 * 1 ≤ C.ρ j ^ 2 * (21 / 20 * specNorm C.A * P ^ 2 * C.γ j) := by
    have := mul_le_mul_of_nonneg_left hp2 (by positivity : 0 ≤ 21 / 20 * specNorm C.A * C.γ j)
    nlinarith
  have h3 := le_of_mul_le_mul_left h2 (by positivity)
  rw [inv_le_iff_one_le_mul₀ hγ]
  linarith

set_option maxHeartbeats 1000000 in
/-- The norm of the vector of `NLAlib.CGRun.recurrenceError_succ`, relative to $\rho_j$. -/
private theorem norm_recurrenceError_succ_mul_le {P B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1))
    (hβ : C.lanczosβ (i + 1) ≤ B) (hδB : C.δ i ≤ B * C.γ i) :
    ‖WithLp.toLp 2 (-C.es (i + 1) + (C.γ (i + 1))⁻¹ • C.er (i + 1) -
        C.A *ᵥ C.ep i + C.δ i • C.es i - (C.δ i / C.γ i) • C.er i +
        (C.ρ (i + 1) ^ 2 / C.ρ i ^ 2 / C.γ i - C.δ i / C.γ i) • (C.r i - C.r (i + 1)))‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B) * C.ρ (i + 1) := by
  have hi' : i < k := by omega
  have hγ := C.γ_pos hi
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hN := specNorm_nonneg C.A
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  obtain ⟨hδ0, hδ1, hδ2⟩ := C.δ_bounds hi'
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ
    linarith [norm_nonneg (WithLp.toLp 2 (C.p (i + 1)))]
  set N := specNorm C.A
  set ρ := C.ρ (i + 1)
  set ρ' := C.ρ i
  set γ := C.γ (i + 1)
  set γ' := C.γ i
  set δ := C.δ i
  set p := ‖WithLp.toLp 2 (C.p (i + 1))‖
  set D := δ * ‖WithLp.toLp 2 (C.p i)‖
  have hp0 : 0 ≤ p := norm_nonneg _
  have hD : D ≤ 21 / 20 * (p + ρ) := C.δ_mul_norm_p_le hi'
  have hD0 : 0 ≤ D := mul_nonneg hδ0 (norm_nonneg _)
  have hβ' : ρ / (γ' * ρ') ≤ B := by
    simpa [lanczosβ] using hβ
  have hB0 : 0 ≤ B := le_trans (by positivity) hβ'
  -- the six terms
  have t1 : ‖WithLp.toLp 2 (C.es (i + 1))‖ ≤ C.ε * N * p := C.norm_es_le (i + 1) hi
  have hs := C.norm_s_le hi
  have hs' := C.norm_s_le hi'
  have hinv := C.inv_γ_le hi hP
  have t2 : ‖WithLp.toLp 2 ((C.γ (i + 1))⁻¹ • C.er (i + 1))‖ ≤
      C.ε * (γ⁻¹ * ρ) + C.ε * ((1 + C.ε) * N * p) := by
    rw [norm_toLp_smul, abs_inv, abs_of_pos hγ]
    have := mul_le_mul_of_nonneg_left (C.norm_er_le' hi) (inv_nonneg.2 hγ.le)
    have e : γ⁻¹ * (C.ε * (ρ + γ * ‖WithLp.toLp 2 (C.s (i + 1))‖)) =
        C.ε * (γ⁻¹ * ρ) + C.ε * ‖WithLp.toLp 2 (C.s (i + 1))‖ := by
      field_simp
    rw [e] at this
    nlinarith
  have t3 : ‖WithLp.toLp 2 (C.A *ᵥ C.ep i)‖ ≤ N * (C.ε * (ρ + D)) :=
    (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_left (C.norm_ep_le' hi') hN)
  have t4 : ‖WithLp.toLp 2 (C.δ i • C.es i)‖ ≤ C.ε * N * D := by
    rw [norm_toLp_smul, abs_of_nonneg hδ0]
    have := mul_le_mul_of_nonneg_left (C.norm_es_le i hi') hδ0
    calc _ ≤ _ := this
      _ = _ := by ring
  -- δ ρ' / γ' ≤ 1.031 ρ B
  have hq : δ * ρ' / γ' ≤ (1 + 31 / 10 * C.ε) * B * ρ := by
    have e1 : δ * ρ' / γ' = δ * ρ' ^ 2 / (γ' * ρ') := by field_simp
    have e2 : (1 + 31 / 10 * C.ε) * ρ ^ 2 / (γ' * ρ') = (1 + 31 / 10 * C.ε) * ρ * (ρ / (γ' * ρ')) := by
      field_simp
    rw [e1]
    calc δ * ρ' ^ 2 / (γ' * ρ') ≤ (1 + 31 / 10 * C.ε) * ρ ^ 2 / (γ' * ρ') := by gcongr
      _ = (1 + 31 / 10 * C.ε) * ρ * (ρ / (γ' * ρ')) := e2
      _ ≤ (1 + 31 / 10 * C.ε) * ρ * B := by gcongr
      _ = _ := by ring
  have t5 : ‖WithLp.toLp 2 ((C.δ i / C.γ i) • C.er i)‖ ≤
      C.ε * ((1 + 31 / 10 * C.ε) * B * ρ) + C.ε * ((1 + C.ε) * N * D) := by
    rw [norm_toLp_smul, abs_of_nonneg (div_nonneg hδ0 hγ'.le)]
    have := mul_le_mul_of_nonneg_left (C.norm_er_le' hi') (div_nonneg hδ0 hγ'.le)
    have e : δ / γ' * (C.ε * (ρ' + γ' * ‖WithLp.toLp 2 (C.s i)‖)) =
        C.ε * (δ * ρ' / γ') + C.ε * (δ * ‖WithLp.toLp 2 (C.s i)‖) := by
      field_simp
    rw [e] at this
    have h2 := mul_le_mul_of_nonneg_left hs' hδ0
    have h3 : δ * ((1 + C.ε) * N * ‖WithLp.toLp 2 (C.p i)‖) = (1 + C.ε) * N * D := by ring
    rw [h3] at h2
    nlinarith
  have t6 : ‖WithLp.toLp 2 ((ρ ^ 2 / ρ' ^ 2 / γ' - δ / γ') • (C.r i - C.r (i + 1)))‖ ≤
      31 / 10 * C.ε * (ρ * B + (1 + 16 / 5 * C.ε) * B * ρ) := by
    rw [norm_toLp_smul]
    have hr := norm_toLp_sub_le (C.r i) (C.r (i + 1))
    have hd := C.abs_δ_sub_le' hi'
    set R := ρ ^ 2 / ρ' ^ 2
    have hR0 : 0 ≤ R := by positivity
    have e1 : R / γ' - δ / γ' = -(δ - R) / γ' := by ring
    rw [e1, abs_div, abs_neg, abs_of_pos hγ']
    have hRρ' : R * ρ' / γ' = ρ * (ρ / (γ' * ρ')) := by
      simp only [R]
      field_simp
    have hRρ : R / γ' ≤ (1 + 16 / 5 * C.ε) * B := by
      have : R ≤ (1 + 16 / 5 * C.ε) * δ := by
        have := hδ2
        simp only [R]
        rw [div_le_iff₀ (by positivity)]
        linarith
      calc R / γ' ≤ (1 + 16 / 5 * C.ε) * δ / γ' := by gcongr
        _ ≤ (1 + 16 / 5 * C.ε) * (B * γ') / γ' := by gcongr
        _ = _ := by field_simp
    calc |δ - R| / γ' * ‖WithLp.toLp 2 (C.r i - C.r (i + 1))‖
        ≤ 31 / 10 * C.ε * R / γ' * (ρ' + ρ) :=
          mul_le_mul (div_le_div_of_nonneg_right hd hγ'.le) hr (norm_nonneg _) (by positivity)
      _ = 31 / 10 * C.ε * (ρ * (ρ / (γ' * ρ')) + R / γ' * ρ) := by
          rw [← hRρ']
          ring
      _ ≤ _ := by gcongr
  -- assemble
  have hsum : ‖WithLp.toLp 2 (-C.es (i + 1) + (C.γ (i + 1))⁻¹ • C.er (i + 1) -
        C.A *ᵥ C.ep i + C.δ i • C.es i - (C.δ i / C.γ i) • C.er i +
        (ρ ^ 2 / ρ' ^ 2 / γ' - δ / γ') • (C.r i - C.r (i + 1)))‖
      ≤ ‖WithLp.toLp 2 (C.es (i + 1))‖ + ‖WithLp.toLp 2 ((C.γ (i + 1))⁻¹ • C.er (i + 1))‖ +
        ‖WithLp.toLp 2 (C.A *ᵥ C.ep i)‖ + ‖WithLp.toLp 2 (C.δ i • C.es i)‖ +
        ‖WithLp.toLp 2 ((C.δ i / C.γ i) • C.er i)‖ +
        ‖WithLp.toLp 2 ((ρ ^ 2 / ρ' ^ 2 / γ' - δ / γ') • (C.r i - C.r (i + 1)))‖ := by
      refine (norm_toLp_add_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_toLp_sub_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_toLp_add_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_toLp_sub_le _ _).trans (add_le_add_left ?_ _)
      refine (norm_toLp_add_le _ _).trans (le_of_eq ?_)
      rw [WithLp.toLp_neg, norm_neg]
  have hpP : p ≤ P * ρ := hP
  have hfin1 : C.ε * (γ⁻¹ * ρ) ≤ C.ε * (21 / 20 * N * P ^ 2 * ρ) := by gcongr
  have hNp : N * p ≤ N * (P * ρ) := mul_le_mul_of_nonneg_left hpP hN
  have hND : N * D ≤ N * (21 / 20 * (P * ρ + ρ)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hD, hpP]) hN
  have hNp0 : 0 ≤ N * p := mul_nonneg hN hp0
  have hND0 : 0 ≤ N * D := mul_nonneg hN hD0
  have hBρ0 : 0 ≤ B * ρ := mul_nonneg hB0 hρ.le
  have hεNp : C.ε * N * p ≤ C.ε * (N * (P * ρ)) := by
    have := mul_le_mul_of_nonneg_left hNp hε0
    linarith
  have hεNp' : C.ε * ((1 + C.ε) * N * p) ≤ C.ε * (2 * (N * (P * ρ))) := by
    have h1 : (1 + C.ε) * (N * p) ≤ 2 * (N * (P * ρ)) :=
      (mul_le_mul_of_nonneg_right (show 1 + C.ε ≤ 2 by linarith) hNp0).trans
        (show 2 * (N * p) ≤ 2 * (N * (P * ρ)) by linarith)
    have := mul_le_mul_of_nonneg_left h1 hε0
    linarith
  have hεND : C.ε * N * D ≤ C.ε * (N * (21 / 20 * (P * ρ + ρ))) := by
    have := mul_le_mul_of_nonneg_left hND hε0
    linarith
  have hεND' : C.ε * ((1 + C.ε) * N * D) ≤ C.ε * (2 * (N * (21 / 20 * (P * ρ + ρ)))) := by
    have h1 : (1 + C.ε) * (N * D) ≤ 2 * (N * (21 / 20 * (P * ρ + ρ))) :=
      (mul_le_mul_of_nonneg_right (show 1 + C.ε ≤ 2 by linarith) hND0).trans
        (show 2 * (N * D) ≤ 2 * (N * (21 / 20 * (P * ρ + ρ))) by linarith)
    have := mul_le_mul_of_nonneg_left h1 hε0
    linarith
  have hεNρD : N * (C.ε * (ρ + D)) ≤ C.ε * (N * ρ + N * (21 / 20 * (P * ρ + ρ))) := by
    have := mul_le_mul_of_nonneg_left hND hε0
    linarith
  have hB1 : C.ε * ((1 + 31 / 10 * C.ε) * B * ρ) ≤ C.ε * (1031 / 1000 * (B * ρ)) := by
    have : (1 + 31 / 10 * C.ε) * (B * ρ) ≤ 1031 / 1000 * (B * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) hBρ0
    have := mul_le_mul_of_nonneg_left this hε0
    linarith
  have hB2 : 31 / 10 * C.ε * (ρ * B + (1 + 16 / 5 * C.ε) * B * ρ) ≤
      C.ε * (6 * (B * ρ) + 3 / 10 * (B * ρ)) := by
    have h1 : (1 + 16 / 5 * C.ε) * (B * ρ) ≤ (1 + 32 / 1000) * (B * ρ) :=
      mul_le_mul_of_nonneg_right (by linarith) hBρ0
    have h2 : 31 / 10 * (ρ * B + (1 + 16 / 5 * C.ε) * B * ρ) ≤ 6 * (B * ρ) + 3 / 10 * (B * ρ) := by
      linarith
    have := mul_le_mul_of_nonneg_left h2 hε0
    linarith
  have hpoly : N * (P * ρ) + 21 / 20 * N * P ^ 2 * ρ + 2 * (N * (P * ρ)) + (N * ρ +
      N * (21 / 20 * (P * ρ + ρ))) + N * (21 / 20 * (P * ρ + ρ)) +
      2 * (N * (21 / 20 * (P * ρ + ρ))) ≤ 8 * (N * (1 + P) ^ 2) * ρ := by
    have h1 : 0 ≤ N * ρ := mul_nonneg hN hρ.le
    have h2 : 0 ≤ N * ρ * P := mul_nonneg h1 hP0
    have h3 : 0 ≤ N * ρ * P ^ 2 := mul_nonneg h1 (sq_nonneg P)
    linarith only [h1, h2, h3]
  have hfinal : C.ε * (N * (P * ρ) + 21 / 20 * N * P ^ 2 * ρ + 2 * (N * (P * ρ)) + (N * ρ +
      N * (21 / 20 * (P * ρ + ρ))) + N * (21 / 20 * (P * ρ + ρ)) +
      2 * (N * (21 / 20 * (P * ρ + ρ)))) ≤ C.ε * (8 * (N * (1 + P) ^ 2) * ρ) :=
    mul_le_mul_of_nonneg_left hpoly hε0
  have hBρ' : C.ε * (6 * (B * ρ) + 3 / 10 * (B * ρ)) + C.ε * (1031 / 1000 * (B * ρ)) ≤
      C.ε * (8 * B * ρ) := by
    have := mul_nonneg hε0 hBρ0
    linarith only [this]
  have e : 8 * C.ε * (N * (1 + P) ^ 2 + B) * ρ =
      C.ε * (8 * (N * (1 + P) ^ 2) * ρ) + C.ε * (8 * B * ρ) := by ring
  rw [e]
  linarith only [hsum, t1, t2, t3, t4, t5, t6, hfin1, hεNp, hεNp', hεND, hεND', hεNρD, hB1, hB2,
    hfinal, hBρ']

/-- The coefficient certificate is nonnegative unless $k = 1$ (when it is vacuous):
$0 < \beta_1 \le B$ for $k \ge 2$. -/
private theorem nonneg_of_certificate {B : ℝ}
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) : 0 ≤ B ∨ k = 1 := by
  by_cases hk : k = 1
  · exact Or.inr hk
  · exact Or.inl ((C.lanczosβ_pos le_rfl (by have := C.k_pos; omega)).le.trans
      (hB 0 (by have := C.k_pos; omega)).1)

/-- The first step of Lemma A: $\|\bar{\mathbf{f}}_0\| \le 8\varepsilon\|\mathbf{A}\|_2(1+\Pi)^2$. -/
private theorem norm_recurrenceError_zero_le {P : ℝ}
    (hP : ‖WithLp.toLp 2 (C.p 0)‖ ≤ P * C.ρ 0) :
    ‖WithLp.toLp 2 (C.toLanczosData.recurrenceError 0)‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2) := by
  have hk := C.k_pos
  have hγ := C.γ_pos hk
  have hρ := C.ρ_pos hk
  have hN := specNorm_nonneg C.A
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p 0))
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ
    linarith
  rw [C.recurrenceError_zero, norm_toLp_smul, abs_inv, abs_of_pos hρ]
  have t := norm_toLp_add_le (-C.es 0) ((C.γ 0)⁻¹ • C.er 0)
  rw [WithLp.toLp_neg, norm_neg, norm_toLp_smul, abs_inv, abs_of_pos hγ] at t
  have t1 := C.norm_es_le 0 hk
  have t2 := mul_le_mul_of_nonneg_left (C.norm_er_le' hk) (inv_nonneg.2 hγ.le)
  have hs := C.norm_s_le hk
  have hinv := C.inv_γ_le hk hP
  have e : (C.γ 0)⁻¹ * (C.ε * (C.ρ 0 + C.γ 0 * ‖WithLp.toLp 2 (C.s 0)‖)) =
      C.ε * ((C.γ 0)⁻¹ * C.ρ 0) + C.ε * ‖WithLp.toLp 2 (C.s 0)‖ := by
    field_simp
  rw [e] at t2
  have h1 : C.ε * ((C.γ 0)⁻¹ * C.ρ 0) ≤ C.ε * (21 / 20 * specNorm C.A * P ^ 2 * C.ρ 0) := by
    gcongr
  have h2 : C.ε * ‖WithLp.toLp 2 (C.s 0)‖ ≤ C.ε * (2 * specNorm C.A * (P * C.ρ 0)) := by
    gcongr
    calc _ ≤ _ := hs
      _ ≤ 2 * specNorm C.A * (P * C.ρ 0) := by gcongr; linarith
  have h3 : C.ε * specNorm C.A * ‖WithLp.toLp 2 (C.p 0)‖ ≤ C.ε * specNorm C.A * (P * C.ρ 0) := by
    gcongr
  have hpoly : C.ε * (specNorm C.A * (P * C.ρ 0)) + C.ε * (21 / 20 * specNorm C.A * P ^ 2 * C.ρ 0) +
      C.ε * (2 * specNorm C.A * (P * C.ρ 0)) ≤ 8 * C.ε * (specNorm C.A * (1 + P) ^ 2) * C.ρ 0 := by
    have a1 : 0 ≤ C.ε * specNorm C.A * C.ρ 0 := by positivity
    have a2 : 0 ≤ C.ε * specNorm C.A * C.ρ 0 * P := by positivity
    have a3 : 0 ≤ C.ε * specNorm C.A * C.ρ 0 * P ^ 2 := by positivity
    linarith only [a1, a2, a3]
  rw [inv_mul_le_iff₀ hρ]
  linarith only [t, t1, t2, h1, h2, h3, hpoly]

/-- **Lemma A with a nonnegative certificate** $B \ge 0$: the form of
`NLAlib.CGRun.norm_recurrenceError_le` that holds for every $k$ (for $k \ge 2$, $B \ge 0$
follows from $\beta_1 \le B$). -/
theorem norm_recurrenceError_le_of_nonneg {P B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) (hB0 : 0 ≤ B) {j : ℕ}
    (hj : j < k) :
    ‖WithLp.toLp 2 (C.toLanczosData.recurrenceError j)‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B) := by
  rcases j with _ | i
  · have h := C.norm_recurrenceError_zero_le (hP 0 C.k_pos)
    have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) C.ε_nonneg) hB0
    nlinarith
  · have hρ := C.ρ_pos hj
    obtain ⟨hβ, hδ⟩ := hB i hj
    have h := C.norm_recurrenceError_succ_mul_le hj (hP (i + 1) hj) hβ hδ
    rw [C.recurrenceError_succ hj, norm_toLp_smul, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
      one_mul, abs_inv, abs_of_pos hρ, inv_mul_le_iff₀ hρ]
    linarith

/-- **Lemma A (recurrence error)**: with certificates $\|\mathbf{p}_j\| \le \Pi\rho_j$
($j < k$) and $\beta_{j+1}, \delta_j/\gamma_j \le B$ ($j + 1 < k$), the Lanczos data of the
run satisfy
$$\|\bar{\mathbf{f}}_j\| \le 8\varepsilon\bigl(\|\mathbf{A}\|_2(1 + \Pi)^2 + B\bigr),
\qquad j < k .$$
No residual ratio enters. No printed source; the research note `HSCG-FiniteP.md` §2.4, after
[GreenbaumLiuChen2021, (2.2)–(2.4)], who derive the perturbation term but do not bound it.
Proof: the exact identity $\mathbf{A}\mathbf{r}_j = (\gamma_j^{-1} + \delta_{j-1}/\gamma_{j-1})
\mathbf{r}_j - \gamma_j^{-1}\mathbf{r}_{j+1} - (\delta_{j-1}/\gamma_{j-1})\mathbf{r}_{j-1} +
\mathbf{g}_j$ in the computed data (eliminate $\mathbf{A}\mathbf{p}_j$ between the residual and
direction updates), normalise by $(-1)^j/\rho_j$, then the term table of the note; the
diagonal convention of `NLAlib.cgTridiagonal` adds $\le 3.2\varepsilon\,\delta_{j-1}/
\gamma_{j-1}$, and $\gamma_j^{-1} \le 1.05\|\mathbf{A}\|_2\pi_j^2$ (`C.ρ_sq_le`). Step $j$
uses $B$ only for $\beta_j$ and $\delta_{j-1}/\gamma_{j-1}$ (index $j - 1$, so $j - 1 + 1 < k$);
$\beta_{j+1}$ enters $\bar{\mathbf{f}}_j$ only through the exact cancellation
$\beta_{j+1}\bar{\mathbf{v}}_{j+2} = (-1)^{j+1}\mathbf{r}_{j+1}/(\gamma_j\rho_j)$.
Difficulty: hard (one identity, then about ten norm estimates). -/
theorem norm_recurrenceError_le {P B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.toLanczosData.recurrenceError j)‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B) := by
  rcases C.nonneg_of_certificate hB with hB0 | hk
  · exact C.norm_recurrenceError_le_of_nonneg hP hB hB0 hj
  · -- `k = 1` and `B < 0`: the statement is false (the right side can be negative while
    -- `‖f₀‖ > 0`); see `NLAlib.CGRun.norm_recurrenceError_le_of_nonneg`.
    sorry

/-- The line search identity of a step taken, before the direction update:
$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1} = \mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j -
\rho_j^2(1+\theta_j)(1+\eta^\gamma_j) + \gamma_je^\mu_j + \mathbf{p}_j^{\mathsf{T}}\mathbf{e}^r_j$. -/
private theorem p_dotProduct_r_succ_eq {j : ℕ} (hj : j < k) :
    C.p j ⬝ᵥ C.r (j + 1) = C.p j ⬝ᵥ C.r j - C.ρ j ^ 2 * (1 + C.θ j) * (1 + C.eγ j) +
      C.γ j * C.eμ j + C.p j ⬝ᵥ C.er j := by
  have h1 : C.p j ⬝ᵥ C.s j = C.μ j - C.eμ j := by rw [C.μ_eq j hj]; ring
  have h2 := C.γ_mul_μ hj
  rw [C.ν_eq' hj.le] at h2
  rw [C.r_succ j hj, dotProduct_add, dotProduct_sub, dotProduct_smul, h1, smul_eq_mul]
  linear_combination -h2

/-- The direction against its own residual: $\mathbf{p}_0^{\mathsf{T}}\mathbf{r}_0 = \rho_0^2$
and $\mathbf{p}_{i+1}^{\mathsf{T}}\mathbf{r}_{i+1} = \rho_{i+1}^2 +
\delta_i\mathbf{p}_i^{\mathsf{T}}\mathbf{r}_{i+1} + \mathbf{e}^{p\mathsf{T}}_i\mathbf{r}_{i+1}$. -/
private theorem p_dotProduct_r_self_zero : C.p 0 ⬝ᵥ C.r 0 = C.ρ 0 ^ 2 := by
  rw [C.p_zero, ← C.r_zero, ρ, norm_toLp_sq]

private theorem p_dotProduct_r_self_succ {i : ℕ} (hi : i < k) :
    C.p (i + 1) ⬝ᵥ C.r (i + 1) =
      C.ρ (i + 1) ^ 2 + C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) + C.ep i ⬝ᵥ C.r (i + 1) := by
  rw [C.p_succ i hi, add_dotProduct, add_dotProduct, smul_dotProduct, ρ, norm_toLp_sq,
    smul_eq_mul]

/-- The local term of the line search recursion,
$\lvert -\rho_j^2(\theta_j + \eta^\gamma_j + \theta_j\eta^\gamma_j) + \gamma_je^\mu_j +
\mathbf{p}_j^{\mathsf{T}}\mathbf{e}^r_j\rvert \le \varepsilon(2.01 + \Pi + 2.02K)\rho_j^2$. -/
private theorem abs_lineSearch_local_le {P K : ℝ} {j : ℕ} (hj : j < k)
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2) :
    |-(C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)) + C.γ j * C.eμ j + C.p j ⬝ᵥ C.er j| ≤
      C.ε * (201 / 100 + P + 202 / 100 * K) * C.ρ j ^ 2 := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hθ := C.abs_θ_le j hj.le
  have he := C.abs_eγ_le j hj
  have hs := C.norm_s_le hj
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hN := specNorm_nonneg C.A
  set p := ‖WithLp.toLp 2 (C.p j)‖
  set G := specNorm C.A * C.γ j * p ^ 2
  have hG0 : 0 ≤ G := by positivity
  have a1 : |C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)| ≤ 201 / 100 * C.ε * C.ρ j ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ C.ρ j ^ 2)]
    have : |C.θ j + C.eγ j + C.θ j * C.eγ j| ≤ 201 / 100 * C.ε := by
      have h1 := abs_add_three (C.θ j) (C.eγ j) (C.θ j * C.eγ j)
      rw [abs_mul] at h1
      have h2 := mul_le_mul hθ he (abs_nonneg _) hε0
      nlinarith
    nlinarith
  have hsp : C.γ j * (p * ‖WithLp.toLp 2 (C.s j)‖) ≤ (1 + C.ε) * G := by
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg hγ.le hp0)
    calc _ = C.γ j * p * ‖WithLp.toLp 2 (C.s j)‖ := by ring
      _ ≤ _ := this
      _ = _ := by ring
  have a2 : |C.γ j * C.eμ j| ≤ C.ε * ((1 + C.ε) * G) := by
    rw [abs_mul, abs_of_pos hγ]
    have := mul_le_mul_of_nonneg_left (C.abs_eμ_le j hj) hγ.le
    calc _ ≤ _ := this
      _ = C.ε * (C.γ j * (p * ‖WithLp.toLp 2 (C.s j)‖)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hsp hε0
  have a3 : |C.p j ⬝ᵥ C.er j| ≤ C.ε * (p * C.ρ j) + C.ε * ((1 + C.ε) * G) := by
    refine (abs_dotProduct_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left (C.norm_er_le' hj) hp0
    calc _ ≤ _ := this
      _ = C.ε * (p * C.ρ j) + C.ε * (C.γ j * (p * ‖WithLp.toLp 2 (C.s j)‖)) := by ring
      _ ≤ _ := by gcongr
  have hpρ : p * C.ρ j ≤ P * C.ρ j ^ 2 := by
    have := mul_le_mul_of_nonneg_right hP hρ.le
    linarith
  have hG : (1 + C.ε) * G ≤ 101 / 100 * (K * C.ρ j ^ 2) :=
    (mul_le_mul_of_nonneg_right (by linarith) hG0).trans
      (mul_le_mul_of_nonneg_left hK (by norm_num))
  have b1 := mul_le_mul_of_nonneg_left hpρ hε0
  have b2 := mul_le_mul_of_nonneg_left hG hε0
  have t := abs_add_three (-(C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j))) (C.γ j * C.eμ j)
    (C.p j ⬝ᵥ C.er j)
  rw [abs_neg] at t
  linarith only [t, a1, a2, a3, b1, b2]

/-- The direction-update term of the line search recursion:
$\lvert\mathbf{e}^{p\mathsf{T}}_i\mathbf{r}_{i+1}\rvert \le \varepsilon(2.05 + 1.05\Pi)
\rho_{i+1}^2$. -/
private theorem abs_ep_dotProduct_r_le {P : ℝ} {i : ℕ} (hi : i < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1)) :
    |C.ep i ⬝ᵥ C.r (i + 1)| ≤ C.ε * (41 / 20 + 21 / 20 * P) * C.ρ (i + 1) ^ 2 := by
  have hε0 := C.ε_nonneg
  have hρ := C.ρ_nonneg (i + 1)
  have hD := C.δ_mul_norm_p_le hi
  have h1 := mul_le_mul_of_nonneg_right (C.norm_ep_le' hi) hρ
  refine (abs_dotProduct_le _ _).trans (h1.trans ?_)
  have h2 : C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖ ≤ (41 / 20 + 21 / 20 * P) * C.ρ (i + 1) :=
    by nlinarith
  have := mul_le_mul_of_nonneg_left h2 hε0
  have := mul_le_mul_of_nonneg_right this hρ
  simp only [ρ] at *
  nlinarith

/-- **The line search defect** [StrakosTichy2002, Theorem 9.1], a posteriori: with certificates
$\|\mathbf{p}_i\| \le \Pi\rho_i$ and $\|\mathbf{A}\|_2\gamma_i\|\mathbf{p}_i\|^2 \le K\rho_i^2$
($i \le j < k$),
$$\lvert\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1}\rvert \le
5(j+1)\varepsilon(1 + \Pi + K)\rho_j^2 .$$
Strakoš and Tichý state it with $\kappa(\mathbf{A})$ and $+O(\varepsilon^2)$, using an imported
bound on residual ratios; in normalised form the multipliers telescope and no ratio enters.
Proof: $\tau_j = \delta_{j-1}\tau_{j-1} + M_j$ with
$\lvert M_j\rvert \le \varepsilon(4.1 + 2.1\pi_j + 2.1\kappa_j)\rho_j^2$ (the updates and
$\gamma_j\mu_j = \nu_j(1+\eta^\gamma_j)$), and
$\delta_{j-1}\rho_{j-1}^2 = \rho_j^2(1 + O(\varepsilon))$;
unroll. Difficulty: moderate. -/
theorem abs_p_dotProduct_r_succ_le {P K : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r (j + 1)| ≤ 5 * (j + 1) * C.ε * (1 + P + K) * C.ρ j ^ 2 := by
  have hk := C.k_pos
  have hρ0 := C.ρ_pos hk
  have hε0 := C.ε_nonneg
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ0
    linarith [norm_nonneg (WithLp.toLp 2 (C.p 0)), hP 0 hk]
  have hK0 : 0 ≤ K := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h (pow_pos hρ0 2)
    have : 0 ≤ specNorm C.A * C.γ 0 * ‖WithLp.toLp 2 (C.p 0)‖ ^ 2 :=
      mul_nonneg (mul_nonneg (specNorm_nonneg _) (C.γ_pos hk).le) (sq_nonneg _)
    linarith [hK 0 hk]
  have hX : 0 ≤ 1 + P + K := by linarith
  induction j with
  | zero =>
    have h := C.abs_lineSearch_local_le hk (hP 0 hk) (hK 0 hk)
    have e : C.p 0 ⬝ᵥ C.r (0 + 1) = -(C.ρ 0 ^ 2 * (C.θ 0 + C.eγ 0 + C.θ 0 * C.eγ 0)) +
        C.γ 0 * C.eμ 0 + C.p 0 ⬝ᵥ C.er 0 := by
      rw [C.p_dotProduct_r_succ_eq hk, C.p_dotProduct_r_self_zero]
      ring
    rw [e]
    refine h.trans ?_
    have : 201 / 100 + P + 202 / 100 * K ≤ 5 * ((0 : ℕ) + 1 : ℝ) * (1 + P + K) := by
      push_cast
      linarith
    have := mul_le_mul_of_nonneg_left this hε0
    have := mul_le_mul_of_nonneg_right this (sq_nonneg (C.ρ 0))
    linarith
  | succ i ih =>
    have hi : i < k := by omega
    have ih := ih hi
    have h1 := C.abs_lineSearch_local_le hj (hP (i + 1) hj) (hK (i + 1) hj)
    have h2 := C.abs_ep_dotProduct_r_le hi (hP (i + 1) hj)
    obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi
    have e : C.p (i + 1) ⬝ᵥ C.r (i + 1 + 1) = C.δ i * (C.p i ⬝ᵥ C.r (i + 1)) +
        C.ep i ⬝ᵥ C.r (i + 1) + (-(C.ρ (i + 1) ^ 2 * (C.θ (i + 1) + C.eγ (i + 1) +
          C.θ (i + 1) * C.eγ (i + 1))) + C.γ (i + 1) * C.eμ (i + 1) +
          C.p (i + 1) ⬝ᵥ C.er (i + 1)) := by
      rw [C.p_dotProduct_r_succ_eq hj, C.p_dotProduct_r_self_succ hi]
      ring
    rw [e]
    have t := abs_add_three (C.δ i * (C.p i ⬝ᵥ C.r (i + 1))) (C.ep i ⬝ᵥ C.r (i + 1))
      (-(C.ρ (i + 1) ^ 2 * (C.θ (i + 1) + C.eγ (i + 1) + C.θ (i + 1) * C.eγ (i + 1))) +
        C.γ (i + 1) * C.eμ (i + 1) + C.p (i + 1) ⬝ᵥ C.er (i + 1))
    rw [abs_mul, abs_of_nonneg hδ0] at t
    set ρ := C.ρ (i + 1)
    set Y := 5 * ((i : ℕ) + 1 : ℝ) * C.ε * (1 + P + K)
    have hY0 : 0 ≤ Y := by positivity
    have h3 : C.δ i * |C.p i ⬝ᵥ C.r (i + 1)| ≤ Y * ((1 + 31 / 10 * C.ε) * ρ ^ 2) := by
      calc C.δ i * |C.p i ⬝ᵥ C.r (i + 1)| ≤ C.δ i * (Y * C.ρ i ^ 2) :=
            mul_le_mul_of_nonneg_left ih hδ0
        _ = Y * (C.δ i * C.ρ i ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hδ1 hY0
    have hiε : ((i : ℕ) + 1 : ℝ) * C.ε ≤ 1 / 100 := by
      have := C.mul_ε_le' (j := i + 1) hj.le
      exact_mod_cast this
    have h4 : Y * (31 / 10 * C.ε) ≤ 155 / 1000 * C.ε * (1 + P + K) := by
      have : Y * (31 / 10 * C.ε) = 31 / 2 * (((i : ℕ) + 1 : ℝ) * C.ε) * (C.ε * (1 + P + K)) := by
        simp only [Y]
        ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hiε (mul_nonneg hε0 hX)
      linarith
    have h5 : 5 * (((i + 1 : ℕ) : ℝ) + 1) * C.ε * (1 + P + K) = Y + 5 * C.ε * (1 + P + K) := by
      simp only [Y]
      push_cast
      ring
    rw [h5]
    have hρ2 : 0 ≤ ρ ^ 2 := sq_nonneg _
    have h6 := mul_le_mul_of_nonneg_right h4 hρ2
    have h7 : C.ε * (41 / 20 + 21 / 20 * P) * ρ ^ 2 + C.ε * (201 / 100 + P + 202 / 100 * K) * ρ ^ 2 +
        155 / 1000 * C.ε * (1 + P + K) * ρ ^ 2 ≤ 5 * C.ε * (1 + P + K) * ρ ^ 2 := by
      have : (41 / 20 + 21 / 20 * P) + (201 / 100 + P + 202 / 100 * K) +
          155 / 1000 * (1 + P + K) ≤ 5 * (1 + P + K) := by linarith
      have := mul_le_mul_of_nonneg_left this hε0
      have := mul_le_mul_of_nonneg_right this hρ2
      linarith
    have h3' : Y * ((1 + 31 / 10 * C.ε) * ρ ^ 2) = Y * ρ ^ 2 + Y * (31 / 10 * C.ε) * ρ ^ 2 := by
      ring
    linarith only [t, h1, h2, h3, h3', h6, h7]

/-- The adjacent inner product of the run's Lanczos data:
$\bar p_j = -\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_{j+1}/(\gamma_j\rho_j^2)$. -/
private theorem adjacentInner_eq {j : ℕ} (hj : j < k) :
    C.toLanczosData.adjacentInner j = -(C.r j ⬝ᵥ C.r (j + 1)) / (C.γ j * C.ρ j ^ 2) := by
  have hγ := (C.γ_pos hj).ne'
  have hρ := (C.ρ_pos hj).ne'
  simp only [LanczosData.adjacentInner, toLanczosData]
  rw [C.lanczosβ_smul_lanczosV hj, C.lanczosV_succ hj, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul]
  have : (-1 : ℝ) ^ (j * 2) = 1 := by rw [mul_comm, pow_mul, neg_one_sq, one_pow]
  field_simp
  linear_combination (-(C.r j ⬝ᵥ C.r (j + 1))) * this

/-- The consecutive residuals of a step taken:
$\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_{j+1} = \rho_j^2 - \gamma_j\mathbf{r}_j^{\mathsf{T}}\mathbf{s}_j
+ \mathbf{r}_j^{\mathsf{T}}\mathbf{e}^r_j$. -/
private theorem r_dotProduct_r_succ_eq {j : ℕ} (hj : j < k) :
    C.r j ⬝ᵥ C.r (j + 1) = C.ρ j ^ 2 - C.γ j * (C.r j ⬝ᵥ C.s j) + C.r j ⬝ᵥ C.er j := by
  rw [C.r_succ j hj, dotProduct_add, dotProduct_sub, dotProduct_smul, ρ, norm_toLp_sq,
    smul_eq_mul]

/-- The local part $R_j = -\rho_j^2(\theta_j + \eta^\gamma_j + \theta_j\eta^\gamma_j) +
\gamma_je^\mu_j + \mathbf{r}_j^{\mathsf{T}}\mathbf{e}^r_j$ of the consecutive-residual identity. -/
private noncomputable def localR (j : ℕ) : ℝ :=
  -(C.ρ j ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j)) + C.γ j * C.eμ j + C.r j ⬝ᵥ C.er j

/-- The first consecutive residuals: $\mathbf{r}_0^{\mathsf{T}}\mathbf{r}_1 = R_0$. -/
private theorem r_dotProduct_r_one_eq : C.r 0 ⬝ᵥ C.r (0 + 1) = C.localR 0 := by
  have hk := C.k_pos
  have h1 : C.r 0 ⬝ᵥ C.s 0 = C.μ 0 - C.eμ 0 := by
    rw [C.μ_eq 0 hk, C.p_zero, ← C.r_zero]
    ring
  have h2 := C.γ_mul_μ hk
  rw [C.ν_eq' hk.le] at h2
  rw [C.r_dotProduct_r_succ_eq hk, h1, localR]
  linear_combination -h2

/-- The conjugacy defect $\zeta_{i+1} = \mathbf{p}_i^{\mathsf{T}}\mathbf{s}_{i+1}$ transports the
previous consecutive residuals: $\gamma_i\zeta_{i+1} = \mathbf{r}_i^{\mathsf{T}}\mathbf{r}_{i+1} +
S_{i+1}$ (one use of $\mathbf{A}^{\mathsf{T}} = \mathbf{A}$). -/
private theorem γ_mul_p_dotProduct_s_succ_eq {i : ℕ} (hi : i + 1 < k) :
    C.γ i * (C.p i ⬝ᵥ C.s (i + 1)) = C.r i ⬝ᵥ C.r (i + 1) +
      ((C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1))) := by
  have hi' : i < k := by omega
  have hγ := (C.γ_pos hi').ne'
  -- symmetry
  have hsym : C.p i ⬝ᵥ (C.A *ᵥ C.p (i + 1)) = (C.A *ᵥ C.p i) ⬝ᵥ C.p (i + 1) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, C.transpose_A, dotProduct_comm]
  have hz : C.p i ⬝ᵥ C.s (i + 1) =
      (C.γ i)⁻¹ * ((C.r i - C.r (i + 1)) ⬝ᵥ C.p (i + 1) + C.er i ⬝ᵥ C.p (i + 1)) -
        C.es i ⬝ᵥ C.p (i + 1) + C.p i ⬝ᵥ C.es (i + 1) := by
    rw [C.s_eq (i + 1) hi, dotProduct_add, hsym, C.mulVec_p_eq hi', sub_dotProduct,
      smul_dotProduct, add_dotProduct, smul_eq_mul]
  -- the direction update against the residual difference
  have hpr : (C.r i - C.r (i + 1)) ⬝ᵥ C.p (i + 1) = C.r i ⬝ᵥ C.r (i + 1) +
      C.δ i * (C.p i ⬝ᵥ (C.r i - C.r (i + 1))) - C.ρ (i + 1) ^ 2 +
      (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i := by
    rw [C.p_succ i hi', dotProduct_add, dotProduct_add, dotProduct_smul, sub_dotProduct,
      sub_dotProduct, ρ, norm_toLp_sq, smul_eq_mul, dotProduct_comm (C.r i) (C.p i),
      dotProduct_comm (C.r (i + 1)) (C.p i), dotProduct_sub]
    ring
  have hpd : C.p i ⬝ᵥ (C.r i - C.r (i + 1)) =
      C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i) - C.γ i * C.eμ i - C.p i ⬝ᵥ C.er i := by
    have h1 := C.p_dotProduct_r_succ_eq hi'
    rw [dotProduct_sub]
    linarith
  rw [hz, hpr, hpd]
  field_simp
  ring

/-- **The consecutive-residual recursion**:
$\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_{j+1} = (\gamma_j\delta_i/\gamma_i)(\mathbf{r}_i^{\mathsf{T}}
\mathbf{r}_j + S_j) + R_j + \gamma_j\mathbf{e}^{p\mathsf{T}}_i\mathbf{s}_j$, $j = i + 1 < k$. -/
private theorem r_dotProduct_r_succ_succ_eq {i : ℕ} (hi : i + 1 < k) :
    C.r (i + 1) ⬝ᵥ C.r (i + 1 + 1) = C.γ (i + 1) * C.δ i / C.γ i *
      (C.γ i * (C.p i ⬝ᵥ C.s (i + 1))) + C.localR (i + 1) +
        C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1)) := by
  have hi' : i < k := by omega
  have hγ := (C.γ_pos hi').ne'
  have h1 : C.r (i + 1) ⬝ᵥ C.s (i + 1) =
      C.μ (i + 1) - C.eμ (i + 1) - C.δ i * (C.p i ⬝ᵥ C.s (i + 1)) - C.ep i ⬝ᵥ C.s (i + 1) := by
    have hr : C.r (i + 1) = C.p (i + 1) - C.δ i • C.p i - C.ep i := by
      rw [C.p_succ i hi']
      abel
    rw [hr, sub_dotProduct, sub_dotProduct, smul_dotProduct, C.μ_eq (i + 1) hi, smul_eq_mul]
    ring
  have h2 := C.γ_mul_μ hi
  rw [C.ν_eq' hi.le] at h2
  rw [C.r_dotProduct_r_succ_eq hi, h1, localR]
  field_simp
  linear_combination -h2

/-- $\lvert(1+x)(1+y)(1+z) - 1\rvert \le 3.04\varepsilon$ for $\lvert x\rvert, \lvert y\rvert,
\lvert z\rvert \le \varepsilon \le 1/100$. -/
private theorem abs_one_add_mul_three_sub_one_le {x y z ε : ℝ} (hx : |x| ≤ ε) (hy : |y| ≤ ε)
    (hz : |z| ≤ ε) (hε : ε ≤ 1 / 100) :
    |(1 + x) * (1 + y) * (1 + z) - 1| ≤ 304 / 100 * ε := by
  have hε0 : 0 ≤ ε := (abs_nonneg x).trans hx
  have e : (1 + x) * (1 + y) * (1 + z) - 1 = x + y + z + (x * y + y * z + x * z) + x * y * z := by
    ring
  rw [e]
  have h1 : |x * y| ≤ ε * ε := by rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) hε0
  have h2 : |y * z| ≤ ε * ε := by rw [abs_mul]; exact mul_le_mul hy hz (abs_nonneg _) hε0
  have h3 : |x * z| ≤ ε * ε := by rw [abs_mul]; exact mul_le_mul hx hz (abs_nonneg _) hε0
  have h4 : |x * y * z| ≤ ε * ε * ε := by
    rw [abs_mul]; exact mul_le_mul h1 hz (abs_nonneg _) (by positivity)
  have t1 := abs_add_three x y z
  have t2 := abs_add_three (x * y) (y * z) (x * z)
  have t3 := abs_add_le (x + y + z + (x * y + y * z + x * z)) (x * y * z)
  have t4 := abs_add_le (x + y + z) (x * y + y * z + x * z)
  have hεε : ε * ε ≤ 1 / 100 * ε := mul_le_mul_of_nonneg_right hε hε0
  have hεεε : ε * ε * ε ≤ 1 / 100 * ε := by
    have h5 := mul_le_mul_of_nonneg_right hεε hε0
    have h6 : 1 / 100 * ε * ε ≤ 1 / 100 * ε := by nlinarith
    linarith
  linarith

/-- The local part of the consecutive-residual recursion, with the direction-update term,
relative to $\|\mathbf{A}\|_2\gamma_j\rho_j^2$:
$\lvert R_j\rvert \le \varepsilon(5\Pi^2 + 2\Pi)\|\mathbf{A}\|_2\gamma_j\rho_j^2$. -/
private theorem abs_localR_le {P : ℝ} {j : ℕ} (hj : j < k)
    (hP : ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j) :
    |C.localR j| ≤ C.ε * (5 * P ^ 2 + 2 * P) * (specNorm C.A * C.γ j * C.ρ j ^ 2) := by
  have hγ := C.γ_pos hj
  have hρ := C.ρ_pos hj
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ
    linarith
  have hs := C.norm_s_le hj
  have heμ := C.abs_eμ_le j hj
  have her := C.norm_er_le' hj
  set N := specNorm C.A
  set ρ := C.ρ j
  set γ := C.γ j
  set p := ‖WithLp.toLp 2 (C.p j)‖
  set G := N * γ * ρ ^ 2 with hG
  have hG0 : 0 ≤ G := mul_nonneg (mul_nonneg hN hγ.le) (sq_nonneg ρ)
  have hp2 : p ^ 2 ≤ P ^ 2 * ρ ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hp0 hP 2
  have hNγp : N * γ * p ^ 2 ≤ P ^ 2 * G := by
    have := mul_le_mul_of_nonneg_left hp2 (mul_nonneg hN hγ.le)
    linarith only [this]
  have hρ2 : ρ ^ 2 ≤ 21 / 20 * (P ^ 2 * G) := by
    have := C.ρ_sq_le hj
    have : 21 / 20 * N * γ * p ^ 2 ≤ 21 / 20 * (P ^ 2 * G) := by linarith only [hNγp]
    linarith
  -- three terms
  have a1 : |-(ρ ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j))| ≤ C.ε * (212 / 100 * (P ^ 2 * G)) := by
    rw [abs_neg, abs_mul, abs_of_nonneg (sq_nonneg ρ)]
    have h1 : |C.θ j + C.eγ j + C.θ j * C.eγ j| ≤ 201 / 100 * C.ε := by
      have := abs_one_add_mul_three_sub_one_le (C.abs_θ_le j hj.le) (C.abs_eγ_le j hj)
        (show |(0 : ℝ)| ≤ C.ε by simpa using hε0) hε
      have e : (1 + C.θ j) * (1 + C.eγ j) * (1 + 0) - 1 = C.θ j + C.eγ j + C.θ j * C.eγ j := by
        ring
      rw [e] at this
      have h2 := abs_add_three (C.θ j) (C.eγ j) (C.θ j * C.eγ j)
      have h3 : |C.θ j * C.eγ j| ≤ C.ε * C.ε := by
        rw [abs_mul]
        exact mul_le_mul (C.abs_θ_le j hj.le) (C.abs_eγ_le j hj) (abs_nonneg _) hε0
      have := mul_le_mul_of_nonneg_right hε hε0
      linarith [C.abs_θ_le j hj.le, C.abs_eγ_le j hj]
    have := mul_le_mul h1 hρ2 (sq_nonneg _) (by linarith)
    have := mul_nonneg hε0 (mul_nonneg (sq_nonneg P) hG0)
    linarith
  have hγps : γ * (p * ‖WithLp.toLp 2 (C.s j)‖) ≤ (1 + C.ε) * (N * γ * p ^ 2) := by
    have := mul_le_mul_of_nonneg_left hs (mul_nonneg hγ.le hp0)
    linarith only [this]
  have a2 : |γ * C.eμ j| ≤ C.ε * (101 / 100 * (P ^ 2 * G)) := by
    rw [abs_mul, abs_of_pos hγ]
    have h1 := mul_le_mul_of_nonneg_left heμ hγ.le
    have h2 : (1 + C.ε) * (N * γ * p ^ 2) ≤ 101 / 100 * (P ^ 2 * G) :=
      (mul_le_mul_of_nonneg_right (by linarith : 1 + C.ε ≤ 101 / 100) (mul_nonneg (mul_nonneg hN hγ.le) (sq_nonneg p))).trans
        (mul_le_mul_of_nonneg_left hNγp (by norm_num))
    have h3 := mul_le_mul_of_nonneg_left (hγps.trans h2) hε0
    linarith only [h1, h3]
  have a3 : |C.r j ⬝ᵥ C.er j| ≤ C.ε * (21 / 20 * (P ^ 2 * G)) + C.ε * (101 / 100 * (P * G)) := by
    refine (abs_dotProduct_le _ _).trans ?_
    change ρ * ‖WithLp.toLp 2 (C.er j)‖ ≤ _
    have h1 := mul_le_mul_of_nonneg_left her hρ.le
    have h2 : ρ * (γ * ‖WithLp.toLp 2 (C.s j)‖) ≤ 101 / 100 * (P * G) := by
      have := mul_le_mul_of_nonneg_left hs (mul_nonneg hρ.le hγ.le)
      have h3 : ρ * γ * ((1 + C.ε) * N * p) ≤ ρ * γ * ((1 + C.ε) * N * (P * ρ)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hP (mul_nonneg (by linarith) hN))
          (mul_nonneg hρ.le hγ.le)
      have h4 : ρ * γ * ((1 + C.ε) * N * (P * ρ)) = (1 + C.ε) * (P * G) := by
        simp only [hG]; ring
      have h5 : (1 + C.ε) * (P * G) ≤ 101 / 100 * (P * G) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hP0 hG0)
      linarith only [this, h3, h4, h5]
    have h6 : ρ * (C.ε * (ρ + γ * ‖WithLp.toLp 2 (C.s j)‖)) =
        C.ε * ρ ^ 2 + C.ε * (ρ * (γ * ‖WithLp.toLp 2 (C.s j)‖)) := by ring
    have h7 := mul_le_mul_of_nonneg_left hρ2 hε0
    have h8 := mul_le_mul_of_nonneg_left h2 hε0
    linarith only [h1, h6, h7, h8]
  have t := abs_add_three (-(ρ ^ 2 * (C.θ j + C.eγ j + C.θ j * C.eγ j))) (γ * C.eμ j)
    (C.r j ⬝ᵥ C.er j)
  have hPG : 0 ≤ P * G := mul_nonneg hP0 hG0
  have e : C.ε * (5 * P ^ 2 + 2 * P) * G = C.ε * (5 * (P ^ 2 * G)) + C.ε * (2 * (P * G)) := by ring
  rw [localR, e]
  have hεPG := mul_nonneg hε0 hPG
  have hεP2G := mul_nonneg hε0 (mul_nonneg (sq_nonneg P) hG0)
  linarith only [t, a1, a2, a3, hεPG, hεP2G]

/-- The direction-update term of the consecutive-residual recursion:
$\gamma_j\lvert\mathbf{e}^{p\mathsf{T}}_i\mathbf{s}_j\rvert \le
\varepsilon(1.1\Pi^2 + 2.1\Pi)\|\mathbf{A}\|_2\gamma_j\rho_j^2$, $j = i + 1$. -/
private theorem abs_γ_mul_ep_dotProduct_s_le {P : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1)) :
    |C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1))| ≤
      C.ε * (11 / 10 * P ^ 2 + 21 / 10 * P) * (specNorm C.A * C.γ (i + 1) * C.ρ (i + 1) ^ 2) := by
  have hi' : i < k := by omega
  have hγ := C.γ_pos hi
  have hρ := C.ρ_pos hi
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ
    linarith [norm_nonneg (WithLp.toLp 2 (C.p (i + 1)))]
  rw [abs_mul, abs_of_pos hγ]
  have h1 := abs_dotProduct_le (C.ep i) (C.s (i + 1))
  have h2 := C.norm_ep_le' hi'
  have h3 := C.norm_s_le hi
  have hD := C.δ_mul_norm_p_le hi'
  have hep : ‖WithLp.toLp 2 (C.ep i)‖ ≤ C.ε * ((41 / 20 + 21 / 20 * P) * C.ρ (i + 1)) := by
    refine h2.trans (mul_le_mul_of_nonneg_left ?_ hε0)
    nlinarith
  have hsn : ‖WithLp.toLp 2 (C.s (i + 1))‖ ≤ 101 / 100 * specNorm C.A * (P * C.ρ (i + 1)) := by
    refine h3.trans ?_
    have := mul_le_mul_of_nonneg_left hP (mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + C.ε) hN)
    have h4 : (1 + C.ε) * specNorm C.A * (P * C.ρ (i + 1)) ≤
        101 / 100 * specNorm C.A * (P * C.ρ (i + 1)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hN) (by positivity)
    linarith
  have h5 := mul_le_mul hep hsn (norm_nonneg _) (by positivity)
  have h6 : C.ε * ((41 / 20 + 21 / 20 * P) * C.ρ (i + 1)) *
      (101 / 100 * specNorm C.A * (P * C.ρ (i + 1))) ≤
      C.ε * (11 / 10 * P ^ 2 + 21 / 10 * P) * (specNorm C.A * C.ρ (i + 1) ^ 2) := by
    have hX : 0 ≤ C.ε * specNorm C.A * C.ρ (i + 1) ^ 2 := by positivity
    have : (41 / 20 + 21 / 20 * P) * (101 / 100 * P) ≤ 11 / 10 * P ^ 2 + 21 / 10 * P := by
      nlinarith
    have := mul_le_mul_of_nonneg_left this hX
    linarith only [this]
  have h7 := mul_le_mul_of_nonneg_left (h1.trans (h5.trans h6)) hγ.le
  linarith only [h7]

/-- The coefficient ratio against $\beta_j$: $\delta_i\rho_i/\gamma_i \le (1 + 3.1\varepsilon)
\beta_{i+1}\rho_{i+1}$, so at most $(1 + 3.1\varepsilon)B\rho_{i+1}$. -/
private theorem δ_mul_ρ_div_γ_le {B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hβ : C.lanczosβ (i + 1) ≤ B) :
    C.δ i * C.ρ i / C.γ i ≤ (1 + 31 / 10 * C.ε) * B * C.ρ (i + 1) := by
  have hi' : i < k := by omega
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hε0 := C.ε_nonneg
  obtain ⟨-, hδ1, -⟩ := C.δ_bounds hi'
  have hβ' : C.ρ (i + 1) / (C.γ i * C.ρ i) ≤ B := by simpa [lanczosβ] using hβ
  have e1 : C.δ i * C.ρ i / C.γ i = C.δ i * C.ρ i ^ 2 / (C.γ i * C.ρ i) := by field_simp
  have e2 : (1 + 31 / 10 * C.ε) * C.ρ (i + 1) ^ 2 / (C.γ i * C.ρ i) =
      (1 + 31 / 10 * C.ε) * C.ρ (i + 1) * (C.ρ (i + 1) / (C.γ i * C.ρ i)) := by
    field_simp
  have hpos : 0 < C.γ i * C.ρ i := mul_pos hγ' hρ'
  have hc : 0 ≤ (1 + 31 / 10 * C.ε) * C.ρ (i + 1) :=
    mul_nonneg (by linarith) hρ.le
  rw [e1]
  calc C.δ i * C.ρ i ^ 2 / (C.γ i * C.ρ i)
      ≤ (1 + 31 / 10 * C.ε) * C.ρ (i + 1) ^ 2 / (C.γ i * C.ρ i) :=
        div_le_div_of_nonneg_right hδ1 hpos.le
    _ = (1 + 31 / 10 * C.ε) * C.ρ (i + 1) * (C.ρ (i + 1) / (C.γ i * C.ρ i)) := e2
    _ ≤ (1 + 31 / 10 * C.ε) * C.ρ (i + 1) * B := mul_le_mul_of_nonneg_left hβ' hc
    _ = _ := by ring

/-- The scalar inequality behind the bound on the transported term of Lemma B. -/
private theorem transport_scalar_le {ε N B P ρ D p q b : ℝ} (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 100)
    (hN : 0 ≤ N) (hB : 0 ≤ B) (hP : 0 ≤ P) (hρ : 0 ≤ ρ) (hD0 : 0 ≤ D) (hp0 : 0 ≤ p)
    (hq0 : 0 ≤ q) (hb0 : 0 ≤ b) (hD : D ≤ 21 / 20 * (p + ρ)) (hp : p ≤ P * ρ)
    (hq : q ≤ (1 + 31 / 10 * ε) * B * ρ) (hb : b ≤ B) :
    N * ((1 + ε) * D ^ 2 + (1 + ε) * D ^ 2 + (1 + ε) * D * p + D * p + D * p) + q * D +
      (q + b * ρ) * (ρ + D) + q * p + 304 / 100 * B * ρ ^ 2 ≤
      6 * (N * (1 + P) ^ 2 * ρ ^ 2) + 10 * (B * (1 + P) * ρ ^ 2) := by
  have hDm : D ≤ 21 / 20 * ((1 + P) * ρ) := by nlinarith
  have hpm : p ≤ (1 + P) * ρ := by nlinarith
  have hqm : q ≤ 1031 / 1000 * B * ρ := by nlinarith [mul_nonneg hB hρ]
  have hX : 0 ≤ (1 + P) * ρ := by positivity
  have hD2 : D ^ 2 ≤ (21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hD0 hDm 2
  have hDp : D * p ≤ 21 / 20 * ((1 + P) * ρ) * (P * ρ) := mul_le_mul hDm hp hp0 (by positivity)
  have hqD : q * D ≤ 1031 / 1000 * B * ρ * (21 / 20 * ((1 + P) * ρ)) :=
    mul_le_mul hqm hDm hD0 (by positivity)
  have hqp : q * p ≤ 1031 / 1000 * B * ρ * (P * ρ) := mul_le_mul hqm hp hp0 (by positivity)
  have hqb : (q + b * ρ) * (ρ + D) ≤ (1031 / 1000 * B * ρ + B * ρ) * (ρ + 21 / 20 * ((1 + P) * ρ)) :=
    mul_le_mul (by nlinarith) (by linarith) (by positivity) (by positivity)
  have hN1 : N * ((1 + ε) * D ^ 2 + (1 + ε) * D ^ 2 + (1 + ε) * D * p + D * p + D * p) ≤
      N * (2 * (101 / 100) * ((21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2) +
        (101 / 100 + 2) * (21 / 20 * ((1 + P) * ρ) * (P * ρ))) := by
    apply mul_le_mul_of_nonneg_left _ hN
    have h1 : (1 + ε) * D ^ 2 ≤ 101 / 100 * ((21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2) :=
      mul_le_mul (by linarith) hD2 (sq_nonneg _) (by norm_num)
    have h2 : (1 + ε) * D * p ≤ 101 / 100 * (21 / 20 * ((1 + P) * ρ) * (P * ρ)) := by
      rw [mul_assoc]
      exact mul_le_mul (by linarith) hDp (by positivity) (by norm_num)
    linarith
  have hN2 : N * (2 * (101 / 100) * ((21 / 20) ^ 2 * ((1 + P) * ρ) ^ 2) +
        (101 / 100 + 2) * (21 / 20 * ((1 + P) * ρ) * (P * ρ))) ≤ 6 * (N * (1 + P) ^ 2 * ρ ^ 2) := by
    have h1 : 0 ≤ N * ρ ^ 2 * P := by positivity
    have h2 : 0 ≤ N * ρ ^ 2 := by positivity
    have h3 : 0 ≤ N * ρ ^ 2 * P ^ 2 := by positivity
    nlinarith
  have hB1 : 0 ≤ B * ρ ^ 2 := by positivity
  have hB2 : 0 ≤ B * ρ ^ 2 * P := by positivity
  nlinarith

/-- **The transported term of Lemma B**: with $b = \delta_i/\gamma_i$,
$b\lvert S_{i+1}\rvert \le \varepsilon\bigl(6\|\mathbf{A}\|_2(1+\Pi)^2 + 10B(1+\Pi)\bigr)
\rho_{i+1}^2$; only $\delta_i/\gamma_i$ and $\beta_{i+1}$ enter. -/
private theorem transport_le {P B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1))
    (hβ : C.lanczosβ (i + 1) ≤ B) (hδB : C.δ i ≤ B * C.γ i) :
    C.δ i / C.γ i * |(C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| ≤
      C.ε * (6 * (specNorm C.A * (1 + P) ^ 2 * C.ρ (i + 1) ^ 2) +
        10 * (B * (1 + P) * C.ρ (i + 1) ^ 2)) := by
  have hi' : i < k := by omega
  have hγ := C.γ_pos hi
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hε := C.ε_le
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  obtain ⟨hδ0, -, -⟩ := C.δ_bounds hi'
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ
    linarith [norm_nonneg (WithLp.toLp 2 (C.p (i + 1)))]
  have hb0 : 0 ≤ C.δ i / C.γ i := div_nonneg hδ0 hγ'.le
  have hb : C.δ i / C.γ i ≤ B := by rw [div_le_iff₀ hγ']; exact hδB
  have hB0 : 0 ≤ B := hb0.trans hb
  have hq := C.δ_mul_ρ_div_γ_le hi hβ
  have hq0 : 0 ≤ C.δ i * C.ρ i / C.γ i := div_nonneg (mul_nonneg hδ0 hρ'.le) hγ'.le
  have hD := C.δ_mul_norm_p_le hi'
  have hD0 : 0 ≤ C.δ i * ‖WithLp.toLp 2 (C.p i)‖ := mul_nonneg hδ0 (norm_nonneg _)
  have hp0 := norm_nonneg (WithLp.toLp 2 (C.p (i + 1)))
  have hpi0 := norm_nonneg (WithLp.toLp 2 (C.p i))
  have hs' := C.norm_s_le hi'
  have her' := C.norm_er_le' hi'
  have hep := C.norm_ep_le' hi'
  have hes := C.norm_es_le (i + 1) hi
  have hes' := C.norm_es_le i hi'
  have heμ' := C.abs_eμ_le i hi'
  -- δ ‖s_i‖ ≤ (1 + ε) N D
  have hδs : C.δ i * ‖WithLp.toLp 2 (C.s i)‖ ≤
      (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) := by
    have := mul_le_mul_of_nonneg_left hs' hδ0
    linarith only [this]
  -- (a)
  have ha : |C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2| ≤
      304 / 100 * C.ε * C.ρ (i + 1) ^ 2 := by
    have hν : C.δ i * (C.ρ i ^ 2 * (1 + C.θ i)) = C.ρ (i + 1) ^ 2 * (1 + C.θ (i + 1)) *
        (1 + C.eδ i) := by
      have h1 := C.one_add_θ_pos hi'.le
      rw [C.δ_eq i hi', C.ν_eq' hi.le, C.ν_eq' hi'.le]
      field_simp
    have e : C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2 =
        C.ρ (i + 1) ^ 2 * ((1 + C.θ (i + 1)) * (1 + C.eδ i) * (1 + C.eγ i) - 1) := by
      linear_combination (1 + C.eγ i) * hν
    rw [e, abs_mul, abs_of_nonneg (sq_nonneg _)]
    have := abs_one_add_mul_three_sub_one_le (C.abs_θ_le (i + 1) hi.le) (C.abs_eδ_le i hi')
      (C.abs_eγ_le i hi') hε
    have := mul_le_mul_of_nonneg_left this (sq_nonneg (C.ρ (i + 1)))
    linarith only [this]
  -- (b)
  have hb' : C.δ i / C.γ i * |C.δ i * (C.γ i * C.eμ i)| ≤
      C.ε * ((1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) ^ 2) := by
    have e : C.δ i / C.γ i * |C.δ i * (C.γ i * C.eμ i)| = C.δ i ^ 2 * |C.eμ i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hδ0, abs_of_pos hγ']
      field_simp
    rw [e]
    have h1 := mul_le_mul_of_nonneg_left heμ' (sq_nonneg (C.δ i))
    have h2 : C.δ i ^ 2 * (C.ε * ‖WithLp.toLp 2 (C.p i)‖ * ‖WithLp.toLp 2 (C.s i)‖) =
        C.ε * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) * (C.δ i * ‖WithLp.toLp 2 (C.s i)‖) := by ring
    have h3 := mul_le_mul_of_nonneg_left hδs (mul_nonneg hε0 hD0)
    nlinarith
  -- (c)
  have hc : C.δ i / C.γ i * |C.δ i * (C.p i ⬝ᵥ C.er i)| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i) * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) +
        (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) ^ 2) := by
    rw [abs_mul, abs_of_nonneg hδ0]
    have h1 := abs_dotProduct_le (C.p i) (C.er i)
    have h2 := mul_le_mul_of_nonneg_left her' hpi0
    have h3 : C.δ i / C.γ i * (C.δ i * (‖WithLp.toLp 2 (C.p i)‖ *
        (C.ε * (C.ρ i + C.γ i * ‖WithLp.toLp 2 (C.s i)‖)))) =
        C.ε * ((C.δ i * C.ρ i / C.γ i) * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) +
          (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) * (C.δ i * ‖WithLp.toLp 2 (C.s i)‖)) := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_left hδs hD0
    have h5 : C.δ i / C.γ i * (C.δ i * |C.p i ⬝ᵥ C.er i|) ≤
        C.δ i / C.γ i * (C.δ i * (‖WithLp.toLp 2 (C.p i)‖ *
          (C.ε * (C.ρ i + C.γ i * ‖WithLp.toLp 2 (C.s i)‖)))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (h1.trans h2) hδ0) hb0
    rw [h3] at h5
    have h6 := mul_le_mul_of_nonneg_left h4 hε0
    nlinarith
  -- (d)
  have hd : C.δ i / C.γ i * |(C.r i - C.r (i + 1)) ⬝ᵥ C.ep i| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i + C.δ i / C.γ i * C.ρ (i + 1)) *
        (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖)) := by
    have h1 := abs_dotProduct_le (C.r i - C.r (i + 1)) (C.ep i)
    have h2 := norm_toLp_sub_le (C.r i) (C.r (i + 1))
    have h3 := mul_le_mul h2 hep (norm_nonneg _) (by positivity)
    have h4 := mul_le_mul_of_nonneg_left (h1.trans h3) hb0
    have e : C.δ i / C.γ i * ((‖WithLp.toLp 2 (C.r i)‖ + ‖WithLp.toLp 2 (C.r (i + 1))‖) *
        (C.ε * (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖))) =
        C.ε * ((C.δ i * C.ρ i / C.γ i + C.δ i / C.γ i * C.ρ (i + 1)) *
          (C.ρ (i + 1) + C.δ i * ‖WithLp.toLp 2 (C.p i)‖)) := by
      simp only [ρ]
      ring
    linarith only [h4, e]
  -- (e)
  have he : C.δ i / C.γ i * |C.er i ⬝ᵥ C.p (i + 1)| ≤
      C.ε * ((C.δ i * C.ρ i / C.γ i) * ‖WithLp.toLp 2 (C.p (i + 1))‖ +
        (1 + C.ε) * specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) *
          ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
    have h1 := abs_dotProduct_le (C.er i) (C.p (i + 1))
    have h2 := mul_le_mul_of_nonneg_right her' hp0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hb0
    have e : C.δ i / C.γ i * (C.ε * (C.ρ i + C.γ i * ‖WithLp.toLp 2 (C.s i)‖) *
        ‖WithLp.toLp 2 (C.p (i + 1))‖) = C.ε * ((C.δ i * C.ρ i / C.γ i) *
          ‖WithLp.toLp 2 (C.p (i + 1))‖ + (C.δ i * ‖WithLp.toLp 2 (C.s i)‖) *
            ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hδs hp0) hε0
    linarith only [h3, e, h4]
  -- (f), (g)
  have hf : C.δ i / C.γ i * |C.γ i * (C.es i ⬝ᵥ C.p (i + 1))| ≤
      C.ε * (specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) * ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
    have e : C.δ i / C.γ i * |C.γ i * (C.es i ⬝ᵥ C.p (i + 1))| =
        C.δ i * |C.es i ⬝ᵥ C.p (i + 1)| := by
      rw [abs_mul, abs_of_pos hγ']
      field_simp
    rw [e]
    have h1 := abs_dotProduct_le (C.es i) (C.p (i + 1))
    have h2 := mul_le_mul_of_nonneg_right hes' hp0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hδ0
    linarith only [h3]
  have hg : C.δ i / C.γ i * |C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| ≤
      C.ε * (specNorm C.A * (C.δ i * ‖WithLp.toLp 2 (C.p i)‖) * ‖WithLp.toLp 2 (C.p (i + 1))‖) := by
    have e : C.δ i / C.γ i * |C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| =
        C.δ i * |C.p i ⬝ᵥ C.es (i + 1)| := by
      rw [abs_mul, abs_of_pos hγ']
      field_simp
    rw [e]
    have h1 := abs_dotProduct_le (C.p i) (C.es (i + 1))
    have h2 := mul_le_mul_of_nonneg_left hes hpi0
    have h3 := mul_le_mul_of_nonneg_left (h1.trans h2) hδ0
    linarith only [h3]
  -- the triangle inequality
  have tri : C.δ i / C.γ i * |(C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| ≤
      C.δ i / C.γ i * |C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2| +
      C.δ i / C.γ i * |C.δ i * (C.γ i * C.eμ i)| + C.δ i / C.γ i * |C.δ i * (C.p i ⬝ᵥ C.er i)| +
      C.δ i / C.γ i * |(C.r i - C.r (i + 1)) ⬝ᵥ C.ep i| +
      C.δ i / C.γ i * |C.er i ⬝ᵥ C.p (i + 1)| +
      C.δ i / C.γ i * |C.γ i * (C.es i ⬝ᵥ C.p (i + 1))| +
      C.δ i / C.γ i * |C.γ i * (C.p i ⬝ᵥ C.es (i + 1))| := by
    simp only [← mul_add]
    refine mul_le_mul_of_nonneg_left ?_ hb0
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    refine (abs_sub _ _).trans (add_le_add_left ?_ _)
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
    refine (abs_sub _ _).trans (add_le_add_left ?_ _)
    exact abs_sub _ _
  have ha' : C.δ i / C.γ i * |C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) -
      C.ρ (i + 1) ^ 2| ≤ C.ε * (304 / 100 * B * C.ρ (i + 1) ^ 2) := by
    have := mul_le_mul hb ha (abs_nonneg _) hB0
    linarith only [this]
  have hsc := transport_scalar_le hε0 hε hN hB0 hP0 hρ.le hD0 hp0 hq0 hb0 hD hP hq hb
  have hsc' := mul_le_mul_of_nonneg_left hsc hε0
  linarith only [tri, ha', hb', hc, hd, he, hf, hg, hsc']

/-- **The recursion of Lemma B**: $\lvert\bar p_{i+1}\rvert \le (1 + 3.1\varepsilon)
\lvert\bar p_i\rvert + \varepsilon\bigl(13\|\mathbf{A}\|_2(1+\Pi)^2 + 10B(1+\Pi)\bigr)$. -/
private theorem abs_adjacentInner_succ_le {P B : ℝ} {i : ℕ} (hi : i + 1 < k)
    (hP : ‖WithLp.toLp 2 (C.p (i + 1))‖ ≤ P * C.ρ (i + 1))
    (hβ : C.lanczosβ (i + 1) ≤ B) (hδB : C.δ i ≤ B * C.γ i) :
    |C.toLanczosData.adjacentInner (i + 1)| ≤
      (1 + 31 / 10 * C.ε) * |C.toLanczosData.adjacentInner i| +
        C.ε * (13 * (specNorm C.A * (1 + P) ^ 2) + 10 * (B * (1 + P))) := by
  have hi' : i < k := by omega
  have hγ := C.γ_pos hi
  have hγ' := C.γ_pos hi'
  have hρ := C.ρ_pos hi
  have hρ' := C.ρ_pos hi'
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  obtain ⟨hδ0, hδ1, -⟩ := C.δ_bounds hi'
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ
    linarith [norm_nonneg (WithLp.toLp 2 (C.p (i + 1)))]
  have hG : 0 < C.γ (i + 1) * C.ρ (i + 1) ^ 2 := by positivity
  rw [C.adjacentInner_eq hi, C.adjacentInner_eq hi', abs_div, abs_div, abs_neg, abs_neg,
    abs_of_pos hG, abs_of_pos (by positivity : 0 < C.γ i * C.ρ i ^ 2), div_le_iff₀ hG]
  rw [C.r_dotProduct_r_succ_succ_eq hi, C.γ_mul_p_dotProduct_s_succ_eq hi]
  set S := (C.δ i * (C.ρ i ^ 2 * (1 + C.θ i) * (1 + C.eγ i)) - C.ρ (i + 1) ^ 2) -
        C.δ i * (C.γ i * C.eμ i) - C.δ i * (C.p i ⬝ᵥ C.er i) +
        (C.r i - C.r (i + 1)) ⬝ᵥ C.ep i + C.er i ⬝ᵥ C.p (i + 1) -
        C.γ i * (C.es i ⬝ᵥ C.p (i + 1)) + C.γ i * (C.p i ⬝ᵥ C.es (i + 1)) with hS
  have hT := C.transport_le hi hP hβ hδB
  rw [← hS] at hT
  have hR := C.abs_localR_le hi hP
  have hE := C.abs_γ_mul_ep_dotProduct_s_le hi hP
  set ψ := C.r i ⬝ᵥ C.r (i + 1)
  have hc0 : 0 ≤ C.γ (i + 1) * C.δ i / C.γ i := div_nonneg (mul_nonneg hγ.le hδ0) hγ'.le
  have t1 : |C.γ (i + 1) * C.δ i / C.γ i * (ψ + S) + C.localR (i + 1) +
      C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1))| ≤
      C.γ (i + 1) * C.δ i / C.γ i * |ψ| + C.γ (i + 1) * (C.δ i / C.γ i * |S|) +
        |C.localR (i + 1)| + |C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1))| := by
    have h1 := abs_add_three (C.γ (i + 1) * C.δ i / C.γ i * (ψ + S)) (C.localR (i + 1))
      (C.γ (i + 1) * (C.ep i ⬝ᵥ C.s (i + 1)))
    rw [abs_mul, abs_of_nonneg hc0] at h1
    have h2 := mul_le_mul_of_nonneg_left (abs_add_le ψ S) hc0
    have e : C.γ (i + 1) * C.δ i / C.γ i * |S| = C.γ (i + 1) * (C.δ i / C.γ i * |S|) := by ring
    linarith only [h1, h2, e]
  -- the transported previous defect
  have t2 : C.γ (i + 1) * C.δ i / C.γ i * |ψ| ≤
      (1 + 31 / 10 * C.ε) * (|ψ| / (C.γ i * C.ρ i ^ 2)) * (C.γ (i + 1) * C.ρ (i + 1) ^ 2) := by
    have e : C.γ (i + 1) * C.δ i / C.γ i * |ψ| =
        C.γ (i + 1) * (C.δ i * C.ρ i ^ 2) * (|ψ| / (C.γ i * C.ρ i ^ 2)) := by
      field_simp
    rw [e]
    have hq0 : 0 ≤ |ψ| / (C.γ i * C.ρ i ^ 2) := by positivity
    have := mul_le_mul_of_nonneg_left hδ1 hγ.le
    have := mul_le_mul_of_nonneg_right this hq0
    linarith only [this]
  have t3 := mul_le_mul_of_nonneg_left hT hγ.le
  have hX : 0 ≤ C.ε * specNorm C.A * C.γ (i + 1) * C.ρ (i + 1) ^ 2 := by positivity
  have hpoly : 5 * P ^ 2 + 2 * P + (11 / 10 * P ^ 2 + 21 / 10 * P) ≤ 7 * (1 + P) ^ 2 := by
    nlinarith
  have t4 := mul_le_mul_of_nonneg_left hpoly hX
  have e : (C.ε * (13 * (specNorm C.A * (1 + P) ^ 2) + 10 * (B * (1 + P)))) *
      (C.γ (i + 1) * C.ρ (i + 1) ^ 2) = C.γ (i + 1) * (C.ε * (6 * (specNorm C.A * (1 + P) ^ 2 *
        C.ρ (i + 1) ^ 2) + 10 * (B * (1 + P) * C.ρ (i + 1) ^ 2))) +
        C.ε * specNorm C.A * C.γ (i + 1) * C.ρ (i + 1) ^ 2 * (7 * (1 + P) ^ 2) := by ring
  rw [add_mul, e]
  linarith only [t1, t2, t3, t4, hR, hE]

/-- **Lemma B with a nonnegative certificate** $B \ge 0$: the form of
`NLAlib.CGRun.abs_adjacentInner_le` that holds for every $k$ (for $k \ge 2$, $B \ge 0$ follows
from $\beta_1 \le B$). -/
theorem abs_adjacentInner_le_of_nonneg {P K B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) (hB0 : 0 ≤ B) {j : ℕ}
    (hj : j < k) :
    |C.toLanczosData.adjacentInner j| ≤
      16 * (j + 1) * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K)) := by
  have hk := C.k_pos
  have hρ0 := C.ρ_pos hk
  have hε0 := C.ε_nonneg
  have hN := specNorm_nonneg C.A
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ0
    linarith [norm_nonneg (WithLp.toLp 2 (C.p 0)), hP 0 hk]
  have hK0 : 0 ≤ K := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h (pow_pos hρ0 2)
    have : 0 ≤ specNorm C.A * C.γ 0 * ‖WithLp.toLp 2 (C.p 0)‖ ^ 2 :=
      mul_nonneg (mul_nonneg hN (C.γ_pos hk).le) (sq_nonneg _)
    linarith [hK 0 hk]
  have hX : 0 ≤ specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K) := by positivity
  induction j with
  | zero =>
    have hγ := C.γ_pos hk
    have hG : 0 < C.γ 0 * C.ρ 0 ^ 2 := by positivity
    rw [C.adjacentInner_eq hk, C.r_dotProduct_r_one_eq, abs_div, abs_neg, abs_of_pos hG,
      div_le_iff₀ hG]
    have hR := C.abs_localR_le hk (hP 0 hk)
    have h1 : 5 * P ^ 2 + 2 * P ≤ 16 * (1 + P) ^ 2 := by nlinarith
    have h2 : specNorm C.A * (1 + P) ^ 2 ≤ specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K) := by
      have : 0 ≤ B * (1 + P + K) := by positivity
      linarith
    have hY : 0 ≤ C.ε * specNorm C.A * C.γ 0 * C.ρ 0 ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 hY
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 16 * C.ε * (C.γ 0 * C.ρ 0 ^ 2))
    push_cast
    linarith only [hR, h3, h4]
  | succ i ih =>
    have hi : i < k := by omega
    have ih := ih hi
    obtain ⟨hβ, hδ⟩ := hB i hj
    have h := C.abs_adjacentInner_succ_le hj (hP (i + 1) hj) hβ hδ
    set X := specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K)
    have hL : C.ε * (13 * (specNorm C.A * (1 + P) ^ 2) + 10 * (B * (1 + P))) ≤ 13 * C.ε * X := by
      have : 13 * (specNorm C.A * (1 + P) ^ 2) + 10 * (B * (1 + P)) ≤ 13 * X := by
        have : B * (1 + P) ≤ B * (1 + P + K) := mul_le_mul_of_nonneg_left (by linarith) hB0
        have : 0 ≤ B * (1 + P) := by positivity
        simp only [X]
        linarith
      have := mul_le_mul_of_nonneg_left this hε0
      linarith only [this]
    have hiε : ((i : ℕ) + 1 : ℝ) * C.ε ≤ 1 / 100 := by
      have := C.mul_ε_le' (j := i + 1) hj.le
      exact_mod_cast this
    have h2 : (1 + 31 / 10 * C.ε) * |C.toLanczosData.adjacentInner i| ≤
        (1 + 31 / 10 * C.ε) * (16 * ((i : ℕ) + 1) * C.ε * X) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    have h3 : 31 / 10 * C.ε * (16 * ((i : ℕ) + 1) * C.ε * X) ≤ 1 / 2 * (C.ε * X) := by
      have e : 31 / 10 * C.ε * (16 * ((i : ℕ) + 1) * C.ε * X) =
          (496 / 10 * (((i : ℕ) + 1 : ℝ) * C.ε)) * (C.ε * X) := by ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg hε0 hX)
    push_cast
    have e2 : (1 + 31 / 10 * C.ε) * (16 * ((i : ℕ) + 1) * C.ε * X) =
        16 * ((i : ℕ) + 1) * C.ε * X + 31 / 10 * C.ε * (16 * ((i : ℕ) + 1) * C.ε * X) := by ring
    have hεX := mul_nonneg hε0 hX
    nlinarith

/-- **Lemma B (local orthogonality is inherited)**: with the certificates of
`NLAlib.CGRun.norm_recurrenceError_le` ($B$ for $j + 1 < k$ only) and
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le K\rho_j^2$ ($j < k$), the adjacent inner
products of the run's Lanczos data satisfy
$$\lvert\bar p_j\rvert \le 16(j+1)\varepsilon\bigl(\|\mathbf{A}\|_2(1 + \Pi)^2 +
B(1 + \Pi + K)\bigr),\qquad j < k .$$
No printed source; the research note `HSCG-FiniteP.md` §2.5. The orthogonality
$\mathbf{r}_j \perp \mathbf{r}_{j+1}$ is not produced at step $j$: it is the previous one
transported by the conjugacy $\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \approx 0$.
Proof: the recursion $\bar p_j = (1 + \eta_{j-1})\bar p_{j-1} + L_j$ (three identities in the
computed data, one use of $\mathbf{A}^{\mathsf{T}} = \mathbf{A}$), the bound on $L_j$ in which
only $\delta_{j-1}/\gamma_{j-1}$, $\gamma_j^{-1}$, $\beta_j$ occur (not $\alpha_{j+1}$,
$\beta_{j+1}$: this is what keeps the a priori hypothesis at $\kappa^2$), and
`NLAlib.CGRun.abs_p_dotProduct_r_succ_le`. Difficulty: hard (the risky step of the design). -/
theorem abs_adjacentInner_le {P K B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) {j : ℕ} (hj : j < k) :
    |C.toLanczosData.adjacentInner j| ≤
      16 * (j + 1) * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K)) := by
  rcases C.nonneg_of_certificate hB with hB0 | hk
  · exact C.abs_adjacentInner_le_of_nonneg hP hK hB hB0 hj
  · -- `k = 1` and `B < 0`: the statement is false (the right side can be negative while
    -- `p̄₀ ≠ 0`); see `NLAlib.CGRun.abs_adjacentInner_le_of_nonneg`.
    sorry

/-- **The a posteriori backward model with a nonnegative certificate** $B \ge 0$: the form of
`NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates` that holds for every $k$ (for
$k \ge 2$, $B \ge 0$ follows from $\beta_1 \le B$). -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_certificates_of_nonneg {P K B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) (hB0 : 0 ≤ B) :
    frobNorm (C.backwardH - C.dilatedH) ≤
      normalizedBackwardBound k (8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B))
        (16 * k * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K))) := by
  have hk := C.k_pos
  have hρ0 := C.ρ_pos hk
  have hP0 : 0 ≤ P := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h hρ0
    linarith [norm_nonneg (WithLp.toLp 2 (C.p 0)), hP 0 hk]
  have hK0 : 0 ≤ K := by
    by_contra h
    push Not at h
    have := mul_neg_of_neg_of_pos h (pow_pos hρ0 2)
    have : 0 ≤ specNorm C.A * C.γ 0 * ‖WithLp.toLp 2 (C.p 0)‖ ^ 2 :=
      mul_nonneg (mul_nonneg (specNorm_nonneg _) (C.γ_pos hk).le) (sq_nonneg _)
    linarith [hK 0 hk]
  have hX : 0 ≤ C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K)) := by
    have := C.ε_nonneg
    have := specNorm_nonneg C.A
    positivity
  refine C.toNormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le (fun j hj => ?_)
    (fun j hj => ?_)
  · exact C.norm_recurrenceError_le_of_nonneg hP hB hB0 hj
  · refine (C.abs_adjacentInner_le_of_nonneg hP hK hB hB0 hj).trans ?_
    have hjk : ((j : ℝ) + 1) ≤ k := by exact_mod_cast hj
    have := mul_le_mul_of_nonneg_right hjk hX
    linarith only [this]

/-- **The a posteriori backward model**: with the certificates $\Pi$, $K$ ($j < k$) and $B$
($j + 1 < k$) of the run,

$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le 102k^3 f + 96k^2 p,
\quad f = 8\varepsilon(\|\mathbf{A}\|_2(1+\Pi)^2 + B),\
p = 16k\varepsilon(\|\mathbf{A}\|_2(1+\Pi)^2 + B(1+\Pi+K)) .$$
The certificates are computable from the run; in practice $\Pi \ll \sqrt{\kappa}$. It is the
engine of the a priori induction (`NLAlibScaffold/Krylov/FinitePrecision/CGBackward.lean`): the
model of the prefix `C.take j` needs $B$ for the steps $i + 1 < j$ only, which the models of the
shorter prefixes provide.
Proof: `NLAlib.NormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le` with Lemmas A and B.
Difficulty: easy. -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_certificates {P K B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) :
    frobNorm (C.backwardH - C.dilatedH) ≤
      normalizedBackwardBound k (8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B))
        (16 * k * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K))) := by
  rcases C.nonneg_of_certificate hB with hB0 | hk
  · exact C.frobNorm_backwardH_sub_dilatedH_le_of_certificates_of_nonneg hP hK hB hB0
  · -- `k = 1` and `B < 0`: the statement is false (for `B` negative enough the right side is
    -- negative); see `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates_of_nonneg`.
    sorry

/-- **The next direction is not small**: with certificates $\Pi$, $K$ on the steps $j < k$ and
$20k\varepsilon(1 + \Pi + K) \le 1$, the direction after the last step satisfies
$\rho_k \le 2\|\mathbf{p}_k\|$. So $\mathbf{p}_k \ne \mathbf{0}$ when $\mathbf{r}_k \ne \mathbf{0}$,
and the next curvature is positive (`NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`): the
program's next division succeeds.
Proof: $\|\mathbf{r}_k + \delta_{k-1}\mathbf{p}_{k-1}\|^2 = \rho_k^2 + \delta_{k-1}^2
\|\mathbf{p}_{k-1}\|^2 + 2\delta_{k-1}\tau_{k-1}$ with `NLAlib.CGRun.abs_p_dotProduct_r_succ_le`
and $\delta_{k-1}\rho_{k-1}^2 \le 1.04\rho_k^2$; then `C.norm_ep_le`, bounded through the
quadratic mean, $\|\mathbf{e}^p_{k-1}\| \le \sqrt{2}\,\varepsilon\,(\rho_k^2 +
\delta_{k-1}^2\|\mathbf{p}_{k-1}\|^2)^{1/2}$, and $\rho_k^2 + \delta_{k-1}^2\|\mathbf{p}_{k-1}\|^2
\le \|\mathbf{r}_k + \delta_{k-1}\mathbf{p}_{k-1}\|^2 + 2\delta_{k-1}\lvert\tau_{k-1}\rvert$
(bounding $\delta_{k-1}\|\mathbf{p}_{k-1}\|$ directly reintroduces $\rho_k/\rho_{k-1}$); the
result is $\|\mathbf{p}_k\| \ge 0.67\rho_k$. Difficulty: moderate. -/
theorem norm_r_le_two_mul_norm_p {P K : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hsmall : 20 * k * C.ε * (1 + P + K) ≤ 1) :
    C.ρ k ≤ 2 * ‖WithLp.toLp 2 (C.p k)‖ := by
  sorry

/-- One step of the residual gap: $\mathbf{g}_{j+1} = \mathbf{g}_j + \gamma_j\mathbf{e}^s_j -
\mathbf{A}\mathbf{e}^x_j - \mathbf{e}^r_j$, bounded. -/
private theorem norm_gap_succ_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x (j + 1) - C.r (j + 1))‖ ≤
      ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ + C.ε * (specNorm C.A *
        (‖WithLp.toLp 2 (C.x j)‖ + 4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) := by
  have hid : C.b - C.A *ᵥ C.x (j + 1) - C.r (j + 1) =
      (C.b - C.A *ᵥ C.x j - C.r j) + C.γ j • C.es j - C.A *ᵥ C.ex j - C.er j := by
    rw [C.x_succ j hj, C.r_succ j hj, C.s_eq j hj, Matrix.mulVec_add, Matrix.mulVec_add,
      Matrix.mulVec_smul, smul_add]
    abel
  rw [hid]
  have h1 := norm_toLp_sub_le ((C.b - C.A *ᵥ C.x j - C.r j) + C.γ j • C.es j - C.A *ᵥ C.ex j)
    (C.er j)
  have h2 := norm_toLp_sub_le ((C.b - C.A *ᵥ C.x j - C.r j) + C.γ j • C.es j) (C.A *ᵥ C.ex j)
  have h3 := norm_toLp_add_le (C.b - C.A *ᵥ C.x j - C.r j) (C.γ j • C.es j)
  have hγ := C.γ_pos hj
  rw [norm_toLp_smul, abs_of_pos hγ] at h3
  have h4 := norm_toLp_mulVec_le C.A (C.ex j)
  have h5 := C.norm_ex_le j hj
  have h6 := C.norm_er_le j hj
  have h7 := C.norm_es_le j hj
  have h8 := C.norm_s_le hj
  rw [abs_of_pos hγ] at h5 h6
  have hN := specNorm_nonneg C.A
  have hε := C.ε_nonneg
  have hε1 := C.ε_le
  have hp := norm_nonneg (WithLp.toLp 2 (C.p j))
  have hx := norm_nonneg (WithLp.toLp 2 (C.x j))
  have e1 := mul_le_mul_of_nonneg_left h5 hN
  have e2 := mul_le_mul_of_nonneg_left h7 hγ.le
  have e3 := mul_le_mul_of_nonneg_left h8 (mul_nonneg hε hγ.le)
  have e4 : C.ε * C.γ j * ((1 + C.ε) * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖) ≤
      C.ε * C.γ j * (2 * specNorm C.A * ‖WithLp.toLp 2 (C.p j)‖) := by
    gcongr
    linarith
  simp only [ρ] at *
  nlinarith

/-- **The residual gap** (true minus updated residual): with $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{b}$,
$$\|(\mathbf{b} - \mathbf{A}\mathbf{x}_k) - \mathbf{r}_k\| \le \varepsilon\sum_{j<k}
\bigl(\|\mathbf{A}\|_2(\|\mathbf{x}_j\| + 4\gamma_j\|\mathbf{p}_j\|) + \|\mathbf{r}_j\|\bigr) .$$
[Greenbaum1997SIMAX]; [StrakosTichy2002, (7.16)], there with $\|\mathbf{x}\| +
\max_j\|\mathbf{x}_j\|$ and $+O(\varepsilon^2)$. Local: no Lanczos reduction, no $\kappa$.
Proof: the gap satisfies $\mathbf{g}_{j+1} = \mathbf{g}_j + \gamma_j\mathbf{e}^s_j -
\mathbf{A}\mathbf{e}^x_j - \mathbf{e}^r_j$, $\mathbf{g}_0 = \mathbf{0}$; sum the norms.
Difficulty: easy. -/
theorem norm_sub_mulVec_x_sub_r_le :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      C.ε * ∑ j ∈ Finset.range k, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
        4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) := by
  suffices h : ∀ m ≤ k, ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x m - C.r m)‖ ≤
      C.ε * ∑ j ∈ Finset.range m, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
        4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) from h k le_rfl
  intro m hm
  induction m with
  | zero =>
    rw [C.x_zero, C.r_zero, Matrix.mulVec_zero, sub_zero, sub_self, WithLp.toLp_zero, norm_zero,
      Finset.sum_range_zero, mul_zero]
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add]
    exact (C.norm_gap_succ_le (by omega)).trans (by linarith [ih (by omega)])

end CGRun

end NLAlib
