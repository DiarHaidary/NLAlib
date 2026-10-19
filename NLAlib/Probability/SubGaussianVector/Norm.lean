/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square
public import NLAlib.Probability.SubGaussianVector.Basic
public import NLAlib.Probability.Tail

/-!
# The squared norm of a sub-Gaussian random vector

For a real sub-Gaussian vector $\mathbf{x}$ with proxy $c$, $\mathbb{E} e^{\theta \|\mathbf{x}\|^2}$
is at most the Laplace transform of $c \chi^2_n$, and the upper tails of a weighted sum of squares
$\sum_i w_i \mathbf{x}_i^2$ and of the squared norm $\|\mathbf{A}\mathbf{x}\|^2$ of its image
under a fixed matrix $\mathbf{A}$ are Hsu, Kakade and Zhang's, with Laurent and Massart's
constants,
$$\mathbb{P}\Bigl(\|\mathbf{A}\mathbf{x}\|^2 \ge c\,\bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 +
  2 \|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}} \sqrt{t} +
  2 \|\mathbf{A}\|_2^2\, t\bigr)\Bigr) \le e^{-t}\,.$$
At $\mathbf{A} = \mathbf{I}$ this is
$\mathbb{P}(\|\mathbf{x}\|^2 \ge c (n + 2\sqrt{n t} + 2t)) \le e^{-t}$. For independent
sub-Gaussian coordinates, the two-sided tail of $\|\mathbf{x}\|^2$ about its mean is Bernstein's
inequality for the centred squares.

The vector $\mathbf{x}$ is real: the proofs linearise with a standard Gaussian vector of the same
dimension (`NLAlib.lintegral_exp_mul_dotProduct_gaussianVector`), which exists over $\mathbb{R}$
only in this library for now. The matrix $\mathbf{A}$ may be over any `RCLike` field, and the
bound has no field factor (see the docstring of
`NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`).

Proofs. The diagonal form linearises $e^{\theta \sum_i w_i \mathbf{x}_i^2}$ with a standard
Gaussian vector at $\sqrt{\mathbf{w}} \odot \mathbf{g}$, applies the proxy, evaluates the weighted
$\chi^2$ transform (`NLAlib.integral_exp_sum_mul_sq_of_hasLaw_gaussianVector`), and bounds the
log-moment generating function by Laurent and Massart's
$-\tfrac12 \sum_i \log(1 - u_i) \le \tfrac12 \sum_i u_i + \sum_i u_i^2 / (4 (1 - \max_i u_i))$
(`Real.neg_log_one_sub_le`); `NLAlib.measureReal_ge_le_exp_neg_of_mgf_le` inverts the resulting
sub-gamma bound. The matrix form diagonalises
$\operatorname{Re}(\mathbf{A}^{\mathsf{H}}\mathbf{A})$, the Gram matrix of $\mathbf{A}$ on real
vectors (the spectral theorem over $\mathbb{R}$), and applies the diagonal form to the rotated
vector.

## Main results

* `NLAlib.IsSubgaussianVector.integral_exp_mul_norm_sq_le`:
  $\mathbb{E} e^{\theta \|\mathbf{x}\|^2} \le (1 - 2\theta c)^{-n/2}$.
* `NLAlib.IsSubgaussianVector.measureReal_sum_mul_sq_ge_le`: weighted squares (the diagonal form).
* `NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`: the Hsu–Kakade–Zhang tail.
* `NLAlib.IsSubgaussianVector.measureReal_norm_sq_ge_le`: the upper tail of $\|\mathbf{x}\|^2$.
* `NLAlib.measureReal_abs_norm_sq_sub_integral_ge_le`: the two-sided tail for independent
  coordinates.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped Matrix NNReal

namespace NLAlib

/-! ### Auxiliary bounds -/

private theorem one_sub_rpow_neg_half_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) :
    (1 - u) ^ (-(1 / 2 : ℝ)) ≤ Real.exp (u / 2 + u ^ 2 / (4 * (1 - u))) := by
  rw [Real.rpow_def_of_pos (by linarith), Real.exp_le_exp]
  have h := Real.neg_log_one_sub_le hu0 hu1
  have : u ^ 2 / (4 * (1 - u)) = u ^ 2 / (2 * (1 - u)) / 2 := by
    rw [div_div]; ring_nf
  linarith

section Gram

variable {n : Type*} [Fintype n] {m : Type*} [Fintype m] {𝕜 : Type*} [RCLike 𝕜]

private theorem norm_toLp_mulVec_ofReal_sq (A : Matrix m n 𝕜) (y : n → ℝ) :
    ‖WithLp.toLp 2 (A *ᵥ fun i => (y i : 𝕜))‖ ^ 2 = y ⬝ᵥ ((Aᴴ * A).map RCLike.re *ᵥ y) := by
  have h := congrArg RCLike.re (quadForm_conjTranspose_mul_self A (fun i => (y i : 𝕜)))
  rw [RCLike.ofReal_re] at h
  rw [← h, quadForm]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal,
    map_sum, Matrix.map_apply, RCLike.re_ofReal_mul, RCLike.re_mul_ofReal]

private theorem norm_toLp_ofReal (y : n → ℝ) :
    ‖WithLp.toLp 2 (fun i => (y i : 𝕜))‖ = ‖WithLp.toLp 2 y‖ := by
  simp only [EuclideanSpace.norm_eq, RCLike.norm_ofReal, Real.norm_eq_abs]

omit [Fintype n] in
private theorem isHermitian_map_re_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    ((Aᴴ * A).map RCLike.re).IsHermitian := by
  have hG : (Aᴴ * A).IsHermitian := Matrix.isHermitian_conjTranspose_mul_self A
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.map_apply, star_trivial]
  rw [← hG.apply j i, RCLike.star_def, RCLike.conj_re]

/-- The real part $\mathbf{M} = \operatorname{Re}(\mathbf{A}^{\mathsf{H}}\mathbf{A})$ of the Gram
matrix, diagonalised: $\|\mathbf{A}\mathbf{y}\|^2 = \sum_i \lambda_i
(\mathbf{V}^{\mathsf{T}}\mathbf{y})_i^2$ for real $\mathbf{y}$, with $0 \le \lambda_i \le
\|\mathbf{A}\|_2^2$, $\sum_i \lambda_i = \|\mathbf{A}\|_{\mathsf{F}}^2$ and
$\sqrt{\sum_i \lambda_i^2} = \|\mathbf{M}\|_{\mathsf{F}} \le
\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}}$. -/
private theorem exists_gram_diagonalisation [DecidableEq n] (A : Matrix m n 𝕜) :
    ∃ (V : Matrix n n ℝ) (lam : n → ℝ), HasOrthonormalCols V ∧
      (∀ y : n → ℝ, ‖WithLp.toLp 2 (A *ᵥ fun i => (y i : 𝕜))‖ ^ 2 =
        ∑ i, lam i * (Vᴴ *ᵥ y) i ^ 2) ∧
      (∀ i, 0 ≤ lam i) ∧ (∀ i, lam i ≤ specNorm A ^ 2) ∧ ∑ i, lam i = frobNorm A ^ 2 ∧
      √(∑ i, lam i ^ 2) ≤ frobNorm (Aᴴ * A) := by
  have hM := isHermitian_map_re_conjTranspose_mul_self A
  set M : Matrix n n ℝ := (Aᴴ * A).map RCLike.re with hM_def
  set V : Matrix n n ℝ := (hM.eigenvectorUnitary : Matrix n n ℝ) with hV_def
  set lam : n → ℝ := hM.eigenvalues with hlam_def
  have hV : HasOrthonormalCols V :=
    hasOrthonormalCols_iff_mem_unitaryGroup.mpr hM.eigenvectorUnitary.2
  have hdiag : Vᴴ * M * V = Matrix.diagonal lam := by
    have h1 := hM.conjStarAlgAut_star_eigenvectorUnitary
    rw [Unitary.conjStarAlgAut_star_apply] at h1
    simpa [Matrix.star_eq_conjTranspose] using h1
  have hquad : ∀ y : n → ℝ, ‖WithLp.toLp 2 (A *ᵥ fun i => (y i : 𝕜))‖ ^ 2 =
      ∑ i, lam i * (Vᴴ *ᵥ y) i ^ 2 := by
    intro y
    rw [norm_toLp_mulVec_ofReal_sq]
    have hVV : V * Vᴴ = 1 := hV.mul_conjTranspose_self
    have hy : y = V *ᵥ (Vᴴ *ᵥ y) := by rw [Matrix.mulVec_mulVec, hVV, Matrix.one_mulVec]
    calc y ⬝ᵥ (M *ᵥ y) = (V *ᵥ (Vᴴ *ᵥ y)) ⬝ᵥ (M *ᵥ (V *ᵥ (Vᴴ *ᵥ y))) := by rw [← hy]
      _ = (Vᴴ *ᵥ y) ⬝ᵥ ((Vᴴ * M * V) *ᵥ (Vᴴ *ᵥ y)) := by
        rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
          ← Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = ∑ i, lam i * (Vᴴ *ᵥ y) i ^ 2 := by
        rw [hdiag]
        simp only [dotProduct, Matrix.mulVec_diagonal]
        exact Finset.sum_congr rfl fun i _ => by ring
  have hlam : ∀ i,
      lam i = ‖WithLp.toLp 2 (A *ᵥ fun j => ((hM.eigenvectorBasis i j : ℝ) : 𝕜))‖ ^ 2 := by
    intro i
    rw [hlam_def, hM.eigenvalues_eq i, norm_toLp_mulVec_ofReal_sq]
    simp only [star_trivial, RCLike.re_to_real]
    rfl
  have hnorm1 : ∀ i, ‖WithLp.toLp 2 (fun j => ((hM.eigenvectorBasis i j : ℝ) : 𝕜))‖ = 1 := by
    intro i
    rw [norm_toLp_ofReal]
    exact hM.eigenvectorBasis.orthonormal.1 i
  have hlam0 : ∀ i, 0 ≤ lam i := fun i => by rw [hlam i]; positivity
  have hlamb : ∀ i, lam i ≤ specNorm A ^ 2 := by
    intro i
    rw [hlam i]
    have := norm_toLp_mulVec_le A (fun j => ((hM.eigenvectorBasis i j : ℝ) : 𝕜))
    rw [hnorm1, mul_one] at this
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  have hsum : ∑ i, lam i = frobNorm A ^ 2 := by
    have h1 := hM.trace_eq_sum_eigenvalues
    simp only [RCLike.ofReal_real_eq_id, id] at h1
    rw [hlam_def, ← h1, frobNorm_sq_eq_re_trace, hM_def, Matrix.trace, Matrix.trace, map_sum]
    rfl
  have hsq : √(∑ i, lam i ^ 2) ≤ frobNorm (Aᴴ * A) := by
    have h1 : ∑ i, lam i ^ 2 = frobNorm M ^ 2 := by
      have e1 : frobNorm (Vᴴ * M * V) = frobNorm M := by
        rw [hV.frobNorm_mul_right, ← frobNorm_conjTranspose, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_conjTranspose, hV.frobNorm_mul_right, frobNorm_conjTranspose]
      rw [← e1, hdiag, frobNorm_diagonal_sq]
      simp only [Real.norm_eq_abs, sq_abs]
    have h2 : frobNorm M ≤ frobNorm (Aᴴ * A) := by
      refine (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 ?_
      rw [frobNorm_sq_eq_sum, frobNorm_sq_eq_sum]
      refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
      rw [hM_def, Matrix.map_apply, Real.norm_eq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) (RCLike.abs_re_le_norm _) 2
    rw [h1, Real.sqrt_sq (frobNorm_nonneg _)]
    exact h2
  exact ⟨V, lam, hV, hquad, hlam0, hlamb, hsum, hsq⟩

end Gram

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {x : Ω → n → ℝ} {c : ℝ≥0}

namespace IsSubgaussianVector

/-! ### Exponential moments -/

private theorem lintegral_exp_mul_sum_mul_sq_le (h : IsSubgaussianVector x c μ) {w : n → ℝ}
    (hw : ∀ i, 0 ≤ w i) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ i, 2 * (θ * c * w i) < 1) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ∑ i, w i * x ω i ^ 2)) ∂μ ≤
      ENNReal.ofReal (∏ i, (1 - 2 * (θ * c * w i)) ^ (-(1 / 2 : ℝ))) := by
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  set s : n → ℝ := fun i => √(2 * θ * w i)
  have hs : ∀ i, s i ^ 2 = 2 * θ * w i := fun i => Real.sq_sqrt (by have := hw i; positivity)
  have hpt : ∀ v : n → ℝ, ENNReal.ofReal (Real.exp (θ * ∑ i, w i * v i ^ 2)) =
      ∫⁻ g, ENNReal.ofReal (Real.exp (1 * ((fun i => s i * v i) ⬝ᵥ g))) ∂(gaussianVector n) := by
    intro v
    rw [lintegral_exp_mul_dotProduct_gaussianVector, EuclideanSpace.real_norm_sq_eq,
      Finset.mul_sum, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_pow, hs]
    ring
  have hxi : ∀ i, AEMeasurable (fun p : Ω × (n → ℝ) => x p.1 i) (μ.prod (gaussianVector n)) :=
    fun i => (aemeasurable_pi_iff.mp h.aemeasurable i).comp_fst
  have hdot : AEMeasurable (fun p : Ω × (n → ℝ) => (fun i => s i * x p.1 i) ⬝ᵥ p.2)
      (μ.prod (gaussianVector n)) :=
    Finset.aemeasurable_fun_sum _ fun i _ =>
      ((hxi i).const_mul (s i)).mul ((measurable_pi_apply i).comp measurable_snd).aemeasurable
  have hmeas : AEMeasurable (Function.uncurry fun ω (g : n → ℝ) =>
      ENNReal.ofReal (Real.exp (1 * ((fun i => s i * x ω i) ⬝ᵥ g)))) (μ.prod (gaussianVector n)) :=
    (Real.measurable_exp.comp_aemeasurable (hdot.const_mul 1)).ennreal_ofReal
  have hθi : ∀ i, 2 * (θ * c * w i) < 1 := hθ
  have hlaw : HasLaw (id : (n → ℝ) → n → ℝ) (gaussianVector n) (gaussianVector n) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have hint := integral_exp_sum_mul_sq_of_hasLaw_gaussianVector hlaw (θ := fun i => θ * c * w i) hθi
  have hpos : 0 < ∏ i, (1 - 2 * (θ * c * w i)) ^ (-(1 / 2 : ℝ)) :=
    Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (by linarith [hθi i]) _
  have hintg : Integrable (fun g : n → ℝ => Real.exp (∑ i, θ * c * w i * id g i ^ 2))
      (gaussianVector n) :=
    Integrable.of_integral_ne_zero (by rw [hint]; exact hpos.ne')
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (θ * ∑ i, w i * x ω i ^ 2)) ∂μ
      = ∫⁻ ω, ∫⁻ g, ENNReal.ofReal (Real.exp (1 * ((fun i => s i * x ω i) ⬝ᵥ g)))
          ∂(gaussianVector n) ∂μ := by
        simp only [hpt]
    _ = ∫⁻ g, ∫⁻ ω, ENNReal.ofReal (Real.exp (1 * ((fun i => s i * x ω i) ⬝ᵥ g))) ∂μ
          ∂(gaussianVector n) :=
        lintegral_lintegral_swap hmeas
    _ ≤ ∫⁻ g, ENNReal.ofReal (Real.exp (∑ i, θ * c * w i * id g i ^ 2)) ∂(gaussianVector n) := by
        refine lintegral_mono fun g => ?_
        have hu := h.hasSubgaussianMGF (fun i => s i * g i)
        simp only [RCLike.re_to_real] at hu
        have hdg : ∀ ω, (fun i => s i * x ω i) ⬝ᵥ g = (fun i => s i * g i) ⬝ᵥ x ω := by
          intro ω
          simp only [dotProduct]
          exact Finset.sum_congr rfl fun i _ => by ring
        have heq : ∫⁻ ω, ENNReal.ofReal (Real.exp (1 * ((fun i => s i * x ω i) ⬝ᵥ g))) ∂μ =
            ENNReal.ofReal (mgf (fun ω => (fun i => s i * g i) ⬝ᵥ x ω) μ 1) := by
          rw [mgf, ofReal_integral_eq_lintegral_ofReal (hu.integrable_exp_mul 1)
            (ae_of_all _ fun _ => (Real.exp_pos _).le)]
          simp only [hdg]
        rw [heq]
        refine ENNReal.ofReal_le_ofReal ((hu.mgf_le 1).trans (Real.exp_le_exp.mpr (le_of_eq ?_)))
        push_cast
        rw [EuclideanSpace.real_norm_sq_eq, Finset.mul_sum, one_pow, mul_one, Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [id]
        rw [mul_pow, hs]
        ring
    _ = ENNReal.ofReal (∏ i, (1 - 2 * (θ * c * w i)) ^ (-(1 / 2 : ℝ))) := by
        rw [← hint, ofReal_integral_eq_lintegral_ofReal hintg
          (ae_of_all _ fun _ => (Real.exp_pos _).le)]

private theorem integrable_exp_mul_sum_mul_sq (h : IsSubgaussianVector x c μ) {w : n → ℝ}
    (hw : ∀ i, 0 ≤ w i) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ i, 2 * (θ * c * w i) < 1) :
    Integrable (fun ω => Real.exp (θ * ∑ i, w i * x ω i ^ 2)) μ := by
  have hcont : Continuous fun v : n → ℝ => Real.exp (θ * ∑ i, w i * v i ^ 2) := by fun_prop
  refine ⟨hcont.comp_aestronglyMeasurable h.aemeasurable.aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => (Real.exp_pos _).le)).mpr ?_⟩
  exact (h.lintegral_exp_mul_sum_mul_sq_le hw hθ0 hθ).trans_lt ENNReal.ofReal_lt_top

private theorem mgf_sum_mul_sq_le (h : IsSubgaussianVector x c μ) {w : n → ℝ}
    (hw : ∀ i, 0 ≤ w i) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ i, 2 * (θ * c * w i) < 1) :
    mgf (fun ω => ∑ i, w i * x ω i ^ 2) μ θ ≤
      ∏ i, (1 - 2 * (θ * c * w i)) ^ (-(1 / 2 : ℝ)) := by
  rw [mgf, integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => (Real.exp_pos _).le)
    (h.integrable_exp_mul_sum_mul_sq hw hθ0 hθ).aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal (Finset.prod_nonneg fun i _ =>
    Real.rpow_nonneg (by linarith [hθ i]) _) (h.lintegral_exp_mul_sum_mul_sq_le hw hθ0 hθ)

/-- The mean squared norm of a sub-Gaussian vector with proxy $c$ is at most $c \lvert n\rvert$:
$\mathbb{E}\|\mathbf{x}\|^2 \le c \lvert n\rvert$ under a probability measure. -/
theorem integral_norm_sq_le [IsProbabilityMeasure μ] (h : IsSubgaussianVector x c μ) :
    ∫ ω, ‖WithLp.toLp 2 (x ω)‖ ^ 2 ∂μ ≤ c * Fintype.card n := by
  have hi : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ := fun i => by
    simpa only [RCLike.re_to_real] using h.hasSubgaussianMGF_re_apply i
  simp only [EuclideanSpace.norm_toLp_sq_eq_sum_sq]
  rw [integral_finsetSum _ fun i _ => ((hi i).memLp 2).integrable_sq]
  calc ∑ i, ∫ ω, x ω i ^ 2 ∂μ ≤ ∑ _i : n, (c : ℝ) :=
        Finset.sum_le_sum fun i _ => (hi i).integral_sq_le
    _ = c * Fintype.card n := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

/-- $e^{\theta \|\mathbf{x}\|^2}$ is integrable for a sub-Gaussian vector with proxy $c$ when
$2 \theta c < 1$. -/
theorem integrable_exp_mul_norm_sq (h : IsSubgaussianVector x c μ) {θ : ℝ}
    (hθ : 2 * θ * c < 1) : Integrable (fun ω => rexp (θ * ‖WithLp.toLp 2 (x ω)‖ ^ 2)) μ := by
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  have hcont : Continuous fun v : n → ℝ => rexp (θ * ‖WithLp.toLp 2 v‖ ^ 2) := by
    simp only [EuclideanSpace.norm_toLp_sq_eq_sum_sq]
    fun_prop
  have hm : AEStronglyMeasurable (fun ω => rexp (θ * ‖WithLp.toLp 2 (x ω)‖ ^ 2)) μ :=
    hcont.comp_aestronglyMeasurable h.aemeasurable.aestronglyMeasurable
  rcases le_or_gt θ 0 with hθ0 | hθ0
  · refine Integrable.mono' (integrable_const 1) hm (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (exp_pos _), exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg hθ0 (sq_nonneg _)
  · refine (h.integrable_exp_mul_sum_mul_sq (w := fun _ => 1) (fun _ => zero_le_one) hθ0.le
      fun _ => by linarith).congr (ae_of_all _ fun ω => ?_)
    simp only [one_mul, EuclideanSpace.norm_toLp_sq_eq_sum_sq]

/-- $\int e^{\theta \|\mathbf{x}\|^2} \, d\mu \le (1 - 2\theta c)^{-\lvert n\rvert/2}$ for a
sub-Gaussian vector with proxy $c$, $\theta \ge 0$ and $2\theta c < 1$: the Laplace transform of
$c \chi^2_n$, by Gaussian linearisation. -/
theorem integral_exp_mul_norm_sq_le (h : IsSubgaussianVector x c μ) {θ : ℝ} (hθ0 : 0 ≤ θ)
    (hθ : 2 * θ * c < 1) :
    ∫ ω, rexp (θ * ‖WithLp.toLp 2 (x ω)‖ ^ 2) ∂μ ≤
      (1 - 2 * θ * c) ^ (-(Fintype.card n / 2 : ℝ)) := by
  have h2 : 0 ≤ 1 - 2 * θ * c := by linarith
  have hw := h.mgf_sum_mul_sq_le (w := fun _ => 1) (fun _ => zero_le_one) hθ0
    fun _ => by linarith
  simp only [mgf, one_mul, mul_one, ← EuclideanSpace.norm_toLp_sq_eq_sum_sq] at hw
  refine hw.trans_eq ?_
  rw [Finset.prod_const, Finset.card_univ, ← rpow_natCast, ← rpow_mul (by linarith)]
  ring_nf

omit [Fintype n] in
private theorem two_mul_le_of_le {w : n → ℝ} {b : ℝ}
    (hwb : ∀ i, w i ≤ b) {θ : ℝ} (hθ : 0 ≤ θ) (i : n) :
    2 * (θ * c * w i) ≤ 2 * c * b * θ := by
  have := mul_le_mul_of_nonneg_left (hwb i) (by positivity : (0 : ℝ) ≤ 2 * θ * c)
  linarith

omit [Fintype n] in
private theorem exp_mul_sub_eq (θ a : ℝ) (Y : Ω → ℝ) :
    (fun ω => Real.exp (θ * (Y ω - a))) = fun ω => Real.exp (-(θ * a)) * Real.exp (θ * Y ω) := by
  funext ω
  rw [← Real.exp_add]
  ring_nf

/-- The centred weighted squares are sub-gamma with variance factor $2 c^2 \sum_i w_i^2$ and scale
$2 c b$: Laurent and Massart's log-moment bound applied to the weighted $\chi^2$ transform. -/
private theorem mgf_sum_mul_sq_sub_le (h : IsSubgaussianVector x c μ) {w : n → ℝ}
    (hw : ∀ i, 0 ≤ w i) {b : ℝ} (hwb : ∀ i, w i ≤ b) {θ : ℝ} (hθ : 0 ≤ θ)
    (hbθ : 2 * c * b * θ < 1) :
    mgf (fun ω => ∑ i, w i * x ω i ^ 2 - c * ∑ i, w i) μ θ ≤
      Real.exp (θ ^ 2 * (2 * c ^ 2 * ∑ i, w i ^ 2) / (2 * (1 - 2 * c * b * θ))) := by
  have hu := two_mul_le_of_le (c := c) hwb hθ
  have hu1 : ∀ i, 2 * (θ * c * w i) < 1 := fun i => (hu i).trans_lt hbθ
  have hu0 : ∀ i, 0 ≤ 2 * (θ * c * w i) := fun i => by have := hw i; positivity
  have hmY := h.mgf_sum_mul_sq_le hw hθ hu1
  have hX : mgf (fun ω => ∑ i, w i * x ω i ^ 2 - c * ∑ i, w i) μ θ =
      Real.exp (-(θ * (c * ∑ i, w i))) * mgf (fun ω => ∑ i, w i * x ω i ^ 2) μ θ := by
    rw [mgf, mgf, ← integral_const_mul]
    exact congrArg (fun f => ∫ ω, f ω ∂μ)
      (exp_mul_sub_eq θ (c * ∑ i, w i) fun ω => ∑ i, w i * x ω i ^ 2)
  have h1 : ∑ i, 2 * (θ * c * w i) / 2 = θ * (c * ∑ i, w i) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h2 : ∑ i, (2 * (θ * c * w i)) ^ 2 = 4 * θ ^ 2 * c ^ 2 * ∑ i, w i ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hB : 0 < 1 - 2 * c * b * θ := by linarith
  rw [hX]
  calc Real.exp (-(θ * (c * ∑ i, w i))) * mgf (fun ω => ∑ i, w i * x ω i ^ 2) μ θ
      ≤ Real.exp (-(θ * (c * ∑ i, w i))) * ∏ i, (1 - 2 * (θ * c * w i)) ^ (-(1 / 2 : ℝ)) := by
        gcongr
    _ ≤ Real.exp (-(θ * (c * ∑ i, w i))) * ∏ i, Real.exp (2 * (θ * c * w i) / 2 +
          (2 * (θ * c * w i)) ^ 2 / (4 * (1 - 2 * (θ * c * w i)))) := by
        refine mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun i _ => ?_)
          fun i _ => one_sub_rpow_neg_half_le (hu0 i) (hu1 i)) (Real.exp_pos _).le
        exact Real.rpow_nonneg (by linarith [hu1 i]) _
    _ ≤ Real.exp (-(θ * (c * ∑ i, w i))) * Real.exp (∑ i, (2 * (θ * c * w i) / 2 +
          (2 * (θ * c * w i)) ^ 2 / (4 * (1 - 2 * c * b * θ)))) := by
        rw [← Real.exp_sum]
        refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (Finset.sum_le_sum fun i _ => ?_))
          (Real.exp_pos _).le
        have h4 : 0 < 4 * (1 - 2 * c * b * θ) := by linarith
        have h5 : 4 * (1 - 2 * c * b * θ) ≤ 4 * (1 - 2 * (θ * c * w i)) := by linarith [hu i]
        have := div_le_div_of_nonneg_left (sq_nonneg (2 * (θ * c * w i))) h4 h5
        linarith
    _ = Real.exp (θ ^ 2 * (2 * c ^ 2 * ∑ i, w i ^ 2) / (2 * (1 - 2 * c * b * θ))) := by
        rw [← Real.exp_add, Finset.sum_add_distrib, h1, ← Finset.sum_div, h2]
        congr 1
        field_simp
        ring

/-- **Weighted squares of a sub-Gaussian vector**, the diagonal Hsu–Kakade–Zhang tail: for a real
sub-Gaussian vector $\mathbf{x}$ with proxy $c \ne 0$, weights $0 \le w_i \le b$ not all zero, and
$t \ge 0$,
$$\mu\Bigl(\sum_i w_i \mathbf{x}_i^2 \ge c\,\Bigl(\sum_i w_i +
  2 \sqrt{\textstyle\sum_i w_i^2}\, \sqrt{t} + 2 b t\Bigr)\Bigr) \le e^{-t}\,.$$
Hsu, Kakade and Zhang 2012, Theorem 2.1 for a diagonal matrix; for a standard Gaussian vector,
Laurent and Massart's weighted bound. The form Gaussian Hutchinson trace-estimator tails use.
$\mathbf{w} \ne \mathbf{0}$ and $c \ne 0$ are needed for the non-strict event: otherwise the
threshold is $0$ at $t = 0$ and $2 b t$ in general, and the event can be everything.
The proof: Gaussian linearisation at $\sqrt{\mathbf{w}} \odot \mathbf{g}$, the weighted
$\chi^2$ transform, Laurent and Massart's log-moment bound, then
`NLAlib.measureReal_ge_le_exp_neg_of_mgf_le` with variance factor $2 c^2 \sum_i w_i^2$ and scale
$2 c b$. -/
theorem measureReal_sum_mul_sq_ge_le (h : IsSubgaussianVector x c μ) (hc : c ≠ 0) {w : n → ℝ}
    (hw : ∀ i, 0 ≤ w i) (hw0 : w ≠ 0) {b : ℝ} (hwb : ∀ i, w i ≤ b) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | c * (∑ i, w i + 2 * √(∑ i, w i ^ 2) * √t + 2 * b * t) ≤
      ∑ i, w i * x ω i ^ 2} ≤ Real.exp (-t) := by
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra! H
    exact hw0 (funext H)
  have hb : 0 ≤ b := (hw j).trans (hwb j)
  have hS : 0 < ∑ i, w i ^ 2 :=
    Finset.sum_pos' (fun i _ => sq_nonneg _)
      ⟨j, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (pow_ne_zero 2 hj).symm⟩
  set v : ℝ := 2 * c ^ 2 * ∑ i, w i ^ 2 with hv_def
  have hv : 0 < v := by positivity
  have hb' : 0 ≤ 2 * c * b := by positivity
  have hint : ∀ θ : ℝ, 0 ≤ θ → 2 * c * b * θ < 1 →
      Integrable (fun ω => Real.exp (θ * (∑ i, w i * x ω i ^ 2 - c * ∑ i, w i))) μ := by
    intro θ hθ hbθ
    rw [exp_mul_sub_eq]
    exact (h.integrable_exp_mul_sum_mul_sq hw hθ fun i =>
      (two_mul_le_of_le hwb hθ i).trans_lt hbθ).const_mul _
  have key := measureReal_ge_le_exp_neg_of_mgf_le hv hb' hint
    (fun θ hθ hbθ => h.mgf_sum_mul_sq_sub_le hw hwb hθ hbθ) ht
  have hsq : √(2 * v * t) = 2 * c * √(∑ i, w i ^ 2) * √t := by
    rw [show 2 * v * t = (2 * c) ^ 2 * ((∑ i, w i ^ 2) * t) by rw [hv_def]; ring,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity), Real.sqrt_mul hS.le]
    ring
  refine le_trans (le_of_eq ?_) key
  congr 1
  ext ω
  simp only [Set.mem_ofPred_eq, hsq]
  constructor <;> intro hω <;> linarith

/-- **The Hsu–Kakade–Zhang tail**: for a real sub-Gaussian vector $\mathbf{x}$ with proxy
$c \ne 0$, a nonzero matrix $\mathbf{A}$ over $\Bbbk$ acting on $\mathbf{x}$, and $t \ge 0$,
$$\mu\Bigl(\|\mathbf{A}\mathbf{x}\|^2 \ge c\,\bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 +
  2 \|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}} \sqrt{t} +
  2 \|\mathbf{A}\|_2^2\, t\bigr)\Bigr) \le e^{-t}\,.$$
Hsu, Kakade and Zhang 2012, Theorem 2.1 (there $\Bbbk = \mathbb{R}$; the real case is this one
through `RCLike.ofReal_real_eq_id`). There is no field factor because $\mathbf{x}$ is real: the
stacked real matrix $\mathbf{A}_r = \begin{bmatrix} \operatorname{Re}\mathbf{A} \\
\operatorname{Im}\mathbf{A} \end{bmatrix}$ has the same Frobenius norm, spectral norm at most
$\|\mathbf{A}\|_2$, $\|\mathbf{A}_r^{\mathsf{T}}\mathbf{A}_r\|_{\mathsf{F}} \le
\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}}$ (it is
$\operatorname{Re}(\mathbf{A}^{\mathsf{H}} \mathbf{A})$), and the same image norm on real
vectors. A complex $\mathbf{x}$ would double
$\|\mathbf{A}\|_{\mathsf{F}}^2$ (the realified operator is
$\begin{bmatrix} \operatorname{Re}\mathbf{A} & -\operatorname{Im}\mathbf{A} \\
\operatorname{Im}\mathbf{A} & \operatorname{Re}\mathbf{A} \end{bmatrix}$).
$\mathbf{A} \ne \mathbf{0}$ and $c \ne 0$ are needed for the non-strict event, as in
`NLAlib.IsSubgaussianVector.measureReal_sum_mul_sq_ge_le`. The case $\mathbf{A} = \mathbf{I}$ is
`NLAlib.IsSubgaussianVector.measureReal_norm_sq_ge_le`.
The proof: the diagonal form at the eigenvalues $\lambda_i$ of
$\mathbf{A}_r^{\mathsf{T}}\mathbf{A}_r = \operatorname{Re}(\mathbf{A}^{\mathsf{H}}\mathbf{A})
= \mathbf{V} \operatorname{diag}(\boldsymbol{\lambda}) \mathbf{V}^{\mathsf{T}}$ (the spectral
theorem over $\mathbb{R}$; $\mathbf{V}^{\mathsf{T}}\mathbf{x}$ has proxy $c$ by
`NLAlib.IsSubgaussianVector.mulVec`), whose sum is $\|\mathbf{A}\|_{\mathsf{F}}^2$, whose squares
sum to at most $\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}}^2$, and which are at most
$\|\mathbf{A}\|_2^2$.
Result: hsu-kakade-zhang -/
theorem measureReal_norm_mulVec_sq_ge_le {m : Type*} [Fintype m] {𝕜 : Type*} [RCLike 𝕜]
    (h : IsSubgaussianVector x c μ) (hc : c ≠ 0) {A : Matrix m n 𝕜} (hA : A ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | c * (frobNorm A ^ 2 + 2 * frobNorm (Aᴴ * A) * √t + 2 * specNorm A ^ 2 * t) ≤
      ‖WithLp.toLp 2 (A *ᵥ fun i => (x ω i : 𝕜))‖ ^ 2} ≤ Real.exp (-t) := by
  classical
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  obtain ⟨V, lam, hV, hquad, hlam0, hlamb, hsum, hsq⟩ := exists_gram_diagonalisation (𝕜 := 𝕜) A
  have hlam_ne : lam ≠ 0 := by
    intro h0
    apply hA
    rw [← frobNorm_eq_zero_iff, ← pow_eq_zero_iff two_ne_zero, ← hsum, h0]
    simp
  have hz : IsSubgaussianVector (fun ω => Vᴴ *ᵥ x ω) c μ := by
    refine (h.mulVec Vᴴ).mono (mul_le_of_le_one_right' (pow_le_one₀ bot_le ?_))
    rw [← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one, Real.norm_of_nonneg (specNorm_nonneg _),
      specNorm_conjTranspose]
    exact hV.specNorm_le_one
  have hc0 : (0 : ℝ) ≤ c := c.2
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _))
    (hz.measureReal_sum_mul_sq_ge_le hc hlam0 hlam_ne hlamb ht)
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [hquad] at hω
  refine le_trans ?_ hω
  rw [hsum]
  gcongr

/-- **The upper tail of $\|\mathbf{x}\|^2$** for a real sub-Gaussian vector with proxy
$c \ne 0$: for $t \ge 0$, with $n = \lvert n\rvert$,
$$\mu\bigl(\|\mathbf{x}\|^2 \ge c\,(n + 2\sqrt{n t} + 2t)\bigr) \le e^{-t}\,.$$
Hsu, Kakade and Zhang 2012, Theorem 2.1 with $\mathbf{A} = \mathbf{I}$; for a standard Gaussian
vector this is Laurent and Massart's bound. $c \ne 0$ is needed for the non-strict event: with
$c = 0$ the vector is $\mathbf{0}$ almost surely and the event is everything. The case
$\mathbf{A} = \mathbf{I}$ of `NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le`. -/
theorem measureReal_norm_sq_ge_le (h : IsSubgaussianVector x c μ) (hc : c ≠ 0) {t : ℝ}
    (ht : 0 ≤ t) :
    μ.real {ω | c * (Fintype.card n + 2 * √(Fintype.card n * t) + 2 * t) ≤
      ‖WithLp.toLp 2 (x ω)‖ ^ 2} ≤ rexp (-t) := by
  have := (h.hasSubgaussianMGF 0).isFiniteMeasure
  have hc0 : (0 : ℝ) < c := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  rcases ht.eq_or_lt with rfl | htpos
  · have huniv := h.integral_exp_mul_norm_sq_le le_rfl (by simp)
    simp only [zero_mul, exp_zero, integral_const, smul_eq_mul, mul_one, mul_zero, sub_zero,
      one_rpow] at huniv
    rw [neg_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans huniv
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card n)).eq_or_lt with hd | hd
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp (by exact_mod_cast hd.symm)
    have hset : {ω | c * (Fintype.card n + 2 * √(Fintype.card n * t) + 2 * t) ≤
        ‖WithLp.toLp 2 (x ω)‖ ^ 2} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le,
        EuclideanSpace.norm_toLp_sq_eq_sum_sq, Finset.univ_eq_empty, Finset.sum_empty, ← hd,
        zero_mul, sqrt_zero, mul_zero, zero_add]
      positivity
    rw [hset, measureReal_empty]
    positivity
  classical
  have : Nonempty n := Fintype.card_pos_iff.mp (by exact_mod_cast hd)
  have hF : frobNorm (1 : Matrix n n ℝ) = √(Fintype.card n) := by
    rw [← frobNorm_one_sq (𝕜 := ℝ), sqrt_sq (frobNorm_nonneg _)]
  have hS : specNorm (1 : Matrix n n ℝ) ^ 2 ≤ 1 := pow_le_one₀ (specNorm_nonneg _) specNorm_one_le
  refine le_trans (measureReal_mono (fun ω hω => ?_) (measure_ne_top _ _))
    (h.measureReal_norm_mulVec_sq_ge_le hc (one_ne_zero (α := Matrix n n ℝ)) ht)
  simp only [Set.mem_ofPred_eq, RCLike.ofReal_real_eq_id, id_eq, Matrix.one_mulVec,
    Matrix.conjTranspose_one, Matrix.mul_one, hF] at hω ⊢
  refine le_trans ?_ hω
  rw [sqrt_mul (Nat.cast_nonneg _), sq_sqrt (Nat.cast_nonneg _)]
  have : specNorm (1 : Matrix n n ℝ) ^ 2 * t ≤ t := mul_le_of_le_one_left ht hS
  refine mul_le_mul_of_nonneg_left ?_ hc0.le
  linarith

end IsSubgaussianVector

/-- The two-sided tail of $\|\mathbf{x}\|^2$ about its mean for a real vector with independent
coordinates, each sub-Gaussian with proxy $c$: for $t \ge 0$,
$$\mu\bigl(\bigl\lvert \|\mathbf{x}\|^2 - \mathbb{E}\|\mathbf{x}\|^2 \bigr\rvert \ge t\bigr)
\le 2 \exp\Bigl(-\min\Bigl(\frac{t^2}{2 \lvert n\rvert \cdot 32 c^2}, \frac{t}{2 \cdot 4c}\Bigr)
\Bigr)\,,$$
Bernstein's inequality for the centred squares, whose variance proxy and scale are $32 c^2$ and
$4 c$. -/
theorem measureReal_abs_norm_sq_sub_integral_ge_le (hind : iIndepFun (fun i ω => x ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |‖WithLp.toLp 2 (x ω)‖ ^ 2 - ∫ ω', ‖WithLp.toLp 2 (x ω')‖ ^ 2 ∂μ|} ≤
      2 * rexp (-min (t ^ 2 / (2 * (Fintype.card n * (32 * c ^ 2)))) (t / (2 * (4 * c)))) := by
  have := hind.isProbabilityMeasure
  have hint : ∀ i, Integrable (fun ω => x ω i ^ 2) μ := fun i => ((h i).memLp 2).integrable_sq
  have hind' : iIndepFun (fun i ω => x ω i ^ 2 - ∫ ω', x ω' i ^ 2 ∂μ) μ :=
    hind.comp (fun i y => y ^ 2 - ∫ ω', x ω' i ^ 2 ∂μ) fun i => by fun_prop
  have hsum := (HasSubexponentialMGF.sum_of_iIndepFun hind' (s := Finset.univ)
    fun i _ => (h i).hasSubexponentialMGF_sq_sub_integral).mono le_rfl
      (Finset.sup_le fun i _ => le_rfl)
  have hfun : ∀ ω, ‖WithLp.toLp 2 (x ω)‖ ^ 2 - ∫ ω', ‖WithLp.toLp 2 (x ω')‖ ^ 2 ∂μ =
      ∑ i, (x ω i ^ 2 - ∫ ω', x ω' i ^ 2 ∂μ) := by
    intro ω
    simp only [EuclideanSpace.norm_toLp_sq_eq_sum_sq]
    rw [integral_finsetSum _ fun i _ => hint i, Finset.sum_sub_distrib]
  have hv : ((∑ _i : n, 32 * c ^ 2 : ℝ≥0) : ℝ) = Fintype.card n * (32 * (c : ℝ) ^ 2) := by
    push_cast
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hb : ((4 * c : ℝ≥0) : ℝ) = 4 * c := by push_cast; ring
  have key := hsum.measureReal_abs_ge_le ht
  rw [hv, hb] at key
  simp only [hfun]
  exact key

end NLAlib
