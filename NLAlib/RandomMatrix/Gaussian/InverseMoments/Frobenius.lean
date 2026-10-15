/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.InverseMoments

/-!
# Frobenius moments of the pseudoinverse of a Gaussian matrix

For a wide standard Gaussian $r \times k$ matrix $\mathbf{G}$, the second and fourth moments of
$\|\mathbf{G}^{+}\|_{\mathsf{F}}$ that the randomized range finder consumes (Halko, Martinsson
and Tropp 2011, Propositions 10.2 and 10.3):
$\mathbb{E} \|\mathbf{G}^{+}\|_{\mathsf{F}}^2
= \lvert r \rvert / (\lvert k \rvert - \lvert r \rvert - 1)$ and the fourth moment. Almost surely
$\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 = \operatorname{tr} (\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$,
so both reduce to the moments of the entries of the inverse Wishart matrix
(`NLAlib.RandomMatrix.Gaussian.InverseMoments`). The spectral moments of $\mathbf{G}^{+}$
(Proposition 10.4) are in `NLAlib.RandomMatrix.Gaussian.InverseMoments.Spectral`.

Split from `NLAlib.RandomMatrix.Gaussian.InverseMoments` on 2026-10-15
(`docs/design/LowRank-S3.md`).

## Main results

* `NLAlib.integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix`, with their integrability.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {r k : Type*} [Fintype r]
  [Fintype k] {X : Ω → Matrix r k ℝ}

/-- Almost surely
$\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 = \operatorname{tr} (\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$. -/
private theorem ae_frobNorm_pinv_sq_eq_sum [DecidableEq r] (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) :
    ∀ᵐ ω ∂μ, frobNorm (pinv (X ω)) ^ 2 = ∑ i, (X ω * (X ω)ᴴ)⁻¹ i i := by
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hX] with ω hω
  have hinj : Function.Injective (X ω)ᴴ.mulVec := by
    rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose, hω, min_eq_left hrk]
  rw [frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose hinj, RCLike.re_to_real]
  rfl

/-- $\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$ is integrable for a standard Gaussian $r \times k$ matrix
with $\lvert r \rvert + 2 \le \lvert k \rvert$. -/
theorem integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω)) ^ 2) μ := by
  classical
  refine (integrable_finsetSum Finset.univ fun i _ =>
    integrable_mul_conjTranspose_inv_apply_of_hasLaw_gaussianMatrix hX hrk i i).congr ?_
  filter_upwards [ae_frobNorm_pinv_sq_eq_sum hX (by omega)] with ω hω
  rw [hω]

/-- **$\mathbb{E} \|\mathbf{G}^{+}\|_{\mathsf{F}}^2
= \lvert r \rvert / (\lvert k \rvert - \lvert r \rvert - 1)$** for a standard Gaussian $r \times k$
matrix $\mathbf{G}$ with $\lvert r \rvert + 2 \le \lvert k \rvert$ (Halko, Martinsson and Tropp,
Proposition 10.2). -/
theorem integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ^ 2 ∂μ =
      (Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1) := by
  classical
  rw [integral_congr_ae (ae_frobNorm_pinv_sq_eq_sum hX (by omega)),
    integral_finsetSum _ fun i _ =>
      integrable_mul_conjTranspose_inv_apply_of_hasLaw_gaussianMatrix hX hrk i i]
  simp only [integral_mul_conjTranspose_inv_apply_of_hasLaw_gaussianMatrix hX hrk,
    Matrix.one_apply_eq, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, div_eq_mul_inv]

private theorem aestronglyMeasurable_frobNorm_pinv (hX : HasLaw X (gaussianMatrix r k) μ) :
    AEStronglyMeasurable (fun ω => frobNorm (pinv (X ω))) μ :=
  ((measurable_frobNorm.comp measurable_pinv).comp_aemeasurable
    hX.aemeasurable).aestronglyMeasurable

private theorem memLp_frobNorm_pinv (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    MemLp (fun ω => frobNorm (pinv (X ω))) 2 μ :=
  (memLp_two_iff_integrable_sq (aestronglyMeasurable_frobNorm_pinv hX)).2
    (integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hX hrk)

/-- $\|\mathbf{G}^{+}\|_{\mathsf{F}}$ is integrable for a standard Gaussian $r \times k$ matrix
with $\lvert r \rvert + 2 \le \lvert k \rvert$. -/
theorem integrable_frobNorm_pinv_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω))) μ := by
  have := hX.isProbabilityMeasure
  exact (memLp_frobNorm_pinv hX hrk).integrable one_le_two

/-- $\mathbb{E} \|\mathbf{G}^{+}\|_{\mathsf{F}}
\le \sqrt{\lvert r \rvert / (\lvert k \rvert - \lvert r \rvert - 1)}$ for a standard Gaussian
$r \times k$ matrix with $\lvert r \rvert + 2 \le \lvert k \rvert$, by Jensen. -/
theorem integral_frobNorm_pinv_le_of_hasLaw_gaussianMatrix (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ∂μ ≤
      √((Fintype.card r : ℝ) / ((Fintype.card k : ℝ) - Fintype.card r - 1)) := by
  have := hX.isProbabilityMeasure
  have hvar := variance_nonneg (fun ω => frobNorm (pinv (X ω))) μ
  rw [variance_eq_sub (memLp_frobNorm_pinv hX hrk)] at hvar
  refine (le_abs_self _).trans (Real.abs_le_sqrt ?_)
  rw [← integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hX hrk]
  simp only [Pi.pow_apply] at hvar
  linarith

private theorem ae_frobNorm_pinv_pow_four_eq [DecidableEq r] (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r ≤ Fintype.card k) :
    ∀ᵐ ω ∂μ, frobNorm (pinv (X ω)) ^ 4 =
      ∑ i, ∑ j, (X ω * (X ω)ᴴ)⁻¹ i i * (X ω * (X ω)ᴴ)⁻¹ j j := by
  filter_upwards [ae_frobNorm_pinv_sq_eq_sum hX hrk] with ω hω
  rw [show 4 = 2 * 2 by rfl, pow_mul, hω, sq, Finset.sum_mul_sum]

/-- $\|\mathbf{G}^{+}\|_{\mathsf{F}}^4$ is integrable for a standard Gaussian $r \times k$ matrix
with $\lvert r \rvert + 4 \le \lvert k \rvert$. -/
theorem integrable_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 4 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (X ω)) ^ 4) μ := by
  classical
  have hint (i j : r) : Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ i i * (X ω * (X ω)ᴴ)⁻¹ j j) μ :=
    (memLp_mul_conjTranspose_inv_apply_of_hasLaw_gaussianMatrix hX hrk i i).integrable_mul
      (memLp_mul_conjTranspose_inv_apply_of_hasLaw_gaussianMatrix hX hrk j j)
  refine (integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ => hint i j).congr ?_
  filter_upwards [ae_frobNorm_pinv_pow_four_eq hX (by omega)] with ω hω
  rw [hω]

/-- The fourth moment of $\|\mathbf{G}^{+}\|_{\mathsf{F}}$ (Halko, Martinsson and Tropp,
Proposition 10.3): for a standard Gaussian $r \times k$ matrix $\mathbf{G}$ with
$\lvert r \rvert + 4 \le \lvert k \rvert$, writing $r$, $k$ for $\lvert r \rvert$,
$\lvert k \rvert$,
$$\mathbb{E} \|\mathbf{G}^{+}\|_{\mathsf{F}}^4
= \frac{r^2 (k - r) - 2 r (r - 1)}{(k - r)(k - r - 1)(k - r - 3)} \,.$$ -/
theorem integral_frobNorm_pinv_pow_four_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix r k) μ) (hrk : Fintype.card r + 4 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (X ω)) ^ 4 ∂μ =
      ((Fintype.card r : ℝ) ^ 2 * ((Fintype.card k : ℝ) - Fintype.card r) -
          2 * Fintype.card r * ((Fintype.card r : ℝ) - 1)) /
        (((Fintype.card k : ℝ) - Fintype.card r) * ((Fintype.card k : ℝ) - Fintype.card r - 1) *
          ((Fintype.card k : ℝ) - Fintype.card r - 3)) := by
  classical
  have hint (i j : r) : Integrable (fun ω => (X ω * (X ω)ᴴ)⁻¹ i i * (X ω * (X ω)ᴴ)⁻¹ j j) μ :=
    (memLp_mul_conjTranspose_inv_apply_of_hasLaw_gaussianMatrix hX hrk i i).integrable_mul
      (memLp_mul_conjTranspose_inv_apply_of_hasLaw_gaussianMatrix hX hrk j j)
  rw [integral_congr_ae (ae_frobNorm_pinv_pow_four_eq hX (by omega)),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  simp only [integral_finsetSum _ fun j _ => hint _ j,
    integral_mul_conjTranspose_inv_apply_self_mul_of_hasLaw_gaussianMatrix hX hrk]
  have hone (i : r) : ∑ j, (1 : Matrix r r ℝ) i j = 1 := by
    simp only [Matrix.one_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [← Finset.sum_div, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, hone]
  have hkr : (Fintype.card r : ℝ) + 4 ≤ Fintype.card k := by exact_mod_cast hrk
  have h1 : (Fintype.card k : ℝ) - Fintype.card r ≠ 0 := by linarith
  have h2 : (Fintype.card k : ℝ) - Fintype.card r - 1 ≠ 0 := by linarith
  have h3 : (Fintype.card k : ℝ) - Fintype.card r - 3 ≠ 0 := by linarith
  field_simp

end NLAlib
