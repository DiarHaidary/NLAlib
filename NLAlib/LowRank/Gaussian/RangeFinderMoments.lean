/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder

/-!
# Coupled spectral moments of the Gaussian range finder

The spectral and Frobenius residuals at a comparison rank share the same input tail energy.
Retaining this coupling improves the spectral residual constant at larger sketch dimensions.

## Main results

* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_add_of_hasLaw_gaussianMatrix`:
  expected Frobenius error using a comparison-rank tail.

* The expected squared spectral residual is at most ten times the rank-$k$ Frobenius tail,
  divided by the sketch width, when that width is at least $200k$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The width sufficient for the spectral-residual constant ten,
at present <!-- value gaussianRangeFinderResidualDim k --> $200k$.
No printed source. -/
irreducible_def gaussianRangeFinderResidualDim (k : ℕ) : ℕ := 200 * k

/-- The Gaussian range-finder spectral-residual constant at width at least $200k$,
at present <!-- value gaussianRangeFinderResidualConstant --> $10$.
No printed source. -/
irreducible_def gaussianRangeFinderResidualConstant : ℝ := 10

/-- The sufficient residual width is at most $200k$. No printed source. -/
theorem gaussianRangeFinderResidualDim_le (k : ℕ) :
    gaussianRangeFinderResidualDim k ≤ 200 * k := by
  rw [gaussianRangeFinderResidualDim_def]

/-- The residual constant is positive. No printed source. -/
theorem gaussianRangeFinderResidualConstant_pos : 0 < gaussianRangeFinderResidualConstant := by
  rw [gaussianRangeFinderResidualConstant_def]
  norm_num

/-- The residual constant is at most ten. No printed source. -/
theorem gaussianRangeFinderResidualConstant_le : gaussianRangeFinderResidualConstant ≤ 10 := by
  rw [gaussianRangeFinderResidualConstant_def]

private theorem mul_gaussianPinvSpecNormBound_sq_le_of_fifth {L j : ℕ}
    (hL : 200 ≤ L) (hj : j = L / 5) :
    (L : ℝ) * gaussianPinvSpecNormBound j L ^ 2 ≤ 6.93 := by
  have hJ : 5 * j ≤ L := by omega
  have hJ' : 5 * (j : ℝ) ≤ L := by exact_mod_cast hJ
  have hL' : (200 : ℝ) ≤ L := by exact_mod_cast hL
  have hLj : 0 < (L : ℝ) - j := by linarith
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have he2 : Real.exp 1 ^ 2 ≤ 7.3891 := by nlinarith
  rw [gaussianPinvSpecNormBound_def, mul_pow, div_pow, Real.sq_sqrt (by linarith),
    show (L : ℝ) * (Real.exp 1 ^ 2 / ((L : ℝ) - j) ^ 2 * (((L : ℝ) + j - 1) / 2)) =
      Real.exp 1 ^ 2 * ((L : ℝ) * ((L : ℝ) + j - 1)) / (2 * ((L : ℝ) - j) ^ 2) by
        field_simp,
    div_le_iff₀ (by positivity)]
  have hA : (L : ℝ) * ((L : ℝ) + j - 1) ≤ 1.2 * (L : ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hJ' (by linarith : (0 : ℝ) ≤ L)]
  have hB : 0.64 * (L : ℝ) ^ 2 ≤ ((L : ℝ) - j) ^ 2 := by
    have h1 : 0.8 * (L : ℝ) ≤ (L : ℝ) - j := by linarith
    nlinarith [sq_nonneg ((L : ℝ) - j - 0.8 * L)]
  have hD := mul_le_mul he2 hA (by nlinarith : 0 ≤ (L : ℝ) * ((L : ℝ) + j - 1))
    (by norm_num : (0 : ℝ) ≤ 7.3891)
  nlinarith

private theorem coupled_residual_arith {L d u w O h β : ℝ} (hL : 200 ≤ L)
    (hd : 0.19 * L ≤ d) (hh0 : 0 ≤ h) (hh : h ≤ 0.252)
    (hβ : L * β ^ 2 ≤ 6.93) (hflat : w ^ 2 + d * u ^ 2 ≤ O ^ 2) :
    u ^ 2 + (u * √h + β * w) ^ 2 + (u * β) ^ 2 ≤ 10 / L * O ^ 2 := by
  have hL0 : 0 < L := by linarith
  have hcross : 2 * u * √h * β * w ≤ 0.6 * u ^ 2 + (5 / 3 : ℝ) * β ^ 2 * h * w ^ 2 := by
    have hs := sq_nonneg (3 * u - 5 * β * √h * w)
    ring_nf at hs
    rw [Real.sq_sqrt hh0] at hs
    nlinarith only [hs]
  have hhead : L * (1 + h + β ^ 2 + 0.6) ≤ 10 * d := by
    nlinarith [mul_le_mul_of_nonneg_left hh hL0.le]
  have htail : L * (1 + (5 / 3 : ℝ) * h) * β ^ 2 ≤ 10 := by
    calc L * (1 + (5 / 3 : ℝ) * h) * β ^ 2 = (L * β ^ 2) * (1 + (5 / 3 : ℝ) * h) := by ring
      _ ≤ 6.93 * (1 + (5 / 3 : ℝ) * 0.252) :=
        mul_le_mul hβ (by linarith) (by positivity) (by norm_num)
      _ ≤ 10 := by norm_num
  rw [div_mul_eq_mul_div, le_div_iff₀ hL0]
  have h1 := mul_le_mul_of_nonneg_right hhead (sq_nonneg u)
  have h2 := mul_le_mul_of_nonneg_right htail (sq_nonneg w)
  have h3 := mul_le_mul_of_nonneg_left hcross hL0.le
  simp only [add_sq, mul_pow, Real.sq_sqrt hh0]
  nlinarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l]
  {X : Ω → Matrix n l ℝ}

-- The declaration name alone exceeds the line limit.
set_option linter.style.longLine false in
/-- The coupled spectral residual of the Gaussian range finder: for a standard Gaussian
$n \times \ell$ matrix, $1 \le k$ and
at present <!-- value gaussianRangeFinderResidualDim k --> $200k \le \ell$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},\mathbf{X})\|_2^2
\le \frac{10}{\ell}\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
The numerator is <!-- value gaussianRangeFinderResidualConstant --> $10$.
The comparison-rank argument retains the coupled spectral and Frobenius tail energy.
No printed source. -/
theorem
    integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix_of_gaussianRangeFinderResidualDim_le
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k)
    (hkl : gaussianRangeFinderResidualDim k ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianRangeFinderResidualConstant / (Fintype.card l : ℝ) *
        frobNorm (A - truncatedSVD A k) ^ 2 := by
  set L := Fintype.card l with hLdef
  set j := L / 5 with hjdef
  have h200 : 200 * k ≤ L := by
    rwa [gaussianRangeFinderResidualDim_def] at hkl
  have hL : 200 ≤ L := by omega
  have hj2 : j + 2 ≤ L := by omega
  have hkj : k ≤ j := by omega
  have hdim : 19 * L ≤ 100 * (j - k) := by omega
  have hd : 0.19 * (L : ℝ) ≤ ((j - k : ℕ) : ℝ) := by
    have hdim' : 19 * (L : ℝ) ≤ 100 * ((j - k : ℕ) : ℝ) := by exact_mod_cast hdim
    linarith
  have hJ : 5 * j ≤ L := by omega
  have hJ' : 5 * (j : ℝ) ≤ L := by exact_mod_cast hJ
  have hL' : (200 : ℝ) ≤ L := by exact_mod_cast hL
  have hden : 0 < (L : ℝ) - j - 1 := by linarith
  have hh0 : 0 ≤ (j : ℝ) / ((L : ℝ) - j - 1) :=
    div_nonneg (Nat.cast_nonneg _) hden.le
  have hh : (j : ℝ) / ((L : ℝ) - j - 1) ≤ 0.252 := by
    rw [div_le_iff₀ hden]
    linarith
  have hflat := frobNorm_sub_truncatedSVD_sq_add_natCast_mul_singularValues_sq_le A k (j - k)
  rw [Nat.add_sub_cancel' hkj] at hflat
  have hmain := integral_specNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_pinvSpecNormBound A hX
    (by simpa only [hLdef] using hj2)
  apply hmain.trans
  rw [gaussianRangeFinderResidualConstant_def]
  change _ ≤ 10 / (L : ℝ) * frobNorm (A - truncatedSVD A k) ^ 2
  exact coupled_residual_arith hL' hd hh0 hh
    (mul_gaussianPinvSpecNormBound_sq_le_of_fifth hL hjdef) hflat


variable {Ω₀ : Type*} {mΩ₀ : MeasurableSpace Ω₀} {μ₀ : Measure Ω₀}
  {m₀ n₀ l₀ : Type*} [Fintype m₀] [Fintype n₀] [Fintype l₀]
  {X₀ : Ω₀ → Matrix n₀ l₀ ℝ}

/-- The expected rank-$k$ Frobenius error of the Gaussian range finder, using a comparison
rank $j\ge k$: the excess is at most $k/(\ell-j-1)$ times the Frobenius tail at rank $j$.
No printed source. -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_add_of_hasLaw_gaussianMatrix
    (A : Matrix m₀ n₀ ℝ) (hX : HasLaw X₀ (gaussianMatrix n₀ l₀) μ₀)
    {k j : ℕ} (hkj : k ≤ j) (hjl : j + 2 ≤ Fintype.card l₀) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X₀ ω)) k) ^ 2 ∂μ₀ ≤
      frobNorm (A - truncatedSVD A k) ^ 2 +
        (k : ℝ) / ((Fintype.card l₀ : ℝ) - j - 1) *
          frobNorm (A - truncatedSVD A j) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt j (Fintype.card n₀) with hjn | hjn
  · obtain ⟨Z, V, hZ, hV, hZV, hcomp, -, -, hprefix⟩ :=
      exists_hasOrthonormalCols_conjTranspose_mul_self_mul_eq_mul_diagonal A hjn
    let W := Z.submatrix id (Fin.castLE hkj)
    have hW : HasOrthonormalCols W := hZ.submatrix (Equiv.refl n₀) (Fin.castLE_injective hkj)
    have hZA : A * Z * Zᴴ = truncatedSVD A j := by simpa using hprefix j le_rfl
    have hWA : A * W * Wᴴ = truncatedSVD A k := hprefix k hkj
    have hJ : Zᴴ * W = (Zᴴ * Z).submatrix id (Fin.castLE hkj) := rfl
    rw [hZ.conjTranspose_mul_self] at hJ
    have hZW : Z * (Zᴴ * W) = W := by
      rw [hJ]
      exact Matrix.mul_submatrix_one (Equiv.refl _) _ Z
    have hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin :=
      range_le_iff_exists_mul.mpr ⟨Zᴴ * W, hZW.symm⟩
    have hJn : frobNorm (Zᴴ * W) ^ 2 = k := by
      rw [← hZ.frobNorm_mul_left (Zᴴ * W), hZW, hW.frobNorm_sq, Fintype.card_fin]
    have hVV : V * Vᴴ = 1 - Z * Zᴴ := by rw [← hcomp]; abel
    have hEZ := hZ.sub_mul_mul_conjTranspose_mul_eq_zero A
    have hEV : (A - truncatedSVD A j) * V * Vᴴ = A - truncatedSVD A j := by
      rw [← hZA, Matrix.mul_assoc, hVV, Matrix.mul_sub, Matrix.mul_one,
        ← Matrix.mul_assoc, hEZ, Matrix.zero_mul, sub_zero]
    have hnorm : frobNorm ((A - truncatedSVD A j) * V) = frobNorm (A - truncatedSVD A j) := by
      rw [← hV.frobNorm_mul_conjTranspose_right ((A - truncatedSVD A j) * V), hEV]
    have hjl' : Fintype.card (Fin j) + 2 ≤ Fintype.card l₀ := by simpa using hjl
    obtain ⟨hMi, hM⟩ := integral_frobNorm_mul_mul_pinv_mul_sq_of_hasLaw_gaussianMatrix
      hX hZ hV hZV hjl' ((A - truncatedSVD A j) * V) (Zᴴ * W)
    have hpt : ∀ᵐ ω ∂μ₀,
        frobNorm (A - truncatedSVD (rsvd A (X₀ ω)) k) ^ 2 ≤
          frobNorm (A - truncatedSVD A k) ^ 2 +
            frobNorm ((A - truncatedSVD A j) * V * (Vᴴ * X₀ ω) *
              pinv (Zᴴ * X₀ ω) * (Zᴴ * W)) ^ 2 := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix Z hX
        (by rw [hZ.rank_eq, Fintype.card_fin]; omega)] with ω hω
      have hp := hZ.frobNorm_sub_rangeProjector_mul_mul_conjTranspose_sq_le hW hWZ hω A
      rw [hWA, hZA] at hp
      have hb : (A - truncatedSVD A j) * X₀ ω * pinv (Zᴴ * X₀ ω) =
          (A - truncatedSVD A j) * V * (Vᴴ * X₀ ω) * pinv (Zᴴ * X₀ ω) := by
        rw [← Matrix.mul_assoc ((A - truncatedSVD A j) * V), hEV]
      rw [hb] at hp
      exact (frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add A (X₀ ω) k).trans
        (add_le_add le_rfl hp)
    have hi := (integrable_const (frobNorm (A - truncatedSVD A k) ^ 2)).add hMi
    refine (integral_mono_ae (integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k)
      hi hpt).trans_eq ?_
    simp only [Pi.add_apply]
    rw [integral_add (integrable_const _) hMi, integral_const, probReal_univ, one_smul, hM,
      hnorm, hJn, Fintype.card_fin]
    ring
  · have hae := ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX
      (A.rank_le_card_width.trans (by omega))
    rw [integral_congr_ae (hae.mono fun ω hω => by rw [hω]), integral_const,
      probReal_univ, one_smul]
    have hd : 0 ≤ (Fintype.card l₀ : ℝ) - j - 1 := by
      have : (j : ℝ) + 2 ≤ Fintype.card l₀ := by exact_mod_cast hjl
      linarith
    exact le_add_of_nonneg_right (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hd) (sq_nonneg _))

end NLAlib
