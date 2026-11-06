/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.Householder
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Perturbation.OrthErr

/-!
# Symmetric backward perturbations from orthonormal bases

The matrix facts behind the backward model of Lanczos with full reorthogonalization: the
symmetric completion of a residual against an orthonormal basis [KahanParlettJiang1982], the
polar factor `NLAlib.polarFactor` of a nearly orthonormal basis, an orthogonal map close to the
identity sending one unit vector to another (a product of two reflectors), and the count of
eigenvalues near orthonormal approximate eigenvectors with small residuals. Design:
`docs/design/Krylov-LanczosReorth.md` §3.3.

## Main results

* `NLAlib.HasOrthonormalCols.exists_transpose_eq_mul_eq_neg`: the symmetric completion of a
  residual.
* `NLAlib.hasOrthonormalCols_polarFactor`, `NLAlib.frobNorm_polarFactor_sub_le`: the polar
  factor of a nearly orthonormal basis.
* `NLAlib.exists_orthogonal_mulVec_eq_specNorm_sub_one_le`: a rotation taking one unit vector to
  another.
* `Matrix.IsHermitian.card_le_card_eigenvalue_mem_of_hasOrthonormalCols`: orthonormal approximate
  eigenvectors are counted by the spectrum.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The symmetric completion of a residual**: for $\mathbf{U}$ with orthonormal columns
and $\mathbf{R}$ with $\mathbf{U}^{\mathsf{T}}\mathbf{R}$ symmetric, the symmetric
$\mathbf{E} = -\mathbf{R}\mathbf{U}^{\mathsf{T}} - \mathbf{U}\mathbf{R}^{\mathsf{T}} +
\mathbf{U}(\mathbf{U}^{\mathsf{T}}\mathbf{R})\mathbf{U}^{\mathsf{T}}$ satisfies
$\mathbf{E}\mathbf{U} = -\mathbf{R}$, $\|\mathbf{E}\|_{\mathsf F} \le
\sqrt2\,\|\mathbf{R}\|_{\mathsf F}$
and $\|\mathbf{E}\|_2 \le 2\|\mathbf{R}\|_2$. [KahanParlettJiang1982] (locator to verify). -/
theorem HasOrthonormalCols.exists_transpose_eq_mul_eq_neg {n k : ℕ}
    {U : Matrix (Fin n) (Fin k) ℝ} (hU : HasOrthonormalCols U) {R : Matrix (Fin n) (Fin k) ℝ}
    (hR : (Uᵀ * R)ᵀ = Uᵀ * R) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ E * U = -R ∧
      frobNorm E ≤ Real.sqrt 2 * frobNorm R ∧ specNorm E ≤ 2 * specNorm R := by
  have hUU : Uᵀ * U = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hU
  have hRU : Rᵀ * U = Uᵀ * R := by
    rw [← hR, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQU : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hUU, Matrix.mul_one, sub_self]
  have hP : IsStarProjection (1 - U * Uᵀ) := by
    have h := isStarProjection_rangeProjector U
    rw [hU.rangeProjector_eq, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h.one_sub
  have hQn : specNorm (1 - U * Uᵀ) ≤ 1 := hP.specNorm_le_one
  have hUn : specNorm Uᵀ ≤ 1 := by
    rw [specNorm_transpose]
    exact hU.specNorm_le_one
  refine ⟨-(R * Uᵀ + U * Rᵀ * (1 - U * Uᵀ)), ?_, ?_, ?_, ?_⟩
  · have hX : U * Rᵀ * (U * Uᵀ) = U * (Uᵀ * R) * Uᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hRU]
      simp only [Matrix.mul_assoc]
    simp only [Matrix.transpose_neg, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc] at hX ⊢
    rw [hX]
    abel
  · rw [Matrix.neg_mul, Matrix.add_mul]
    simp only [Matrix.mul_assoc, hUU, hQU, Matrix.mul_one, Matrix.mul_zero, add_zero]
  · rw [frobNorm_neg]
    have htr : ((R * Uᵀ)ᵀ * (U * Rᵀ * (1 - U * Uᵀ))).trace = 0 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose,
        show U * Rᵀ * (U * Rᵀ * (1 - U * Uᵀ)) = (U * Rᵀ * (U * Rᵀ)) * (1 - U * Uᵀ) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [← Matrix.mul_assoc, hQU, Matrix.zero_mul, Matrix.trace_zero]
    have hfA : frobNorm (R * Uᵀ) ≤ frobNorm R :=
      (frobNorm_mul_le_frobNorm_mul_specNorm R Uᵀ).trans
        (mul_le_of_le_one_right (frobNorm_nonneg R) hUn)
    have hfB : frobNorm (U * Rᵀ * (1 - U * Uᵀ)) ≤ frobNorm R := by
      rw [Matrix.mul_assoc, hU.frobNorm_mul_left]
      refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans ?_
      rw [frobNorm_transpose]
      exact mul_le_of_le_one_right (frobNorm_nonneg R) hQn
    have hsq := frobNorm_add_sq_of_frobInner_eq_zero (A := R * Uᵀ)
      (B := U * Rᵀ * (1 - U * Uᵀ)) (by
      rw [frobInner_eq_re_trace, Matrix.conjTranspose_eq_transpose_of_trivial, htr, map_zero])
    have h1 : frobNorm (R * Uᵀ) ^ 2 ≤ frobNorm R ^ 2 := pow_le_pow_left₀ (frobNorm_nonneg _) hfA 2
    have h2 : frobNorm (U * Rᵀ * (1 - U * Uᵀ)) ^ 2 ≤ frobNorm R ^ 2 :=
      pow_le_pow_left₀ (frobNorm_nonneg _) hfB 2
    have hs2 : (Real.sqrt 2 * frobNorm R) ^ 2 = 2 * frobNorm R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have hR0 : 0 ≤ Real.sqrt 2 * frobNorm R := by positivity
    nlinarith [frobNorm_nonneg (R * Uᵀ + U * Rᵀ * (1 - U * Uᵀ))]
  · rw [specNorm_neg]
    have hA : specNorm (R * Uᵀ) ≤ specNorm R :=
      (specNorm_mul_le R Uᵀ).trans (mul_le_of_le_one_right (specNorm_nonneg R) hUn)
    have hB : specNorm (U * Rᵀ * (1 - U * Uᵀ)) ≤ specNorm R := by
      rw [Matrix.mul_assoc, hU.specNorm_mul_left]
      refine (specNorm_mul_le _ _).trans ?_
      rw [specNorm_transpose]
      exact mul_le_of_le_one_right (specNorm_nonneg R) hQn
    linarith [specNorm_add_le (R * Uᵀ) (U * Rᵀ * (1 - U * Uᵀ))]

/-- **The polar factor of a nearly orthonormal basis is orthonormal**: if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta < 1$ then the polar factor
`NLAlib.polarFactor` $\mathbf{V}$, which for full column rank is
$\mathbf{V}(\mathbf{V}^{\mathsf{T}}\mathbf{V})^{-1/2}$, has orthonormal columns. [Higham2008,
Theorem 8.1]. -/
theorem hasOrthonormalCols_polarFactor {n m : ℕ} {V : Matrix (Fin n) (Fin m) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) (hη : η < 1) : HasOrthonormalCols (polarFactor V) := by
  rw [hasOrthonormalCols_polarFactor_iff]
  exact injective_mulVec_of_specNorm_transpose_mul_self_sub_one_lt_one (lt_of_le_of_lt hV hη)

/-- **The polar factor is close to a nearly orthonormal basis**: if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta < 1$ then
$$\|\operatorname{polar}(\mathbf{V}) - \mathbf{V}\|_{\mathsf F} \le
\frac{\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_{\mathsf F}}{2\sqrt{1 - \eta}}.$$
The constant is the Lipschitz constant of $\sqrt{\cdot}$ on $[1 - \eta, 1 + \eta]$.
[Higham2008, Theorem 8.4] for the nearest-orthonormal property of the polar factor. -/
theorem frobNorm_polarFactor_sub_le {n m : ℕ} {V : Matrix (Fin n) (Fin m) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) (hη : η < 1) :
    frobNorm (polarFactor V - V) ≤ frobNorm (Vᵀ * V - 1) / (2 * Real.sqrt (1 - η)) := by
  open scoped MatrixOrder in
  have hη0 : 0 ≤ η := le_trans (specNorm_nonneg _) hV
  have hs : 0 < 1 - η := by linarith
  have hspos : 0 < Real.sqrt (1 - η) := Real.sqrt_pos.2 hs
  have hGH : (Vᵀ * V).IsHermitian := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.isHermitian_conjTranspose_mul_self V
  have hGnn : 0 ≤ Vᵀ * V := by
    refine Matrix.nonneg_iff_posSemidef.mpr ?_
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact Matrix.posSemidef_conjTranspose_mul_self V
  have hI : (1 : Matrix (Fin m) (Fin m) ℝ).IsHermitian := Matrix.isHermitian_one
  have hU := hasOrthonormalCols_polarFactor hV hη
  have hsq : polarFactor V * CFC.sqrt (Vᵀ * V) = V := by
    have h := polarFactor_mul_sqrt V
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  have hdiff : polarFactor V - V = polarFactor V * (1 - CFC.sqrt (Vᵀ * V)) := by
    rw [Matrix.mul_sub, Matrix.mul_one, hsq]
  have hsqrt : CFC.sqrt (Vᵀ * V) = cfc Real.sqrt (Vᵀ * V) := by
    rw [CFC.sqrt_eq_real_sqrt _ hGnn, cfcₙ_eq_cfc]
  have hcfc1 : cfc Real.sqrt (1 : Matrix (Fin m) (Fin m) ℝ) = 1 := by
    simp
  have hspecG : spectrum ℝ (Vᵀ * V) ⊆ Set.Icc (1 - η) (1 + η) := by
    rw [hGH.spectrum_subset_iff]
    intro i hi
    have h1 := abs_le.mp ((hGH.abs_eigenvalue_sub_le hI i).trans hV)
    rw [eigenvalue_one hi] at h1
    exact Set.mem_Icc.2 ⟨by linarith [h1.1, h1.2], by linarith [h1.1, h1.2]⟩
  have hspecI : spectrum ℝ (1 : Matrix (Fin m) (Fin m) ℝ) ⊆ Set.Icc (1 - η) (1 + η) := by
    rw [hI.spectrum_subset_iff]
    intro i hi
    rw [eigenvalue_one hi]
    exact Set.mem_Icc.2 ⟨by linarith, by linarith⟩
  have hc : 0 ≤ 1 / (2 * Real.sqrt (1 - η)) := by positivity
  have hlip : LipschitzOnWith (Real.toNNReal (1 / (2 * Real.sqrt (1 - η)))) Real.sqrt
      (Set.Icc (1 - η) (1 + η)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [Real.coe_toNNReal _ hc, Real.dist_eq, Real.dist_eq]
    have ha : Real.sqrt (1 - η) ≤ Real.sqrt x := Real.sqrt_le_sqrt hx.1
    have hb : Real.sqrt (1 - η) ≤ Real.sqrt y := Real.sqrt_le_sqrt hy.1
    have hax : Real.sqrt x ^ 2 = x := Real.sq_sqrt (by linarith [hx.1])
    have hby : Real.sqrt y ^ 2 = y := Real.sq_sqrt (by linarith [hy.1])
    have e : x - y = (Real.sqrt x - Real.sqrt y) * (Real.sqrt x + Real.sqrt y) := by
      linear_combination hby - hax
    have h1 : 1 ≤ 1 / (2 * Real.sqrt (1 - η)) * (Real.sqrt x + Real.sqrt y) := by
      rw [one_div_mul_eq_div, le_div_iff₀ (by linarith)]
      linarith
    rw [e, abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.sqrt x + Real.sqrt y)]
    nlinarith [mul_le_mul_of_nonneg_left h1 (abs_nonneg (Real.sqrt x - Real.sqrt y))]
  have key := hGH.frobNorm_cfc_sub_cfc_le_of_lipschitzOnWith hI hspecG hspecI hlip
  rw [Real.coe_toNNReal _ hc, hcfc1] at key
  rw [hdiff, hU.frobNorm_mul_left, hsqrt, frobNorm_sub_comm 1 (cfc Real.sqrt (Vᵀ * V)),
    div_eq_mul_one_div]
  exact key.trans_eq (mul_comm _ _)

/-- Real form of `NLAlib.householder_mulVec`. -/
private theorem householder_mulVec_real {n : ℕ} (v u : Fin n → ℝ) :
    householder v *ᵥ u = u - (2 / ‖WithLp.toLp 2 v‖ ^ 2 * (v ⬝ᵥ u)) • v := by
  rw [householder_mulVec, star_trivial, smul_smul]
  rfl

/-- The squared norm of the difference of two reflectors applied to a vector. -/
private theorem norm_householder_sub_householder_add_mulVec_sq {n : ℕ} {x y : Fin n → ℝ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (hy : ‖WithLp.toLp 2 y‖ = 1) (hw : x + y ≠ 0) (v : Fin n → ℝ) :
    ‖WithLp.toLp 2 ((householder x - householder (x + y)) *ᵥ v)‖ ^ 2 * (1 + x ⬝ᵥ y) =
      2 * ((x ⬝ᵥ v) ^ 2 + (y ⬝ᵥ v) ^ 2 - 2 * (x ⬝ᵥ y) * (x ⬝ᵥ v) * (y ⬝ᵥ v)) := by
  have hxx : x ⬝ᵥ x = 1 := by rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hx, one_pow]
  have hyy : y ⬝ᵥ y = 1 := by rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hy, one_pow]
  have hww : ‖WithLp.toLp 2 (x + y)‖ ^ 2 = 2 * (1 + x ⬝ᵥ y) := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    simp only [dotProduct_add, add_dotProduct, hxx, hyy, dotProduct_comm y x]; ring
  have hc : 0 < 1 + x ⬝ᵥ y := by
    have : ‖WithLp.toLp 2 (x + y)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hw)
    have : 0 < ‖WithLp.toLp 2 (x + y)‖ ^ 2 := by positivity
    linarith
  rw [Matrix.sub_mulVec, householder_mulVec_real, householder_mulVec_real, hx, hww,
    EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  simp only [dotProduct_add, add_dotProduct, dotProduct_sub, sub_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul, hxx, hyy, dotProduct_comm y x, dotProduct_comm v x,
    dotProduct_comm v y]
  field_simp
  ring

/-- A rotation taking one unit vector to another: for unit vectors $\mathbf{x}$, $\mathbf{y}$ the
orthogonal $\mathbf{Z} = \mathbf{H}_{\mathbf{x}+\mathbf{y}}\mathbf{H}_{\mathbf{x}}$ (two
reflectors, `NLAlib.householder`; the identity on $\{\mathbf{x}, \mathbf{y}\}^\perp$) satisfies
$\mathbf{Z}\mathbf{x} = \mathbf{y}$, $\|\mathbf{Z} - \mathbf{I}\|_2 \le \|\mathbf{x} -
\mathbf{y}\|$ and $\|\mathbf{Z} - \mathbf{I}\|_{\mathsf F} \le \sqrt2\|\mathbf{x} - \mathbf{y}\|$
(a single reflector has $\|\mathbf{H} - \mathbf{I}\|_2 = 2$). -/
theorem exists_orthogonal_mulVec_eq_specNorm_sub_one_le {n : ℕ} {x y : Fin n → ℝ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (hy : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Zᵀ * Z = 1 ∧ Z *ᵥ x = y ∧
      specNorm (Z - 1) ≤ ‖WithLp.toLp 2 (x - y)‖ ∧
      frobNorm (Z - 1) ≤ Real.sqrt 2 * ‖WithLp.toLp 2 (x - y)‖ := by
  have hxx : x ⬝ᵥ x = 1 := by rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hx, one_pow]
  have hyy : y ⬝ᵥ y = 1 := by rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hy, one_pow]
  have hH (v : Fin n → ℝ) : (householder v)ᵀ = householder v := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial, (isHermitian_householder v).eq]
  by_cases hw : x + y = 0
  · obtain rfl : y = -x := (neg_eq_of_add_eq_zero_right hw).symm
    have hD : householder x - 1 = -((2 : ℝ) • Matrix.vecMulVec x x) := by
      rw [householder, hx, star_trivial]; simp
    have h2 : ‖WithLp.toLp 2 (x - -x)‖ = 2 := by
      rw [sub_neg_eq_add, ← two_smul ℝ x, WithLp.toLp_smul, norm_smul, hx]; norm_num
    refine ⟨householder x, by rw [hH, householder_mul_self], householder_mulVec_self x, ?_, ?_⟩
    · rw [hD, specNorm_neg, specNorm_smul, specNorm_vecMulVec, hx, h2]; norm_num
    · rw [hD, frobNorm_neg, frobNorm_smul, frobNorm_vecMulVec, hx, h2]
      norm_num
  have hc : 0 < 1 + x ⬝ᵥ y := by
    have : ‖WithLp.toLp 2 (x + y)‖ ≠ 0 :=
      norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hw)
    have h : 0 < ‖WithLp.toLp 2 (x + y)‖ ^ 2 := by positivity
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at h
    simp only [dotProduct_add, add_dotProduct, hxx, hyy, dotProduct_comm y x] at h
    linarith
  have hxy : ‖WithLp.toLp 2 (x - y)‖ ^ 2 = 2 - 2 * (x ⬝ᵥ y) := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    simp only [dotProduct_sub, sub_dotProduct, hxx, hyy, dotProduct_comm y x]; ring
  have hZ : householder (x + y) * householder x - 1 =
      householder (x + y) * (householder x - householder (x + y)) := by
    rw [Matrix.mul_sub, householder_mul_self]
  have key := norm_householder_sub_householder_add_mulVec_sq hx hy hw
  refine ⟨householder (x + y) * householder x, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_mul, hH, hH, Matrix.mul_assoc, ← Matrix.mul_assoc (householder (x + y)),
      householder_mul_self, Matrix.one_mul, householder_mul_self]
  · rw [← Matrix.mulVec_mulVec, householder_mulVec_self, householder_mulVec_real]
    have hs : 2 / ‖WithLp.toLp 2 (x + y)‖ ^ 2 * ((x + y) ⬝ᵥ -x) = -1 := by
      rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
      simp only [dotProduct_add, add_dotProduct, dotProduct_neg, hxx, hyy, dotProduct_comm y x]
      rw [div_mul_eq_mul_div, div_eq_iff (by linarith)]
      ring
    rw [hs]; module
  · rw [hZ, (hasOrthonormalCols_householder _).specNorm_mul_left]
    refine (specNorm_le_iff (norm_nonneg _)).2 fun v => ?_
    have cs := pow_le_pow_left₀ (abs_nonneg _)
      (EuclideanSpace.abs_dotProduct_le_norm (y - (x ⬝ᵥ y) • x) (v - (x ⬝ᵥ v) • x)) 2
    rw [sq_abs, mul_pow, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at cs
    simp only [dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
      hxx, hyy, dotProduct_comm y x, dotProduct_comm v x] at cs
    have := key v
    refine (sq_le_sq₀ (norm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, hxy, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self v]
    refine le_of_mul_le_mul_right ?_ hc
    nlinarith
  · rw [hZ, (hasOrthonormalCols_householder _).frobNorm_mul_left]
    refine (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 ?_
    rw [mul_pow, hxy, Real.sq_sqrt zero_le_two, frobNorm_sq_eq_sum_col]
    refine le_of_mul_le_mul_right ?_ hc
    simp only [Finset.sum_mul, ← Matrix.mulVec_single_one, key, dotProduct_single_one]
    have hs (c : ℝ) : ∑ j, 2 * (x j ^ 2 + y j ^ 2 - 2 * c * x j * y j) =
        2 * (x ⬝ᵥ x) + 2 * (y ⬝ᵥ y) - 4 * c * (x ⬝ᵥ y) := by
      simp only [dotProduct, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [hs, hxx, hyy]
    nlinarith

/-- Rows of unit length whose columns have squared norms at most one, each with mass less than
$1/r$ outside `S`, force $r \le \lvert S\rvert$. -/
private theorem le_card_of_sum_sq_compl_lt {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ}
    (hr : 0 < r) (z : Fin r → ι → ℝ) (S : Finset ι) (hnorm : ∀ i, ∑ j, z i j ^ 2 = 1)
    (hcol : ∀ j, ∑ i, z i j ^ 2 ≤ 1) (hout : ∀ i, ∑ j ∈ Sᶜ, z i j ^ 2 < 1 / r) :
    r ≤ S.card := by
  have hin (i : Fin r) : 1 - 1 / r < ∑ j ∈ S, z i j ^ 2 := by
    have h := hnorm i
    rw [← Finset.sum_add_sum_compl S] at h
    linarith [hout i]
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have hlt : (r : ℝ) - 1 < S.card :=
    calc (r : ℝ) - 1 = ∑ _i : Fin r, (1 - 1 / (r : ℝ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ < ∑ i, ∑ j ∈ S, z i j ^ 2 :=
          Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun i _ => hin i
      _ = ∑ j ∈ S, ∑ i, z i j ^ 2 := Finset.sum_comm
      _ ≤ ∑ _j ∈ S, (1 : ℝ) := Finset.sum_le_sum fun j _ => hcol j
      _ = S.card := by rw [Finset.sum_const, nsmul_one]
  have : r < S.card + 1 := by exact_mod_cast (by linarith : (r : ℝ) < S.card + 1)
  omega

/-- Orthonormal approximate eigenvectors are counted by the spectrum: for symmetric
$\mathbf{M}$, $r$ orthonormal vectors $\mathbf{x}_i$ and values $\theta_i \in [a, b]$ with
residuals $\|\mathbf{M}\mathbf{x}_i - \theta_i\mathbf{x}_i\| < d/\sqrt r$, $d > 0$, the number of
eigenvalues of $\mathbf{M}$ in $(a - d, b + d)$ is at least $r$: the finite-dimensional core of
"converged Ritz values are not duplicated". `docs/design/Krylov-LanczosReorth.md` §3.3. -/
theorem _root_.Matrix.IsHermitian.card_le_card_eigenvalue_mem_of_hasOrthonormalCols {n r : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) {X : Matrix (Fin n) (Fin r) ℝ}
    (hX : HasOrthonormalCols X) {θ : Fin r → ℝ} {a b d : ℝ} (hd : 0 < d)
    (hθ : ∀ i, θ i ∈ Set.Icc a b)
    (hres : ∀ i, ‖WithLp.toLp 2 (M *ᵥ (fun k => X k i) - θ i • fun k => X k i)‖ <
      d / Real.sqrt r) :
    r ≤ ((Finset.range n).filter fun i => eigenvalue M i ∈ Set.Ioo (a - d) (b + d)).card := by
  classical
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact Nat.zero_le _
  obtain ⟨U, hU, hMU⟩ := hM.exists_eq_mul_diagonal_mul_conjTranspose
  have hU' : HasOrthonormalCols Uᴴ := hU.conjTranspose_of_card_eq (Fintype.card_fin _).symm
  -- the coordinates of the `i`-th vector in the eigenbasis
  set z : Fin r → Fin (Fintype.card (Fin n)) → ℝ := fun i => Uᴴ *ᵥ fun k => X k i with hz
  have hnorm (i : Fin r) : ∑ j, z i j ^ 2 = 1 := by
    rw [← EuclideanSpace.norm_toLp_sq_eq_sum_sq, hU'.norm_toLp_mulVec]
    rw [show (fun k => X k i) = X.col i from rfl, hX.norm_toLp_col, one_pow]
  have hres2 (i : Fin r) :
      ∑ j : Fin (Fintype.card (Fin n)), (eigenvalue M j - θ i) ^ 2 * z i j ^ 2 =
      ‖WithLp.toLp 2 (M *ᵥ (fun k => X k i) - θ i • fun k => X k i)‖ ^ 2 := by
    rw [← hU'.norm_toLp_mulVec, EuclideanSpace.norm_toLp_sq_eq_sum_sq]
    have h2 : Uᴴ *ᵥ (M *ᵥ fun k => X k i) =
        (Matrix.diagonal fun j : Fin (Fintype.card (Fin n)) => eigenvalue M ↑j) *ᵥ z i := by
      conv_lhs => rw [hMU]
      rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        hU.conjTranspose_mul_self, Matrix.one_mul]
      rfl
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h2, Pi.sub_apply, Matrix.mulVec_diagonal,
      Pi.smul_apply, smul_eq_mul]
    ring
  have hbessel (j : Fin (Fintype.card (Fin n))) : ∑ i, z i j ^ 2 ≤ 1 := by
    have h := hX.norm_toLp_conjTranspose_mulVec_le (U.col j)
    rw [hU.norm_toLp_col] at h
    have h2 : ∑ i, z i j ^ 2 = ‖WithLp.toLp 2 (Xᴴ *ᵥ U.col j)‖ ^ 2 := by
      rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hz, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, star_trivial,
        Matrix.col_apply, mul_comm]
    rw [h2]
    exact pow_le_one₀ (norm_nonneg _) h
  set S := Finset.univ.filter fun j : Fin (Fintype.card (Fin n)) =>
    eigenvalue M j ∈ Set.Ioo (a - d) (b + d) with hS
  have hr' : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  have hout (i : Fin r) : ∑ j ∈ Sᶜ, z i j ^ 2 < 1 / r := by
    have hlt :
        ‖WithLp.toLp 2 (M *ᵥ (fun k => X k i) - θ i • fun k => X k i)‖ ^ 2 < d ^ 2 / r := by
      rw [← Real.sq_sqrt hr'.le, ← div_pow]
      exact pow_lt_pow_left₀ (hres i) (norm_nonneg _) two_ne_zero
    have hout : d ^ 2 * ∑ j ∈ Sᶜ, z i j ^ 2 ≤
        ∑ j : Fin (Fintype.card (Fin n)), (eigenvalue M j - θ i) ^ 2 * z i j ^ 2 := by
      rw [Finset.mul_sum]
      refine (Finset.sum_le_sum fun j hj => ?_).trans
        (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ => by positivity)
      simp only [hS, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ, true_and,
        Set.mem_Ioo, not_and_or, not_lt] at hj
      obtain ⟨h1, h2⟩ := hθ i
      refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
      rcases hj with hj | hj <;> nlinarith
    rw [lt_div_iff₀ hr']
    nlinarith [hres2 i, mul_div_cancel₀ (d ^ 2) hr'.ne']
  refine (le_card_of_sum_sq_compl_lt hr z S hnorm hbessel hout).trans_eq ?_
  rw [hS, Finset.card_filter, Finset.card_filter,
    Fin.sum_univ_eq_sum_range
      (fun k => if eigenvalue M k ∈ Set.Ioo (a - d) (b + d) then 1 else 0),
    Fintype.card_fin]

end NLAlib
