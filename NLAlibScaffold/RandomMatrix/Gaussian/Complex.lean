/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.Matrix.Perturbation.Pseudospectrum

/-!
# Sharper tails for complex Gaussian matrices (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/RandomMatrix/Gaussian/Complex.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I5 and I6): the upper tail
of $\lvert z \rvert^2$, a norm tail with the full Gaussian exponent, and a smallest singular value
tail linear in the size, within a factor $e$ of Edelman's exact law [Edelman1988].

## Main results

* `NLAlib.measureReal_le_normSq_le_of_hasLaw_complexGaussian` (CG7): $\mathbb{P}[s \le
  \lvert z\rvert^2] \le e^{-s}$.
* `NLAlib.measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix` (CG4'): tail
  $e^{-t^2}$ above $\sqrt2(\sqrt m + \sqrt n)$.
* `NLAlib.measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix` (CG6'):
  $\mathbb{P}[\sigma_{\min}(\mathbf{G}) \le x] \le e\,r x^2$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n]

private lemma gaussianPDFReal_two_inv (x : ℝ) :
    gaussianPDFReal 0 2⁻¹ x = (√Real.pi)⁻¹ * Real.exp (-x ^ 2) := by
  rw [gaussianPDFReal_def]
  simp only [NNReal.coe_inv, NNReal.coe_ofNat, sub_zero]
  congr 2
  · ring_nf
  · ring

/-- The radial one-dimensional integral of the exponential tail: $\int_0^\infty r\,
\mathbf 1_{\{s \le r^2\}} e^{-r^2}\,dr = e^{-s}/2$ for $s \ge 0$. -/
private lemma integral_Ioi_radial_tail {s : ℝ} (hs : 0 ≤ s) :
    ∫ x in Set.Ioi (0 : ℝ), x * (if s ≤ x ^ 2 then Real.exp (-x ^ 2) else 0) =
      Real.exp (-s) / 2 := by
  have ha : 0 ≤ √s := Real.sqrt_nonneg s
  have hsa : (√s) ^ 2 = s := Real.sq_sqrt hs
  have key : ∀ x : ℝ, 0 < x → (s ≤ x ^ 2 ↔ √s ≤ x) := fun x hx => by
    constructor
    · intro h
      calc √s ≤ √(x ^ 2) := Real.sqrt_le_sqrt h
        _ = x := Real.sqrt_sq hx.le
    · intro h
      nlinarith [Real.sqrt_nonneg s]
  have hcongr : ∫ x in Set.Ioi (0 : ℝ), x * (if s ≤ x ^ 2 then Real.exp (-x ^ 2) else 0) =
      ∫ x in Set.Ioi (0 : ℝ), (Set.Ici (√s)).indicator (fun x => x * Real.exp (-x ^ 2)) x := by
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have hx' : (0 : ℝ) < x := hx
    simp only [Set.indicator_apply, Set.mem_Ici, key x hx']
    split_ifs <;> simp
  rw [hcongr, setIntegral_indicator measurableSet_Ici]
  have hf : ∀ x ∈ Set.Ioi (√s), HasDerivAt (fun x : ℝ => -Real.exp (-x ^ 2) / 2)
      (x * Real.exp (-x ^ 2)) x := by
    intro x _
    have h1 : HasDerivAt (fun y : ℝ => -y ^ 2) (-(2 * x)) x := by
      exact ((hasDerivAt_pow 2 x).neg).congr_deriv (by norm_num)
    exact ((h1.exp.neg).div_const 2).congr_deriv (by ring)
  have hlim : Filter.Tendsto (fun x : ℝ => -Real.exp (-x ^ 2) / 2) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => -x ^ 2) Filter.atTop Filter.atBot :=
      Filter.tendsto_neg_atTop_atBot.comp (Filter.tendsto_pow_atTop two_ne_zero)
    have h2 := ((Real.tendsto_exp_atBot.comp h1).neg).div_const 2
    simpa using h2
  have hI : Integrable (fun x : ℝ => x * Real.exp (-x ^ 2)) := by
    simpa using integrable_mul_exp_neg_mul_sq one_pos
  have hc : ContinuousWithinAt (fun x : ℝ => -Real.exp (-x ^ 2) / 2) (Set.Ici (√s)) (√s) :=
    Continuous.continuousWithinAt (by fun_prop)
  rcases ha.eq_or_lt with h0 | h0
  · rw [← h0] at hf hsa hc ⊢
    rw [Set.inter_eq_left.2 Set.Ioi_subset_Ici_self,
      integral_Ioi_of_hasDerivAt_of_tendsto hc hf hI.integrableOn hlim]
    norm_num at hsa
    rw [← hsa]
    norm_num
  · rw [Set.inter_eq_right.2 (Set.Ici_subset_Ioi.2 h0), integral_Ici_eq_integral_Ioi,
      integral_Ioi_of_hasDerivAt_of_tendsto hc hf hI.integrableOn hlim, hsa]
    ring

/-- The exponential tail in polar coordinates: $\int_{\{s \le \lvert p\rvert^2\}} \pi^{-1}
e^{-\lvert p\rvert^2}\,dp = e^{-s}$ for $s \ge 0$. -/
private lemma integral_tail_polar {s : ℝ} (hs : 0 ≤ s) :
    ∫ p in {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2},
      (Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) = Real.exp (-s) := by
  have hT : MeasurableSet {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  rw [← integral_indicator hT, ← integral_comp_polarCoord_symm]
  have hpt : ∀ q : ℝ × ℝ,
      q.1 • ({p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2}.indicator
        (fun p : ℝ × ℝ => (Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2))))
        (polarCoord.symm q) =
      (Real.pi)⁻¹ * (q.1 * (if s ≤ q.1 ^ 2 then Real.exp (-q.1 ^ 2) else 0)) * 1 := by
    intro q
    have hr : (q.1 * Real.cos q.2) ^ 2 + (q.1 * Real.sin q.2) ^ 2 = q.1 ^ 2 := by
      linear_combination (q.1 ^ 2) * Real.sin_sq_add_cos_sq q.2
    rw [polarCoord_symm_apply]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, hr, smul_eq_mul]
    split_ifs <;> ring
  simp only [hpt]
  rw [Measure.volume_eq_prod, polarCoord_target,
    setIntegral_prod_mul (fun x : ℝ => (Real.pi)⁻¹ * (x * if s ≤ x ^ 2 then
      Real.exp (-x ^ 2) else 0)) (fun _ : ℝ => (1 : ℝ))]
  have hvol : (volume : Measure ℝ).real (Set.Ioo (-Real.pi) Real.pi) = 2 * Real.pi := by
    rw [Measure.real_def, Real.volume_Ioo, ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [integral_const_mul, integral_Ioi_radial_tail hs, setIntegral_const, hvol, smul_eq_mul,
    mul_one]
  field_simp

/-- The tail of a standard complex Gaussian, as a Lebesgue integral over `ℝ × ℝ` of its density
in the real and imaginary parts. -/
private lemma complexGaussian_real_eq_integral (s : ℝ) :
    complexGaussian.real {w | s ≤ ‖w‖ ^ 2} =
      ∫ p in {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2},
        (Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2)) := by
  have hν : gaussianReal 0 2⁻¹ = volume.withDensity (gaussianPDF 0 2⁻¹) :=
    gaussianReal_of_var_ne_zero _ (by norm_num)
  have hT : MeasurableSet {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  have hpre : Complex.measurableEquivRealProd.symm ⁻¹' {w : ℂ | s ≤ ‖w‖ ^ 2} =
      {p : ℝ × ℝ | s ≤ p.1 ^ 2 + p.2 ^ 2} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Complex.sq_norm, Complex.normSq_mk,
      Complex.measurableEquivRealProd_symm_apply]
    ring_nf
  have hpt : ∀ p : ℝ × ℝ, gaussianPDF 0 2⁻¹ p.1 * gaussianPDF 0 2⁻¹ p.2 =
      ENNReal.ofReal ((Real.pi)⁻¹ * Real.exp (-(p.1 ^ 2 + p.2 ^ 2))) := by
    intro p
    have h0 : 0 ≤ (√Real.pi)⁻¹ * Real.exp (-p.1 ^ 2) := by positivity
    have h1 : 0 ≤ (√Real.pi)⁻¹ * Real.exp (-p.2 ^ 2) := by positivity
    simp only [gaussianPDF_def, gaussianPDFReal_two_inv]
    rw [← ENNReal.ofReal_mul h0]
    congr 1
    have hs : (√Real.pi)⁻¹ * (√Real.pi)⁻¹ = (Real.pi)⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt Real.pi_pos.le]
    rw [show (√Real.pi)⁻¹ * Real.exp (-p.1 ^ 2) * ((√Real.pi)⁻¹ * Real.exp (-p.2 ^ 2)) =
      ((√Real.pi)⁻¹ * (√Real.pi)⁻¹) * (Real.exp (-p.1 ^ 2) * Real.exp (-p.2 ^ 2)) by ring,
      hs, ← Real.exp_add]
    ring_nf
  rw [complexGaussian, map_measureReal_apply Complex.measurableEquivRealProd.symm.measurable
    (measurableSet_le measurable_const (by fun_prop)), hpre, Measure.real, hν,
    MeasureTheory.prod_withDensity (by fun_prop) (by fun_prop), withDensity_apply _ hT,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun p => by positivity)
      (by fun_prop)]
  congr 2
  funext p
  exact hpt p
/-- **Exponential upper tail of a standard complex Gaussian** (CG7): for $z \sim
\mathcal{N}_{\mathbb C}(0, 1)$ and every real $s$, $\mathbb{P}[s \le \lvert z \rvert^2] \le
e^{-s}$ ($\lvert z\rvert^2$ is exponential of mean $1$).
Proof: by `NLAlib.complexGaussian_eq_map_stdGaussian`, $2\lvert z \rvert^2$ is
$\chi^2_2$ (`NLAlib.hasLaw_norm_sq_of_hasLaw_gaussianVector` on the realification, or a direct
computation of the product of two `gaussianReal 0 2⁻¹`); the $\chi^2_2$ upper tail is
$e^{-x/2}$ in closed form; for $s < 0$ the bound is at least $1$. M, about 50 lines. -/
theorem measureReal_le_normSq_le_of_hasLaw_complexGaussian {z : Ω → ℂ}
    (hz : HasLaw z complexGaussian μ) (s : ℝ) :
    μ.real {ω | s ≤ ‖z ω‖ ^ 2} ≤ Real.exp (-s) := by
  have : IsProbabilityMeasure μ := hz.isProbabilityMeasure_iff.2 inferInstance
  rcases lt_or_ge s 0 with hs | hs
  · exact (measureReal_le_one).trans (Real.one_le_exp (by linarith))
  · rw [hz.measureReal_eq (p := fun w : ℂ => s ≤ ‖w‖ ^ 2)
      (measurableSet_le measurable_const (measurable_norm.pow_const 2)),
      complexGaussian_real_eq_integral, integral_tail_polar hs]

/-- The squared Euclidean norm of a complex vector is the sum of those of its real and
imaginary parts. -/
private theorem norm_toLp_sq_eq_re_add_im' (v : n → ℂ) : ‖WithLp.toLp 2 v‖ ^ 2 =
    ‖WithLp.toLp 2 fun j => (v j).re‖ ^ 2 + ‖WithLp.toLp 2 fun j => (v j).im‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
    EuclideanSpace.norm_toLp_sq_eq_sum_sq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The complexification of a real matrix has spectral norm at most that of the matrix. -/
private theorem specNorm_map_ofReal_le' (A : Matrix m n ℝ) :
    specNorm (A.map fun x : ℝ => (x : ℂ)) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  have hv : ∀ i, ((A.map fun r : ℝ => (r : ℂ)) *ᵥ x) i =
      ((A *ᵥ fun j => (x j).re) i : ℂ) + ((A *ᵥ fun j => (x j).im) i : ℂ) * Complex.I := by
    intro i
    apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum]
  have hre := norm_toLp_mulVec_le A fun j => (x j).re
  have him := norm_toLp_mulVec_le A fun j => (x j).im
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_toLp_sq_eq_re_add_im',
    norm_toLp_sq_eq_re_add_im' x]
  simp only [hv, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, add_zero,
    mul_one, zero_add]
  rw [mul_add]
  gcongr
  · exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hre |>.trans_eq (mul_pow _ _ _)
  · exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 him |>.trans_eq (mul_pow _ _ _)

/-- The complex matrix $\mathbf{X}_1 + i\mathbf{X}_2$ built from the two halves of a real
$2m \times n$ matrix $\mathbf{X}$ has the Frobenius norm of $\mathbf{X}$. -/
private theorem frobNorm_map_ofReal_add_I_smul (X : Matrix (m ⊕ m) n ℝ) :
    frobNorm ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
      Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) = frobNorm X := by
  rw [← sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _), frobNorm_sq_eq_sum,
    frobNorm_sq_eq_sum_sq, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- **Norm tail of a complex Gaussian matrix with the full exponent** (CG4'): for
$\mathbf{G}$ an $m \times n$ standard complex Gaussian matrix and $t \ge 0$,
$\mathbb{P}[\sqrt2(\sqrt m + \sqrt n) + t \le \|\mathbf{G}\|_2] \le e^{-t^2}$. Compared with
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`, the deviation $t$ is not
multiplied by $\sqrt2$ and there is no union bound over the two parts. The sharp mean
$\sqrt m + \sqrt n$ is not claimed (design note, item I6).
Proof: by `NLAlib.complexGaussianMatrix_eq_map_gaussianMatrix`, $\mathbf{G} = (\mathbf{G}_1 +
i\mathbf{G}_2)/\sqrt2$ with $(\mathbf{G}_1; \mathbf{G}_2)$ a real $2m \times n$ Gaussian matrix;
$X \mapsto \|(X_1 + iX_2)/\sqrt2\|_2$ is $2^{-1/2}$-Lipschitz for the Frobenius norm, so
`NLAlib.measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix` gives the tail $e^{-t^2}$ above the
mean; the mean is at most $\sqrt2(\sqrt m + \sqrt n)$ by the triangle inequality and
`NLAlib.integral_specNorm_le_of_hasLaw_gaussianMatrix` on each part. M, about 80 lines. -/
theorem measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) + t ≤ specNorm (G ω)} ≤
      Real.exp (-t ^ 2) := by
  set φ : Matrix (m ⊕ m) n ℝ → Matrix m n ℂ := fun X => (√2 : ℝ)⁻¹ •
      ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) with hφ
  have hf : Measurable φ := Continuous.measurable (by fun_prop)
  have hS : MeasurableSet {A : Matrix m n ℂ |
      √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) + t ≤ specNorm A} :=
    measurableSet_le measurable_const continuous_specNorm.measurable
  rw [hG.measureReal_eq hS, complexGaussianMatrix_eq_map_gaussianMatrix,
    map_measureReal_apply hf hS]
  have hX := HasLaw.id (μ := gaussianMatrix (m ⊕ m) n)
  have hlip : ∀ A B, |specNorm (φ A) - specNorm (φ B)| ≤
      ((‖(√2 : ℝ)⁻¹‖₊ : ℝ)) * frobNorm (A - B) := by
    intro A B
    have hsub : φ A - φ B = φ (A - B) := by
      ext i j
      simp only [hφ, Matrix.sub_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.map_apply,
        Matrix.submatrix_apply, id, Complex.ofReal_sub, Complex.real_smul, smul_eq_mul]
      ring
    refine (abs_specNorm_sub_specNorm_le _ _).trans ?_
    rw [hsub, hφ, specNorm_real_smul, coe_nnnorm, Real.norm_eq_abs]
    gcongr
    exact (specNorm_le_frobNorm _).trans (frobNorm_map_ofReal_add_I_smul _).le
  have hmean : ∫ X, specNorm (φ X) ∂(gaussianMatrix (m ⊕ m) n) ≤
      √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) := by
    have h₁ : HasLaw (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix Sum.inl id) _ _ :=
      hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inl_injective Function.injective_id
    have h₂ : HasLaw (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix Sum.inr id) _ _ :=
      hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inr_injective Function.injective_id
    have hle : ∀ X : Matrix (m ⊕ m) n ℝ, specNorm (φ X) ≤
        (√2)⁻¹ * (specNorm (X.submatrix Sum.inl id) + specNorm (X.submatrix Sum.inr id)) := by
      intro X
      rw [hφ, specNorm_real_smul, abs_of_pos (by positivity)]
      gcongr
      refine (specNorm_add_le _ _).trans (add_le_add (specNorm_map_ofReal_le' _) ?_)
      rw [specNorm_smul, Complex.norm_I, one_mul]
      exact specNorm_map_ofReal_le' _
    calc ∫ X, specNorm (φ X) ∂(gaussianMatrix (m ⊕ m) n)
        ≤ ∫ X, (√2)⁻¹ * (specNorm (X.submatrix Sum.inl id) +
            specNorm (X.submatrix Sum.inr id)) ∂(gaussianMatrix (m ⊕ m) n) :=
          integral_mono (integrable_comp_of_hasLaw_gaussianMatrix hX hlip)
            (((integrable_specNorm_of_hasLaw_gaussianMatrix h₁).add
              (integrable_specNorm_of_hasLaw_gaussianMatrix h₂)).const_mul _) hle
      _ ≤ (√2)⁻¹ * (2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ))) := by
          rw [integral_const_mul, integral_add (integrable_specNorm_of_hasLaw_gaussianMatrix h₁)
            (integrable_specNorm_of_hasLaw_gaussianMatrix h₂)]
          gcongr
          linarith [integral_specNorm_le_of_hasLaw_gaussianMatrix h₁,
            integral_specNorm_le_of_hasLaw_gaussianMatrix h₂]
      _ = √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) := by
          field_simp; rw [Real.sq_sqrt zero_le_two]
  have h := measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix hX hlip ht
  rw [coe_nnnorm, Real.norm_of_nonneg (by positivity), inv_pow, Real.sq_sqrt zero_le_two,
    mul_inv_cancel₀ two_ne_zero, div_one] at h
  refine (measureReal_mono fun X hX => ?_).trans h
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, id] at hX ⊢
  linarith

/-- The realification $z \mapsto (\sqrt2\,\Re z, \sqrt2\,\Im z)$ maps a standard complex Gaussian
to a standard Gaussian vector of dimension $2$. -/
private theorem measurePreserving_complexGaussian_finTwo :
    MeasurePreserving (fun z : ℂ => (MeasurableEquiv.finTwoArrow.symm (√2 * z.re, √2 * z.im)))
      complexGaussian (Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  have h1 : MeasurePreserving (fun x : ℝ => √2 * x) (gaussianReal 0 2⁻¹) (gaussianReal 0 1) := by
    refine ⟨measurable_const_mul _, ?_⟩
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
    ext
    simp
  have h2 : MeasurePreserving Complex.measurableEquivRealProd complexGaussian
      ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)) :=
    (MeasurePreserving.symm Complex.measurableEquivRealProd.symm
      ⟨Complex.measurableEquivRealProd.symm.measurable, rfl⟩)
  exact ((measurePreserving_finTwoArrow (gaussianReal 0 1)).symm.comp (h1.prod h1)).comp h2

private theorem sum_sq_finTwo_eq (z : ℂ) :
    ∑ i, (MeasurableEquiv.finTwoArrow.symm (√2 * z.re, √2 * z.im) : Fin 2 → ℝ) i ^ 2 =
      2 * ‖z‖ ^ 2 := by
  simp only [Fin.sum_univ_two, MeasurableEquiv.finTwoArrow_symm_apply, Fin.cons_zero,
    Fin.cons_one, mul_pow, Real.sq_sqrt zero_le_two, Complex.sq_norm, Complex.normSq_apply]
  ring

/-- $\mathbb{P}[1 \le \lvert z\rvert^2] \ge e^{-1}$ for a standard complex Gaussian $z$:
$2\lvert z \rvert^2$ is exponential of rate $1/2$. -/
private theorem exp_neg_one_le_complexGaussian_real :
    Real.exp (-1) ≤ complexGaussian.real {z | 1 ≤ ‖z‖ ^ 2} := by
  have hY := hasLaw_sum_sq_of_hasLaw_pi_gaussianReal measurePreserving_complexGaussian_finTwo.hasLaw
  rw [Fintype.card_fin, show ((2 : ℕ) : ℝ) / 2 = 1 by norm_num] at hY
  have hI : ∫ x in Set.Ioi (2 : ℝ), (1 / 2) * Real.exp ((-1 / 2) * x) = Real.exp (-1) := by
    rw [integral_const_mul, integral_exp_mul_Ioi (by norm_num)]
    norm_num
    ring
  have htail : (gammaMeasure 1 (1 / 2)).real (Set.Ioi 2) = Real.exp (-1) := by
    rw [measureReal_def, gammaMeasure, withDensity_apply _ measurableSet_Ioi,
      setLIntegral_congr_fun measurableSet_Ioi (g := fun x => ENNReal.ofReal
        ((1 / 2) * Real.exp ((-1 / 2) * x))) (fun x hx => by
          rw [gammaPDF_of_nonneg (le_of_lt (lt_trans two_pos hx))]
          congr 1
          simp only [Real.rpow_one, Real.Gamma_one, sub_self, Real.rpow_zero]
          ring_nf),
      ← ofReal_integral_eq_lintegral_ofReal, hI, ENNReal.toReal_ofReal (Real.exp_pos _).le]
    · exact (integrableOn_exp_mul_Ioi (by norm_num) _).const_mul _
    · exact Filter.Eventually.of_forall fun x => by positivity
  calc Real.exp (-1) = (gammaMeasure 1 (1 / 2)).real {y | 2 < y} := htail.symm
    _ = _ := (hY.measureReal_eq measurableSet_Ioi).symm
    _ ≤ _ := measureReal_mono fun z hz => by
      simp only [Set.mem_ofPred_eq, sum_sq_finTwo_eq] at hz ⊢
      linarith

/-- $\mathbb{E}\lvert z\rvert^2 = 1$ for a standard complex Gaussian $z$. -/
private theorem lintegral_ofReal_norm_sq_complexGaussian :
    ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂complexGaussian = 1 := by
  have h1 : ∫ x, x ^ 2 ∂(gaussianReal 0 1) = 1 := by
    have h := variance_fun_id_gaussianReal (μ := 0) (v := 1)
    rw [variance_of_integral_eq_zero (by fun_prop) (by simp [integral_id_gaussianReal])] at h
    simpa using h
  have hint : Integrable (fun x : ℝ => x ^ 2) (gaussianReal 0 1) :=
    (memLp_id_gaussianReal 2).integrable_sq
  have heval : ∀ i : Fin 2, ∫⁻ y : Fin 2 → ℝ, ENNReal.ofReal (y i ^ 2)
      ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) = 1 := fun i => by
    rw [(measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) i).lintegral_comp
      (f := fun x => ENNReal.ofReal (x ^ 2)) (by fun_prop),
      ← ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall fun x => by positivity), h1, ENNReal.ofReal_one]
  calc ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂complexGaussian
      = ∫⁻ z, ENNReal.ofReal (2⁻¹) * ∑ i, ENNReal.ofReal
          ((MeasurableEquiv.finTwoArrow.symm (√2 * z.re, √2 * z.im) : Fin 2 → ℝ) i ^ 2)
          ∂complexGaussian := by
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun i _ => sq_nonneg _, ← ENNReal.ofReal_mul
          (by norm_num), sum_sq_finTwo_eq]
        congr 1
        ring
    _ = ENNReal.ofReal (2⁻¹) * ∑ i : Fin 2, ∫⁻ y : Fin 2 → ℝ, ENNReal.ofReal (y i ^ 2)
          ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
        rw [lintegral_const_mul _ (by fun_prop), lintegral_finsetSum _ fun i _ => by fun_prop]
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        exact measurePreserving_complexGaussian_finTwo.lintegral_comp
          (f := fun y : Fin 2 → ℝ => ENNReal.ofReal (y i ^ 2)) (by fun_prop)
    _ = 1 := by
      simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by norm_num)]
      norm_num

/-- $\mathbb{E}\|\mathbf{g}\|^2 = \lvert r \rvert$ for a standard complex Gaussian vector. -/
private theorem lintegral_ofReal_norm_sq_complexGaussianVector (r : Type*) [Fintype r] :
    ∫⁻ v, ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) ∂complexGaussianVector r =
      (Fintype.card r : ENNReal) := by
  calc ∫⁻ v, ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) ∂complexGaussianVector r
      = ∫⁻ v, ∑ i, ENNReal.ofReal (‖v i‖ ^ 2) ∂complexGaussianVector r := by
        refine lintegral_congr fun v => ?_
        rw [EuclideanSpace.norm_sq_eq, ENNReal.ofReal_sum_of_nonneg fun i _ => by positivity]
    _ = ∑ i : r, ∫⁻ z, ENNReal.ofReal (‖z‖ ^ 2) ∂complexGaussian := by
        rw [lintegral_finsetSum _ fun i _ => by fun_prop]
        refine Finset.sum_congr rfl fun i _ => ?_
        exact (measurePreserving_eval (fun _ : r => complexGaussian) i).lintegral_comp
          (f := fun z => ENNReal.ofReal (‖z‖ ^ 2)) (by fun_prop)
    _ = _ := by
        rw [lintegral_ofReal_norm_sq_complexGaussian, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, mul_one]

/-- The transpose of a standard complex Gaussian matrix is standard complex Gaussian. -/
private theorem hasLaw_transpose_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) :
    HasLaw (fun ω => (G ω)ᵀ) (complexGaussianMatrix n m) μ :=
  ((measurePreserving_curry_pi (ν := fun (_ : n) (_ : m) => complexGaussian)).comp
    ((measurePreserving_arrowCongr' (fun _ : m × n => complexGaussian)
      (fun _ : n × m => complexGaussian) (Equiv.prodComm m n) (MeasurableEquiv.refl ℂ)
      fun _ => MeasurePreserving.id _).comp
    (measurePreserving_curry_pi (ν := fun (_ : m) (_ : n) => complexGaussian)).symm)).comp_hasLaw
    hG

/-- Right multiplication by a unitary matrix preserves the standard complex Gaussian law. -/
private theorem hasLaw_mul_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    [DecidableEq r] {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ)
    {V : Matrix r r ℂ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => G ω * V) (complexGaussianMatrix r r) μ := by
  have hW : HasOrthonormalCols Vᴴᵀ := by
    rw [hasOrthonormalCols_iff, show Vᴴᵀᴴ = Vᵀ by ext; simp, ← Matrix.transpose_mul,
      hV.conjTranspose_mul_self, Matrix.transpose_one]
  convert hasLaw_transpose_of_hasLaw_complexGaussianMatrix
    (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix
      (hasLaw_transpose_of_hasLaw_complexGaussianMatrix hG) hW) using 2 with ω
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, show Vᴴᵀᴴᵀ = V by ext; simp]

/-- A unit vector is column $i$ of a unitary matrix. -/
private theorem exists_hasOrthonormalCols_col_eq {r : Type*} [Fintype r] [DecidableEq r]
    {u : r → ℂ} (hu : ‖WithLp.toLp 2 u‖ = 1) (i : r) :
    ∃ V : Matrix r r ℂ, HasOrthonormalCols V ∧ ∀ a, V a i = u a := by
  set U : Matrix r {a // a = i} ℂ := Matrix.of fun a _ => u a
  have hU : HasOrthonormalCols U := by
    rw [hasOrthonormalCols_iff]
    ext a b
    obtain rfl : a = b := Subsingleton.elim a b
    have h1 := EuclideanSpace.inner_toLp_toLp u u
    rw [inner_self_eq_norm_sq_to_K, hu, dotProduct] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, U, Matrix.of_apply,
      Matrix.one_apply_eq]
    simpa [mul_comm] using h1.symm
  obtain ⟨U', hU'⟩ := hU.exists_fromCols (p := {a // ¬a = i}) (by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
    have := Fintype.card_pos_iff.2 ⟨i⟩
    omega)
  refine ⟨(Matrix.fromCols U U').submatrix (Equiv.refl r) (Equiv.sumCompl (· = i)).symm,
    hU'.submatrix (Equiv.refl r) (Equiv.injective _), fun a => ?_⟩
  simp only [Matrix.submatrix_apply, Equiv.refl_apply]
  rw [Equiv.sumCompl_symm_apply_of_pos (p := fun x => x = i) rfl, Matrix.fromCols_apply_inl]
  rfl

/-- The residual of $\mathbf{g}$ off the range of $\mathbf{Y}$ is at most its distance to
that range. -/
private theorem norm_one_sub_rangeProjector_mulVec_le_iInf {r q : Type*} [Fintype r]
    [Fintype q] [DecidableEq r] (Y : Matrix r q ℂ) (g : r → ℂ) :
    ‖WithLp.toLp 2 ((1 - rangeProjector Y) *ᵥ g)‖ ≤
      ⨅ z : q → ℂ, ‖WithLp.toLp 2 (g + Y *ᵥ z)‖ := by
  have hQY : (1 - rangeProjector Y) * Y = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]
  refine le_ciInf fun z => ?_
  calc _ = ‖WithLp.toLp 2 ((1 - rangeProjector Y) *ᵥ (g + Y *ᵥ z))‖ := by
        rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, hQY, Matrix.zero_mulVec, add_zero]
    _ ≤ _ := (isStarProjection_rangeProjector Y).one_sub.norm_toLp_mulVec_le _

/-- The projector off the range of a matrix with fewer columns than rows is nonzero. -/
private theorem one_sub_rangeProjector_ne_zero {r q : Type*} [Fintype r] [Fintype q]
    [DecidableEq r] (Y : Matrix r q ℂ) (h : Fintype.card q < Fintype.card r) :
    1 - rangeProjector Y ≠ 0 := by
  intro h0
  have h1 := Matrix.rank_mul_le_left Y (pinv Y)
  rw [mul_pinv, ← sub_eq_zero.mp h0, Matrix.rank_one] at h1
  exact absurd (h1.trans (Matrix.rank_le_card_width Y)) (not_le.mpr h)

/-- Column $j$ of a standard complex Gaussian square matrix is within $s$ of the span of the other
columns with probability at most $s^2$: condition on the other columns, which are independent of
it. -/
private theorem measureReal_iInf_norm_add_mulVec_le_le {r : Type*} [Fintype r]
    [DecidableEq r] {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) (j : r)
    {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ⨅ z : {j' // j' ≠ j} → ℂ, ‖WithLp.toLp 2 ((fun i => G ω i j) +
      (G ω).submatrix id (Subtype.val : {j' // j' ≠ j} → r) *ᵥ z)‖ ≤ s} ≤ s ^ 2 := by
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  -- split the matrix into column `j` and the other columns, which are independent
  let : Fintype {j' // j' = j} := Subtype.fintype _
  have h1 : MeasurePreserving (fun x : {j' // j' = j} → ℂ => x ⟨j, rfl⟩)
      (Measure.pi fun _ => complexGaussian) complexGaussian := by
    convert measurePreserving_funUnique complexGaussian {j' // j' = j}
    exact congrArg _ (Subsingleton.elim _ _)
  have hΨ := ((measurePreserving_pi _ _ fun _ => h1).prod
      (MeasurePreserving.id (Measure.pi fun _ : r =>
        Measure.pi fun _ : {j' // ¬j' = j} => complexGaussian))).comp
    ((measurePreserving_arrowProdEquivProdArrow _ _ r _ _).comp
      (measurePreserving_pi _ _ fun _ =>
        measurePreserving_piEquivPiSubtypeProd (fun _ : r => complexGaussian) (· = j)))
  set S : Set ((r → ℂ) × (r → {j' // ¬j' = j} → ℂ)) :=
    {p | ⨅ z : {j' // ¬j' = j} → ℂ, ‖WithLp.toLp 2 (p.1 + Matrix.of p.2 *ᵥ z)‖ ≤ s}
  have hS : MeasurableSet S := by
    refine measurableSet_le (UpperSemicontinuous.measurable (upperSemicontinuous_ciInf
      (fun p => ⟨0, ?_⟩) fun z => Continuous.upperSemicontinuous ?_)) measurable_const
    · rintro _ ⟨z, rfl⟩
      positivity
    · fun_prop
  calc _ = ((complexGaussianVector r).prod
        (Measure.pi fun _ : r => Measure.pi fun _ : {j' // ¬j' = j} => complexGaussian)).real S :=
        (hΨ.comp_hasLaw hG).measureReal_eq (p := (· ∈ S)) hS
    _ ≤ s ^ 2 := by
      rw [measureReal_def, Measure.prod_apply_symm hS]
      refine ENNReal.toReal_le_of_le_ofReal (sq_nonneg s) ?_
      refine (lintegral_mono fun y => ?_).trans_eq (by rw [lintegral_const, measure_univ, mul_one])
      have h := measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector HasLaw.id
        (isStarProjection_rangeProjector (Matrix.of y)).one_sub
        (one_sub_rangeProjector_ne_zero _ (Fintype.card_subtype_lt (x := j) (by simp))) hs
      calc _ ≤ complexGaussianVector r
            {x | ‖WithLp.toLp 2 ((1 - rangeProjector (Matrix.of y)) *ᵥ x)‖ ≤ s} :=
            measure_mono fun x hx => (norm_one_sub_rangeProjector_mulVec_le_iInf _ x).trans hx
        _ = ENNReal.ofReal ((complexGaussianVector r).real
            {x | ‖WithLp.toLp 2 ((1 - rangeProjector (Matrix.of y)) *ᵥ x)‖ ≤ s}) :=
            (ofReal_measureReal (measure_ne_top _ _)).symm
        _ ≤ ENNReal.ofReal (s ^ 2) := ENNReal.ofReal_le_ofReal h
/-- Column $j$ of a standard complex Gaussian square matrix is within $s$ of a combination of the
other columns with probability at most $s^2$. -/
private theorem measureReal_exists_norm_mulVec_le_le {r : Type*} [Fintype r]
    {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) (j : r) {s : ℝ}
    (hs : 0 ≤ s) :
    μ.real {ω | ∃ y : r → ℂ, y j = 1 ∧ ‖WithLp.toLp 2 (G ω *ᵥ y)‖ ≤ s} ≤ s ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  refine (measureReal_mono fun ω hω => ?_).trans (measureReal_iInf_norm_add_mulVec_le_le hG j hs)
  obtain ⟨y, hy, hyle⟩ := hω
  simp only [Set.mem_ofPred_eq]
  refine (ciInf_le ⟨0, ?_⟩ fun j' => y j'.1).trans (le_of_eq_of_le ?_ hyle)
  · rintro _ ⟨z, rfl⟩
    positivity
  · congr 2
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.submatrix_apply, id]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j, hy, mul_one]

/-- Cauchy–Schwarz for the bilinear dot product of complex vectors. -/
private theorem norm_dotProduct_le {r : Type*} [Fintype r] (a b : r → ℂ) :
    ‖a ⬝ᵥ b‖ ≤ ‖WithLp.toLp 2 a‖ * ‖WithLp.toLp 2 b‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (WithLp.toLp 2 (star a)) (WithLp.toLp 2 b)
  rw [EuclideanSpace.inner_toLp_toLp, star_star, dotProduct_comm] at h
  refine h.trans_eq ?_
  congr 1
  simp [EuclideanSpace.norm_eq]

/-- For an invertible $\mathbf{A}$ and $\mathbf{a} = \mathbf{A}^{-\mathsf{T}}\mathbf{g} \ne 0$
there is $\mathbf{x}$ with $\mathbf{g}^{\mathsf{T}}\mathbf{x} = 1$ and
$\|\mathbf{A}\mathbf{x}\| = 1/\|\mathbf{a}\|$. -/
private theorem exists_dotProduct_eq_one_and_norm_mulVec_le {r : Type*} [Fintype r]
    [DecidableEq r] (A : Matrix r r ℂ) (hA : IsUnit A.det) (g : r → ℂ)
    (ha : Matrix.vecMul g A⁻¹ ≠ 0) :
    ∃ x : r → ℂ, g ⬝ᵥ x = 1 ∧
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ≤ 1 / ‖WithLp.toLp 2 (Matrix.vecMul g A⁻¹)‖ := by
  set a := Matrix.vecMul g A⁻¹
  have hn : ‖WithLp.toLp 2 a‖ ≠ 0 := by
    rw [norm_ne_zero_iff]
    exact fun h => ha (congrArg WithLp.ofLp h)
  have hstar : ‖WithLp.toLp 2 (star a)‖ = ‖WithLp.toLp 2 a‖ := by
    simp [EuclideanSpace.norm_eq]
  have hdot : a ⬝ᵥ star a = (‖WithLp.toLp 2 a‖ : ℂ) ^ 2 := by
    have h1 := EuclideanSpace.inner_toLp_toLp a a
    rw [inner_self_eq_norm_sq_to_K] at h1
    exact h1.symm
  refine ⟨A⁻¹ *ᵥ (((‖WithLp.toLp 2 a‖ : ℂ) ^ 2)⁻¹ • star a), ?_, ?_⟩
  · rw [Matrix.dotProduct_mulVec, dotProduct_smul, hdot, smul_eq_mul,
      inv_mul_cancel₀ (by exact_mod_cast pow_ne_zero 2 hn)]
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hA, Matrix.one_mulVec, WithLp.toLp_smul,
      norm_smul, hstar, norm_inv, norm_pow, Complex.norm_real, norm_norm]
    exact le_of_eq (by field_simp)

/-- For a fixed probe $\mathbf{g}$ and $T > 0$, $\mathbb{P}[T \le
\|\mathbf{G}^{-\mathsf{T}}\mathbf{g}\|^2] \le \|\mathbf{g}\|^2/T$. -/
private theorem complexGaussianMatrix_real_le_norm_vecMul_inv_sq_le {r : Type*} [Fintype r]
    [DecidableEq r] (g : r → ℂ) {T : ℝ} (hT : 0 < T) :
    (complexGaussianMatrix r r).real {A | T ≤ ‖WithLp.toLp 2 (Matrix.vecMul g A⁻¹)‖ ^ 2} ≤
      ‖WithLp.toLp 2 g‖ ^ 2 / T := by
  rcases eq_or_ne g 0 with rfl | hg
  · refine le_of_eq_of_le (by
      rw [show {A : Matrix r r ℂ | T ≤ ‖WithLp.toLp 2 (Matrix.vecMul 0 A⁻¹)‖ ^ 2} = ∅ from
        Set.eq_empty_of_forall_notMem fun A hA => by simp at hA; linarith, measureReal_empty])
      (by positivity)
  obtain ⟨j₀, -⟩ := Function.ne_iff.1 hg
  set n := ‖WithLp.toLp 2 g‖
  have hn : 0 < n := by
    rw [norm_pos_iff]
    exact fun h => hg (congrArg WithLp.ofLp h)
  have hu : ‖WithLp.toLp 2 ((n : ℂ)⁻¹ • star g)‖ = 1 := by
    rw [WithLp.toLp_smul, norm_smul, norm_inv, Complex.norm_real, norm_norm,
      show ‖WithLp.toLp 2 (star g)‖ = n by simp [n, EuclideanSpace.norm_eq], inv_mul_cancel₀ hn.ne']
  obtain ⟨V, hV, hVcol⟩ := exists_hasOrthonormalCols_col_eq hu j₀
  have hVV : V * Vᴴ = 1 := mul_eq_one_comm.1 hV.conjTranspose_mul_self
  refine (measureReal_mono fun A hA => ?_).trans ((measureReal_exists_norm_mulVec_le_le
    (hasLaw_mul_of_hasLaw_complexGaussianMatrix HasLaw.id hV) j₀ (s := n / √T)
    (by positivity)).trans_eq (by rw [div_pow, Real.sq_sqrt hT.le]))
  simp only [Set.mem_ofPred_eq] at hA ⊢
  have ha : Matrix.vecMul g A⁻¹ ≠ 0 := fun h => by simp [h] at hA; linarith
  have hdet : IsUnit A.det := by
    by_contra h
    exact ha (by rw [Matrix.nonsing_inv_apply_not_isUnit A h, Matrix.vecMul_zero])
  obtain ⟨x, hgx, hAx⟩ := exists_dotProduct_eq_one_and_norm_mulVec_le A hdet g ha
  have hsq : √T ≤ ‖WithLp.toLp 2 (Matrix.vecMul g A⁻¹)‖ := Real.sqrt_le_iff.2 ⟨by positivity, hA⟩
  refine ⟨(n : ℂ) • (Vᴴ *ᵥ x), ?_, ?_⟩
  · rw [← hgx, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct, dotProduct,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.conjTranspose_apply, hVcol]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', Pi.star_apply, star_inv₀,
      Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
  · rw [Matrix.mulVec_smul, show (id A * V) *ᵥ (Vᴴ *ᵥ x) = A *ᵥ x by
        rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hVV, Matrix.mul_one]; rfl,
      WithLp.toLp_smul, norm_smul, Complex.norm_real, norm_norm, div_eq_mul_inv]
    gcongr
    exact hAx.trans (by simpa using inv_anti₀ (by positivity) hsq)

/-- If $\mathbf{A}$ is invertible and $\|\mathbf{A}\mathbf{w}\| \le x$ for a unit $\mathbf{w}$,
then $\mathbb{P}[1/x^2 \le \|\mathbf{A}^{-\mathsf{T}}\mathbf{g}\|^2] \ge e^{-1}$ for a standard
complex Gaussian vector $\mathbf{g}$. -/
private theorem exp_neg_one_le_complexGaussianVector_real {r : Type*} [Fintype r]
    [DecidableEq r] (A : Matrix r r ℂ) (hA : IsUnit A.det) {w : r → ℂ}
    (hw : ‖WithLp.toLp 2 w‖ = 1) {x : ℝ} (hx : 0 < x) (hAw : ‖WithLp.toLp 2 (A *ᵥ w)‖ ≤ x) :
    Real.exp (-1) ≤ (complexGaussianVector r).real
      {v | 1 / x ^ 2 ≤ ‖WithLp.toLp 2 (Matrix.vecMul v A⁻¹)‖ ^ 2} := by
  have : IsProbabilityMeasure (complexGaussianVector r) := inferInstance
  -- `v ⬝ᵥ w` is a standard complex Gaussian: one column of a unitary invariance
  set V : Matrix r Unit ℂ := Matrix.of fun i _ => star (w i)
  have hV : HasOrthonormalCols V := by
    rw [hasOrthonormalCols_iff]
    ext a b
    have h1 := EuclideanSpace.inner_toLp_toLp w w
    rw [inner_self_eq_norm_sq_to_K, hw, dotProduct] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply,
      Matrix.one_apply_eq, star_star]
    simpa using h1.symm
  have hM : HasLaw (fun v : r → ℂ => Matrix.of fun i (_ : Unit) => v i)
      (complexGaussianMatrix r Unit) (complexGaussianVector r) :=
    (measurePreserving_pi _ _ fun _ =>
      (measurePreserving_funUnique complexGaussian Unit).symm).comp_hasLaw HasLaw.id
  have hz : HasLaw (fun v : r → ℂ => (Vᴴ * Matrix.of fun i (_ : Unit) => v i) () ())
      complexGaussian (complexGaussianVector r) :=
    ((measurePreserving_funUnique complexGaussian Unit).comp
      (measurePreserving_funUnique (complexGaussianVector Unit) Unit)).comp_hasLaw
      (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix hM hV)
  calc Real.exp (-1) ≤ complexGaussian.real {z | 1 ≤ ‖z‖ ^ 2} :=
        exp_neg_one_le_complexGaussian_real
    _ = (complexGaussianVector r).real
        {v | 1 ≤ ‖(Vᴴ * Matrix.of fun i (_ : Unit) => v i) () ()‖ ^ 2} :=
        (hz.measureReal_eq (p := fun z => 1 ≤ ‖z‖ ^ 2)
          (measurableSet_le measurable_const (by fun_prop))).symm
    _ ≤ _ := measureReal_mono fun v hv => by
      simp only [Set.mem_ofPred_eq] at hv ⊢
      have hvw : (Vᴴ * Matrix.of fun i (_ : Unit) => v i) () () =
          Matrix.vecMul v A⁻¹ ⬝ᵥ (A *ᵥ w) := by
        rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA,
          Matrix.one_mulVec, dotProduct_comm]
        simp [V, Matrix.mul_apply, dotProduct]
      rw [hvw] at hv
      have hcs := norm_dotProduct_le (Matrix.vecMul v A⁻¹) (A *ᵥ w)
      rw [div_le_iff₀ (by positivity)]
      have h0 := norm_nonneg (Matrix.vecMul v A⁻¹ ⬝ᵥ (A *ᵥ w))
      have h1 := norm_nonneg (WithLp.toLp 2 (Matrix.vecMul v A⁻¹))
      have h2 := norm_nonneg (WithLp.toLp 2 (A *ᵥ w))
      nlinarith [mul_le_mul_of_nonneg_left hAw h1]

/-- **Smallest singular value of a square complex Gaussian matrix, linear in the size** (CG6'):
for $\mathbf{G}$ an $r \times r$ standard complex Gaussian matrix and $x \ge 0$,
$\mathbb{P}[\sigma_{\min}(\mathbf{G}) \le x] \le e\,r x^2$. Edelman's exact law
$1 - e^{-r x^2}$ [Edelman1988] is smaller by the factor $e$; the elementary
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix` has $r^2x^2$. The probe
argument of [SankarSpielmanTeng2006, Lemma 3.2], complex version.
Proof: let $\mathbf{g}$ be an independent standard complex Gaussian vector (work on the product
of the law of $\mathbf{G}$ with `NLAlib.complexGaussianVector`, as in the helper of CG6). If
$\sigma_{\min}(\mathbf{G}) \le x$ then $\|\mathbf{G}^{-1}\|_2 \ge 1/x$
(`NLAlib.singularValues_le_iff_mem_spectrum_or_le_specNorm_inv`, invertibility a.s. from
CG6 at $x = 0$), and $\|\mathbf{G}^{-1}\mathbf{g}\| \ge \|\mathbf{G}^{-1}\|\,\lvert
\mathbf{b}^{\mathsf H}\mathbf{g}\rvert$ for a top right singular vector $\mathbf{b}$ of
$\mathbf{G}^{-1}$; given $\mathbf{G}$, $\mathbf{b}^{\mathsf H}\mathbf{g}$ is standard complex
Gaussian (`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`), so
$\mathbb{P}[\lvert\mathbf{b}^{\mathsf H}\mathbf{g}\rvert^2 \ge 1] = e^{-1}$ (CG7, and its
equality version). Conversely, given $\mathbf{g} \ne 0$, a unitary $\mathbf{Q}$ with
$\mathbf{Q}\mathbf{g} = \|\mathbf{g}\|\mathbf{e}_1$ gives $\|\mathbf{G}^{-1}\mathbf{g}\| =
\|\mathbf{g}\|\,\|(\mathbf{Q}\mathbf{G})^{-1}\mathbf{e}_1\|$ with $\mathbf{Q}\mathbf{G}$ again
standard, and $\|\mathbf{H}^{-1}\mathbf{e}_1\| = 1/\operatorname{dist}(\text{row}_1,
\text{span of the other rows})$, whose square is at least $1/T$ with probability at most $1/T$
(the CG5 step of CG6, on rows); averaging over $\mathbf{g}$ gives
$\mathbb{P}[\|\mathbf{G}^{-1}\mathbf{g}\|^2 \ge T] \le \mathbb{E}\|\mathbf{g}\|^2/T = r/T$. With
$T = 1/x^2$: $e^{-1}\,\mathbb{P}[\sigma_{\min} \le x] \le r x^2$. L, about 350 lines. -/
theorem measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix
    {r : Type*} [Fintype r] {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ)
    {k : ℕ} (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ Real.exp 1 * (Fintype.card r : ℝ) * x ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  have h0 : μ.real {ω | singularValues (G ω) k ≤ 0} = 0 := le_antisymm (by
    simpa using measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix hG hk le_rfl)
    measureReal_nonneg
  rcases hx.eq_or_lt with rfl | hx
  · rw [h0]
    positivity
  set γ := complexGaussianVector r
  set ρ := complexGaussianMatrix r r
  set S : Set (Matrix r r ℂ × (r → ℂ)) :=
    {p | 1 / x ^ 2 ≤ ‖WithLp.toLp 2 (Matrix.vecMul p.2 p.1⁻¹)‖ ^ 2}
  have hS : MeasurableSet S := by
    have hv : Measurable fun q : (r → ℂ) × Matrix r r ℂ => Matrix.vecMul q.1 q.2 :=
      (continuous_fst.matrix_vecMul continuous_snd).measurable
    exact measurableSet_le measurable_const ((measurable_norm.comp
      ((PiLp.continuous_toLp 2 _).measurable.comp
        (hv.comp (measurable_snd.prodMk measurable_fst.matrix_inv)))).pow_const 2)
  set B : Set (Matrix r r ℂ) := {A | ENNReal.ofReal (Real.exp (-1)) ≤ γ (Prod.mk A ⁻¹' S)}
  have hB : MeasurableSet B := measurableSet_le measurable_const (measurable_measure_prodMk_left hS)
  have hsub : {ω | singularValues (G ω) k ≤ x} ⊆ {ω | singularValues (G ω) k ≤ 0} ∪ G ⁻¹' B := by
    intro ω hω
    have hG' : (0 : ℂ) • (1 : Matrix r r ℂ) - -G ω = G ω := by simp
    have hiff := fun ε => exists_norm_eq_one_and_norm_mulVec_le_iff (-G ω) 0 hk ε
    rw [hG'] at hiff
    by_cases hdet : IsUnit (G ω).det
    · right
      obtain ⟨w, hw, hAw⟩ := (hiff x).2 hω
      change ENNReal.ofReal _ ≤ γ _
      rw [← ofReal_measureReal (measure_ne_top _ _)]
      exact ENNReal.ofReal_le_ofReal
        (exp_neg_one_le_complexGaussianVector_real (G ω) hdet hw hx hAw)
    · left
      obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (by
        simpa [isUnit_iff_ne_zero] using hdet)
      have hn : ‖WithLp.toLp 2 v‖ ≠ 0 := by
        rw [norm_ne_zero_iff]
        exact fun h => hv0 (congrArg WithLp.ofLp h)
      refine (hiff 0).1 ⟨(‖WithLp.toLp 2 v‖ : ℂ)⁻¹ • v, ?_, ?_⟩
      · simp [norm_smul, hn]
      · simp [Matrix.mulVec_smul, hv]
  have hBle : ρ.real B ≤ Real.exp 1 * (Fintype.card r : ℝ) * x ^ 2 := by
    -- Markov in `A`, Fubini, then the bound for a fixed probe `v`
    have hv : ∀ v, ρ ((fun A => (A, v)) ⁻¹' S) ≤
        ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) := fun v => by
      rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_measureReal (measure_ne_top _ _)]
      refine ENNReal.ofReal_le_ofReal
        ((complexGaussianMatrix_real_le_norm_vecMul_inv_sq_le v (by positivity)).trans_eq ?_)
      field_simp
    have hE : ENNReal.ofReal (Real.exp (-1)) * ρ B ≤
        ENNReal.ofReal (x ^ 2) * (Fintype.card r : ENNReal) := by
      calc ENNReal.ofReal (Real.exp (-1)) * ρ B
          ≤ ∫⁻ A, γ (Prod.mk A ⁻¹' S) ∂ρ :=
            mul_meas_ge_le_lintegral₀ (measurable_measure_prodMk_left hS).aemeasurable _
        _ = ∫⁻ v, ρ ((fun A => (A, v)) ⁻¹' S) ∂γ := by
            rw [← Measure.prod_apply hS, Measure.prod_apply_symm hS]
        _ ≤ ∫⁻ v, ENNReal.ofReal (x ^ 2) * ENNReal.ofReal (‖WithLp.toLp 2 v‖ ^ 2) ∂γ :=
            lintegral_mono hv
        _ = _ := by
            rw [lintegral_const_mul _ (by fun_prop),
              lintegral_ofReal_norm_sq_complexGaussianVector]
    have hR := ENNReal.toReal_mono (by finiteness) hE
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_natCast, ← measureReal_def] at hR
    calc ρ.real B = Real.exp 1 * (Real.exp (-1) * ρ.real B) := by
          rw [← mul_assoc, ← Real.exp_add]; simp
      _ ≤ Real.exp 1 * (x ^ 2 * Fintype.card r) := by gcongr
      _ = _ := by ring
  calc μ.real {ω | singularValues (G ω) k ≤ x}
      ≤ μ.real ({ω | singularValues (G ω) k ≤ 0} ∪ G ⁻¹' B) := measureReal_mono hsub
    _ ≤ μ.real {ω | singularValues (G ω) k ≤ 0} + μ.real (G ⁻¹' B) := measureReal_union_le _ _
    _ = ρ.real B := by rw [h0, zero_add]; exact hG.measureReal_eq (p := (· ∈ B)) hB
    _ ≤ _ := hBle

end NLAlib
