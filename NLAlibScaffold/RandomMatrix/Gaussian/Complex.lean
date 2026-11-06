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
  sorry

end NLAlib
