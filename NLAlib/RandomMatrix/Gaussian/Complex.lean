/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Basic
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.Matrix.Spectral.LeastSingularValue
public import NLAlib.Matrix.Basic.Projector
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Complex Gaussian vectors and matrices

`NLAlib.complexGaussian` is the standard complex Gaussian law $\mathcal{N}_{\mathbb{C}}(0, 1)$ on
$\mathbb{C}$: the real and imaginary parts are independent centred Gaussians of variance $1/2$,
so that $\mathbb{E}\lvert z \rvert^2 = 1$. `NLAlib.complexGaussianVector n` and
`NLAlib.complexGaussianMatrix m n` are the laws of a vector and of a matrix with independent
standard complex Gaussian entries, written as products as the real laws
`NLAlib.gaussianVector` and `NLAlib.gaussianMatrix` are. Mathlib's `stdGaussian ℂ` is the real
two-dimensional standard Gaussian on $\mathbb{C}$, of variance $1$ in each part, which is
$\sqrt2$ times a standard complex Gaussian. These are the test matrices of randomized deflation
([Shah2024, Section 3]), whose analysis uses the norm tail of
[BanksKulkarniMukherjeeSrivastava2021] and, in place of the exact law of the smallest singular
value [Edelman1988], an elementary small-ball bound.

## Main definitions

* `NLAlib.complexGaussian`, `NLAlib.complexGaussianVector`, `NLAlib.complexGaussianMatrix`.

## Main results

* `NLAlib.isProbabilityMeasure_complexGaussian`,
  `NLAlib.isProbabilityMeasure_complexGaussianVector`,
  `NLAlib.isProbabilityMeasure_complexGaussianMatrix`.
* `NLAlib.complexGaussian_eq_map_stdGaussian`: the bridge to Mathlib.
* `NLAlib.complexGaussianMatrix_eq_map_gaussianMatrix`: the realification.
* `NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`,
  `NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix`.
* `NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`: Lemma 3.2.
* `NLAlib.measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector`: small ball of a
  projection.
* `NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`: Lemma 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal Matrix

namespace NLAlib

/-- The **standard complex Gaussian law** $\mathcal{N}_{\mathbb{C}}(0, 1)$: the law of
$x + iy$ for independent real $x, y \sim \mathcal{N}(0, 1/2)$. -/
noncomputable def complexGaussian : Measure ℂ :=
  ((gaussianReal 0 2⁻¹).prod (gaussianReal 0 2⁻¹)).map Complex.measurableEquivRealProd.symm

/-- The standard complex Gaussian law is a probability measure. -/
instance isProbabilityMeasure_complexGaussian : IsProbabilityMeasure complexGaussian :=
  Measure.isProbabilityMeasure_map Complex.measurableEquivRealProd.symm.measurable.aemeasurable

/-- The law of a vector with independent standard complex Gaussian entries. -/
noncomputable abbrev complexGaussianVector (n : Type*) [Fintype n] : Measure (n → ℂ) :=
  Measure.pi fun _ : n => complexGaussian

/-- The complex Gaussian vector law is a probability measure. -/
instance isProbabilityMeasure_complexGaussianVector (n : Type*) [Fintype n] :
    IsProbabilityMeasure (complexGaussianVector n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : n => complexGaussian))

/-- The law of a matrix with independent standard complex Gaussian entries, written as
independent rows, each a standard complex Gaussian vector. -/
noncomputable abbrev complexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    Measure (Matrix m n ℂ) :=
  Measure.pi fun _ : m => complexGaussianVector n

/-- The complex Gaussian matrix law is a probability measure. -/
instance isProbabilityMeasure_complexGaussianMatrix (m n : Type*) [Fintype m] [Fintype n] :
    IsProbabilityMeasure (complexGaussianMatrix m n) :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi fun _ : m => complexGaussianVector n))

section Laws

open MeasureTheory ProbabilityTheory
open scoped Matrix

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n p q : Type*} [Fintype m]
  [Fintype n] [Fintype p] [Fintype q]

/-- Bridge to Mathlib's standard Gaussian: the standard complex Gaussian law is the image of
Mathlib's `ProbabilityTheory.stdGaussian` on $\mathbb{C}$ (the real two-dimensional standard
Gaussian, of variance $1$ in each part) under $z \mapsto z/\sqrt2$. -/
theorem complexGaussian_eq_map_stdGaussian :
    complexGaussian = (stdGaussian ℂ).map fun z => ((√2 : ℝ)⁻¹ : ℂ) * z := by
  set c : ℝ := (√2)⁻¹ with hc
  have hc2 : (⟨c ^ 2, sq_nonneg c⟩ : NNReal) * 1 = 2⁻¹ := by
    rw [mul_one]
    apply NNReal.eq
    simp [hc, inv_pow, Real.sq_sqrt]
    rfl
  have hν : (gaussianReal 0 1).map (fun x : ℝ => c * x) = gaussianReal 0 2⁻¹ := by
    rw [gaussianReal_map_const_mul, mul_zero]
    congr 1
  have hF : (fun v : Fin 2 → ℝ => ∑ i, v i • Complex.orthonormalBasisOneI i) =
      (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ∘ MeasurableEquiv.finTwoArrow := by
    ext v
    simp [Fin.sum_univ_two, Complex.orthonormalBasisOneI]
  have hpi := (measurePreserving_finTwoArrow (gaussianReal 0 1)).map_eq
  rw [stdGaussian_eq_map_pi_orthonormalBasis Complex.orthonormalBasisOneI,
    Measure.map_map (by fun_prop) (by fun_prop), hF, ← Function.comp_assoc,
    ← Measure.map_map (by fun_prop) (by fun_prop), hpi, complexGaussian, ← hν,
    Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext p
  rw [← Complex.ofReal_inv, ← hc]
  apply Complex.ext <;> simp

/-- A product of images of product measures is the image of the product of the two products. -/
private lemma pi_map_prod_eq_map_prod_pi {ι α β γ : Type*} [Fintype ι] [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ₁ : Measure α) (μ₂ : Measure β)
    [IsProbabilityMeasure μ₁] [IsProbabilityMeasure μ₂] {h : α × β → γ} (hh : Measurable h) :
    Measure.pi (fun _ : ι => (μ₁.prod μ₂).map h) =
      ((Measure.pi fun _ : ι => μ₁).prod (Measure.pi fun _ : ι => μ₂)).map
        fun p i => h (p.1 i, p.2 i) := by
  have := Measure.isProbabilityMeasure_map (μ := μ₁.prod μ₂) hh.aemeasurable
  rw [← Measure.pi_map_pi fun _ => hh.aemeasurable,
    ← (measurePreserving_arrowProdEquivProdArrow α β ι (fun _ => μ₁) (fun _ => μ₂)).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  rfl

/-- One entry: $(x + iy)/\sqrt2$ with $x, y \sim \mathcal{N}(0, 1)$ independent. -/
private lemma complexGaussian_eq_map_prod_gaussianReal :
    complexGaussian = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      fun p : ℝ × ℝ => (√2 : ℝ)⁻¹ • ((p.1 : ℂ) + Complex.I * p.2) := by
  have h : gaussianReal 0 2⁻¹ = (gaussianReal 0 1).map ((√2 : ℝ)⁻¹ * ·) := by
    rw [gaussianReal_map_const_mul]
    congr 1
    · simp
    · ext; simp
  rw [complexGaussian, h, Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    Measure.map_map (MeasurableEquiv.measurable _) (by fun_prop)]
  congr 1
  ext p
  apply Complex.ext <;> simp [-Complex.ofReal_inv]

/-- A complex Gaussian matrix is a real Gaussian matrix in disguise: the standard complex
Gaussian law on $m \times n$ matrices is the law of $(\mathbf{G}_1 + i\mathbf{G}_2)/\sqrt2$,
where $\begin{bmatrix} \mathbf{G}_1 \\ \mathbf{G}_2 \end{bmatrix}$ is a $2m \times n$ standard
real Gaussian matrix (rows indexed by $m \oplus m$). No printed source. -/
theorem complexGaussianMatrix_eq_map_gaussianMatrix :
    complexGaussianMatrix m n = (gaussianMatrix (m ⊕ m) n).map fun X =>
      (√2 : ℝ)⁻¹ • ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) := by
  have hg : Measurable fun p : ℝ × ℝ => (√2 : ℝ)⁻¹ • ((p.1 : ℂ) + Complex.I * p.2) := by
    fun_prop
  have hrow : complexGaussianVector n = ((gaussianVector n).prod (gaussianVector n)).map
      fun p j => (√2 : ℝ)⁻¹ • ((p.1 j : ℂ) + Complex.I * p.2 j) := by
    rw [complexGaussianVector, complexGaussian_eq_map_prod_gaussianReal]
    exact pi_map_prod_eq_map_prod_pi _ _ hg
  have hrowm : Measurable fun (p : (n → ℝ) × (n → ℝ)) (j : n) =>
      (√2 : ℝ)⁻¹ • ((p.1 j : ℂ) + Complex.I * p.2 j) := by
    fun_prop
  rw [complexGaussianMatrix, hrow, pi_map_prod_eq_map_prod_pi _ _ hrowm, gaussianMatrix,
    ← (measurePreserving_sumPiEquivProdPi fun _ : m ⊕ m => gaussianVector n).map_eq,
    Measure.map_map (by fun_prop) (MeasurableEquiv.measurable _)]
  rfl

/-- **Unitary invariance of a complex Gaussian matrix**: if $\mathbf{G}$ is a standard complex
Gaussian $n \times k$ matrix and $\mathbf{V} \in \mathbb{C}^{n \times r}$ has orthonormal
columns, then $\mathbf{V}^{\mathsf{H}}\mathbf{G}$ is a standard complex Gaussian $r \times k$
matrix. [Shah2024, proof of Theorem 3.3], "by rotational invariance". -/
theorem hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    [DecidableEq r] {G : Ω → Matrix n q ℂ} (hG : HasLaw G (complexGaussianMatrix n q) μ)
    {V : Matrix n r ℂ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => Vᴴ * G ω) (complexGaussianMatrix r q) μ := by
  classical
  have hW : Vᴴ * Vᴴᴴ = 1 := by rw [Matrix.conjTranspose_conjTranspose]; exact hV
  have hre : ∀ i j : r, ∑ k, ((Vᴴ i k).re * (Vᴴ j k).re + (Vᴴ i k).im * (Vᴴ j k).im) =
      (if i = j then 1 else 0) := by
    intro i j
    have := congrArg Complex.re (congrFun (congrFun hW i) j)
    simp only [Matrix.mul_apply, Complex.re_sum, Complex.mul_re, Matrix.one_apply,
      Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im] at this
    simp only [apply_ite Complex.re, Complex.one_re, Complex.zero_re, neg_mul, neg_neg,
      sub_eq_add_neg] at this
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
      neg_mul, mul_neg, neg_neg]
    linarith [this]
  have him : ∀ i j : r, ∑ k, ((Vᴴ i k).im * (Vᴴ j k).re - (Vᴴ i k).re * (Vᴴ j k).im) = 0 := by
    intro i j
    have := congrArg Complex.im (congrFun (congrFun hW i) j)
    simp only [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Matrix.one_apply,
      apply_ite Complex.im, Complex.one_im, Complex.zero_im, ite_self] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im]
    ring
  set U : Matrix (r ⊕ r) (n ⊕ n) ℝ :=
    Matrix.fromBlocks (Vᴴ.map Complex.re) (-(Vᴴ.map Complex.im)) (Vᴴ.map Complex.im)
      (Vᴴ.map Complex.re) with hUdef
  have hU : HasOrthonormalCols Uᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose]
    have hre' := hre
    have him' := him
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Finset.sum_add_distrib, neg_mul, mul_neg, neg_neg, Finset.sum_neg_distrib,
      sub_neg_eq_add] at hre' him'
    ext (i | i) (j | j) <;>
      simp [hUdef, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.fromBlocks] <;>
      linarith [hre' i j, him' i j, him' j i, hre' j i]
  have hkey : ∀ X : Matrix (n ⊕ n) q ℝ,
      Vᴴ * ((√2 : ℝ)⁻¹ • ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ)))) =
      (√2 : ℝ)⁻¹ • (((U * X).submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • ((U * X).submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) := by
    intro X
    have hc : ∀ z : ℂ, (starRingEnd ℂ) z = (z.re : ℂ) - (z.im : ℂ) * Complex.I := fun z => by
      apply Complex.ext <;> simp
    ext i j
    simp only [hUdef, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.submatrix_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.neg_apply, Matrix.conjTranspose_apply, id, Matrix.mul_apply, Complex.real_smul,
      smul_eq_mul]
    have key : ∀ (w x1 x2 : ℂ), w * ((((√2 : ℝ)⁻¹ : ℝ) : ℂ) * (x1 + Complex.I * x2)) =
        ((((√2 : ℝ)⁻¹ : ℝ) : ℂ)) * ((w.re : ℂ) * x1 + -(w.im : ℂ) * x2 +
          Complex.I * ((w.im : ℂ) * x1 + (w.re : ℂ) * x2)) := by
      intro w x1 x2
      linear_combination (-((((√2 : ℝ)⁻¹ : ℝ) : ℂ) * (x1 + Complex.I * x2))) * (Complex.re_add_im w)
        + ((((√2 : ℝ)⁻¹ : ℝ) : ℂ) * (w.im : ℂ) * x2) * Complex.I_sq
    simp only [Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_mul,
      Finset.mul_sum, mul_add, Finset.sum_add_distrib, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    have k := key ((starRingEnd ℂ) (V x i)) ((X (Sum.inl x) j : ℝ) : ℂ)
      ((X (Sum.inr x) j : ℝ) : ℂ)
    simp only [Complex.conj_re, Complex.conj_im, Complex.ofReal_neg] at k
    linear_combination k
  have hUlaw : (gaussianMatrix (n ⊕ n) q).map (fun X => U * X) = gaussianMatrix (r ⊕ r) q :=
    (hasLaw_const_mul_of_hasLaw_gaussianMatrix
      (HasLaw.id (μ := gaussianMatrix (n ⊕ n) q)) hU).map_eq
  have hmeas : Measurable (fun Z : Matrix n q ℂ => Vᴴ * Z) :=
    measurable_const.matrix_mul measurable_id
  have hA : (fun ω => Vᴴ * G ω) = (fun Z : Matrix n q ℂ => Vᴴ * Z) ∘ G := rfl
  refine ⟨(hmeas.comp_aemeasurable hG.aemeasurable), ?_⟩
  rw [hA, ← AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hG.aemeasurable, hG.map_eq,
    complexGaussianMatrix_eq_map_gaussianMatrix, complexGaussianMatrix_eq_map_gaussianMatrix,
    Measure.map_map hmeas (by fun_prop), ← hUlaw, Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext X
  exact hkey X

/-- A submatrix of a standard complex Gaussian matrix on injective row and column maps is a
standard complex Gaussian matrix. -/
theorem hasLaw_submatrix_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {f : p → m} (hf : Function.Injective f)
    {e : q → n} (he : Function.Injective e) :
    HasLaw (fun ω => (G ω).submatrix f e) (complexGaussianMatrix p q) μ := by
  classical
  have hsub : Function.Injective (Sum.map f f) := Sum.map_injective.mpr ⟨hf, hf⟩
  have hreal : (gaussianMatrix (m ⊕ m) n).map
      (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix (Sum.map f f) e) = gaussianMatrix (p ⊕ p) q :=
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix (HasLaw.id) hsub he).map_eq
  have hcomm : ∀ X : Matrix (m ⊕ m) n ℝ,
      (√2 : ℝ)⁻¹ • (((X.submatrix (Sum.map f f) e).submatrix Sum.inl id).map
          (fun x : ℝ => (x : ℂ)) +
        Complex.I • ((X.submatrix (Sum.map f f) e).submatrix Sum.inr id).map
          (fun x : ℝ => (x : ℂ))) =
      ((√2 : ℝ)⁻¹ • ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ)))).submatrix f e := by
    intro X
    ext i j
    simp [Matrix.submatrix_apply]
  have hmeasSub : Measurable (fun Z : Matrix m n ℂ => Z.submatrix f e) := by fun_prop
  have hmeasSubR : Measurable (fun X : Matrix (m ⊕ m) n ℝ => X.submatrix (Sum.map f f) e) := by
    fun_prop
  have heq : (complexGaussianMatrix m n).map (fun Z : Matrix m n ℂ => Z.submatrix f e) =
      complexGaussianMatrix p q := by
    rw [complexGaussianMatrix_eq_map_gaussianMatrix, complexGaussianMatrix_eq_map_gaussianMatrix,
      Measure.map_map hmeasSub (by fun_prop), ← hreal, Measure.map_map (by fun_prop) hmeasSubR]
    congr 1
  refine ⟨hmeasSub.comp_aemeasurable hG.aemeasurable, ?_⟩
  rw [← heq, ← hG.map_eq, AEMeasurable.map_map_of_aemeasurable hmeasSub.aemeasurable
    hG.aemeasurable]
  rfl

/-- The squared Euclidean norm of a complex vector is the sum of those of its real and
imaginary parts. -/
private theorem norm_toLp_sq_eq_re_add_im (v : n → ℂ) : ‖WithLp.toLp 2 v‖ ^ 2 =
    ‖WithLp.toLp 2 fun j => (v j).re‖ ^ 2 + ‖WithLp.toLp 2 fun j => (v j).im‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
    EuclideanSpace.norm_toLp_sq_eq_sum_sq, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The complexification of a real matrix has spectral norm at most that of the matrix. -/
private theorem specNorm_map_ofReal_le (A : Matrix m n ℝ) :
    specNorm (A.map fun x : ℝ => (x : ℂ)) ≤ specNorm A := by
  refine (specNorm_le_iff (specNorm_nonneg A)).2 fun x => ?_
  have hv : ∀ i, ((A.map fun r : ℝ => (r : ℂ)) *ᵥ x) i =
      ((A *ᵥ fun j => (x j).re) i : ℂ) + ((A *ᵥ fun j => (x j).im) i : ℂ) * Complex.I := by
    intro i
    apply Complex.ext <;> simp [Matrix.mulVec, dotProduct, Complex.re_sum, Complex.im_sum]
  have hre := norm_toLp_mulVec_le A fun j => (x j).re
  have him := norm_toLp_mulVec_le A fun j => (x j).im
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, norm_toLp_sq_eq_re_add_im,
    norm_toLp_sq_eq_re_add_im x]
  simp only [hv, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, mul_zero, sub_zero, add_zero,
    mul_one, zero_add]
  rw [mul_add]
  gcongr
  · exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hre |>.trans_eq (mul_pow _ _ _)
  · exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 him |>.trans_eq (mul_pow _ _ _)

/-- **Norm tail of a complex Gaussian matrix** (Lemma 3.2): for a standard complex Gaussian
$m \times n$ matrix $\mathbf{G}$ and $t \ge 0$,
$$\mathbb{P}\bigl[\sqrt2\,(\sqrt{\lvert m \rvert} + \sqrt{\lvert n \rvert} + t) \le
\|\mathbf{G}\|_2\bigr] \le 2e^{-t^2/2} \,.$$
[Shah2024, Lemma 3.2], citing [BanksKulkarniMukherjeeSrivastava2021, Lemma 2.2]: there
$\mathbb{P}[\|\mathbf{G}\|_2 > (2\sqrt2 + t)\sqrt n] \le 2e^{-nt^2}$ for square $\mathbf{G}$; the
constant in the exponent differs. -/
theorem measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ≤ specNorm (G ω)} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  have hf : Measurable fun X : Matrix (m ⊕ m) n ℝ => (√2 : ℝ)⁻¹ •
      ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) :=
    Continuous.measurable (by fun_prop)
  rw [hG.measureReal_eq (p := fun A =>
      √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ≤ specNorm A)
      (measurableSet_le measurable_const continuous_specNorm.measurable),
    complexGaussianMatrix_eq_map_gaussianMatrix,
    map_measureReal_apply hf (measurableSet_le measurable_const continuous_specNorm.measurable)]
  have hX := HasLaw.id (μ := gaussianMatrix (m ⊕ m) n)
  have h₁ := measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inl_injective Function.injective_id) ht
  have h₂ := measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hX Sum.inr_injective Function.injective_id) ht
  refine (measureReal_mono fun X hX => ?_).trans ((measureReal_union_le _ _).trans
    ((add_le_add h₁ h₂).trans_eq (two_mul _).symm))
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_union, id] at hX ⊢
  by_contra hcon
  simp only [not_or, not_le] at hcon
  rw [specNorm_real_smul, abs_inv, abs_of_pos (by positivity), ← div_eq_inv_mul,
    le_div_iff₀ (by positivity), mul_comm, ← mul_assoc, Real.mul_self_sqrt zero_le_two] at hX
  have hS := (specNorm_add_le _ _).trans (add_le_add
    (specNorm_map_ofReal_le (X.submatrix Sum.inl id)) (le_refl (specNorm (Complex.I •
      (X.submatrix Sum.inr id).map fun x : ℝ => (x : ℂ)))))
  rw [specNorm_smul, Complex.norm_I, one_mul] at hS
  linarith [hcon.1, hcon.2, specNorm_map_ofReal_le (X.submatrix Sum.inr id)]

/-- The disk of radius $s$ has mass at most $s^2$ under a standard complex Gaussian: $\sqrt2$
times its real and imaginary parts form a standard Gaussian vector of dimension $2$. -/
private theorem complexGaussian_real_closedBall_le {s : ℝ} (hs : 0 ≤ s) :
    complexGaussian.real (Metric.closedBall 0 s) ≤ s ^ 2 := by
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
  have hΦ := ((measurePreserving_finTwoArrow (gaussianReal 0 1)).symm.comp
    (h1.prod h1)).comp h2
  have key := measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector hΦ.hasLaw
    (u := 2 * s ^ 2) (by positivity)
  refine (le_of_eq (congrArg complexGaussian.real ?_)).trans (key.trans (le_of_eq ?_))
  · ext z
    simp only [Metric.mem_closedBall, dist_zero_right, Set.mem_ofPred_eq, Function.comp_apply]
    rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fin.sum_univ_two]
    simp only [Complex.measurableEquivRealProd_apply, Prod.map_apply,
      MeasurableEquiv.finTwoArrow_symm_apply, Fin.cons_zero, Fin.cons_one, mul_pow,
      Real.sq_sqrt zero_le_two]
    rw [← sq_le_sq₀ (norm_nonneg z) hs, Complex.sq_norm, Complex.normSq_apply]
    constructor <;> intro h <;> nlinarith
  · norm_num

/-- Small ball of a projected complex Gaussian vector: for a standard complex Gaussian vector
$\mathbf{g}$, a nonzero orthogonal projector $\mathbf{\Pi}$ and $s \ge 0$,
$\mathbb{P}[\|\mathbf{\Pi}\mathbf{g}\| \le s] \le s^2$. A complex Gaussian has two real degrees of
freedom per coordinate: $\lvert z \rvert^2$ is exponential, $\mathbb{P}[\lvert z \rvert \le s] =
1 - e^{-s^2} \le s^2$. No printed source. -/
theorem measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector {g : Ω → n → ℂ}
    (hg : HasLaw g (complexGaussianVector n) μ) {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (hP₀ : P ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖WithLp.toLp 2 (P *ᵥ g ω)‖ ≤ s} ≤ s ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure_iff.2 inferInstance
  -- a unit vector `w` in the range of `P`
  obtain ⟨v, hv⟩ : ∃ v, P *ᵥ v ≠ 0 := by
    by_contra! h
    exact hP₀ (Matrix.ext_iff_mulVec.mpr fun x => by rw [h x, Matrix.zero_mulVec])
  have hu : ‖WithLp.toLp 2 (P *ᵥ v)‖ ≠ 0 := by simpa using hv
  set w : n → ℂ := ((‖WithLp.toLp 2 (P *ᵥ v)‖ : ℂ)⁻¹) • (P *ᵥ v) with hw_def
  have hw : ‖WithLp.toLp 2 w‖ = 1 := by simp [hw_def, norm_smul, hu]
  have hPw : Pᴴ *ᵥ w = w := by
    rw [hP.conjTranspose_eq, hw_def, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hP.mul_self]
  -- `w` as a one-column frame, and `g` as a one-column matrix
  let V : Matrix n Unit ℂ := Matrix.of fun i _ => w i
  have hV : HasOrthonormalCols V := by
    ext a b
    have h1 := EuclideanSpace.inner_toLp_toLp w w
    rw [inner_self_eq_norm_sq_to_K, hw] at h1
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, V, Matrix.of_apply,
      Matrix.one_apply_eq]
    rw [dotProduct] at h1
    simpa [mul_comm] using h1.symm
  have hG : HasLaw (fun ω => Matrix.of fun i (_ : Unit) => g ω i)
      (complexGaussianMatrix n Unit) μ :=
    (measurePreserving_pi _ _ fun _ =>
      (measurePreserving_funUnique complexGaussian Unit).symm).comp_hasLaw hg
  have hz : HasLaw (fun ω => (Vᴴ * Matrix.of fun i (_ : Unit) => g ω i) () ())
      complexGaussian μ :=
    ((measurePreserving_funUnique complexGaussian Unit).comp
      (measurePreserving_funUnique (complexGaussianVector Unit) Unit)).comp_hasLaw
      (hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix hG hV)
  calc μ.real {ω | ‖WithLp.toLp 2 (P *ᵥ g ω)‖ ≤ s}
      ≤ μ.real {ω | ‖(Vᴴ * Matrix.of fun i (_ : Unit) => g ω i) () ()‖ ≤ s} :=
        measureReal_mono fun ω hω => by
          simp only [Set.mem_ofPred_eq] at hω ⊢
          have h1 : (Vᴴ * Matrix.of fun i (_ : Unit) => g ω i) () () =
              inner ℂ (WithLp.toLp 2 w) (WithLp.toLp 2 (P *ᵥ g ω)) := by
            rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm, Matrix.dotProduct_mulVec,
              ← Matrix.conjTranspose_conjTranspose P, ← Matrix.star_mulVec, hPw]
            rfl
          rw [h1]
          refine (norm_inner_le_norm _ _).trans ?_
          rwa [hw, one_mul]
    _ = complexGaussian.real (Metric.closedBall 0 s) := by
      rw [hz.measureReal_eq (p := fun z => ‖z‖ ≤ s) (measurableSet_le measurable_norm
        measurable_const)]
      congr 1
      ext z
      simp
    _ ≤ s ^ 2 := complexGaussian_real_closedBall_le hs

/-- The distance from column $j$ to the span of the other columns is at most the norm of any
combination of the columns with coefficient $1$ on column $j$. -/
private theorem iInf_norm_add_mulVec_le_iInf {r : Type*} [Fintype r] [DecidableEq r]
    (A : Matrix r r ℂ) (j : r) :
    ⨅ z : {j' // j' ≠ j} → ℂ, ‖WithLp.toLp 2 ((fun i => A i j) +
      A.submatrix id (Subtype.val : {j' // j' ≠ j} → r) *ᵥ z)‖ ≤
      ⨅ x : {x : r → ℂ // x j = 1}, ‖WithLp.toLp 2 (A *ᵥ x.1)‖ := by
  have : Nonempty {x : r → ℂ // x j = 1} := ⟨⟨Pi.single j 1, by simp⟩⟩
  refine le_ciInf fun ⟨x, hx⟩ => (ciInf_le ⟨0, ?_⟩ fun j' => x j'.1).trans_eq ?_
  · rintro _ ⟨z, rfl⟩
    positivity
  · congr 2
    ext i
    simp only [Matrix.mulVec, dotProduct, Pi.add_apply, Matrix.submatrix_apply, id]
    rw [Fintype.sum_eq_add_sum_subtype_ne _ j, hx, mul_one]

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

/-- **Smallest singular value of a square complex Gaussian matrix** (Lemma 3.1): for a standard
complex Gaussian $r \times r$ matrix $\mathbf{G}$, $k + 1 = \lvert r \rvert$ and $x \ge 0$,
$$\mathbb{P}[\sigma_k(\mathbf{G}) \le x] \le \lvert r \rvert^2 x^2 \,.$$
[Shah2024, Lemma 3.1], citing [Edelman1988, Theorem 3.2]: there $(\lvert r \rvert/2)x^2$ (the exact
law of $\sigma_{\min}$); this elementary bound loses a factor $2\lvert r \rvert$, which costs
$O(\log n)$ bits in the precision of the eigensolver. This can be improved when the proof is
written: Edelman's sharp law, $\mathbb{P}[\sigma_{\min} \le x] = 1 - e^{-\lvert r \rvert x^2}$,
would improve the constant (a follow-up, not needed for the stage). -/
theorem measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) {k : ℕ}
    (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ (Fintype.card r : ℝ) ^ 2 * x ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hG.isProbabilityMeasure_iff.2 inferInstance
  calc μ.real {ω | singularValues (G ω) k ≤ x}
      ≤ μ.real (⋃ j, {ω | ⨅ z : {j' // j' ≠ j} → ℂ, ‖WithLp.toLp 2 ((fun i => G ω i j) +
          (G ω).submatrix id (Subtype.val : {j' // j' ≠ j} → r) *ᵥ z)‖ ≤
            √(Fintype.card r) * x}) := measureReal_mono fun ω hω => by
        obtain ⟨j, hj⟩ := exists_iInf_norm_mulVec_le_of_singularValues_le (G ω) hk hω
        exact Set.mem_iUnion.2 ⟨j, (iInf_norm_add_mulVec_le_iInf _ j).trans hj⟩
    _ ≤ ∑ j : r, (√(Fintype.card r) * x) ^ 2 := (measureReal_iUnion_fintype_le _).trans
        (Finset.sum_le_sum fun j _ =>
          measureReal_iInf_norm_add_mulVec_le_le hG j (by positivity))
    _ = (Fintype.card r : ℝ) ^ 2 * x ^ 2 := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_pow,
        Real.sq_sqrt (Nat.cast_nonneg _)]
      ring

end Laws

end NLAlib
