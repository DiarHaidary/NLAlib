/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.Matrix.Spectral.LeastSingularValue
public import NLAlib.Matrix.Basic.Projector
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Complex Gaussian matrices: invariance, norm and smallest singular value (scaffold)

Statements for `NLAlib/RandomMatrix/Gaussian/Complex.lean` (stage HDIAG, wave W3, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.5). A standard complex Gaussian matrix
is the image of a real Gaussian matrix with twice the rows, $(\mathbf{G}_1 +
i\mathbf{G}_2)/\sqrt2$; through it the real results apply: unitary invariance of the
compression $\mathbf{V}^{\mathsf{H}}\mathbf{G}$, the norm tail, and an elementary tail for the
smallest singular value of a square one that replaces Edelman's exact law ([Shah2024, Lemmas 3.1,
3.2]).

## Main results

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
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n p q : Type*} [Fintype m]
  [Fintype n] [Fintype p] [Fintype q]

/-- **Bridge to Mathlib's standard Gaussian**: the standard complex Gaussian law is the image of
Mathlib's `ProbabilityTheory.stdGaussian` on $\mathbb{C}$ (the real two-dimensional standard
Gaussian, of variance $1$ in each part) under $z \mapsto z/\sqrt2$.
Proof: `ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis` with the basis
`Complex.orthonormalBasisOneI`, then `Measure.map_map` and
`ProbabilityTheory.gaussianReal_map_const_mul` on each coordinate, `Measure.map_prod_map`. M,
about 25 lines. -/
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

/-- **A complex Gaussian matrix is a real Gaussian matrix in disguise**: the standard complex
Gaussian law on $m \times n$ matrices is the law of $(\mathbf{G}_1 + i\mathbf{G}_2)/\sqrt2$,
where $\begin{bmatrix} \mathbf{G}_1 \\ \mathbf{G}_2 \end{bmatrix}$ is a $2m \times n$ standard
real Gaussian matrix (rows indexed by $m \oplus m$). No printed source.
Proof: both sides are product measures over the entries (`Measure.pi`); for one entry the law of
$(x + iy)/\sqrt2$ with $x, y \sim \mathcal{N}(0, 1)$ independent is `NLAlib.complexGaussian`
(`ProbabilityTheory.gaussianReal_map_const_mul`, `Measure.map_map`, `Measure.map_prod_map`);
reorganise the index $(m \oplus m) \times n$ as $m \times n \times \mathrm{Bool}$
(`MeasureTheory.measurePreserving_piCongrLeft`, `MeasureTheory.Measure.pi_map_pi`-type lemmas).
L, about 70 lines. -/
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
matrix. [Shah2024, proof of Theorem 3.3], "by rotational invariance".
Proof: realify with `NLAlib.complexGaussianMatrix_eq_map_gaussianMatrix`: the real form of
$\mathbf{V}^{\mathsf{H}}$, $\begin{bmatrix} \operatorname{Re}\mathbf{V}^{\mathsf{H}} &
-\operatorname{Im}\mathbf{V}^{\mathsf{H}} \\ \operatorname{Im}\mathbf{V}^{\mathsf{H}} &
\operatorname{Re}\mathbf{V}^{\mathsf{H}} \end{bmatrix}$ (`Matrix.fromBlocks`), has orthonormal
rows and maps the stacked real Gaussian to the stacked real and imaginary parts of
$\sqrt2\,\mathbf{V}^{\mathsf{H}}\mathbf{G}$; `NLAlib.hasLaw_const_mul_of_hasLaw_gaussianMatrix`,
then back through the realification. M, about 60 lines. -/
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
    simp only [apply_ite Complex.re, Complex.one_re, Complex.zero_re, neg_mul, mul_neg, neg_neg,
      sub_eq_add_neg] at this
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
      neg_mul, mul_neg, neg_neg, sub_eq_add_neg]
    linarith [this]
  have him : ∀ i j : r, ∑ k, ((Vᴴ i k).im * (Vᴴ j k).re - (Vᴴ i k).re * (Vᴴ j k).im) = 0 := by
    intro i j
    have := congrArg Complex.im (congrFun (congrFun hW i) j)
    simp [Matrix.mul_apply, Complex.im_sum, Complex.mul_im, Matrix.one_apply,
      Complex.star_def, Finset.sum_sub_distrib, apply_ite Complex.im] at this ⊢
    rw [← this]
    exact Finset.sum_congr rfl fun k _ => by ring
  set U : Matrix (r ⊕ r) (n ⊕ n) ℝ :=
    Matrix.fromBlocks (Vᴴ.map Complex.re) (-(Vᴴ.map Complex.im)) (Vᴴ.map Complex.im)
      (Vᴴ.map Complex.re) with hUdef
  have hU : HasOrthonormalCols Uᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose]
    have hre' := hre
    have him' := him
    simp only [Matrix.conjTranspose_apply, Complex.star_def, Complex.conj_re, Complex.conj_im,
      Finset.sum_add_distrib, Finset.sum_sub_distrib, neg_mul, mul_neg, neg_mul_neg, neg_neg,
      Finset.sum_neg_distrib, sub_neg_eq_add] at hre' him'
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
      Complex.ofReal_sub, Finset.mul_sum, mul_add, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Complex.star_def, Complex.conj_re, Complex.conj_im]
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
standard complex Gaussian matrix.
Proof: as `NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix` (selection matrices with orthonormal
columns, `NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix` on both sides via the
transpose), or directly from the product structure (`MeasureTheory.Measure.pi_map_restrict`-type
marginal lemmas). M, about 25 lines. -/
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

/-- **Norm tail of a complex Gaussian matrix** (Lemma 3.2): for a standard complex Gaussian
$m \times n$ matrix $\mathbf{G}$ and $t \ge 0$,
$$\mathbb{P}\bigl[\sqrt2\,(\sqrt{\lvert m \rvert} + \sqrt{\lvert n \rvert} + t) \le
\|\mathbf{G}\|_2\bigr] \le 2e^{-t^2/2} \,.$$
[Shah2024, Lemma 3.2], citing [BanksKulkarniMukherjeeSrivastava2021, Lemma 2.2]: there
$\mathbb{P}[\|\mathbf{G}\|_2 > (2\sqrt2 + t)\sqrt n] \le 2e^{-nt^2}$ for square $\mathbf{G}$; the
constant in the exponent differs.
Proof: with the realification,
$\|\mathbf{G}\|_2 \le (\|\mathbf{G}_1\|_2 + \|\mathbf{G}_2\|_2)/\sqrt2$
(`NLAlib.specNorm_add_le`, `NLAlib.specNorm_smul`, and $\|\mathbf{A}.\mathrm{map}(\uparrow)\|_2
\le \|\mathbf{A}\|_2$ for real $\mathbf{A}$, not in the library: a private lemma of about 15
lines, only $\le$ needed); if the left event holds one of the two real norms is at least
$\sqrt{\lvert m \rvert} + \sqrt{\lvert n \rvert} + t$; union bound and
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix` for the two blocks
(`NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix` on `Sum.inl`, `Sum.inr`). M, about 45 lines. -/
theorem measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ≤ specNorm (G ω)} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  sorry

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

/-- **Small ball of a projected complex Gaussian vector**: for a standard complex Gaussian vector
$\mathbf{g}$, a nonzero orthogonal projector $\mathbf{\Pi}$ and $s \ge 0$,
$\mathbb{P}[\|\mathbf{\Pi}\mathbf{g}\| \le s] \le s^2$. A complex Gaussian has two real degrees of
freedom per coordinate: $\lvert z \rvert^2$ is exponential, $\mathbb{P}[\lvert z \rvert \le s] =
1 - e^{-s^2} \le s^2$. No printed source.
Proof: pick a unit $\mathbf{w}$ in the range of $\mathbf{\Pi}$; $\|\mathbf{\Pi}\mathbf{g}\| \ge
\lvert \langle \mathbf{w}, \mathbf{g} \rangle \rvert$; $\langle \mathbf{w}, \mathbf{g} \rangle$ is
a standard complex Gaussian (`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`
with a one-column frame, or the realification and
`NLAlib.hasLaw_dotProduct_of_hasLaw_gaussianVector`); its squared modulus is a sum of two
independent $\mathcal{N}(0, 1/2)$ squares, whose CDF at $s^2$ is $1 - e^{-s^2}$ (polar
coordinates, `integral_comp_polarCoord_symm`, or the $\chi^2_2$ law of
`Probability/Distributions/ChiSquare.lean`); `Real.add_one_le_exp`. L, about 60 lines. -/
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

/-- **Smallest singular value of a square complex Gaussian matrix** (Lemma 3.1): for a standard
complex Gaussian $r \times r$ matrix $\mathbf{G}$, $k + 1 = \lvert r \rvert$ and $x \ge 0$,
$$\mathbb{P}[\sigma_k(\mathbf{G}) \le x] \le \lvert r \rvert^2 x^2 \,.$$
[Shah2024, Lemma 3.1], citing [Edelman1988, Theorem 3.2]: there $(\lvert r \rvert/2)x^2$ (the exact
law of $\sigma_{\min}$); this elementary bound loses a factor $2\lvert r \rvert$, which costs
$O(\log n)$ bits in the precision of the eigensolver. This can be improved when the proof is
written: Edelman's sharp law, $\mathbb{P}[\sigma_{\min} \le x] = 1 - e^{-\lvert r \rvert x^2}$,
would improve the constant (a follow-up, not needed for the stage).
Proof: by `NLAlib.exists_iInf_norm_mulVec_le_of_singularValues_le`, $\sigma_k \le x$ puts some
column $\mathbf{g}_j$ within $\sqrt{\lvert r \rvert}\,x$ of the span of the others, that is
$\|(\mathbf{I} - \mathbf{P}_j)\mathbf{g}_j\| \le \sqrt{\lvert r \rvert}\,x$ with $\mathbf{P}_j$ the
projector onto the span of the other columns (`NLAlib.rangeProjector`; identify the infimum with
the projection residual, `NLAlib.isStarProjection_rangeProjector`), a nonzero projector since the
others span at most $\lvert r \rvert - 1$ dimensions. Union bound over $j$; for each $j$, condition
on the other columns (independent of $\mathbf{g}_j$, `ProbabilityTheory.iIndepFun` of the columns
from the product law, `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral` or
`Measure.prod` Fubini) and apply
`NLAlib.measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector`
with $s = \sqrt{\lvert r \rvert}\,x$. Measurability of $\mathbf{P}_j$ in the other columns:
`Probability/Measurability/Matrix.lean`. L, about 120 lines. -/
theorem measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) {k : ℕ}
    (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ (Fintype.card r : ℝ) ^ 2 * x ^ 2 := by
  sorry

end NLAlib
