/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.QuadraticForm.HansonWright.OffDiagonal
public import NLAlib.Probability.SubExponential.Tail
public import NLAlib.Probability.SubGaussian.Square

/-!
# The Hanson–Wright inequality

For a real random vector $\mathbf{x}$ with independent coordinates, each sub-Gaussian with proxy
$c$, and any real square matrix $\mathbf{A}$, the quadratic form
$\mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x}$ concentrates about its
mean: <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} -
\mathbb{E}\,\mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} \rvert \ge t\bigr]
\le 2 \exp\Bigl(-\frac{1}{196} \min\Bigl(\frac{t^2}{c^2 \|\mathbf{A}\|_{\mathsf{F}}^2},
\frac{t}{c \|\mathbf{A}\|_2}\Bigr)\Bigr),$$
where the constant in the exponent (`NLAlib.hansonWrightConstant`) is universal, unspecified in
the sources, and is the one the proof here reaches.
The diagonal part is Bernstein's inequality for the centred squares; the
off-diagonal part is bounded by decoupling and comparison with a Gaussian chaos
(`NLAlib/Probability/QuadraticForm/HansonWright/OffDiagonal.lean`). The two are combined by
convexity of $\exp$ with weights $4/7$ and $3/7$ (`NLAlib.HasSubexponentialMGF.add`), which needs
no independence between them: the centred form is sub-exponential with variance proxy
$98 c^2 \|\mathbf{A}\|_{\mathsf{F}}^2$ and scale $28 c \|\mathbf{A}\|_2$, which gives the
constant <!-- value hansonWrightConstant -->$1/196$.

## Main definitions

* `NLAlib.hansonWrightConstant`: the constant in the exponent, of
  value <!-- value hansonWrightConstant -->$1/196$.

## Main results

* `NLAlib.measureReal_quadForm_sub_integral_ge_le`,
  `NLAlib.measureReal_quadForm_sub_integral_le_le`: the upper and lower tails.
* `NLAlib.measureReal_abs_quadForm_sub_integral_ge_le`: **the Hanson–Wright inequality**.

## References

* [R. Vershynin, *High-Dimensional Probability*][Vershynin2018], Theorem 6.2.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {x : Ω → n → ℝ} {c : ℝ≥0}

/-- The Hanson–Wright constant $C_{\mathrm{HW}}$: the universal constant in the exponent of the
Hanson–Wright inequality, which the sources leave unspecified.
[Vershynin2018, Theorem 6.2.1]; Rudelson and Vershynin 2013, Theorem 1.1. The value is what the
proof here reaches; a larger value is a better bound. Use only `hansonWrightConstant_pos` and
`le_hansonWrightConstant`.

The proof reaches <!-- value hansonWrightConstant -->$1/196$: the centred quadratic
form is sub-exponential with variance proxy
$98 c^2 \|\mathbf{A}\|_{\mathsf{F}}^2$ and scale $28 c \|\mathbf{A}\|_2$ (the diagonal part has
$32 c^2 \|\mathbf{A}\|_{\mathsf{F}}^2$ and $4 c \|\mathbf{A}\|_2$, the off-diagonal part
$18 c^2 \|\mathbf{A}\|_{\mathsf{F}}^2$ and $12 c \|\mathbf{A}\|_2$, combined by convexity with
weights $4/7$ and $3/7$), so its tail is at most
$\exp(-\min(t^2 / (196 c^2 \|\mathbf{A}\|_{\mathsf{F}}^2), t / (56 c \|\mathbf{A}\|_2)))$. The
prototype's proof reached $1 / (256 e^2)$. -/
noncomputable irreducible_def hansonWrightConstant : ℝ := 1 / 196

/-- The Hanson–Wright constant is positive: $C_{\mathrm{HW}} > 0$. -/
theorem hansonWrightConstant_pos : 0 < hansonWrightConstant := by
  rw [hansonWrightConstant_def]
  norm_num

/-- An explicit lower bound, $1/196$, on `hansonWrightConstant`, whose value
is <!-- value hansonWrightConstant -->$1/196$. -/
theorem le_hansonWrightConstant : 1 / 196 ≤ hansonWrightConstant := by
  rw [hansonWrightConstant_def]

/-- The diagonal part: $\sum_i \mathbf{A}_{i,i} (\mathbf{x}_i^2 - \mathbb{E}[\mathbf{x}_i^2])$ is
sub-exponential with variance proxy $32 c^2 \|\mathbf{A}\|_{\mathsf{F}}^2$ and scale
$4 c \|\mathbf{A}\|_2$, Bernstein's inequality for the centred squares. -/
private lemma hasSubexponentialMGF_diag (hind : iIndepFun (fun i ω => x ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ) (A : Matrix n n ℝ) :
    HasSubexponentialMGF (fun ω => ∑ i, A i i * (x ω i ^ 2 - ∫ ω', x ω' i ^ 2 ∂μ))
      (32 * c ^ 2 * (frobNorm A).toNNReal ^ 2) (4 * c * (specNorm A).toNNReal) μ := by
  have := hind.isProbabilityMeasure
  have hind' : iIndepFun (fun i ω => x ω i ^ 2 - ∫ ω', x ω' i ^ 2 ∂μ) μ :=
    hind.comp (fun i y => y ^ 2 - ∫ ω', x ω' i ^ 2 ∂μ) fun i => by fun_prop
  have hs := HasSubexponentialMGF.sum_const_mul_of_iIndepFun hind' (s := Finset.univ)
    (fun i _ => (h i).hasSubexponentialMGF_sq_sub_integral) fun i => A i i
  have hF : ((frobNorm A).toNNReal : ℝ) = frobNorm A := Real.coe_toNNReal _ (frobNorm_nonneg A)
  have hS : ((specNorm A).toNNReal : ℝ) = specNorm A := Real.coe_toNNReal _ (specNorm_nonneg A)
  refine hs.mono ?_ (Finset.sup_le fun i _ => ?_)
  · rw [← NNReal.coe_le_coe]
    push_cast
    rw [hF, frobNorm_sq_eq_sum_sq, ← Finset.sum_mul, mul_comm]
    have hd : ∑ i, ‖A i i‖ ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := Finset.sum_le_sum fun i _ => by
      rw [Real.norm_eq_abs, sq_abs]
      exact Finset.single_le_sum (f := fun j => A i j ^ 2) (fun j _ => sq_nonneg _)
        (Finset.mem_univ i)
    gcongr
  · rw [← NNReal.coe_le_coe]
    push_cast
    rw [hS, mul_comm]
    gcongr
    exact norm_apply_le_specNorm A i i

/-- A quadratic form is its diagonal part plus its off-diagonal part. -/
private lemma quadForm_eq_sum_add [DecidableEq n] (A : Matrix n n ℝ) (x : n → ℝ) :
    quadForm A x = ∑ i, A i i * x i ^ 2 + quadForm (A - Matrix.diagonal A.diag) x := by
  rw [quadForm_sub_left, quadForm_diagonal]
  simp [Real.norm_eq_abs, sq_abs]

/-- The centred quadratic form is sub-exponential with variance proxy
$98 c^2 \|\mathbf{A}\|_{\mathsf{F}}^2$ and scale $28 c \|\mathbf{A}\|_2$. -/
private lemma hasSubexponentialMGF_quadForm_sub_integral (hind : iIndepFun (fun i ω => x ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ) (A : Matrix n n ℝ) :
    HasSubexponentialMGF (fun ω => quadForm A (x ω) - ∫ ω', quadForm A (x ω') ∂μ)
      (98 * c ^ 2 * (frobNorm A).toNNReal ^ 2) (28 * c * (specNorm A).toNNReal) μ := by
  classical
  have := hind.isProbabilityMeasure
  have hD := hasSubexponentialMGF_diag hind h A
  have hO := hasSubexponentialMGF_quadForm_sub_diagonal hind h A
  rw [Real.nnnorm_of_nonneg (frobNorm_nonneg A), Real.nnnorm_of_nonneg (specNorm_nonneg A),
    ← Real.toNNReal_of_nonneg, ← Real.toNNReal_of_nonneg] at hO
  have hsq : ∀ i, Integrable (fun ω => A i i * x ω i ^ 2) μ := fun i =>
    (((h i).memLp 2).integrable_sq).const_mul _
  have hEQ : ∫ ω', quadForm A (x ω') ∂μ = ∑ i, A i i * ∫ ω', x ω' i ^ 2 ∂μ := by
    simp only [quadForm_eq_sum_add A]
    rw [integral_add (integrable_finsetSum _ fun i _ => hsq i) hO.integrable,
      hO.integral_eq_zero, add_zero, integral_finsetSum _ fun i _ => hsq i]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _
  have hZ : (fun ω => quadForm A (x ω) - ∫ ω', quadForm A (x ω') ∂μ) = fun ω =>
      (∑ i, A i i * (x ω i ^ 2 - ∫ ω', x ω' i ^ 2 ∂μ)) +
        quadForm (A - Matrix.diagonal A.diag) (x ω) := by
    ext ω
    rw [hEQ, quadForm_eq_sum_add A]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [hZ]
  have hpq : (7 / 4 : ℝ≥0).HolderConjugate (7 / 3) :=
    NNReal.holderConjugate_coe_iff.mp ⟨by norm_num, by norm_num, by norm_num⟩
  have hc : (0 : ℝ) ≤ c := c.coe_nonneg
  refine (hD.add hO hpq).mono (max_le ?_ ?_) (max_le ?_ ?_) <;> rw [← NNReal.coe_le_coe] <;>
    push_cast <;> nlinarith [mul_nonneg hc (NNReal.coe_nonneg (specNorm A).toNNReal)]

/-- The exponent of the sub-exponential tail of the centred form against the Hanson–Wright
exponent. -/
private lemma hansonWrightConstant_mul_min_le (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    hansonWrightConstant * min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)) ≤
      min (t ^ 2 / (2 * ((98 * c ^ 2 * (frobNorm A).toNNReal ^ 2 : ℝ≥0) : ℝ)))
        (t / (2 * ((28 * c * (specNorm A).toNNReal : ℝ≥0) : ℝ))) := by
  rw [hansonWrightConstant_def]
  push_cast
  rw [Real.coe_toNNReal _ (frobNorm_nonneg A), Real.coe_toNNReal _ (specNorm_nonneg A)]
  have hb : 0 ≤ t / (c * specNorm A) := div_nonneg ht (mul_nonneg c.coe_nonneg (specNorm_nonneg A))
  have h1 : t ^ 2 / (2 * (98 * c ^ 2 * frobNorm A ^ 2)) =
      1 / 196 * (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) := by
    ring
  have h2 : t / (2 * (28 * c * specNorm A)) = 1 / 56 * (t / (c * specNorm A)) := by
    ring
  rw [h1, h2]
  refine le_min ?_ ?_
  · exact mul_le_mul_of_nonneg_left (min_le_left _ _) (by norm_num)
  · calc 1 / 196 * min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A))
        ≤ 1 / 196 * (t / (c * specNorm A)) :=
          mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)
      _ ≤ 1 / 56 * (t / (c * specNorm A)) := by nlinarith

/-- The upper tail of a quadratic form in independent sub-Gaussian coordinates: if the
coordinates $\mathbf{x}_i$ of a real random vector $\mathbf{x}$ are independent and each is
sub-Gaussian with variance proxy $c$ ($\mathbb{E}\, e^{s \mathbf{x}_i} \le e^{c s^2 / 2}$ for every
real $s$, `HasSubgaussianMGF`), then for every real square matrix $\mathbf{A}$ and every
$t \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} -
\mathbb{E}\,\mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} \ge t\bigr]
\le \exp\Bigl(-\frac{1}{196} \min\Bigl(\frac{t^2}{c^2 \|\mathbf{A}\|_{\mathsf{F}}^2},
\frac{t}{c \|\mathbf{A}\|_2}\Bigr)\Bigr)\,.$$
A one-sided form of the Hanson–Wright inequality `measureReal_abs_quadForm_sub_integral_ge_le`;
the constant is `hansonWrightConstant`. -/
theorem measureReal_quadForm_sub_integral_ge_le (hind : iIndepFun (fun i ω => x ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ quadForm A (x ω) - ∫ ω', quadForm A (x ω') ∂μ} ≤
      rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) :=
  ((hasSubexponentialMGF_quadForm_sub_integral hind h A).measureReal_ge_le ht).trans
    (exp_le_exp.mpr (neg_le_neg (hansonWrightConstant_mul_min_le A ht)))

/-- The lower tail of a quadratic form in independent sub-Gaussian coordinates: if the
coordinates $\mathbf{x}_i$ of a real random vector $\mathbf{x}$ are independent and each is
sub-Gaussian with variance proxy $c$ ($\mathbb{E}\, e^{s \mathbf{x}_i} \le e^{c s^2 / 2}$ for every
real $s$, `HasSubgaussianMGF`), then for every real square matrix $\mathbf{A}$ and every
$t \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} -
\mathbb{E}\,\mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} \le -t\bigr]
\le \exp\Bigl(-\frac{1}{196} \min\Bigl(\frac{t^2}{c^2 \|\mathbf{A}\|_{\mathsf{F}}^2},
\frac{t}{c \|\mathbf{A}\|_2}\Bigr)\Bigr)\,.$$
A one-sided form of the Hanson–Wright inequality `measureReal_abs_quadForm_sub_integral_ge_le`;
the constant is `hansonWrightConstant`. -/
theorem measureReal_quadForm_sub_integral_le_le (hind : iIndepFun (fun i ω => x ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | quadForm A (x ω) - ∫ ω', quadForm A (x ω') ∂μ ≤ -t} ≤
      rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) :=
  ((hasSubexponentialMGF_quadForm_sub_integral hind h A).measureReal_le_le ht).trans
    (exp_le_exp.mpr (neg_le_neg (hansonWrightConstant_mul_min_le A ht)))

/-- **The Hanson–Wright inequality.** If the coordinates $\mathbf{x}_i$ of a real random vector
$\mathbf{x}$ are independent and each satisfies the sub-Gaussian moment generating function bound
with variance proxy $c$ (`HasSubgaussianMGF`), then for every real square matrix $\mathbf{A}$ and
every $t \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} -
\mathbb{E}\,\mathbf{x}^{\mathsf{T}}\mathbf{A}\mathbf{x} \rvert \ge t\bigr]
\le 2 \exp\Bigl(-\frac{1}{196} \min\Bigl(\frac{t^2}{c^2 \|\mathbf{A}\|_{\mathsf{F}}^2},
\frac{t}{c \|\mathbf{A}\|_2}\Bigr)\Bigr);$$
the explicit constant is `hansonWrightConstant`.
[Vershynin2018, Theorem 6.2.1]; there with an unspecified absolute constant and the sub-Gaussian
norm $K$ of the coordinates, $c$ playing the role of $K^2$.
Result: hanson-wright -/
theorem measureReal_abs_quadForm_sub_integral_ge_le (hind : iIndepFun (fun i ω => x ω i) μ)
    (h : ∀ i, HasSubgaussianMGF (fun ω => x ω i) c μ) (A : Matrix n n ℝ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ |quadForm A (x ω) - ∫ ω', quadForm A (x ω') ∂μ|} ≤
      2 * rexp (-(hansonWrightConstant *
        min (t ^ 2 / (c ^ 2 * frobNorm A ^ 2)) (t / (c * specNorm A)))) :=
  ((hasSubexponentialMGF_quadForm_sub_integral hind h A).measureReal_abs_ge_le ht).trans
    (mul_le_mul_of_nonneg_left
      (exp_le_exp.mpr (neg_le_neg (hansonWrightConstant_mul_min_le A ht))) zero_le_two)

end NLAlib
