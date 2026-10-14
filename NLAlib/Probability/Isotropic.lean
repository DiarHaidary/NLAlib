/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Integration
public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Law

/-!
# Isotropic random vectors

A random vector $\mathbf{x}$ in $\Bbbk^n$ (`x : Ω → n → 𝕜`) is isotropic when its coordinates are
square integrable and its second-moment matrix $\mathbb{E}[\mathbf{x}\mathbf{x}^{\mathsf{H}}]$ is
the identity. No mean is assumed and nothing is said about
$\mathbb{E}[\mathbf{x}\mathbf{x}^{\mathsf{T}}]$. Rademacher and standard Gaussian vectors are
isotropic, and so are $\sqrt{\lvert n \rvert}$ times a uniform point of the unit sphere and
$\sqrt{\lvert n \rvert}$ times a column of a Haar-distributed unitary matrix.

Isotropy is what trace estimation and the second moment of a sketch use: for isotropic
$\mathbf{x}$, $\mathbb{E}[\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}]
= \operatorname{tr}\mathbf{A}$ (Hutchinson) and
$\mathbb{E}\|\mathbf{A}\mathbf{x}\|^2 = \|\mathbf{A}\|_{\mathsf{F}}^2$. Fourth moments, which the
variance of these estimators needs, are separate hypotheses where they are used.

## Main definitions

* `NLAlib.IsIsotropic x μ`: $\mathbf{x}$ has square-integrable coordinates and
  $\mathbb{E}[\mathbf{x}\mathbf{x}^{\mathsf{H}}] = \mathbf{I}$.

## Main results

* `NLAlib.IsIsotropic.integral_quadForm`: Hutchinson's identity
  $\mathbb{E}[\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}] = \operatorname{tr}\mathbf{A}$.
* `NLAlib.IsIsotropic.integral_norm_mulVec_sq`:
  $\mathbb{E}\|\mathbf{A}\mathbf{x}\|^2 = \|\mathbf{A}\|_{\mathsf{F}}^2$.
* `NLAlib.IsIsotropic.integral_norm_mulVec_le`:
  $\mathbb{E}\|\mathbf{A}\mathbf{x}\| \le \|\mathbf{A}\|_{\mathsf{F}}$ under a probability measure.
* `NLAlib.IsIsotropic.integral_norm_dotProduct_sq`:
  $\mathbb{E}\lvert\mathbf{u}^{\mathsf{T}}\mathbf{x}\rvert^2 = \|\mathbf{u}\|^2$.
* `NLAlib.IsIsotropic.mulVec`: maps with orthonormal rows preserve isotropy.
* `NLAlib.IsIsotropic.of_iIndepFun`: independent coordinates with mean zero and unit second
  moment.
* `ProbabilityTheory.HasLaw.isIsotropic_iff`: isotropy depends only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [DecidableEq n] {x : Ω → n → 𝕜}

/-- A random vector $\mathbf{x}$ in $\Bbbk^n$ is isotropic for $\mu$ when its coordinates are
square integrable and its second-moment matrix is the identity:
$\int \mathbf{x}_i \overline{\mathbf{x}_j} \, d\mu = 1$ if $i = j$ and $0$ otherwise.
No mean is assumed and nothing is said about $\mathbb{E}[\mathbf{x}\mathbf{x}^{\mathsf{T}}]$. -/
structure IsIsotropic (x : Ω → n → 𝕜) (μ : Measure Ω) : Prop where
  /-- Each coordinate is square integrable. -/
  memLp : ∀ i, MemLp (fun ω => x ω i) 2 μ
  /-- The second-moment matrix $\mathbb{E}[\mathbf{x}\mathbf{x}^{\mathsf{H}}]$ is the identity. -/
  integral_mul_star : ∀ i j, ∫ ω, x ω i * star (x ω j) ∂μ = if i = j then 1 else 0

namespace IsIsotropic

/-- The products of two coordinates of an isotropic vector are integrable. -/
theorem integrable_mul_star (hx : IsIsotropic x μ) (i j : n) :
    Integrable (fun ω => x ω i * star (x ω j)) μ :=
  (hx.memLp i).integrable_mul (hx.memLp j).star

variable [Fintype n]

omit [DecidableEq n] in
private theorem quadForm_eq_sum_mul_star (A : Matrix n n 𝕜) (x : n → 𝕜) :
    quadForm A x = ∑ i, ∑ j, A i j * (x j * star (x i)) := by
  rw [quadForm_eq_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The quadratic form of an isotropic vector is integrable. -/
theorem integrable_quadForm (hx : IsIsotropic x μ) (A : Matrix n n 𝕜) :
    Integrable (fun ω => quadForm A (x ω)) μ := by
  simp only [quadForm_eq_sum_mul_star]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hx.integrable_mul_star j i).const_mul (A i j)

/-- **Hutchinson's identity**: for an isotropic probe $\mathbf{x}$, the quadratic form
$\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}$ is an unbiased estimator of
$\operatorname{tr}\mathbf{A}$: $\mathbb{E}[\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}]
= \operatorname{tr}\mathbf{A}$.
Result: hutchinson-trace-estimator -/
theorem integral_quadForm (hx : IsIsotropic x μ) (A : Matrix n n 𝕜) :
    ∫ ω, quadForm A (x ω) ∂μ = A.trace := by
  have h (i : n) : ∫ ω, ∑ j, A i j * (x ω j * star (x ω i)) ∂μ = A i i := by
    rw [integral_finsetSum _ fun j _ => (hx.integrable_mul_star j i).const_mul (A i j)]
    simp only [integral_const_mul, hx.integral_mul_star, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [quadForm_eq_sum_mul_star]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hx.integrable_mul_star j i).const_mul (A i j)]
  simp only [h, Matrix.trace, Matrix.diag]

/-- The squared Euclidean norm $\|\mathbf{A}\mathbf{x}\|^2$ is integrable for an isotropic
$\mathbf{x}$. -/
theorem integrable_norm_mulVec_sq (hx : IsIsotropic x μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ x ω)‖ ^ 2) μ := by
  have h := (hx.integrable_quadForm (Aᴴ * A)).re
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re] at h
  exact h

/-- $\mathbb{E}\|\mathbf{A}\mathbf{x}\|^2 = \|\mathbf{A}\|_{\mathsf{F}}^2$ for an isotropic
$\mathbf{x}$ and any rectangular $\mathbf{A}$. -/
theorem integral_norm_mulVec_sq (hx : IsIsotropic x μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : ∫ ω, ‖WithLp.toLp 2 (A *ᵥ x ω)‖ ^ 2 ∂μ = frobNorm A ^ 2 := by
  have h := integral_re (hx.integrable_quadForm (Aᴴ * A))
  rw [hx.integral_quadForm] at h
  simp only [quadForm_conjTranspose_mul_self, RCLike.ofReal_re] at h
  rw [h, frobNorm_sq_eq_re_trace]

/-- $\mathbb{E}\lvert\mathbf{u}^{\mathsf{T}}\mathbf{x}\rvert^2 = \|\mathbf{u}\|^2$ for an isotropic
$\mathbf{x}$, with the bilinear (unconjugated) pairing `u ⬝ᵥ x`: the second moment behind the
Johnson–Lindenstrauss lemma. Over $\mathbb{R}$ the absolute value can be dropped, by
`Real.norm_eq_abs` and `sq_abs`. -/
theorem integral_norm_dotProduct_sq (hx : IsIsotropic x μ) (u : n → 𝕜) :
    ∫ ω, ‖u ⬝ᵥ x ω‖ ^ 2 ∂μ = ‖WithLp.toLp 2 u‖ ^ 2 := by
  have key (v : n → 𝕜) :
      ‖u ⬝ᵥ v‖ ^ 2 = RCLike.re (quadForm (Matrix.vecMulVec (star u) u) v) := by
    have h := quadForm_vecMulVec_star (star u) v
    rw [star_star] at h
    rw [h, RCLike.ofReal_re]
  simp only [key]
  rw [integral_re (hx.integrable_quadForm _), hx.integral_quadForm, Matrix.trace_vecMulVec,
    EuclideanSpace.norm_toLp_sq_eq_re_star_dotProduct]

/-- The mean squared Euclidean norm of an isotropic vector is the dimension:
$\mathbb{E}\|\mathbf{x}\|^2 = \lvert n \rvert$. -/
theorem integral_norm_sq (hx : IsIsotropic x μ) :
    ∫ ω, ‖WithLp.toLp 2 (x ω)‖ ^ 2 ∂μ = Fintype.card n := by
  have key (v : n → 𝕜) : ‖WithLp.toLp 2 v‖ ^ 2 = RCLike.re (quadForm 1 v) := by
    rw [quadForm_one, RCLike.ofReal_re]
  simp only [key]
  rw [integral_re (hx.integrable_quadForm _), hx.integral_quadForm, Matrix.trace_one,
    RCLike.natCast_re]

/-- The Euclidean norm $\|\mathbf{A}\mathbf{x}\|$ is square integrable for an isotropic
$\mathbf{x}$. -/
private theorem memLp_norm_mulVec (hx : IsIsotropic x μ) {m : Type*} [Fintype m]
    (A : Matrix m n 𝕜) : MemLp (fun ω => ‖WithLp.toLp 2 (A *ᵥ x ω)‖) 2 μ := by
  have hsq := hx.integrable_norm_mulVec_sq A
  have hf : (fun ω => ‖WithLp.toLp 2 (A *ᵥ x ω)‖) =
      fun ω => √(‖WithLp.toLp 2 (A *ᵥ x ω)‖ ^ 2) := by
    funext ω
    rw [Real.sqrt_sq (norm_nonneg _)]
  have hm : AEStronglyMeasurable (fun ω => ‖WithLp.toLp 2 (A *ᵥ x ω)‖) μ := by
    rw [hf]
    exact Real.continuous_sqrt.comp_aestronglyMeasurable hsq.aestronglyMeasurable
  exact (memLp_two_iff_integrable_sq hm).2 hsq

/-- The Euclidean norm $\|\mathbf{A}\mathbf{x}\|$ is integrable for an isotropic $\mathbf{x}$ under
a probability measure. -/
theorem integrable_norm_mulVec [IsProbabilityMeasure μ] (hx : IsIsotropic x μ) {m : Type*}
    [Fintype m] (A : Matrix m n 𝕜) : Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ x ω)‖) μ :=
  (hx.memLp_norm_mulVec A).integrable one_le_two

/-- $\mathbb{E}\|\mathbf{A}\mathbf{x}\| \le \|\mathbf{A}\|_{\mathsf{F}}$ for an isotropic
$\mathbf{x}$ under a probability measure, by Jensen and
`NLAlib.IsIsotropic.integral_norm_mulVec_sq`; with $\mathbf{A} = \mathbf{I}$,
$\mathbb{E}\|\mathbf{x}\| \le \sqrt{\lvert n \rvert}$ (`frobNorm_one_sq`).
The probability hypothesis is needed: isotropy does not imply it, and Jensen's step
$\mathbb{E}\lvert Y\rvert \le (\mathbb{E}\lvert Y\rvert^2)^{1/2}$ fails on a measure of mass
greater than $1$. -/
theorem integral_norm_mulVec_le [IsProbabilityMeasure μ] (hx : IsIsotropic x μ) {m : Type*}
    [Fintype m] (A : Matrix m n 𝕜) : ∫ ω, ‖WithLp.toLp 2 (A *ᵥ x ω)‖ ∂μ ≤ frobNorm A := by
  set f : Ω → ℝ := fun ω => ‖WithLp.toLp 2 (A *ᵥ x ω)‖ with hf_def
  set c : ℝ := ∫ ω, f ω ∂μ with hc_def
  have hf : Integrable f μ := hx.integrable_norm_mulVec A
  have hsq : Integrable (fun ω => f ω ^ 2) μ := hx.integrable_norm_mulVec_sq A
  have hsq_int : ∫ ω, f ω ^ 2 ∂μ = frobNorm A ^ 2 := hx.integral_norm_mulVec_sq A
  have hexp : ∫ ω, (f ω - c) ^ 2 ∂μ = frobNorm A ^ 2 - c ^ 2 := by
    have e (ω : Ω) : (f ω - c) ^ 2 = f ω ^ 2 - 2 * c * f ω + c ^ 2 := by ring
    simp only [e]
    have h1 : Integrable (fun ω => f ω ^ 2 - 2 * c * f ω) μ := hsq.sub (hf.const_mul _)
    rw [integral_add h1 (integrable_const _), integral_sub hsq (hf.const_mul _),
      integral_const_mul, integral_const, probReal_univ,
      hsq_int, ← hc_def, smul_eq_mul, one_mul]
    ring
  have h0 : 0 ≤ frobNorm A ^ 2 - c ^ 2 := hexp ▸ integral_nonneg fun ω => sq_nonneg _
  have hc0 : 0 ≤ c := integral_nonneg fun ω => norm_nonneg _
  exact (pow_le_pow_iff_left₀ hc0 (frobNorm_nonneg A) two_ne_zero).1 (by linarith)

omit [DecidableEq n] in
private theorem mulVec_mul_star_mulVec {m : Type*} (U : Matrix m n 𝕜) (x : n → 𝕜) (i j : m) :
    (U *ᵥ x) i * star ((U *ᵥ x) j) = ∑ k, ∑ l, U i k * star (U j l) * (x k * star (x l)) := by
  simp only [Matrix.mulVec, dotProduct, star_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [star_mul']
  ring

/-- A map with orthonormal rows preserves isotropy: if $\mathbf{U}\mathbf{U}^{\mathsf{H}}
= \mathbf{I}$ (that is, `HasOrthonormalCols Uᴴ`), then $\mathbf{U}\mathbf{x}$ is isotropic.
Rotations of isotropic vectors, the rows of a randomized Hadamard transform and rescaled columns
of a Haar frame get their isotropy this way. -/
theorem mulVec (hx : IsIsotropic x μ) {m : Type*} [DecidableEq m]
    {U : Matrix m n 𝕜} (hU : HasOrthonormalCols Uᴴ) : IsIsotropic (fun ω => U *ᵥ x ω) μ := by
  have hU' : U * Uᴴ = 1 := by
    simpa only [Matrix.conjTranspose_conjTranspose] using hU.conjTranspose_mul_self
  refine ⟨fun i => ?_, fun i j => ?_⟩
  · simp only [Matrix.mulVec, dotProduct]
    exact memLp_finsetSum _ fun k _ => (hx.memLp k).const_mul (U i k)
  have h (k : n) : ∫ ω, ∑ l, U i k * star (U j l) * (x ω k * star (x ω l)) ∂μ =
      U i k * star (U j k) := by
    rw [integral_finsetSum _ fun l _ => (hx.integrable_mul_star k l).const_mul _]
    simp only [integral_const_mul, hx.integral_mul_star, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  have hij := congrFun (congrFun hU' i) j
  rw [Matrix.one_apply, Matrix.mul_apply] at hij
  simp only [mulVec_mul_star_mulVec]
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ =>
    (hx.integrable_mul_star k l).const_mul _, ← hij]
  simp only [h, Matrix.conjTranspose_apply]

omit [Fintype n] in
/-- Independent coordinates with mean zero and unit second moment form an isotropic vector: if the
$\mathbf{x}_i$ are independent and square integrable with $\mathbb{E}[\mathbf{x}_i] = 0$ and
$\mathbb{E}\lvert\mathbf{x}_i\rvert^2 = 1$, then $\mathbf{x}$ is isotropic. -/
theorem of_iIndepFun (hind : iIndepFun (fun i ω => x ω i) μ)
    (hL2 : ∀ i, MemLp (fun ω => x ω i) 2 μ) (hmean : ∀ i, ∫ ω, x ω i ∂μ = 0)
    (hvar : ∀ i, ∫ ω, ‖x ω i‖ ^ 2 ∂μ = 1) : IsIsotropic x μ := by
  refine ⟨hL2, fun i j => ?_⟩
  split_ifs with h
  · subst h
    have key (ω : Ω) : x ω i * star (x ω i) = ((‖x ω i‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.star_def, RCLike.mul_conj, RCLike.ofReal_pow]
    simp only [key]
    rw [integral_ofReal, hvar, RCLike.ofReal_one]
  · have hij := (hind.indepFun h).comp measurable_id continuous_star.measurable
    have hint := hij.integral_fun_mul_eq_mul_integral (hL2 i).1 (hL2 j).1.star
    simp only [Function.comp_apply, id_eq] at hint
    rw [hint, hmean, zero_mul]

end IsIsotropic

/-- Isotropy depends only on the law: a random vector with law $\nu$ is isotropic exactly when the
identity is isotropic for $\nu$. -/
theorem _root_.ProbabilityTheory.HasLaw.isIsotropic_iff {ν : Measure (n → 𝕜)}
    (hx : HasLaw x ν μ) : IsIsotropic x μ ↔ IsIsotropic id ν := by
  have hm (i : n) : Measurable fun v : n → 𝕜 => v i := measurable_pi_apply i
  have hint (i j : n) : ∫ ω, x ω i * star (x ω j) ∂μ = ∫ v, v i * star (v j) ∂ν :=
    hx.integral_comp ((hm i).mul (continuous_star.measurable.comp (hm j))).aestronglyMeasurable
  have hmem (i : n) : MemLp (fun ω => x ω i) 2 μ ↔ MemLp (fun v : n → 𝕜 => v i) 2 ν :=
    hx.memLp_comp_iff (hm i).aestronglyMeasurable
  constructor
  · intro h
    exact ⟨fun i => (hmem i).1 (h.memLp i),
      fun i j => (hint i j).symm.trans (h.integral_mul_star i j)⟩
  · intro h
    exact ⟨fun i => (hmem i).2 (h.memLp i),
      fun i j => (hint i j).trans (h.integral_mul_star i j)⟩

end NLAlib
