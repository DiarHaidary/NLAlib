/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.Probability.Tail
public import NLAlib.Regression.Embedding
public import NLAlib.Regression.Oblique
public import NLAlib.Sketching.Properties.MatrixMultiplication
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Tail bounds from a subspace injection

The two probabilistic consequences of an oblivious subspace injection in
[CamanoEpperlyMeyerTropp2025]: *OSIs respect orthogonality* (their Lemma 2.1), the step behind
the randomized range finder, Nyström and generalized Nyström bounds; and *sketch-and-solve with an
OSI* (their Theorem 2.7), for a vector and for a matrix right-hand side. Each is stated for a
random subspace injection of a fixed subspace together with isotropy, and again for an OSI.
Sketch-and-solve is also stated for a random design independent of an OSI (the completion step
of generalized Nyström with a structured co-range sketch), and to relative error through the
JL moment property and approximate multiplication [Woodruff2014, Theorem 23], for a fixed and a
random design.

Each event is the negation of the guarantee ($\{c < X\}$ for $X \le c$), so the degenerate cases
$\mathbf{B}\mathbf{Z}^{\mathsf{H}} = \mathbf{0}$,
$(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y} = \mathbf{0}$ need no hypothesis. The proofs
combine the deterministic bounds of `NLAlib.Regression.Embedding` with Markov's
inequality for $\mathbb{E}\|\mathbf{S}\mathbf{M}\|_{\mathsf{F}}^2 = \|\mathbf{M}\|_{\mathsf{F}}^2$
off the injection event (`NLAlib.measureReal_le_add_one_div`, in `NLAlib.Probability.Tail`).
Design: `docs/design/Sketching-S1.md` §3.4.

## Main results

* `NLAlib.HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le`,
  `NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le`: CEMT Lemma 2.1.
* `NLAlib.HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le`: sketch-and-solve, CEMT
  Theorem 2.7.
* `NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`: its matrix form.
* `NLAlib.IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_union_gt_le_of_indepFun`:
  the two events of these tails for a random design independent of an OSI.
* `NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun`
  is sketch-and-solve with a random design.
* `NLAlib.HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le`,
  `NLAlib.HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun`:
  sketch-and-solve to relative error through approximate multiplication.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k l n p q r : Type*} [Fintype k] [Fintype l] [Fintype n] [Fintype p] [Fintype q] [Fintype r]
  [DecidableEq n] {S : Ω → Matrix k n 𝕜} {Q : Matrix n p 𝕜} {A : Matrix n q 𝕜} {a δ t : ℝ}
  {d : ℕ}

/-! ### OSIs respect orthogonality -/

/-- **OSIs respect orthogonality**: if $\mathbf{S}$ is isotropic and a subspace injection for
$\operatorname{range}\mathbf{Q}$ with constant $a > 0$ and failure probability $\delta$,
$\mathbf{Q}$ with orthonormal columns, then for $t > 0$
$$\bigl\|\mathbf{B}(\mathbf{S}\mathbf{Z})^{\mathsf{H}}
((\mathbf{S}\mathbf{Q})^{\mathsf{H}})^{+}\bigr\|_{\mathsf{F}}^2
\le \frac{t \|\mathbf{B}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}}^2}{a}$$
except with probability $\delta + 1 / t$.
[CamanoEpperlyMeyerTropp2025, Lemma 2.1]; there $\mathbf{Q}^{\mathsf{H}}\mathbf{Z} = \mathbf{0}$
(unused here), $\mathbf{Z}$ with orthonormal columns and $t = 20$. -/
theorem HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le [IsFiniteMeasure μ]
    [DecidableEq p] (h : HasSubspaceInjection S Q a δ μ) (hiso : IsIsotropicSketch S μ)
    (hQ : HasOrthonormalCols Q) (ha : 0 < a) (ht : 0 < t) (B : Matrix l r 𝕜)
    (Z : Matrix n r 𝕜) :
    μ.real {ω | t * frobNorm (B * Zᴴ) ^ 2 / a <
      frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t := by
  have hm : ∫ ω, frobNorm (S ω * (Z * Bᴴ)) ^ 2 ∂μ = frobNorm (B * Zᴴ) ^ 2 := by
    rw [hiso.integral_frobNorm_mul_sq, ← frobNorm_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  refine measureReal_le_add_one_div (G := {ω | IsSubspaceInjection (S ω) Q a}) h
    (fun ω => sq_nonneg _) (hiso.integrable_frobNorm_mul_sq _) hm (fun h0 ω => ?_) ht
    (ae_of_all _ fun ω hω hE => ?_)
  · have hZB : Z * Bᴴ = 0 := by
      rw [← Matrix.conjTranspose_conjTranspose (Z * Bᴴ), Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose,
        frobNorm_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), Matrix.conjTranspose_zero]
    rw [hZB, Matrix.mul_zero, frobNorm_zero, sq, mul_zero]
  · have hdet := (hω : IsSubspaceInjection (S ω) Q a).frobNorm_mul_pinv_sq_le hQ ha
      (B * (S ω * Z)ᴴ)
    have e : frobNorm (B * (S ω * Z)ᴴ) = frobNorm (S ω * (Z * Bᴴ)) := by
      rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [e] at hdet
    have hE' : t * frobNorm (B * Zᴴ) ^ 2 / a <
        frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2 := hE
    exact (div_lt_div_iff_of_pos_right ha).1 (hE'.trans_le hdet)

/-- **OSIs respect orthogonality**, in CEMT's form: for an OSI for dimension $d \ge \lvert p \rvert$
with constant $a > 0$ and failure probability $\delta$, $\mathbf{Q}$ (with $p$ columns) and
$\mathbf{Z}$ with orthonormal columns, and $t > 0$,
$$\bigl\|\mathbf{B}(\mathbf{S}\mathbf{Z})^{\mathsf{H}}
((\mathbf{S}\mathbf{Q})^{\mathsf{H}})^{+}\bigr\|_{\mathsf{F}}^2
\le \frac{t \|\mathbf{B}\|_{\mathsf{F}}^2}{a}$$
except with probability $\delta + 1 / t$. [CamanoEpperlyMeyerTropp2025, Lemma 2.1]; there
$\mathbf{Q}^{\mathsf{H}}\mathbf{Z} = \mathbf{0}$ (unused here) and $t = 20$. -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le [IsFiniteMeasure μ]
    [DecidableEq p] [DecidableEq r] (h : IsObliviousSubspaceInjection S d a δ μ)
    (hQ : HasOrthonormalCols Q) (hpd : Fintype.card p ≤ d) {Z : Matrix n r 𝕜}
    (hZ : HasOrthonormalCols Z) (ha : 0 < a) (ht : 0 < t) (B : Matrix l r 𝕜) :
    μ.real {ω | t * frobNorm B ^ 2 / a <
      frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t := by
  have h' := (h.hasSubspaceInjection (hQ.rank_eq ▸ hpd)).measure_frobNorm_mul_pinv_sq_gt_le
    h.isotropic hQ ha ht B Z
  rwa [hZ.frobNorm_mul_conjTranspose_right] at h'

/-! ### Sketch-and-solve with an injection -/

/-- **Sketch-and-solve with an OSI**: if $\mathbf{S}$ is isotropic and a subspace injection for
$\operatorname{range}\mathbf{A}$ with constant $a > 0$ and failure probability $\delta$, and
$\mathbf{x}(\omega)$ is (almost surely) a minimizer of
$\|\mathbf{S}\mathbf{A}\mathbf{x} - \mathbf{S}\mathbf{y}\|$, then for $t > 0$
$$\|\mathbf{y} - \mathbf{A}\mathbf{x}\|^2
\le \Bigl(1 + \frac{t}{a}\Bigr) \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2$$
except with probability $\delta + 1 / t$. [CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there for an
OSI, the minimum-norm solution and a fixed $t$, here a tail in $t$ for every minimizer.
Result: sketch-and-solve-ls -/
theorem HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le [IsFiniteMeasure μ]
    (h : HasSubspaceInjection S A a δ μ) (hiso : IsIsotropicSketch S μ) (ha : 0 < a)
    (ht : 0 < t) (y : n → 𝕜) {x : Ω → q → 𝕜}
    (hx : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x ω)) :
    μ.real {ω | (1 + t / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2} ≤ δ + 1 / t := by
  set w := (1 - rangeProjector A) *ᵥ y
  refine measureReal_le_add_one_div (G := {ω | IsSubspaceInjection (S ω) A a}) h
    (fun ω => sq_nonneg _) (hiso.integrable_norm_mulVec_sq w) (hiso.integral_norm_mulVec_sq w)
    (fun h0 ω => ?_) ht (hx.mono fun ω hxω hω hE => ?_)
  · have hw : w = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.1 h0
      rwa [norm_eq_zero, WithLp.toLp_eq_zero] at this
    rw [hw, Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sq, mul_zero]
  · have hdet := (hω : IsSubspaceInjection (S ω) A a).norm_sub_mulVec_sq_le ha hxω
    have hE' : (1 + t / a) * ‖WithLp.toLp 2 w‖ ^ 2 < ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2 := hE
    have e : (1 + t / a) * ‖WithLp.toLp 2 w‖ ^ 2 =
        ‖WithLp.toLp 2 w‖ ^ 2 + t * ‖WithLp.toLp 2 w‖ ^ 2 / a := by ring
    refine (div_lt_div_iff_of_pos_right ha).1 ?_
    linarith

/-- **Sketch-and-solve with an OSI, matrix right-hand side**, for the minimum-norm output
$(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{Y}$: if $\mathbf{S}$ is isotropic and a subspace
injection for $\operatorname{range}\mathbf{A}$ with constant $a > 0$ and failure probability
$\delta$, then for $t > 0$
$$\|\mathbf{Y} - \mathbf{A}(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{t}{a}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{Y}\|_{\mathsf{F}}^2$$
except with probability $\delta + 1 / t$. [CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there a
vector right-hand side. -/
theorem HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le [IsFiniteMeasure μ]
    (h : HasSubspaceInjection S A a δ μ) (hiso : IsIsotropicSketch S μ) (ha : 0 < a)
    (ht : 0 < t) (Y : Matrix n r 𝕜) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector A) * Y) ^ 2 <
      frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2} ≤ δ + 1 / t := by
  set C := (1 - rangeProjector A) * Y
  refine measureReal_le_add_one_div (G := {ω | IsSubspaceInjection (S ω) A a}) h
    (fun ω => sq_nonneg _) (hiso.integrable_frobNorm_mul_sq C) (hiso.integral_frobNorm_mul_sq C)
    (fun h0 ω => ?_) ht (ae_of_all _ fun ω hω hE => ?_)
  · rw [frobNorm_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), Matrix.mul_zero,
      frobNorm_zero, sq, mul_zero]
  · have hdet := (hω : IsSubspaceInjection (S ω) A a).frobNorm_sub_mul_pinv_mul_sq_le ha Y
    have hE' : (1 + t / a) * frobNorm C ^ 2 <
        frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2 := hE
    have e : (1 + t / a) * frobNorm C ^ 2 = frobNorm C ^ 2 + t * frobNorm C ^ 2 / a := by ring
    refine (div_lt_div_iff_of_pos_right ha).1 ?_
    linarith

/-- **Sketch-and-solve with an OSI** for dimension $d \ge \operatorname{rank}\mathbf{A}$: the
bound of `NLAlib.HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.7]. -/
theorem IsObliviousSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le [IsFiniteMeasure μ]
    (h : IsObliviousSubspaceInjection S d a δ μ) (hA : A.rank ≤ d) (ha : 0 < a) (ht : 0 < t)
    (y : n → 𝕜) {x : Ω → q → 𝕜}
    (hx : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x ω)) :
    μ.real {ω | (1 + t / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2} ≤ δ + 1 / t := by
  exact (h.hasSubspaceInjection hA).measure_norm_sub_mulVec_sq_gt_le h.isotropic ha ht y hx

/-- **Sketch-and-solve with an OSI, matrix right-hand side**, for dimension
$d \ge \operatorname{rank}\mathbf{A}$: the bound of
`NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there a vector right-hand side. -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le
    [IsFiniteMeasure μ] (h : IsObliviousSubspaceInjection S d a δ μ) (hA : A.rank ≤ d)
    (ha : 0 < a) (ht : 0 < t) (Y : Matrix n r 𝕜) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector A) * Y) ^ 2 <
      frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2} ≤ δ + 1 / t := by
  exact (h.hasSubspaceInjection hA).measure_frobNorm_sub_mul_pinv_mul_sq_gt_le h.isotropic ha ht
    Y

/-! ### Sketch-and-solve with a random design -/

/-- **The two events of an OSI tail on a random design**: if $\mathbf{S}$ is an OSI for
dimension $d$ with constant $a$ and failure probability $\delta$, independent of a random design
$\mathbf{Y}$ of rank at most $d$ and a right-hand side $\mathbf{B}$, then for $t > 0$ the event
that $\mathbf{S}$ fails to inject $\operatorname{range}\mathbf{Y}$ or
$$\|\mathbf{S}(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{B}\|_{\mathsf{F}}^2 >
t\,\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{B}\|_{\mathsf{F}}^2$$
has probability at most $\delta + 1/t$. On its complement every deterministic bound of the
oblique projector under an injection applies, with the rank identity
`NLAlib.IsSubspaceInjection.rank_mul_eq`; sketch-and-solve with a random design
(`NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun`)
and late-truncated generalized Nyström use it so. The random-design form of the two events of
[CamanoEpperlyMeyerTropp2025, Lemma 2.1 and Theorem 2.7]. -/
theorem IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_union_gt_le_of_indepFun
    [IsProbabilityMeasure μ] (h : IsObliviousSubspaceInjection S d a δ μ) (ht : 0 < t)
    {Y : Ω → Matrix n q 𝕜} {B : Ω → Matrix n r 𝕜} (hind : IndepFun S (fun ω => (Y ω, B ω)) μ)
    (hS : AEMeasurable S μ) (hY : AEMeasurable Y μ) (hB : AEMeasurable B μ)
    (hrank : ∀ᵐ ω ∂μ, (Y ω).rank ≤ d) :
    μ.real ({ω | ¬ IsSubspaceInjection (S ω) (Y ω) a} ∪
      {ω | t * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 <
        frobNorm (S ω * ((1 - rangeProjector (Y ω)) * B ω)) ^ 2}) ≤ δ + 1 / t := by
  have hC : Measurable fun x : Matrix k n 𝕜 × (Matrix n q 𝕜 × Matrix n r 𝕜) =>
      (1 - rangeProjector x.2.1) * x.2.2 :=
    (measurable_const.sub (measurable_rangeProjector.comp measurable_snd.fst)).matrix_mul
      measurable_snd.snd
  have hI : MeasurableSet ((fun x : Matrix k n 𝕜 × (Matrix n q 𝕜 × Matrix n r 𝕜) =>
      (x.1, x.2.1)) ⁻¹' {x : Matrix k n 𝕜 × Matrix n q 𝕜 | IsSubspaceInjection x.1 x.2 a}ᶜ) :=
    (isClosed_setOf_isSubspaceInjection a).isOpen_compl.measurableSet.preimage
      (measurable_fst.prodMk measurable_snd.fst)
  have hM : MeasurableSet {x : Matrix k n 𝕜 × (Matrix n q 𝕜 × Matrix n r 𝕜) |
      t * frobNorm ((1 - rangeProjector x.2.1) * x.2.2) ^ 2 <
        frobNorm (x.1 * ((1 - rangeProjector x.2.1) * x.2.2)) ^ 2} :=
    measurableSet_lt (((measurable_frobNorm.comp hC).pow_const 2).const_mul t)
      ((measurable_frobNorm.comp (measurable_fst.matrix_mul hC)).pow_const 2)
  have hG : MeasurableSet {y : Matrix n q 𝕜 × Matrix n r 𝕜 | y.1.rank ≤ d} :=
    (isClosed_setOf_rank_le d).measurableSet.preimage measurable_fst
  have hδ : 0 ≤ δ := measureReal_nonneg.trans (h.injection 0 (by simp))
  have h' := hind.measureReal_mem_le_add hS (hY.prodMk hB) (hI.union hM) hG
    (δ₁ := δ + 1 / t) (add_nonneg hδ (by positivity)) (fun y (hy : y.1.rank ≤ d) => ?_)
    (δ₂ := 0) ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 (ae_iff.1 hrank)).le
  · rw [add_zero] at h'
    exact h'
  · set C := (1 - rangeProjector y.1) * y.2
    refine measureReal_le_add_one_div (G := {ω | IsSubspaceInjection (S ω) y.1 a})
      (h.hasSubspaceInjection hy) (fun ω => sq_nonneg _)
      (h.isotropic.integrable_frobNorm_mul_sq C) (h.isotropic.integral_frobNorm_mul_sq C)
      (fun h0 ω => ?_) ht (ae_of_all _ fun ω hω hEω => ?_)
    · rw [frobNorm_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), Matrix.mul_zero,
        frobNorm_zero, sq, mul_zero]
    · rcases hEω with hEω | hEω
      · exact absurd hω hEω
      · exact hEω

/-- **Sketch-and-solve with an OSI and a random design**: if $\mathbf{S}$ is an OSI for dimension
$d$ with constant $a > 0$ and failure probability $\delta$, independent of a random design
$\mathbf{Y}$ of rank at most $d$ and a right-hand side $\mathbf{B}$, then for $t > 0$
$$\|\mathbf{B} - \mathbf{Y}\,\mathsf{sketchAndSolve}(\mathbf{Y}, \mathbf{S}, \mathbf{B})
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{t}{a}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{B}\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. The fixed-design form is
`NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`. It is the
completion step of generalized Nyström and of its early-truncated form with a structured co-range
sketch. [CamanoEpperlyMeyerTropp2025, Theorem 2.7 and proof of Corollary 2.8]; there a fixed
design, a vector right-hand side and probability $9/10$.
Result: sketch-and-solve-ls -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun
    [IsProbabilityMeasure μ] (h : IsObliviousSubspaceInjection S d a δ μ) (ha : 0 < a)
    (ht : 0 < t) {Y : Ω → Matrix n q 𝕜} {B : Ω → Matrix n r 𝕜}
    (hind : IndepFun S (fun ω => (Y ω, B ω)) μ) (hS : AEMeasurable S μ) (hY : AEMeasurable Y μ)
    (hB : AEMeasurable B μ) (hrank : ∀ᵐ ω ∂μ, (Y ω).rank ≤ d) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 <
      frobNorm (B ω - Y ω * sketchAndSolve (Y ω) (S ω) (B ω)) ^ 2} ≤ δ + 1 / t := by
  refine (measureReal_mono fun ω hω => ?_).trans
    (h.measure_not_isSubspaceInjection_union_gt_le_of_indepFun ht hind hS hY hB hrank)
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_lt] at hc
  have hdet := hc.1.frobNorm_sub_mul_pinv_mul_sq_le ha (B ω)
  have hω' : (1 + t / a) * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 <
      frobNorm (B ω - Y ω * (pinv (S ω * Y ω) * (S ω * B ω))) ^ 2 := hω
  have hdiv := div_le_div_of_nonneg_right hc.2 ha.le
  have e : (1 + t / a) * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 =
      frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 +
        t * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 / a := by ring
  linarith

/-! ### Sketch-and-solve to relative error through approximate multiplication -/

section JLMoment

variable {S : Ω → Matrix k n ℝ}

/-- **Sketch-and-solve to relative error through approximate multiplication**: if the real
sketch $\mathbf{S}$ injects $\operatorname{range}\mathbf{A}$ with constant $a > 0$ except with
probability $\delta$ and has the $(\varepsilon, \delta', p)$ JL moment property, $\varepsilon > 0$,
$p \ge 2$, $\delta' \ge 0$, then
$$\|\mathbf{B} - \mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{\operatorname{rank}(\mathbf{A})\,\varepsilon^2}{a^2}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. Its neighbour without the moment property,
`NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`, has the constant factor
$1 + t/a$ at failure probability $\delta + 1/t$; this one reaches $1 + \varepsilon$ when the
moment's $\delta'$ decays with the sketch size. [Woodruff2014, Theorem 23]; there sparse
embeddings, a vector right-hand side and the unsquared objective; here any injection and JL
moment, a matrix right-hand side.
Result: sketch-and-solve-ls -/
theorem HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le [IsFiniteMeasure μ]
    {A : Matrix n q ℝ} {ε δ' p : ℝ} (hJL : HasJLMoment S ε δ' p μ)
    (h : HasSubspaceInjection S A a δ μ) (hS : AEMeasurable S μ) (ha : 0 < a) (hε : 0 < ε)
    (hp : 2 ≤ p) (hδ' : 0 ≤ δ') (B : Matrix n r ℝ) :
    μ.real {ω | (1 + (A.rank : ℝ) * ε ^ 2 / a ^ 2) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ + δ' := by
  set P := rangeProjector A with hPdef
  set C := (1 - P) * B with hCdef
  have hPC0 : P * C = 0 := by
    rw [hCdef, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPdef,
      rangeProjector_mul_rangeProjector, sub_self, Matrix.zero_mul]
  have hdet : ∀ ω, IsSubspaceInjection (S ω) A a →
      frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 ≤
        frobNorm C ^ 2 + (frobNorm (Pᴴ * (S ω)ᴴ * S ω * C - Pᴴ * C) / a) ^ 2 := by
    intro ω hω
    have e1 : B - A * sketchAndSolve A (S ω) B = (1 - obliqueProjector A (S ω)) * B := by
      rw [mul_sketchAndSolve, Matrix.sub_mul, Matrix.one_mul]
    have hL1 := hω.matrixNorm_obliqueProjector_mul_le ha (lpGauge 2 one_le_two) C
    rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at hL1
    have e2 : Pᴴ * (S ω)ᴴ * S ω * C - Pᴴ * C = rangeProjector A * (S ω)ᴴ * S ω * C := by
      rw [hPdef, conjTranspose_rangeProjector, ← hPdef, hPC0, sub_zero]
    rw [e1, frobNorm_one_sub_obliqueProjector_mul_sq (hω.rank_mul_eq ha), e2]
    gcongr
  unfold HasSubspaceInjection at h
  by_cases hPC : P = 0 ∨ C = 0
  · have hz : ∀ ω, Pᴴ * (S ω)ᴴ * S ω * C - Pᴴ * C = 0 := by
      intro ω
      rcases hPC with h0 | h0 <;> simp [h0]
    refine (measureReal_mono fun ω hω => ?_).trans (h.trans (le_add_of_nonneg_right hδ'))
    intro hinj
    have h1 := hdet ω hinj
    rw [hz ω, frobNorm_zero, zero_div, sq (0 : ℝ), mul_zero, add_zero] at h1
    have hω' : (1 + (A.rank : ℝ) * ε ^ 2 / a ^ 2) * frobNorm C ^ 2 <
        frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 := hω
    have : frobNorm C ^ 2 ≤ (1 + (A.rank : ℝ) * ε ^ 2 / a ^ 2) * frobNorm C ^ 2 :=
      le_mul_of_one_le_left (sq_nonneg _) (le_add_of_nonneg_right (by positivity))
    linarith
  · rw [not_or] at hPC
    have hF := hJL.measure_frobNorm_conjTranspose_mul_sub_ge_le hε hp hS hPC.1 hPC.2
    refine (measureReal_mono (s₂ := {ω | ¬ IsSubspaceInjection (S ω) A a} ∪
      {ω | ε * frobNorm P * frobNorm C ≤ frobNorm (Pᴴ * (S ω)ᴴ * S ω * C - Pᴴ * C)})
      fun ω hω => ?_).trans ((measureReal_union_le _ _).trans (add_le_add h hF))
    by_contra hc
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_le] at hc
    have h1 := hdet ω hc.1
    have hω' : (1 + (A.rank : ℝ) * ε ^ 2 / a ^ 2) * frobNorm C ^ 2 <
        frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 := hω
    have hx0 := frobNorm_nonneg (Pᴴ * (S ω)ᴴ * S ω * C - Pᴴ * C)
    have hsq : (frobNorm (Pᴴ * (S ω)ᴴ * S ω * C - Pᴴ * C) / a) ^ 2 ≤
        (ε * frobNorm P * frobNorm C / a) ^ 2 := by
      gcongr
      exact hc.2.le
    have hP2 : frobNorm P ^ 2 = A.rank := frobNorm_rangeProjector_sq A
    have e : (ε * frobNorm P * frobNorm C / a) ^ 2 =
        (A.rank : ℝ) * ε ^ 2 / a ^ 2 * frobNorm C ^ 2 := by
      rw [div_pow, mul_pow, mul_pow, hP2]
      ring
    nlinarith

/-- **Sketch-and-solve to relative error with a random design**: for a real OSI $\mathbf{S}$ for
dimension $d$ (constant $a > 0$, failure probability $\delta$) with the $(\varepsilon, \delta', p)$
JL moment property, $\varepsilon > 0$, $p \ge 2$, $\delta' \ge 0$, independent of a random design
$\mathbf{Y}$ of rank at most $d$ and a right-hand side $\mathbf{B}$,
$$\|\mathbf{B} - \mathbf{Y}\,\mathsf{sketchAndSolve}(\mathbf{Y}, \mathbf{S}, \mathbf{B})
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{d\,\varepsilon^2}{a^2}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{Y}})\mathbf{B}\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta'$. The random-design form of
`NLAlib.HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le`; its constant-factor
neighbour is
`NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun`.
[Woodruff2014, Theorem 23, and proof of Theorem 47]; there a fixed design.
Result: sketch-and-solve-ls -/
theorem HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_indepFun
    [IsProbabilityMeasure μ] {ε δ' p : ℝ} (hJL : HasJLMoment S ε δ' p μ)
    (h : IsObliviousSubspaceInjection S d a δ μ) (ha : 0 < a) (hε : 0 < ε) (hp : 2 ≤ p)
    (hδ' : 0 ≤ δ') {Y : Ω → Matrix n q ℝ} {B : Ω → Matrix n r ℝ}
    (hind : IndepFun S (fun ω => (Y ω, B ω)) μ) (hS : AEMeasurable S μ)
    (hY : AEMeasurable Y μ) (hB : AEMeasurable B μ) (hrank : ∀ᵐ ω ∂μ, (Y ω).rank ≤ d) :
    μ.real {ω | (1 + (d : ℝ) * ε ^ 2 / a ^ 2) * frobNorm ((1 - rangeProjector (Y ω)) * B ω) ^ 2 <
      frobNorm (B ω - Y ω * sketchAndSolve (Y ω) (S ω) (B ω)) ^ 2} ≤ δ + δ' := by
  have hC : Measurable fun x : Matrix k n ℝ × (Matrix n q ℝ × Matrix n r ℝ) =>
      (1 - rangeProjector x.2.1) * x.2.2 :=
    (measurable_const.sub (measurable_rangeProjector.comp measurable_snd.fst)).matrix_mul
      measurable_snd.snd
  have hsas : Measurable fun x : Matrix k n ℝ × (Matrix n q ℝ × Matrix n r ℝ) =>
      x.2.2 - x.2.1 * sketchAndSolve x.2.1 x.1 x.2.2 := by
    unfold sketchAndSolve
    exact measurable_snd.snd.sub (measurable_snd.fst.matrix_mul
      ((measurable_pinv.comp (measurable_fst.matrix_mul measurable_snd.fst)).matrix_mul
        (measurable_fst.matrix_mul measurable_snd.snd)))
  have hE : MeasurableSet {x : Matrix k n ℝ × (Matrix n q ℝ × Matrix n r ℝ) |
      (1 + (d : ℝ) * ε ^ 2 / a ^ 2) * frobNorm ((1 - rangeProjector x.2.1) * x.2.2) ^ 2 <
        frobNorm (x.2.2 - x.2.1 * sketchAndSolve x.2.1 x.1 x.2.2) ^ 2} :=
    measurableSet_lt (((measurable_frobNorm.comp hC).pow_const 2).const_mul _)
      ((measurable_frobNorm.comp hsas).pow_const 2)
  have hG : MeasurableSet {y : Matrix n q ℝ × Matrix n r ℝ | y.1.rank ≤ d} :=
    (isClosed_setOf_rank_le d).measurableSet.preimage measurable_fst
  have hδ : 0 ≤ δ := measureReal_nonneg.trans (h.injection 0 (by simp))
  have h' := hind.measureReal_mem_le_add hS (hY.prodMk hB) hE hG (add_nonneg hδ hδ')
    (fun y (hy : y.1.rank ≤ d) => ?_) (δ₂ := 0)
    ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 (ae_iff.1 hrank)).le
  · rw [add_zero] at h'
    exact h'
  · refine (measureReal_mono fun ω hω => ?_).trans
      (hJL.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le (h.hasSubspaceInjection hy) hS ha
        hε hp hδ' y.2)
    refine lt_of_le_of_lt ?_ (show (1 + (d : ℝ) * ε ^ 2 / a ^ 2) *
      frobNorm ((1 - rangeProjector y.1) * y.2) ^ 2 <
        frobNorm (y.2 - y.1 * sketchAndSolve y.1 (S ω) y.2) ^ 2 from hω)
    gcongr

end JLMoment

end NLAlib
