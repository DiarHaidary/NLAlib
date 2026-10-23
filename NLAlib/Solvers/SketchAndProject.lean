/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.ForMathlib.Probability.Independence.InfinitePi
public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import NLAlib.Probability.Law
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.Probability.Measurability.Matrix

/-!
# Sketch-and-project

`NLAlib.sketchAndProject A S b x` is the point nearest $\mathbf{x}$ among the least-squares
solutions of the sketched system $\mathbf{S}\mathbf{A}\mathbf{y} = \mathbf{S}\mathbf{b}$,
$\mathbf{x} + (\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{b} - \mathbf{A}\mathbf{x})$, and
`NLAlib.sketchAndProjectIterate A S b x₀ q` iterates it with a sequence of sketches
$\mathbf{S}_0, \mathbf{S}_1, \ldots$. The correction
$(\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{b} - \mathbf{A}\mathbf{x})$ is the vector
sketch-and-solve correction for the current residual. Randomized Kaczmarz is the instance with
single-row selection sketches (`NLAlib.kaczmarzIterate`); block Kaczmarz, Gaussian
sketch-and-project and coordinate methods are others.

Every step moves the iterate within the row space of $\mathbf{A}$ and, for a consistent system,
never increases the error. With independent sketches drawn from a law $\nu$, written as the
i.i.d.-sequence hypothesis `HasLaw S (iidSequence ν) μ`, the expected
squared error contracts by the expected projector
$\mathbb{E}_{\nu}[(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}]$ (Gower and Richtárik's
$\mathbb{E}[\mathbf{Z}]$ in the Euclidean metric), and its least eigenvalue on the row space of
$\mathbf{A}$ is the rate. No rank assumption is needed. Matrix-valued integrals are taken under
`open scoped Matrix.Norms.L2Operator`. [GowerRichtarik2015].
Design: `docs/design/Regression-Kaczmarz.md`.

## Main definitions

* `NLAlib.sketchAndProject`: one sketch-and-project step.
* `NLAlib.sketchAndProjectIterate`: the iterate for a sequence of sketches.

## Main results

* `NLAlib.isLeastSquaresSolution_sketchAndProject`,
  `NLAlib.norm_sub_sketchAndProject_le_of_isLeastSquaresSolution`: the step is the nearest
  sketched least-squares solution.
* `NLAlib.norm_sub_sketchAndProject_sq`: Pythagoras for one step.
* `NLAlib.sketchAndProjectIterate_sub_mem_range`, `NLAlib.norm_sub_sketchAndProjectIterate_le`:
  row-space invariance and monotonicity.
* `NLAlib.integral_sub_sketchAndProjectIterate_of_hasLaw_iidSequence`: the mean error.
* `NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_of_hasLaw_iidSequence`: linear
  convergence in expectation.
* `NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_hasLaw_iidSequence_of_log_div_le`:
  the iteration count, with its asymptotic form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k m n : Type*} [Fintype k] [Fintype m] [Fintype n]

/-! ### The step and the iterate -/

/-- The **sketch-and-project step** for $\mathbf{A} \in \Bbbk^{m \times n}$, a sketch
$\mathbf{S} \in \Bbbk^{k \times m}$, $\mathbf{b} \in \Bbbk^m$ and a point $\mathbf{x}$:
$$\mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}) := \mathbf{x} +
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{b} - \mathbf{A}\mathbf{x})\,,$$
the point nearest $\mathbf{x}$ among the least-squares solutions of the sketched system
$\mathbf{S}\mathbf{A}\mathbf{y} = \mathbf{S}\mathbf{b}$, which are its solutions when that system
is consistent (`NLAlib.isLeastSquaresSolution_sketchAndProject`,
`NLAlib.norm_sub_sketchAndProject_le_of_isLeastSquaresSolution`). Total; the step is the identity
when $\mathbf{S}\mathbf{A} = \mathbf{0}$. The argument order is that of `NLAlib.sketchAndSolve`.
[GowerRichtarik2015, (2.2), (2.7)]; there with a metric $\mathbf{B}$ and the sketch
$\mathbf{S}^{\mathsf{T}}$, here $\mathbf{B} = \mathbf{I}$ and the sketch on the left. -/
noncomputable def sketchAndProject (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) : n → 𝕜 :=
  x + pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ x))

/-- The **sketch-and-project iterate** with sketches $\mathbf{S}_0, \mathbf{S}_1, \ldots$:
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, 0) :=
\mathbf{x}_0$ and
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q + 1) :=
\mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}_q, \mathbf{b}, \mathbf{x}_q)$, with
$\mathbf{x}_q$ the $q$-th iterate. A random iterate is
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}(\omega), \mathbf{b}, \mathbf{x}_0,
q)$ for a random sequence $\mathbf{S} : \Omega \to (\mathbb{N} \to \Bbbk^{k \times m})$; it
depends only on the first $q$ sketches (`NLAlib.dependsOn_sketchAndProjectIterate`).
[GowerRichtarik2015, (2.2)]. -/
noncomputable def sketchAndProjectIterate (A : Matrix m n 𝕜) (S : ℕ → Matrix k m 𝕜) (b : m → 𝕜)
    (x₀ : n → 𝕜) : ℕ → n → 𝕜
  | 0 => x₀
  | q + 1 => sketchAndProject A (S q) b (sketchAndProjectIterate A S b x₀ q)

/-- The zeroth sketch-and-project iterate is the start:
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, 0) =
\mathbf{x}_0$. -/
@[simp]
theorem sketchAndProjectIterate_zero (A : Matrix m n 𝕜) (S : ℕ → Matrix k m 𝕜) (b : m → 𝕜)
    (x₀ : n → 𝕜) : sketchAndProjectIterate A S b x₀ 0 = x₀ :=
  rfl

/-- One sketch-and-project step of the iterate:
$\mathbf{x}_{q+1} = \mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}_q, \mathbf{b}, \mathbf{x}_q)$
for the iterates
$\mathbf{x}_q = \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0,
q)$. -/
theorem sketchAndProjectIterate_succ (A : Matrix m n 𝕜) (S : ℕ → Matrix k m 𝕜) (b : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) :
    sketchAndProjectIterate A S b x₀ (q + 1) =
      sketchAndProject A (S q) b (sketchAndProjectIterate A S b x₀ q) :=
  rfl

/-! ### The geometry of one step -/

/-- **The step solves the sketched least-squares problem**: for every
$\mathbf{A} \in \Bbbk^{m \times n}$, sketch $\mathbf{S}$, $\mathbf{b}$ and $\mathbf{x}$,
$\mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x})$ minimizes
$\|\mathbf{S}\mathbf{A}\mathbf{y} - \mathbf{S}\mathbf{b}\|$ over $\mathbf{y}$.
[GowerRichtarik2015, (2.2)], there for a consistent system. -/
theorem isLeastSquaresSolution_sketchAndProject (A : Matrix m n 𝕜) (S : Matrix k m 𝕜)
    (b : m → 𝕜) (x : n → 𝕜) :
    IsLeastSquaresSolution (S * A) (S *ᵥ b) (sketchAndProject A S b x) := by
  have hu : S *ᵥ (b - A *ᵥ x) = S *ᵥ b - (S * A) *ᵥ x := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec]
  rw [isLeastSquaresSolution_iff_mulVec_eq_rangeProjector_mulVec, sketchAndProject, hu,
    Matrix.mulVec_add, Matrix.mulVec_mulVec _ (S * A) (pinv (S * A)), mul_pinv,
    Matrix.mulVec_sub, Matrix.mulVec_mulVec _ (rangeProjector (S * A)) (S * A),
    rangeProjector_mul_self, add_sub_cancel]

/-- **The step is the nearest sketched least-squares solution**: for every minimizer
$\mathbf{y}$ of $\|\mathbf{S}\mathbf{A}\mathbf{y} - \mathbf{S}\mathbf{b}\|$,
$$\|\mathbf{x} - \mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x})\| \le
\|\mathbf{x} - \mathbf{y}\|\,.$$
[GowerRichtarik2015, (2.2)], there the projection of $\mathbf{x}$ onto the solution set of a
consistent sketched system. -/
theorem norm_sub_sketchAndProject_le_of_isLeastSquaresSolution {A : Matrix m n 𝕜}
    {S : Matrix k m 𝕜} {b : m → 𝕜} {y : n → 𝕜} (hy : IsLeastSquaresSolution (S * A) (S *ᵥ b) y)
    (x : n → 𝕜) :
    ‖WithLp.toLp 2 (x - sketchAndProject A S b x)‖ ≤ ‖WithLp.toLp 2 (x - y)‖ := by
  have hy' : IsLeastSquaresSolution (S * A) (S *ᵥ (b - A *ᵥ x)) (y - x) := fun z => by
    have e : ∀ w, S *ᵥ (b - A *ᵥ x) - (S * A) *ᵥ w = S *ᵥ b - (S * A) *ᵥ (w + x) := fun w => by
      rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_add]; abel
    rw [e, e, sub_add_cancel]
    exact hy (z + x)
  rw [sketchAndProject, sub_add_cancel_left, WithLp.toLp_neg, norm_neg, WithLp.toLp_sub,
    norm_sub_rev, ← WithLp.toLp_sub]
  exact hy'.norm_pinv_mulVec_le

/-- **The error after one step**: for every reference point $\mathbf{x}_\star$, with
$\mathbf{P} = \mathbf{P}_{(\mathbf{S}\mathbf{A})^{\mathsf{H}}}$ the projector onto the row space
of $\mathbf{S}\mathbf{A}$,
$$\mathbf{x}_\star - \mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}) =
(\mathbf{I} - \mathbf{P})(\mathbf{x}_\star - \mathbf{x}) -
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{b} - \mathbf{A}\mathbf{x}_\star)\,:$$
the complementary projection of the error, minus the sketched solution for the residual of
$\mathbf{x}_\star$. -/
theorem sub_sketchAndProject_eq [DecidableEq n] (A : Matrix m n 𝕜) (S : Matrix k m 𝕜)
    (b : m → 𝕜) (x xs : n → 𝕜) :
    xs - sketchAndProject A S b x =
      (1 - rangeProjector (S * A)ᴴ) *ᵥ (xs - x) - pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ xs)) := by
  have hu : S *ᵥ (b - A *ᵥ x) = S *ᵥ (b - A *ᵥ xs) + (S * A) *ᵥ (xs - x) := by
    simp only [Matrix.mulVec_sub, ← Matrix.mulVec_mulVec]; abel
  rw [sketchAndProject, hu, Matrix.mulVec_add, Matrix.mulVec_mulVec (xs - x) (pinv (S * A)),
    pinv_mul, Matrix.sub_mulVec, Matrix.one_mulVec]
  abel

/-- **Pythagoras for one step**: for every reference point $\mathbf{x}_\star$, with
$\mathbf{P} = \mathbf{P}_{(\mathbf{S}\mathbf{A})^{\mathsf{H}}}$ the projector onto the row space
of $\mathbf{S}\mathbf{A}$ and $\mathbf{x}^{+} = \mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S},
\mathbf{b}, \mathbf{x})$,
$$\|\mathbf{x}_\star - \mathbf{x}^{+}\|^2 = \|\mathbf{x}_\star - \mathbf{x}\|^2 -
\|\mathbf{P}(\mathbf{x}_\star - \mathbf{x})\|^2 +
\|(\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{b} - \mathbf{A}\mathbf{x}_\star)\|^2\,.$$
For a consistent system and a solution $\mathbf{x}_\star$ the last term vanishes.
[GowerRichtarik2015, proof of Theorem 4.6], there for a consistent system. -/
theorem norm_sub_sketchAndProject_sq (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x xs : n → 𝕜) :
    ‖WithLp.toLp 2 (xs - sketchAndProject A S b x)‖ ^ 2 =
      ‖WithLp.toLp 2 (xs - x)‖ ^ 2 - ‖WithLp.toLp 2 (rangeProjector (S * A)ᴴ *ᵥ (xs - x))‖ ^ 2 +
        ‖WithLp.toLp 2 (pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ xs)))‖ ^ 2 := by
  classical
  have hP := isStarProjection_rangeProjector (S * A)ᴴ
  have hPw : rangeProjector (S * A)ᴴ *ᵥ (pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ xs))) =
      pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ xs)) := by
    rw [← pinv_mul, Matrix.mulVec_mulVec, pinv_mul_mul_pinv]
  have h1 := hP.norm_toLp_sq_eq_add (xs - x)
  have h2 := hP.norm_toLp_sq_eq_add (xs - sketchAndProject A S b x)
  have hPa : rangeProjector (S * A)ᴴ *ᵥ (xs - sketchAndProject A S b x) =
      -(pinv (S * A) *ᵥ (S *ᵥ (b - A *ᵥ xs))) := by
    rw [sub_sketchAndProject_eq, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.mul_one_sub_self,
      Matrix.zero_mulVec, hPw, zero_sub]
  have hPb : (1 - rangeProjector (S * A)ᴴ) *ᵥ (xs - sketchAndProject A S b x) =
      (1 - rangeProjector (S * A)ᴴ) *ᵥ (xs - x) := by
    rw [sub_sketchAndProject_eq, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hP.one_sub.mul_self,
      Matrix.sub_mulVec (1 : Matrix n n 𝕜) _ (pinv (S * A) *ᵥ _), Matrix.one_mulVec, hPw,
      sub_self, sub_zero]
  rw [h2, hPa, hPb, WithLp.toLp_neg, norm_neg]
  linarith

/-- **A step moves within the row space**: for every $\mathbf{A}$, sketch $\mathbf{S}$,
$\mathbf{b}$ and $\mathbf{x}$, $\mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}, \mathbf{b},
\mathbf{x}) - \mathbf{x} \in \operatorname{range}\mathbf{A}^{\mathsf{H}}$. -/
theorem sketchAndProject_sub_mem_range (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) : sketchAndProject A S b x - x ∈ LinearMap.range Aᴴ.mulVecLin := by
  rw [sketchAndProject, add_sub_cancel_left, pinv_eq_conjTranspose_mul_pinv_mul_conjTranspose_self,
    Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mulVec_mulVec]
  exact ⟨_, rfl⟩

/-! ### The iterate -/

/-- **The iterate stays in the row space through the start**: for every sequence of sketches,
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q) -
\mathbf{x}_0 \in \operatorname{range}\mathbf{A}^{\mathsf{H}}$. -/
theorem sketchAndProjectIterate_sub_mem_range (A : Matrix m n 𝕜) (S : ℕ → Matrix k m 𝕜)
    (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    sketchAndProjectIterate A S b x₀ q - x₀ ∈ LinearMap.range Aᴴ.mulVecLin := by
  induction q with
  | zero => rw [sketchAndProjectIterate_zero, sub_self]; exact Submodule.zero_mem _
  | succ q ih =>
    rw [sketchAndProjectIterate_succ,
      ← sub_add_sub_cancel _ (sketchAndProjectIterate A S b x₀ q) x₀]
    exact Submodule.add_mem _ (sketchAndProject_sub_mem_range A (S q) b _) ih

/-- **For a consistent system the error never grows**: if $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, then for every sequence of sketches
$$\|\mathbf{x}_\star - \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b},
\mathbf{x}_0, q)\| \le \|\mathbf{x}_\star - \mathbf{x}_0\|\,.$$ -/
theorem norm_sub_sketchAndProjectIterate_le {A : Matrix m n 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (S : ℕ → Matrix k m 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A S b x₀ q)‖ ≤ ‖WithLp.toLp 2 (xs - x₀)‖ := by
  induction q with
  | zero => exact le_rfl
  | succ q ih =>
    refine le_trans ?_ ih
    rw [sketchAndProjectIterate_succ]
    have h := norm_sub_sketchAndProject_sq A (S q) b (sketchAndProjectIterate A S b x₀ q) xs
    rw [hxs, sub_self, Matrix.mulVec_zero, Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero] at h
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [h]
    nlinarith [sq_nonneg ‖WithLp.toLp 2 (rangeProjector (S q * A)ᴴ *ᵥ
      (xs - sketchAndProjectIterate A S b x₀ q))‖]

/-- The $q$-th iterate
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q)$ depends
only on the first $q$ sketches $\mathbf{S}_0, \ldots, \mathbf{S}_{q-1}$, in the sense of
Mathlib's `DependsOn`. -/
theorem dependsOn_sketchAndProjectIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) :
    DependsOn (fun S : ℕ → Matrix k m 𝕜 => sketchAndProjectIterate A S b x₀ q) (Set.Iio q) := by
  induction q with
  | zero => intro S T _; rfl
  | succ q ih =>
    intro S T h
    have h' : sketchAndProjectIterate A S b x₀ q = sketchAndProjectIterate A T b x₀ q :=
      ih fun i hi => h i (lt_trans hi q.lt_succ_self)
    change sketchAndProject A (S q) b _ = sketchAndProject A (T q) b _
    rw [h', h q q.lt_succ_self]

/-- The $q$-th iterate
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q)$ is a
measurable function of the sequence of sketches $\mathbf{S}$. -/
theorem measurable_sketchAndProjectIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) : Measurable fun S : ℕ → Matrix k m 𝕜 => sketchAndProjectIterate A S b x₀ q := by
  induction q with
  | zero => exact measurable_const
  | succ q ih =>
    have hSq : Measurable fun S : ℕ → Matrix k m 𝕜 => S q := measurable_pi_apply q
    exact ih.add ((measurable_pinv.comp (hSq.matrix_mul measurable_const)).matrix_mulVec
      (hSq.matrix_mulVec (measurable_const.sub (measurable_const.matrix_mulVec ih))))

/-! ### Random sketches, consistent systems -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [DecidableEq n]

omit [DecidableEq n] in
/-- The quadratic form of a range projector is the squared norm of the projection. -/
private lemma quadForm_rangeProjector {l : Type*} [Fintype l] (B : Matrix n l 𝕜) (v : n → 𝕜) :
    quadForm (rangeProjector B) v = ((‖WithLp.toLp 2 (rangeProjector B *ᵥ v)‖ ^ 2 : ℝ) : 𝕜) := by
  have hP := isStarProjection_rangeProjector B
  have h : rangeProjector B = (rangeProjector B)ᴴ * rangeProjector B := by
    rw [hP.conjTranspose_eq, hP.mul_self]
  conv_lhs => rw [h]
  exact quadForm_conjTranspose_mul_self _ v

/-- The expected projector integrand is integrable. -/
private lemma integrable_rangeProjector (ν : Measure (Matrix k m 𝕜)) [IsFiniteMeasure ν]
    (A : Matrix m n 𝕜) : Integrable (fun T => rangeProjector (T * A)ᴴ) ν :=
  Integrable.of_bound ((measurable_rangeProjector.comp (Measurable.matrix_conjTranspose
    continuous_star.measurable (measurable_id.matrix_mul measurable_const))).aestronglyMeasurable)
    1 (ae_of_all _ fun _ => (isStarProjection_rangeProjector _).norm_le)

/-- The quadratic form of the expected projector is the mean squared norm of the projection. -/
private lemma re_quadForm_integral_rangeProjector (ν : Measure (Matrix k m 𝕜)) [IsFiniteMeasure ν]
    (A : Matrix m n 𝕜) (v : n → 𝕜) :
    RCLike.re (quadForm (∫ T, rangeProjector (T * A)ᴴ ∂ν) v) =
      ∫ T, ‖WithLp.toLp 2 (rangeProjector (T * A)ᴴ *ᵥ v)‖ ^ 2 ∂ν := by
  rw [← integral_quadForm (integrable_rangeProjector ν A) v]
  simp only [quadForm_rangeProjector]
  rw [integral_ofReal, RCLike.ofReal_re]

omit [DecidableEq n] in
/-- A bounded continuous function of the iterate is integrable. -/
private lemma integrable_comp_sketchAndProjectIterate {E : Type*} [NormedAddCommGroup E]
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (iidSequence ν) μ) (A : Matrix m n 𝕜) (b : m → 𝕜)
    (x₀ : n → 𝕜) (q : ℕ) {f : (n → 𝕜) → E} (hf : Continuous f) {R : ℝ}
    (hR : ∀ T : ℕ → Matrix k m 𝕜, ‖f (sketchAndProjectIterate A T b x₀ q)‖ ≤ R) :
    Integrable (fun ω => f (sketchAndProjectIterate A (S ω) b x₀ q)) μ := by
  have : IsProbabilityMeasure μ := hS.isProbabilityMeasure
  exact Integrable.of_bound (hf.comp_aestronglyMeasurable
    ((measurable_sketchAndProjectIterate A b x₀ q).comp_aemeasurable
      hS.aemeasurable).aestronglyMeasurable) R (ae_of_all _ fun ω => hR (S ω))

omit [DecidableEq n] in
/-- Conditioning on the past for the sketch-and-project iterate. -/
private lemma integral_comp_sketchAndProjectIterate {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν]
    {S : Ω → ℕ → Matrix k m 𝕜} (hS : HasLaw S (iidSequence ν) μ)
    (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) {f : (n → 𝕜) × Matrix k m 𝕜 → E}
    (hf : AEStronglyMeasurable f
      ((μ.map fun ω => sketchAndProjectIterate A (S ω) b x₀ q).prod ν))
    {g : (n → 𝕜) → ℝ} (hg : Continuous g) (hfg : ∀ p, ‖f p‖ ≤ g p.1) {R : ℝ}
    (hR : ∀ T : ℕ → Matrix k m 𝕜, g (sketchAndProjectIterate A T b x₀ q) ≤ R) :
    ∫ ω, f (sketchAndProjectIterate A (S ω) b x₀ q, S ω q) ∂μ =
      ∫ ω, ∫ T, f (sketchAndProjectIterate A (S ω) b x₀ q, T) ∂ν ∂μ := by
  have hF := measurable_sketchAndProjectIterate (k := k) A b x₀ q
  have hFS : AEMeasurable (fun ω => sketchAndProjectIterate A (S ω) b x₀ q) μ :=
    hF.comp_aemeasurable hS.aemeasurable
  have hgi : Integrable g (μ.map fun ω => sketchAndProjectIterate A (S ω) b x₀ q) := by
    refine (integrable_map_measure hg.aestronglyMeasurable hFS).mpr ?_
    refine integrable_comp_sketchAndProjectIterate hS A b x₀ q hg (R := R) fun T => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg ((norm_nonneg _).trans (hfg (_, 0)))]
    exact hR T
  exact hS.integral_comp_eq_integral_integral_of_dependsOn hF
    (dependsOn_sketchAndProjectIterate A b x₀ q) ((hgi.comp_fst ν).mono' hf (ae_of_all _ hfg))

omit [DecidableEq n] in
/-- For a consistent system one step multiplies the error by the complementary projector. -/
private lemma sub_sketchAndProject_eq_of_mulVec_eq {A : Matrix m n 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (T : Matrix k m 𝕜) (x : n → 𝕜) :
    xs - sketchAndProject A T b x = xs - x - rangeProjector (T * A)ᴴ *ᵥ (xs - x) := by
  classical
  rw [sub_sketchAndProject_eq, hxs, sub_self, Matrix.mulVec_zero, Matrix.mulVec_zero, sub_zero,
    Matrix.sub_mulVec, Matrix.one_mulVec]

omit [DecidableEq n] in
/-- For a consistent system the squared error drops by the squared projection. -/
private lemma norm_sub_sketchAndProject_sq_of_mulVec_eq {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (T : Matrix k m 𝕜) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (xs - sketchAndProject A T b x)‖ ^ 2 = ‖WithLp.toLp 2 (xs - x)‖ ^ 2 -
      ‖WithLp.toLp 2 (rangeProjector (T * A)ᴴ *ᵥ (xs - x))‖ ^ 2 := by
  rw [norm_sub_sketchAndProject_sq, hxs, sub_self, Matrix.mulVec_zero, Matrix.mulVec_zero,
    WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero, add_zero]

omit [DecidableEq n] in
/-- The Euclidean norm squared, a continuous function. -/
private lemma continuous_norm_toLp_sq : Continuous fun v : n → 𝕜 => ‖WithLp.toLp 2 v‖ ^ 2 :=
  (continuous_norm.comp (PiLp.continuous_toLp 2 _)).pow 2

omit [DecidableEq n] in
/-- A random projection does not increase the mean squared norm. -/
private lemma integral_norm_rangeProjector_sq_le (ν : Measure (Matrix k m 𝕜))
    [IsProbabilityMeasure ν] (A : Matrix m n 𝕜) (v : n → 𝕜) :
    ∫ T, ‖WithLp.toLp 2 (rangeProjector (T * A)ᴴ *ᵥ v)‖ ^ 2 ∂ν ≤ ‖WithLp.toLp 2 v‖ ^ 2 := by
  calc _ ≤ ∫ _T, ‖WithLp.toLp 2 v‖ ^ 2 ∂ν := by
        refine integral_mono_of_nonneg (ae_of_all _ fun _ => sq_nonneg _) (integrable_const _)
          (ae_of_all _ fun T => ?_)
        exact pow_le_pow_left₀ (norm_nonneg _)
          ((isStarProjection_rangeProjector _).norm_toLp_mulVec_le v) 2
    _ = _ := by rw [integral_const, probReal_univ, one_smul]

/-- A Loewner bound on the expected projector bounds its quadratic form on the row space. -/
private lemma mul_norm_sq_le_re_quadForm_integral {ν : Measure (Matrix k m 𝕜)}
    {A : Matrix m n 𝕜} {lam : ℝ}
    (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν) {v : n → 𝕜}
    (hv : v ∈ LinearMap.range Aᴴ.mulVecLin) :
    lam * ‖WithLp.toLp 2 v‖ ^ 2 ≤ RCLike.re (quadForm (∫ T, rangeProjector (T * A)ᴴ ∂ν) v) := by
  have h := re_quadForm_le_re_quadForm_of_le hlam v
  rwa [RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left, RCLike.re_ofReal_mul,
    quadForm_rangeProjector, RCLike.ofReal_re, rangeProjector_mulVec_eq_self_iff.mpr hv] at h

/-- The constant of a Loewner bound holding at a nonzero row-space vector is at most one. -/
private lemma le_one_of_smul_rangeProjector_le {ν : Measure (Matrix k m 𝕜)}
    [IsProbabilityMeasure ν] {A : Matrix m n 𝕜} {lam : ℝ}
    (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν) {v : n → 𝕜}
    (hv : v ∈ LinearMap.range Aᴴ.mulVecLin) (hv0 : v ≠ 0) : lam ≤ 1 := by
  have h := mul_norm_sq_le_re_quadForm_integral hlam hv
  rw [re_quadForm_integral_rangeProjector] at h
  have h2 := integral_norm_rangeProjector_sq_le ν A v
  have hpos : 0 < ‖WithLp.toLp 2 v‖ ^ 2 := by
    have : WithLp.toLp 2 v ≠ 0 := by rwa [Ne, WithLp.toLp_eq_zero]
    positivity
  nlinarith

/-- **The one-step identity in expectation**: for a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and independent sketches $\mathbf{S}_0, \mathbf{S}_1,
\ldots$, each with the probability law $\nu$, the iterates
$\mathbf{x}_q = \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0,
q)$ satisfy, with $\mathbf{Z} = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}$ for
$\mathbf{S} \sim \nu$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 = \mathbb{E}\|\mathbf{x}_\star -
\mathbf{x}_q\|^2 - \mathbb{E}\operatorname{Re}\langle \mathbf{x}_\star - \mathbf{x}_q,
\mathbb{E}_{\nu}[\mathbf{Z}](\mathbf{x}_\star - \mathbf{x}_q)\rangle\,.$$
[GowerRichtarik2015, proof of Theorem 4.6]. -/
theorem integral_norm_sub_sketchAndProjectIterate_succ_sq_of_hasLaw_iidSequence
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (iidSequence ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ (q + 1))‖ ^ 2 ∂μ =
      ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ -
        ∫ ω, RCLike.re (quadForm (∫ T, rangeProjector (T * A)ᴴ ∂ν)
          (xs - sketchAndProjectIterate A (S ω) b x₀ q)) ∂μ := by
  have hbd2 : ∀ j (T : ℕ → Matrix k m 𝕜),
      ‖‖WithLp.toLp 2 (xs - sketchAndProjectIterate A T b x₀ j)‖ ^ 2‖ ≤
        ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := fun j T => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_sketchAndProjectIterate_le hxs T x₀ j) 2
  have hc : Continuous fun v : n → 𝕜 => ‖WithLp.toLp 2 (xs - v)‖ ^ 2 :=
    continuous_norm_toLp_sq.comp (continuous_const.sub continuous_id)
  have hI := fun j => integrable_comp_sketchAndProjectIterate hS A b x₀ j hc (hbd2 j)
  have hpt : ∀ ω, ‖WithLp.toLp 2 (rangeProjector (S ω q * A)ᴴ *ᵥ
      (xs - sketchAndProjectIterate A (S ω) b x₀ q))‖ ^ 2 =
      ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 -
        ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ (q + 1))‖ ^ 2 := fun ω => by
    rw [sketchAndProjectIterate_succ, norm_sub_sketchAndProject_sq_of_mulVec_eq hxs]
    ring
  have hfub := integral_comp_sketchAndProjectIterate hS A b x₀ q
    (f := fun p => ‖WithLp.toLp 2 (rangeProjector (p.2 * A)ᴴ *ᵥ (xs - p.1))‖ ^ 2)
    ((continuous_norm_toLp_sq.measurable.comp ((measurable_rangeProjector.comp
      (Measurable.matrix_conjTranspose continuous_star.measurable
        (measurable_snd.matrix_mul measurable_const))).matrix_mulVec
      (measurable_const.sub measurable_fst))).aestronglyMeasurable) hc
    (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _)
        ((isStarProjection_rangeProjector _).norm_toLp_mulVec_le _) 2)
    (fun T => pow_le_pow_left₀ (norm_nonneg _) (norm_sub_sketchAndProjectIterate_le hxs T x₀ q) 2)
  simp only at hfub
  rw [integral_congr_ae (ae_of_all _ hpt), integral_sub (hI q) (hI (q + 1))] at hfub
  simp only [← re_quadForm_integral_rangeProjector] at hfub
  linarith

/-- **The mean error contracts by the expected projector**: for a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and independent sketches $\mathbf{S}_0, \mathbf{S}_1,
\ldots$, each with the probability law $\nu$, the iterates
$\mathbf{x}_q = \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0,
q)$ satisfy
$$\mathbf{x}_\star - \mathbb{E}[\mathbf{x}_q] = (\mathbf{I} - \mathbb{E}_{\nu}[\mathbf{Z}])^q
(\mathbf{x}_\star - \mathbf{x}_0)\,,\qquad
\mathbf{Z} = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}\,,\ \mathbf{S} \sim \nu\,.$$
[GowerRichtarik2015, Theorem 4.4, (4.6)], there with a metric $\mathbf{B}$. -/
theorem integral_sub_sketchAndProjectIterate_of_hasLaw_iidSequence
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (iidSequence ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, (xs - sketchAndProjectIterate A (S ω) b x₀ q) ∂μ =
      (1 - ∫ T, rangeProjector (T * A)ᴴ ∂ν) ^ q *ᵥ (xs - x₀) := by
  have : IsProbabilityMeasure μ := hS.isProbabilityMeasure
  have hc : Continuous fun v : n → 𝕜 => xs - v := continuous_const.sub continuous_id
  have hIe := fun j => integrable_comp_sketchAndProjectIterate hS A b x₀ j hc fun T =>
    (EuclideanSpace.norm_le_norm_toLp _).trans (norm_sub_sketchAndProjectIterate_le hxs T x₀ j)
  have hin : ∀ v, ∫ T, (v - rangeProjector (T * A)ᴴ *ᵥ v) ∂ν =
      (1 - ∫ T, rangeProjector (T * A)ᴴ ∂ν) *ᵥ v := fun v => by
    have h := Matrix.integral_mulVec (X := fun T => 1 - rangeProjector (T * A)ᴴ)
      ((integrable_const _).sub (integrable_rangeProjector ν A)) v
    rw [integral_sub (integrable_const _) (integrable_rangeProjector ν A), integral_const,
      probReal_univ, one_smul] at h
    rw [← h]
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
  induction q with
  | zero =>
    simp only [sketchAndProjectIterate_zero, pow_zero, Matrix.one_mulVec, integral_const,
      probReal_univ, one_smul]
  | succ q ih =>
    have hfub := integral_comp_sketchAndProjectIterate hS A b x₀ q
      (f := fun p => xs - p.1 - rangeProjector (p.2 * A)ᴴ *ᵥ (xs - p.1))
      ((measurable_const.sub measurable_fst).sub ((measurable_rangeProjector.comp
        (Measurable.matrix_conjTranspose continuous_star.measurable
          (measurable_snd.matrix_mul measurable_const))).matrix_mulVec
        (measurable_const.sub measurable_fst))).aestronglyMeasurable
      ((continuous_norm.comp (PiLp.continuous_toLp 2 _)).comp hc)
      (fun p => by
        refine (EuclideanSpace.norm_le_norm_toLp _).trans ?_
        have h := (isStarProjection_rangeProjector (p.2 * A)ᴴ).one_sub.norm_toLp_mulVec_le
          (xs - p.1)
        rwa [Matrix.sub_mulVec, Matrix.one_mulVec] at h)
      (fun T => norm_sub_sketchAndProjectIterate_le hxs T x₀ q)
    simp only at hfub
    simp_rw [sketchAndProjectIterate_succ, sub_sketchAndProject_eq_of_mulVec_eq hxs]
    rw [hfub]
    simp only [hin]
    have hL : ∫ ω, (1 - ∫ T, rangeProjector (T * A)ᴴ ∂ν) *ᵥ
        (xs - sketchAndProjectIterate A (S ω) b x₀ q) ∂μ =
        (1 - ∫ T, rangeProjector (T * A)ᴴ ∂ν) *ᵥ
          ∫ ω, (xs - sketchAndProjectIterate A (S ω) b x₀ q) ∂μ :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin
        (1 - ∫ T, rangeProjector (T * A)ᴴ ∂ν))).integral_comp_comm (hIe q)
    rw [hL, ih, Matrix.mulVec_mulVec, ← pow_succ']

/-- **Sketch-and-project converges linearly in expectation**: for a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, a start with $\mathbf{x}_\star - \mathbf{x}_0$ in the
row space of $\mathbf{A}$, independent sketches $\mathbf{S}_0, \mathbf{S}_1, \ldots$, each with
the probability law $\nu$, and
$\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq \mathbb{E}_{\nu}[\mathbf{Z}]$ with
$\mathbf{Z} = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S},
\mathbf{b}, \mathbf{x}_0, q)\|^2 \le (1 - \lambda)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
[GowerRichtarik2015, Theorem 4.6]; there for $\mathbb{E}[\mathbf{Z}]$ positive definite (full
column rank) and $\lambda = \lambda_{\min}(\mathbb{E}[\mathbf{Z}])$, with a metric $\mathbf{B}$;
here any rank, any law and $\mathbf{B} = \mathbf{I}$. Since $\nu$ is a probability measure and
$\mathbf{Z} \preceq \mathbf{P}_{\mathbf{A}^{\mathsf{H}}}$, $\lambda \le 1$ whenever
$\mathbf{A} \ne \mathbf{0}$. Iteration count:
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_hasLaw_iidSequence_of_log_div_le`.
Result: sketch-and-project -/
theorem integral_norm_sub_sketchAndProjectIterate_sq_le_of_hasLaw_iidSequence
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (iidSequence ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs x₀ : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {lam : ℝ} (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - lam) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  have : IsProbabilityMeasure μ := hS.isProbabilityMeasure
  rcases eq_or_ne (xs - x₀) 0 with h0 | h0
  · have hz : ∀ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 = 0 :=
      fun ω => by
        have h := norm_sub_sketchAndProjectIterate_le hxs (S ω) x₀ q
        rw [h0, WithLp.toLp_zero, norm_zero] at h
        rw [le_antisymm h (norm_nonneg _), zero_pow two_ne_zero]
    simp only [hz, integral_zero, h0, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero,
      mul_zero, le_refl]
  have hlam1 := le_one_of_smul_rangeProjector_le hlam hx₀ h0
  have hbd2 : ∀ j (T : ℕ → Matrix k m 𝕜),
      ‖‖WithLp.toLp 2 (xs - sketchAndProjectIterate A T b x₀ j)‖ ^ 2‖ ≤
        ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := fun j T => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_sub_sketchAndProjectIterate_le hxs T x₀ j) 2
  have hI := fun j => integrable_comp_sketchAndProjectIterate hS A b x₀ j
    (continuous_norm_toLp_sq.comp (continuous_const.sub continuous_id)) (hbd2 j)
  have hcq : Continuous fun v : n → 𝕜 =>
      RCLike.re (quadForm (∫ T, rangeProjector (T * A)ᴴ ∂ν) (xs - v)) := by
    simp only [quadForm]
    exact RCLike.continuous_re.comp (((continuous_const.sub continuous_id).star).dotProduct
      (continuous_const.matrix_mulVec (continuous_const.sub continuous_id)))
  induction q with
  | zero =>
    simp only [sketchAndProjectIterate_zero, pow_zero, one_mul, integral_const, probReal_univ,
      one_smul, le_refl]
  | succ q ih =>
    rw [integral_norm_sub_sketchAndProjectIterate_succ_sq_of_hasLaw_iidSequence hS hxs x₀ q]
    have hIq := integrable_comp_sketchAndProjectIterate hS A b x₀ q hcq fun T => by
      rw [re_quadForm_integral_rangeProjector, Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg fun _ => sq_nonneg _)]
      exact (integral_norm_rangeProjector_sq_le ν A _).trans (by simpa using hbd2 q T)
    have hmono : lam * ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ
        ≤ ∫ ω, RCLike.re (quadForm (∫ T, rangeProjector (T * A)ᴴ ∂ν)
          (xs - sketchAndProjectIterate A (S ω) b x₀ q)) ∂μ := by
      rw [← integral_const_mul]
      refine integral_mono ((hI q).const_mul lam) hIq fun ω => ?_
      refine mul_norm_sq_le_re_quadForm_integral hlam ?_
      have h := Submodule.sub_mem _ hx₀ (sketchAndProjectIterate_sub_mem_range A (S ω) b x₀ q)
      rwa [sub_sub_sub_cancel_right] at h
    calc _ ≤ (1 - lam) *
          ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ := by
          linarith
      _ ≤ (1 - lam) * ((1 - lam) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left ih (by linarith)
      _ = (1 - lam) ^ (q + 1) * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by ring

/-- **Sketch-and-project, iteration count**: for a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, a start with $\mathbf{x}_\star - \mathbf{x}_0$ in the
row space of $\mathbf{A}$, independent sketches $\mathbf{S}_0, \mathbf{S}_1, \ldots$, each with
the probability law $\nu$, $\lambda > 0$ with
$\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq
\mathbb{E}_{\nu}[(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}]$, $\varepsilon > 0$ and
$q \ge \lambda^{-1}\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S},
\mathbf{b}, \mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
Asymptotic form:
`exists_forall_integral_norm_sub_sketchAndProjectIterate_sq_le_of_hasLaw_iidSequence_of_log_div_le`.
-/
theorem integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_hasLaw_iidSequence_of_log_div_le
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (iidSequence ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs x₀ : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : Real.log (1 / ε) / lam ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  refine (integral_norm_sub_sketchAndProjectIterate_sq_le_of_hasLaw_iidSequence hS hxs hx₀ hlam
    q).trans ?_
  rcases eq_or_ne (xs - x₀) 0 with h0 | h0
  · simp [h0]
  have hlam1 := le_one_of_smul_rangeProjector_le hlam hx₀ h0
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  exact Real.one_sub_pow_le_of_log_le_mul hlam1 hε (by rwa [div_le_iff₀ hlam0, mul_comm] at hq)

end Random

-- The declaration name with its indentation exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\lambda^{-1}\log(1/\varepsilon))$ iterations suffice for sketch-and-project**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, a start with $\mathbf{x}_\star - \mathbf{x}_0$ in the
row space of $\mathbf{A}$, independent sketches $\mathbf{S}_0, \mathbf{S}_1, \ldots$, each with
the probability law $\nu$, $\lambda > 0$ with
$\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq
\mathbb{E}_{\nu}[(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}]$,
$0 < \varepsilon \le \varepsilon_0$ and $q \ge C\lambda^{-1}\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S},
\mathbf{b}, \mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
The constants come before every dimension and the law. Proved from
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_hasLaw_iidSequence_of_log_div_le`
with $C = 1$ and
$\varepsilon_0 = 1$. [GowerRichtarik2015, Theorem 4.6].
Asymptotic:
NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_hasLaw_iidSequence_of_log_div_le
Result: sketch-and-project -/
theorem
    exists_forall_integral_norm_sub_sketchAndProjectIterate_sq_le_of_hasLaw_iidSequence_of_log_div_le :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k]
      [Fintype m] [Fintype n] [DecidableEq n] (μ : Measure Ω) (ν : Measure (Matrix k m 𝕜))
      [IsProbabilityMeasure ν] (S : Ω → ℕ → Matrix k m 𝕜) (A : Matrix m n 𝕜) (b : m → 𝕜)
      (xs x₀ : n → 𝕜) (lam : ℝ) (q : ℕ) (ε : ℝ),
      HasLaw S (iidSequence ν) μ → A *ᵥ xs = b →
      xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < lam →
      lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν → 0 < ε → ε ≤ ε₀ →
      C * (Real.log (1 / ε) / lam) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro Ω 𝕜 k m n _ _ _ _ _ _ μ ν _ S A b xs x₀ lam q ε hS hxs hx₀ hlam0 hlam hε _ hq
  exact integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_hasLaw_iidSequence_of_log_div_le
    hS hxs hx₀ hlam0 hlam hε (by rwa [one_mul] at hq)

end NLAlib
