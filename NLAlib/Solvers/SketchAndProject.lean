/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

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
i.i.d.-sequence hypothesis `HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ`, the expected
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
* `NLAlib.integral_sub_sketchAndProjectIterate`: the mean error.
* `NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le`: linear convergence in expectation.
* `NLAlib.exists_forall_integral_norm_sub_sketchAndProjectIterate_sq_le_of_log_div_le`: its
  asymptotic iteration count.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **A step moves within the row space**: for every $\mathbf{A}$, sketch $\mathbf{S}$,
$\mathbf{b}$ and $\mathbf{x}$, $\mathsf{sketchAndProject}(\mathbf{A}, \mathbf{S}, \mathbf{b},
\mathbf{x}) - \mathbf{x} \in \operatorname{range}\mathbf{A}^{\mathsf{H}}$. -/
theorem sketchAndProject_sub_mem_range (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (b : m → 𝕜)
    (x : n → 𝕜) : sketchAndProject A S b x - x ∈ LinearMap.range Aᴴ.mulVecLin := by
  sorry

/-! ### The iterate -/

/-- **The iterate stays in the row space through the start**: for every sequence of sketches,
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q) -
\mathbf{x}_0 \in \operatorname{range}\mathbf{A}^{\mathsf{H}}$. -/
theorem sketchAndProjectIterate_sub_mem_range (A : Matrix m n 𝕜) (S : ℕ → Matrix k m 𝕜)
    (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    sketchAndProjectIterate A S b x₀ q - x₀ ∈ LinearMap.range Aᴴ.mulVecLin := by
  sorry

/-- **For a consistent system the error never grows**: if $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, then for every sequence of sketches
$$\|\mathbf{x}_\star - \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b},
\mathbf{x}_0, q)\| \le \|\mathbf{x}_\star - \mathbf{x}_0\|\,.$$ -/
theorem norm_sub_sketchAndProjectIterate_le {A : Matrix m n 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (S : ℕ → Matrix k m 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A S b x₀ q)‖ ≤ ‖WithLp.toLp 2 (xs - x₀)‖ := by
  sorry

/-- The $q$-th iterate
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q)$ depends
only on the first $q$ sketches $\mathbf{S}_0, \ldots, \mathbf{S}_{q-1}$, in the sense of
Mathlib's `DependsOn`. -/
theorem dependsOn_sketchAndProjectIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) :
    DependsOn (fun S : ℕ → Matrix k m 𝕜 => sketchAndProjectIterate A S b x₀ q) (Set.Iio q) := by
  sorry

/-- The $q$-th iterate
$\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q)$ is a
measurable function of the sequence of sketches $\mathbf{S}$. -/
theorem measurable_sketchAndProjectIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) : Measurable fun S : ℕ → Matrix k m 𝕜 => sketchAndProjectIterate A S b x₀ q := by
  sorry

/-! ### Random sketches, consistent systems -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [DecidableEq n]

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
theorem integral_norm_sub_sketchAndProjectIterate_succ_sq
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ (q + 1))‖ ^ 2 ∂μ =
      ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ -
        ∫ ω, RCLike.re (quadForm (∫ T, rangeProjector (T * A)ᴴ ∂ν)
          (xs - sketchAndProjectIterate A (S ω) b x₀ q)) ∂μ := by
  sorry

/-- **The mean error contracts by the expected projector**: for a consistent system
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and independent sketches $\mathbf{S}_0, \mathbf{S}_1,
\ldots$, each with the probability law $\nu$, the iterates
$\mathbf{x}_q = \mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0,
q)$ satisfy
$$\mathbf{x}_\star - \mathbb{E}[\mathbf{x}_q] = (\mathbf{I} - \mathbb{E}_{\nu}[\mathbf{Z}])^q
(\mathbf{x}_\star - \mathbf{x}_0)\,,\qquad
\mathbf{Z} = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{A}\,,\ \mathbf{S} \sim \nu\,.$$
[GowerRichtarik2015, Theorem 4.4, (4.6)], there with a metric $\mathbf{B}$. -/
theorem integral_sub_sketchAndProjectIterate
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, (xs - sketchAndProjectIterate A (S ω) b x₀ q) ∂μ =
      (1 - ∫ T, rangeProjector (T * A)ᴴ ∂ν) ^ q *ᵥ (xs - x₀) := by
  sorry

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
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_log_div_le`.
Result: sketch-and-project -/
theorem integral_norm_sub_sketchAndProjectIterate_sq_le
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs x₀ : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {lam : ℝ} (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - lam) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  sorry

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
`NLAlib.exists_forall_integral_norm_sub_sketchAndProjectIterate_sq_le_of_log_div_le`. -/
theorem integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_log_div_le
    {ν : Measure (Matrix k m 𝕜)} [IsProbabilityMeasure ν] {S : Ω → ℕ → Matrix k m 𝕜}
    (hS : HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ) {A : Matrix m n 𝕜} {b : m → 𝕜}
    {xs x₀ : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {lam : ℝ} (hlam0 : 0 < lam)
    (hlam : lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : Real.log (1 / ε) / lam ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  sorry

end Random

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
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_log_div_le` with $C = 1$ and
$\varepsilon_0 = 1$. [GowerRichtarik2015, Theorem 4.6].
Asymptotic: NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le_mul_of_log_div_le
Result: sketch-and-project -/
theorem exists_forall_integral_norm_sub_sketchAndProjectIterate_sq_le_of_log_div_le :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k]
      [Fintype m] [Fintype n] [DecidableEq n] (μ : Measure Ω) (ν : Measure (Matrix k m 𝕜))
      [IsProbabilityMeasure ν] (S : Ω → ℕ → Matrix k m 𝕜) (A : Matrix m n 𝕜) (b : m → 𝕜)
      (xs x₀ : n → 𝕜) (lam : ℝ) (q : ℕ) (ε : ℝ),
      HasLaw S (Measure.infinitePi fun _ : ℕ => ν) μ → A *ᵥ xs = b →
      xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < lam →
      lam • rangeProjector Aᴴ ≤ ∫ T, rangeProjector (T * A)ᴴ ∂ν → 0 < ε → ε ≤ ε₀ →
      C * (Real.log (1 / ε) / lam) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProjectIterate A (S ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  sorry

end NLAlib
