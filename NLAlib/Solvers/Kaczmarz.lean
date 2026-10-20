/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.Richardson
public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Probability.Distributions.Sampling
public import NLAlib.Solvers.SketchAndProject

/-!
# Randomized Kaczmarz

`NLAlib.kaczmarzIterate A ι b x₀ q` is the sketch-and-project iterate whose $q$-th sketch selects
row $\iota_q$ of $\mathbf{A}$: each step projects the iterate orthogonally onto the hyperplane
$\{\mathbf{y} : (\mathbf{A}\mathbf{y})_{\iota_q} = b_{\iota_q}\}$, and the familiar row-action
update is `NLAlib.kaczmarzIterate_succ`. Randomized Kaczmarz draws the rows independently with
the squared-row-norm probabilities $p_i = \|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$
(`NLAlib.rowNormSqDistribution`), written as the i.i.d.-sequence hypothesis
`HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ`.

The rate is $1 - (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^{-2}$, with the Frobenius
pseudo-condition number `NLAlib.frobPseudoConditionNumber`, and no rank assumption is needed.
For any right-hand side the expected squared error about any reference point
$\mathbf{x}_\star$ with $\mathbf{x}_\star - \mathbf{x}_0$ in the row space contracts at this rate
up to the horizon $\|\mathbf{A}^{+}\|_2^2\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2$; about the
least-squares solution nearest $\mathbf{x}_0$ the horizon is the optimal residual. For consistent
systems this is Strohmer and Vershynin's theorem. Through sketch-and-project, any row
probabilities give the rate of the least eigenvalue of the expected row projector on the row space;
and the mean iterate is Landweber's iteration with step $\|\mathbf{A}\|_{\mathsf{F}}^{-2}$.
[StrohmerVershynin2009]; [ZouziasFreris2013]; [GowerRichtarik2015]; [LeventhalLewis2010];
[Needell2010]; [MaNeedellRamdas2015]. Block Kaczmarz with row pavings [NeedellTropp2014] and the
randomized extended Kaczmarz method are not here yet.
Design: `docs/design/Regression-Kaczmarz.md`.

## Main definitions

* `NLAlib.kaczmarzIterate`: the Kaczmarz iterate for a sequence of rows.

## Main results

* `NLAlib.kaczmarzIterate_succ`: the row-action formula.
* `NLAlib.integral_norm_sub_kaczmarzIterate_succ_sq_le`: the one-step bound in expectation.
* `NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_add`: randomized Kaczmarz for any right-hand
  side.
* `NLAlib.integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le`: convergence to the
  least-squares solution nearest the start, up to the horizon.
* `NLAlib.integral_norm_sub_kaczmarzIterate_sq_le`: Strohmer and Vershynin's theorem, any rank.
* `NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_of_hasLaw_samplingMeasure`: any row
  probabilities.
* `NLAlib.integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose`,
  `NLAlib.integral_kaczmarzIterate`: the mean iterate is Landweber's iteration.
* `NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_of_mul_log_le`,
  `NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le`:
  the iteration counts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder NNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-! ### The iterate and the row-action formula -/

/-- The **Kaczmarz iterate** for $\mathbf{A} \in \Bbbk^{m \times n}$ with row choices
$\iota_0, \iota_1, \ldots$: the sketch-and-project iterate
$$\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q) :=
\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q)$$
whose $q$-th sketch $\mathbf{S}_q$ selects row $\iota_q$, so that each step is the orthogonal
projection onto the hyperplane $\{\mathbf{y} : (\mathbf{A}\mathbf{y})_{\iota_q} = b_{\iota_q}\}$.
The row-action formula
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \frac{b_{\iota_q} - (\mathbf{A}\mathbf{x}_q)_{\iota_q}}
{\|\mathbf{a}_{\iota_q}\|^2}\,\overline{\mathbf{a}_{\iota_q}}\,,$$
with $\mathbf{a}_i$ the rows of $\mathbf{A}$, is `NLAlib.kaczmarzIterate_succ`; a zero row leaves
the iterate unchanged. Randomized Kaczmarz draws the rows independently with probabilities
`NLAlib.rowNormSqDistribution A`. [StrohmerVershynin2009, Algorithm 1];
[MaNeedellRamdas2015, (2.1)], the complex update; [GowerRichtarik2015, §3.3], as
sketch-and-project. -/
noncomputable def kaczmarzIterate (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) :
    ℕ → n → 𝕜 :=
  sketchAndProjectIterate A (fun q => (selectionMatrix fun _ : Unit => ι q)ᴴ) b x₀

section Deterministic

variable {A : Matrix m n 𝕜} {b : m → 𝕜} {x₀ : n → 𝕜}

/-- The zeroth Kaczmarz iterate is the start:
$\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, 0) = \mathbf{x}_0$. -/
@[simp]
theorem kaczmarzIterate_zero (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) :
    kaczmarzIterate A ι b x₀ 0 = x₀ :=
  rfl

/-- **The row-action formula** of the Kaczmarz iterate: with $\mathbf{a}_i$ the rows of
$\mathbf{A}$ and $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)$,
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \frac{b_{\iota_q} - (\mathbf{A}\mathbf{x}_q)_{\iota_q}}
{\|\mathbf{a}_{\iota_q}\|^2}\,\overline{\mathbf{a}_{\iota_q}}\,,$$
and $\mathbf{x}_{q+1} = \mathbf{x}_q$ when $\mathbf{a}_{\iota_q} = \mathbf{0}$ (division by zero is
zero). [StrohmerVershynin2009, Algorithm 1]; [MaNeedellRamdas2015, (2.1)]. -/
theorem kaczmarzIterate_succ (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    kaczmarzIterate A ι b x₀ (q + 1) =
      kaczmarzIterate A ι b x₀ q +
        ((b (ι q) - (A *ᵥ kaczmarzIterate A ι b x₀ q) (ι q)) /
          ((‖WithLp.toLp 2 (A (ι q))‖ ^ 2 : ℝ) : 𝕜)) • star (A (ι q)) := by
  sorry

/-- **Each step solves its equation**: if row $\iota_q$ of $\mathbf{A}$ is nonzero, the iterate
$\mathbf{x}_{q+1} = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q + 1)$
satisfies $(\mathbf{A}\mathbf{x}_{q+1})_{\iota_q} = b_{\iota_q}$.
[MaNeedellRamdas2015, (2.2)]. -/
theorem mulVec_kaczmarzIterate_succ_apply {ι : ℕ → m} {q : ℕ} (hA : A (ι q) ≠ 0) :
    (A *ᵥ kaczmarzIterate A ι b x₀ (q + 1)) (ι q) = b (ι q) := by
  sorry

/-- **The one-step identity**, for any reference point $\mathbf{x}_\star$ and every row: with
$\mathbf{a}_i$ the rows of $\mathbf{A}$ and $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A},
\iota, \mathbf{b}, \mathbf{x}_0, q)$,
$$\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 = \|\mathbf{x}_\star - \mathbf{x}_q\|^2 -
\frac{\lvert(\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q))_{\iota_q}\rvert^2}
{\|\mathbf{a}_{\iota_q}\|^2} + \frac{\lvert(\mathbf{b} -
\mathbf{A}\mathbf{x}_\star)_{\iota_q}\rvert^2}{\|\mathbf{a}_{\iota_q}\|^2}\,;$$
for a zero row both fractions are $0$ and the step is the identity.
[StrohmerVershynin2009, proof of Theorem 2], there for a consistent system. -/
theorem norm_sub_kaczmarzIterate_succ_sq (ι : ℕ → m) (xs : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (xs - kaczmarzIterate A ι b x₀ (q + 1))‖ ^ 2 =
      ‖WithLp.toLp 2 (xs - kaczmarzIterate A ι b x₀ q)‖ ^ 2 -
        ‖(A *ᵥ (xs - kaczmarzIterate A ι b x₀ q)) (ι q)‖ ^ 2 / ‖WithLp.toLp 2 (A (ι q))‖ ^ 2 +
        ‖(b - A *ᵥ xs) (ι q)‖ ^ 2 / ‖WithLp.toLp 2 (A (ι q))‖ ^ 2 := by
  sorry

/-- **The Kaczmarz iterate stays in the row space through the start**: for every sequence of
rows, $\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q) - \mathbf{x}_0
\in \operatorname{range}\mathbf{A}^{\mathsf{H}}$. -/
theorem kaczmarzIterate_sub_mem_range (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) : kaczmarzIterate A ι b x₀ q - x₀ ∈ LinearMap.range Aᴴ.mulVecLin := by
  sorry

end Deterministic

/-! ### Squared-row-norm sampling -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [MeasurableSpace m]
  [MeasurableSingletonClass m] {A : Matrix m n 𝕜} {b : m → 𝕜} {ι : Ω → ℕ → m} {x₀ : n → 𝕜}

/-- **The one-step bound in expectation**, for any right-hand side and reference point: with rows
drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$), the
iterates $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q)$
satisfy, for every $\mathbf{x}_\star$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 \le \mathbb{E}\|\mathbf{x}_\star -
\mathbf{x}_q\|^2 - \frac{\mathbb{E}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2} + \frac{\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2}\,.$$
The gap is the residual on the zero rows, which are never chosen; with no zero row it is an
identity (`NLAlib.integral_norm_sub_kaczmarzIterate_succ_sq`).
[StrohmerVershynin2009, proof of Theorem 2]; [ZouziasFreris2013, Theorem 7, (5)], there after
the singular-value bound. -/
theorem integral_norm_sub_kaczmarzIterate_succ_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (xs : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (q + 1))‖ ^ 2 ∂μ ≤
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ -
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 +
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2 := by
  sorry

/-- **The one-step identity in expectation**, when no row of $\mathbf{A}$ is zero: with rows
drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i \ne \mathbf{0}$ the rows of
$\mathbf{A}$), the iterates $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota,
\mathbf{b}, \mathbf{x}_0, q)$ satisfy, for every $\mathbf{x}_\star$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 = \mathbb{E}\|\mathbf{x}_\star -
\mathbf{x}_q\|^2 - \frac{\mathbb{E}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2} + \frac{\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2}\,.$$
Without the hypothesis it fails: for
$\mathbf{A} = \begin{bmatrix} 1 \\ 0 \end{bmatrix}$, $\mathbf{b} = (0, 1)$ and
$\mathbf{x}_0 = \mathbf{x}_\star = \mathbf{0}$ the left side is $0$ and the right side $1$.
[StrohmerVershynin2009, proof of Theorem 2], there for a consistent system. -/
theorem integral_norm_sub_kaczmarzIterate_succ_sq (hA : ∀ i, A i ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (xs : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (q + 1))‖ ^ 2 ∂μ =
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ -
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 +
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2 := by
  sorry

/-- **Randomized Kaczmarz, any right-hand side**: with rows drawn independently from the
squared-row-norm law, row $i$ with probability $\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$
($\mathbf{a}_i$ the rows of
$\mathbf{A}$), for every $\mathbf{x}_\star$ with $\mathbf{x}_\star - \mathbf{x}_0$ in the row
space of $\mathbf{A}$ and with
$\rho = 1 - (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^{-2}$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \rho^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2 + (1 - \rho^q)\,
\|\mathbf{A}^{+}\|_2^2\,\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2\,.$$
No rank assumption. **The reference point.** For $\mathbf{x}_0 = \mathbf{0}$ take
$\mathbf{x}_\star = \mathbf{A}^{+}\mathbf{b}$; in general take the least-squares solution
nearest $\mathbf{x}_0$, $\mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$,
which minimises the horizon (`NLAlib.integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le`).
The choice $\mathbf{x}_\star = \mathbf{A}^{+}\mathbf{b}$ with a generic $\mathbf{x}_0$ violates the
row-space hypothesis, and the bound then fails. [ZouziasFreris2013, Theorem 7]; the same horizon
$\|\mathbf{w}\|^2/\sigma_{\min}^2$, here with the factor $1 - \rho^q$. [Needell2010,
Theorem 2.1]; there for full column rank, in the unsquared norm and with the larger horizon
$R\gamma^2 \ge \|\mathbf{A}^{+}\|_2^2\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2$, which this
implies by Jensen's inequality. Port of `NLAlib.Kaczmarz.expErr_le_add_of_sub_mem_range` and
five variants. Iteration count:
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le`.
Result: kaczmarz-inconsistent -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_add
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
        (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q) * specNorm (pinv A) ^ 2 *
          ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by
  sorry

/-- **From any start, randomized Kaczmarz converges to the least-squares solution nearest the
start, up to the horizon**, for any right-hand side and with no hypothesis: with rows drawn
independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$\mathbf{x}_\star = \mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$ and
$\rho = 1 - (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^{-2}$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \rho^q\|\mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)\|^2 +
(1 - \rho^q)\,\|\mathbf{A}^{+}\|_2^2\,\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{b}\|^2\,.$$
From $\mathbf{x}_0 = \mathbf{0}$ the limit is $\mathbf{A}^{+}\mathbf{b}$.
[ZouziasFreris2013, Theorem 7], there from $\mathbf{x}_0 = \mathbf{0}$;
[LeventhalLewis2010, Theorem 4.7], there for consistent systems.
Port of `NLAlib.Kaczmarz.expErr_zero_le_moorePenroseInverse`.
Result: kaczmarz-rank-deficient -/
theorem integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (x₀ + pinv A *ᵥ (b - A *ᵥ x₀) - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q *
          ‖WithLp.toLp 2 (pinv A *ᵥ (b - A *ᵥ x₀))‖ ^ 2 +
        (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q) * specNorm (pinv A) ^ 2 *
          ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ ^ 2 := by
  sorry

/-- **Randomized Kaczmarz for a consistent system converges to the projection of the start onto
the solution set**: with rows drawn independently from the squared-row-norm law, row $i$ with
probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$\mathbf{b} \in \operatorname{range}\mathbf{A}$ and
$\mathbf{x}_\star = \mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \Bigl(1 - \frac{1}{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2}
\Bigr)^q\|\mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)\|^2\,.$$
[LeventhalLewis2010, Theorem 4.7]; [ZouziasFreris2013, Theorem 4], there from
$\mathbf{x}_0 = \mathbf{0}$. -/
theorem integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le_of_mem_range
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (hb : b ∈ LinearMap.range A.mulVecLin) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (x₀ + pinv A *ᵥ (b - A *ᵥ x₀) - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q *
        ‖WithLp.toLp 2 (pinv A *ᵥ (b - A *ᵥ x₀))‖ ^ 2 := by
  sorry

/-- **Randomized Kaczmarz converges linearly in expectation** (Strohmer–Vershynin), any rank: for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of
$\mathbf{A}$ and rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \Bigl(1 - \frac{1}{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2}
\Bigr)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,,$$
the rate in $[0, 1)$ for $\mathbf{A} \ne \mathbf{0}$. [StrohmerVershynin2009, Theorem 2]; there
for full column rank, where the row-space hypothesis is empty. [ZouziasFreris2013, Theorem 4].
Port of `NLAlib.integral_sqErr_kaczmarz_le_frobPseudoConditionNumber`. Iteration count:
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le`.
Result: randomized-kaczmarz -/
theorem integral_norm_sub_kaczmarzIterate_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  sorry

/-- **Randomized Kaczmarz, iteration count**: for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\mathbf{x}_\star - \mathbf{x}_0$ in the row space of $\mathbf{A}$, rows drawn independently from
the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$
the rows of $\mathbf{A}$), $\varepsilon > 0$ and
$q \ge \|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
[StrohmerVershynin2009, (11)], which counts $2\kappa(\mathbf{A})^2\log(1/\varepsilon)$ steps for
the unsquared error.
Asymptotic form:
`NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_of_mul_log_le`. -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε) ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  sorry

/-- **Randomized Kaczmarz, any right-hand side, iteration count**: for every $\mathbf{x}_\star$
with $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of $\mathbf{A}$, rows drawn independently
from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$\varepsilon > 0$ and
$q \ge \|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2 +
\|\mathbf{A}^{+}\|_2^2\,\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2\,.$$
[ZouziasFreris2013, Theorem 7].
Asymptotic form:
`NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le`. -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε) ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
        specNorm (pinv A) ^ 2 * ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by
  sorry

/-! ### Kaczmarz as sketch-and-project; the mean iterate -/

/-- **The expected projector of a random row**: for weights $p_i$ (any, not necessarily summing
to one), with $\mathbf{a}_i$ the rows of $\mathbf{A}$ and the row-selection sketch
$\mathbf{e}_i^{\mathsf{T}}$,
$$\int \mathbf{P}_{(\mathbf{e}_i^{\mathsf{T}}\mathbf{A})^{\mathsf{H}}}\,dp(i) = \sum_i p_i\,
\mathbf{P}_{\overline{\mathbf{a}_i}}\,,$$
the integral against `NLAlib.samplingMeasure p`, and
$\mathbf{P}_{\overline{\mathbf{a}_i}}$ the projector onto the span of $\overline{\mathbf{a}_i}$.
[StrohmerVershynin2009, (8)], there the random projection $\mathbf{Z}$. -/
theorem integral_rangeProjector_conjTranspose_selectionMatrix_mul [DecidableEq n]
    (A : Matrix m n 𝕜) (p : m → ℝ≥0) :
    ∫ i, rangeProjector ((selectionMatrix fun _ : Unit => i)ᴴ * A)ᴴ ∂samplingMeasure p =
      ∑ i, (p i : ℝ) • rangeProjector (Matrix.replicateCol Unit (star (A i))) := by
  sorry

/-- **The expected projector at squared-row-norm weights** is
$\mathbf{A}^{\mathsf{H}}\mathbf{A}/\|\mathbf{A}\|_{\mathsf{F}}^2$: with $\mathbf{e}_i^{\mathsf{T}}$
the row-selection sketch and the integral against `NLAlib.samplingMeasure` at the weights
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\int \mathbf{P}_{(\mathbf{e}_i^{\mathsf{T}}\mathbf{A})^{\mathsf{H}}}\,dp(i) =
\frac{\mathbf{A}^{\mathsf{H}}\mathbf{A}}{\|\mathbf{A}\|_{\mathsf{F}}^2}\,.$$
[StrohmerVershynin2009, (7)–(9)]. -/
theorem integral_rangeProjector_conjTranspose_selectionMatrix_mul_rowNormSqDistribution
    [DecidableEq n] (A : Matrix m n 𝕜) :
    ∫ i, rangeProjector ((selectionMatrix fun _ : Unit => i)ᴴ * A)ᴴ
        ∂samplingMeasure (rowNormSqDistribution A) = (frobNorm A ^ 2)⁻¹ • (Aᴴ * A) := by
  sorry

/-- **Randomized Kaczmarz with any row probabilities**, consistent systems: for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of
$\mathbf{A}$, rows drawn independently from the squared-row-norm law, row $i$ with probability $p_i$
($\sum_i p_i = 1$), and $\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq \sum_i p_i
\mathbf{P}_{\overline{\mathbf{a}_i}}$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$,
$\mathbf{P}_{\overline{\mathbf{a}_i}}$ the projector onto the span of $\overline{\mathbf{a}_i}$),
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le (1 - \lambda)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
Uniform sampling is $p_i = 1/\lvert m \rvert$. The sketch-and-project theorem
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le` with row-selection sketches.
[GowerRichtarik2015, §3.3]. -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_of_hasLaw_samplingMeasure
    {p : m → ℝ≥0} (hp : ∑ i, p i = 1)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure p) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) {lam : ℝ}
    (hlam : lam • rangeProjector Aᴴ ≤
      ∑ i, (p i : ℝ) • rangeProjector (Matrix.replicateCol Unit (star (A i)))) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - lam) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  sorry

/-- **The mean Kaczmarz iterate is Landweber's iteration** with step
$\|\mathbf{A}\|_{\mathsf{F}}^{-2}$, for any right-hand side: for $\mathbf{A} \ne \mathbf{0}$ and
rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\mathbb{E}[\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q)] =
\mathsf{richardsonIterate}(\mathbf{A}, \|\mathbf{A}\|_{\mathsf{F}}^{-2}\mathbf{A}^{\mathsf{H}},
\mathbf{b}, \mathbf{x}_0, q)\,,$$
that is $\mathbb{E}[\mathbf{x}_{q+1}] = \mathbb{E}[\mathbf{x}_q] +
\|\mathbf{A}\|_{\mathsf{F}}^{-2}\mathbf{A}^{\mathsf{H}}(\mathbf{b} -
\mathbf{A}\mathbb{E}[\mathbf{x}_q])$. For $\mathbf{A} = \mathbf{0}$ the law is the zero measure and
the identity fails. The averaged form of the observation that randomized Kaczmarz is stochastic
gradient descent on the least-squares objective [MaNeedellRamdas2015, §2.1]. Its
normal-equations form is `NLAlib.integral_kaczmarzIterate`. -/
theorem integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose (hA : A ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, kaczmarzIterate A (ι ω) b x₀ q ∂μ =
      richardsonIterate A ((frobNorm A ^ 2)⁻¹ • Aᴴ) b x₀ q := by
  sorry

/-- **The mean Kaczmarz iterate is Richardson's iteration on the normal equations** with step
$\|\mathbf{A}\|_{\mathsf{F}}^{-2}$, for any right-hand side: for $\mathbf{A} \ne \mathbf{0}$ and
rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\mathbb{E}[\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q)] =
\mathsf{richardsonIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \|\mathbf{A}\|_{\mathsf{F}}^{-2}
\mathbf{I}, \mathbf{A}^{\mathsf{H}}\mathbf{b}, \mathbf{x}_0, q)\,.$$
The Landweber form, which avoids $\mathbf{A}^{\mathsf{H}}\mathbf{A}$, is
`NLAlib.integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose`.
[MaNeedellRamdas2015, §2.1], the stochastic-gradient reading. -/
theorem integral_kaczmarzIterate [DecidableEq n] (hA : A ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, kaczmarzIterate A (ι ω) b x₀ q ∂μ =
      richardsonIterate (Aᴴ * A) ((frobNorm A ^ 2)⁻¹ • (1 : Matrix n n 𝕜)) (Aᴴ *ᵥ b) x₀ q := by
  sorry

end Random

/-! ### Asymptotic iteration counts -/

/-- **$O(\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon))$ iterations
suffice for randomized Kaczmarz**: there are absolute constants $C, \varepsilon_0 > 0$ such that
for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space
of $\mathbf{A}$, rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
The constants come before every dimension. Proved from
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le` with $C = 1$ and
$\varepsilon_0 = 1$. [StrohmerVershynin2009, (11)], which counts
$2\kappa(\mathbf{A})^2\log(1/\varepsilon)$ steps for the unsquared error.
Asymptotic: NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le
Result: randomized-kaczmarz -/
theorem exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_of_mul_log_le :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
      [Fintype n] [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m]
      (μ : Measure Ω) (A : Matrix m n 𝕜) (b : m → 𝕜) (ι : Ω → ℕ → m) (xs x₀ : n → 𝕜) (q : ℕ)
      (ε : ℝ),
      HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ →
      A *ᵥ xs = b → xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < ε → ε ≤ ε₀ →
      C * (frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε)) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  sorry

/-- **$O(\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon))$ iterations
suffice for randomized Kaczmarz to reach its horizon**, for any right-hand side: there are
absolute constants $C, \varepsilon_0 > 0$ such that for every $\mathbf{x}_\star$ with
$\mathbf{x}_\star - \mathbf{x}_0$ in the row space of $\mathbf{A}$, rows drawn independently from
the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$
the rows of $\mathbf{A}$), $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2 +
\|\mathbf{A}^{+}\|_2^2\,\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2\,.$$
The constants come before every dimension. Proved from
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le` with $C = 1$ and
$\varepsilon_0 = 1$. [ZouziasFreris2013, Theorem 7].
Asymptotic: NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le
Result: kaczmarz-inconsistent -/
theorem exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
      [Fintype n] [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m]
      (μ : Measure Ω) (A : Matrix m n 𝕜) (b : m → 𝕜) (ι : Ω → ℕ → m) (xs x₀ : n → 𝕜) (q : ℕ)
      (ε : ℝ),
      HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ →
      xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < ε → ε ≤ ε₀ →
      C * (frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε)) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
          specNorm (pinv A) ^ 2 * ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by
  sorry

end NLAlib
