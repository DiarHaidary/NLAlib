# Gaussian lower tails and lower coordinate maxima

Status (2026-10-29): Bounded review accepted and implementation completed. Targeted single-module
Lean checks passed; full integration validation passed (see the BI1 integration report).
This is a routine extension of the existing real Gaussian law; it introduces no new
carrier, law, pairing datatype, or matrix process. Source backend commit:
`77514ce42a0e437d837797a063ac161f41022730`.

## Missing content and reuse

The two modules `Probability/Gaussian/Concentration/LowerTail.lean` and
`Probability/Gaussian/Moments/MaximumLower.lean` have five unmatched public theorems in the
coverage inventory. Their content is not supplied by the current Gaussian concentration
upper tails or the Sudakov–Fernique comparison theorem: a concrete independent Gaussian
reference maximum still needs a lower estimate. These proofs need only Mathlib's Gaussian
density, finite product measures, elementary exponentials, and norm integrability. All are
already available in the frontend.

Searches covered Mathlib's `Probability/Distributions/Gaussian`, frontend
`Probability/Distributions/{Gaussian,GaussianConcentration,GaussianComparison,GaussianMoments}`,
and `Probability/SubGaussian/Moments`. The last file supplies upper maximal inequalities;
`GaussianComparison` supplies comparison between Gaussian families. Neither supplies the
positive lower mass or expected maximum below. Mathlib supplies `gaussianReal_apply_eq_integral`,
`integrable_gaussianPDFReal`, finite product probabilities, `Real.one_sub_le_exp_neg`, and
`mul_meas_ge_le_integral_of_nonneg`.

The actual backend consumers include `RandomMatrix/Gaussian/Basic/RowTailLower.lean`,
`RandomMatrix/Gaussian/Moments/SymmetricRowEnergyLower.lean`, and
`Probability/Gaussian/Moments/MaximumLower.lean`. The frontend can use the reference maximum
with its existing Sudakov–Fernique theorem to obtain lower bounds for Gaussian processes.
No symmetric-profile law is introduced as part of these supporting estimates.

## Exact public API

Use the ordinary Pi norm `‖g ω‖` below: it is the **maximum absolute coordinate**, the
$\ell_\infty$ norm. State that explicitly in every docstring, so it cannot be confused with
the Euclidean norm `‖WithLp.toLp 2 (g ω)‖`. This preserves all finite types, including empty
types whose Pi norm is zero.

Common variables are `{Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}`.

Place the scalar lower tail in existing `Probability/Distributions/GaussianConcentration.lean`:

```lean
noncomputable irreducible_def gaussianLowerTailConstant : ℝ :=
  Real.exp (-1) / Real.sqrt (2 * Real.pi)

theorem gaussianLowerTailConstant_pos : 0 < gaussianLowerTailConstant

theorem mul_exp_neg_sq_le_measureReal_abs_ge_of_hasLaw_gaussianReal
    {X : Ω → ℝ} (hX : HasLaw X (gaussianReal 0 1) μ) {t : ℝ} (ht : 0 ≤ t) :
    gaussianLowerTailConstant * Real.exp (-t ^ 2) ≤ μ.real {ω | t ≤ |X ω|}
```

Place the finite product tail and expected maximum in existing
`Probability/Distributions/GaussianMoments.lean`, importing GaussianConcentration. A recursive
import check found that GaussianConcentration does not import GaussianMoments, so this edge
is acyclic.

```lean
variable {n : Type*} [Fintype n] {g : Ω → n → ℝ}

theorem one_sub_exp_le_measureReal_norm_ge_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (t : ℝ) :
    1 - Real.exp (-(Fintype.card n : ℝ) *
      (gaussianReal 0 1).real {x : ℝ | t ≤ |x|}) ≤ μ.real {ω | t ≤ ‖g ω‖}

noncomputable irreducible_def gaussianMaximumLowerConstant : ℝ :=
  1 - Real.exp (-(Real.exp (-1) / Real.sqrt (2 * Real.pi)) / 2)

theorem gaussianMaximumLowerConstant_pos : 0 < gaussianMaximumLowerConstant

theorem mul_sqrt_log_le_integral_norm_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) :
    gaussianMaximumLowerConstant * Real.sqrt (Real.log ((Fintype.card n : ℝ) + 1)) ≤
      ∫ ω, ‖g ω‖ ∂μ
```

The integrability companion is already supplied without a wrapper by
`hg.hasGaussianLaw.integrable.norm`. The current Gaussian law file registers
`isGaussian_gaussianVector`; Mathlib `HasLaw.hasGaussianLaw` and
`HasGaussianLaw.integrable` apply to the complete finite Pi space with its Pi norm.
The expectation docstring names this exact route. Register both numerical constants,
their normalized bodies and docstring value markers in `docs/constants.toml`. The maximum
constant already has a backend name; the scalar constant replaces an unnamed numerical factor.

## Proof and edge cases

Integrate the density on `[t,t+1]` for `t≥0`. On that interval,
$-t^2-1\le-x^2/2$, so the interval mass is at least the named scalar factor times $e^{-t^2}$.
This interval proof remains a private helper; the public scalar event is the absolute tail.

First handle `t≤0` directly: the norm event has probability one, including when the index
type is empty. For `t>0`, independence is part of `gaussianVector n`: the probability that all
coordinates have absolute value below `t` is `(1-q)^d`, where `q` is the scalar absolute tail
and `d=card n`. Apply `(1-q)^d≤exp(-dq)` and take complements. This proves the product-tail
statement in the remaining positive-threshold case, including empty index types. Then use
`t=sqrt(log(d+1))`; for `d≥1`, `d/(d+1)≥1/2` gives the fixed positive tail mass. Integrating
the nonnegative maximum above that threshold proves the expectation bound. For `d=0`, both
sides of the expectation bound are zero. The law hypotheses imply probability measures, so
do not add redundant instances or canonical-measure twins.

The proof of every declaration is split below 80 lines. It uses no new Gaussian comparison
principle. These constants are valid explicit constants, not claims of sharpness. The backend
mentions Latała–van Handel–Youssef as its consuming application; cite the verified backend
provenance without importing an unchecked numbered locator from that paper.

## Accounting

| Backend declaration | Implemented destination |
|---|---|
| `NLAlib.exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_abs_tail` | `NLAlib.mul_exp_neg_sq_le_measureReal_abs_ge_of_hasLaw_gaussianReal` |
| `NLAlib.one_sub_exp_gaussian_tail_le_measure_norm_ge` | `NLAlib.one_sub_exp_le_measureReal_norm_ge_of_hasLaw_gaussianVector` |
| `NLAlib.gaussianMaximumLowerConstant_mul_sqrt_log_le_integral_norm_gaussianVector` | `NLAlib.mul_sqrt_log_le_integral_norm_of_hasLaw_gaussianVector` |
| `NLAlib.gaussianMaximumLowerConstant_pos` | `NLAlib.gaussianMaximumLowerConstant_pos` |

`NLAlib.exp_neg_sq_div_sqrt_two_pi_le_gaussianReal_unit_interval` is retained as the private
density proof and receives an explicit inlining note. Do not map it to the weaker absolute-tail
statement as an equivalent theorem. The four mappings above are new public coverage; the
interval proof is an implementation dependency. The constants do not create an additional
backend-public-theorem count beyond the listed positivity result.

## Review and validation

Bounded review accepted the placements and Pi-norm naming. The implementation passed targeted
Lean checks in the orchestrator's serial queue. Full integration, extraction-backed naming,
constants, axiom and replay checks passed; see the BI1 integration report.
