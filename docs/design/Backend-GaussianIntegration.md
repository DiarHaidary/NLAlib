# Design: uniform inverse chi-square moments

Written 2026-10-29 for the backend integration requested by the maintainer. This note concerns
the existing real Gaussian law and its moments. The Probability standing approval in
`docs/PORT_PROBABILITY.md` §1 covers routine decisions without a new carrier, global instance,
or hypothesis interface. It follows the available-model review precedent recorded in
`docs/design/Gaussian-FourthMoments.md`. The requested Opus/Fable aliases were unavailable;
this run used available author and separate independent-review agents, without claiming review
by those unavailable models. The aggregate integration report records the fallback.
The bounded design review accepted these statements;
implementation in both owner files passed targeted single-module Lean checks. Full integration
validation passed in the orchestrator's serial queue; see the BI1 integration report.

The source snapshots are backend `77514ce42a0e437d837797a063ac161f41022730` and frontend
`6491e7528c1b1e68e46301cde6a76ae153e8e834`.

## 1. Scope and consumers

Complete the uniform negative-moment estimates for the squared norm of a standard Gaussian
vector. For dimension $d$ and exponent $q$ with $0 < q \le (d-1)/2$, the backend proves

$$
\bigl(\mathbb{E}\|\mathbf{g}\|^{-2q}\bigr)^{1/q}
\le \frac{3}{d}\quad(d\ge5),\qquad
\bigl(\mathbb{E}\|\mathbf{g}\|^{-2q}\bigr)^{1/q}
\le \frac{4}{d}\quad(d\ge2).
$$

The frontend already has the exact Gamma formula and integrability for every $q<d/2$.
The uniform estimates require the additional half-unit margin; they do not extend uniformly
to $q\uparrow d/2$. The public statements below use unrooted moments. The estimate with
factor three is strict for $q>0$, preserving the backend's strict endpoint. The general
factor-four bound also includes $q=0$, where both sides equal one. For $q>0$ they imply the
displayed forms by raising both sides to $1/q$; no additional rooted or canonical-measure
twin is exported.

Forward consumers are Gaussian pseudoinverse Frobenius moment and polynomial-tail analyses,
including the backend's `RandomMatrix/Gaussian/InverseMoments/FrobeniusMoments.lean` and
`DeviationInputs.lean`, and confidence bounds for randomized range finding. These estimates
complement the existing exact inverse-Wishart and Gaussian block-moment API. They do not change
that API or replace sharper existing bounds.

Wishart density construction, the hard-edge endpoint density argument, complex Gaussian laws,
arbitrary-order Wick pairings, and Gaussian/free comparison are outside this routine extension:
their missing representations and proof infrastructure are separate work. This note does not
change their ledger entries to claim mathematical coverage.

## 2. Objects and interfaces

Reuse `gaussianVector n`, Mathlib `HasLaw`, `Integrable`, real powers, `Real.Gamma`, and
`‖WithLp.toLp 2 (g ω)‖` as the Euclidean norm. Statements quantify over an arbitrary
finite type `n`; no `Fin`-specific interface, raw sum of coordinate squares, or alternate law
is introduced. Gaussian laws stay real as required by Probability D4. `HasLaw` supplies
the probability-measure instance when a proof needs it.

One numerical bound is introduced under CONTRIBUTING §5.2:

```lean
irreducible_def chiSquareInverseMomentFactor : ℝ := 4

theorem chiSquareInverseMomentFactor_pos : 0 < chiSquareInverseMomentFactor

theorem chiSquareInverseMomentFactor_le_four : chiSquareInverseMomentFactor ≤ 4
```

It is an absolute numerical factor, not a mathematical hypothesis interface. Register its body,
hash, and value `4` in `docs/constants.toml`. Its public API permits a later improvement without
renaming the general moment theorem. HMT's small printed factor `3` remains explicit in the
dimension-at-least-five statement. No new Mathlib deviation is introduced.

## 3. Search and reuse

Searched pinned Mathlib's Gaussian distribution files, Gamma files, and
`MeasureTheory/Function/LpSeminorm/{CompareExp,LpNorm}.lean`. No uniform inverse chi-square
estimate of the required shape was found. Mathlib supplies:

- `eLpNorm_le_eLpNorm_of_exponent_le` and `integrable_norm_rpow_of_le` for moment comparison,
  also for positive exponents below one;
- `Real.Gamma_one_half_eq`, `Real.Gamma_add_one`, and `Real.Gamma_mul_Gamma_add_half`;
- `Stirling.le_factorial_stirling`, `Real.exp_one_lt_d9`, and `Real.pi_le_four`.

The current frontend `Probability/Distributions/ChiSquareMoments.lean` supplies:

- `integrable_norm_sq_rpow_of_hasLaw_gaussianVector`, with exponent condition
  `-((Fintype.card n : ℝ) / 2) < s`;
- `integral_norm_sq_rpow_of_hasLaw_gaussianVector`, the exact Gamma formula;
- `integral_norm_sq_inv_of_hasLaw_gaussianVector`, the first inverse moment;
- exact positive moments and Gaussian norm-growth estimates that remain unchanged.

`RandomMatrix/Gaussian/InverseMoments/Spectral.lean` has private moment-comparison helpers.
Probability must not import that higher layer or reference private declarations. Use Mathlib's
comparison API directly for the local Gaussian interpolation. If implementation exposes a
second genuinely shared helper, place it in its mathematical owner and amend this note before
adding it; do not copy the higher-layer helper into a second public interface.

The scalar half-shift Gamma inequality is part of the concurrent Matrix/scalar integration:
`Real.Gamma_add_half_le_mul_sqrt` in
`NLAlib/ForMathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`. The endpoint Gamma estimate
below also belongs in that file and is coordinated with its owner.
The duplicate audit found the same half-shift proof as a private theorem in
`RandomMatrix/Gaussian/InverseMoments/Spectral.lean`. That private copy is removed; its two
consumers explicitly use `Real.Gamma_add_half_le_mul_sqrt` through a direct import of the
shared scalar file. This changes no public statement or theorem count.

## 4. Exact statements and file ownership

### Scalar dependency

`NLAlib/ForMathlib/Analysis/SpecialFunctions/Gamma/Basic.lean` owns the following scalar result:

```lean
theorem Real.sqrt_pi_div_rpow_mul_Gamma_lt_rpow {d : ℕ} (hd : 5 ≤ d) :
    Real.sqrt Real.pi /
        (2 ^ (((d : ℝ) - 1) / 2) * Real.Gamma ((d : ℝ) / 2)) <
      (3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2)
```

This is the backend's private `sqrt_pi_div_lt_rpow`, in
`Probability/ChiSquare/ChiSquare.lean`, made public in its scalar home because a second
probability file can use it. Its proof uses the Gamma half-shift bound, duplication, and
factorial Stirling. The backend's long proof must be split into helpers of at most 80 lines;
the elementary exponential estimate is private to this file. The scalar dependency is part
of the design review, not an implicit request to copy its source unchanged.

### Probability owner

Add the numerical factor, its two API lemmas, and the following results to the existing
`NLAlib/Probability/Distributions/ChiSquareMoments.lean`, after the exact inverse moment and
before Gaussian norm growth. Add a public import of the scalar Gamma file; its lower-layer
placement respects P1. No new topic file or aggregator is needed.

Common variables:

```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {n : Type*} [Fintype n] {g : Ω → n → ℝ}
```

The HMT bound, uniformly in the exponent:

```lean
theorem integral_norm_sq_rpow_lt_of_five_le_card_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hn : 5 ≤ Fintype.card n)
    {q : ℝ} (hq : 0 < q) (hqd : 2 * q + 1 ≤ (Fintype.card n : ℝ)) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ <
      (3 / (Fintype.card n : ℝ)) ^ q
```

The all-dimension bound:

```lean
theorem integral_norm_sq_rpow_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ)
    {q : ℝ} (hq : 0 ≤ q) (hqd : 2 * q + 1 ≤ (Fintype.card n : ℝ)) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ ≤
      (chiSquareInverseMomentFactor / (Fintype.card n : ℝ)) ^ q
```

The existing `integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg` at exponent `-q` is
the integrability companion for both bounds: `hqd` gives its strict integrability condition.
No separate integrability theorem with an equivalent signature is added. The module summary
and each bound's docstring must name that companion so the Bochner-integral convention is clear.

Names follow N2/N3/N6/N9/N13: the integral statistic is first, `norm_sq_rpow` describes the
integrand, the relation precedes hypotheses, the law has its required suffix, and the stronger
sibling is distinguished by its dimension hypothesis rather than by a quality adjective.

## 5. Proof plan and boundary cases

1. Prove the scalar Gamma endpoint in its owner file. Use the backend mathematics but split
   the long polynomial inequality into reusable local steps; preserve its strict inequality.
2. At $r=(d-1)/2$ and $d\ge5$, instantiate the existing exact Gamma formula with exponent
   $-r$, simplify the numerator to $\Gamma(1/2)$, and apply the scalar endpoint bound.
3. For $0<q\le r$, apply probability-space moment monotonicity to
   $(\|\mathbf{g}\|^2)^{-1}$. Use `HasLaw` for probability and existing real-power
   integrability. Strictness comes from the endpoint, not from moment monotonicity. The scalar
   root transformations use nonnegative integrals and positive $q,r$.
4. Handle $q=0$ directly for the general bound. For $q>0$, its dimension hypothesis forces
   $d\ge2$. Dimensions two, three, and four reduce respectively to endpoint exponents
   $1/2,1,3/2$, the Gamma formula, and $\pi\le4$. All larger dimensions use step 3.
5. Give the resulting all-dimension bound through the registered factor. Its docstring displays
   the current value four with the required value marker and explains that this extends HMT's
   dimension-at-least-five estimate to small dimensions.

The empty index type never satisfies `hqd`; dimension one only permits $q=0$. At $g(ω)=0$,
Lean's inverse/negative-power conventions agree with the existing exact-moment theorem and do
not define the integral; for positive dimension this is a null event under the Gaussian law.
The probability space need not have a global `IsProbabilityMeasure` instance in the statement.
No real/complex twin, `Fin` reindexing theorem, or measure/`HasLaw` twin is exported.

The estimate at a lower exponent is part of the single parameterized primary theorem, not an
additional Jensen corollary (T15). The exact existing Gamma formula still applies outside the
uniform range up to the integrability threshold.

## 6. Backend accounting and metadata

The new declarations passed targeted checks; use stage `Backend-GaussianIntegration`
and record the following mappings with a note that the target is unrooted, takes `HasLaw`,
and generalizes the index type. The factor-three target is stronger by strictness; the
factor-four target additionally permits exponent zero:

| Backend declaration | Frontend destination |
|---|---|
| `NLAlib.integral_rpow_inv_sum_sq_gaussianVector_root_le_three_div` | `NLAlib.integral_norm_sq_rpow_lt_of_five_le_card_of_hasLaw_gaussianVector` |
| `NLAlib.integral_rpow_inv_sum_sq_gaussianVector_root_le_four_div` | `NLAlib.integral_norm_sq_rpow_le_of_hasLaw_gaussianVector` |
| `NLAlib.integral_rpow_inv_sum_sq_root_le_four_div_of_hasLaw` | `NLAlib.integral_norm_sq_rpow_le_of_hasLaw_gaussianVector` |
| `NLAlib.integral_rpow_inv_sum_sq_gaussianVector_lt` | `NLAlib.integral_norm_sq_rpow_lt_of_five_le_card_of_hasLaw_gaussianVector` |

The first three source declarations are in `Probability/ChiSquare/NegativeMomentBounds.lean`
and were unaccounted in the comparison. The final one is the ledger-null endpoint in
`Probability/ChiSquare/ChiSquare.lean`: set $q=(d-1)/2$ in the strict target to recover it.
Its old R4 note said that the Frobenius-tail moment step had no consumer; the present task
reopens it as part of the full parameterized family. Private endpoint/interpolation helpers
remain proof material only and do not create backend-public coverage counts.

The HMT theorem docstring cites `[HalkoMartinssonTropp2011, Lemma A.10]`. The locator was checked
against [arXiv:0909.4061v2, p. 67](https://arxiv.org/pdf/0909.4061): the printed range is
$2\le q\le(d-1)/2$, and moment comparison extends its endpoint to the stated full positive
range. The all-dimension extension states its
small-dimension derivation; it does not claim that HMT printed the factor four. Both docstrings
record the source declarations. The integrability API and exact moment formula remain unchanged.
Use the existing chi-square inverse-moment result identifier if one is already registered;
otherwise choose a single reviewed identifier for the general bound, not one per helper.

## 7. Acceptance and handoff

The scalar and probability proofs are separate owned jobs in dependency order. Only the
orchestrator updates the shared ledger, constants registry, and port status after acceptance.
Run targeted module checks with `LEAN_NUM_THREADS=2` and an 8000 MB cap, then the full §9
validation, extraction-backed naming checks, axiom audit, and kernel replay before the PR.
There must be no new `sorry`, axiom, generated-root drift, duplicate interface, or naming
allowlist entry added to silence a real violation.

Review must check the half-unit margin, the distinction between exact Gamma moments and
uniform bounds, the $q=0$ branch, all three small dimensions, and the preservation of strictness
in the scalar endpoint. A semantic restatement is documented in the ledger and never presented
as an unchanged theorem signature. No unresolved maintainer-level interface question is required
for this routine extension; proof-level changes to the signatures above return to the
orchestrator for an amendment.
