# Jackson approximation and moment/orthogonal-polynomial roadmap

**J0/J2 proved and independently reviewed, 2026-10-16; stronger-bound integration checks in progress.** The user approved roadmap steps
1 (kernel/damping) and 2 (constructive approximation), using agents. The roadmap and exact J0
proposal passed two bounded independent reviews; root accepted both reviews and clarifications.
The exact J2 implementation addendum below passed bounded independent review; root accepted it. J1 coefficient
regularity, moment comparison and OP retain later exact-design checkpoints; moment/OP proof work
is not authorized here. The current theorem exposes the named factor `jacksonApproximationConstant`, whose value is π,
with uniform error πL/(N+2). The earlier π²L/(2(N+2)) reports below are historical at `c769e96`.
The kernel alone does not complete constructive approximation.
Poly0–3 are complete at `f527934`. Read CONTRIBUTING, PORT_POLYNOMIAL and current status.
Historical model aliases are unavailable; the authorized available-agent fallback continues.

## 1. Goal, order and recommended decisions

The immediate goal is spectral-distribution approximation from exact or noisy moments. Deliver
one constructive Jackson polynomial with BOTH a uniform error guarantee and controlled canonical
Chebyshev coefficients, then transfer moment errors to all Lipschitz test integrals. Finite
orthogonal-polynomial theory subsequently explains positive Gauss/Jacobi/Lanczos constructions
that generate matching moments. General OP existence is not a prerequisite for the first bound.

Recommend these choices for explicit assessment:

* Keep Poly2's full coefficients (unhalved a0), one RCLike spelling and inclusive degree N.
  Add one Jackson damping sequence, one nonnegative periodic kernel and one damped polynomial.
  Damping is defined by zero-padded sine autocorrelation; the customary trigonometric closed
  formula is a representation theorem. This makes positivity structural rather than assumed.
* Expose the proved constructive error πL/(N+2), including N = 0, through the named-bound API.
  The source's π²L/(2(N+2)) is a comparison, not the current library guarantee.
  Do not port the 1430-line sharp-existence sawtooth chain as the first Jackson implementation.
* Introduce one basis-independent degree ≤ N polynomial-integral exactness predicate when the
  measure stage begins, with raw iff and monomial/Chebyshev bridges. Later OP/Gauss uses it too.
* First state universal real Lipschitz test bounds for probability or equal-mass measures. Do not invent a new Wasserstein distance or
  identify a test supremum with a transport metric without a separate reviewed duality theorem.
* Preserve finite-support OPs through finite valid degree caps. Monic scalar foundations first,
  orthonormal normalization/Jacobi adapters later; their exact interface is a future checkpoint.

No pointwise density bound follows just from finitely many moments. Empirical spectra can be
atomic and have no Lebesgue density. A later smoothed-density theorem needs a named smoothing
kernel, bandwidth and regularity/error bound; it is separate from the present distribution result.

## 2. Mathlib/current/prototype search and verified sources

Mathlib first: no Jackson approximation, general measure OP recurrence/CD/Gauss, or Wasserstein/KR
API was found by pinned filename/text searches. Existing Levy–Prokhorov is a different metric.
Reuse `LipschitzOnWith`, `Metric.IsUniformApproxOn`, Bochner integrals, `Measure ℝ`,
`IsFiniteMeasure`/`IsProbabilityMeasure`, `ProbabilityTheory.moment`, polynomial degree/span,
Chebyshev orthogonality, Fourier/Haar integration and Lagrange interpolation. Mathlib's Bernstein
approximation remains the qualitative density theorem, not the quantitative Jackson estimate.

Current NLAlib already supplies the full coefficient/truncation, generic Fourier representation,
reconstruction, real-to-complex embedding, matrix functional-calculus polynomial bounds and
Hermitian spectral/interlacing API. Do not create alternate Chebyshev coefficients or moment
numbers. Compactly supported integrals require actual integrability; total integral defaults do
not make arbitrary polynomial integral manipulations linear.

Prototype Jackson has eleven files/1430 lines plus generic supporting imports. Its real sawtooth
interpolation→zeros/sign→exact L1 norm→AC integration-by-parts→polynomial route is source
material, not a file layout to inherit. It does not furnish the damping-coefficient control needed
for noisy moments. Its aliasing import is not a genuine prerequisite. Prototype quadrature has
spectral-measure, Gauss exactness and decomposition-specific Jacobi results, but no general W1
or standalone finite measure-OP foundation. No fresh prototype build/audit is claimed.

Durable inventory of inspected APIs and source material:

* `Mathlib/Algebra/Polynomial/Sequence.lean`: `Polynomial.Sequence.span_degreeLE`,
  `span_degreeLT`, `linearIndependent` and `basis`; use existing degree bases.
* `Mathlib/MeasureTheory/Function/L2Space.lean`: `MeasureTheory.L2.inner_def`;
  `Mathlib/Analysis/InnerProductSpace/GramSchmidtOrtho.lean`:
  `InnerProductSpace.gramSchmidt_orthogonal`, `span_gramSchmidt_Iic` and
  `gramSchmidtNormed_orthonormal`. These require an actual inner-product space;
  they do not install one on all polynomials for a finite-support measure.
* `Mathlib/LinearAlgebra/Lagrange.lean`: `Lagrange.interpolate`,
  `eval_interpolate_at_node`, `degree_interpolate_lt` and `eq_interpolate`.
* `Mathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Orthogonality.lean`:
  `Polynomial.Chebyshev.integral_measureT_eq_integral_cos` and T-product orthogonality;
  `Mathlib/Analysis/Fourier/AddCircle.lean`: `fourierCoeff_eq_intervalIntegral` and
  summable Fourier reconstruction, already used by NLAlib's `ChebyshevSeries` owner.
* `Mathlib/Probability/Moments/Basic.lean`: `ProbabilityTheory.moment`;
  `MeasureTheory/Function/LocallyIntegrable.lean`: `ContinuousOn.integrableOn_compact`;
  `MeasureTheory/Integral/Bochner/Basic.lean`: integral subtraction and norm bounds.
  FiniteMeasure/ProbabilityMeasure wrappers and finite-measure integral extensionality are
  measure infrastructure, not quantitative Wasserstein duality.
* `Mathlib/MeasureTheory/Integral/IntervalIntegral/AbsolutelyContinuousFun.lean`:
  `AbsolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul` (real functions);
  `MeasureTheory/Function/AbsolutelyContinuous.lean`:
  `LipschitzOnWith.absolutelyContinuousOnInterval`; `Analysis/Calculus/Deriv/Basic.lean`:
  `norm_deriv_le_of_lipschitz`. These inspected APIs inform the later coefficient proof;
  no generic RCLike integration-by-parts theorem is assumed.
* Prototype `Polynomial/BestApproximation/{SawtoothInterpolation,SawtoothDerivative,
  SawtoothZeros,SawtoothSign,SawtoothSquareWave,SawtoothNorm,SquareWave,SineBasis,
  JacksonPeriodic,JacksonPolynomial,Jackson}.lean`, with supporting
  `ForMathlib/Analysis/{Lipschitz,FourierCircle,FourierConvolution}` and
  `Polynomial/Chebyshev/CosineBasis.lean`: inspected material for the alternative
  sharp-existence route, not an approved port list. Jackson/Periodic received full-text inspection;
  the remaining files were inspected at relevant proof sections or declaration/source/import level,
  not subjected to a complete proof audit. ChebyshevAliasing was inspected for dependency scope;
  its import does not make aliasing a Jackson prerequisite. No J0 finite-autocorrelation lemma
  has yet been verified upstream; that search is refreshed before implementation.
* Prototype `Krylov/Quadrature/{SpectralMeasure,GaussQuadrature,LipschitzQuadrature,
  Jacobi}.lean`: inspected finite spectral measures, degree `< 2*q` exactness,
  Jackson error transfer, and decomposition-specific orthogonal polynomials/Jacobi identities.
  These later Matrix/Krylov consumers do not belong in the scalar foundation.

Primary source for the proposed constructive route is EXPLICITLY Chen–Trogdon–Ubaru,
[arXiv:2204.01941v1](https://arxiv.org/abs/2204.01941v1),
[Appendix C, printed pp. 39–43](https://arxiv.org/pdf/2204.01941v1#page=39)
(PDF indices 38–42).
Theorem 38 and Lemmas 44–45 give the full kernel argument and the stronger constant. The later v3
Theorem 3.10 (HTML Theorem 14) instead states a weaker 6/s reading and cites Rivlin for its first
bound; do not conflate the versions. Its coefficient-control argument uses bounded variation and
Trefethen's Theorem 7.1. Formal proofs will retain source relation and generic generalizations.

Verified OP sources: Gautschi2004, *Orthogonal Polynomials: Computation and Approximation*,
§1.1 Thms 1.2/1.6–1.8 (positivity, existence and degree budgets); Thms 1.27/1.29 pp 10–13
(recurrence/normalization), Thm 1.32 p 14 (CD), Thms 1.19–1.20 p 7 (zeros/interlacing),
Thms 1.45–1.46 pp 21–23 (Gauss exactness/weights). GolubMeurant2010 Thms 2.7/2.9/2.11,
2.13–2.14 and 6.1–6.2 corroborate recurrence/CD/zeros/Gauss/Jacobi. Bibliography additions
wait implementation after exact title/edition metadata review; no ledger dispositions now.

## 3. Jackson stages and exact first-stage objects/API

The following J0 signatures are implemented; later stages remain design targets. Stage J0 is the bounded first
implementation checkpoint; J2 follows J0 under the authorized addendum; J1 is deferred until noisy moments needs it.

### J0: damping and positive periodic kernel

New `Polynomial/Approximation/JacksonKernel.lean`, approximately 350–650 lines. The subject is
Jackson's mathematical kernel, not arbitrary circle infrastructure. Three definitions across
J0/J2 constitute the new vocabulary; none is an approximation predicate or alternate coefficient.

Proposed §5.3 vocabulary rows for J0 (record actual implemented bridges in CONTRIBUTING at
mechanical handoff, not before proof):

| New object | Definition and total behavior | Representation bridge |
| --- | --- | --- |
| `jacksonDamping N k : ℝ` | Normalized zero-padded sine autocorrelation; zero for k > N, mass mode 1, values in [0,1] | Raw autocorrelation by definition; `jacksonDamping_eq_closed_form` gives the trigonometric representation. No corresponding pinned Mathlib object was found. |
| `jacksonKernel N θ : ℝ` | Finite even periodic cosine polynomial with coefficients 1 and twice positive-mode damping; nonnegative, integral 2π | `jacksonKernel_eq_norm_sq` identifies the squared-modulus sine polynomial; `integral_jacksonKernel` and `integral_cos_mul_jacksonKernel` fix normalization. It uses ordinary real functions and Mathlib finite sums/exponentials, not a parallel circle-function type. |

```lean
namespace NLAlib
noncomputable def jacksonDamping (N k : ℕ) : ℝ :=
  if k ≤ N then
    (2 / (N + 2 : ℝ)) * ∑ j ∈ Finset.range (N + 1 - k),
      Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2))) *
      Real.sin (((j + k + 1 : ℕ) : ℝ) * (Real.pi / (N + 2)))
  else 0

noncomputable def jacksonKernel (N : ℕ) (θ : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range N,
    jacksonDamping N (k + 1) * Real.cos (((k + 1 : ℕ) : ℝ) * θ)

theorem jacksonDamping_zero (N : ℕ) : jacksonDamping N 0 = 1

theorem jacksonDamping_of_lt {N k : ℕ} (hNk : N < k) : jacksonDamping N k = 0

theorem jacksonDamping_nonneg (N k : ℕ) : 0 ≤ jacksonDamping N k

theorem jacksonDamping_le_one (N k : ℕ) : jacksonDamping N k ≤ 1

theorem jacksonDamping_one (N : ℕ) :
    jacksonDamping N 1 = Real.cos (Real.pi / (N + 2))

theorem jacksonDamping_eq_closed_form {N k : ℕ} (hk : k ≤ N) :
    jacksonDamping N k =
      (((N : ℝ) - k + 2) * Real.cos ((k : ℝ) * (Real.pi / (N + 2))) +
        Real.sin ((k : ℝ) * (Real.pi / (N + 2))) *
          (Real.cos (Real.pi / (N + 2)) / Real.sin (Real.pi / (N + 2)))) / (N + 2)

theorem jacksonKernel_eq_norm_sq (N : ℕ) (θ : ℝ) :
    jacksonKernel N θ = (2 / (N + 2 : ℝ)) *
      ‖∑ j ∈ Finset.range (N + 1),
        (Real.sin (((j + 1 : ℕ) : ℝ) * (Real.pi / (N + 2))) : ℂ) *
          Complex.exp ((((j : ℝ) * θ : ℝ) : ℂ) * Complex.I)‖ ^ 2

theorem jacksonKernel_nonneg (N : ℕ) (θ : ℝ) : 0 ≤ jacksonKernel N θ

theorem jacksonKernel_periodic (N : ℕ) :
    Function.Periodic (jacksonKernel N) (2 * Real.pi)

theorem integral_jacksonKernel (N : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, jacksonKernel N θ) = 2 * Real.pi

theorem integral_cos_mul_jacksonKernel (N : ℕ) :
    (∫ θ in (-Real.pi)..Real.pi, Real.cos θ * jacksonKernel N θ) =
      2 * Real.pi * Real.cos (Real.pi / (N + 2))
end NLAlib
```

Totalization: weights beyond N are zero; all denominators N+2 are positive; no artificial
positive-N premise. N = 0 has damping at zero equal to 1, kernel equal to 1, and first cosine moment equal to 0, consistent with
cos(π/2) = 0. Nonnegativity is distinct from strict positivity; kernel zeros are allowed.
Source normalization: Appendix C writes u = 1/2 + ∑ρ_k cos(kθ); our K = 2u is the same kernel
normalized for (2π)⁻¹∫K = 1. Full a0 coefficients and the earlier contour/Fourier normalizations
are unchanged. The polynomial convolution representation requires at least interval continuity
(or the reviewed integrability hypotheses); total integral defaults do not justify an unconditional
linearity/reconstruction theorem.
The square-norm identity and mass/first-moment facts are useful to the subsequent generic
convolution and positive KPM consumers, so they are public rather than hidden assumptions.

Proof route: normalized sine-vector energy is (N+2)/2. Finite autocorrelation expansion gives
the squared-modulus identity; product-to-sum and geometric trigonometric sums give the closed
formula. Cauchy–Schwarz on shifted zero-padded vectors proves damping ≤ 1. Orthogonality gives
mass and first cosine moment. Refresh Mathlib finite geometric sums, Fourier identities and
Chebyshev orthogonality before each proof; do not reprove a generic identity already upstream.
Private finite-sum helpers remain private unless a concrete second consumer justifies a reviewed
ForMathlib home. One file/one capped build at a time, proofs split before about 80 lines.

### J1: canonical coefficient regularity

Extend existing ChebyshevCoefficients owner, with target

```lean
theorem norm_chebyshevCoeff_le_of_lipschitz
    {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (-1 : ℝ) 1)) {k : ℕ} (hk : 0 < k) :
    ‖chebyshevCoeff f k‖ ≤ 4 * (L : ℝ) / (Real.pi * k)
```

This is a proposed later-stage exact target, requiring a bounded proof design before work.
Lipschitz variation ≤ 2L and integration by parts give the real inequality; a norming phase
projection can preserve the constant for RCLike values using the SAME canonical coefficient.
Mathlib's AC product integration-by-parts theorem is currently real-valued. Do not silently take
independent real/imaginary estimates and lose √2, or use a global derivative bound where the
needed local chain estimate is L sinθ. Compare BV versus AC proof cost before fixing helpers.
No custom variation/modulus interface is introduced merely to package this one theorem.

### J2: canonical damped polynomial and constructive error

New `Polynomial/Approximation/Jackson.lean` follows J0; the exact authorized addendum below
supersedes the earlier J1 dependency. J1 is needed only for the later noisy coefficient bound.

```lean
noncomputable def jacksonApprox {𝕜 : Type*} [RCLike 𝕜] (f : ℝ → 𝕜) (N : ℕ) : 𝕜[X] :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C ((jacksonDamping N k : 𝕜) * chebyshevCoeff f k) *
      Polynomial.Chebyshev.T 𝕜 (k : ℤ)
```

The implemented API gives unconditional degree ≤ N, the canonical coefficient identity for every k
(with zero padding beyond N), and the uniform bound
`Metric.IsUniformApproxOn (fun x => (jacksonApprox f N).eval (x : 𝕜)) f (Icc (-1) 1)
 (jacksonApproximationConstant * (L:ℝ) / (N+2))` under `LipschitzOnWith L f (Icc (-1) 1)`.
The positive coefficient bound for this same polynomial follows J1 and damping ≤ 1. No separate
existential witness may replace it in the noisy moment theorem.

Proof: identify the canonical polynomial with normalized convolution by jacksonKernel of f∘cos.
The implemented finite-integral argument needs no Fourier summability. Positivity, kernel mass
and first cosine moment combine with the chord/Young inequality to give πL/(N+2) directly for
RCLike norms. The named factor exposes this stronger value; the source's mean-angle argument
instead gives π²L/(2(N+2)). No new public circle-function object or real-only sawtooth chain is
needed. Affine transport remains a later consumer.

## 4. Moment stages: one exactness spelling and honest noisy weights

Place generic scalar measure/polynomial integration below Matrix, preferably a matching
ForMathlib measure-integral subject after exact upstream search. Moment comparison belongs in `Probability/Moments`, which may import scalar Polynomial;
future ESD adapters belong in `Matrix/Spectral`, algorithms in Krylov/Estimation. Proposed interface:

```lean
namespace MeasureTheory
-- Proposed future interface; exact stage review still required.
def MatchesPolynomialIntegralsUpTo (μ ν : Measure ℝ) (N : ℕ) : Prop :=
  ∀ p : ℝ[X], p.degree ≤ (N : WithBot ℕ) →
    (∫ x, p.eval x ∂μ) = ∫ x, p.eval x ∂ν
end MeasureTheory
```

N is an inclusive degree budget, matching existing approximation theorems; an n-node Gauss rule
will conclude budget 2n−1 only when n > 0. At n = 0, degree < 2n exactness is vacuous whereas
budget (2n−1) = 0 demands mass equality; never convert with natural subtraction unconditionally. Keep the predicate basis-independent; ship raw iff,
apply/mono/refl/symm/trans and monomial/Chebyshev equivalences under finite measures with common
AE compact-interval support. On the normalized interval, the Chebyshev bridge uses T_k(x); on [a,b], the normalized
Chebyshev moments use T_k((2x−a−b)/(b−a)). These are different test polynomials.
Existing `ProbabilityTheory.moment id k μ` is the monomial bridge,
not a new moment object. The predicate itself is total; equivalences/integral manipulations carry
integrability hypotheses, supplied by compact support. No exactness wrapper unique to OP/Gauss.

M0: finite measure polynomial approximation transfer. For p approximating f within ε on the
common AE support, bound test-integral discrepancy by
`(μ.real univ + ν.real univ)*ε + |∫p dμ−∫p dν|`. Use `[IsFiniteMeasure]` and an integrable/
continuous-on-compact test interface, not raw total-integral linearity. Probability specialization
is twoε. Include mass/constant mode; N = 0 exactness is equality of total mass, not an empty condition.

M1: exact and noisy normalized spectral distributions. For two probability measures AE-supported
on [-1,1], exact budget N matching gives every L-Lipschitz test discrepancy ≤ 2πL/(N+2).
The SAME Jackson polynomial gives the proposed noisy headline

`|∫f dμ−∫f dν| ≤ 2πL/(N+2) + (4L/π) * ∑ k∈range N, |Δ_(k+1)|/(k+1)`,

where Δj is the actual Chebyshev-T integral discrepancy. Probability mass cancels k = 0 even for
unbounded additive constants in f. Exact monomial and Chebyshev matching are equivalent; noisy
monomial errors are NOT interchangeable with Δj without change-of-basis coefficient costs.
Affine support uses Tj((2x−a−b)/(b−a)), not Tj(x), and rescales the Lipschitz/error factors.

M2: optional sharper weighted ℓ2 bounds. Musco–Musco–Rosenblatt–Singh, COLT2025/PMLR291,
Theorem 1 and Lemma 13 give a source-backed target, but require a separate coefficient-energy
bound `∑ j²|a_j|²≤C L²`. Damping contraction then preserves that energy. Coefficientwise 1/j
alone costs √N under Cauchy–Schwarz and cannot justify a dimension-free noisy term. Do not
expand the first stage to claim this result without its own exact proof review.

W1 decision: no pinned transport/KR API was found. Recommend publish universal Lipschitz test
bounds first, clearly described as spectral-distribution observables. If a named distance is wanted,
review an anchored dual-supremum definition with finiteness/mass conditions separately, or implement
CDF-L1/coupling duality with endpoint/atom conventions. Never call an unproved identification a
bridge. ESD construction later requires nonempty matrix index type for probability normalization;
vector spectral measures have mass ‖v‖² and should use the finite-mass version instead.

## 5. OP sequence: future exact-design checkpoints

OP0: scalar finite orthogonality, uniqueness and moment invariance.
Moment matching transfers integrals for given polynomials. Equality of canonically constructed
orthogonal polynomials additionally needs the relevant uniqueness and nondegeneracy theorem. Use positive `Measure ℝ` and
real polynomials; integrability, monicity, degree and positive norm are separate facts. Recommend
one lower-degree orthogonality interface, assessed before implementation, rather than an infinite
OP-space object. Monic foundations avoid square-root/sign choices. A supplied finite family is
enough initially; Gram–Schmidt construction in a finite degree submodule/L² comes later. Never
install an arbitrary-measure inner product globally on all polynomials.

OP1: recurrence and CD. Valid finite degree ranges, positive previous norms, then one normalization
bridge to orthonormal polynomials with positive leading coefficients. Initial orthonormal constant
is 1/√mass, not 1 without probability normalization. Prove multiplied Christoffel–Darboux first,
valid also on the diagonal; quotient/derivative forms are optional consumers, not separate objects.

OP2: Gauss exactness/weights. Given an orthogonal monic degree-n node polynomial with n distinct
real nodes, integrated Lagrange weights yield exactness through 2n−1 and positive weights under
appropriate nondegeneracy. A rule with positive total mass requires n > 0; the zero-node
case must not silently claim mass preservation. Root location/interlacing may be a preceding bounded stage or supplied
hypotheses initially. Do not assert failure at degree 2n unless independently justified.

OP3: Jacobi/spectral measures/Lanczos. Scalar theory stays below Matrix. Matrix Jacobi facts use
existing eigenvalue/CFC/interlacing machinery; Lanczos adapters stay in Krylov. Gaussian weights
are measure mass times squared first normalized eigenvector coordinate. No reverse scalar import.

Finite-support warning: N distinct positive atoms permit positive norms only through degree N−1;
a terminal monic nodal polynomial of degree N can have zero norm and endpoint roots. Infinite
positive-definite assumptions, interior-root conclusions and division by terminal norms would
exclude the intended spectral measures. Moment budgets also differ: degree-n orthogonality needs
matching through 2n−1, squared norm through 2n, recurrence diagonal numerator through 2n + 1.

These are proposal-level later statements, not approved exact APIs or proof claims. Finite-family
interface and monic/orthonormal construction choices return for user assessment when their exact
stage is designed; they do not block Jackson or the real-test moment comparison stage.

## 6. Approval and validation contract

The approved objects are autocorrelation-primary damping, zero-padding, a public nonnegative
periodic kernel and the canonical damped polynomial. J0/J2 are user-authorized and independently
reviewed. The later moment exactness convention remains a proposal. Root briefs one file at a
time, refreshes searches, requests bounded
review, and runs capped logged target/single-file checks sequentially. Full gates run once at
stage handoff, with genuine prototype mappings and object/interface/deviation records. The original
design checkpoint made no builds, source edits, ledger changes or commits. Implementation state
is recorded in `docs/port/status.md`. The sharp sawtooth route,
modulus-of-continuity framework, pointwise density and full infinite moment problem are deferred.

## 7. Authorized J2 implementation addendum (2026-10-16)

The user approved roadmap steps 1 and 2: J0 kernel/damping and the constructive Jackson
approximation. This authorizes the canonical polynomial and the RCLike uniform bound below,
subject to bounded implementation-design review and sequential file handoff. Ordinary elaboration
choices do not require renewed user approval. Moment comparison and OP implementation remain
unapproved; J1 coefficient regularity and any later noisy-moment headline retain their own exact
design checkpoint. The kernel alone does not complete constructive approximation.

### Ordering and public vocabulary

Implement J0 first, then J2. J1 is not a dependency of the uniform Jackson estimate: positivity,
normalization and the first cosine moment of J0's kernel prove it directly. Defer the Lipschitz
`4L/(πk)` coefficient-regularity theorem until noisy moment comparison needs it. J2 nevertheless
exports the exact canonical coefficient identity and damping contraction, so that later J1 uses
the same polynomial rather than a separately chosen witness.

The file `NLAlib/Polynomial/Approximation/Jackson.lean` owns the six constructive API
declarations below plus the implemented named factor and its two support lemmas (later amendment). It imports the J0 owner and existing Chebyshev coefficient/polynomial
machinery, with only the particular integration/trigonometric files actually required. Do not
import an analytic-ellipse owner: the hypotheses and proof are Lipschitz, not analytic.

| New object | Definition and total behavior | Representation bridge |
| --- | --- | --- |
| `jacksonApprox f N : 𝕜[X]` | Inclusive finite sum with J0 damping and Poly2 full coefficients; arbitrary real-input RCLike-valued f; each coefficient retains its total Bochner convention | `eval_jacksonApprox` and `chebyshevCoeff_jacksonApprox`; under interval continuity, a private normalized-kernel convolution identity |

Together with J0's damping and kernel, this is the third approved vocabulary object; no new
approximation predicate or coefficient definition. It is a damped approximant, not an alternate
name for `chebyshevTrunc`: damping is generally not 1 at positive modes. It reproduces constants
but does not generally reproduce every polynomial of degree ≤ N.

### Exact J2 signatures

These signatures reflect the implemented constructive API; the named factor is defined in the
stronger-bound amendment below. The standard local
open declarations provide polynomial, interval-integral and measure notation.

```lean
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def jacksonApprox (f : ℝ → 𝕜) (N : ℕ) : 𝕜[X] :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C ((jacksonDamping N k : 𝕜) * chebyshevCoeff f k) *
      Polynomial.Chebyshev.T 𝕜 (k : ℤ)

theorem eval_jacksonApprox (f : ℝ → 𝕜) (N : ℕ) (x : 𝕜) :
    (jacksonApprox f N).eval x = ∑ k ∈ Finset.range (N + 1),
      (jacksonDamping N k : 𝕜) * chebyshevCoeff f k *
        (Polynomial.Chebyshev.T 𝕜 (k : ℤ)).eval x

theorem degree_jacksonApprox_le (f : ℝ → 𝕜) (N : ℕ) :
    (jacksonApprox f N).degree ≤ (N : WithBot ℕ)

theorem chebyshevCoeff_jacksonApprox (f : ℝ → 𝕜) (N k : ℕ) :
    chebyshevCoeff (fun x : ℝ => (jacksonApprox f N).eval (x : 𝕜)) k =
      (jacksonDamping N k : 𝕜) * chebyshevCoeff f k

theorem norm_chebyshevCoeff_jacksonApprox_le (f : ℝ → 𝕜) (N k : ℕ) :
    ‖chebyshevCoeff (fun x : ℝ => (jacksonApprox f N).eval (x : 𝕜)) k‖ ≤
      ‖chebyshevCoeff f k‖

theorem isUniformApproxOn_jacksonApprox_of_lipschitz
    {f : ℝ → 𝕜} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    Metric.IsUniformApproxOn
      (fun x : ℝ => (jacksonApprox f N).eval (x : 𝕜)) f (Set.Icc (-1 : ℝ) 1)
      (jacksonApproximationConstant * (L : ℝ) / (N + 2 : ℝ))

end NLAlib
```

The coefficient and contraction statements are unconditional in f: their input is a finite
polynomial, whose pullback is continuous/integrable, even when the original f is not. Every k is
covered; for k > N, basis orthogonality and J0's zero padding make both sides zero. This does not
assert unconditional additivity of arbitrary total integrals.

### Proof decomposition and checked upstream reuse

1. Evaluation and degree use the existing Poly2 pattern: `Polynomial.eval_finsetSum`,
   `eval_mul`, `eval_C`, `degree_sum_le`, `degree_smul_le` and `Polynomial.Chebyshev.degree_T`.
   The coefficient identity uses the existing `chebyshevCoeff_add`,
   `chebyshevCoeff_const_mul` and `chebyshevCoeff_eval_T`, with actual integrability of each
   finite polynomial summand. J0's nonnegative damping bounded by one gives norm contraction.
   If a finite-sum coefficient helper is useful only here, keep it private rather than exporting
   another coefficient interface.
2. Under `ContinuousOn f (Icc (-1) 1)`, identify evaluation at `cos θ` with
   `(2π)⁻¹ ∫ t in -π..π, (jacksonKernel N t : 𝕜) * f (cos (θ-t))`.
   This is a private representation lemma, not a public circle-function object. Expand the finite
   kernel, use cosine addition, evenness and periodic interval translation, and identify the full
   coefficients. Existing `fourierCoeff_cosinePullback_eq_chebyshevCoeff` is an alternative
   complex dictionary if it shortens the bridge, but an infinite Fourier reconstruction theorem
   or coefficient summability must not be assumed for arbitrary Lipschitz f.
3. Lipschitz continuity supplies the preceding continuity and integrability. Kernel mass rewrites
   the difference as an integral against `f(cos θ) - f(cos(θ-t))`. Norm it directly over RCLike
   values: no real/imaginary split and no √2 loss. Both cosine values lie in the interval.
4. Prefer the direct chord estimate
   `|cos(θ-t) - cos θ|² ≤ 2 * (1 - cos t)`. Cosine addition, `sin²+cos²=1` and the real
   two-coordinate Cauchy–Schwarz inequality prove it without shifting a periodic Lipschitz
   hypothesis. Weighted Cauchy–Schwarz with J0's nonnegative kernel, mass and first cosine moment
   then gives error at most `L * sqrt(2 * (1 - cos β))`, where `β = π/(N+2)`. Since this equals
   `2L * sin(β/2) ≤ Lβ`, the private proof actually obtains `πL/(N+2)`. The implemented Young majorant gives the same `πL/(N+2)` estimate without square roots.
   Expose it through the named factor, preserving the existing theorem name and hypotheses.
   This is a direct estimate for the existing construction, not a claim of a new source theorem.
   If the chord-square formalization proves unexpectedly expensive, the checked alternative
   `Real.cos_le_one_sub_mul_cos_sq` on `[-π,π]` bounds the mean angle instead and gives the
   approved constant directly. Keep either weighted integral/second-moment helper private;
   a new reusable public analysis lemma needs separate placement review.
5. Every x in the closed segment is `cos(arccos x)`. Finish with the existing real arccos endpoint
   identities. The conclusion is exactly the shared Metric bound, with no existence wrapper or
   second “real Jackson” theorem.

Pinned relevant files/names additionally checked for this addendum:
`MeasureTheory/Integral/IntervalIntegral/Periodic.lean`,
`Function.Periodic.intervalIntegral_add_eq`; interval-integral Basic,
`intervalIntegral.norm_integral_le_integral_norm` and `norm_integral_le_of_norm_le`;
`MeasureTheory/Integral/Bochner/Basic.lean`, `integral_mul_le_Lp_mul_Lq_of_nonneg`;
`Analysis/SpecialFunctions/Trigonometric/Bounds.lean`,
`Real.abs_cos_sub_cos_le`, `Real.cos_le_one_sub_mul_cos_sq`, `Real.sin_le`.
Refresh exact applicability before proving; do not introduce a general convolution framework merely
for this finite kernel. A local period witness must reuse the existing upstream witness if the
AddCircle route is used, following Poly3; no generated public Fact duplicates.

### Edges, source and handoff

N = 0 gives the constant coefficient and the current bound πL/2. L = 0 gives zero error for
functions constant on the segment, without a separate global constancy premise. Zero polynomials
and vanished coefficients are covered by the WithBot degree bound. The theorem includes both
endpoints and complex-valued functions with the same constant. Values outside the segment are
irrelevant; no global Lipschitz premise, analytic extension or boundary assumption is introduced.

Source: [Chen–Trogdon–Ubaru, arXiv:2204.01941v1, Appendix C](https://arxiv.org/pdf/2204.01941v1#page=39),
Theorem 38 and Lemmas 44–45. Preserve the checked source-to-library kernel normalization
`K = 2u` and full unhalved constant coefficient. The generic RCLike norm proof is an explicit
extension of the source argument. The preferred chord estimate improves an internal bound while
now exposed through the named public factor; it is not attributed as a separately printed source
result. The bibliography key is `ChenTrogdonUbaru2022`. The later v3 weaker constant is not substituted. J2's degree-N
approximation is a mathematical theorem about this explicit polynomial, not a claim of numerical
stability or a sampling algorithm.

After bounded review and the J0 handoff, the proof owner works sequentially on this one file,
logs two-thread target and capped checks, and supplies the mathematical read-back. No moments,
OP, Jackson coefficient regularity, affine consumer or sharp sawtooth theorem is smuggled into
this file. Root may accept routine proof factoring/import adjustments within the authorized scope;
new public vocabulary or changed hypotheses must be reported before implementation. No proof or
build was performed while drafting this addendum.

### Independent vocabulary review (mechanical design pass, 2026-10-16)

The design promotion/review agent independently checked the three proposed §5.3 rows against
pinned Mathlib/current NLAlib and the existing Poly2 objects. They introduce exactly a scalar
multiplier sequence, its positive periodic kernel, and the polynomial formed by damping the
existing canonical coefficients. None duplicates `chebyshevCoeff`, `chebyshevTrunc`,
`Metric.IsUniformApproxOn`, `Polynomial.Chebyshev.T` or a verified Mathlib Jackson object.
The autocorrelation/closed-form and kernel/squared-modulus equalities are representation bridges;
finite coefficient identification is the polynomial bridge. No fictional Mathlib alias or new
coefficient/approximation predicate is proposed. The rows retain raw definitions and totalization,
with regularity assumptions only on the convolution/error theorems. This satisfies the requested
second vocabulary review at design level; actual bridge elaboration and CONTRIBUTING entries
remain mechanical handoff work after proofs. No CONTRIBUTING or Lean edits were made here.

### Prototype ledger assessment for J0/J2

The integration review found no genuine new prototype mapping for these stages. The prototype's
`jacksonPeriodicApprox` is a derivative/sawtooth operator, not the sine-autocorrelation damping
operator. Its `exists_degree_le_abs_sub_eval_le_jackson_unit` has error πL/(2(n+1)), and
`exists_degree_le_abs_sub_eval_le_jackson_interval` has the corresponding sharper affine rate.
Neither statement is replaced by J2's approved constructive bound; both remain outstanding.
The circle representation and sawtooth helper chain also have no newly exported counterparts
here. Preserve the ledger rather than mark a stronger theorem ported under a weaker statement.
J0/J2 are new constructive source additions; existing Poly2 coefficient mappings stay unchanged.
This assessment is checked against the final public declarations at stage handoff.

### J0 implementation read-back and independent approval (2026-10-16)

Independently approved against the final 429-line source: exactly two definitions and eleven
public theorems implement the approved damping/kernel API. Zero padding, nonnegative damping
bounded by one, constant mode one and first mode cos(π/(N+2)) hold for every N, including zero.
The closed-form bridge has the exact source normalization. The kernel is 2π-periodic, has mass
2π and first cosine moment 2π cos(π/(N+2)); its normalized squared-modulus identity proves
nonnegativity for every angle. Thus the library kernel is precisely twice the source's
half-constant kernel. All denominators are valid at N=0; no positivity or cutoff premise was
silently omitted.

Mathlib reuse includes `Real.sin_mul_sum_cos`, finite-sum reindexing and interval trigonometric
integrals. The reviewed `norm_add_square` helper directly wraps `Complex.normSq_add`; the
remaining finite triangular expansion is private proof plumbing, with no exact upstream
counterpart found. Proofs stay below 80 lines, the file stays within budget, and no extra public
object, global instance, file-level option, axiom or sorry was introduced. The module lists its
main results and cites the version-specific primary source.

Both actual CONTRIBUTING rows were independently reviewed: damping and nonnegative periodic
kernel accurately state their total construction and proved representation/normalization bridges;
neither duplicates a canonical coefficient, approximation predicate or existing Mathlib object.
No genuine prototype ledger mapping applies: the sharper derivative/sawtooth chain remains
unported, and existing mappings are unchanged.

Proof-owner target build passed (2716 jobs), and the capped single-file check passed, both without
warnings: `/tmp/nlalib-j0-checks/jackson-kernel-build.log` and `jackson-kernel-lean.log`.
This reviewer ran no build and changed only this design note. Root's integration audit is separate;
no full-stage gate or J2 completion is claimed here.

### Shared finite-coefficient API amendment (2026-10-16)

Final integration review found the same finite coefficient induction in two actual consumers:
`ChebyshevTruncation.coeff_finite_T_expansion` (its inner arbitrary-finset lemma) and
`Jackson.coeff_finite_expansion`. Their only representation difference is scalar multiplication
versus multiplication by `Polynomial.C`. Under CONTRIBUTING's shared-helper rule, factor this
once into the existing canonical coefficient owner, rather than keep both private copies.
This is a routine shared API addition within the authorized implementation, not a new object,
approximation interface or coefficient spelling.

Home: `NLAlib/Polynomial/Approximation/ChebyshevCoefficients.lean`, immediately after
`chebyshevCoeff_eval_T`, with a brief finite-orthogonality docstring and source relation.

```lean
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

theorem chebyshevCoeff_sum_smul_T (c : ℕ → 𝕜) (s : Finset ℕ) (k : ℕ) :
    chebyshevCoeff (fun x : ℝ =>
      (∑ j ∈ s, c j • Polynomial.Chebyshev.T 𝕜 (j : ℤ)).eval (x : 𝕜)) k =
      ∑ j ∈ s, c j * (if j = k then 1 else 0)

end NLAlib
```

The input is a finite polynomial expansion; its evaluation is continuous, so no integrability
assumption on c is needed. Reuse `chebyshevCoeff_add`, unconditional scalar multiplication and
basis identification in the single Finset induction. This does not assert coefficient additivity
for arbitrary nonintegrable function inputs. No additional generic sum-integral interface is needed.

Consumer changes: remove the private finite-coefficient induction from ChebyshevTruncation and
apply the public theorem at `Finset.range (N+1)` in polynomial reproduction; preserve its
signature and finite-span proof. Remove the private Jackson induction; rewrite polynomial C-times-T
summands using `Polynomial.C_mul'` to the scalar-multiplication representation and apply the
same owner theorem. All six J2 public signatures remain unchanged. The combined integration
contribution gains one public owner theorem; do not continue reporting only the six J2 statements
as the total number of additions. No existing object or prototype disposition changes.

The proof owner checks the owner and both consumers sequentially with capped logged checks
before final handoff. Final review confirms exactly one induction remains. Also change the J2
headline's fractional error conclusion to a displayed `\frac` formula under CONTRIBUTING §6,
without changing its value. No Lean edit or build was performed while proposing this amendment.

### Historical J2 and shared-owner read-back at `c769e96` (2026-10-16)

Independently approved against the final source and affected-target logs. Jackson is 337 lines
with exactly its six approved public declarations. The shared coefficient owner adds exactly one
public theorem, `chebyshevCoeff_sum_smul_T`; its single Finset induction replaces both consumer
copies. Truncation reproduction and all prior public signatures are unchanged, and Jackson
rewrites C-times-T to scalar multiplication before using the same theorem. Combined J0/J2
integration therefore adds twenty public declarations: thirteen J0, six J2 and one owner theorem.

The canonical polynomial has unconditional degree ≤ N and exactly the damped canonical
coefficients at every index, zero-padded beyond N. Those unconditional facts integrate finite
continuous polynomials, not arbitrary nonintegrable input functions. Convolution and integral
splitting explicitly obtain integrability from continuity of the cosine pullback. The main theorem
requires only interval Lipschitz continuity, with no summability, analytic extension or global
Lipschitz premise. It covers RCLike values, both endpoints, N=0 and L=0. Positive kernel mass and
the first cosine moment, combined with the chord/Young inequality, prove the private bound
πL/(N+2); the comparison 2≤π yields exactly the approved public bound π²L/(2(N+2)). The
stronger intermediate is not exported or attributed as a separate printed theorem.

Module documentation, version-specific Chen–Trogdon–Ubaru source relation and
`Result: jackson-lipschitz` are consistent with this constructive theorem. The headline fraction
is now displayed with `\frac` as required. All three actual CONTRIBUTING rows accurately describe
the implemented damping, kernel and canonical polynomial with their proved bridges. They do not
duplicate the coefficient, truncation, Metric predicate or a Mathlib object. No genuine new
prototype ledger dispositions apply; the sharper sawtooth/existential guarantees remain unmapped.
No additional public object, global instance, file-level option, axiom or sorry was introduced.

Final affected-target builds passed without warnings: coefficient owner 2717 jobs, truncation
2718 jobs, Jackson 2749 jobs. All three capped Lean logs are empty. Evidence:
`/tmp/nlalib-j2-checks/06-coefficient-owner-{build,lean}.log`,
`07-truncation-reuse-{build,lean}.log`, `08-jackson-reuse-{build,lean}.log`.
The reviewer ran no builds and changed only this design note. Root's combined integration gates
are separate; no full-gate success, moment/OP completion or commit is claimed by this read-back.

### Historical combined integration validation at `c769e96` (2026-10-16)

Root accepted the independent J0, J2, shared-owner and vocabulary reviews. Full `NLAlib` and
`NLAlibScaffold` build passes 3909 jobs without warnings. Root import checks pass. Axiom audit:
7502 reachable declarations, zero violations. Fourteen linters: 5112 declarations plus 2390
generated, zero errors. Duplicate report: 4707 library theorems, zero classes. Proof reuse confirms
the canonical coefficient owner, kernel API and upstream trigonometric/integral facts are used.
References (57 keys), constants (25), and LaTeX (18193 spans) pass. Target and capped file checks
were clean before integration; no scaffold or sorry is added.

Logs: `/tmp/nlalib-jackson-{build,audit,lint,duplicates,reuse,imports,explore}.log`.
Explorer extraction `/tmp/nlalib-jackson-explore.json` has 315 modules and 3530 declarations,
including the exact generic theorem and `Result: jackson-lipschitz`; source fingerprints match.
This checks extraction and document metadata, not a deployed Explorer site.

The textual ledger checker still reports the known pre-existing `IsSVD.eq` field false positive
(documented in Sketching-REPORT); `/tmp/nlalib-jackson-field-check.log` confirms the field exists
in Lean. The ledger is deliberately unchanged for the source-coverage reasons above. No
moment-comparison, coefficient-regularity or OP theorem is claimed by completion of J0/J2.

### Stronger public Jackson bound amendment (2026-10-16)

The user explicitly requests exposing the stronger bound already proved internally. This
supersedes the earlier decision to discard the private πL/(N+2) estimate by comparison with the
source's π²L/(2(N+2)). Keep the existing theorem name, hypotheses and
`Result: jackson-lipschitz`; no second “improved” theorem or weaker replacement is introduced.
This is authorized work, not a request for renewed approval of ordinary elaboration choices.

**Numerical-bound contract.** CONTRIBUTING §5.2 rule 2 permits a small literal source constant
when the proof reaches it, but requires any other proof-derived constant or tail function to be
named. The source factor here is π²/2; the new factor π is a proof improvement, even though π
itself is the existing mathematical constant `Real.pi`. Naming the bound does not redefine π:
it gives the algorithm's numerical guarantee an improvement-stable API. This is the actual HMT
Gaussian pseudoinverse precedent: `gaussianPinvSpecNormBound` in
`RandomMatrix/Gaussian/InverseMoments/Spectral.lean` names the proof-derived
`e * sqrt((k+r-1)/2)/(k-r)`, documents its difference from HMT's `e*sqrt(k)/(k-r)`,
and supplies an explicit comparison and constants-registry entry. The algorithm theorem must
not hide the stronger result merely to retain the source's printed literal.

Recommended minimal owner API, in `Polynomial/Approximation/Jackson.lean` before its main
uniform theorem (ordinary local openings omitted):

```lean
namespace NLAlib

noncomputable irreducible_def jacksonApproximationConstant : ℝ := Real.pi

theorem jacksonApproximationConstant_pos : 0 < jacksonApproximationConstant

theorem jacksonApproximationConstant_le : jacksonApproximationConstant ≤ Real.pi

theorem isUniformApproxOn_jacksonApprox_of_lipschitz
    {𝕜 : Type*} [RCLike 𝕜] {f : ℝ → 𝕜} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    Metric.IsUniformApproxOn
      (fun x : ℝ => (jacksonApprox f N).eval (x : 𝕜)) f (Set.Icc (-1 : ℝ) 1)
      (jacksonApproximationConstant * (L : ℝ) / (N + 2 : ℝ))

end NLAlib
```

The numerical factor is a bound definition under rule 2, not a fourth approximation object or
new hypothesis interface. Its current body is exactly π; consumers use positivity and the
one-sided comparison rather than unfold it. The current-value comparison ≤π remains valid if
the factor improves. No equality-to-π API is needed. The body equation generated by the
irreducible definition serves the owner proof. Future same-shape improvements update the body,
comparison proof, current-value formulas and registry without renaming the main theorem.

Proposed numerical-bound vocabulary row for the same implementation handoff:

| Numerical bound | Current body and role | Consumer API and bridge |
| --- | --- | --- |
| Jackson approximation factor | `jacksonApproximationConstant : ℝ := Real.pi`; named proof-derived factor, support declaration rather than an Explorer headline | `jacksonApproximationConstant_pos`, `jacksonApproximationConstant_le`; upper comparison to the current explicit value π, documented source factor π²/2 |

No explicit Result or Concept metadata is added to this numerical factor. Existing Explorer
support-role behavior keeps it out of the headline catalogue; the existing Jackson result's
mathematical display shows the numeric π factor. No Explorer configuration or frontend edit is
needed. The registry records the numerical bound, independently of result membership.

Proof change is minimal: the existing `norm_error_cos` already proves
`L * (π/(N+2))`. Rewrite the bound's body only in the owner proof and rearrange multiplication;
remove the final weakening via `Real.two_le_pi`. No kernel, polynomial, coefficient or
hypothesis changes. Positivity and comparison are direct `Real.pi_pos`/reflexivity bridges.
At N=0 the public current error is πL/2; L=0 remains zero. No affine or noisy-moment claim is
added. The library value is strictly below the source factor for positive L, but no optimality or
sharpness is claimed: it is the estimate this chord/Young proof reaches.

The source docstring still cites `ChenTrogdonUbaru2022`, v1 Appendix C/Theorem 38, then
explicitly distinguishes its π²L/(2(N+2)) from our proved πL/(N+2). The main displayed
conclusion shows the **current value**, not a bare C:

```text
... the uniform error is at most <!-- value jacksonApproximationConstant -->
$$\frac{\pi L}{N+2}.$$
```

The constant's docstring also displays π and states both source and proved factors. Its
registry entry is included in `docs/constants.toml`, with body `Real.pi`, current
LaTeX `\pi` and the script-generated body hash; do not invent a source value or bypass markers
because π is familiar. Update explanatory prose that currently calls π²L/(2(N+2)) the final
library guarantee, while retaining that expression when identifying the source or earlier
reviewed design. Target/capped checks and final root documentation/constants/reuse gates must
refer to the final stronger statement; no builds were run for this design amendment.

**Proposed targeted CONTRIBUTING clarification.** Existing numerical-bound rules clearly settle
naming and comparison, but do not explicitly require exposing an already-proved stronger result.
A single sentence after rule 2's opening paragraph would make the user's requested lasting
practice explicit: “When a proof establishes a stronger bound under the same hypotheses, expose
that bound through the existing theorem and named-bound API; record its relation to the source
rather than weaken it solely to reproduce the source's constant or an earlier approved draft.
Changes to hypotheses, mathematical scope or public interfaces retain their normal design review.” No broader policy or automatic
new objects are needed. That narrow clarification is now applied in CONTRIBUTING; this documentation pass makes no
further CONTRIBUTING edits.

### Current stronger-bound implementation status and background (2026-10-16)

The stronger named factor is implemented and target/capped checks are clean. The current main
theorem has the same name, hypotheses and result identifier, with bound
`jacksonApproximationConstant * L / (N+2)` and current displayed value πL/(N+2).
The registry now has 26 numerical bounds, and CONTRIBUTING includes the targeted stronger-bound
clarification and factor row. Combined final gates pass, as recorded below; the historical `c769e96` counts
and checks above describe the previous statement.
There are 23 explicit new public declarations in the combined work: thirteen J0, six constructive
J2, one shared coefficient theorem, and the factor with its two lemmas. The irreducible definition
also generates machinery, counted according to the existing audit/extraction policy.

This follows the actual HMT Gaussian pseudoinverse precedent described above: preserve the
proved stronger value through a stable named bound and display its current number, while stating
the source comparison honestly. The value π here is what this proof establishes, not an optimal
Jackson constant and not a novelty claim. The earlier library source guarantee was π²/2 times
L/(N+2); no weaker theorem is retained merely to reproduce that value.

User-supplied background references are `Rivlin1981`, *An Introduction to the Approximation of
Functions*, and [Shah–Urschel–West2026, version 2](https://arxiv.org/abs/2607.23375v2),
*What is Jackson's constant?*. The latter's §1/Theorem 1.3 discusses a sharper asymptotic constant
approximately 2.4306 with a remainder term. That asymptotic theorem and its remainder are not
proved here, and must not be conflated with the present finite-N constructive bound or cited as
its formal proof. These references supply background for further exact-design work.

The proposed, still unimplemented M1 targets now use approximation contribution **2πL/(N+2)**
for probability measures, plus `(4L/π) * ∑ |Δ_k|/k` if the deferred J1 coefficient bound is proved
for the same polynomial. The named factor would express this as twice its value in Lean. Neither
an exact/noisy moment theorem, W1 transport identification nor pointwise spectral density estimate
is claimed by the current Jackson implementation.

### Stronger-bound final validation and read-back (2026-10-16)

Root accepted the bounded design review and independent actual-source/registry review. From the
Lean statement: the same canonical polynomial approximates any RCLike-valued function that is
L-Lipschitz on [-1,1], with degree budget N and error bounded by the named factor times L/(N+2).
The factor currently equals π and its public comparison is ≤π; N=0, L=0 and endpoints remain
covered. The proof uses the established chord/Young estimate directly, with no final weakening.
The existing result identifier and theorem name are preserved. The source docstring correctly
identifies the source factor π²/2 and the new proved value; no optimality/novelty claim is made.

Final full build passes 3909 jobs with no warnings; target and capped file checks are clean.
Axiom audit: 7501 reachable declarations, zero violations. Fourteen linters: 5116 declarations
plus 2385 generated, zero errors. Duplicate report: 4709 theorems, zero classes. Root imports,
proof reuse, references (59 keys), constants (26), and LaTeX (18199 spans) pass. Logs are
`/tmp/nlalib-jackson-stronger-{target,lean,build,audit,lint,duplicates,reuse,imports,explore}.log`.

Explorer extraction `/tmp/nlalib-jackson-stronger-explore.json` contains 315 modules and 3534
declarations; all source fingerprints match. The headline doc displays πL/(N+2) and the factor
is marked `explorerRole: support`. This is extraction validation, not deployment. The existing
prototype ledger is unchanged: this improvement still does not port the sharper existential
sawtooth theorem. No new scaffold, sorry, axiom, coefficient spelling or approximation object.
