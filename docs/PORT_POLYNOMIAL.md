# Port brief: polynomial approximation

**Roadmap and Poly0 implementation approved by the user, 2026-10-16.** Implement Poly0
sequentially under its reviewed design. Later stages still require exact designs; important lasting
interface or scope decisions return to the user for assessment. Approval does not fix every future API.

Read CONTRIBUTING in full, this brief, the relevant stage design and `docs/port/status.md`.
The historical model aliases are unavailable; the previously authorized available-agent fallback
continues for inventory and bounded independent design review. The root orchestrator owns decisions.

## 0. Goal and scope

Build the scalar polynomial foundation that numerical linear algebra users apply: Chebyshev
polynomials and filters, actual function approximation by Chebyshev series/truncations,
interpolation and extremal/derivative estimates. Polynomial convergence bounds then transfer
through the existing Matrix functional-calculus API into later Krylov and quadrature results.
This is not a port of the prototype directory structure or all its helper lemmas.

Prominent deliverables, not just residual filters:

* Chebyshev growth and normalized residuals, with the familiar geometric CG/Chebyshev rate.
* Coefficients with one documented zero-mode normalization, series reconstruction, finite
  truncation and geometric error for functions holomorphic and bounded on a Bernstein ellipse.
* Explicit inverse, monomial and exponential approximation, including usable degree/error bounds.
* Chebyshev interpolation and analytic interpolation error; sharp extremal/minimax and polynomial
  derivative estimates; Lipschitz/Jackson approximation when its larger proof infrastructure is ready.

Not this round: matrix polynomial evaluation (already Matrix), Krylov spaces/iterations/CG/Lanczos,
quadrature algorithms, random-start probability, rational approximation, multivariate polynomials,
finite precision, certified numerical coefficient computation, or a general approximation-space
framework. Future topics can extend the logical families below after their own designs.

## 1. Evidence and proof status

Inventory order was Mathlib → current NLAlib → prototype, followed by downstream consumers.
The pinned Mathlib is the authority, not recollection of an older upstream version.

* Current NLAlib has no Polynomial or Krylov directory. `Matrix/Functions/Polynomial.lean` already
  uses `Polynomial.aeval` and supplies scalar-spectrum/interval bounds for matrix norm and energy,
  `cfc` approximation transfer, and SVD/Gram polynomial-filter intertwining. Reuse its proofs and names; the proposed uniform-approximation interface below migrates the
  existing `specNorm_cfc_sub_aeval_le` hypothesis in place.
* Prototype `/home/tyler/Documents/prove2me/lean/NLAlib/Polynomial`: 32 files, 4861 source lines,
  241 lexical top-level declaration matches. Counts include helpers and are not a public-API
  target. Its 38-file transitive local closure has no lexical `sorry`/`admit`/`axiom` holes and
  no missing local imports. This means source-complete, **not** compiled or kernel-audited here.
* Six supporting prototype ForMathlib files: Algebra/{Intervals,Polynomial} and
  Analysis/{Calculus/IteratedDeriv,FourierCircle,FourierConvolution,Lipschitz}. Each requires a
  fresh upstream/reuse search; no blanket import or copy of that infrastructure is authorized.
* Independent inventory and API assessment agree that much prototype Core/interpolation material
  is already upstream. Existing downstream CG/Lanczos recurrence gaps belong to Krylov, not to
  this scalar plan. No claims about all prototype consumers being complete are made.

## 2. Upstream/current reuse, representative exact API

Use Mathlib's `Polynomial.Chebyshev.T` and `U`, indexed by integers; NLA degree parameters may be
natural numbers cast to that index. No parallel Chebyshev polynomial definitions or real/complex twins.

| Topic | Existing API to reuse |
| --- | --- |
| Recurrence, parity, degree, derivative | RingTheory.Polynomial.Chebyshev: `degree_T`, `natDegree_T`, `T_eval_one`, `T_eval_neg`, `T_derivative_eq_U`, `derivative_T_eval_one` |
| Trigonometric/hyperbolic forms | Chebyshev.Basic: `T_real_cos`, `T_real_cosh` and complex counterparts |
| Interval bounds and roots/extrema | RootsExtrema: `abs_eval_T_real_le_one`, `one_le_eval_T_real`, `roots_T_real_nodup`, roots/local extrema, `abs_iterate_derivative_T_real_le` |
| Weighted orthogonality | Orthogonality: `measureT`, cosine integral change of variables and `integral_eval_T_real_mul_eval_T_real_measureT` |
| Extremal behavior | Extremal: `leadingCoeff_le_of_forall_abs_le_one`, `eval_iterate_derivative_le_of_forall_abs_le_one` for x≥1; k=0 already yields external one-sided growth comparison |
| Interpolation algebra | `Lagrange.interpolate`, `degree_interpolate_lt`, `eval_interpolate_at_node`, `funEquivDegreeLT`, nodal polynomials and barycentric weights |
| Qualitative approximation | Mathlib Stone–Weierstrass/Bernstein approximation should remain the qualitative API; do not reconstruct density just to prove a quantitative estimate |
| Matrix application | Current `Matrix.IsHermitian.specNorm_aeval_le`, quadratic-form bounds and `NLAlib.specNorm_cfc_sub_aeval_le` |

Missing after targeted search, rather than assumed absent: radical closed-form growth estimates,
normalized residual/filter API, global interior Markov and weighted Bernstein inequalities,
quantitative Chebyshev-series/ellipse approximation as needed by this round. Exact stage designs
must repeat the statement-level search; “missing” here is an inventory finding, not permission
for an independent proof of an upstream result found later. T-specific derivative bounds are
already upstream consequences and are not the full general-polynomial Markov theorem.

## 3. Logical organization and provisional stages

All scalar topics are layer 0; no imports of Matrix, Probability or Krylov. Generic upstream
additions live in ForMathlib under the Mathlib subject/namespace they extend. The application-facing
normalized residual/filter and approximation objects live under Polynomial. No stage-named files,
per-directory aggregators or paper-named declarations. Final file splits belong to each design.

Provisional stable families:

```
ForMathlib/Topology/UniformSpace/UniformApproximation.lean  generic metric interface
ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/…
Polynomial/
  Chebyshev/       normalized residuals and polynomial filters
  Approximation/  coefficient/series/truncation, analytic and special-function approximation
  Interpolation/  Chebyshev node models and interpolation error
  Inequalities/   extremal/derivative results not better housed upstream
```

These directories are a topic map, not a commitment to build empty files. Keep upstream-only
facts out of bespoke NLAlib wrappers; keep matrix applications in Matrix/Krylov. In particular,
“Bernstein” has three meanings here: derivative inequality, analytic ellipse, and Mathlib's
Bernstein polynomial density theorem. Use filenames/titles that distinguish them.

Recommended order (decision for the user):

| Stage | Coherent deliverable | Main dependencies/consumers | Effort/risk |
| --- | --- | --- | --- |
| Poly0 Scalar interface/growth/residual/inverse | Proposed uniform approximation predicate and Matrix hypothesis migration; missing growth; normalized residual and inverse existence | Mathlib Chebyshev; CG, Chebyshev iteration and inverse actions | Small–medium; interface review is the main risk |
| Poly1 Minimax follow-up | Outside modulus comparison, exact residual and monic minimax | Mathlib Extremal and Poly0; optimization reading of CG residual | Small–medium; largely upstream corollaries |
| Poly2 Chebyshev series | Canonical RCLike coefficients, finite degree-N truncation, linearity, basis identification and polynomial reproduction | Mathlib orthogonality/sequence spans; Poly3/Poly4 | Complete; no arbitrary-function reconstruction claimed |
| Poly3 Analytic approximation | Bernstein ellipse geometry, cosine-to-Fourier/contour bridges, coefficient decay, series reconstruction, geometric truncation error and interval rescaling | Poly2 and complex analysis; matrix-function/Lanczos analytic quadrature | High; ellipse/Fourier boundary conditions |
| Poly4 Explicit approximants | Compressed monomials and exponential with degree/error bounds | Poly0/Poly2 as needed; exp-action and quadrature | Medium; cutoff and quantitative tail bookkeeping |
| Poly5 Interpolation | Node-polynomial identities and derivative remainder; Chebyshev extrema-grid aliasing/analytic interpolation | Mathlib Lagrange; roots vs extrema kept distinct; Poly3 for analytic error | Medium–high; nodes and analytic/derivative routes |
| Poly6 Derivative inequalities | Schur/Bernstein/Markov with sharp constants and interval forms | Mathlib Extremal and Poly5 lemmas only where needed | Medium–high; interior/endpoint distinctions |
| Poly7 Jackson/Lipschitz | Quantitative interval approximation with degree/error estimate | Periodic convolution/trigonometric-polynomial infrastructure; Lipschitz quadrature | Highest; substantial reusable analysis infrastructure |
| Poly8 Specialized filters | Amplifier and even second-kind/weighted filters, only with a concrete consumer | Poly0/growth; block Krylov/eigenvalue approximation | Medium; specialized consumer and source review |

This order deliberately puts real function approximation near the front rather than treating it
as an optional appendix to CG. Poly0 includes inverse approximation, including degree-zero edge cases. The small exact-minimax
follow-up is placed before analytic series; Poly5/Poly6 may move earlier for a reviewed consumer. Work remains sequential:
only the currently designed, approved stage is implemented, one file at a time. A changed ordering
is recorded before implementation, not used to launch all stages concurrently.

## 4. Prototype coverage and intended reuse decisions

Paths below are relative to prototype Polynomial. These are proposed dispositions, **not ledger
entries or final name mappings**. Eliminate duplicates against the pinned Mathlib before proving.

| Prototype topic/material | Key results/objects | Proposed treatment |
| --- | --- | --- |
| Chebyshev/Core (140), Growth (154) | residual/amplifier/zero names; radical T formula, upper/lower growth, monotonicity, gap/condition-number bounds; U and T′ interval bounds | Reuse T/U upstream; port only missing growth, one residual API in Poly0. Defer amplifier; reuse upstream derivative consequences |
| BestApproximation/Minimax (270) | external modulus extremality, residual exact minimax and monic minimality | Reuse Mathlib Extremal; add only scaled/absolute/interval corollaries and residual optimization reading in Poly1 |
| FunctionApproximation/Approximation (137) | residual 2·ratio^q rate, inverse polynomial existence, amplifier API | Poly0 residual/inverse; Poly8 amplifier. Split by mathematical subject, not prototype import history |
| Chebyshev/CosineBasis (42), FunctionApproximation/ChebyshevCoefficients (137) | cosine basis and real coefficient normalization, weighted/cosine integrals, compatibility of analytic/real coefficients | Poly2, with a single public coefficient spelling and complex bridge |
| FunctionApproximation/BernsteinEllipse (169), AnalyticCoefficients (161), AnalyticFourier (210), AnalyticApproximation (226) | open ellipse, coefficient decay, Fourier reconstruction, finite Chebyshev truncation, error 2M·ρ^(−N)/(ρ−1) and interval form | Poly3: preserve holomorphic/bounded **open** ellipse hypotheses; do not add boundary regularity without need |
| FunctionApproximation/Monomial (276), Exponential (281) | compressed x^s approximant, explicit degree/error; exp(−x) approximant and rounded cutoffs | Poly4, review canonical objects and cutoff/degree names; separate named bound from approximation polynomial |
| Interpolation/Lagrange (283) | derivative/Rolle remainder, Chebyshev-root nodal factor and sharp interpolation remainder | Reuse upstream interpolation algebra; only missing analytic/error API in Poly5 |
| Chebyshev/ChebyshevAliasing (94), Interpolation/AnalyticInterpolation (174) | extrema-grid aliasing, analytic interpolation bound with factor 4 | Poly5 after Poly3; distinguish extrema-grid interpolation from roots-grid quadrature/interpolation |
| Chebyshev/Markov (461) | Schur, Bernstein nM/√(1−x²), sharp Markov n²M, interval constant 2n²/(b−a) | Poly6; first-stage T′ bound is not a substitute for this general result |
| BestApproximation/Jackson (79), JacksonPeriodic (100), JacksonPolynomial (169), SineBasis (63), SquareWave (157), Sawtooth* (862 total) | Lipschitz/Jackson theorem through periodic/sawtooth machinery | Poly7, highest infrastructure/port-risk; collapse proof-oriented file fragmentation where budgets allow |
| Chebyshev/EvenChebyshevFilter (172) | contracted U_(2k)(√x)/(2k+1), degree/normalization, weighted squared bounds | Poly8 if eigenvalue/Lanczos consumer is retained; no probability in scalar file |
| Four root aggregator files, wrappers and duplicated aliases | imports and re-exports | Do not port; callers import topic files directly |

The last row means existing prototype aggregators, not new API files. Core may contain an
actual definition absent upstream; “Core overlap” is not a reason to discard the residual itself.
All numerical gaps/changed hypotheses must be stated in the new docstring, not silently lost.

## 5. Downstream consumers checked

* `Krylov/Solvers/{CG,PolynomialMethods}`: residual degree, value 1 at 0 and bound
  `2((√b−√a)/(√b+√a))^q`. Matrix energy bounds already exist in current Matrix.
* `Krylov/MatrixFunctions/FunctionApprox`: inverse and general scalar approximation transfer.
* `Krylov/Quadrature/AnalyticQuadrature`: ellipse approximation; ExponentialQuadrature:
  monomial/exponential; LipschitzQuadrature: Jackson. Quadrature itself stays in Krylov.
* Spectral/eigenvalue and block methods: amplifier and even-filter bounds. A concrete retained
  theorem must justify each specialized filter before Poly8 implementation.
* The deliberate existing Matrix hypothesis migration is the only current consumer change. No Krylov
  namespace or algorithm is invented in this round, and no prototype Krylov proof status is
  promoted to a claim about this repository.

## 6. Sources, conventions and remaining design questions

Primary provenance to check per theorem: Trefethen's Approximation Theory and Approximation
Practice (coefficients/ellipse/truncation/interpolation), Rivlin (Chebyshev growth/extremality/
derivatives), Saad/Greenbaum/Golub–Meurant (normalized residual/inverse and Krylov reading),
Sachdeva–Vishnoi (monomial/exponential compression), a standard Jackson theorem source, and
Musco–Musco or Kuczyński–Woźniakowski only for the specialized filters actually retained.
`Trefethen2019`, `Saad2003` and `KuczynskiWozniakowski1992` already exist in references.bib;
missing entries/printed locators must be verified before citations are added. Prototype source
claims and informal atlas labels are leads, not verified citations.

Statements use Mathlib polynomials, evaluation and interval hypotheses; `degree` (`WithBot ℕ`)
where zero-polynomial behavior matters, and `natDegree` only with the right zero-case treatment.
Do not invent a residual/approximation predicate merely to package degree and one value. New
repeated analytic hypotheses require a deliberate interface decision and constructors/bridges;
no speculative `IsAnalyticApproximation` or custom holomorphy bundle is authorized by this brief.

Approved Poly0 interface decision: `Metric.IsUniformApproxOn g f s ε` means
`∀ x∈s, dist (g x) (f x)≤ε`, with arbitrary domain and pseudometric codomain. Real polynomial
constructors use `p.eval`; the same spelling supports future complex-valued approximation.
Degree, domain topology, continuity, compactness and nonnegative error stay separate. A generic
compact continuous-map distance bridge preserves Mathlib compatibility. The upstream-candidate
home is `ForMathlib/Topology/UniformSpace/UniformApproximation.lean`, extending Mathlib's module,
with no NLAlib alias or empty polynomial interface file. The existing Matrix theorem's raw error
hypothesis is replaced in place; search found no internal callers beyond its declaration/module-doc
entry. Exact signatures and empty-set behavior are in the Poly0 design. This is a significant
§5.4 vocabulary/interface choice approved for Poly0 implementation.

Approved direction and later design checkpoints:

1. Approve the broad coverage and recommended order, starting with bounded Poly0 (including inverse) and then small minimax and actual
   coefficient/analytic approximation?
2. Approve the proposed uniform approximation interface and in-place Matrix hypothesis migration?
3. Approve direct Mathlib reuse and upstream-oriented growth additions, rather than porting Core?
4. Keep Poly6/Poly7/Poly8 in the roadmap, but require their own consumer/source/budget checkpoints before
   implementing the larger derivative/Jackson and specialized-filter stages?
5. Select real-valued versus complex-valued analytic approximation at Poly2/Poly3 design: prototype
   has real-part approximation and explicit compatibility when F is real on the interval. A
   real theorem must not silently claim approximation of an arbitrary complex F.

The first-stage exact signature plan is `docs/design/Polynomial-Chebyshev.md`; both documents
have user approval for the roadmap and Poly0. No public definitions or file APIs beyond the proposed first stage
are fixed by the provisional directory map.

## 7. Completion and handoff contract

For each approved stage: search per statement, design exact signatures and edge cases, bounded
review, then stop if user approval remains required. Skeletons never add sorry to proved files.
Use source proofs only after statement review; no axiom/native_decide or weakened conclusions.
Track genuine prototype dispositions in the ledger only during implementation, with reasons;
this plan changes none. Record names, source relation, constants and proof gaps accurately.

Run capped, logged, sequential target/Lean checks and appropriate root audit/lint/import,
references/constants/LaTeX/reuse/duplicate gates when implementation exists. Named bounds need
registry entries and values in docstrings; numerical algorithm/sample-size readings get useful
explicit/asymptotic pairs where applicable, without calling every degree estimate an algorithm.
A stage report states source reuse, changed hypotheses/constants, anything scaffolded and
remaining consumers. Do not claim proof completion from lexical token scans or green imports.

**Current state: Poly0 complete (`e33043d`), Poly1 complete, and Poly2 complete with independent
reviews and all mechanical gates passed (reports: `docs/design/Polynomial-Minimax.md` and
`docs/design/Polynomial-Series.md`). Poly2 implements the user-approved full coefficients, one
RCLike API and inclusive degree-N truncation. Poly3 extension-interface shape awaits user approval;
dependent implementation remains paused. Later exact APIs retain their design checkpoints.**
