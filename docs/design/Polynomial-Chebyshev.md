# Poly0: uniform approximation, Chebyshev residuals and inverse approximation

**Poly0 implementation approved by the user, 2026-10-16.** Read CONTRIBUTING and
`docs/PORT_POLYNOMIAL.md`. Signatures below are reviewed targets, elaborated file by file.
The previously authorized available-agent fallback continues. Important lasting design changes
return to the user for assessment; later roadmap stages are not blanket approval of exact APIs.

## 0. Consumers and proposed files

The first stage supplies scalar facts needed by later CG/Chebyshev iteration and inverse-action
approximation, without implementing those algorithms. It also tests a shared approximation
interface against the existing Matrix theorem rather than inventing an unconsumed predicate.

Sequential plan, one file at a time:

1. New `ForMathlib/Topology/UniformSpace/UniformApproximation.lean`: the proposed generic
   metric uniform-approximation predicate/API and compact continuous-map distance bridge.
2. New `ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean`: only missing
   external growth facts, in Mathlib's `Polynomial.Chebyshev` namespace, marked upstream candidates.
3. New `Polynomial/Chebyshev/Residual.lean`: the normalized residual and degree/normalization/
   uniform-error API, using Mathlib's T and the interface of item 1.
4. New `ForMathlib/Algebra/Polynomial/Div.lean`: the degree-controlled factorization below,
   in namespace Polynomial, only if the refreshed statement-level search still finds no equivalent.
5. New `Polynomial/Approximation/Inverse.lean`: inverse approximation from the residual and
   factorization; degree-zero behavior included. No otherwise empty `Polynomial/Approximation.lean`
   is introduced: the generic interface has its upstream home.
6. Amend existing `Matrix/Functions/Polynomial.lean`: import item 1 and migrate the existing
   scalar-approximation hypothesis in place. Matrix placement is required by its subject, not
   by a proof import. No duplicate wrapper theorem and no scalar import of Matrix.

Target modest files (roughly 60–250 lines each), no new broad infrastructure or parallel proofs.
Exact minimax is the next small Poly1 stage; general Markov/Jackson is outside Poly0.

## 1. Proposed objects and interface decision

The following is a **approved vocabulary/interface choice**.
A function-level metric predicate accommodates both real polynomial approximation now and
real-domain complex-valued approximation later. Domain topology, degree, continuity, compactness
and ε≥0 remain separate. Its upstream-candidate home extends Mathlib's matching module;
there is no NLAlib alias and no polynomial-specific second spelling.

```lean
namespace Metric

variable {α β : Type*} [PseudoMetricSpace β]
variable {g f : α → β} {s t : Set α} {ε η : ℝ}

def IsUniformApproxOn (g f : α → β) (s : Set α) (ε : ℝ) : Prop :=
  ∀ x ∈ s, dist (g x) (f x) ≤ ε

theorem isUniformApproxOn_iff :
    IsUniformApproxOn g f s ε ↔ ∀ x ∈ s, dist (g x) (f x) ≤ ε

theorem IsUniformApproxOn.apply (h : IsUniformApproxOn g f s ε) {x : α}
    (hx : x ∈ s) : dist (g x) (f x) ≤ ε

theorem IsUniformApproxOn.mono_set (h : IsUniformApproxOn g f s ε) (ht : t ⊆ s) :
    IsUniformApproxOn g f t ε

theorem IsUniformApproxOn.mono_error (h : IsUniformApproxOn g f s ε) (hεη : ε ≤ η) :
    IsUniformApproxOn g f s η

theorem IsUniformApproxOn.nonneg (h : IsUniformApproxOn g f s ε) (hs : s.Nonempty) :
    0 ≤ ε

theorem isUniformApproxOn_iff_dist_le [TopologicalSpace α] [CompactSpace α]
    (g f : C(α, β)) (hε : 0 ≤ ε) :
    IsUniformApproxOn g f Set.univ ε ↔ dist g f ≤ ε

end Metric
```

The iff gives a raw-condition constructor via `.mpr`; `ContinuousMap.dist_le` supplies the
compact bridge directly. Real polynomial constructors use `p.eval` and `Real.dist_eq`.
Scalar and Matrix consumers need no continuous-map packaging or global continuity assumption.
Empty s permits any ε, so `.nonneg` requires a point. This is one predicate with four elementary
operations, not a framework; no custom approximation norm, degree bundle or topology is added.
The genericity costs an explicit `.eval` at polynomial use sites and avoids later real/complex
interface migration. The signatures are design proposals, not elaborated Lean evidence.

Approved §5.3/§5.4 vocabulary rows; CONTRIBUTING registration accompanies implementation:

| Object | Owner and construction | Existing interface / bridge |
|---|---|---|
| `Metric.IsUniformApproxOn g f s ε` | Generic ForMathlib module above; pointwise `dist ≤ ε`, no NLAlib alias | Raw-condition iff; existing `ContinuousMap.dist_le` on compact domains; `Real.dist_eq` for real bounds |
| `NLAlib.chebyshevResidual a b q` | Polynomial/Chebyshev/Residual; scalar normalization and affine composition of Mathlib `Polynomial.Chebyshev.T` | Ordinary polynomial `eval`, `degree`, `C` and `comp`; no duplicate Chebyshev family or residual predicate |

## 2. Missing growth API: exact proposed signatures

Use Mathlib's integer-indexed T, with natural degree parameter cast to ℤ. All declarations below
are in `namespace Polynomial.Chebyshev`, not a parallel NLAlib polynomial family.

```lean
theorem eval_T_real_eq_of_one_le {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (T ℝ (q : ℤ)).eval x =
      ((x + Real.sqrt (x ^ 2 - 1)) ^ q + (x - Real.sqrt (x ^ 2 - 1)) ^ q) / 2

theorem pow_div_two_le_eval_T_real {x : ℝ} (hx : 1 ≤ x) (q : ℕ) :
    (x + Real.sqrt (x ^ 2 - 1)) ^ q / 2 ≤ (T ℝ (q : ℤ)).eval x

theorem sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real {a b : ℝ}
    (ha : 0 < a) (hab : a < b) (q : ℕ) :
    ((Real.sqrt b + Real.sqrt a) / (Real.sqrt b - Real.sqrt a)) ^ q / 2 ≤
      (T ℝ (q : ℤ)).eval ((b + a) / (b - a))
```

Prototype Growth has proofs via Mathlib `T_real_cosh`, `Real.cosh_arcosh`, real logarithm/square-root
identities. The square-root algebra converting the center to the condition ratio can be a
proof-local lemma if only this file needs it. Upper growth, monotonicity and gap filters are
not required to prove these consumers and can wait for a stage that uses them. Do not reprove
`abs_eval_T_real_le_one`, `one_le_eval_T_real`, degree/parity or T′ facts already upstream.

## 3. Normalized residual: exact proposed signatures

In namespace NLAlib, with ordinary Mathlib polynomial operations:

```lean
noncomputable def chebyshevResidual (a b : ℝ) (q : ℕ) : ℝ[X] :=
  Polynomial.C (((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (q : ℤ)).comp
      (Polynomial.C ((b + a) / (b - a)) - Polynomial.C (2 / (b - a)) * Polynomial.X)

theorem degree_chebyshevResidual_le (a b : ℝ) (q : ℕ) :
    (chebyshevResidual a b q).degree ≤ (q : WithBot ℕ)

theorem eval_chebyshevResidual_zero {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    (chebyshevResidual a b q).eval 0 = 1

theorem isUniformApproxOn_chebyshevResidual {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    Metric.IsUniformApproxOn (chebyshevResidual a b q).eval (fun _ => 0) (Set.Icc a b)
      (((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹)

theorem isUniformApproxOn_chebyshevResidual_two_mul_pow {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    Metric.IsUniformApproxOn (chebyshevResidual a b q).eval (fun _ => 0) (Set.Icc a b)
      (2 * ((Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a)) ^ q)
```

A single evaluation-unfolding lemma may be added as basic API if rewriting the definition is
insufficient; it must not introduce another residual definition. Degree is unconditional, while
normalization/error require 0<a<b. The total definition has Lean's inverse/division junk values
outside that regime; document them, without asserting invalid normalization. q=0 gives the
constant 1 in the valid regime, and the geometric bound is the harmless upper bound 2.
No minimax claim is made by these bounds; Poly1 proves optimality separately.

## 4. Inverse construction and degree-zero edge case

Generic factorization, namespace Polynomial (refresh upstream search first):

```lean
theorem exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one
    {R : Type*} [Ring R] [Nontrivial R] {p : R[X]} {q : ℕ}
    (hp : p.degree ≤ (q : WithBot ℕ)) (hp0 : p.eval 0 = 1) :
    ∃ s : R[X], s.degree < (q : WithBot ℕ) ∧ 1 - p = X * s
```

This signature is a proposed generality target, not elaborated evidence; if the pinned degree/eval
API requires a stronger algebraic class, report that in design review before implementation.
Reuse `Polynomial.X_dvd_iff`, `degree_X_mul`/`degree_mul_X` and zero-polynomial degree facts.
The real specialization drives the following NLAlib constructor:

```lean
theorem exists_degree_lt_isUniformApproxOn_inv {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    ∃ p : ℝ[X], p.degree < (q : WithBot ℕ) ∧
      Metric.IsUniformApproxOn p.eval (fun x => x⁻¹) (Set.Icc a b)
        ((2 / a) * ((Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a)) ^ q)
```

Construct p by factoring 1−residual and divide the pointwise residual estimate by x≥a>0.
At q=0 choose the zero polynomial (degree ⊥<0); the error is ≤1/a≤2/a. Do not substitute
`natDegree p < q` or impose an unnecessary positive-q hypothesis. This is genuine function
approximation in the first stage, not just a polynomial bounded near zero.

## 5. Existing Matrix theorem migration, not a second API

Add `public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation` in Matrix/Functions/Polynomial. Preserve the
existing theorem name and conclusion, replacing only its raw scalar error hypothesis:

```lean
theorem specNorm_cfc_sub_aeval_le {𝕜 : Type*} [RCLike 𝕜] {n : Type*}
    [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜} {a b : ℝ}
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ A) (h₂ : A ≤ b • (1 : Matrix n n 𝕜))
    {f : ℝ → ℝ} (p : ℝ[X]) {c : ℝ} (hc : 0 ≤ c)
    (h : Metric.IsUniformApproxOn p.eval f (Set.Icc a b) c) :
    specNorm (cfc f A - Polynomial.aeval A p) ≤ c
```

The source context opens MatrixOrder. Existing proof uses `h.apply`, `Real.dist_eq` and `abs_sub_comm`; its
finite-spectrum reasoning does not require continuity of f on the whole interval. Keep hc for
empty matrix types; empty-domain approximation cannot imply nonnegative c. Search of current
NLAlib/NLAlibScaffold found no callers beyond the declaration and module-doc entry. External
callers migrate their raw bound with `Metric.isUniformApproxOn_iff.mpr` and `Real.dist_eq`, flipping subtraction if
needed. Record this in-place public signature change and the proposed §5.3/§5.4 row explicitly.

## 6. Search/source/review contract

Mathlib search precedes current NLAlib and prototype. Reuse inventory and exact upstream names
are in PORT_POLYNOMIAL §2. No fixed-error function-level metric approximation predicate matching this
API was found; `ContinuousMap.dist_le` is the bridge, not an absent upstream replacement.
Prototype sources read: Polynomial/Chebyshev/{Core,Growth}, BestApproximation/Minimax,
FunctionApproximation/Approximation and the relevant ForMathlib polynomial facts. Reuse only
needed proofs, replacing prototype namespaces, aggregators and duplicate upstream bounds.

First-stage provenance was verified against the local primary source Saad (2003), second edition:
§6.11.1, Eq. (6.111) gives the closed form; the proof of Theorem 6.29, Eqs. (6.124)–(6.128),
gives the lower growth and square-root ratio. Theorem 6.25 and its following corollary give the
normalized residual. Inverse approximation is a scalar corollary using (1−r)/x, not a separately
printed theorem. No unverified Rivlin/Golub–Meurant citation or new bibliography entry is needed.

The user approved the lightweight interface, Matrix migration, upstream homes and bounded stage
order on 2026-10-16. Each proof file receives bounded review and capped sequential checks;
stage wrap-up adds source/reuse read-back and genuine ledger dispositions. Future important
lasting changes require user assessment. No commit is authorized to this proof agent.

## Implementation read-back

2026-10-16, file 1: `Metric.IsUniformApproxOn g f s ε` means exactly pointwise distance at most
ε on s. Raw iff, point evaluation, restriction and error enlargement retain arbitrary domains and
pseudometric codomains. Nonnegativity requires a nonempty set. On a compact topological domain,
the bridge to continuous-map distance retains ε≥0, covering empty domains. The bridge directly
uses Mathlib `ContinuousMap.dist_le`; no prototype proof or new literature result is claimed.
Target build (1910 jobs) and capped single-file check passed without warnings; logs:
`/tmp/nlalib-poly0-checks/01-uniform-build.log`, `01-uniform-lean.log`.

2026-10-16, file 2: the three approved `Polynomial.Chebyshev` statements give the radical
closed form for x≥1, its half-power lower bound, and the square-root condition-ratio lower bound
for 0<a<b, including q=0. Refreshed Mathlib/current searches found no exact overlap. Proofs adapt
the prototype Growth arguments using upstream `T_real_cosh`, `cosh_arcosh` and inverse identities;
the condition-ratio algebra remains proof-local. No extra T/U API or signature amendment.
Target build (2229 jobs) and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly0-checks/02-growth-build.log`, `02-growth-lean.log`.

2026-10-16, file 3: the exact total `chebyshevResidual` definition has unconditional degree≤q;
normalization and both uniform zero-function approximation bounds assume 0<a<b. Both include q=0.
The one permitted evaluation lemma rewrites the definition to the scalar quotient. Degenerate
parameters are documented: a zero normalizing denominator gives the zero polynomial; a=b gives
the constant T_q(0)⁻¹T_q(0). No minimax assertion is added. Refreshed Mathlib/current searches
found no residual API; prototype Core/Minimax/Approximation supplied proof material, now using
the shared metric predicate and upstream interval bound. Only routine beta-reduction/rewrite
elaboration adjustments were needed, with no statement amendment. Target build (2490 jobs)
and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly0-checks/03-residual-build.log`, `03-residual-lean.log`.

2026-10-16, file 4: the factorization retains the approved `[Ring R] [Nontrivial R]`,
including noncommutative coefficients, and q=0 with `WithBot` degree. Fresh upstream/current
search found no exact wrapper. The proof adapts prototype Core using `X_dvd_iff`, `X_mul` and
`degree_mul_X`, so no commutative or domain assumption is added. Target build (1294 jobs)
and capped Lean check passed without warnings; independent review approved. Logs:
`/tmp/nlalib-poly0-checks/04-factorization-build.log`, `04-factorization-lean.log`.

2026-10-16, file 5: inverse approximation has exactly the reviewed existence statement for
every natural q and 0<a<b, with degree<q and error (2/a) times the square-root ratio to power q.
The same factorization proof covers q=0 without a positivity premise or natDegree substitution.
Refreshed upstream/current search found no equivalent quantitative constructor. Prototype
Approximation supplied the scalar algebra; the proof directly consumes files 3–4 and the named
metric interface. Source relation is explicitly a scalar corollary, not a printed standalone
inverse theorem. Target build (2492 jobs) and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly0-checks/05-inverse-build.log`, `05-inverse-lean.log`.

2026-10-16, file 6: `specNorm_cfc_sub_aeval_le` retains its name, matrix/scalar types, Loewner
interval assumptions, nonnegative c and matrix-error conclusion. Its sole public signature change
is the raw scalar error hypothesis becoming `Metric.IsUniformApproxOn p.eval f (Icc a b) c`.
Fresh caller search found only its definition and module-doc entry. The proof uses `h.apply`,
`Real.dist_eq` and `abs_sub_comm`; no global continuity hypothesis or second theorem is added.
Target build (2750 jobs) and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly0-checks/06-matrix-build.log`, `06-matrix-lean.log`.

Proof-stage handoff: all six sequential files are complete without sorry or statement weakening.
All six files have independent mathematical approval. The proof-stage handoff had no active
build; mechanical validation is completed below. No proof-stage commit was made. Later stages retain their design checkpoints.


## Poly0 final validation and review read-back

2026-10-16: complete, no proof changes during mechanical validation. Five new modules are registered
in the generated root; the stage adds 18 public declarations and migrates the existing Matrix
consumer in place. CONTRIBUTING §5.3 records the two approved vocabulary rows. The Mathlib
comparison document records the generic metric predicate and normalized residual as additions
using Mathlib's `dist` and `Chebyshev.T`, with the compact `ContinuousMap.dist_le` bridge;
there is no competing upstream spelling and no numbered deviation was manufactured.

The ledger adds exactly eleven genuine Poly0 prototype mappings. Growth facts move to
`Polynomial.Chebyshev`; residual and inverse pointwise bounds map to the shared metric interface;
the residual factorization generalizes from real coefficients to a nontrivial ring. Every target
resolves in fresh extraction. Minimax, Markov, amplifier, interpolation and series material, and
intermediate helpers without a corresponding completed public declaration, are left untouched.

Read-back from Lean alone: the generic approximation predicate requires only a pseudometric
codomain and controls distance on an arbitrary set. Its nonnegative-error conclusion needs a
point; its compact continuous-map equivalence retains an explicit nonnegative error to cover
empty domains. Chebyshev growth holds for every natural q and x≥1. For 0<a<b the total normalized
residual has degree≤q, value one at zero, and uniform error from zero bounded first by the exact
reciprocal Chebyshev denominator, then by twice the square-root condition ratio to power q.
Factoring 1−residual by X produces a polynomial of degree<q approximating x⁻¹ on [a,b] within
(2/a) times that ratio to power q. At q=0 the zero polynomial has degree ⊥<0, so no positive-q
premise is needed. The Matrix theorem transfers the same named scalar error bound to the spectral
norm of `cfc f A - aeval A p` under the existing Loewner interval assumptions; no global continuity
premise is introduced and the nonnegative matrix-error constant remains explicit.

Primary-source verification used Saad2003, printed pp. 209–210 (§6.11.1, Eq. (6.111), Theorem 6.25
and its following corollary) and p. 215 (proof of Theorem 6.29, Eqs. (6.124)–(6.128)). Inverse
approximation is explicitly a scalar corollary of that construction, not a separately printed
inverse theorem. The reuse report confirms the compact bridge uses `ContinuousMap.dist_le`,
growth uses upstream hyperbolic identities, the geometric residual uses the exact residual and
condition-ratio growth, inverse approximation uses the residual API plus generic factorization,
and the Matrix consumer uses `Metric.IsUniformApproxOn.apply` and the existing spectral transfer.

All required gates passed, sequentially with two Lean threads and logs under
`/tmp/nlalib-poly0-checks`:

* full `NLAlib NLAlibScaffold` build: 3893 jobs, zero warnings;
* both generated-root checks; axiom audit: 7267 declarations, zero violations;
* 14 linters: 5012 declarations plus 2255 generated, zero errors;
* duplicate report: 4613 library theorems, zero classes;
* references: 55 bibliography keys, 40 asymptotic forms, zero problems;
* constants: 25 bounds, 259 markers on 255 spans, zero problems;
* LaTeX: 5483 docstrings and 18083 math spans, zero problems;
* 11 metadata regressions and all 19 reuse targets (18 new declarations plus the Matrix consumer).

Fresh extraction `/tmp/nlalib-poly0-explore.json` contains 306 listed modules and 3484 public
declarations. All 306 source hashes match; all nineteen changed/new targets are present and proved.
The unchanged actual explorer metadata builds strictly against this extraction and matching
sources: 305 visible modules, 248 results and 169 definition bodies enriched, with the existing
32 Rates rows, nine guarantees and three families retained. No explorer metadata, new Rates
family or frontend change was requested or made. `git diff --check` passed. The overlapping
stage script and browser reruns were omitted because the full root and strict rendering gates
already passed. No active validation process or build remains; no commit or push was performed.
The root orchestrator owns the requested commit and subsequent bounded Poly1 design review.

## Upstreaming to Mathlib

Maintainer decision 2026-10-20: the Polynomial layer keeps its headline scalar results (CONTRIBUTING
§2, exempt from P9) on condition that it stays easy to upstream. Rule P11 checks the import
discipline: `NLAlib/Polynomial` imports only Mathlib, `NLAlib.ForMathlib` and `NLAlib.Polynomial`,
and ForMathlib imports only ForMathlib (P1). An audit of the layer and of the ForMathlib files it
imports (2026-10-20) found the frictions below.

**Fixed in the audit** (renames in `docs/renames/2026-10-rules.json`):
`norm_chebyshevCoeff_le_of_differentiableOn`, `isUniformApproxOn_chebyshevTrunc_of_differentiableOn`,
`exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn` (named by the hypothesis, not
`_of_open_ellipse`), `jacksonDamping_of_le` (was `_eq_closed_form`), `chebyshevTrunc_eval` (was
`_eval_eq`; `eq` is omitted, N3), `HasStieltjesMeasure.monotoneOn_id_mul` (was `_mul_self`, which
in Mathlib means `a * a`); two `:= by exact` one-liners made terms; stage comments removed from
ForMathlib `Chebyshev/Growth.lean` and `Convex/SupportingLine.lean`.

**What remains**, with an estimate:

| friction | what Mathlib would want | effort |
|---|---|---|
| `Metric.IsUniformApproxOn` (ForMathlib, 38 uses); 20 of them only say `‖g x‖ ≤ M` | the raw `∀ x ∈ s, ‖g x‖ ≤ M`, as Mathlib's own Chebyshev extremal file states it; or upstream the predicate first in its own PR (it sits in a file about uniform limits) | 1 day |
| namespace `NLAlib` (F4, P8 forbid moving now) | `Polynomial.Chebyshev` (coefficients, truncation, series, Jackson, residual, minimax, extrema, weights), `Lagrange` (`dividedDifference`, the interpolation-error formulas), `MeasureTheory` next to `resolventTransform` (`HasStieltjesMeasure`, renamed, since Mathlib's `StieltjesFunction` is another object), `Polynomial` (`residualMinimax`) | 1–2 days at PR time, with a rename map |
| `𝕜`-valued analytic results through `RCLike.toComplex` | statements for `f : ℝ → ℂ`; `ToComplex` belongs in `Analysis/Complex/Basic` | 0.5–1 day |
| `chebyshevCoeff` is a raw cosine integral | a definition (or at least a bridge) through Mathlib's `Polynomial.Chebyshev.measureT` | bridge 0.5 day, redefinition 1–2 days |
| docstrings: `Result:` lines, value markers, `[Key, label]`, locator notes, references to NLAlib consumers | Mathlib docstrings with `[Key]` and its bibliography | a stripping script, 0.5 day |
| `jacksonApproximationConstant` (`irreducible_def`, value `π`) | inline `π` | trivial |
| ForMathlib `Chebyshev/Growth.lean` carries Tropp–Webber's supporting-line filter (81-line proof, `HasSupportingLineOn`), `Pow/Real` and `Log/Basic` carry application lemmas | split the application material out before the PR | 0.5 day |
| ForMathlib Extremal corollaries are thin (`k = 0` of `eval_iterate_derivative_le_of_forall_abs_le_one`) | merge into the existing Mathlib lemmas | 0.5 day |
| argument order in Growth (`eval_T_real_eq_of_one_le`, `pow_div_two_le_eval_T_real`, …): the degree is not first, as in Mathlib's `one_le_eval_T_real (n) {x} (hx)` | reorder (5 call sites) | 1 hour; a statement change, left for the maintainer |
| small API: `@[simp]` on `chebyshevCoeff_zero`, `chebyshevCoeff_eval_T`, `jacksonDamping_zero`, `jacksonDamping_of_lt`; a shared `RCLike.toComplexLI`; `local instance : Fact (0 < 2 * π)` in place of borrowing Mathlib's local `Polynomial.instTwoPiPos`; a public `Polynomial.degree_lt_of_degree_le_of_coeff_eq_zero`; `chebyshevExtremum_eq_node` to Mathlib's `Polynomial.Chebyshev.node` | as stated | 2 hours, each needs the simp-normal-form and duplicate checks |
| proofs of 47–63 lines (`pullback_coeff_nat`, `isLeast_sum_mul_sq_sub_eval`, `norm_error_cos`, `isLUB_weightedResidualMin`, `sine_correlation`) | shorter, split lemmas | 1–2 days |

**An upstream PR series** would go bottom up: (1) the Div and degree lemmas into
`Algebra/Polynomial`, nodal weights and `Lagrange.dividedDifference` into `LinearAlgebra/Lagrange`,
`RCLike.toComplex` into `Analysis/Complex/Basic`; (2) Chebyshev growth (without the supporting
line) as `Analysis/SpecialFunctions/Trigonometric/Chebyshev/Growth.lean` and the extremal
corollaries into the existing `Extremal.lean`; (3) residual polynomials, minimax and the inverse
approximation in a `Chebyshev/Residual.lean`, with `residualMinimax` and its Sion duality separate
so that Residual does not import `Topology/Sion`; (4) coefficients, truncation and series through
`measureT`, next to `Orthogonality.lean`, then the Bernstein ellipse and analytic decay; (5) the
Jackson kernel (pure trigonometry) and Jackson's theorem; (6) the Stieltjes class beside
`MeasureTheory/Measure/ResolventTransform.lean` and the interpolation-error theorems. On the way:
the `IsUniformApproxOn` decision, the namespaces, ℂ-only or `RCLike`, the docstring strip, and the
constant inlined.
