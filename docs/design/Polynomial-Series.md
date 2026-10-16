# Poly2: canonical Chebyshev coefficients and degree-N truncation

**Design approved by root and independent bounded review, 2026-10-16.** The user explicitly approved
full coefficients, one generic RCLike spelling and inclusive degree-N truncation. Root GO authorizes sequential implementation, starting with file 1. Poly1 is complete.
Read CONTRIBUTING, PORT_POLYNOMIAL, Polynomial-Chebyshev and Polynomial-Minimax designs/status.
Previously authorized available-agent fallback continues.

## 1. Scope and consumers

Provide the canonical coefficients and finite polynomial truncation used by later analytic
approximation, with coefficient linearity, basis orthogonality and exact reproduction of every
polynomial in its degree budget. Poly3 adds series reconstruction, ellipse coefficient decay and
geometric truncation error using these same objects. No contour/Fourier coefficient definition,
analytic error bound or arbitrary Banach-valued polynomial framework belongs here.

The concrete function-approximation consumer is exact polynomial reproduction: a degree≤N
polynomial, viewed as a real-input function, is recovered by the degree-N truncation. This
identity is stronger and more reusable than a duplicate Metric-error-zero corollary. Later
quantitative approximation uses the existing `Metric.IsUniformApproxOn`, with no new predicate.

## 2. Approved vocabulary and total behavior

| Object | Construction/home | Bridge and convention |
|---|---|---|
| `chebyshevCoeff f k` | Cosine Bochner interval integral; ChebyshevCoefficients | Raw integral by definition; coefficient of T_j is Kronecker delta; future contour/Fourier representations are equalities |
| `chebyshevTrunc f N` | Finite sum in ChebyshevTruncation | Polynomial eval sum and degree≤N; exact polynomial reproduction |

Both are namespace NLAlib, `{𝕜 : Type*} [RCLike 𝕜]`, `f : ℝ → 𝕜`. There is one spelling,
not real/complex twins. Coefficients have normalization 1/π at k=0 and 2/π for k>0;
there is no half-zero term in the expansion. Truncation includes terms 0 through N.

Each coefficient is total: Bochner integration uses zero for its own nonintegrable weighted
integrand. Integrability can differ with k; nonintegrability of f or its unweighted cosine pullback
does NOT imply every coefficient vanishes. Neither definition promises reconstruction for
arbitrary f. No continuity, degree or analyticity is bundled into a function type.

## 3. Refreshed Mathlib-first search and generic proof route

* Targeted exact-name searches found no `chebyshevCoeff`/canonical truncation in pinned Mathlib
  or current NLAlib. Current Poly0/Poly1 supplies Metric approximation and scalar residual APIs,
  not series coefficients. Do not replace Mathlib's T or polynomial sequence machinery.
* Mathlib Chebyshev.Orthogonality supplies `measureT`, the real cosine substitution
  `integral_measureT_eq_integral_cos`, and real T-product orthogonality: distinct degrees give
  zero; the zero self-product gives π; positive-degree self-products give π/2.
* `Polynomial.Chebyshev.map_T` transports real T to 𝕜 T, and evaluation commutes with the
  coefficient map. `T_real_cos` supplies the cosine pullback. No generic analytic cosine on 𝕜
  is needed: the input parameter and cosine stay real and their values are coerced into 𝕜.
* `RCLike.intervalIntegral_ofReal` is already generic and unconditional. It transports the real
  cosine-product orthogonality integral to 𝕜. This avoids a new generic arcsine-measure API.
* `intervalIntegral.integral_add` requires integrability; `integral_const_mul` and
  `integral_mul_const` already support the scalar fields needed here. Multiplying an integrable
  pullback by continuous cosine is justified by `IntervalIntegrable.continuousOn_mul` on the
  compact interval. Constant multiplication is unconditional, including the zero scalar.
* Arbitrary-polynomial reproduction has a verified upstream span route, not a guessed basis API:
  `Polynomial.Chebyshev.chebyshevTsequence 𝕜 : Polynomial.Sequence 𝕜` exists for an IsDomain
  with NeZero 2. RCLike supplies a characteristic-zero field, so both requirements hold.
  `Polynomial.Sequence.ne_zero` makes leading coefficients nonzero, hence units over the field.
  `Polynomial.Sequence.span_degreeLE` says the first N+1 elements span `Polynomial.degreeLE`.
  `Polynomial.mem_degreeLE` and `Submodule.mem_span_image_finset_iff_exists_fun'` yield a finite
  expansion after identifying `Set.Iic N` with `Finset.range (N+1)`. This exact construction is
  also used by the real prototype CosineBasis; generalization changes no mathematical argument.
* A refreshed search is repeated before each file. Exact overlaps discovered later are reused,
  not independently reproved.

## 4. File 1: coefficients, exact signatures

New `NLAlib/Polynomial/Approximation/ChebyshevCoefficients.lean`, roughly 150–230 lines.
Import RCLike, interval integration, Chebyshev orthogonality and only required tactics.
Definitions/basic linearity precede the main orthogonality identification.

```lean
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def chebyshevCoeff (f : ℝ → 𝕜) (k : ℕ) : 𝕜 :=
  (((if k = 0 then 1 else 2) / Real.pi : ℝ) : 𝕜) *
    ∫ θ in 0..Real.pi, f (Real.cos θ) * (Real.cos ((k : ℝ) * θ) : 𝕜)

theorem chebyshevCoeff_zero (k : ℕ) :
    chebyshevCoeff (fun _ : ℝ => (0 : 𝕜)) k = 0

theorem chebyshevCoeff_add {f g : ℝ → 𝕜}
    (hf : IntervalIntegrable (fun θ => f (Real.cos θ)) volume 0 Real.pi)
    (hg : IntervalIntegrable (fun θ => g (Real.cos θ)) volume 0 Real.pi) (k : ℕ) :
    chebyshevCoeff (fun x => f x + g x) k = chebyshevCoeff f k + chebyshevCoeff g k

theorem chebyshevCoeff_const_mul (c : 𝕜) (f : ℝ → 𝕜) (k : ℕ) :
    chebyshevCoeff (fun x => c * f x) k = c * chebyshevCoeff f k

theorem chebyshevCoeff_eval_T (j k : ℕ) :
    chebyshevCoeff (fun x : ℝ => (Polynomial.Chebyshev.T 𝕜 (j : ℤ)).eval (x : 𝕜)) k =
      if j = k then 1 else 0

end NLAlib
```

Namespaces for `IntervalIntegrable`, `volume` and integral notation are opened locally in the
implementation. `chebyshevCoeff_add` has no analyticity or global continuity premise; each supplied
pullback is interval-integrable. No unsound unconditional addition theorem is proposed.
Const-multiplication can directly reuse unconditional Bochner linearity, keeping f arbitrary.
A private real cosine-product evaluation helper and/or generic T-evaluation transport helper may
support the basis theorem. Do not add public generic scalar-cosine lemmas merely for proof plumbing.

## 5. File 2: finite truncation, exact signatures

New `NLAlib/Polynomial/Approximation/ChebyshevTruncation.lean`, roughly 130–220 lines.
Import file 1 and the upstream sequence/span machinery as needed.

```lean
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜]

noncomputable def chebyshevTrunc (f : ℝ → 𝕜) (N : ℕ) : 𝕜[X] :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (chebyshevCoeff f k) * Polynomial.Chebyshev.T 𝕜 (k : ℤ)

theorem eval_chebyshevTrunc (f : ℝ → 𝕜) (N : ℕ) (x : 𝕜) :
    (chebyshevTrunc f N).eval x = ∑ k ∈ Finset.range (N + 1),
      chebyshevCoeff f k * (Polynomial.Chebyshev.T 𝕜 (k : ℤ)).eval x

theorem degree_chebyshevTrunc_le (f : ℝ → 𝕜) (N : ℕ) :
    (chebyshevTrunc f N).degree ≤ (N : WithBot ℕ)

theorem chebyshevTrunc_eval_eq {p : 𝕜[X]} {N : ℕ}
    (hp : p.degree ≤ (N : WithBot ℕ)) :
    chebyshevTrunc (fun x : ℝ => p.eval (x : 𝕜)) N = p

end NLAlib
```

The total degree bound uses finite-sum degree bounds and upstream T degree; coefficients may
vanish and p may be zero. N=0 includes its constant coefficient, rather than an empty sum.
Exact reproduction needs only degree≤N because polynomials are automatically continuous;
no separate integrability premise should burden the user.

Proof plan: privately obtain the finite Chebyshev expansion from the upstream span theorem;
use coefficient linearity on the continuous polynomial summands and basis delta to identify the
finite expansion coefficients. Substitution into the truncation then gives polynomial equality.
A finite-sum coefficient lemma may be private if used only in reproduction. The generic algebraic
span fact is not a new public application API: use upstream directly in a private proof helper.
If a genuinely reusable public spanning theorem becomes necessary, its intended home is
ForMathlib/RingTheory/Polynomial/Chebyshev and the design must be amended before adding a third file.

## 6. Source relation and omissions

Read prototype `Polynomial/FunctionApproximation/ChebyshevCoefficients.lean` (137 lines),
`Polynomial/Chebyshev/CosineBasis.lean` (42 lines) and the truncation definition/degree argument
in `FunctionApproximation/AnalyticApproximation.lean`. Reuse normalization, cosine representation,
finite spanning argument and finite-sum degree reasoning. Do not copy its three real/complex/
analytic coefficient spellings, complex-real-part truncation, contour coefficient object or
Fourier-circle infrastructure. Later representation equalities refer to the ONE coefficient.

Verified primary locators: Trefethen2019 Extended Edition, p. 16 (finite basis), Theorem 3.1,
Eqs. (3.11)–(3.12) on p. 17 (full coefficients), Exercise 3.7 on p. 22 (orthogonality), and
Eq. (4.3) on p. 25 (inclusive degree-N truncation). Author-hosted primary extract:
https://people.maths.ox.ac.uk/trefethen/ATAP/first6.pdf . GolubMeurant2010 §2.5.1, p. 16,
also gives the weighted orthogonality. Cosine substitution, generic RCLike transport and exact
polynomial reproduction are the corresponding derived/generalized consequences, not separate
numbered printed theorems. Mathlib orthogonality supplies the formal proof source.

## 7. Review and gates

Bounded review checks the user-approved normalizations, RCLike coercion route, integrability,
finite-span reproduction, total-integral wording and N=0. All nine public declarations are now elaborated and independently approved.
No new lasting choice is open. Any unexpected need for a second coefficient notion, new interface
or changed cutoff goes to root/user assessment; routine elaboration adjustments are recorded.
After root GO: one file at a time, capped two-thread target and single-file checks with logs,
read-back and independent review. No concurrent build, full-gate duplication, commit or push.
Poly3 analytic reconstruction/error remains explicitly outside this stage.

## File 1 read-back (2026-10-16)

The coefficient uses the exact approved full cosine-integral normalization over arbitrary RCLike
values. Zero, addition under the two pullback-integrability hypotheses, unconditional scalar
multiplication, and Chebyshev basis delta all match the signatures. The basis proof transports
real orthogonality using `map_T`, `eval_map_apply` and `RCLike.intervalIntegral_ofReal` directly.
Two private helpers provide scalar transport and the real cosine-product integral; no public
plumbing API or additional hypothesis was introduced. Routine elaboration used explicit
`algebraMap` in a helper and `IntervalIntegrable.mul_continuousOn` for right multiplication.
Target build (2715 jobs) and capped single-file check passed without warnings; logs:
`/tmp/nlalib-poly2-checks/01-coefficients-build.log`, `01-coefficients-lean.log`. No active build.

## File 2 and proof-stage handoff (2026-10-16)

The truncation is exactly the inclusive sum from zero through N. Evaluation is termwise and
the unconditional WithBot degree bound includes vanished coefficients and zero polynomials.
Every RCLike polynomial of degree≤N is reproduced as a polynomial identity, with no added
integrability premise and no mirror error-zero theorem. N=0 recovers constants. The proof
uses `chebyshevTsequence`, `Sequence.span_degreeLE`, the finite-span constructor and coefficient
linearity/basis delta. Two private helpers obtain the finite expansion and identify its coefficients;
no new public spanning API was introduced. Routine elaboration required direct Eval.SMul and
Topology.Algebra.Polynomial imports, not a statement or interface change.
Target build (2716 jobs) and capped Lean check passed without warnings; logs:
`/tmp/nlalib-poly2-checks/02-truncation-build.log`, `02-truncation-lean.log`. Both files and all nine public declarations independently
approved. Final registration, genuine ledger dispositions, vocabulary rows and full-gate evidence
are reported below. No commit was made. Poly3 implementation has not started; its durable
extension-interface question remains with the user.

## Final mechanical validation (2026-10-16)

Both files and all nine public declarations are independently approved. Two modules are registered,
and the two approved vocabulary rows are recorded in CONTRIBUTING. The Mathlib comparison records
an addition, not a numbered deviation: canonical coefficients/truncation were absent upstream,
and the implementation directly reuses T, orthogonality, cosine integration and sequence spans.
No proof changes were made during wrap-up.

Exactly one genuine prototype disposition was added: the real `NLAlib.chebyshevCoeff` generalizes
to the same canonical RCLike object. The prototype's unconditional cosine-integral equality
establishes its real specialization, including total integral behavior. Previous mappings are
unchanged. The prototype analytic contour coefficient, real-part coefficient and analytic real
truncation are not direct aliases of the new full-complex objects; they remain unmapped pending
actual representation bridges. Private finite-span proof reuse does not invent a public mapping.

The sequential two-thread full build passed (3900 jobs, zero warnings), both root checks passed,
audit checked 7300 declarations with zero violations, and 14 linters checked 5033 declarations
plus 2267 generated ones with zero errors. Duplicate reporting found 4632 theorems and zero
classes. References checked 56 keys/40 asymptotic forms; constants checked 25 bounds; KaTeX checked
5501 docstrings/18134 spans. Eleven metadata tests and all nine reuse targets passed. Prior
capped module/file checks passed; no redundant full-stage build or browser run was performed.
Logs: `/tmp/nlalib-poly2-checks`.

Fresh extraction `/tmp/nlalib-poly2-explore.json` has 309 modules/3499 public declarations;
all 309 source hashes match and all nine additions are proved. The unchanged strict Explorer
build passes with 308 visible modules, 252 results and 171 enriched definitions. Its 32 Rates
rows/nine guarantees/three families are unchanged. No Explorer edits were needed. The extraction
records the pre-commit snapshot; root handles commit and restamp. No validation process remains
active, and the validation agent made no commit or push.

The read-back above retains full normalization, RCLike values, conditional addition,
unconditional scalar multiplication, N=0 and exact polynomial reproduction including zero.
Each weighted integrand has its own total-integral behavior; arbitrary functions are not promised
reconstruction. Verified sources distinguish the published Extended Edition locators from the
local 2018 draft and identify RCLike transport/reproduction as generalized consequences.
Poly3 implementation remains paused pending the user's extension-interface decision; no dependent
geometry/analytic proofs or design edits belong to this wrap-up.
