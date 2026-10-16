# Poly1: Chebyshev extremality and exact minimax

**Design approved by root and independent bounded review, 2026-10-16.** The user approved the roadmap and routine stage
progression. No new lasting interface choice is proposed: use `Metric.IsUniformApproxOn` and
Mathlib `IsLeast`. Root GO authorizes sequential implementation, starting with file 1.
Read CONTRIBUTING, `docs/PORT_POLYNOMIAL.md` and `docs/port/status.md`.
The previously authorized available-agent fallback continues.

## 1. Scope, objects and consumers

Establish exact optimality after Poly0's constructive residual bounds: external Chebyshev modulus
comparison, monic minimax on the unit interval, and normalized-residual minimax on a positive
interval. These support the interpretation of Chebyshev iteration/CG residuals and later
interpolation/error estimates. No uniqueness theorem, alternation framework or approximation-space
structure is introduced. No new data definition, predicate or §5.3/§5.4 vocabulary row is needed.

All polynomials use Mathlib `Polynomial`, `T`, `eval`, `Monic`, `degree` and `natDegree`.
Natural q is cast to Mathlib's integer Chebyshev index. `natDegree` occurs only under `Monic`,
which excludes the zero polynomial; residual constraints retain `WithBot` degree.

## 2. Refreshed reuse search

Search order: pinned Mathlib → current NLAlib → prototype. Search exact proposed names and
statement fragments, then inspect the existing extremal module, not merely filenames.

* Mathlib `Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean`:
  `eval_iterate_derivative_le_of_forall_abs_le_one` already bounds a polynomial of degree≤q
  by T_q at x≥1 when k=0. Apply it to p and −p for modulus; use p.comp(−X) for x≤−1.
  Do not reprove interpolation/alternation or Mathlib's derivative theorem.
* `leadingCoeff_le_of_forall_abs_le_one` bounds the leading coefficient by 2^(q−1).
  Scale by M⁻¹ and use monicity for monic minimality. Its degree-zero convention matches this stage.
* Mathlib supplies T parity, degree, leading coefficient and unit-interval bounds. Reuse
  `T_eval_neg`, `natDegree_T`, `leadingCoeff_T`, `abs_eval_T_real_le_one` and basic polynomial API.
* Poly0 already supplies the normalized residual, unconditional degree bound, value at zero and
  reciprocal-T uniform bound. Reuse these directly for residual attainment.
* Refreshed search found no exact external-modulus wrapper, normalized-residual minimax or
  monic `IsLeast` theorem in Mathlib/current NLAlib. The wrappers below adapt upstream theorems,
  rather than claim a new independent extremality proof.
* The M≤0 branch can use polynomial identity from vanishing on the infinite interval;
  refresh the exact `Polynomial.eq_zero_of_infinite_isRoot`/evaluation identity API before proof.
  Prototype's zero-from-nonpositive-bound helper is proof material, not an automatically public API.

## 3. Files, placement and exact signatures

Sequential file 1: new
`NLAlib/ForMathlib/Analysis/SpecialFunctions/Trigonometric/Chebyshev/Extremal.lean`.
All its statements use only Mathlib vocabulary plus the upstream-candidate metric predicate;
namespace `Polynomial.Chebyshev`. Import the matching Mathlib module and generic interface.
The unit/scaled wrappers bridge its raw bounds to the approved shared interface.

```lean
namespace Polynomial.Chebyshev

theorem abs_eval_le_abs_eval_T_real_of_isUniformApproxOn
    {q : ℕ} {p : ℝ[X]} {x : ℝ}
    (hp : p.degree ≤ (q : WithBot ℕ))
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) 1)
    (hx : 1 ≤ |x|) : |p.eval x| ≤ |(T ℝ (q : ℤ)).eval x|

theorem abs_eval_le_mul_abs_eval_T_real_of_isUniformApproxOn
    {q : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hp : p.degree ≤ (q : WithBot ℕ))
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M)
    (hx : 1 ≤ |x|) : |p.eval x| ≤ M * |(T ℝ (q : ℤ)).eval x|

theorem inv_two_pow_le_of_monic_of_isUniformApproxOn
    {q : ℕ} {p : ℝ[X]} {M : ℝ} (hp : p.Monic) (hdeg : p.natDegree = q)
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M) :
    ((2 : ℝ) ^ (q - 1))⁻¹ ≤ M

theorem isLeast_chebyshev_monic_minimax (q : ℕ) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.Monic ∧ p.natDegree = q ∧
      Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M}
      (((2 : ℝ) ^ (q - 1))⁻¹)

end Polynomial.Chebyshev
```

The explicit witness for monic attainment is
`Polynomial.C (((2 : ℝ) ^ (q - 1))⁻¹) * Polynomial.Chebyshev.T ℝ (q : ℤ)`.
Use direct leading-coefficient/degree computations and the upstream interval bound. No separate
normalized monic polynomial definition or redundant public witness API is planned. Proof-local
lemmas may split long proofs; any helper useful outside this file must be reviewed for its home.

Sequential file 2: append to `NLAlib/Polynomial/Chebyshev/Residual.lean`, importing file 1.
Its current size leaves ample room for the roughly 60–100-line addition. The subject is the
existing NLAlib residual, so these statements belong in its owner rather than a generic dump.

```lean
namespace NLAlib

theorem inv_eval_T_real_le_of_isUniformApproxOn
    {a b M : ℝ} {q : ℕ} {p : ℝ[X]}
    (ha : 0 < a) (hab : a < b) (hp : p.degree ≤ (q : WithBot ℕ)) (hp0 : p.eval 0 = 1)
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc a b) M) :
    ((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹ ≤ M

theorem isLeast_chebyshev_minimax {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.degree ≤ (q : WithBot ℕ) ∧ p.eval 0 = 1 ∧
      Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc a b) M}
      (((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹)

end NLAlib
```

Pull p back by the affine map t↦(b+a)/2−(b−a)t/2; it maps [−1,1] into [a,b] and
maps (b+a)/(b−a) to zero. Apply scaled external comparison and positive T at this center.
Attainment uses `chebyshevResidual` and Poly0's three corresponding API facts, without redoing
its degree, normalization or interval proof.

## 4. Edge cases and proof budget

* q=0 is included everywhere. In monic minimax, q−1 is natural subtraction, so the objective
  is one and the witness is the constant one. In residual minimax T_0=1 and the optimum is one.
* The scaled external theorem imposes no M>0 premise. Nonempty [−1,1] gives M≥0; M=0 forces
  p=0 on the interval and hence as a polynomial. Monic p excludes that case for its lower bound.
* x=±1 is included. Negative exterior x uses parity/absolute values, not a second signed API.
* Residual minimax requires 0<a<b, retaining positive denominators and normalizer. No claim is
  made about degenerate parameters, already documented by the total residual definition.
* Target file 1 about 180–260 lines, file 2 under 250 total. Split proofs before about 80 lines;
  no new file-level heartbeat/backward settings. If a missing generic identity helper is needed,
  report its intended home before adding it; do not copy all prototype ForMathlib material.

## 5. Prototype and source relation

Read prototype `Polynomial/BestApproximation/Minimax.lean` (270 lines), corresponding definitions
in `Polynomial/Chebyshev/Core.lean`, and the small nonpositive-bound helper in
`ForMathlib/Algebra/Polynomial.lean`. Their six external/lower/IsLeast statements provide proof
material, restated through Metric rather than raw bounds; no aggregator, alias or monic witness
API is copied. Prototype residual construction/API already mapped by Poly0 is reused, not remapped.
The exact genuine ledger dispositions are recorded during implementation, never inferred from
matching names alone. Any supporting helper disposition must reflect actual reuse.

Saad2003, Theorem 6.25 and its following corollary, was verified in the local second-edition
primary source during Poly0 and supports normalized-residual minimax. External modulus is a
corollary of this extremality, proved here directly through Mathlib's k=0 derivative comparison.
Monic minimality is verified in Golub–Meurant, *Matrices, Moments and Quadrature with Applications*
(Princeton, 2010), §2.5.1, Theorem 2.15, printed p. 16. Its source range is q≥1; q=0 is our trivial
extension with constant one and natural subtraction. The verified book entry `GolubMeurant2010`
is included in the bibliography. The prototype's Trefethen Theorem 2.2
locator is not supported by the available local draft and must not be copied. Mathlib theorem
attribution remains explicit alongside literature provenance.

## 6. Review and validation

Bounded review checks placement, exact signatures, q=0/M=0, Mathlib reuse and source relation.
No user reassessment is needed for these routine approved-roadmap choices; a genuinely lasting
new interface or mathematical scope change returns to the user before implementation.
After root GO: one file at a time, refreshed searches, two-thread logged target build and capped
single-file check; read-back and independent review before progressing. Full root gates run once
at handoff, with no overlapping build. Refs/constants/LaTeX/reuse and genuine ledger updates are
included at stage wrap-up. No commit or push is authorized to the proof agent.

## File 1 implementation read-back (2026-10-16)

All four public statements match the design: degree≤q polynomials bounded by one or M on the
unit interval are bounded externally by |T_q| or M|T_q|; any monic degree-q polynomial has
uniform bound at least 2^(-(q−1)); this value is attained and is the `IsLeast` objective. Natural
subtraction includes q=0. M=0 is handled without weakening using infinite-root polynomial
identity. The proof directly uses upstream derivative comparison at order zero and the
leading-coefficient inequality. Two private helpers keep proofs short; no witness API was added.
Routine elaboration required explicit `Polynomial.C` (avoiding continuous-map notation) and
a direct RootsExtrema import for the interval bound; no mathematical signature change.
Verified `GolubMeurant2010` bibliography metadata was added, with the source q≥1 versus q=0
extension documented. Target build (2494 jobs) and capped Lean check passed without warnings:
`/tmp/nlalib-poly1-checks/01-extremal-build.log`, `01-extremal-lean.log`. No active build.

## File 2 and proof-stage handoff (2026-10-16)

Both residual statements match the design: for every natural q and 0<a<b, any degree≤q
polynomial equal to one at zero and uniformly bounded by M must have M≥T_q(center)⁻¹.
That reciprocal is the least feasible bound and is attained by the existing normalized residual.
At q=0 the optimum is one. The affine pullback feeds the new generic scaled external comparison;
attainment consumes the existing degree, zero-value and reciprocal-error facts. All Poly0 API
remains unchanged. No new definition or extra public theorem was added.
Target build (2496 jobs) and capped single-file Lean check passed without warnings; logs:
`/tmp/nlalib-poly1-checks/02-residual-build.log`, `02-residual-lean.log`. Both files and all six statements have independent
approval. Mechanical registration, exact genuine prototype ledger dispositions, full gates/reuse
and extraction are reported below. Poly2 implementation has not started. The user approved full
coefficient normalization, one generic RCLike API and inclusive degree-N truncation (0 through N);
its exact design and sequential proof work remain a separate stage.

## Final mechanical validation (2026-10-16)

Both implementation files and all six statements passed independent review. One new root import
and exactly six genuine prototype mappings were added; all prior ledger entries, including Poly0,
are unchanged. No new CONTRIBUTING vocabulary or Mathlib deviation is needed: this stage reuses
the approved metric interface and upstream extremal/leading-coefficient results. No proof edits
were made during mechanical validation.

The sequential two-thread full build passed (3895 jobs, zero warnings), both root checks passed,
audit checked 7278 declarations with zero violations, and 14 linters checked 5020 declarations
plus 2258 generated ones with zero errors. Duplicate reporting found 4621 theorems and zero
classes. References checked 56 keys/40 asymptotic forms; constants checked 25 bounds; KaTeX checked
5490 docstrings/18117 spans. Eleven metadata tests and reuse of all six headlines passed.
Target builds and capped file checks had already passed; no redundant overlapping stage build
or browser run was performed. Logs: `/tmp/nlalib-poly1-checks`.

Fresh extraction `/tmp/nlalib-poly1-explore.json` contains 307 modules/3490 public declarations;
all 307 source hashes match and all six additions are proved. The unchanged Explorer metadata
passes its strict source-aware build: 306 visible modules, 251 results, 169 enriched definitions.
Its 32 Rates rows/nine guarantees/three families are unchanged. No Explorer changes were needed.
The extraction records the pre-commit snapshot; root handles the requested commit and subsequent
stamp. No validation process remains active, and no commit or push was made by the validation agent.

The mathematical read-back above retains M=0, both exterior signs and q=0. Monic q=0 has optimum
one; the cited Golub–Meurant theorem covers q≥1, and the constant case is our trivial extension.
The exact residual optimum uses 0<a<b and is attained by the existing residual. Saad2003,
Theorem 6.25 and following corollary, supports the residual minimax statement; no unsupported
Trefethen locator was copied. Poly2 has no implementation in this stage. Its full coefficient
normalization, one RCLike API and inclusive degree-N cutoff are user-approved; exact design and
proofs follow separately.
