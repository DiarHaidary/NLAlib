# Matrix positive-part projection

2026-10-29 amendment to Backend-SpectralIntegration, section 4. The user's request reopens
backend omissions whose infrastructure is present; the Matrix standing instruction in
`docs/port/status.md` permits bounded design review followed by implementation.

Status: Bounded review accepted and implementation completed. Targeted single-module Lean checks
passed; full integration validation passed (see the BI1 integration report).

## Objects, interfaces and placement

Use existing `hermitianPart`, Mathlib `cfc`, `MatrixOrder`, `PosSemidef`, `frobInner` and
`frobNorm`. There is no new clipping definition, proof-carrying functional calculus, global
instance, scalar restriction or algorithm target. The projection above a real floor `a` is
`cfc (max a) (hermitianPart A)`. This keeps the full backend scope, including negative floors,
singular and non-Hermitian inputs and empty index types. The zero-floor formula is Mathlib's
positive part; it need not become a competing primary API.

All additions belong in the new topic file `NLAlib/Matrix/Functions/PositivePart.lean`, except
`Matrix.IsHermitian.frobInner_sub_hermitianPart`, which belongs in
`Matrix/Spectral/HermitianPart.lean`: for Hermitian `X` it states
`frobInner (A - hermitianPart A) X = 0`. It is an API lemma about the Hermitian-part operation.
Imports: `Matrix/Functions/HermitianCalculus`, `Matrix/Spectral/HermitianPart`, and existing
positive-semidefinite trace-product infrastructure. Matrix layer 0 only.

## Exact statements

Inside `namespace NLAlib`, with `open scoped Matrix MatrixOrder`:

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem frobInner_sub_cfc_max_hermitianPart_le_zero
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobInner (A - cfc (max a) (hermitianPart A))
      (X - cfc (max a) (hermitianPart A)) ≤ 0

theorem frobNorm_sub_cfc_max_hermitianPart_le
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobNorm (A - cfc (max a) (hermitianPart A)) ≤ frobNorm (A - X)

theorem frobNorm_sub_eq_frobNorm_sub_cfc_max_hermitianPart_iff
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobNorm (A - X) = frobNorm (A - cfc (max a) (hermitianPart A)) ↔
      X = cfc (max a) (hermitianPart A)

theorem frobNorm_cfc_max_hermitianPart_sub_le
    (A B : Matrix n n 𝕜) (a : ℝ) :
    frobNorm (cfc (max a) (hermitianPart A) -
      cfc (max a) (hermitianPart B)) ≤ frobNorm (A - B)

theorem frobNorm_sub_cfc_max_hermitianPart_sq
    (A : Matrix n n 𝕜) (a : ℝ) :
    frobNorm (A - cfc (max a) (hermitianPart A)) ^ 2 =
      frobNorm (A - hermitianPart A) ^ 2 +
        ∑ i ∈ Finset.range (Fintype.card n),
          max (a - eigenvalue (hermitianPart A) i) 0 ^ 2
```

Feasibility uses `cfc_le_iff`/`cfc_le_cfc` and the constant functional calculus. The implemented
public feasibility helper is
`Matrix.IsHermitian.smul_one_le_cfc_max (hH : H.IsHermitian) (a : ℝ) : a • 1 ≤ cfc (max a) H`.
The corresponding correction identity is supporting API, not a new hypothesis interface.

## Search, proof plan and consumers

Pinned Mathlib has positive/negative parts and their complementarity, but no nearest-matrix
Frobenius projection theorem was found. Frontend provides `frobNorm_sub_sq`, `frobInner_self`,
`frobInner_conjTranspose`, the PSD trace-product inequality, `Matrix.IsHermitian.re_trace_cfc`,
and `Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le`. Use those public APIs.

Write `H = hermitianPart A` and `P = cfc (max a) H`. Functional calculus gives
`a • 1 ≤ P`, `H ≤ P`, and `(P - H) * (P - a • 1) = 0`. Frobenius orthogonality removes
`A - H`; positivity of the trace of a product of PSD matrices gives the variational inequality.
Expand squared distances for minimality and uniqueness. Nonexpansiveness follows from paired
variational inequalities and Cauchy-Schwarz, or the existing CFC Lipschitz theorem plus the
Hermitian-part contraction. The exact squared distance uses the trace functional calculus,
with indices bounded to `Finset.range (Fintype.card n)` so padding is excluded.

Consumers: covariance correction, projection methods with a prescribed spectral floor, and
stability bounds for such corrections. The real floor is unrestricted, and its normalization
is unchanged in every theorem. No minimality claim about the spectral norm is made.

## Provenance and verification

Backend commit `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Functions/NearestPSD.lean`: variational inequality, unique minimizer,
nonexpansiveness and exact distance. The new statements split the backend conjunctions, remove
redundant Hermitian hypotheses implied by the Loewner floor, and replace `nearestPSD` and
proof-carrying `spectralClip` with the native CFC expression. Record these translations in the
ledger; do not represent the old definitions as newly imported objects.

Higham (1988) provenance was verified as recorded below. Targeted checks passed. The orchestrator
coordinates generated roots, extraction-backed naming, axiom/replay, duplicate/reuse and full
integration checks. The amendment received bounded review before implementation. Available-model author/reviewer
fallback is recorded in the
integration report, following the Gaussian-FourthMoments precedent.

Bounded independent review accepted the full-floor amendment on 2026-10-29. Higham's
[original paper](https://nhigham.com/wp-content/uploads/2023/10/high88d.pdf), Theorem 2.1,
pages 105-106, gives the real zero-floor unique minimizer and exact distance. The current
statements generalize its scalar field and floor; nonexpansiveness is a projection consequence.
