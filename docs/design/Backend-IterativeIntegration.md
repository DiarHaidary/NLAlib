# Richardson convergence from the backend integration

Date: 2026-10-29. Status: Bounded review accepted and implementation completed. Targeted
single-module Lean checks passed; full integration validation passed (see the BI1 integration report). The independent review
accepted R1-R4 including empty dimensions
and requested the R3 placement correction below; the orchestrator approved that correction.
Implementation of R1-R4 passed the orchestrator's serial targeted Lean checks. The source-rule
check also passes for both files using Python's UTF-8 mode; full integration validation passed (see the BI1 integration report).

## Scope and authorization

The maintainer's current request reopens previously omitted backend results when the frontend
already has suitable infrastructure, with an architecture- and naming-compliant integration PR.
This note specifies a routine extension of the approved Richardson interface in
`Regression-SketchPrecondition.md` (D3 and sections 3.1, 4.1). It introduces no algorithm,
hypothesis predicate, data structure, program, target, or alternative mathematical vocabulary.
The signatures received bounded review before implementation. This note does not
claim that the maintainer has separately approved any new interface or unrelated stage.

Frontend base: `6491e7528c1b1e68e46301cde6a76ae153e8e834`.
Backend source: `tchen-research/NLAlib`, revision `77514ce`,
`NLAlib/Krylov/Solvers/StationarySplitting.lean`, especially lines 99, 116, 124, 157 and 165.

## Objects, placement and existing infrastructure

Use `richardsonIterate A M b x₀`, `specRadius`, `IsUnit`, ordinary matrix multiplication,
`Tendsto` and the existing fixed-point equation `M *ᵥ (b - A *ᵥ xs) = 0`.
Scalars remain `RCLike`; finite index types may be empty. The first two statements are
rectangular. The last two concern square systems. There is no real/complex duplication.

R1, R2 and R4 belong in `NLAlib/Krylov/LinearSystems/Richardson.lean`, after its
fixed-point error identity and before the energy-norm bounds. Add the specific import
`NLAlib.Matrix.Spectral.PowerBounds`; Krylov importing Matrix respects P1. No new Lean file,
root import is planned. R3 belongs in `NLAlib/Matrix/Spectral/PowerBounds.lean`, immediately
after the Neumann invertibility API: it is a matrix-only statement and is placed by its subject
(P10). This dated amendment extends that Matrix topic and the Richardson file list in
`Regression-SketchPrecondition.md` section 7.

Existing API verified in the frontend:

- `sub_richardsonIterate_eq` (Richardson line 109): fixed-point error is
  `(1 - M * A) ^ q *ᵥ (xs - x₀)`.
- `tendsto_pow_zero_iff_specRadius_lt_one` (PowerBounds line 129).
- `isUnit_det_one_sub_of_specRadius_lt_one` (PowerBounds line 174).
- Mathlib `Matrix.isUnit_iff_isUnit_det`, `Matrix.det_mul`,
  `Matrix.mul_nonsing_inv`, and `Matrix.mulVec_injective_iff_isUnit`.

Searches found no existing Richardson limit theorem in frontend or Mathlib. Mathlib's
product topology and continuity of finite sums suffice to transfer matrix limits to vectors;
the converse tests standard coordinate vectors. Do not copy the backend's separate
matrix-power/mulVec convergence lemma without checking whether its statement warrants public
API. Initially perform these finite-dimensional steps within the proofs, splitting a helper
only if necessary to respect the 80-line proof limit. A reusable new helper requires a placement
amendment before being made public.

## Exact implemented signatures

The following blocks record the implemented, targeted-check-passed declarations. The context is the
existing `namespace NLAlib`, with `open Filter Topology` and `open scoped Matrix`.

### R1: convergence to a specified fixed point

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}
  [Fintype m] [Fintype n] [DecidableEq n]

theorem tendsto_richardsonIterate_of_specRadius_lt_one
    {A : Matrix m n 𝕜} {M : Matrix n m 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : M *ᵥ (b - A *ᵥ xs) = 0) (hρ : specRadius (1 - M * A) < 1)
    (x₀ : n → 𝕜) :
    Tendsto (richardsonIterate A M b x₀) atTop (𝓝 xs)
```

This covers a consistent solution, or a least-squares fixed point under an appropriate
preconditioner. It does not claim convergence merely from one stable starting vector.

### R2: the exact criterion for every starting vector

```lean
theorem forall_tendsto_richardsonIterate_iff_specRadius_lt_one
    {A : Matrix m n 𝕜} {M : Matrix n m 𝕜} {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : M *ᵥ (b - A *ᵥ xs) = 0) :
    (∀ x₀ : n → 𝕜, Tendsto (richardsonIterate A M b x₀) atTop (𝓝 xs)) ↔
      specRadius (1 - M * A) < 1
```

The forward implication uses starts `xs - e_j`, so every column of the error matrix tends
to zero. Entrywise convergence gives matrix convergence, then the existing spectral-radius
criterion applies. The backward implication is R1. No diagonalizability or normality is assumed.

### R3: stability implies unique solvability of the square system

```lean
theorem isUnit_of_specRadius_one_sub_mul_lt_one
    {A M : Matrix n n 𝕜} (hρ : specRadius (1 - M * A) < 1) :
    IsUnit A
```

Apply the existing Neumann invertibility result to `1 - M * A` to make `M * A` invertible.
Use determinant multiplicativity and the field's unit-product criterion to deduce `IsUnit A`.
No invertibility hypothesis on `M` is necessary: the conclusion follows from the spectral
condition. The statement is placed in Matrix, alongside the existing inverse/spectral fact,
as required by the bounded review's placement correction.

### R4: all right-hand sides, unique solution, convergence from every start

```lean
theorem forall_exists_mulVec_eq_and_tendsto_richardsonIterate_iff_specRadius_lt_one
    (A M : Matrix n n 𝕜) :
    (∀ b : n → 𝕜, ∃ xs : n → 𝕜,
      A *ᵥ xs = b ∧
      (∀ ys : n → 𝕜, A *ᵥ ys = b → ys = xs) ∧
      ∀ x₀ : n → 𝕜, Tendsto (richardsonIterate A M b x₀) atTop (𝓝 xs)) ↔
      specRadius (1 - M * A) < 1
```

The conjunction is the single full convergence contract, not a bundle of unrelated bounds.
The backward implication uses R3, `xs = A⁻¹ *ᵥ b`, injectivity of `A.mulVec`, and R1.
Forwards, specialize to `b = 0`; uniqueness identifies `xs = 0`, and R2 gives the criterion.
This is meaningful for empty index types as well. It does not require `M` invertible as an
extra hypothesis, and it does not mistake a preconditioned fixed point for a solution of `Ax=b`.

## Backend correspondence and consumers

Backend splitting `splittingIterate M N b x₀` is Richardson on `A = M - N` with
preconditioner `M⁻¹`, when `IsUnit M`. Then `1 - M⁻¹ * (M - N) = M⁻¹ * N`.
This is an interpretation/port correspondence; do not introduce a new frontend splitting
definition or retain backend `SplittingConverges` merely to preserve spelling.

| Backend family | Frontend coverage after proof |
|---|---|
| `affineStationaryIterate_sub_eq_pow_mulVec`, `splittingIterate_sub_eq_pow_mulVec` | existing fixed-point error identity; correspondence changes iteration vocabulary |
| `isUnit_sub_of_tendsto_splitting_pow_zero` | R3 after power-decay/spectral-radius equivalence and the splitting substitution |
| `splittingConverges_iff_tendsto_pow_zero` | R4 composed with existing power-decay equivalence |
| `splittingConverges_iff_spectralRadius_lt_one` | R4, complex specialization and splitting substitution |
| `splittingConverges_iff_complex_spectralRadius_lt_one` | same R4, real specialization; frontend `specRadius` already complexifies |

Ledger notes must state these substitutions and the generalized interface. R1 alone does not
justify marking any full all-right-hand-sides backend theorem covered. Add ledger mappings only
after the complete scope has been checked. Do not change mappings for backend algorithm
definitions as though those definitions were copied.

Actual existing consumers are `Regression/IterativeSketching.lean` and the mean-iterate
identities in `Regression/Kaczmarz.lean` (Richardson lines 19-22 describe both). They can use R1
when their error matrix is strictly stable. In rank-deficient Kaczmarz, full-space stability
usually fails because null-space directions are fixed; these results do not replace its
row-space convergence theorem. The Jacobi spectral criterion already in
`Matrix/Spectral/SpectralRadius.lean` can specialize R4 with the diagonal preconditioner.

## Proof plan, metadata and validation

Prove R1, R2, R3, R4 in that dependency order, using existing public API. Keep signatures fixed
after review; report any required statement change. The source attribution is the backend module
and revision above. Reuse the verified matrix-power result's mathematical citation only for that
step; the backend's vague Darve source label has not been checked against a printed source here.
Do not invent a theorem number. A new headline citation needs verification; otherwise use the
repository's explicit `No printed source.` convention with port provenance, and review whether
R4 should share the existing `richardson-iteration` result family. Helpers carry no result id.

Targeted module checks and source rules passed. The orchestrator coordinates the remaining
full integration, extraction-backed naming, references, ledger, axiom and replay checks.

Bounded review questions: are R1-R4 correctly quantified including empty dimensions; is R3's
placement appropriate; does R4 cover the full backend contract without a duplicate interface;
do names meet the current grammar? The independent bounded review accepted these scopes and the Matrix placement of R3
before proof implementation.

## Separate future stages

Diagonal estimation, Gaussian residual certificates, tail-averaged Kaczmarz, adaptive Cholesky
laws, volume sampling, RQI/QR iteration and normal spectral reconstruction are not folded into
this extension. Their new algorithm/output or probabilistic interfaces need their own designs.
No ready additional existing-interface-only family was verified sufficiently to include here.
