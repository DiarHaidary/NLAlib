# Existing-interface spectral extensions

2026-10-29. Status: Bounded review accepted and implementation completed. Targeted single-module
Lean checks passed; full integration validation passed (see the BI1 integration report).
The user's explicit reopening of suitable backend omissions and the Matrix standing approval
authorize this scope. This note amends the earlier decisions to omit these families, without
adding vocabulary, hypothesis interfaces, targets or a backend package dependency.
Backend revision: `77514ce42a0e437d837797a063ac161f41022730`; frontend base:
`6491e7528c1b1e68e46301cde6a76ae153e8e834`.

## 1. Principal-submatrix survival

Destination: `Matrix/Spectral/Diagonalizable.lean`. Despite placement, this theorem does not
assume diagonalizability. Its subject is geometric multiplicity, next to the multiplicity API.

```lean
variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

theorem mem_spectrum_submatrix_of_card_lt_add_finrank_eigenspace
    (A : Matrix n n K) (μ : K) (s : Finset n)
    (h : Fintype.card n <
      s.card + Module.finrank K (Module.End.eigenspace A.toLin' μ)) :
    μ ∈ spectrum K (A.submatrix (fun j : s => j.val) (fun j : s => j.val))
```

Consumer: track an eigenvalue after deleting coordinates, without normality or semisimplicity.
Proof: restrict eigenspace vectors to the deleted coordinates. Its dimension exceeds the
codomain dimension, so its kernel contains a nonzero vector; that vector is supported on `s`
and restricts to an eigenvector. Search/use Mathlib finrank/rank-nullity and matrix spectrum API.
Avoid the backend's truncated cardinal subtraction in the public statement (V2).

Backend `Spectral/DiagonalizablePrincipal.lean:23–81` has
`mem_spectrum_principal_submatrix_of_finrank_eigenspace_gt` and
`mem_spectrum_principal_submatrix_of_le_finrank_eigenspace`. The displayed condition is equivalent
to the first since `s.card ≤ card n`; the second follows by monotonicity from its lower bound `k`.
Both map to this single theorem with the arithmetic substitution recorded. Empty `s` makes the
hypothesis impossible; no extra nonemptiness assumption is needed. Fields are arbitrary.

## 2. Same-listing change of eigenbasis

Destination: `Matrix/Spectral/Diagonalizable.lean`, same field and finite-index context.

```lean
theorem diagonal_mul_inv_mul_eq_inv_mul_diagonal
    {A V W : Matrix n n K} {d : n → K} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d)
    (hAW : A * W = W * Matrix.diagonal d) :
    Matrix.diagonal d * (V⁻¹ * W) = (V⁻¹ * W) * Matrix.diagonal d

theorem inv_mul_apply_eq_zero_of_ne
    {A V W : Matrix n n K} {d : n → K} (hV : IsUnit V)
    (hAV : A * V = V * Matrix.diagonal d)
    (hAW : A * W = W * Matrix.diagonal d)
    {i j : n} (hij : d i ≠ d j) : (V⁻¹ * W) i j = 0
```

Consumer: compare eigenbases within repeated-eigenvalue blocks. No assumption that the listed
eigenvalues are distinct, and no invertibility assumption on `W` is needed. Use inverse identities
to prove commutation, then compare one matrix entry and cancel `d i - d j` in the field.

Backend `Spectral/DiagonalizableBlocks.lean:83–118`: respectively
`diagonal_mul_change_eigenbasis_eq_change_eigenbasis_mul_diagonal` and
`change_eigenbasis_apply_eq_zero_of_eigenvalues_ne`. The bundled third result,
`isUnit_change_eigenbasis_and_apply_eq_zero`, is covered by the second plus existing `IsUnit.inv`
and multiplication under its additional `IsUnit W`; do not add a redundant conjunction theorem.
This is sameness of a full ordered listing, not merely equality of spectrum sets.

## 3. Rank-one eigenprojector identities

Destinations: the idempotence theorem is in `Matrix/Subspaces/ObliqueProjector.lean`; the two
eigenvector multiplication identities are in `Matrix/Spectral/EigenvectorPairing.lean`, with
the same field and finite-index context. The raw expression is intentional existing matrix/scalar vocabulary, not a new projector object.

```lean
theorem isIdempotentElem_inv_smul_vecMulVec {x y : n → K} :
    IsIdempotentElem ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y)

theorem mul_smul_vecMulVec_eq_smul {A : Matrix n n K} {x y : n → K}
    {μ : K} (hx : A *ᵥ x = μ • x) :
    A * ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) =
      μ • ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y)

theorem smul_vecMulVec_mul_eq_smul {A : Matrix n n K} {x y : n → K}
    {μ : K} (hy : y ᵥ* A = μ • y) :
    ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y) * A =
      μ • ((y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y)
```

Consumer: oblique spectral projector calculations and later deflation. Idempotence also holds at zero pairing, when the expression is zero. Bounded review places
this general identity in `Matrix/Subspaces/ObliqueProjector.lean`; only the multiplication
identities remain in EigenvectorPairing.
The two multiplication statements each drop the source's unused other eigenvector hypothesis.
No conjugation of the left vector is silently inserted; the left vector represents a row.

Backend `Spectral/EigenvectorPairing.lean`: `normalized_vecMulVec_mul_self` maps to the first;
`mul_normalized_vecMulVec_eq_smul` is covered by both halves. Mathlib's
`Matrix.mul_vecMulVec`, `Matrix.vecMulVec_mul`, `Matrix.vecMulVec_mul_vecMulVec`, scalar
multiplication identities and field cancellation suffice. Do not add duplicate outer-product
lemmas already available from Mathlib. No nonempty-index assumption is needed.

## 4. Simultaneous triangularization transfer

Destination: `Matrix/Spectral/Simultaneous.lean`. Add a specific import of
`Matrix/Factorizations/QR.lean`. Source import-graph traversal found no path from QR to
Simultaneous (68 reachable local modules checked); the new edge is acyclic and stays at layer 0.

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {ι n : Type*} [Fintype n] [DecidableEq n]

theorem exists_forall_isUpperTriangular_inv_mul_mul_iff [LinearOrder n]
    (A : ι → Matrix n n 𝕜) :
    (∃ V : Matrix n n 𝕜, IsUnit V ∧
      ∀ i, (V⁻¹ * A i * V).IsUpperTriangular) ↔
    ∃ U : Matrix n n 𝕜, HasOrthonormalCols U ∧
      ∀ i, (Uᴴ * A i * U).IsUpperTriangular
```

Consumer: a common invariant flag supplied by an arbitrary similarity can be represented in
an orthonormal basis. There is no pairwise-commutation hypothesis, no finiteness assumption on
`ι`, and no algebraic closure/splitting hypothesis: the triangularizing similarity is supplied.
Generalization from complex scalars to `RCLike` is supported by the existing generic QR theorem.

Proof: `exists_isQR V le_rfl` gives `V = Q * R`; invertibility of `V` forces invertibility of
upper-triangular `R`. Then `Qᴴ * A i * Q = R * (V⁻¹ * A i * V) * R⁻¹`, upper triangular by
the existing triangular multiplication/inverse API. Reverse direction uses `Q⁻¹ = Qᴴ` for
square orthonormal `Q`. Preserve empty dimensions, where these identities remain valid.

Backend `Spectral/SimultaneousTriangularBasis.lean:21–81` gives
`exists_simultaneous_triangular_similarity_iff_unitary` and its `_of_equiv` variant. The first
maps by `HasOrthonormalCols`/unitary-group equivalence. For `_of_equiv`, transport the finite
index type to `Fin (card n)` along its explicit enumeration, apply this theorem there, and
transport matrices back. Record this instantiation in the ledger; no second public transported
order theorem is required. The backend's WellFounded/LocallyFinite order assumptions disappear
because the frontend QR theorem already handles arbitrary finite linear orders.

## Review, provenance and acceptance

No source locator is newly verified by this note. Public docstrings will give the mathematical
statement and backend `Port of` attribution and reuse existing result-family citations only
where their scope is appropriate; never invent a printed label. Every source mapping records
split statements, arithmetic equivalents and reindexing rather than claiming identical syntax.
No separate algorithm target, global instance, `sorry`, new object or scope weakening is allowed.

Bounded review fixed these signatures before proof dispatch; implementation and targeted checks
are complete. The parent owns the build queue,
ledger/root/status updates and extraction-backed checks. Authors run the source-rule checker
on their owned files and report any unelaborated claim; they do not run concurrent Lean builds.
Implementation ownership covered Diagonalizable, EigenvectorPairing, Simultaneous and
ObliqueProjector, with the latter explicitly added by the accepted amendment below.

Bounded review accepted the statements with total idempotence in its canonical predicate.
Parent approved this amendment and ObliqueProjector ownership before proof implementation.
