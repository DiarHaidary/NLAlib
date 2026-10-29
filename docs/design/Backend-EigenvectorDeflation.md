# Eigenvector deflation using existing matrix interfaces

Status (2026-10-29): Bounded review accepted and implementation completed. Targeted single-module
Lean checks passed; full integration validation passed (see the BI1 integration report). The user explicitly reopened suitable
omissions, and Matrix standing approval covers the existing-interface scope below.
No new deflation predicate, bundle, eigenvalue listing, or chosen basis is introduced.
Read the complete rules digest and Matrix topic rules before writing this record.
Backend source pin: `77514ce42a0e437d837797a063ac161f41022730`.

## Placement and consumers

Place the paired-basis existence, converse and scalar perturbation entry in existing
`Matrix/Spectral/EigenvectorPairing.lean`. Its consumer is the spectral exclusion
corollary below, then simple-eigenvalue perturbation. Place the block split and
one-coordinate characteristic factor in `Matrix/Spectral/EigenvalueListing.lean`,
which already contains a private one-column factorization used by triangularization.
Promote that existing factorization instead of duplicating it. The spectrum exclusion
and simple-root corollary can live in EigenvectorPairing, importing EigenvalueListing
after the bounded reviewer confirmed the local recursive import graph is acyclic. No higher layer imports.

The long paired-basis proof must be split into private basis/dual-row and conjugation
helpers, each below 80 lines. A private helper is not a new public interface.
All contracts below retain the full source scope, using arbitrary finite index types
and a field; the simple-root existence corollary also needs no algebraic closure.

```lean
variable {n : Type*} [Fintype n] [DecidableEq n] {K : Type*} [Field K]
```

## Exact contracts and provenance

### `exists_inv_mul_mul_apply_eq_of_dotProduct_ne_zero`

Backend `NLAlib/Matrix/Spectral/EigenvectorDeflation.lean:27` (`exists_isolated_eigenvector_similarity`).

```lean
theorem exists_inv_mul_mul_apply_eq_of_dotProduct_ne_zero {A : Matrix n n K} {x y : n → K} {μ : K}
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y) (hpair : y ⬝ᵥ x ≠ 0) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      (y ⬝ᵥ x)⁻¹ • Matrix.vecMulVec x y =
        S * Matrix.diagonal (Pi.single i 1) * S⁻¹
```

### `not_mem_spectrum_submatrix_of_rootMultiplicity_eq_one`

Backend `NLAlib/Matrix/Spectral/EigenvectorDeflationSpectrum.lean:25` (`not_mem_spectrum_submatrix_of_isolated_coordinate_of_simple`).

```lean
theorem not_mem_spectrum_submatrix_of_rootMultiplicity_eq_one
    (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hμ : M.charpoly.rootMultiplicity μ = 1) :
    μ ∉ spectrum K
      (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val))
```

### `exists_inv_mul_mul_apply_eq_of_rootMultiplicity_eq_one`

Backend `NLAlib/Matrix/Spectral/EigenvectorDeflationSpectrum.lean:51` (`exists_simple_eigenvalue_isolated_similarity`).

```lean
theorem exists_inv_mul_mul_apply_eq_of_rootMultiplicity_eq_one
    {A : Matrix n n K} {x y : n → K} {μ : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (hAx : A *ᵥ x = μ • x) (hyA : y ᵥ* A = μ • y)
    (hμ : A.charpoly.rootMultiplicity μ = 1) :
    ∃ (S : Matrix n n K) (i : n), IsUnit S ∧ Matrix.col S i = x ∧
      (∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) ∧
      (∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0) ∧
      (∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) ∧
      μ ∉ spectrum K ((S⁻¹ * A * S).submatrix
        (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val))
```

### `submatrix_eq_fromBlocks_of_isolated_coordinate`

Backend `NLAlib/Matrix/Spectral/EigenvectorDeflationBlocks.lean:22` (`submatrix_eq_fromBlocks_of_isolated_coordinate`).

```lean
theorem submatrix_eq_fromBlocks_of_isolated_coordinate (M : Matrix n n K) (i : n) (μ : K)
    (hcol : ∀ j, M j i = if j = i then μ else 0)
    (hrow : ∀ j, M i j = if j = i then μ else 0) :
    M.submatrix (Equiv.sumCompl (fun j => j = i)) (Equiv.sumCompl (fun j => j = i)) =
      Matrix.fromBlocks (Matrix.diagonal (fun _ : {j : n // j = i} => μ)) 0 0
        (M.submatrix (fun j : {j : n // j ≠ i} => j.val) (fun j : {j : n // j ≠ i} => j.val))
```

### Deliberately excluded scalar/row/column helper

The initial review considered backend
`EigenvectorDeflationBlocks.lean:54` (`submatrix_eq_fromBlocks_scalar_row_col`).
It has no independent consumer in this integration and was deliberately not implemented or
exported. Its elementary block decomposition is not counted among the seven retained public
contracts. A future concrete consumer can justify the appropriate private support.

### `nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div`

Backend `NLAlib/Matrix/Spectral/EigenvectorDeflationBlocks.lean:97` (`nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div`).

```lean
theorem nonsing_inv_mul_mul_apply_eq_dotProduct_mulVec_div
    (S E : Matrix n n K) (i : n) (x y : n → K)
    (hcol : Matrix.col S i = x) (hrow : ∀ j, S⁻¹ i j = y j / (y ⬝ᵥ x)) :
    (S⁻¹ * E * S) i i = (y ⬝ᵥ (E *ᵥ x)) / (y ⬝ᵥ x)
```

### `col_ne_zero_and_vecMul_eq_smul_of_inv_mul_mul_apply_eq`

Backend `NLAlib/Matrix/Spectral/EigenvectorDeflationConverse.lean:24` (`eigenpair_of_isolated_similarity`).

```lean
theorem col_ne_zero_and_vecMul_eq_smul_of_inv_mul_mul_apply_eq
    (A S : Matrix n n K) (i : n) (μ : K) (hS : IsUnit S)
    (hcol : ∀ j, (S⁻¹ * A * S) j i = if j = i then μ else 0)
    (hrow : ∀ j, (S⁻¹ * A * S) i j = if j = i then μ else 0) :
    Matrix.col S i ≠ 0 ∧ (fun j => S⁻¹ i j) ≠ 0 ∧
    (fun j => S⁻¹ i j) ⬝ᵥ Matrix.col S i = 1 ∧
    A *ᵥ Matrix.col S i = μ • Matrix.col S i ∧
    (fun j => S⁻¹ i j) ᵥ* A = μ • (fun j => S⁻¹ i j)
```

### Promoted characteristic factorization

Existing frontend `EigenvalueListing.lean:306`, shared with the new exclusion
consumer; make the existing declaration public, retaining its stronger scope.
The unused row hypothesis is also dropped from spectral exclusion above.

```lean
theorem charpoly_eq_X_sub_C_mul_charpoly_submatrix {M : Matrix n n K}
    {i₀ : n} {α : K} [DecidableEq {i // ¬i = i₀}]
    (hcol : ∀ i, M i i₀ = if i = i₀ then α else 0) :
    M.charpoly = (Polynomial.X - Polynomial.C α) *
      (M.submatrix (Subtype.val : {i // ¬i = i₀} → n) Subtype.val).charpoly
```

## Bounded review

Probability agent accepted the mathematical scopes, names and layers on 2026-10-29,
subject to the two amendments now recorded: explicit promotion signature and removal
of the redundant exclusion row hypothesis. Recursive import inspection found
EigenvalueListing does not reach EigenvectorPairing, so no new topic file is needed.
The unused scalar/row/column helper was deliberately excluded from implementation. The
remaining seven public contracts, including the promoted existing characteristic factorization,
passed targeted Lean checks. Full integration validation passed; see the BI1 integration report.

## Reuse searches and exclusions

Mathlib `LinearAlgebra/Basis/VectorSpace.lean:350` already provides
`exists_basis_of_pairing_ne_zero`; use it directly. Basis reindexing and
`Basis.invertibleToMatrix` give a square change of basis on the original finite type.
Frontend `EigenvalueListing.lean:277` has `charpoly_mul_mul_of_mul_eq_one`,
and `:306` has the private `charpoly_eq_X_sub_C_mul_charpoly_submatrix`.
Promote the latter, retaining its stronger one-column hypothesis (the row hypothesis
is not needed). Mathlib `Matrix.mem_spectrum_iff_isRoot_charpoly` and
`Polynomial.rootMultiplicity_mul` supply spectral exclusion. The existing
`rootMultiplicity_charpoly_eq_one_iff_dotProduct_ne_zero` in EigenvectorPairing,
combined with geometric multiplicity at most algebraic multiplicity and the supplied
nonzero eigenvector, supplies the simple-root pairing condition.

Do not add the backend similarity-charpoly and similarity-spectrum wrappers as new
public APIs: the existing similarity charpoly theorem and Mathlib spectrum/charpoly
bridge already supply these steps. Use local rewrites.
Do not add the backend adjugate converse: frontend
`exists_adjugate_eq_smul_vecMulVec` explicitly ports that result with the more general
kernel-one matrix statement. Substitution `M = μ • 1 - A` recovers the source scope.
The arbitrary matrix scalar/row/column decomposition is routine block infrastructure and
was excluded because no consumer needed it; no public export is claimed.

## Mathematical edge cases and review constraints

Nonzero pairing implies a nonzero right vector and hence a nonempty index type;
no redundant `[Nonempty n]` is imposed. For a singleton index, the complementary block
is empty and its characteristic polynomial is one, so spectral exclusion still holds.
Division is field division; no analytic norms, conjugation conventions or RCLike
restriction are introduced. The row `y` is bilinear; for a complex adjoint convention
the caller supplies the conjugated vector. The scalar perturbation entry identity
is valid even at zero pairing under its explicit row hypothesis, so it gains no
nonzero or invertibility assumption. The converse has normalized pairing exactly one.

Printed source locators carried by backend docstrings are not verified in this review;
use verified backend provenance in supporting API docstrings and do not copy unverified
book theorem numbers. The retained exact API signatures are implemented and have passed
targeted Lean checks; full integration validation passed (see the BI1 integration report).

Whole-library lint confirmed that the simple-root isolation corollary does not use
algebraic closure. Its assumption was removed: the native theorem strengthens the
backend contract to arbitrary fields, since supplied eigenvectors and a simple
characteristic root already give the required one-dimensional eigenspace.

The extraction-backed T11 advisory on the converse is a conjunction heuristic. Its two
conclusions say that the extracted row is nonzero and satisfies the left-eigenvector equation;
together they certify an eigenvector. They are not a lower/upper pair of numerical bounds.
