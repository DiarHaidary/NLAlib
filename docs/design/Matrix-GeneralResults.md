# Real similarity and structured matrix coverage

The source atlas at backend commit `77514ce42a0e437d837797a063ac161f41022730`
groups these statements under `real-similarity-descent` and `structured-matrices-def`.
The former already has two independent statements in `Matrix/Spectral/RealSimilarity.lean`.
Both receive the result identifier `real-similarity-descent`. The two structured matrix
results have their own mathematical identifiers `cauchy-determinant` and
`circulant-toeplitz`. Definitions are indexed by their declaration names.

## Objects and interfaces

The Toeplitz constructor `toeplitzMatrix t` takes diagonal parameters `t : ℤ → R`.
The Hankel constructor `hankelMatrix h` takes anti-diagonal parameters `h : ℕ → R`.
Both use ordinary integer differences or natural sums of zero-based row and column indices,
so `Fin` carries mathematical content. Both work for any entry type and rectangular shape.
Mathlib has no Toeplitz or Hankel constructor (searched). Their entry formulas are the
definitional bridge to `Matrix.of`. The structured matrices row in CONTRIBUTING §5.3
registers both constructors. Use Mathlib's `Matrix.circulant` and
`Matrix.circulant (Pi.single 1 1)` for the circulant constructor and cyclic shift.
The latter is the spelling already used in the existing commutation theorem.

Cauchy and Hilbert matrices use the existing `cauchyMatrix` and `hilbertMatrix`.
The Cauchy determinant uses Mathlib's Vandermonde matrices and determinants.
Real similarity uses `complexify`, `IsUnit` and `HasOrthonormalCols`, with no new
hypothesis interface.

## Statement shapes and placement

The metadata in `Matrix/Spectral/RealSimilarity.lean` points to these existing signatures:

```lean
theorem exists_real_similarity_of_complexify
    {ι n : Type*} [Fintype n] [DecidableEq n] {A B : ι → Matrix n n ℝ} {S : Matrix n n ℂ}
    (hS : IsUnit S.det) (h : ∀ i, complexify (A i) * S = S * complexify (B i)) :
    ∃ T : Matrix n n ℝ, IsUnit T.det ∧ ∀ i, A i * T = T * B i

theorem HasOrthonormalCols.exists_real_orthogonal_of_complexify
    {ι n : Type*} [Fintype n] [DecidableEq n] {A B : ι → Matrix n n ℝ}
    {U : Matrix n n ℂ} (hU : HasOrthonormalCols U)
    (h : ∀ i, complexify (A i) = U * complexify (B i) * Uᴴ) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ ∀ i, A i = Q * B i * Qᴴ
```

`Matrix/Structured/ToeplitzHankel.lean` owns the two entry-based constructors:

```lean
def toeplitzMatrix {R : Type*} {m n : ℕ} (t : ℤ → R) : Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j => t ((j.val : ℤ) - (i.val : ℤ))

def hankelMatrix {R : Type*} {m n : ℕ} (h : ℕ → R) : Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j => h (i.val + j.val)
```

`Matrix/Structured/Circulant.lean` owns the representation of a circulant by Toeplitz
parameters. The zero entry provides a parameter value for the empty matrix:

```lean
theorem exists_toeplitzMatrix_eq_circulant {R : Type*} [Zero R] {n : ℕ}
    (v : Fin n → R) : ∃ t : ℤ → R, toeplitzMatrix t = Matrix.circulant v
```

`Matrix/Structured/Cauchy.lean` owns the transport of the existing field-valued determinant
formula from `Fin` to arbitrary finite labels. The caller chooses one ordering for both
Vandermonde determinants:

```lean
theorem det_cauchyMatrix_eq_vandermonde {K n : Type*} [Field K] [Fintype n] [DecidableEq n]
    (e : n ≃ Fin (Fintype.card n)) (x y : n → K) (h : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      (Matrix.vandermonde (x ∘ e.symm)).det * (Matrix.vandermonde (y ∘ e.symm)).det /
        (∏ i : n, ∏ j : n, (x i + y j))
```

## Atlas clause read-back

* For arbitrary real square families and a common complex invertible similarity, right
  multiplication by that similarity converts conjugation into the existing intertwining
  hypothesis. The theorem supplies a real intertwiner whose determinant is a unit.
  Right multiplication by its inverse recovers the atlas conjugation
  equation. The family and matrix index types are unrestricted apart from the finiteness and
  decidable equality of the matrix index. Empty families and zero-dimensional matrices are
  included.
* For arbitrary real square families and one common complex orthonormal-column similarity,
  the second descent theorem supplies one common real orthonormal-column similarity. For
  square matrices that predicate is unitarity. Over the reals the adjoint is the transpose.
* The two constructors implement the atlas entry formulas for Toeplitz and Hankel matrices.
  The existing `cauchyMatrix_apply` gives the Cauchy entry formula over a field.
  `hilbertMatrix_eq_cauchyMatrix` specialises it with the real parameters
  `i ↦ i + 1` and `j ↦ j`.
* Nonzero Cauchy denominators suffice for the determinant formula. The existing
  `det_cauchyMatrix` gives the ordered product of differences on `Fin n`. The finite-label
  statement gives the product of the two Vandermonde determinants divided by the intrinsic
  denominator product. It includes repeated parameters and empty index types.
* Every circulant has ordinary Toeplitz parameters. In positive dimension
  `mul_circulant_single_comm_iff` gives the exact shift-commutation characterization.
  Its two directions together with the Toeplitz representation establish the atlas form
  “Toeplitz and commuting with the shift” without a second public iff theorem. In dimension
  zero any empty matrix equals the Toeplitz matrix of the zero parameters and the circulant
  of the empty vector, by subsingleton elimination. The representation theorem covers this
  endpoint.

## Consumers and sources

The constructors give ordinary diagonal and anti-diagonal parametrizations to structured
matvec and Fourier arguments. The circulant theorem supplies the Toeplitz representation
when replacing modular indices by ordinary diagonal parameters. The finite-label Cauchy
formula applies directly to Cauchy matrices on subtypes and reindexed coordinates. It reuses
`Matrix.det_reindex_self`, `Equiv.prod_comp`, `Matrix.det_vandermonde` and the existing
determinant proof. Real descent relates real canonical forms to their complex models.

The card provenance is Horn and Johnson (2013), §§0.9.7, 0.9.8 and 0.9.12 for structured
matrices, and Theorems 1.3.29 and 2.5.21 for descent. The backend's conjunction wrapper and
standalone empty case are covered by the independent statements and their specializations.
The backend's real-only Cauchy transport and circulant representation are generalized to the
same entry types as the current constructors. The Fin determinant remains available for
callers that directly use the ordered product of differences.
