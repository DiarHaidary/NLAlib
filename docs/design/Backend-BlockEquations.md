# Block intertwiners and the Sylvester equation

2026-10-29. Status: Bounded review accepted and implementation completed. Targeted single-module
Lean checks passed; full integration validation passed (see the BI1 integration report).
Source rules also pass.
The user reopened suitable backend omissions. This extends the approved Matrix structured
spectral scope using existing Mathlib objects and the frontend Sylvester equation. No new
block predicate, algorithm, matrix wrapper or spectral-separation interface is proposed.

Backend source: `NLAlib/Matrix/Spectral/SylvesterBlocks.lean` at
`77514ce42a0e437d837797a063ac161f41022730`. Frontend base: `6491e75`, with the current
integration branch's previously reviewed Sylvester converse additions.

## Existing infrastructure and placement

Place the following declarations in `NLAlib/Matrix/Spectral/SylvesterEquation.lean`.
`Matrix-Structured.md` already assigns coprime characteristic polynomials and block
diagonalisation to this topic. Binary `Matrix.fromBlocks` remains appropriate for binary
splittings; Mathlib's dependent `Matrix.blockDiagonal'` expresses genuinely many-block
families without an NLAlib interface. Rows and columns may have different sizes in each block.
Empty block families and empty constituent spaces remain included.

Mathlib `Data/Matrix/Block.lean` supplies `blockDiagonal'` (570), its equal/off-diagonal
entry equations (595/599), `blockDiagonal'_mul` (676), `blockDiag'` (721), and
`blockDiag'_blockDiagonal'` (763). No existing frontend many-block theorem was found.
The frontend supplies `eq_zero_of_mul_eq_mul_of_isCoprime_charpoly`,
`existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly`, and
`isCoprime_charpoly_iff_disjoint_spectrum` in the target file.

## 1. Rectangular block intertwining

```lean
open scoped Matrix
namespace NLAlib
variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {m n : ι → Type*} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)]
  [∀ i, Fintype (n i)] [∀ i, DecidableEq (n i)]

theorem blockDiagonal'_mul_eq_mul_blockDiagonal'_iff_of_isCoprime_charpoly
    (A : ∀ i, Matrix (m i) (m i) K) (B : ∀ i, Matrix (n i) (n i) K)
    (h : ∀ i j, i ≠ j → IsCoprime (A i).charpoly (B j).charpoly)
    (X : Matrix (Σ i, m i) (Σ i, n i) K) :
    Matrix.blockDiagonal' A * X = X * Matrix.blockDiagonal' B ↔
      X = Matrix.blockDiagonal' (Matrix.blockDiag' X) ∧
        ∀ i, A i * Matrix.blockDiag' X i = Matrix.blockDiag' X i * B i
```

This strengthens backend `eq_blockDiagonal'_of_intertwines_of_disjoint_spectrum`
(SylvesterBlocks:78) in two ways: arbitrary fields via coprimality, and an iff instead of only
necessity. Off-diagonal coprimality is cross-family: it must relate `A i` to `B j`, not merely
assert pairwise separation within each family. No condition is imposed on matching blocks.

Proof: extract the `(i,j)` block of the equation. The private block-product identities below
reduce it to `A i * Xij = Xij * B j`. For `i ≠ j`, apply the existing homogeneous Sylvester
lemma. For `i=j`, retain the intertwining condition. Reconstruct the matrix using the Mathlib
entry equations. The reverse implication rewrites both products with `blockDiagonal'_mul`.

Two private proof helpers are needed, matching backend SylvesterBlocks:46 and :61:
the `(i,j)` submatrix of `blockDiagonal' A * X` is `A i * Xij`, and the corresponding
submatrix of `X * blockDiagonal' B` is `Xij * B j`. These are finite-sum computations and
need no public NLAlib vocabulary. If a second independent module later consumes them, move
semiring-general statements to `ForMathlib/Data/Matrix/Block.lean`; do not prematurely expose
field-specialized foundational lemmas under NLAlib.

## 2. The commutant

```lean
theorem commute_blockDiagonal'_iff_of_isCoprime_charpoly
    (A : ∀ i, Matrix (m i) (m i) K)
    (h : Pairwise fun i j => IsCoprime (A i).charpoly (A j).charpoly)
    (X : Matrix (Σ i, m i) (Σ i, m i) K) :
    Commute (Matrix.blockDiagonal' A) X ↔
      ∃ Y : ∀ i, Matrix (m i) (m i) K,
        X = Matrix.blockDiagonal' Y ∧ ∀ i, Commute (A i) (Y i)
```

Backend `commute_blockDiagonal'_iff` (SylvesterBlocks:106) is covered without an algebraic
closure restriction. Diagonal-block commutation is essential: being block diagonal alone does
not imply commutation. This is a direct consumer of the rectangular theorem, specializing
`B=A`, with the diagonal blocks supplied by `Matrix.blockDiag' X`.

For algebraically closed fields, the existing
`isCoprime_charpoly_iff_disjoint_spectrum` converts each backend spectral hypothesis. Separate
duplicated spectrum formulations are not needed for this integration: the source correspondence
records the conversion explicitly. Consumers include decomposition of centralizers and isolation
of invariant spectral clusters; no decomposition algorithm or bundled centralizer is introduced.

## 3. Complex spectral conditions for real or complex matrices

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {p q : Type*}
  [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

theorem isCoprime_charpoly_iff_disjoint_spectrum_complexify
    (A : Matrix p p 𝕜) (B : Matrix q q 𝕜) :
    IsCoprime A.charpoly B.charpoly ↔
      Disjoint (spectrum ℂ (complexify A)) (spectrum ℂ (complexify B))
```

Backend `existsUnique_real_sylvester_of_disjoint_complex_spectrum` (SylvesterBlocks:22)
uses precisely this descent. The new bridge plus
`existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly` proves its full rectangular real statement
without copying a real-only wrapper; it also accepts complex and any `RCLike` scalar type.
The same bridge makes sections 1 and 2 available over real matrices with disjoint complex
spectra, which avoids the false inference from disjoint real spectra.

Proof dependencies: frontend `charpoly_complexify` (`Functions/Complexification.lean:157`),
Mathlib `Polynomial.isCoprime_map` (`Algebra/Polynomial/FieldDivision.lean:493`), and the
target file's algebraically closed spectral criterion over `ℂ`. The scalar map is the existing
`RCLike.toComplex.toRingHom`; no new complexification object is required. Complexification
is already available in the target's dependency closure through `EigenvectorPairing`.

## Review and delivery

Bounded review checked the cross-family hypothesis, dependent rectangular shapes,
`Commute` orientation, public naming, and the bridge's `RCLike` scope. The core remains over
an arbitrary field; no analytic or norm hypothesis is introduced. No new imports should be
needed beyond an explicit narrow Mathlib block import if the current transitive closure changes.
Preserve the existing binary block theorem and the current integration's Sylvester converse.

Implementation and targeted validation used the parent's serial queue. Parent owns the
provenance ledger, root imports and remaining integration checks. The independent review accepted the math, names, dependent shapes and placement.
Verify the backend's Horn–Johnson 2013 Corollary 2.4.4.2 locator before citing it in a new
declaration; otherwise cite backend provenance only. The arbitrary-field/coprime generalization
and iff strengthening are recorded here.
