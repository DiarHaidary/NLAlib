# Matrix approximation and real normal specializations

2026-10-29. Status: Bounded review accepted and implementation completed. Targeted single-module
Lean checks passed; full integration validation passed (see the BI1 integration report).
The current user instruction reopens omitted backend results when existing frontend interfaces
support them. This note amends the omissions in `Matrix-Factorizations.md` (scaled orthogonal
Procrustes) and `Matrix-Structured.md` section 9 (real normal specializations and the
Hermitian-part converse). It adds no definitions, hypothesis interfaces or algorithm targets.
Frontend base `6491e7528c1b1e68e46301cde6a76ae153e8e834`; backend source revision
`77514ce42a0e437d837797a063ac161f41022730`.

## 1. Nearest scaled isometry in Frobenius norm

Backend source: `Matrix/Factorizations/ScaledOrthogonal.lean`, lines 19-115. The frontend
already has the unscaled all-unitarily-invariant-norm theorem in `Factorizations/Polar.lean`;
do not duplicate that theorem or the backend's old norm infrastructure. Extend the existing
`Polar.lean` with the following Frobenius/scalar optimization API. This stays in Matrix layer 0.

The result is generalized from real square matrices to `RCLike` tall matrices. A polar
extension `U` has orthonormal columns and `U * CFC.sqrt (Aᴴ * A) = A`; it need not equal
`polarFactor A` when `A` is rank deficient. Requiring the canonical partial polar factor to be
an isometry would incorrectly remove singular matrices. The scalar is real, including negative
competitor scalars; complex phases are already absorbed by the isometry. Empty column type is
included, with Lean's total division convention giving scalar zero and optimum zero.

```lean
open scoped Matrix MatrixOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}
  [Fintype m] [Fintype n] [DecidableEq n]

theorem HasOrthonormalCols.frobNorm_sub_smul_sq_of_mul_sqrt_eq
    {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᴴ * A) = A) (c : ℝ) :
    frobNorm (A - c • U) ^ 2 =
      frobNorm A ^ 2 - 2 * c * nuclearNorm A + (Fintype.card n : ℝ) * c ^ 2

theorem HasOrthonormalCols.frobNorm_sq_sub_le_frobNorm_sub_smul_sq
    {U : Matrix m n 𝕜} (hU : HasOrthonormalCols U) (A : Matrix m n 𝕜) (c : ℝ) :
    frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ) ≤
      frobNorm (A - c • U) ^ 2

theorem HasOrthonormalCols.frobNorm_sub_smul_sq_eq_of_mul_sqrt_eq
    {A U : Matrix m n 𝕜} (hU : HasOrthonormalCols U)
    (hA : U * CFC.sqrt (Aᴴ * A) = A) :
    frobNorm (A - (nuclearNorm A / (Fintype.card n : ℝ)) • U) ^ 2 =
      frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ)

theorem isLeast_frobNorm_sub_smul_sq (A : Matrix m n 𝕜)
    (hcard : Fintype.card n ≤ Fintype.card m) :
    IsLeast {z : ℝ | ∃ (c : ℝ) (U : Matrix m n 𝕜),
      HasOrthonormalCols U ∧ frobNorm (A - c • U) ^ 2 = z}
      (frobNorm A ^ 2 - nuclearNorm A ^ 2 / (Fintype.card n : ℝ))
```

Proof infrastructure verified: `exists_hasOrthonormalCols_mul_sqrt_eq` (Polar:265),
`frobNorm_sub_sq`, real-scalar Frobenius identities, and
`abs_frobInner_le_nuclearNorm_mul_specNorm` (Nuclear:234). Establish the polar trace pairing
from `A=U sqrt(AᴴA)`, `UᴴU=1`, and the existing trace/square-root nuclear norm identity;
reuse any existing Procrustes lemma after searching before proving. The Frobenius square of an
isometry is the column count. Complete the scalar square at positive dimension, splitting off
empty columns before division. Attainment uses the existing polar-extension existence theorem.
No rank/full-column-rank hypothesis is permitted. Wide coisometry variants are obtained by
adjoint and are not separate declarations absent a consumer.

Consumers: scaled Procrustes fitting and approximation by an isotropic frame. Existing nearest
unitary API is the unscaled comparison; the new optimum optimizes the scalar as well.
The first three declarations are supporting API; the attained minimum is the headline.
Source citation from backend: Horn-Johnson 2013 section 7.4.6, to be checked against the book
before a new headline citation is asserted. Preserve the backend provenance and distinguish the
rectangular/complex/empty generalization. Do not add old `frobSq` or `avg` definitions.

## 2. Converse Hermitian-part majorization

Backend source: `Matrix/Inequalities/HermitianPartConverse.lean:26-95`.
Placement: existing `Matrix/Spectral/HermitianPart.lean` beside
`majorized_re_of_isEigenvalueListing`. The parent completed a separate orthogonality addition
and explicitly handed over the file; that addition was preserved.

```lean
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_isEigenvalueListing_hermitianPart_of_majorized
    {x : n → ℝ} {z : n → ℂ} (h : Majorized (fun i => (z i).re) x) :
    ∃ A : Matrix n n ℂ, IsEigenvalueListing A z ∧
      IsEigenvalueListing (hermitianPart A) (fun i => (x i : ℂ))

theorem majorized_re_iff_exists_isEigenvalueListing_hermitianPart
    (x : n → ℝ) (z : n → ℂ) :
    Majorized (fun i => (z i).re) x ↔
      ∃ A : Matrix n n ℂ, IsEigenvalueListing A z ∧
        IsEigenvalueListing (hermitianPart A) (fun i => (x i : ℂ))
```

No sortedness or distinctness assumption; the listing certifies multiplicity, including empty
dimension. This is intrinsically complex data, so `ℂ` is appropriate. Use frontend
`exists_hasOrthonormalCols_diag_eq_of_majorized` (Inequalities/SchurHorn:370), then double the
strict upper triangle of its real symmetric output and insert `z` on the diagonal. The
Hermitian part is the complexified symmetric matrix and the triangular matrix has listing `z`.
Use `complexify`, not backend `realMatrixComplexification`; use `hermitianPart`, not
`selfAdjointPart` as the public expression. Arbitrary finite indices can be ordered using
`Fintype.equivFin`; no extra public order parameter is needed.

The iff's reverse implication is the existing `majorized_re_of_isEigenvalueListing`.
Consumers: spectral realization and sharpness of the existing forward majorization theorem.
Retain the existing `real-part-majorization` result family. Backend cites Horn-Johnson 2013
Theorem 4.3.50; verify locator before adding the new citation.

## 3. Real skew-symmetric and orthogonal canonical forms

Backend source: `Matrix/Spectral/RealNormalSpecializations.lean:16-119`.
Placement: existing `Matrix/Spectral/RealSchur.lean`, immediately after its real-normal theorem.
Use existing `IsRealSchurForm T` plus the off-diagonal skew relation, rather than copying
`IsRealNormalForm`. A Schur-form predicate alone does not express block diagonality, so retain
the off-diagonal relation explicitly. Over the real field all public adjoints are still `ᴴ`.
Mathlib has no directly applicable standard skew-Hermitian matrix predicate (its bilinear-form
`Matrix.IsSkewAdjoint` is relative to a form); retain the equation `Aᴴ = -A`.

```lean
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem exists_hasOrthonormalCols_isRealSchurForm_of_conjTranspose_eq_neg
    {A : Matrix n n ℝ} (hA : Aᴴ = -A) (order : Fin (Fintype.card n) ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᴴ ∧
      IsRealSchurForm (T.submatrix order order) ∧
      (∀ i j, i ≠ j → T i j = -T j i) ∧ ∀ i, T i i = 0

theorem HasOrthonormalCols.exists_isRealSchurForm
    {A : Matrix n n ℝ} (hA : HasOrthonormalCols A)
    (order : Fin (Fintype.card n) ≃ n) :
    ∃ Q T : Matrix n n ℝ, HasOrthonormalCols Q ∧ A = Q * T * Qᴴ ∧
      IsRealSchurForm (T.submatrix order order) ∧
      (∀ i j, i ≠ j → T i j = -T j i) ∧
      (∀ i, (∀ j, j ≠ i → T j i = 0) → T i i = -1 ∨ T i i = 1) ∧
      (∀ i j : Fin (Fintype.card n), (j : ℕ) + 1 = (i : ℕ) →
        T (order i) (order j) ≠ 0 →
        T (order j) (order j) ^ 2 + T (order i) (order j) ^ 2 = 1)
```

These preserve the backend's arbitrary finite dimensions and explicit order equivalence, rather
than silently narrowing to `Fin k`. The existing frontend normal-form theorem is Fin-indexed;
apply it to `A.submatrix order order` and transport the two factor matrices back. This is an
implementation step, not a new public family of transport lemmas. Empty dimension is included.

For the skew case, `Aᴴ=-A` gives normality; conjugation preserves the equation and makes each
diagonal entry zero. For the orthogonal case, orthogonality implies normality; conjugation
preserves orthonormal columns. A singleton column has diagonal entry of square one. In an active
two-by-two block, use the existing quasi-triangular sparsity plus off-diagonal skew relation to
isolate the two entries in its unit column norm, giving the unit-circle identity. The backend's
bundled coefficient helper is split into two private lemmas unless a second file consumes it.
Search existing frontend private block-support lemmas before reproducing that argument.

Consumers: explicit rotations/reflections from real orthogonal matrices and pure rotation planes
from skew generators. No uniqueness or canonical ordering of the blocks is claimed. Reuse the
existing normal-matrices result family if current metadata permits; verify the backend's
Horn-Johnson 2013 Theorem 2.5.4 locator against the frontend's 2.5.8 before citing either.

## 4. Review and delivery

The backend-proposed printed locators for scaled approximation and Hermitian-part realization
remain unverified. Primary book links were inaccessible (404 or login), so no verification is
claimed. The new public headline docstrings use the repository's `No printed source.` convention
and explain their named backend provenance: the exact rectangular generalization, and the iff
assembled from ported realization and the existing forward bound. This is not a novelty claim.
Unrelated preexisting citations are unchanged.

The independent bounded review accepted the names, polarity of majorization, polar-extension
requirement, negative scales, empty-column handling, and arbitrary finite real-form indexing.
The parent authorized implementation in the three existing topic files; its Hermitian-part
orthogonality addition is preserved. No new interfaces were introduced.

Review confirmed names, majorization direction, the polar-extension requirement, negative scales,
empty columns and the real block structure. All implemented statements passed targeted Lean
checks. Ledger mappings must retain their direct, derived or private-helper distinctions;
the complex rectangular scaled minimum covers the backend's square nonempty and empty minima,
but its left-polar trace spelling is only covered after checking the trace/nuclear bridge.

Implementation preserved concurrent changes and passed source rules and targeted Lean checks
in the parent's single build queue. Parent owns
ledger, status and generated roots. No new root import is needed for these existing topic files.
The broader nonlinear polar iterations and new approximation algorithms remain separate stages.

The extraction-backed T7 advisories on the two new real canonical-form theorems are intentional.
Their conclusions describe real one- and two-dimensional blocks, including singleton signs
`-1` and `1` for orthogonal matrices. A complex unitary matrix instead permits arbitrary unit
phases in singleton blocks, so the same conclusion cannot be generalized to `RCLike`.
