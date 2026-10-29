# Backend spectral and scalar integration

Status (2026-10-29): Bounded review accepted and implementation completed. Targeted single-module
Lean checks passed; full integration validation passed (see the BI1 integration report).

The user explicitly requested integration of omitted and unaccounted backend results when the
frontend infrastructure is suitable. This reopens the omission decisions for multiplicities and
the Sylvester converse recorded in Matrix-Structured §9 (the paragraph beginning “Not ported,
by decision”). This amendment retains the existing vocabulary, namespaces and dependency layers.
It does not authorize new algorithm targets or a new hypothesis interface. The nearest-PSD amendment uses native CFC at an arbitrary real floor and the existing
`hermitianPart`, not a new object (see section 4).

Source snapshots: frontend `6491e7528c1b1e68e46301cde6a76ae153e8e834`; backend
`tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`. Source inspection and
Mathlib searches informed this note. The implemented statements passed targeted Lean checks
and preserve Apache-2.0 attribution and the frontend file/docstring conventions. No backend
package dependency is introduced.

## 1. Diagonalizable multiplicities

Placement: existing `NLAlib/Matrix/Spectral/Diagonalizable.lean`, after the semisimplicity API.
Use that file's arbitrary finite index types and field, not a new matrix predicate.

```lean
variable {K : Type*} [Field K] {n : Type*} [Fintype n] [DecidableEq n]

theorem IsDiagonalizable.finrank_eigenspace_eq_rootMultiplicity
    {A : Matrix n n K} (hA : IsDiagonalizable A) (μ : K) :
    Module.finrank K (Module.End.eigenspace A.toLin' μ) =
      A.charpoly.rootMultiplicity μ

theorem isDiagonalizable_iff_forall_finrank_eigenspace_eq_rootMultiplicity
    [IsAlgClosed K] (A : Matrix n n K) :
    IsDiagonalizable A ↔ ∀ μ : K,
      Module.finrank K (Module.End.eigenspace A.toLin' μ) =
        A.charpoly.rootMultiplicity μ
```

Consumer: verify diagonalizability from independently computed eigenspace dimensions; expose
the multiplicity conclusion of the existing diagonalization interface to spectral arguments.
The first theorem holds over any field; only the converse needs algebraic closure. Scalars
outside the spectrum and empty matrix index types remain included; no `Nonempty` assumption.

Reuse verified by source search:

- Frontend `IsDiagonalizable.isSemisimple` and
  `isDiagonalizable_iff_iSup_eigenspace_eq_top` in the destination file.
- Mathlib `LinearMap.finrank_maxGenEigenspace_eq`,
  `Mathlib/LinearAlgebra/Eigenspace/Zero.lean:202`.
- `IsFinitelySemisimple.maxGenEigenspace_eq_eigenspace`, already used by the frontend's
  simultaneous diagonalization proof, and `Module.End.iSup_maxGenEigenspace_eq_top`.
- `Submodule.eq_of_le_of_finrank_eq` and `Matrix.charpoly_toLin'`.

Proof plan: semisimplicity identifies ordinary and maximal generalized eigenspaces; Mathlib
computes the latter's dimension. For the converse, equal finite dimensions and inclusion identify
the two spaces, and the generalized spaces span. No duplicate standalone generalized-eigenspace
API is needed.

Backend provenance: `Matrix/Spectral/Diagonalizable.lean:185–212`,
`IsDiagonalizable.finrank_eigenspace_eq_rootMultiplicity` and
`isDiagonalizable_iff_finrank_eigenspace_eq_rootMultiplicity`.
Citation: `[HornJohnson2013, Theorem 1.4.10]`. Preserve the existing result-id policy; do not
create a competing almost-identical identifier just to account for the two components.

## 2. Sylvester converse

Placement: existing `NLAlib/Matrix/Spectral/SylvesterEquation.lean`, importing the existing
`EigenvectorPairing` file. This stays in Matrix layer 0. The public expression is the matrix
equation; do not recreate the backend's `sylvesterLinearMap` definition.

```lean
variable {K : Type*} [Field K] [IsAlgClosed K]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem forall_eq_zero_iff_disjoint_spectrum
    (A : Matrix m m K) (B : Matrix n n K) :
    (∀ X : Matrix m n K, A * X = X * B → X = 0) ↔
      Disjoint (spectrum K A) (spectrum K B)

theorem forall_existsUnique_mul_sub_mul_eq_iff_disjoint_spectrum
    (A : Matrix m m K) (B : Matrix n n K) :
    (∀ C : Matrix m n K, ∃! X : Matrix m n K, A * X - X * B = C) ↔
      Disjoint (spectrum K A) (spectrum K B)
```

Bounded review fixed the first name as `forall_eq_zero_iff_disjoint_spectrum`, avoiding
an `_of_` segment before the main `_iff`. The second is the public solvability criterion. There is no
separate `Function.Bijective` wrapper unless a concrete consumer needs it.

Consumers: uniqueness tests for matrix equations and block diagonalization; detect failure from
a common eigenvalue. Both rectangular dimensions may be zero. Algebraic closure is explicit;
do not claim the spectral converse over an arbitrary field.

Reuse: frontend `eq_zero_of_mul_eq_mul_of_isCoprime_charpoly`,
`existsUnique_mul_sub_mul_eq_of_isCoprime_charpoly`,
`isCoprime_charpoly_iff_disjoint_spectrum` in the destination;
`exists_mulVec_eq_smul_of_mem_spectrum` and `exists_vecMul_eq_smul_of_mem_spectrum` in
`EigenvectorPairing.lean:47,61`. A common eigenvalue yields a nonzero rank-one outer product
intertwining the two matrices. Mathlib matrix multiplication/outer-product identities discharge
the computation; search for them before adding any helper. The reverse direction is existing
frontend API. Unique solvability at right-hand side zero supplies the first criterion.

Backend provenance: `Matrix/Spectral/SylvesterQualitative.lean:96–129`,
`sylvesterLinearMap_injective_iff_disjoint_spectrum` and
`sylvesterLinearMap_bijective_iff_disjoint_spectrum`.
Citation: `[HornJohnson2013, Theorem 2.4.4.1]`. These extend the existing `sylvester-equation`
result; they do not replace or weaken its arbitrary-field coprime-polynomial theorem.

## 3. Gamma half-shift

Placement: existing `NLAlib/ForMathlib/Analysis/SpecialFunctions/Gamma/Basic.lean`, in namespace
`Real` (not `NLAlib`), with a specific import of Mathlib's Gamma Bohr–Mollerup file if needed.

```lean
theorem Real.Gamma_add_half_le_mul_sqrt {x : ℝ} (hx : 0 < x) :
    Real.Gamma (x + 1 / 2) ≤ Real.Gamma x * Real.sqrt x
```

Consumer: Gamma-ratio estimates in chi-square moments and inverse moments. The strictly positive
domain is essential; do not extend across Gamma's poles. This is an upstream-suitable scalar
fact and introduces no NLAlib vocabulary.

Search found Mathlib `Real.Gamma_mul_add_mul_le_rpow_Gamma_mul_rpow_Gamma` in
`Analysis/SpecialFunctions/Gamma/BohrMollerup.lean:58`; no exact half-shift theorem was found in
the Gamma folder. Apply log-convexity at `x` and `x+1`, then `Real.Gamma_add_one` and square-root
identities. Frontend Gamma/Basic already contains related inequalities but no half-shift bound.
Backend source: `ForMathlib/Analysis/SpecialFunctions/Gamma.lean:24–33`; ledger says “not needed”.
Retain its source attribution, but do not invent a printed locator: the docstring should identify
this as the displayed consequence of Mathlib's log-convexity theorem and cite a verified source
only if a precise one is available. No new headline result id is necessary for this supporting API.

## 4. Positive-part projection: final arbitrary-floor amendment

The initial zero-floor proposal was superseded before final implementation by
[Matrix-PositivePart](Matrix-PositivePart.md). The final API uses
`cfc (max a) (hermitianPart A)` for every real floor `a`, over `RCLike`, including singular,
non-Hermitian and empty inputs. It supplies the variational inequality, minimum and unique
minimizer, nonexpansiveness, and exact squared distance in
`Matrix/Functions/PositivePart.lean`, plus Hermitian-part orthogonality in its owning file.
The full-floor amendment received bounded review and all statements passed targeted Lean
checks. The obsolete zero-floor signatures are not exports or separate port claims.
Named backend provenance, verified Higham provenance and the scope generalizations are recorded
in the linked final note. Full integration checks passed; see the BI1 integration report.

## 5. Delivery and excluded families

Implementation should update port-ledger rows to exact declared names, preserve source notes,
update the status record and generated root import for the new PositivePart file, and run the
repository's required checks. Do not mark a specialized theorem as a full general port. No
protected algorithm target files, new global instances or dependency direction changes are needed.

Rational Christoffel–Uvarov modifications remain outside this bounded design: the backend's
moment-functional bundles and divided-polynomial integrability predicates need a separate native
design against frontend `IsOrthogonalPolynomial`/`IsMomentPosDef`. General block commutants
were subsequently implemented under
[Backend-BlockEquations](Backend-BlockEquations.md); other omitted helpers remain outside
this initial note. Reconcile already covered private helpers instead of duplicating them, notably
`IsDiagonalizable.of_surjective_intertwiner` versus frontend private `IsDiagonalizable.of_surjective`.

## Gaussian consumer follow-up: implemented scalar ratio

The inverse chi-square integration identified this further scalar dependency. The subsequent
bounded review in [Backend-GaussianIntegration](Backend-GaussianIntegration.md) accepted it;
it is implemented and passed targeted Lean validation:

```lean
theorem Real.sqrt_pi_div_rpow_mul_Gamma_lt_rpow {d : ℕ} (hd : 5 ≤ d) :
    Real.sqrt Real.pi /
        (2 ^ (((d : ℝ) - 1) / 2) * Real.Gamma ((d : ℝ) / 2)) <
      (3 / (d : ℝ)) ^ (((d : ℝ) - 1) / 2)
```

It is implemented in Gamma/Basic after bounded review. Backend provenance is private
`sqrt_pi_div_lt_rpow`, `Probability/ChiSquare/ChiSquare.lean:503–606`. Its source proof uses
Gamma duplication, the half-shift bound, factorial Stirling, and an exponential comparison.
The implementation splits that proof into mathematical steps below the 80-line limit.
Its strict bound and `d ≥ 5` condition passed targeted checks without new vocabulary.
