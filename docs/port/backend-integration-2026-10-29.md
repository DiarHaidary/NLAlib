# Backend results on existing frontend interfaces

Stage BI1, 2026-10-29. Frontend base: `6491e7528c1b1e68e46301cde6a76ae153e8e834`.
Backend source: `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`.
The user's request reopens omitted and unaccounted results where the frontend infrastructure
supports them. The scope is mathematical API integration; the frontend does not acquire a
dependency on the backend checkout.

## Implemented families

| Family | Native interface and placement |
|---|---|
| Spectral multiplicity and principal-submatrix survival | `IsDiagonalizable`, eigenspaces and `spectrum`; `Matrix/Spectral/Diagonalizable` |
| Changes of eigenbasis and left-right deflation | Ordinary matrices, `IsUnit`, basis columns and bilinear pairings; `EigenvectorPairing` and `EigenvalueListing` |
| Common triangularization | `HasOrthonormalCols`, `IsUpperTriangular`, and existing QR; `Simultaneous` |
| Sylvester converse and block commutants | Coprime characteristic polynomials, `Commute`, and Mathlib dependent blocks; `SylvesterEquation` |
| Nearest matrix above a spectral floor | `cfc (max a) (hermitianPart A)`; new topic file `Matrix/Functions/PositivePart` |
| Nearest scaled isometry | Isometric polar extensions and `nuclearNorm`; existing `Factorizations/Polar` |
| Hermitian-part spectral realization | `Majorized`, `IsEigenvalueListing`, and `complexify`; existing `HermitianPart` |
| Real skew and orthogonal forms | `IsRealSchurForm` and explicit block relations; existing `RealSchur` |
| Stationary iteration and projector limits | `richardsonIterate`, `specRadius`, and `IsIdempotentElem`; `Richardson` and `PowerBounds` |
| Inverse Gaussian moments | Existing `HasLaw` and `gaussianVector`; `ChiSquareMoments` |
| Gaussian lower tails and maxima | Existing scalar/vector Gaussian laws; `GaussianConcentration` and `GaussianMoments` |
| Scalar Gamma estimates | Proper `Real` namespace in `ForMathlib/Analysis/SpecialFunctions/Gamma/Basic` |

There are no new algorithm targets or hypothesis interfaces. The three numerical factors use
the named-bound registry. The existing one-column characteristic factorization is promoted from
private support because the deflation theorem is now a second consumer. Foundational helpers
and transport wrappers are not exported merely to preserve a backend name.

The source additions comprise 53 authored public theorems, one promoted supporting theorem,
and three named constants. Environment extraction consequently adds 60 public declarations:
the 54 explicit theorems, three constant definitions, and their three generated value lemmas.
The shared Gamma estimate also replaces an existing private duplicate in the Gaussian inverse
spectral-moment file; both consumers now use the common `Real` lemma.

## Scope read-back

The spectral-floor projection retains every real floor, either scalar field, non-Hermitian
inputs and empty matrices. Its feasibility, variational inequality, unique Frobenius minimum,
nonexpansiveness and exact distance are separate API results. The scaled-isometry theorem
allows singular rectangular matrices with at least as many rows as columns, negative competitor
scales, and empty columns. It uses an isometric polar extension rather than assuming the
canonical partial polar factor has full column rank.

Deflation preserves the normalized dual row and rank-one projector, and excludes a simple
eigenvalue from the complementary block. The characteristic-factor and spectral-exclusion
statements need only the isolated column. The real canonical forms preserve the specified
finite-index enumeration, off-diagonal skew relation, singleton signs and active-block
unit-circle equation. No order or uniqueness of the blocks is asserted.

The Sylvester core uses arbitrary fields and coprime characteristic polynomials; its converse
uses algebraic closure. Many-block separation is cross-family, and matching diagonal blocks
still must commute. The real spectral specialization uses complexification. Richardson's
square-system criterion retains all right-hand sides, unique solutions, and all initial vectors;
it is stronger than convergence from a single fixed point. Projector limits include oblique
idempotents and handle exponent zero separately from the positive-power identity.

The uniform inverse-moment bounds require `2*q+1 <= d`; they are not claimed throughout the
larger integrability domain `q < d/2`. The factor-three bound additionally needs `d >= 5` and
`q > 0`; the factor-four statement includes `q=0`. HMT Lemma A.10 prints the rooted bound for
`q >= 2`; the extension to every positive admissible exponent is documented as a consequence
of moment comparison. Gaussian maximum bounds use the finite Pi norm, meaning the maximum
absolute coordinate, not the Euclidean norm.

## Provenance accounting

The ledger revisits 78 previously omitted or unaccounted backend theorem entries: 38 previously
had a null destination and 40 had no decision. Of these, 66 now point to public frontend API.
The remaining 12 have explicit decisions for native Mathlib results, private support,
algebraic reexpression, or unused wrappers. Previous ledger reasons are retained in the notes.
Five already-recorded references were checked without being counted again.

Public-target mappings include both new ports and existing mathematical coverage. In particular,
the real Haar top-Gram and Gaussian inverse-vector entries are derived correspondences using
existing native laws and theorems. They are not new cross-repository bridge proofs. Ledger notes
record law identification, normalization, and companion results rather than asserting identical
signatures. Private helpers and inlined proofs are not counted as new public theorem coverage.

These decisions do not assert that all 11,315 formerly unmatched names represent absent
mathematics, or that this stage ports all of them. New algorithm/output stages such as diagonal
estimation, adaptive Cholesky histories, residual certificates, tail averaging, RQI and QR
iteration remain separate designs. Rational polynomial modifications and sparse, Wishart and
free-probability machinery likewise require additional native infrastructure. The complex Haar
top-Gram results are not mapped to the frontend's real-only Haar law.

## Review and validation

Exact signatures received bounded independent review before implementation, under the current
user instruction and the recorded Matrix/probability standing approvals. The available-agent
author/reviewer fallback follows the precedent in `docs/design/Gaussian-FourthMoments.md`;
it is not represented as an unavailable-model review. A second read-back checked the final
Lean statements and the derived ledger correspondences against the source scopes.

Every changed theorem module passed a targeted `lake lean` check with repository options.
Final integration validation passed:

- Warning-fatal build of `NLAlib`, `NLAlibScaffold` and `NLAlibTools`, all three generated-root
  checks, and the full rehash/freshness check.
- Axiom/safety audit of 14,660 declarations with zero violations; all 14 Lean linters;
  program checks, all five registered targets and three registered trees, and access-model
  fixtures. Kernel replay checked 16,601 constants with zero violations. All eight replay
  fixtures passed, including the intentionally permissive non-strict case.
- Extraction-backed contribution/naming checks: 110 rules, zero new errors. The unchanged
  repository retains 73 previously baselined findings. Ten advisory warnings occur in touched files:
  seven predate this change; the two new real-form generality advisories and the eigenvector
  conjunction advisory are explained in their design notes. No baseline or allowlist was changed.
- Bibliography, port ledger, named constants, and generated-rule checks; 70 Python and 14
  JavaScript regression tests; KaTeX validation of 9,576 docstrings and 36,152 math spans.
- The duplicate audit has no public/public or private/public duplicates. Its one remaining
  private/private pair predates this change. The dependency-reuse report was inspected.

Native Windows validation used canonical LF copies of the unchanged target registry and
canonical checkout bytes for `lake-manifest.json` and `lakefile.toml`; each matched its Git
blob and approved hash. An external launcher passes `--zero` to Git's unchanged GNU
`sha256sum`, preventing a filename-escape prefix from entering the validator's digest token.
The original approval file and validator were unchanged. Replay fixtures ran with Windows
path separators. Rebuilding and rehashing after these adjustments left all 3,074 compiled
proof-artifact files byte-identical. The optional `NLAlibTools` NumPy differential test was
skipped because NumPy was unavailable; required checks passed.

Higham's Theorem 2.1 and HMT's Lemma A.10 were checked against their primary texts. Two proposed
Horn-Johnson locators for new approximation headlines could not be verified from an accessible
primary text; those new docstrings retain backend provenance without asserting the locators.
The corresponding design note records this limitation. Existing citations outside these new
headlines were not re-audited.
