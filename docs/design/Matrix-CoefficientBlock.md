# Coefficient block partial transpose

The atlas card `coefficient-block-partial-transpose` concerns a finite family of
Hermitian matrices over `RCLike`. The two norm bounds use the same pair of
coordinate swaps as the backend at `77514ce42a0e437d837797a063ac161f41022730`.
The source is [Bandeira et al., arXiv:2610.01982v1](https://arxiv.org/html/2610.01982v1),
Section 1.1, equations (7)–(8) and Propositions 1.3–1.4.

## Objects and interfaces

| Concept | Lean spelling | Existing object used |
|---|---|---|
| Coefficient block matrix | `coefficientBlock A` | Matrix with block `(i,j)` equal to `A j * A i` |
| Matrix variance | `coefficientVariance A` | Finite sum of `A i * A i` |
| Entry covariance | `coefficientCovariance A` | Sum of outer products of row-major vectors, using `Function.uncurry` and `Matrix.vecMulVec` |
| Coefficient block parameter | `coefficientBlockKappa A` | `Real.sqrt (eigenvalue (coefficientBlock A) 0)` |
| Covariance compression | `coefficientCovarianceLift A`, `coefficientCovarianceSwap` | Mathlib Kronecker product with identity and coordinate permutation |

Mathlib and NLAlib were searched for the coefficient block and covariance
objects. The definitions use existing matrix primitives and need no new
hypothesis predicate. The family hypotheses use `Matrix.IsHermitian` and
`Pairwise` commutation. The parameter inherits the zero convention for empty or
non-Hermitian coefficient blocks from `eigenvalue`.

## Statements and consumers

In these signatures `ι`, `d` and `r` are arbitrary finite index types and `𝕜`
is an `RCLike` field. Bounds are separate statements for the two source
quantities so consumers can use either without unpacking a conjunction.

```lean
theorem isHermitian_coefficientBlock (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) : (coefficientBlock A).IsHermitian

theorem eigenvalue_coefficientBlock_zero_nonneg (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) : 0 ≤ eigenvalue (coefficientBlock A) 0

theorem coefficientBlock_eq_conjTranspose_coefficientCovarianceLift_mul_permMatrix_mul
    [DecidableEq d] (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlock A = (coefficientCovarianceLift A)ᴴ *
      coefficientCovarianceSwap.permMatrix 𝕜 * coefficientCovarianceLift A

theorem specNorm_coefficientBlock_le_specNorm_coefficientVariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientBlock A) ≤ specNorm (coefficientVariance A)

theorem specNorm_coefficientBlock_le_specNorm_coefficientCovariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientBlock A) ≤ specNorm (coefficientCovariance A)

theorem coefficientBlockKappa_le_sqrt_specNorm_coefficientVariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa A ≤ Real.sqrt (specNorm (coefficientVariance A))

theorem coefficientBlockKappa_le_sqrt_specNorm_coefficientCovariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa A ≤ Real.sqrt (specNorm (coefficientCovariance A))

theorem coefficientBlockKappa_eq_sqrt_specNorm_coefficientVariance_of_pairwise_commute
    (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    coefficientBlockKappa A = Real.sqrt (specNorm (coefficientVariance A))

theorem coefficientBlockKappa_kronecker_one [DecidableEq r] [Nonempty r]
    (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa (fun i => A i ⊗ₖ (1 : Matrix r r 𝕜)) = coefficientBlockKappa A
```

Gaussian matrix series consumers can use the block as a Hermitian operator,
apply the exact covariance compression, use either scalar bound, and transfer
the parameter across identity amplification. The two `min` conclusions of
the atlas follow by `le_min` from the pairs of inequalities.

The Hermitian property, largest-eigenvalue sign, norm bounds and equality for
commuting families all admit empty coefficient or coordinate index types.
Amplification requires a nonempty factor even when the original coefficient
block is indefinite. The source's nonempty complex instances therefore use
the same statements and definitions with `𝕜 := ℂ`.

## Placement and reuse

`Matrix/Structured/CoefficientBlock.lean` contains the definitions, the two
finite compressions and the main results. It uses the existing spectral norm
and eigenvalue API and Mathlib's finite permutation matrix norm bound. The
variance lift and its swap are local to the proof. The commuting equality
identifies the block with a Gram matrix and uses the equality of Gram norms.

`Matrix/Structured/Kronecker.lean` gains the largest-eigenvalue identity for
tensoring a Hermitian matrix with a nonempty identity. Its proof specializes
the existing Kronecker sum theorem and handles the empty original index with
the zero padding convention. The block amplification uses that identity and
`eigenvalue_submatrix_equiv` for the coordinate association.

The integration gives one result ID to the headline statements. It uses the
source's finite operator formulas with the backend's coordinate compression
proof and extends them to `RCLike`. The parameter always uses the largest
signed eigenvalue. The original conjunction is available by combining the
named results.
