# Five matrix atlas clauses

The five cards below add nine public theorems to the existing matrix API. They use Mathlib’s
`Matrix.IsHermitian`, `Matrix.PosSemidef`, `Submodule`, `Module.finrank`, `EuclideanSpace` and
`HasGradientAt` directly, together with NLAlib’s `eigenvalue`, `singularValues`, `specNorm`,
`quadForm`, `rayleighQuotient`, `frobInner` and `frobNorm`. All the hypothesis predicates,
constructors and vocabulary are already available. Each statement concerns an exact mathematical
quantity. [Library design](https://nla-lib.org/design/) ·
[Original atlas revision](https://github.com/tchen-research/NLAlib/tree/77514ce42a0e437d837797a063ac161f41022730)

The signatures below use this common context. The congruence statement additionally uses
`[DecidableEq n]` for the determinant and diagonal matrix.

```lean
open scoped Matrix ComplexOrder MatrixOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
```

## Quadratic probe detection

`quadratic-probe-spectral-detection` chooses one unit direction before the probe is supplied. The
ordered Hermitian eigendecomposition and the PSD spectral-norm formula give the bound for every
probe, including probes orthogonal to the top eigenvector. The nonempty assumption permits a unit
vector even when the matrix is zero.

```lean
theorem _root_.Matrix.PosSemidef.exists_norm_eq_one_and_specNorm_mul_norm_dotProduct_sq_le
    [Nonempty n] {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ v : n → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧
      ∀ z : n → 𝕜, specNorm A * ‖star v ⬝ᵥ z‖ ^ 2 ≤ RCLike.re (quadForm A z)
```

**Placement and consumer.** `Matrix/Spectral/CourantFischer.lean` already contains the
top-eigenvector and norm-attainment theorems. `RandomMatrix/Gaussian/InverseMoments/Spectral.lean`
uses the new result to bound a positive moment of the spectral norm of an inverse Gaussian Gram
matrix. This replaces the private real-matrix proof there and recovers the atlas result
`exists_unit_specNorm_mul_dotProduct_sq_le` over `ℝ`.

## Eigenvalue order and counting

`eigenvalue-order-and-counting` uses the existing decreasing, zero-padded `eigenvalue A k`. The
lower subspace dimension bound already implies `k < Fintype.card n`. The upper test needs that
hypothesis explicitly because it addresses the finite spectrum. The two counts distinguish an
eigenvalue equal to the threshold from one strictly above it, and count repeated eigenvalues by
position.

```lean
theorem _root_.Matrix.IsHermitian.lt_eigenvalue_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (S : Submodule 𝕜 (n → 𝕜)) (hS : k + 1 ≤ Module.finrank 𝕜 S)
    {c : ℝ} (h : ∀ x ∈ S, x ≠ 0 → c * ‖WithLp.toLp 2 x‖ ^ 2 < RCLike.re (quadForm A x)) :
    c < eigenvalue A k

theorem _root_.Matrix.IsHermitian.eigenvalue_lt_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ Module.finrank 𝕜 W + k) {c : ℝ}
    (h : ∀ x ∈ W, x ≠ 0 → RCLike.re (quadForm A x) < c * ‖WithLp.toLp 2 x‖ ^ 2) :
    eigenvalue A k < c

theorem _root_.Matrix.IsHermitian.finrank_le_card_le_eigenvalue_of_forall_mem
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (S : Submodule 𝕜 (n → 𝕜)) {c : ℝ}
    (h : ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x)) :
    Module.finrank 𝕜 S ≤
      ((Finset.range (Fintype.card n)).filter fun i => c ≤ eigenvalue A i).card

theorem _root_.Matrix.IsHermitian.finrank_le_card_lt_eigenvalue_of_forall_mem
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (S : Submodule 𝕜 (n → 𝕜)) {c : ℝ}
    (h : ∀ x ∈ S, x ≠ 0 → c * ‖WithLp.toLp 2 x‖ ^ 2 < RCLike.re (quadForm A x)) :
    Module.finrank 𝕜 S ≤
      ((Finset.range (Fintype.card n)).filter fun i => c < eigenvalue A i).card
```

**Placement and consumers.** `Matrix/Spectral/CourantFischer.lean` shares a private subspace witness
between the weak and strict lower tests, then obtains the strict upper test by applying the lower
test to `-A` and using `eigenvalue_neg`. These tests certify lower or upper eigenvalue bounds from
trial subspaces. `Matrix/Spectral/Inertia.lean` adds the private finite counting lemma
`finrank_le_card_filter_range`, followed by the closed and open threshold results. Taking `c = 0`
recovers the atlas nonnegative and positive counts. The existing positive-inertia proof uses the
open-threshold result directly. See Horn and Johnson, *Matrix Analysis*, Theorem 4.2.10 and
Corollary 4.2.12.

## Rayleigh quotient residual

`eigenvalue-residual-bounds` identifies the gradient on the underlying real space, including for
complex Hermitian matrices. A Rayleigh-quotient iteration or stationary-point argument can use the
residual vector directly. Mathlib’s `HasGradientAt.hasFDerivAt` gives the directional derivative
from the same theorem.

```lean
theorem _root_.Matrix.IsHermitian.hasGradientAt_rayleighQuotient {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {x : EuclideanSpace 𝕜 n} (hx : x ≠ 0) :
    HasGradientAt (fun y : EuclideanSpace 𝕜 n => rayleighQuotient A y.ofLp)
      ((2 / ‖x‖ ^ 2) • (WithLp.toLp 2 (A *ᵥ x.ofLp) - rayleighQuotient A x.ofLp • x)) x
```

**Placement and reuse.** `Matrix/Perturbation/Residual.lean` places the gradient beside residual
orthogonality and minimization. The proof uses the existing `rayleighQuotient_eq_toEuclideanCLM`
bridge and Mathlib’s `LinearMap.IsSymmetric.hasStrictFDerivAt_reApplyInnerSelf`,
`hasStrictFDerivAt_norm_sq`, and `hasGradientAt_iff_hasFDerivAt`. All calculations specific to the
real inner product are local. The real specialization gives the differential in Trefethen and Bau,
*Numerical Linear Algebra*, (27.2), and the atlas `hasFDerivAt_rayleighQuotient`.

## Congruence of a semidefinite pair

`simultaneous-diagonalization-congruence` describes a possibly singular Hermitian pencil. One
simultaneous factorization identifies the active coordinates of `A`, the additional active
coordinates of `B` on the kernel of `A`, and the common kernel. Their cardinalities determine the
three block sizes for a generalized eigenvalue calculation. Reordering the coordinates gives the
atlas identity and zero blocks, including empty blocks.

```lean
section
variable [DecidableEq n]

theorem _root_.Matrix.PosSemidef.exists_eq_mul_diagonal_mul_conjTranspose {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    ∃ (S : Matrix n n 𝕜) (a b : n → ℝ), IsUnit S.det ∧
      A = S * Matrix.diagonal (fun i => (a i : 𝕜)) * Sᴴ ∧
      B = S * Matrix.diagonal (fun i => (b i : 𝕜)) * Sᴴ ∧
      (∀ i, a i = 0 ∨ a i = 1) ∧ (∀ i, 0 ≤ b i) ∧
      (∀ i, a i = 0 → b i = 0 ∨ b i = 1) ∧
      A.rank = Fintype.card {i // a i = 1} ∧
      (A + B).rank = Fintype.card {i // a i = 1} + Fintype.card {i // a i = 0 ∧ b i = 1} ∧
      Module.finrank 𝕜 ↥(LinearMap.ker A.mulVecLin ⊓ LinearMap.ker B.mulVecLin) =
        Fintype.card {i // a i = 0 ∧ b i = 0}
end
```

**Placement and reuse.** `Matrix/Spectral/Congruence.lean` extends
`Matrix.PosSemidef.exists_conjTranspose_mul_mul_eq_diagonal`, which already normalizes the sum. Two
private helpers choose and apply the diagonal rescaling. A third obtains the binary first diagonal,
and a fourth reads the rank via Mathlib’s `Matrix.rank_diagonal`. The public factorization then uses
the existing `Matrix.PosSemidef.ker_add` to identify common nullity. Its projections supply the
atlas normalization and semidefinite normal form. The definite-pair congruence and its
diagonalizability criterion retain their existing individual statements. See Horn and Johnson, §7.6.

## Procrustes and equality in Mirsky’s inequality

`orthogonal-procrustes` asks when the Frobenius distance attains the singular-value lower bound. The
equivalence lets a caller use the real trace pairing to certify equality. A caller analyzing an
optimal alignment can then recover positivity of both cross-products. These statements apply to
rectangular matrices and either dimension may be zero.

```lean
theorem frobNorm_sub_sq_eq_sum_singularValues_sub_sq_iff (A B : Matrix m n 𝕜) :
    frobNorm (A - B) ^ 2 = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      (singularValues A i - singularValues B i) ^ 2 ↔
    frobInner A B = ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
      singularValues A i * singularValues B i

theorem posSemidef_mul_conjTranspose_of_frobNorm_sub_sq_eq
    {A B : Matrix m n 𝕜} (h : frobNorm (A - B) ^ 2 =
      ∑ i ∈ Finset.range (min (Fintype.card m) (Fintype.card n)),
        (singularValues A i - singularValues B i) ^ 2) :
    (A * Bᴴ).PosSemidef
```

**Placement and reuse.** `Matrix/Majorization/TraceInequalities.lean` factors the singular-value
square expansion into one private lemma shared by Mirsky’s inequality and its equality criterion.
The criterion carries both `mirsky-inequality` and `orthogonal-procrustes` metadata.
`Matrix/Factorizations/Procrustes.lean` follows the existing two-sided minimization theorem with the
row cross-product theorem. The proof uses the polar factor,
`abs_frobInner_le_sum_singularValues_mul`, and `trace_eq_nuclearNorm_iff_posSemidef`, which identify
equality in the real trace bound. For the second conclusion of the atlas `ProcrustesRotations`
module, apply the same theorem to the adjoints and use adjoint invariance of the Frobenius distance
and singular values. This gives positivity of `Aᴴ * B`. Taking the adjoint gives the atlas
conclusion for `Bᴴ * A`. See Horn and Johnson, §7.4.1 and Corollary 7.4.1.5.

## Review decisions

The Procrustes API exposes one cross-product orientation. The other is recovered by adjunction, so
publishing the two together would duplicate this symmetry. Keep the PSD factors indexed by the
caller’s `n`. Their explicit cardinalities suffice to recover the ordered block display without
selecting an ordering in the API. Keep the Rayleigh gradient as the public calculus result and
recover the derivative through Mathlib’s projection. Conjunctions that merely repack the legacy
cards can be assembled at the call site. A search of Mathlib’s matrix and inner-product-space
developments found no exact restatement of these nine signatures.
