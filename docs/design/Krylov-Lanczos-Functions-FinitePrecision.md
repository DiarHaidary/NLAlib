# Finite precision Lanczos matrix function vectors

2026-11-04. Design submitted for review before library proofs.

The result concerns the physical computed basis. The backward matrix alone, or the scalar
spectral measure, does not establish a matrix function vector bound. The route here collapses
all blocks of the existing orthonormal dilation. The geometric identity
`C * sum (K^r) = 1` recovers the original normalized basis exactly. The collapse map has
spectral norm at most the square root of the number of blocks.

## Objects and vocabulary

| Concept | Spelling | Mathlib bridge |
| --- | --- | --- |
| Sum of vector blocks as a matrix | `blockSumMatrix` | entrywise identity; multiplication sums blocks |
| Normalized physical Lanczos function vector | `LanczosRun.normalizedFunctionApprox f` | `blockSumMatrix *ᵥ lanczosFA backwardH f dilatedStart k` |
| Computed physical Lanczos function vector | `LanczosRun.functionApprox f` | `basis *ᵥ (cfc f tridiagonal *ᵥ Pi.single 0 1)` |

The function vectors are ideal postprocessing of a finite precision recurrence: the small
matrix functional calculus and final matrix-vector product in their definitions are exact.
A theorem accepting an arbitrary returned vector with an explicit postprocessing error adds
that error. This is not an implementation, operation-count, or eigensolver theorem.

No new hypothesis interface is introduced. `LanczosRun`, `Metric.IsUniformApproxOn`, spectra,
and `LipschitzOnWith` are reused. The function can be arbitrary, including discontinuous away
from the finitely many eigenvalues. The approximating polynomial, not the function, supplies
the Lipschitz estimate.

## Headline statements

The exact numerical presentation depends on the reviewed lower polynomial API. The primary
compositional statement is (real matrices because the existing run model is real):

```lean
theorem LanczosRun.norm_cfc_mulVec_sub_normalizedFunctionApprox_le
    (L : LanczosRun n k) {s : Set ℝ} {f : ℝ → ℝ} {p : ℝ[X]} {δ c : ℝ}
    {ℓ : ℝ≥0} (hs : spectrum ℝ L.H ⊆ s)
    (hback : spectrum ℝ L.backwardH ⊆ s)
    (hpoly : LipschitzOnWith ℓ (fun x => p.eval x) s)
    (hp : p.degree < k)
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f s δ)
    (hc : frobNorm (L.backwardH - L.dilatedH) ≤ c) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ L.normalizedV 1 -
      L.normalizedFunctionApprox f)‖ ≤
      (1 + Real.sqrt (k + 1)) * δ + Real.sqrt (k + 1) * ℓ * c
```

The interval and run-local specialization replaces `s` by `[a-ρ,a'+ρ]`, `c` by the
existing `lanczosBackwardFactor k * L.ε * specNorm L.H`, and derives the backward-spectrum
premise from the existing Weyl theorem. A coarse Markov estimate gives polynomial dependence
`4 k² (M+δ)/(a'-a+2ρ)` for the scalar Lipschitz coefficient when `|f|≤M` on that interval.
No exponential dependence on the iteration count is concealed in a constant.

The computed physical basis result adds `sqrt(k) * L.ε * M`, from the difference between
computed and normalized columns. Homogeneity gives the same bound times `‖b‖` when
`b = ‖b‖ • normalizedV 1`. A postprocessing theorem adds an explicitly supplied residual.

## Proof structure

1. Prove the collapse matrix operator norm, collapse of `orthonormalDilation`, and collapse
   commuting with functions of a repeated diagonal block. The latter follows directly from
   the existing `cfc_blockDiagonal`.
2. Exact backward Lanczos reproduces the computed tridiagonal and dilated basis. Therefore
   collapsing its exact polynomial output gives the normalized physical polynomial output.
3. Insert a degree-bounded polynomial in the exact physical function vector and the physical
   computed output. The two approximation tails cost `δ` and `sqrt(k+1) δ` respectively.
4. Apply Hermitian Frobenius functional calculus perturbation to the polynomial on the enlarged
   interval, then the collapse norm. This costs `sqrt(k+1) ℓ c`.
5. Bound the normalization correction columnwise, and scale the initial vector explicitly.

## Consumers and files

`NLAlib/Krylov/FinitePrecision/LanczosFunctions.lean` owns physical function outputs, their
backward representation, polynomial approximation bounds and raw basis correction. Future
matrix exponential, sign and inverse function consumers can instantiate it with their scalar
uniform approximation results.

The clean block-sum matrix and its norm belong to matrix block analysis; its collapse of the
orthonormal dilation belongs in `Matrix/Subspaces/OrthonormalDilation.lean`. The interval
polynomial derivative bound belongs in `Polynomial/Approximation/Markov.lean`. Matrix
functional calculus with a scalar Lipschitz coefficient on a common interval belongs in
`Matrix/Functions/HermitianCalculus.lean`. These lower-layer additions are coordinated with
the parent agent before editing.

## Material and relation to the literature

Read Musco, Musco and Sidford, *Stability of the Lanczos Method for Matrix Function
Approximation*, SODA 2018, Theorem 2.1, https://groups.csail.mit.edu/tds/papers/Musco/SODA18.pdf.
Their bound is `(7k δ_k + ε C) ‖b‖`, using a specified floating point implementation with
logarithmically many precision bits, including stable small-matrix postprocessing. The present
proof uses the library's local recurrence model and its polynomial backward bound. It gives a
polynomial precision coefficient and a general polynomial approximation forward theorem for
the physical basis. It does not claim the printed `7k` constant, the same precision threshold,
their implementation guarantee, or their runtime bound.

Reused NLAlib material: exact `Functions/LanczosFA`, `FinitePrecision/BackwardSpectral`,
`FinitePrecision/Dilation`, `Matrix/Subspaces/OrthonormalDilation`, and Hermitian Frobenius
functional calculus. Mathlib search found `Polynomial.Chebyshev.eval_iterate_derivative_le_of_forall_abs_le_one`
(an endpoint bound); searched for full interval Markov, none. The endpoint theorem can give a
coarse full interval estimate by restriction to a subinterval ending at the target point, with
length at least half the original interval, and reflection on the left half.

## Review questions

Accept the polynomial precision coefficient and exact postprocessing scope as an explicit
comparison with, rather than a claim to reproduce, SODA 2018 Theorem 2.1. Recommended: yes.

## 2026-11-04 scope audit and amendments

The repository already has matrix function approximation bounds. In particular,
`Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn` proves the
exact-arithmetic vector bound for canonical Krylov compression, and `BackwardSpectral` proves
finite precision scalar quadratic-form comparison for globally Lipschitz test functions.
Neither conclusion contains the physical computed basis multiplied by `cfc f tridiagonal e₀`.
The addition reuses those exact-arithmetic objects and their polynomial reproduction theorem;
it does not create another exact Lanczos function approximation algorithm.

The primary compositional theorem uses a common interval, rather than a general spectral set:
a compression can have Ritz values in the convex hull of a disconnected set. The matrix
Frobenius perturbation helper itself remains valid on any common spectral set.

The normalization bridge `LanczosRun.norm_v_sub_normalizedV_le` is added to
`FinitePrecision/Normalized.lean`, where its subject belongs. No new predicate is needed.
The initial-vector scaling corollary explicitly assumes `b = ‖b‖ • normalizedV 1`, since the
run model has no input-vector field. This includes the zero input and makes the initialization
contract visible. A final-vector residual accounts for postprocessing error after the small
matrix function, multiplication by the computed physical basis, and scaling.

## Final explicit precision statement

The scalar Lipschitz coefficient is eliminated using the proved interval polynomial estimate.
The public degree factor is `polynomialDerivativeFactor k = 4 k²`; the existing backward
factor remains `lanczosBackwardFactor k = 400 k³`. The approximation multiplier is named `lanczosFunctionApproxFactor k`, currently `4 k`, with nonnegativity and one-sided comparison API.
The exact final scalar-normalized signature is:

```lean
theorem LanczosRun.norm_cfc_mulVec_sub_functionApprox_le_of_precision
    (L : LanczosRun n k) {a a' ρ M δ η : ℝ} {f : ℝ → ℝ} {p : ℝ[X]}
    (hab : a < a') (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100)
    (hρ : lanczosBackwardFactor k * L.ε * specNorm L.H ≤ ρ)
    (hp : p.degree < k)
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f
      (Set.Icc (a - ρ) (a' + ρ)) δ)
    (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc (a - ρ) (a' + ρ), |f x| ≤ M)
    (hη : η ≤ 1)
    (hprecision : Real.sqrt (k + 1) * polynomialDerivativeFactor k /
      (a' - a + 2 * ρ) * (lanczosBackwardFactor k * L.ε * specNorm L.H) +
      Real.sqrt k * L.ε ≤ η) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ L.normalizedV 1 - L.functionApprox f)‖ ≤
      lanczosFunctionApproxFactor k * δ + η * M
```

The scaling corollary adds `b` and `hb : b = ‖WithLp.toLp 2 b‖ • L.normalizedV 1`,
uses output `‖WithLp.toLp 2 b‖ • L.functionApprox f`, and multiplies the error bound by
`‖WithLp.toLp 2 b‖`. Thus its output is precisely the norm of the initial vector times the
physical computed basis applied to the small matrix function at the first coordinate.
The sufficient local accuracy is inverse polynomial in `k`, the spectral scale and inverse
interval width. If local accuracy decays exponentially with precision bits, this budget takes
logarithmically many bits. The theorem itself does not introduce a floating point semantics
or prove that implementation implication.
