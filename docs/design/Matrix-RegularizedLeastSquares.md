# Regularized least squares and generalized singular filters

Design, 2026-11-02. This is a four-card regularization migration, with standard Tikhonov,
truncated SVD and Landweber covered by their companion notes. The source is the original atlas
at `tchen-research/NLAlib`, commit `77514ce42a0e437d837797a063ac161f41022730`.

## Objects and reuse

One objective and one canonical inverse serve standard and general penalties:

```lean
tikhonovObjective (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) (β : ℝ) (x : n → 𝕜) : ℝ :=
  ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2 + β * ‖WithLp.toLp 2 (L *ᵥ x)‖ ^ 2
tikhonovInverse (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) (β : ℝ) : Matrix n m 𝕜 :=
  pinv (Aᴴ * A + β • (Lᴴ * L)) * Aᴴ
```

Both are total. No rank or positivity assumption enters a definition. The shared minimization
theorems permit nonnegative parameters; the affine minimizer and uniqueness statements and
GSVD filter theorems assume positivity. The identity
penalty is the standard case. Mathlib has no matching regularization object (searched).
The bridge is ordinary least squares for `Matrix.fromRows A (Real.sqrt β • L)` and data
`Sum.elim b 0`. Reuse `IsLeastSquaresSolution`, `isLeastSquaresSolution_iff_normal_equations`,
`pinv_eq_pinv_conjTranspose_mul_self_mul`, and the existing uniqueness theorem. Do not port the
backend's separate normal matrices, residual energy, or quadratic-minimization theory.

## Statement shapes

All statements use `RCLike`, arbitrary finite index types, and `DecidableEq` only where needed.

```lean
isMinOn_tikhonovObjective_iff_normal_equations (hβ : 0 ≤ β) :
  IsMinOn (tikhonovObjective A L b β) Set.univ x ↔
    (Aᴴ * A + β • (Lᴴ * L)) *ᵥ x = Aᴴ *ᵥ b
isMinOn_tikhonovObjective :
  IsMinOn (tikhonovObjective A L b β) Set.univ (tikhonovInverse A L β *ᵥ b)
isMinOn_tikhonovObjective_iff_exists (hβ : 0 < β) :
  IsMinOn (tikhonovObjective A L b β) Set.univ x ↔
    ∃ v, v ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin ∧
      x = tikhonovInverse A L β *ᵥ b + v
existsUnique_isMinOn_tikhonovObjective_iff (hβ : 0 < β) :
  (∃! x, IsMinOn (tikhonovObjective A L b β) Set.univ x) ↔
    LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥
```

The canonical minimizer theorem also assumes `0 ≤ β`. The GSVD filter is
`X *ᵥ fun i => (Xᴴ *ᵥ (Aᴴ *ᵥ b)) i / ((c i ^ 2 + β * s i ^ 2 : ℝ) : 𝕜)`.
With `h : IsGSVD A L X c s`, it solves the normal equations for positive parameters, and
therefore minimizes the objective. It equals the canonical inverse solution under trivial
common kernel; at deficient stacked rank this equality is deliberately not asserted.

The two limits retain nonzero data coordinates as `β → 0+` and zero penalty coordinates as
`β → ∞`. Their variational statements use the existing least-squares predicate and Mathlib
`IsMinOn`: least penalty among least-squares solutions, and least data residual on `ker L`.
Trivial common kernel gives uniqueness. No claim that the zero endpoint is generally `pinv A b`.

## Files, consumers and coverage

* `Matrix/Pseudoinverse/RegularizedLeastSquares.lean`: shared objective/inverse, augmented
  least-squares bridge, normal equations, affine minimizer set and uniqueness.
* `Matrix/Pseudoinverse/GeneralTikhonov.lean`: GSVD filter and both coordinate limits.
* `Matrix/Pseudoinverse/GeneralTikhonovLimits.lean`: endpoint feasibility, variational meanings,
  and uniqueness, with the six signatures specified in its companion design note.
* Companion topic files: standard Tikhonov and truncated-SVD regularization in Pseudoinverse;
  Landweber in Krylov alongside the Richardson recurrence it consumes. Its standalone matrix
  power formula and power limit extend the existing `Matrix/Spectral/PowerBounds.lean`.

Consumers are inverse problems, regularized regression, spectral filtering, and comparisons of
iterative and direct regularization. The general-form source card is completed only when the
endpoint interpretations and uniqueness are present, not merely the GSVD coordinate formula.

## Review decisions

The scope is the four original cards, without TLS, new program-cost targets, or unrelated
quadratic optimization. Reusable helpers stay with their subjects; proof-specific transport
stays private. Exact duplicates are consumed from the current library. Root imports, vocabulary,
references, result metadata and the independent read-back are updated together after compilation.

## Amendment, 2026-11-02: endpoint module and coordinate definitions

The endpoint proofs live in `GeneralTikhonovLimits.lean` so consumers of the finite filter do
not import the strict-convexity proof machinery. The only coordinate definitions are

```lean
gsvdTikhonovFilter (A : Matrix m n 𝕜) (X : Matrix n n 𝕜)
    (c s : n → ℝ) (b : m → 𝕜) (β : ℝ) : n → 𝕜
gsvdPenaltyKernelSolution (A : Matrix m n 𝕜) (X : Matrix n n 𝕜)
    (c s : n → ℝ) (b : m → 𝕜) : n → 𝕜
```

The zero endpoint is `gsvdTikhonovFilter A X c s b 0`, not a duplicate definition. The
infinite-parameter coordinate limit is `tendsto_gsvdTikhonovFilter_atTop` in the root `NLAlib`
namespace: it holds for arbitrary finite coordinate data, without a GSVD hypothesis. The
zero-parameter limit and all variational interpretations require `IsGSVD`.

The general-penalty statements are derived from the pinned atlas proof and native interfaces;
the source card's contextual textbook reference is not presented as a printed source for
these particular formulas or endpoint claims.
