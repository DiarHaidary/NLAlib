# Truncated-SVD regularization

Design, 2026-11-02. Scope: the original `truncated-svd-regularization` card, including
the stronger arbitrary retained-family bias/noise identity in its formalization.

## Objects and interfaces

No new definitions, predicates, constants, or deviations from Mathlib. Use the existing
`IsSVD`, `pinv`, `truncatedSVD`, `HasOrthonormalCols`, and Mathlib's `IsMinOn` and
`LinearMap.range`. A fixed SVD split as `Sum r s` represents arbitrary retained coordinates:
the first block is retained and the second discarded. Neither block is required to be sorted.
Strict positivity is required only for retained singular values, to make the restricted
minimizer unique on the whole retained right space. Empty retained/discarded types are allowed.

## Statement shapes

All statements are over `RCLike`, arbitrary finite row/column types, with decidable equality
only where needed. Here the shared context is:

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n r s : Type*}
  [Fintype m] [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s]
variable {A : Matrix m n 𝕜} {U₁ : Matrix m r 𝕜} {U₂ : Matrix m s 𝕜}
  {V₁ : Matrix n r 𝕜} {V₂ : Matrix n s 𝕜} {σ₁ : r → ℝ} {σ₂ : s → ℝ}
```

The following signatures use `B` only as a design shorthand for the explicit expression
`U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ`; no such definition will be added.

```lean
theorem IsSVD.isMinOn_norm_sub_mulVec_pinv_mulVec
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
      (LinearMap.range V₁.mulVecLin) (pinv B *ᵥ b)

theorem IsSVD.eq_pinv_mulVec_of_isMinOn
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i) (b : m → 𝕜)
    {x : n → 𝕜} (hx : x ∈ LinearMap.range V₁.mulVecLin)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.range V₁.mulVecLin) x) : x = pinv B *ᵥ b

theorem IsSVD.norm_sub_pinv_mulVec_sq
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i)
    (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - pinv B *ᵥ (A *ᵥ x + e))‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - V₁ * V₁ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 (pinv B *ᵥ e)‖ ^ 2
```

Membership `pinv B *ᵥ b ∈ range V₁` is supplied by its existing SVD pseudoinverse formula,
and will have a short public range-membership lemma if needed to state the full minimizer
contract. `IsMinOn` itself does not imply membership.

The inverse formula and arbitrary retained inverse norm are already exactly
`h.fromCols_left.pinv_eq` and `h.fromCols_left.pinv.specNorm_eq`; do not duplicate these.
For a leading block, use `r = Fin (k+1)`, `σ₁ i = singularValues A i`, and `k+1 ≤ A.rank`:

```lean
theorem IsSVD.specNorm_pinv_of_fromCols
    (h : IsSVD A (Matrix.fromCols U₁ U₂)
      (Sum.elim (fun i : Fin (k + 1) => singularValues A i) σ₂)
      (Matrix.fromCols V₁ V₂)) (hk : k + 1 ≤ A.rank) :
    specNorm (pinv (U₁ * Matrix.diagonal
      (fun i : Fin (k + 1) => (singularValues A i : 𝕜)) * V₁ᴴ)) =
      (singularValues A k)⁻¹

theorem IsSVD.norm_sub_pinv_mulVec_sq_le_of_fromCols
    (h : IsSVD A (Matrix.fromCols U₁ U₂)
      (Sum.elim (fun i : Fin (k + 1) => singularValues A i) σ₂)
      (Matrix.fromCols V₁ V₂)) (hk : k + 1 ≤ A.rank)
    (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - pinv (U₁ * Matrix.diagonal
      (fun i : Fin (k + 1) => (singularValues A i : 𝕜)) * V₁ᴴ) *ᵥ
        (A *ᵥ x + e))‖ ^ 2 ≤
      ‖WithLp.toLp 2 ((1 - V₁ * V₁ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 e‖ ^ 2 / singularValues A k ^ 2
```

Canonical corollaries use `pinv (truncatedSVD A k)`, with constrained space the actual row
space of the truncation. They hold at every `k`, including zero and beyond the rank. The
sharp reciprocal norm/noise bound uses a nonempty retained positive block.

```lean
theorem isMinOn_norm_sub_mulVec_pinv_truncatedSVD_mulVec
    (A : Matrix m n 𝕜) (k : ℕ) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
      (LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin)
      (pinv (truncatedSVD A k) *ᵥ b)

theorem eq_pinv_truncatedSVD_mulVec_of_isMinOn
    (A : Matrix m n 𝕜) (k : ℕ) (b : m → 𝕜) {x : n → 𝕜}
    (hx : x ∈ LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin) x) :
    x = pinv (truncatedSVD A k) *ᵥ b

theorem norm_sub_pinv_truncatedSVD_mulVec_sq
    (A : Matrix m n 𝕜) (k : ℕ) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - pinv (truncatedSVD A k) *ᵥ (A *ᵥ x + e))‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - rangeProjector (truncatedSVD A k)ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 (pinv (truncatedSVD A k) *ᵥ e)‖ ^ 2

theorem specNorm_pinv_truncatedSVD (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 ≤ A.rank) :
    specNorm (pinv (truncatedSVD A (k + 1))) = (singularValues A k)⁻¹

theorem norm_sub_pinv_truncatedSVD_mulVec_sq_le (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 ≤ A.rank) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - pinv (truncatedSVD A (k + 1)) *ᵥ (A *ᵥ x + e))‖ ^ 2 ≤
      ‖WithLp.toLp 2 ((1 - rangeProjector (truncatedSVD A (k + 1))ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 e‖ ^ 2 / singularValues A k ^ 2
```

## Files, reuse, and consumers

One new `Matrix/Pseudoinverse/TruncatedSVD.lean`, ordered retained-block restricted minimization,
orthogonal error identity, leading-block bounds, canonical corollaries. No addition elsewhere.
Existing `Spectral/SVD.lean` supplies `IsSVD.fromCols_left`, `eq_add`, `pinv_eq`, and singular
vector orthogonality. `Pseudoinverse/LeastSquares.lean` supplies the actual minimizer and
uniqueness argument. `Spectral/LowRank.lean` supplies both projector identities for the canonical
truncation and its singular values. `Basic/ComplementaryProjector.lean` supplies Pythagoras.
Mathlib was searched for truncated-SVD regularization and retained-family inverse results: none.

Consumers are deterministic inverse problems, principal-component regression, and analyses of
approximate subspace solvers. No general filter calculus or unrelated approximation theory is
introduced. The sum split permits any ordering and cutoff ties: no canonical top-subspace
claim is made. Any retained positive singular family extends to such a full split SVD;
the source's fixed-SVD formulation directly provides that split.

## Material and coverage

Source: `tchen-research/NLAlib` at `77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Basic/TruncatedSVDRegularization.lean` and card
`atlas/atlas.json#truncated-svd-regularization`. Citation: Fessler–Nadakuditi 2024,
§§5.6.1–5.6.4, equations (5.39)–(5.43); exact orthogonality is derived from (5.42).
The source-specific `singularTripletMatrix`, `truncatedSingularInverse`, and
`IsSingularTripletFamily` are replaced by existing native objects and a split `IsSVD`.
The inverse formula and exact arbitrary-family inverse norm are existing coverage;
the constrained minimizer, uniqueness, orthogonal bias/noise identity and leading sharp bound
are new. Empty types, zero rank and zero cutoff use the canonical statements, while empty
retained families also satisfy the general statements.

## Review

Integration review accepted these signatures on 2026-11-02. The only deliberate change
from the old formal signatures is use of a full split SVD and exact-minus-computed errors.

2026-11-02 placement amendment: `IsSVD.rangeProjector_conjTranspose_eq`
belongs in `Matrix/Pseudoinverse/Pinv.lean`, because both TSVD and Landweber need the row
projector formula for a positive compact SVD. Its signature is
`(h : IsSVD A U σ V) (hσ : ∀ i, 0 < σ i) : rangeProjector Aᴴ = V * Vᴴ`.
This is a reusable SVD consequence of `pinv_mul`, not TSVD-specific proof infrastructure.
