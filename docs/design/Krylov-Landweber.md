# Landweber as preconditioned Richardson iteration

Design date: 2026-11-02. Scope: the complete original `landweber-spectral-filter` card.

## Objects and interfaces

No new definition or recurrence is introduced. Landweber is the existing
`richardsonIterate A (η • Aᴴ) b x₀ q`. Use `IsSVD`, `pinv`, `rangeProjector`, and the existing
Richardson fixed-point error formula. All matrices are over an `RCLike` field and arbitrary
finite row and column types. An SVD may contain zero singular values; the filter is total with
zero inverse and hence zero at those values.

The convergence hypothesis is `0 < η` and `η * specNorm A ^ 2 < 2`. For nonzero `A` this is
exactly the usual open interval `0 < η < 2 / specNorm A ^ 2`. The multiplicative form also
covers `A = 0`, when every iterate equals the starting vector, and empty matrix dimensions.
The limit is `pinv A *ᵥ b + (1 - rangeProjector Aᴴ) *ᵥ x₀`; no claim that arbitrary starts
give the minimum-norm solution is made.

## Exact headline signatures

The declarations are in `NLAlib`; the two SVD identities live in its `IsSVD` namespace.

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]

theorem IsSVD.one_sub_smul_conjTranspose_mul_self_pow [DecidableEq n]
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜}
    (h : IsSVD A U σ V) (η : ℝ) (q : ℕ) :
    (1 - η • (Aᴴ * A)) ^ q = 1 - V * Vᴴ +
      V * Matrix.diagonal (fun i => (((1 - η * σ i ^ 2) ^ q : ℝ) : 𝕜)) * Vᴴ

theorem IsSVD.richardsonIterate_smul_conjTranspose_zero
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {σ : r → ℝ} {V : Matrix n r 𝕜}
    (h : IsSVD A U σ V) (b : m → 𝕜) (η : ℝ) (q : ℕ) :
    richardsonIterate A (η • Aᴴ) b 0 q =
      (V * Matrix.diagonal (fun i =>
        (((1 - (1 - η * σ i ^ 2) ^ q) / σ i : ℝ) : 𝕜)) * Uᴴ) *ᵥ b

theorem tendsto_richardsonIterate_smul_conjTranspose [DecidableEq n] (A : Matrix m n 𝕜)
    (b : m → 𝕜) {η : ℝ} (hη : 0 < η) (hstep : η * specNorm A ^ 2 < 2)
    (x₀ : n → 𝕜) :
    Tendsto (fun q => (WithLp.toLp 2
      (richardsonIterate A (η • Aᴴ) b x₀ q) : EuclideanSpace 𝕜 n)) atTop
      (𝓝 (WithLp.toLp 2 (pinv A *ᵥ b + (1 - rangeProjector Aᴴ) *ᵥ x₀)))

theorem tendsto_richardsonIterate_smul_conjTranspose_zero (A : Matrix m n 𝕜)
    (b : m → 𝕜) {η : ℝ} (hη : 0 < η) (hstep : η * specNorm A ^ 2 < 2) :
    Tendsto (fun q => (WithLp.toLp 2
      (richardsonIterate A (η • Aᴴ) b 0 q) : EuclideanSpace 𝕜 n)) atTop
      (𝓝 (WithLp.toLp 2 (pinv A *ᵥ b)))
```

Each headline carries `Result: landweber-spectral-filter`. Supporting statements expose exact
error propagation about the pseudoinverse solution and convergence of the error-multiplier
powers to the kernel projector. The zero-matrix recurrence is stated explicitly.

## Consumers, placement, and reused material

`NLAlib/Krylov/LinearSystems/Landweber.lean` owns the iteration-specific identities and limits,
beside `Richardson.lean`. The standalone SVD power identity and its kernel-projector limit
belong to the existing `Matrix/Spectral/PowerBounds.lean`, with their private multiplier helper.
Regularization and iterative least-squares proofs consume the finite
filter and the limit without translating to a new iteration type. No new vocabulary rows are
planned. A 2026-11-02 amendment shares `IsSVD.rangeProjector_conjTranspose_eq` with truncated-SVD
regularization in `Matrix/Pseudoinverse/Pinv.lean`: a compact SVD with positive singular values
gives its row-space projector. It is owned by the pseudoinverse topic and used by both consumers.

Read backend `NLAlib/Matrix/Basic/Landweber.lean` and `LandweberLimit.lean` from the original
card at commit `77514ce42a0e437d837797a063ac161f41022730`: retain its finite filter, arbitrary-start kernel component and all-rank statement. Replace
its duplicate recurrence, step-matrix definition, `IsThinSVD`, and old pseudoinverse spelling.
The original card cites Fessler and Nadakuditi (2024), sections 9.2–9.2.3, equations (9.2)
and (9.7)–(9.12). The full-column-rank source form is extended here to arbitrary rank by
retaining the starting vector's kernel component. Exact locators are inherited from the pinned
source card; the publisher's book metadata was verified by the batch coordinator.

Mathlib search found no Landweber or Richardson theorem. Reuse its
`tendsto_pow_atTop_nhds_zero_of_abs_lt_one`, finite-product topology, and continuity of matrix
operations. Existing NLAlib supplies `sub_richardsonIterate_eq`, `IsSVD.conjTranspose_mul_self_eq`,
`IsSVD.pinv_eq`, `exists_isSVD` at the rank, `singularValues_pos_iff`,
`singularValues_le_specNorm`, and the Penrose identities. These are used directly rather than
restated as independent facts.

## Review decisions

Use the product step-size condition to preserve zero and empty cases in one main limit theorem.
No new cost claim, registered target, mathematical hypothesis interface, or Mathlib deviation.

2026-11-02 full-rule review amendment: rule P10 identified the two matrix-only power statements
as matrix infrastructure, independently of the iteration. They now live in `PowerBounds.lean`,
which already imports the required SVD/pseudoinverse API and treats idempotent power limits.
Their names, mathematical statements and result metadata are retained. The iteration module
imports this existing owner; no additional theory module or wrapper theorem is introduced.
The zero-forward-matrix lemma is an explicit theorem rather than a simplification rule, because
its left-hand side has a reducible zero preconditioner.
