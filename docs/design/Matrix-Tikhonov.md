# Standard Tikhonov regularization

Design date: 2026-11-02. This is the standard-penalty part of the coherent regularization
batch, covering the complete original `tikhonov-spectral-filter` card.

## Objects and interfaces

Use the shared `tikhonovObjective A L b β` and `tikhonovInverse A L β` from
`Matrix/Pseudoinverse/RegularizedLeastSquares.lean`, specializing the penalty to the identity.
The shared operator is `pinv (Aᴴ * A + β • (Lᴴ * L)) * Aᴴ`; its positive-parameter standard
instance agrees with the ordinary inverse formula. At zero the shared definition already
equals `pinv A`, rather than inheriting the singular total inverse's zero value.

No standard-only objective, normal-matrix alias, second regularized inverse, or hypothesis
interface is added. Native `IsSVD` permits arbitrary finite column types and zero singular
values. `IsMinOn` is the minimizer predicate and its normal equations come from the shared
regularized least-squares API. Every statement is over `RCLike` and arbitrary finite row and
column types, with no rank or nonempty-dimension hypothesis. The parameter is a real number
and substantive inequalities assume it is positive.

The shared vocabulary is specified in `Matrix-RegularizedLeastSquares.md`; this note adds none.

## Exact signatures

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq n]

omit [Fintype n] in
theorem posDef_conjTranspose_mul_self_add_smul_one [Finite n] (A : Matrix m n 𝕜)
    {β : ℝ} (hβ : 0 < β) : (Aᴴ * A + β • 1).PosDef

theorem tikhonovInverse_one_eq (A : Matrix m n 𝕜) {β : ℝ} (hβ : 0 < β) :
    tikhonovInverse A (1 : Matrix n n 𝕜) β = (Aᴴ * A + β • 1)⁻¹ * Aᴴ

theorem IsSVD.tikhonovInverse_one_eq {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsSVD A U σ V) {β : ℝ} (hβ : 0 < β) :
    tikhonovInverse A (1 : Matrix n n 𝕜) β =
      V * Matrix.diagonal (fun i => ((σ i / (σ i ^ 2 + β) : ℝ) : 𝕜)) * Uᴴ

theorem isMinOn_tikhonovObjective_one_iff (A : Matrix m n 𝕜) (b : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) {x : n → 𝕜} :
    IsMinOn (tikhonovObjective A (1 : Matrix n n 𝕜) b β) Set.univ x ↔
      x = tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ b

theorem specNorm_tikhonovInverse_one_le (A : Matrix m n 𝕜) {β : ℝ} (hβ : 0 < β) :
    specNorm (tikhonovInverse A (1 : Matrix n n 𝕜) β) ≤ 1 / (2 * Real.sqrt β)

theorem norm_sub_tikhonovInverse_mulVec_le (A : Matrix m n 𝕜) (b e : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) :
    ‖WithLp.toLp 2 (tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ b -
      tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ (b + e))‖ ≤
        ‖WithLp.toLp 2 e‖ / (2 * Real.sqrt β)

theorem tendsto_tikhonovInverse_one_zero (A : Matrix m n 𝕜) :
    Filter.Tendsto (fun β : ℝ => tikhonovInverse A (1 : Matrix n n 𝕜) β)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (pinv A))

theorem tendsto_tikhonovInverse_one_mulVec_zero (A : Matrix m n 𝕜) (b : m → 𝕜) :
    Filter.Tendsto (fun β : ℝ =>
      (WithLp.toLp 2 (tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ b) : EuclideanSpace 𝕜 n))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (WithLp.toLp 2 (pinv A *ᵥ b)))
```

The SVD filter, minimizer equivalence, norm bound, noise bound and both limits share
`Result: tikhonov-spectral-filter`. The two one-line normal/inverse bridges are supporting API.
The scalar envelope is exact uniformly over matrices, attained at a singular value `sqrt β`;
the theorem does not claim a statistical risk or a parameter-choice guarantee.

## Reuse and proof plan

Mathlib searches found no Tikhonov/ridge regularization theorem. Exact overlaps are reused:

* Positive definiteness is the one-line specialization of Mathlib
  `Matrix.PosDef.posSemidef_add`, `Matrix.posSemidef_conjTranspose_mul_self`, and
  `Matrix.PosDef.one.smul`; the inverse bridge uses native `pinv_of_isUnit`.
* The SVD formula uses `IsSVD.mul_right_eq`, its conjugate-transpose instance, the existing
  orthonormal-column cancellation lemmas, and inverse cancellation. No new thin-SVD interface
  or completion of zero singular directions is needed.
* The unique minimizer equivalence specializes the shared
  `isMinOn_tikhonovObjective_iff_normal_equations` with `hβ.le`, then applies injectivity of the
  positive definite normal matrix. No quadratic-objective definition or independent minimization
  proof.
* The envelope uses the existing unitary-invariant norm lemmas and `specNorm_diagonal`, with a
  private scalar inequality from `(σ - sqrt β)^2 ≥ 0`. The data-error corollary is native
  `norm_toLp_mulVec_le`, written as clean-data output minus noisy-data output.
* Limits use one fixed native compact SVD with positive singular values, scalar continuity,
  native `IsSVD.pinv_eq`, continuity of finite matrix multiplication and `WithLp.toLp`.
  The matrix limit implies the Euclidean solution limit in one application of continuity.

The shared normal-equation interface is the only dependency on another new file. No existing
support module needs to change. If compilation reveals a shared support gap, request a design
amendment before editing its topic home.

## Files and consumers

One new file, `NLAlib/Matrix/Pseudoinverse/Tikhonov.lean`, expected under 400 lines, ordered as
normal/inverse bridges, SVD filter, unique minimizer, stability, limits. The two original source
files are consolidated; a separate limit file is unnecessary at this scale.

This API supports deterministic ridge regression, regularized inverse computations, noise
amplification estimates, and standard-penalty specialization of the general GSVD theory. The
matrix limit serves any fixed data vector without redoing the spectral argument.

## Source material and exclusions

Read committed `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730` through `git show origin/main`:
`NLAlib/Matrix/Basic/Tikhonov.lean` and `TikhonovLimit.lean` (250 lines together).
The atlas source is Fessler–Nadakuditi 2024, section 5.6.5, equations (5.44)–(5.48);
the source code instead cites Hansen section 4.3. This migration uses the atlas locators.
The publisher's bibliographic metadata was verified; the equation locators are inherited
from the pinned card, rather than independently checked against the full book. The bound is
the derived scalar envelope and is documented as such.

Do not reproduce `tikhonovNormal`, a standard-only `tikhonovObjective`, `IsThinSVD`,
`moorePenroseInverse`, the separate source limit file, or quadratic-minimization infrastructure.
No statistical risk, early stopping, TLS, arbitrary-penalty noise envelope, or algorithm-cost
claim is part of this card.

## Review

Integration review accepted this shared-interface plan on 2026-11-02 before proof
implementation. The general regularized least-squares normal-equation theorem permits
nonnegative parameters; the standard statements apply it with `hβ.le`.
