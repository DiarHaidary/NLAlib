# Design note: Sketching stage S0, the embedding and injection predicates

Status: drafted 2026-10-14 under `docs/PORT_SKETCHING.md` (D1 (b) with the OSI addition; D7).
`IsSubspaceInjection`, `IsSubspaceEmbedding`, their API, D7's consequences. No question of the brief's
§2 kind (§7). Two Matrix-layer additions (§3.3), in a new file.

## 0. Scope and consumers

A sketch `S : Matrix k n 𝕜`, a subspace `range U`, `U : Matrix n p 𝕜` of any shape and rank; deterministic.

| Item | Consumers |
|---|---|
| `IsSubspaceInjection S U a` (D1, OSI addition) | S1's `HasSubspaceInjection`, `IsObliviousSubspaceInjection`; every family's lower half (S2 to S7); LowRank R1, R2, R5, R6 and HMT §11 through CEMT Lemma 2.1 |
| `IsSubspaceEmbedding S U a b` (D1) | S1's `HasSubspaceEmbedding`, `IsObliviousSubspaceEmbedding`; every family theorem; Solvers |
| norm, range, Gram, `specNorm`, singular-value forms; `of_range_le`, `smul`, `mul` | families' Gram-error (S4, S6, S7) and `σ_min` (S2, S3) tails; S1's oblivious API and composition; `(√k)⁻¹ • G` |
| `injOn`, `injective_mulVec`; closedness, measurability | sketch-and-solve, range finder; S1's `HasLaw` lemmas and transfer |
| sketch-and-solve `b / a`, preconditioned conditioning `b / a` | Solvers: sketch-and-solve, sketch-and-precondition, Blendenpik, LSRN |
| error formula, deterministic Lemma 2.1 (injection only) | S1's two OSI tails; LowRank R1, R5, R6 (CEMT Theorem 2.2, Corollaries 2.5, 2.8) |

## 1. Objects

New §5.3 rows (the PR adding them adds the rows):

| Concept | Spelling | Bridge |
|---|---|---|
| one-sided (lower) subspace embedding | `IsSubspaceInjection S U a := a • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)`, a `def`, `a : ℝ` | `isSubspaceInjection_iff_forall_mem_range`; `HasOrthonormalCols.isSubspaceInjection_iff` (Gram form) |
| subspace embedding | `IsSubspaceEmbedding S U a b`, structure, fields `lower : IsSubspaceInjection S U a`, `upper : (S * U)ᴴ * (S * U) ≤ b • (Uᴴ * U)`; the `ε` form is `a = 1 - ε`, `b = 1 + ε` written so | `HasOrthonormalCols.isSubspaceEmbedding_iff_specNorm_le` |

Searched Mathlib (`Analysis/Matrix`, `LinearAlgebra/Matrix`): none. Used directly: the Loewner order
(`MatrixOrder`), `Matrix.rank`, `LinearMap.range U.mulVecLin`, and the Matrix layer's names. No
deviation from Mathlib.

## 2. Interfaces

The two rows above; the raw-condition constructors are the definition itself and `⟨lower, upper⟩`.
The upper half gets no name (D1): a one-sided upper statement is `IsSubspaceEmbedding S U 0 b`
(`isSubspaceInjection_of_nonpos` fills `lower`).

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix MatrixOrder`. Variables `{𝕜 : Type*} [RCLike 𝕜]
{k l n p q r : Type*}`, `[Fintype _]` on each, `{S : Matrix k n 𝕜} {U : Matrix n p 𝕜}
{V : Matrix n q 𝕜} {a a' b b' ε : ℝ}`; `[DecidableEq _]` only where `1` or `⁻¹` appears, `[LinearOrder q]`
where `IsQR` appears (§8).

Degenerate cases (checked for each statement). `p` empty: every predicate holds; the singular-value
form's `hj` is then unsatisfiable, the `specNorm` form needs `0 ≤ ε` for this case only. `k` empty or
`S = 0`: the injection holds iff `a ≤ 0` or `U = 0`, the upper half iff `0 ≤ b` or `U = 0` (in the
docstrings). `a ≤ 0`: `isSubspaceInjection_of_nonpos`. Rank-deficient `U`: everything is about
`range U`; only `injective_mulVec` assumes full rank. `ε = 0`: exact isometry; `ε ≥ 1`: the lower half
is vacuous. Junk: `b / a` at `a = 0` is `0`, so consumers take `0 < a`; `pinv`, `pseudoConditionNumber` total.

### 3.1 `Sketching/Properties/SubspaceEmbedding.lean`

```lean
/-- **Subspace injection** for `range U`: `a ‖U x‖² ≤ ‖S U x‖²`; vacuous for `a ≤ 0`.
[CamanoEpperlyMeyerTropp2025, Definition 1.2 (1.3)]; there `α ∈ (0, 1]`. Result: subspace-injection -/
def IsSubspaceInjection (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (a : ℝ) : Prop :=
  a • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)
/-- **Subspace embedding**, lower `a`, upper `b`. [Woodruff2014, Definition 1] (`1 ∓ ε`);
[CamanoEpperlyMeyerTropp2025, Definition 1.1] (`α`, `β`); [MartinssonTropp2020, §8.1]. Result: ose-def -/
structure IsSubspaceEmbedding (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (a b : ℝ) : Prop where
  lower : IsSubspaceInjection S U a
  upper : (S * U)ᴴ * (S * U) ≤ b • (Uᴴ * U)

theorem isSubspaceInjection_iff_forall_mem_range : IsSubspaceInjection S U a ↔
    ∀ y ∈ LinearMap.range U.mulVecLin, a * ‖WithLp.toLp 2 y‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2
theorem isSubspaceEmbedding_iff_forall_mem_range : IsSubspaceEmbedding S U a b ↔
    ∀ y ∈ LinearMap.range U.mulVecLin, a * ‖WithLp.toLp 2 y‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 ∧
      ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 ≤ b * ‖WithLp.toLp 2 y‖ ^ 2
theorem HasOrthonormalCols.isSubspaceInjection_iff [DecidableEq p] (hU : HasOrthonormalCols U) :
    IsSubspaceInjection S U a ↔ a • (1 : Matrix p p 𝕜) ≤ (S * U)ᴴ * (S * U)
theorem HasOrthonormalCols.isSubspaceEmbedding_iff_specNorm_le [DecidableEq p]
    (hU : HasOrthonormalCols U) (hε : 0 ≤ ε) :
    IsSubspaceEmbedding S U (1 - ε) (1 + ε) ↔ specNorm ((S * U)ᴴ * (S * U) - 1) ≤ ε
/-- `a ≤ σ_min(S U)²`; the upper half is `specNorm_sq_le_iff_conjTranspose_mul_self_le` after `hU`. -/
theorem HasOrthonormalCols.isSubspaceInjection_iff_le_sq_singularValues [DecidableEq p]
    (hU : HasOrthonormalCols U) {j : ℕ} (hj : j + 1 = Fintype.card p) :
    IsSubspaceInjection S U a ↔ a ≤ singularValues (S * U) j ^ 2
/-- AMM at `A = B = U` gives the embedding (D7): `specNorm ≤ frobNorm`. -/
theorem HasOrthonormalCols.isSubspaceEmbedding_of_frobNorm_le [DecidableEq p]
    (hU : HasOrthonormalCols U) (h : frobNorm (Uᴴ * Sᴴ * S * U - Uᴴ * U) ≤ ε) :
    IsSubspaceEmbedding S U (1 - ε) (1 + ε)
theorem IsSubspaceInjection.mono (h : IsSubspaceInjection S U a) (ha : a' ≤ a) :
    IsSubspaceInjection S U a'
theorem IsSubspaceEmbedding.mono (h : IsSubspaceEmbedding S U a b) (ha : a' ≤ a) (hb : b ≤ b') :
    IsSubspaceEmbedding S U a' b'
theorem IsSubspaceInjection.of_range_le (h : IsSubspaceInjection S U a)
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) : IsSubspaceInjection S V a
theorem IsSubspaceEmbedding.of_range_le (h : IsSubspaceEmbedding S U a b)
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) : IsSubspaceEmbedding S V a b
theorem IsSubspaceInjection.mul_right (h : IsSubspaceInjection S U a) (C : Matrix p q 𝕜) :
    IsSubspaceInjection S (U * C) a
theorem IsSubspaceEmbedding.mul_right (h : IsSubspaceEmbedding S U a b) (C : Matrix p q 𝕜) :
    IsSubspaceEmbedding S (U * C) a b
theorem IsSubspaceInjection.smul (h : IsSubspaceInjection S U a) (c : 𝕜) :
    IsSubspaceInjection (c • S) U (‖c‖ ^ 2 * a)
theorem IsSubspaceEmbedding.smul (h : IsSubspaceEmbedding S U a b) (c : 𝕜) :
    IsSubspaceEmbedding (c • S) U (‖c‖ ^ 2 * a) (‖c‖ ^ 2 * b)
theorem IsSubspaceInjection.mul {S₂ : Matrix l k 𝕜} (h₂ : IsSubspaceInjection S₂ (S * U) a₂)
    (h : IsSubspaceInjection S U a) (ha₂ : 0 ≤ a₂) : IsSubspaceInjection (S₂ * S) U (a₂ * a)
theorem IsSubspaceEmbedding.mul {S₂ : Matrix l k 𝕜} (h₂ : IsSubspaceEmbedding S₂ (S * U) a₂ b₂)
    (h : IsSubspaceEmbedding S U a b) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) :
    IsSubspaceEmbedding (S₂ * S) U (a₂ * a) (b₂ * b)
theorem isSubspaceInjection_of_nonpos (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (ha : a ≤ 0) :
    IsSubspaceInjection S U a
theorem IsSubspaceInjection.injOn (h : IsSubspaceInjection S U a) (ha : 0 < a) :
    Set.InjOn S.mulVec (LinearMap.range U.mulVecLin)
theorem IsSubspaceInjection.injective_mulVec (h : IsSubspaceInjection S U a) (ha : 0 < a)
    (hU : Function.Injective U.mulVec) : Function.Injective (S * U).mulVec
theorem isClosed_setOf_isSubspaceInjection (a : ℝ) :
    IsClosed {x : Matrix k n 𝕜 × Matrix n p 𝕜 | IsSubspaceInjection x.1 x.2 a}
theorem isClosed_setOf_isSubspaceEmbedding (a b : ℝ) :
    IsClosed {x : Matrix k n 𝕜 × Matrix n p 𝕜 | IsSubspaceEmbedding x.1 x.2 a b}
theorem measurableSet_setOf_isSubspaceInjection (U : Matrix n p 𝕜) (a : ℝ) :
    MeasurableSet {S : Matrix k n 𝕜 | IsSubspaceInjection S U a}
theorem measurableSet_setOf_isSubspaceEmbedding (U : Matrix n p 𝕜) (a b : ℝ) :
    MeasurableSet {S : Matrix k n 𝕜 | IsSubspaceEmbedding S U a b}
```

Proof routes: range forms from `Matrix.IsHermitian.le_iff_re_quadForm_le` (as
`smul_one_le_conjTranspose_mul_self_iff`); `mul_right` by `range_mulVecLin_le_iff_exists_mul`; `mul`,
`mono` by `conjTranspose_mul_mul_le_conjTranspose_mul_mul`; `specNorm` form by
`one_sub_smul_one_le_conjTranspose_mul_self_of_specNorm_le`, its upper twin, `IsHermitian.specNorm_le_iff`;
singular values by `le_sq_singularValues_last_of_smul_one_le`, `sq_singularValues_last_smul_one_le`; AMM
by `specNorm_le_frobNorm`; closedness by `isClosed_le` (scoped `Matrix.instOrderClosedTopology`).

### 3.2 `Sketching/Properties/LeastSquares.lean`

`[DecidableEq n]`; `A : Matrix n q 𝕜`, `y : n → 𝕜`, `x : q → 𝕜`. The sketched problem is
`IsLeastSquaresSolution (S * A) (S *ᵥ y) x` (every minimizer, not only the minimum-norm one); the
optimal residual is `(1 - rangeProjector A) *ᵥ y` (§5.3).

```lean
/-- **Sketch-and-solve** (D7). [Woodruff2014, proof of Theorem 21]; [MartinssonTropp2020, §10.3];
there `(1 + ε) / (1 - ε)`. Result: sketch-and-solve-ls -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sq_le (h : IsSubspaceEmbedding S U a b) (ha : 0 < a)
    (hA : LinearMap.range A.mulVecLin ≤ LinearMap.range U.mulVecLin)
    (hy : y ∈ LinearMap.range U.mulVecLin) (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤ b / a * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2
theorem IsSubspaceEmbedding.norm_sub_mulVec_le … :   -- same hypotheses
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ≤ √(b / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖
/-- The brief's form, `U = [A, y]`. -/
theorem IsSubspaceEmbedding.norm_sub_mulVec_sq_le_of_fromCols
    (h : IsSubspaceEmbedding S (Matrix.fromCols A (Matrix.replicateCol Unit y)) a b) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤ b / a * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2
/-- **Sketch-and-precondition**, spectral equivalence, for any `M` with `S A M` orthonormal. -/
theorem IsSubspaceEmbedding.inv_smul_one_le_conjTranspose_mul_self [DecidableEq r]
    {M : Matrix q r 𝕜} (h : IsSubspaceEmbedding S A a b) (hb : 0 < b)
    (hM : HasOrthonormalCols (S * A * M)) : b⁻¹ • (1 : Matrix r r 𝕜) ≤ (A * M)ᴴ * (A * M)
theorem IsSubspaceEmbedding.conjTranspose_mul_self_le_inv_smul_one [DecidableEq r]
    {M : Matrix q r 𝕜} (h : IsSubspaceEmbedding S A a b) (ha : 0 < a)
    (hM : HasOrthonormalCols (S * A * M)) : (A * M)ᴴ * (A * M) ≤ a⁻¹ • (1 : Matrix r r 𝕜)
/-- `κ(A M)² ≤ b / a`. [MartinssonTropp2020, §10.5]. Result: sketch-and-precondition -/
theorem IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le [DecidableEq r] {M : Matrix q r 𝕜}
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hb : 0 ≤ b)
    (hM : HasOrthonormalCols (S * A * M)) : pseudoConditionNumber (A * M) ^ 2 ≤ b / a
theorem IsSubspaceEmbedding.pseudoConditionNumber_mul_inv_sq_le_of_isQR [DecidableEq q]
    {Q : Matrix k q 𝕜} {R : Matrix q q 𝕜} (h : IsSubspaceEmbedding S A a b) (ha : 0 < a)
    (hb : 0 ≤ b) (hQR : IsQR (S * A) Q R) (hR : IsUnit R) : pseudoConditionNumber (A * R⁻¹) ^ 2 ≤ b / a
/-- The sketched solution's error from the injection alone (CEMT Lemma 2.6, norm form). -/
theorem IsSubspaceInjection.norm_mulVec_sub_rangeProjector_mulVec_sq_le
    (h : IsSubspaceInjection S A a) (ha : 0 < a) (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (A *ᵥ x - rangeProjector A *ᵥ y)‖ ^ 2 ≤
      ‖WithLp.toLp 2 (S *ᵥ ((1 - rangeProjector A) *ᵥ y))‖ ^ 2 / a
/-- **Sketch-and-solve error formula** [CamanoEpperlyMeyerTropp2025, Lemma 2.6, proof of Theorem 2.7];
there an identity for the minimum-norm solution, here a bound for every minimizer. -/
theorem IsSubspaceInjection.norm_sub_mulVec_sq_le (h : IsSubspaceInjection S A a) (ha : 0 < a)
    (hx : IsLeastSquaresSolution (S * A) (S *ᵥ y) x) :
    ‖WithLp.toLp 2 (y - A *ᵥ x)‖ ^ 2 ≤ ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 +
      ‖WithLp.toLp 2 (S *ᵥ ((1 - rangeProjector A) *ᵥ y))‖ ^ 2 / a
/-- The matrix right-hand side, for the minimum-norm output `pinv (S A) (S Y)` (generalized Nyström). -/
theorem IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le (h : IsSubspaceInjection S A a)
    (ha : 0 < a) (Y : Matrix n r 𝕜) :
    frobNorm (Y - A * (pinv (S * A) * (S * Y))) ^ 2 ≤
      frobNorm ((1 - rangeProjector A) * Y) ^ 2 + frobNorm (S * ((1 - rangeProjector A) * Y)) ^ 2 / a
/-- **Deterministic half of CEMT Lemma 2.1**: `‖X (S U)ᴴ†‖_F² ≤ ‖X‖_F² / a` for orthonormal `U`;
CEMT apply it at `X = B (S Q⊥)ᴴ`. -/
theorem IsSubspaceInjection.frobNorm_mul_pinv_sq_le [DecidableEq p] (h : IsSubspaceInjection S U a)
    (hU : HasOrthonormalCols U) (ha : 0 < a) (X : Matrix l k 𝕜) :
    frobNorm (X * pinv ((S * U)ᴴ)) ^ 2 ≤ frobNorm X ^ 2 / a
```

Proof routes: sketch-and-solve, `a ‖y - A x̃‖² ≤ ‖S (y - A x̃)‖² ≤ ‖S (y - A x⋆)‖² ≤ b ‖r‖²`;
preconditioning, both halves on `A M` by `of_range_le`, then
`pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one` (empty `r`: `κ = 0`, hence `hb`); error
formula, for `w = A x̃ - P_A y ∈ range A` the sketched normal equations
(`isLeastSquaresSolution_iff_conjTranspose_mulVec_sub_eq_zero`) make `S w` the projection of `S r` on
`range (S A)`, so `a ‖w‖² ≤ ‖S w‖² ≤ ‖S r‖²`, then `IsLeastSquaresSolution.norm_sub_mulVec_sq_eq_add`;
matrix form by columns (`isLeastSquaresSolution_pinv_mulVec`); Lemma 2.1 by
`frobNorm_mul_le_frobNorm_mul_specNorm`, `pinv_conjTranspose`, `specNorm_pinv_sq_le_inv_of_smul_one_le`.

### 3.3 Matrix-layer additions (skeleton file `NLAlib/Matrix/Basic/FromCols.lean`)

A new file, as R5's `PolarFrames.lean` (proved files take no `sorry`); merged into its owner at the
wrap-up. Searched: Mathlib has `Matrix.fromCols_mulVec`, no range statement; NLAlib none.
1. `range_mulVecLin_le_range_fromCols_left (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
   LinearMap.range A.mulVecLin ≤ LinearMap.range (Matrix.fromCols A B).mulVecLin`.
2. `mem_range_mulVecLin_fromCols_replicateCol (A : Matrix n q 𝕜) (y : n → 𝕜) :
   y ∈ LinearMap.range (Matrix.fromCols A (Matrix.replicateCol Unit y)).mulVecLin`.
Everything else S0 uses is built (named in the proof routes).

## 4. Files

1. `NLAlib/Matrix/Basic/FromCols.lean`: §3.3 (2).
2. `Sketching/Properties/SubspaceEmbedding.lean`: §3.1 (25). Imports `Matrix/Norms/Loewner`, `Matrix/Spectral/SingularValues`,
   `Matrix/Norms/Compare`, `Matrix/Basic/Projector`, `ForMathlib/LinearAlgebra/Matrix/PosDef`,
   `ForMathlib/MeasureTheory/Matrix`.
3. `Sketching/Properties/LeastSquares.lean`: §3.2 (11). Imports 1, 2,
   `Matrix/Pseudoinverse/{LeastSquares,ConditionNumber,NormBounds}`, `Matrix/Factorizations/QR`. 1 is independent of 2.

## 5. Material

Read: the prototype's `Sketching/Properties/SubspaceEmbedding/` (5 files, 320 lines),
`LowRank/Nystrom/SketchedRegression.lean` (`error_decomp`, `frobSq_error`: proof material for the
matrix error formula; its LowRank port should cite S0), the inventory §2, §4.1, §10, CEMT §1.1, §2.1,
§2.4. Ledger (prototype → here): `IsSubspaceEmbedding` → D1 structure;
`isSubspaceEmbedding_iff_of_hasOrthonormalCols` → range form; the three `specNorm_transpose_mul_self_sub_one`
lemmas → `isSubspaceEmbedding_iff_specNorm_le`; `isSubspaceEmbedding_iff_singularValues` → singular-value
form; `specNorm_gram_sub_one_le_iff_singularValues_sq`, `transpose_mul_self_sub_one_reindex` → Matrix
layer, already ported (`specNorm_conjTranspose_mul_self_sub_one_le_iff`); `.mono` → `mono`; `.mul_right`,
`.of_mul_right`, `isSubspaceEmbedding_mul_right_iff` → `mul_right`, `of_range_le`;
`isSubspaceEmbedding_reindex_iff` → not ported (§6). `CamanoEpperlyMeyerTropp2025` enters
`docs/references.bib` in the first S0 PR (D16). Result ids: `ose-def`, `sketch-and-solve-ls`,
`sketch-and-precondition` (atlas), `subspace-injection` (new).

## 6. Cut, and why

- `isSubspaceEmbedding_reindex_iff` and the `Fin` transport (D5); an `ε`-only predicate with its
  `3 * a ≤ ε`, `ε ≤ 1` side conditions, and a separate upper-half predicate (D1).
- `…_iff_of_range_eq`, `…_rangeProjector_iff`: two applications of `of_range_le`.
- An iterative-solver theorem for sketch-and-precondition (Solvers round); S0 gives its conditioning.
- CEMT's exact identity `Z̃ - Z⋆ = Ψ₁† Ψ₂ Q⊥ᴴ B`: its consumers (Theorem 2.7, Corollary 2.8) use only
  the bound; added if one rewrites with it.

## 7. Questions and decisions

No question of the brief's §2 kind. Decisions taken (open to correction):

**Q1. Sketch-and-solve takes any `U` with `range A ≤ range U`, `y ∈ range U`**; `[A, y]` is a
corollary. A consumer holding an embedding of a larger subspace (many right-hand sides) applies it
without rebasing.

**Q2. Preconditioning for any `M` with `HasOrthonormalCols (S * A * M)`** (QR's `R⁻¹`, SVD's `V Σ⁻¹`,
Cholesky-QR), the QR form a corollary; the Loewner pair is stated beside `κ`, because preconditioned
CG and LSQR bounds take the spectral equivalence.

**Q3. Every minimizer in the vector statements** (`IsLeastSquaresSolution`, §5.3); the matrix form
uses `pinv (S * A) * (S * Y)`, the reported output, which generalized Nyström needs (CEMT
Corollary 2.8 applies Theorem 2.7 with a matrix right-hand side).

**Q4. `IsSubspaceInjection` is a `def`, not an `abbrev`**: an `abbrev` makes `simp` normal forms
unstable (it sees `≤`); the range form is the documented interface.

## 8. Amendments from the review (2026-10-14)

Review of S0 and S1 (2026-10-14); all findings accepted by the orchestrator. Skeletons:
`NLAlib/Matrix/Basic/FromCols.lean` (2), `NLAlib/Sketching/Properties/SubspaceEmbedding.lean` (27),
`NLAlib/Sketching/Properties/LeastSquares.lean` (11), every proof `sorry`.

1. **`IsQR` needs `[LinearOrder q]`** (`Matrix/Factorizations/QR.lean`, its variable line).
   `pseudoConditionNumber_mul_inv_sq_le_of_isQR` takes `[LinearOrder q] [DecidableEq q]`; the §3
   variable sentence is corrected.
2. **Citations.** [MartinssonTropp2020, §8.1] defines the embedding with unsquared norms and §10.3
   prints `‖A x̂ - b‖ ≤ (1 + ε) ‖A x⋆ - b‖` unsquared (after Sarlós); `(1 + ε) / (1 - ε)` is
   Woodruff's proof of Theorem 21, in squared norms. The `IsSubspaceEmbedding` and sketch-and-solve
   docstrings say "unsquared there" and attribute the ratio to Woodruff.
3. **Real-scalar corollaries** `IsSubspaceInjection.smul_real`, `IsSubspaceEmbedding.smul_real`
   (`c : ℝ`, constants `c ^ 2 * a`, `c ^ 2 * b`), after the `𝕜` forms: families scale by
   `(√k)⁻¹ : ℝ`. §3.1 has 27 statements.
4. **`pseudoConditionNumber_mul_sq_le` keeps `hb : 0 ≤ b`.** For nonempty `r`, `hM` and the upper half give
   `1 ≤ b • (A M)ᴴ (A M)`, so `0 < b`; `b = 0` forces `r` empty, where `κ(A M) = 0` and the bound is
   `hb`. The route splits on `IsEmpty r`; the docstring says so. Same for the QR corollary.
5. **Preconditioning route**: both halves on `A * M` by `h.mul_right M` (not `of_range_le`), then
   `hM` turns `(S A M)ᴴ (S A M)` into `1`.

Skeleton-level changes, same meaning:

- Instance placement. Mathlib's Loewner order on `Matrix p p 𝕜` needs no `Fintype p`, so the two
  predicates and the lemmas that only mention them take no `[Fintype p]`; `[Fintype p]`,
  `[Fintype q]`, `[Fintype r]` sit on the declarations that use `mulVecLin`, `specNorm`,
  `frobNorm`, `singularValues` or a product over that index (`unusedFintypeInType`). In
  `LeastSquares.lean`, `[DecidableEq n]` is a section variable of the sketch-and-solve and
  error-formula sections only (`unusedDecidableInType`).

### Placement refactor (2026-10-15)

- Amendment 2026-10-15: `Matrix/Basic/FromCols.lean` moves to
  `ForMathlib/Data/Matrix/ColumnRowPartitioned.lean` as
  `Matrix.range_mulVecLin_le_range_fromCols_left` and
  `Matrix.mem_range_mulVecLin_fromCols_replicateCol` over any commutative semiring; `FromCols.lean`
  keeps only the two deprecated aliases. The private `smul_le_smul` copies of
  `SubspaceEmbedding.lean` and `LeastSquares.lean` are one public `NLAlib.smul_le_smul_of_nonneg` in
  `Matrix/Norms/Loewner.lean`.
