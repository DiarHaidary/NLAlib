/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Moments
public import NLAlib.RandomMatrix.Haar.Sphere
public import NLAlib.RandomMatrix.Haar.Transfer
public import NLAlib.Sketching.Gaussian.Gaussian

/-!
# Haar sketches

The Haar sketch is `S = √(n/k) • Qᴴ` for an `n × k` Haar frame `Q`, `card k ≤ card n`: `k`
orthonormal rows, scaled. It is written out in each statement,
`fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ`, with the hypothesis
`HasLaw Q (haarFrame n k) μ`; there is no named sketch law (`docs/design/Sketching-S2.md` §7 Q1).

It is exactly isotropic, like a Gaussian sketch, and unlike it has a deterministic norm
`specNorm S = √(n/k)`. Its upper half is deterministic: `(S U)ᴴ (S U) ≤ (n/k) • Uᴴ U` almost
surely, and at `k = n` the sketch is orthogonal, an exact embedding. Its Gram matrix on `U` has the
law of `(n/k) Uᴴ P_G U` for the range projector `P_G` of an `n × k` Gaussian (the transfer of
`NLAlib/RandomMatrix/Haar/Transfer.lean`); the inverse-Gram identity
`Uᴴ P_G U = (Gᴴ U)ᴴ (Gᴴ G)⁻¹ (Gᴴ U)` and Gordon's tails then give the lower constant
`a_H = (1 - (√p + t)/√k)² / (1 + (√k + s)/√n)²`, with a tail in `t` for the subspace and one in
`s` for the frame, and the upper constant `b_H = (1 + (√p + t)/√k)² / (1 - (√k + s)/√n)²` for
`s < √n - √k`. Both are lossy near `k = n`; there the complement route is sharp: with `c` the
codimension (`card k + c = card n`), `Q ~ P V₁` and `Q⊥ := P V₂` for a square Haar frame `P`,
`Uᴴ Q Qᴴ U = 1 - Uᴴ Q⊥ Q⊥ᴴ U`, and the inverse-Gram step on the `n × c` Gaussian behind `Q⊥` gives
`a = (n/k)(1 - (√c + √p + t)² / (√n - √c - s)²)`, which tends to `1` as `c / n → 0`.

The JL tails are the projection tails of a uniform unit vector
(`NLAlib/RandomMatrix/Haar/Sphere.lean`), with the Gaussian's constants; the JL variance is
`2 (n - k) / (k (n + 2))`, below the Gaussian's `2 / k` and `0` at `k = n`.

Degenerate cases: for empty `k`, `√(n/0) = 0` and `S = 0`, hence `[Nonempty k]` on isotropy, the
OSI and the moments. Design: `docs/design/Sketching-S2.md` §3.4, §8.

## Main results

* `NLAlib.isIsotropicSketch_of_hasLaw_haarFrame`, `NLAlib.ae_specNorm_eq_of_hasLaw_haarFrame`.
* `NLAlib.hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame`: the Gaussian transfer.
* `NLAlib.ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`: the upper half.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_eq`: exact at `k = n`.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame`,
  `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`,
  `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq`: three
  incomparable fixed-subspace embeddings.
* `NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame`,
  `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame`.
* `NLAlib.hasJLProperty_of_hasLaw_haarFrame`, `NLAlib.hasJLMoment_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n p : Type*} [Fintype k]
  [Fintype n] [Fintype p] [DecidableEq k] {Q : Ω → Matrix n k ℝ} {U : Matrix n p ℝ}
  {t s ε δ : ℝ}

/-! ### Helpers -/

omit [DecidableEq k] in
/-- The scaling of the Haar sketch squares to `n/k`. -/
private theorem sqrt_mul_sqrt_card_div :
    √(Fintype.card n / Fintype.card k : ℝ) * √(Fintype.card n / Fintype.card k : ℝ) =
      (Fintype.card n / Fintype.card k : ℝ) :=
  Real.mul_self_sqrt (by positivity)

omit [DecidableEq k] [Fintype p] in
/-- The Gram matrix of the Haar sketch on `U`: `(S U)ᴴ (S U) = (n/k) • Uᴴ (Q Qᴴ) U`. -/
private theorem gram_smul_conjTranspose (M : Matrix n k ℝ) (U : Matrix n p ℝ) :
    (√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ * U) =
      (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * (M * Mᴴ) * U) := by
  rw [Matrix.smul_mul, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, sqrt_mul_sqrt_card_div, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

omit [DecidableEq k] in
/-- The squared length of `S x`: `‖S x‖² = (n/k) ‖Qᴴ x‖²`. -/
private theorem norm_smul_conjTranspose_mulVec_sq (M : Matrix n k ℝ) (x : n → ℝ) :
    ‖WithLp.toLp 2 ((√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ) *ᵥ x)‖ ^ 2 =
      (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 (Mᴴ *ᵥ x)‖ ^ 2 := by
  rw [Matrix.smul_mulVec, WithLp.toLp_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

omit [Fintype k] [DecidableEq k] [Fintype p] in
/-- **Congruence preserves positive semidefiniteness**, for a factor with any column type (no
finiteness of `p`): the quadratic form of `Xᴴ D X` at a finitely supported `x` is that of the
compression to the support. -/
private theorem posSemidef_conjTranspose_mul_mul_same' {D : Matrix n n ℝ} (hD : D.PosSemidef)
    (X : Matrix n p ℝ) : (Xᴴ * D * X).PosSemidef := by
  classical
  refine ⟨Matrix.isHermitian_conjTranspose_mul_mul X hD.1, fun x => ?_⟩
  have hs := hD.conjTranspose_mul_mul_same (X.submatrix id (Subtype.val : x.support → p))
  have h := hs.2 (x.subtypeDomain (· ∈ x.support))
  have key : (X.submatrix id (Subtype.val : x.support → p))ᴴ * D *
      X.submatrix id (Subtype.val : x.support → p) =
      (Xᴴ * D * X).submatrix Subtype.val Subtype.val := by
    ext i j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
  rw [key] at h
  simp only [Matrix.submatrix_apply] at h
  have hin (i : p) (xi : ℝ) : ((x.subtypeDomain (· ∈ x.support)).sum fun j xj =>
      star xi * (Xᴴ * D * X) i j * xj) = x.sum fun j xj => star xi * (Xᴴ * D * X) i j * xj :=
    Finsupp.sum_subtypeDomain_index (v := x) (p := fun a => a ∈ x.support)
      (h := fun j xj => star xi * (Xᴴ * D * X) i j * xj) (fun _ hi => hi)
  simp only [hin] at h
  rwa [Finsupp.sum_subtypeDomain_index (v := x) (p := fun a => a ∈ x.support)
    (h := fun i xi => x.sum fun j xj => star xi * (Xᴴ * D * X) i j * xj) (fun _ hi => hi)] at h

omit [Fintype k] [DecidableEq k] [Fintype p] in
/-- Congruence preserves the Loewner order, for a factor with any column type. -/
private theorem conjTranspose_mul_mul_le_conjTranspose_mul_mul' {G H : Matrix n n ℝ}
    (h : G ≤ H) (X : Matrix n p ℝ) : Xᴴ * G * X ≤ Xᴴ * H * X := by
  rw [Matrix.le_iff] at h ⊢
  rw [← Matrix.sub_mul, ← Matrix.mul_sub]
  exact posSemidef_conjTranspose_mul_mul_same' h X

omit [Fintype p] in
/-- A nonnegative scalar preserves the Loewner order. -/
private theorem smul_le_smul_loewner {A B : Matrix p p ℝ} (h : A ≤ B) {c : ℝ} (hc : 0 ≤ c) :
    c • A ≤ c • B := by
  rw [Matrix.le_iff] at h ⊢
  rw [← smul_sub]
  exact h.smul hc

/-! ### Isotropy, norm and the Gaussian transfer -/

open scoped Matrix.Norms.L2Operator in
/-- **A Haar sketch is isotropic**: `E [Sᴴ S] = (n/k) E [Q Qᴴ] = 1`
(`NLAlib.integral_mul_conjTranspose_of_hasLaw_haarFrame`), exactly, as for a Gaussian sketch.
[MartinssonTropp2020, §8.9]. -/
theorem isIsotropicSketch_of_hasLaw_haarFrame [DecidableEq n] [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    IsIsotropicSketch (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.conjTranspose_apply, star_trivial, smul_eq_mul]
    exact (memLp_apply_of_hasLaw_haarFrame hQ j i 2).const_mul _
  · have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
    have hN : (0 : ℝ) < Fintype.card n := hK.trans_le (Nat.cast_le.2 hk)
    have h (ω : Ω) : (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) =
        (Fintype.card n / Fintype.card k : ℝ) • (Q ω * (Q ω)ᴴ) := by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_conjTranspose,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt_mul_sqrt_card_div]
    simp only [h]
    rw [integral_smul, integral_mul_conjTranspose_of_hasLaw_haarFrame hQ hk, smul_smul,
      div_mul_div_comm, mul_comm (Fintype.card n : ℝ), div_self (by positivity), one_smul]

/-- **The norm of a Haar sketch is deterministic**: `specNorm S = √(n/k)` almost surely, since
`Q` has orthonormal columns (`NLAlib.HasOrthonormalCols.specNorm_eq_one`); for empty `k` both
sides are `0`. [MartinssonTropp2020, §8.9]. -/
theorem ae_specNorm_eq_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    ∀ᵐ ω ∂μ, specNorm (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) =
      √(Fintype.card n / Fintype.card k : ℝ) := by
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hk] with ω hω
  rw [specNorm_smul, specNorm_conjTranspose, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases isEmpty_or_nonempty k with hk0 | hk0
  · rw [Fintype.card_eq_zero (α := k), Nat.cast_zero, div_zero, Real.sqrt_zero, zero_mul]
  · rw [hω.specNorm_eq_one, mul_one]

omit [Fintype p] in
/-- **Gaussian transfer of the Haar Gram matrix**: `(S U)ᴴ (S U)` has the law of
`(n/k) Uᴴ P_G U`, `P_G` the range projector of an `n × k` standard Gaussian, for every `U`; `Q Qᴴ`
is the range projector of `Q` almost surely (`NLAlib.HasOrthonormalCols.rangeProjector_eq`), and
`NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame` at `A = 1` transfers it. -/
theorem hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (U : Matrix n p ℝ) :
    HasLaw (fun ω => (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U))
      ((gaussianMatrix n k).map fun G =>
        (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * rangeProjector G * U)) μ := by
  classical
  have hP := hasLaw_rangeProjector_mul_of_hasLaw_haarFrame (1 : Matrix n n ℝ) hQ
  simp only [Matrix.one_mul] at hP
  have hf : Measurable fun M : Matrix n n ℝ =>
      (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * M * U) :=
    ((measurable_const.matrix_mul measurable_id).matrix_mul measurable_const).matrix_const_smul _
  have h := HasLaw.fun_comp (Y := fun M : Matrix n n ℝ =>
    (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * M * U)) ⟨hf.aemeasurable, rfl⟩ hP
  rw [Measure.map_map hf measurable_rangeProjector] at h
  refine h.congr ?_
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hk] with ω hω
  rw [gram_smul_conjTranspose, hω.rangeProjector_eq]

/-! ### Deterministic halves -/

omit [Fintype p] in
/-- **The upper half of a Haar sketch is deterministic**: `(S U)ᴴ (S U) ≤ (n/k) • (Uᴴ U)` almost
surely, for every `U`, every shape, with no parameter: `Q Qᴴ ≤ 1` because `specNorm Q ≤ 1`
(`NLAlib.ae_specNorm_le_one_of_hasLaw_haarFrame`,
`NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le`). -/
theorem ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame n k) μ) (U : Matrix n p ℝ) :
    ∀ᵐ ω ∂μ, (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U) ≤
      (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * U) := by
  classical
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ] with ω hω
  rw [gram_smul_conjTranspose]
  have h1 : Q ω * (Q ω)ᴴ ≤ (1 : ℝ) • (1 : Matrix n n ℝ) := by
    have := (specNorm_sq_le_iff_conjTranspose_mul_self_le (T := (Q ω)ᴴ) zero_le_one).1
      (by rw [specNorm_conjTranspose]; nlinarith [specNorm_nonneg (Q ω)])
    rwa [Matrix.conjTranspose_conjTranspose] at this
  rw [one_smul] at h1
  have h2 := conjTranspose_mul_mul_le_conjTranspose_mul_mul' h1 U
  rw [Matrix.mul_one] at h2
  exact smul_le_smul_loewner h2 (by positivity)

omit [Fintype p] in
/-- **A square Haar sketch is an exact embedding**: for `card k = card n`, `S = Qᴴ` is orthogonal
almost surely, so it is a subspace embedding for every `range U` with constants `1`, `1` and
failure probability `0`. -/
theorem hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_eq (hQ : HasLaw Q (haarFrame n k) μ)
    (hkn : Fintype.card k = Fintype.card n) (U : Matrix n p ℝ) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U 1 1 0 μ := by
  classical
  have hae : ∀ᵐ ω ∂μ, IsSubspaceEmbedding (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ)
      U 1 1 := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hkn.le] with ω hω
    have hg : (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U) = (1 : ℝ) • (Uᴴ * U) := by
      rw [gram_smul_conjTranspose, hω.mul_conjTranspose_self_of_card_eq hkn.symm, Matrix.mul_one,
        hkn]
      rcases isEmpty_or_nonempty n with hn | hn
      · have : Uᴴ * U = 0 := by
          ext i j
          simp only [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty, Matrix.zero_apply]
        rw [this, smul_zero, smul_zero]
      · rw [div_self (by positivity)]
    exact ⟨by rw [IsSubspaceInjection, hg], by rw [hg]⟩
  unfold HasSubspaceEmbedding
  rw [Measure.real, ae_iff.1 hae, ENNReal.toReal_zero]

omit [Fintype k] [DecidableEq k] [Fintype p] in
/-- Every event on matrices indexed by an empty type has probability `0`, so for empty `p` every
fixed-subspace property holds with any `δ ≥ 0`. -/
private theorem hasSubspaceEmbedding_of_isEmpty {m : Type*} [Fintype m] [IsEmpty p]
    {S : Ω → Matrix m n ℝ} {a b δ : ℝ} (hδ : 0 ≤ δ) : HasSubspaceEmbedding S U a b δ μ := by
  have hsub : ∀ M N : Matrix p p ℝ, M ≤ N :=
    fun M N => le_of_eq (Matrix.ext fun i => isEmptyElim i)
  have : {ω | ¬ IsSubspaceEmbedding (S ω) U a b} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact ⟨hsub _ _, hsub _ _⟩
  unfold HasSubspaceEmbedding
  rw [this, measureReal_empty]
  exact hδ

omit [Fintype k] [DecidableEq k] [Fintype p] in
/-- The injection form of `hasSubspaceEmbedding_of_isEmpty`. -/
private theorem hasSubspaceInjection_of_isEmpty {m : Type*} [Fintype m] [IsEmpty p]
    {S : Ω → Matrix m n ℝ} {a δ : ℝ} (hδ : 0 ≤ δ) : HasSubspaceInjection S U a δ μ := by
  have hsub : ∀ M N : Matrix p p ℝ, M ≤ N :=
    fun M N => le_of_eq (Matrix.ext fun i => isEmptyElim i)
  have : {ω | ¬ IsSubspaceInjection (S ω) U a} = ∅ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hsub _ _
  unfold HasSubspaceInjection
  rw [this, measureReal_empty]
  exact hδ

omit [Fintype k] [DecidableEq k] [Fintype p] in
/-- The inverse-Gram identity `Uᴴ P_G U = (Gᴴ U)ᴴ (Gᴴ G)⁻¹ (Gᴴ U)` for invertible `Gᴴ G`. -/
private theorem conjTranspose_mul_rangeProjector_mul_eq {l : Type*} [Fintype l] [DecidableEq l]
    {G : Matrix n l ℝ} (hG : IsUnit (Gᴴ * G)) (U : Matrix n p ℝ) :
    Uᴴ * rangeProjector G * U = (Gᴴ * U)ᴴ * (Gᴴ * G)⁻¹ * (Gᴴ * U) := by
  rw [rangeProjector_eq_mul_inv_mul_conjTranspose hG, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-! ### A fixed subspace -/

variable [DecidableEq p]

omit [Fintype k] [DecidableEq k] [Fintype p] [DecidableEq p] in
/-- `Xᴴ (c • 1) X = c • Xᴴ X`. -/
private theorem conjTranspose_mul_smul_one_mul {l : Type*} [Fintype l] [DecidableEq l]
    (X : Matrix l p ℝ) (c : ℝ) : Xᴴ * (c • (1 : Matrix l l ℝ)) * X = c • (Xᴴ * X) := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

omit [Fintype k] [DecidableEq k] in
/-- **The Gaussian lower bound on `Uᴴ P_G U`**: for an `n × l` Gaussian `G`, `l ≤ n`,
`(√l - √p - t)² / (√n + √l + s)² • 1 ≤ Uᴴ P_G U` outside probability `e^{-t²/2} + e^{-s²/2}`:
Gordon's lower tail for the `l × p` Gaussian `Gᴴ U`, the upper tail of `Gᴴ G`, and the
inverse-Gram identity. -/
private theorem measureReal_not_smul_one_le_conjTranspose_mul_rangeProjector_mul_le
    (hU : HasOrthonormalCols U) {l : Type*} [Fintype l] (hl : Fintype.card l ≤ Fintype.card n)
    (ht : 0 ≤ t) (htl : t ≤ √(Fintype.card l : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s) :
    (gaussianMatrix n l).real {G | ¬ ((√(Fintype.card l : ℝ) - √(Fintype.card p : ℝ) - t) ^ 2 /
      (√(Fintype.card n : ℝ) + √(Fintype.card l : ℝ) + s) ^ 2) • (1 : Matrix p p ℝ) ≤
        Uᴴ * rangeProjector G * U} ≤ Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2) := by
  classical
  rcases isEmpty_or_nonempty p with hp | hp
  · have hsub : ∀ M N : Matrix p p ℝ, M ≤ N :=
      fun M N => le_of_eq (Matrix.ext fun i => isEmptyElim i)
    have : {G : Matrix n l ℝ | ¬ ((√(Fintype.card l : ℝ) - √(Fintype.card p : ℝ) - t) ^ 2 /
        (√(Fintype.card n : ℝ) + √(Fintype.card l : ℝ) + s) ^ 2) • (1 : Matrix p p ℝ) ≤
        Uᴴ * rangeProjector G * U} = ∅ := by
      ext G
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      exact hsub _ _
    rw [this, measureReal_empty]
    positivity
  have hp1 : (1 : ℝ) ≤ √(Fintype.card p : ℝ) :=
    Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have hn1 : (1 : ℝ) ≤ √(Fintype.card n : ℝ) :=
    (by linarith : (1 : ℝ) ≤ √(Fintype.card l : ℝ)).trans
      (Real.sqrt_le_sqrt (Nat.cast_le.2 hl))
  set α := (√(Fintype.card l : ℝ) - √(Fintype.card p : ℝ) - t) ^ 2
  set β := (√(Fintype.card n : ℝ) + √(Fintype.card l : ℝ) + s) ^ 2
  have hβ : 0 < β := by positivity
  have hGU : HasLaw (fun G : Matrix n l ℝ => Gᴴ * U) (gaussianMatrix l p) (gaussianMatrix n l) :=
    hasLaw_mul_const_of_hasLaw_gaussianMatrix
      (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix HasLaw.id) hU
  have hA := measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix hGU
    ht htl
  have hB := measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix
    (HasLaw.id (μ := gaussianMatrix n l)) hs
  have hunit : ∀ᵐ G ∂gaussianMatrix n l, IsUnit (Gᴴ * G) := by
    have := ae_isUnit_conjTranspose_mul_self_mul_of_hasLaw_gaussianMatrix
      (A := (1 : Matrix n n ℝ)) (by rw [Matrix.rank_one]; exact hl)
      (HasLaw.id (μ := gaussianMatrix n l))
    simpa only [Matrix.one_mul, id] using this
  have hN : (gaussianMatrix n l).real {G | ¬ IsUnit (Gᴴ * G)} = 0 := by
    rw [Measure.real, ae_iff.1 hunit, ENNReal.toReal_zero]
  calc _ ≤ (gaussianMatrix n l).real (({G | ¬ α • (1 : Matrix p p ℝ) ≤ (Gᴴ * U)ᴴ * (Gᴴ * U)} ∪
        {G | ¬ (id G)ᴴ * id G ≤ β • (1 : Matrix l l ℝ)}) ∪ {G | ¬ IsUnit (Gᴴ * G)}) := by
        refine measureReal_mono (fun G hbad => ?_) (measure_ne_top _ _)
        by_contra hgood
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, id] at hgood
        obtain ⟨⟨h1, h2⟩, hG⟩ := hgood
        apply hbad
        have hpd : (Gᴴ * G).PosDef :=
          (Matrix.posSemidef_conjTranspose_mul_self G).posDef_iff_isUnit.2 hG
        have hinv : β⁻¹ • (1 : Matrix l l ℝ) ≤ (Gᴴ * G)⁻¹ := by
          have h := hpd.inv_le_inv_of_le h2
          have e : (β • (1 : Matrix l l ℝ))⁻¹ = β⁻¹ • (1 : Matrix l l ℝ) :=
            Matrix.inv_eq_right_inv (by
              rw [Matrix.smul_mul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hβ.ne', one_smul])
          rwa [e] at h
        rw [conjTranspose_mul_rangeProjector_mul_eq hG, div_eq_inv_mul, ← smul_smul]
        refine le_trans (smul_le_smul_loewner h1 (inv_nonneg.2 hβ.le)) ?_
        rw [← conjTranspose_mul_smul_one_mul]
        exact conjTranspose_mul_mul_le_conjTranspose_mul_mul hinv _
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by
        rw [hN, add_zero]
        exact (measureReal_union_le _ _).trans (add_le_add hA hB)

omit [Fintype k] [DecidableEq k] in
/-- **The Gaussian upper bound on `Uᴴ P_G U`**: for an `n × l` Gaussian `G`,
`Uᴴ P_G U ≤ (√l + √p + t)² / (√n - √l - s)² • 1` outside probability `e^{-t²/2} + e^{-s²/2}`, for
`t ≥ 0` and `0 ≤ s < √n - √l`: Gordon's upper tail for `Gᴴ U`, the lower tail of `Gᴴ G`, and the
inverse-Gram identity. -/
private theorem measureReal_not_conjTranspose_mul_rangeProjector_mul_le_smul_one_le
    (hU : HasOrthonormalCols U) {l : Type*} [Fintype l] (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hsl : s < √(Fintype.card n : ℝ) - √(Fintype.card l : ℝ)) :
    (gaussianMatrix n l).real {G | ¬ Uᴴ * rangeProjector G * U ≤
      ((√(Fintype.card l : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2 /
        (√(Fintype.card n : ℝ) - √(Fintype.card l : ℝ) - s) ^ 2) • (1 : Matrix p p ℝ)} ≤
      Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2) := by
  classical
  set b := (√(Fintype.card l : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2
  set γ := (√(Fintype.card n : ℝ) - √(Fintype.card l : ℝ) - s) ^ 2
  have hγ : 0 < γ := by
    have : 0 < √(Fintype.card n : ℝ) - √(Fintype.card l : ℝ) - s := by linarith
    positivity
  have hGU : HasLaw (fun G : Matrix n l ℝ => Gᴴ * U) (gaussianMatrix l p) (gaussianMatrix n l) :=
    hasLaw_mul_const_of_hasLaw_gaussianMatrix
      (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix HasLaw.id) hU
  have hA := measureReal_not_conjTranspose_mul_self_le_smul_one_le_of_hasLaw_gaussianMatrix hGU ht
  have hB := measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (HasLaw.id (μ := gaussianMatrix n l)) hs hsl.le
  calc _ ≤ (gaussianMatrix n l).real ({G | ¬ (Gᴴ * U)ᴴ * (Gᴴ * U) ≤ b • (1 : Matrix p p ℝ)} ∪
        {G | ¬ γ • (1 : Matrix l l ℝ) ≤ (id G)ᴴ * id G}) := by
        refine measureReal_mono (fun G hbad => ?_) (measure_ne_top _ _)
        by_contra hgood
        simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, id] at hgood
        obtain ⟨h1, h2⟩ := hgood
        apply hbad
        have hpd : (Gᴴ * G).PosDef := by
          have := (Matrix.PosDef.one.smul hγ).add_posSemidef (Matrix.le_iff.mp h2)
          rwa [add_sub_cancel] at this
        have hinv := inv_le_inv_smul_one_of_smul_one_le hγ h2
        rw [conjTranspose_mul_rangeProjector_mul_eq hpd.isUnit, div_eq_inv_mul, ← smul_smul]
        refine le_trans (conjTranspose_mul_mul_le_conjTranspose_mul_mul hinv _) ?_
        rw [conjTranspose_mul_smul_one_mul]
        exact smul_le_smul_loewner h1 (inv_nonneg.2 hγ.le)
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add hA hB)

omit [Fintype p] [DecidableEq p] in
/-- The failure event of the injection, transferred to a Gaussian `G`. -/
private theorem measureReal_not_isSubspaceInjection_eq [Finite p]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (a : ℝ) :
    μ.real {ω | ¬ IsSubspaceInjection (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U a} =
      (gaussianMatrix n k).real {G | ¬ a • (Uᴴ * U) ≤
        (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * rangeProjector G * U)} := by
  have := Fintype.ofFinite p
  have hT : MeasurableSet {M : Matrix p p ℝ | ¬ a • (Uᴴ * U) ≤ M} :=
    (isClosed_le continuous_const continuous_id).measurableSet.compl
  refine ((hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame hQ hk U).measureReal_eq
    (p := fun M => ¬ a • (Uᴴ * U) ≤ M) hT).trans ?_
  exact map_measureReal_apply (((measurable_const.matrix_mul measurable_rangeProjector).matrix_mul
    measurable_const).matrix_const_smul _) hT

omit [Fintype p] [DecidableEq p] in
/-- The failure event of an upper bound, transferred to a Gaussian `G`. -/
private theorem measureReal_not_le_smul_eq [Finite p] (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (b : ℝ) :
    μ.real {ω | ¬ (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U) ≤ b • (Uᴴ * U)} =
      (gaussianMatrix n k).real {G | ¬ (Fintype.card n / Fintype.card k : ℝ) •
        (Uᴴ * rangeProjector G * U) ≤ b • (Uᴴ * U)} := by
  have := Fintype.ofFinite p
  have hT : MeasurableSet {M : Matrix p p ℝ | ¬ M ≤ b • (Uᴴ * U)} :=
    (isClosed_le continuous_id continuous_const).measurableSet.compl
  rw [(hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame hQ hk U).measureReal_eq
    (p := fun M => ¬ M ≤ b • (Uᴴ * U)) hT]
  exact map_measureReal_apply (((measurable_const.matrix_mul measurable_rangeProjector).matrix_mul
    measurable_const).matrix_const_smul _) hT

/-- The lower constant in the two normalisations: `(b²/a²) (a - x)²/(b + y)² =
(1 - x/a)²/(1 + y/b)²`. -/
private theorem div_sq_mul_sub_sq_div_add_sq {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : 0 ≤ y) : b ^ 2 / a ^ 2 * ((a - x) ^ 2 / (b + y) ^ 2) =
      (1 - x / a) ^ 2 / (1 + y / b) ^ 2 := by
  have : b + y ≠ 0 := by linarith
  field_simp

/-- The upper constant in the two normalisations: `(b²/a²) (a + x)²/(b - y)² =
(1 + x/a)²/(1 - y/b)²` for `y < b`. -/
private theorem div_sq_mul_add_sq_div_sub_sq {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : y < b) : b ^ 2 / a ^ 2 * ((a + x) ^ 2 / (b - y) ^ 2) =
      (1 + x / a) ^ 2 / (1 - y / b) ^ 2 := by
  have : b - y ≠ 0 := by linarith
  field_simp

omit [DecidableEq k] [DecidableEq p] in
/-- With a nonempty `p` and `t ≤ √k - √p`, both `√k` and `√n` are positive. -/
private theorem sqrt_card_pos_of_le [Nonempty p] (hk : Fintype.card k ≤ Fintype.card n)
    (ht : 0 ≤ t) (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) :
    0 < √(Fintype.card k : ℝ) ∧ 0 < √(Fintype.card n : ℝ) := by
  have hp1 : (1 : ℝ) ≤ √(Fintype.card p : ℝ) :=
    Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have hK : 0 < √(Fintype.card k : ℝ) := by linarith
  exact ⟨hK, hK.trans_le (Real.sqrt_le_sqrt (Nat.cast_le.2 hk))⟩

/-- **Haar subspace injection**: for `U` with orthonormal columns, the Haar sketch is a subspace
injection for `range U` with constant `a_H = (1 - (√p + t)/√k)² / (1 + (√k + s)/√n)²` outside
probability `e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √p` and `s ≥ 0`. By the transfer and
`Uᴴ P_G U = (Gᴴ U)ᴴ (Gᴴ G)⁻¹ (Gᴴ U)` with `Gᴴ U` a `k × p` Gaussian: Gordon's lower tail for
`Gᴴ U` (`t`), the upper tail of `‖G‖` (`s`), a union bound (no independence needed). Lossy near
`k = n` (`a_H ≈ (1 - √(p/n))² / 4` there);
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq` is better
when the codimension is small, this one when `k ≤ n/2` (rule 4). -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame (hU : HasOrthonormalCols U)
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s) :
    HasSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  classical
  rcases isEmpty_or_nonempty p with hp | hp
  · exact hasSubspaceInjection_of_isEmpty (by positivity)
  obtain ⟨hK, hN⟩ := sqrt_card_pos_of_le hk ht htk
  have e := div_sq_mul_sub_sq_div_add_sq hK hN
    (x := √(Fintype.card p : ℝ) + t) (y := √(Fintype.card k : ℝ) + s) (by positivity)
  rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _), ← sub_sub,
    ← add_assoc] at e
  unfold HasSubspaceInjection
  rw [measureReal_not_isSubspaceInjection_eq hQ hk]
  refine (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)).trans
    (measureReal_not_smul_one_le_conjTranspose_mul_rangeProjector_mul_le hU hk ht htk hs)
  simp only [Set.mem_ofPred_eq] at hG ⊢
  intro hle
  apply hG
  rw [hU.conjTranspose_mul_self, ← e, ← smul_smul]
  exact smul_le_smul_loewner hle (by positivity)

/-- **Haar subspace embedding, deterministic upper half**: for `U` with orthonormal columns, the
lower constant `a_H` of `NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame` and
the upper constant `n/k`, outside probability `e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √p`
and `s ≥ 0`; no condition on `s` and `k < n` not needed. The upper half is
`NLAlib.ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`. Its upper constant is exact
at `k = n` and incomparable with the `b_H` of
`NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`, which
is better for `k` small against `n` (rule 4).
Result: haar-sketch-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame (hU : HasOrthonormalCols U)
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Fintype.card n / Fintype.card k : ℝ)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  have h := (hU.hasSubspaceInjection_of_hasLaw_haarFrame hQ hk ht htk hs).hasSubspaceEmbedding
    (b := (Fintype.card n / Fintype.card k : ℝ)) (δ' := 0) (le_of_eq ?_)
  · rwa [add_zero] at h
  · rw [Measure.real, ae_iff.1 (ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame hQ U),
      ENNReal.toReal_zero]

/-- **Haar subspace embedding, Gaussian upper half**: for `U` with orthonormal columns, constants
`a_H` and `b_H = (1 + (√p + t)/√k)² / (1 - (√k + s)/√n)²` outside probability
`2 e^{-t²/2} + 2 e^{-s²/2}`, for `0 ≤ t ≤ √k - √p` and `0 ≤ s < √n - √k`; four tails, two for
`Gᴴ U` and two for `G`, with `NLAlib.Matrix.PosDef.inv_le_inv_of_le` on `Gᴴ G`. Better than the
upper constant `n/k` of `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame` for
`k` small against `n`, worse near `k = n` (rule 4).
Result: haar-sketch-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt
    (hU : HasOrthonormalCols U) (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s)
    (hsk : s < √(Fintype.card n : ℝ) - √(Fintype.card k : ℝ)) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 - (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (2 * Real.exp (-t ^ 2 / 2) + 2 * Real.exp (-s ^ 2 / 2)) μ := by
  classical
  rcases isEmpty_or_nonempty p with hp | hp
  · exact hasSubspaceEmbedding_of_isEmpty (by positivity)
  obtain ⟨hK, hN⟩ := sqrt_card_pos_of_le hk ht htk
  have e := div_sq_mul_add_sq_div_sub_sq hK hN
    (x := √(Fintype.card p : ℝ) + t) (y := √(Fintype.card k : ℝ) + s) (by linarith)
  rw [Real.sq_sqrt (Nat.cast_nonneg _), Real.sq_sqrt (Nat.cast_nonneg _), ← add_assoc,
    ← sub_sub] at e
  have hup : μ.real {ω | ¬ (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
      (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U) ≤
      ((1 + (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 - (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2) • (Uᴴ * U)} ≤
      Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2) := by
    rw [measureReal_not_le_smul_eq hQ hk]
    refine (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)).trans
      (measureReal_not_conjTranspose_mul_rangeProjector_mul_le_smul_one_le hU ht hs hsk)
    simp only [Set.mem_ofPred_eq] at hG ⊢
    intro hle
    apply hG
    rw [hU.conjTranspose_mul_self, ← e, ← smul_smul]
    exact smul_le_smul_loewner hle (by positivity)
  have h := (hU.hasSubspaceInjection_of_hasLaw_haarFrame hQ hk ht htk hs).hasSubspaceEmbedding hup
  convert h using 1
  ring

omit [Fintype p] [DecidableEq p] in
/-- **Complementary coordinate frames**: for `card k + c = card n` there are frames `V₁ : n × k`
and `V₂ : n × c` with `V₁ V₁ᴴ + V₂ V₂ᴴ = 1` (selection matrices of a split of `n`). -/
private theorem exists_complementary_frames [DecidableEq n] {c : ℕ}
    (hc : Fintype.card k + c = Fintype.card n) :
    ∃ (V₁ : Matrix n k ℝ) (V₂ : Matrix n (Fin c) ℝ), HasOrthonormalCols V₁ ∧
      HasOrthonormalCols V₂ ∧ V₁ * V₁ᴴ + V₂ * V₂ᴴ = 1 := by
  classical
  obtain ⟨e⟩ : Nonempty (k ⊕ Fin c ≃ n) :=
    ⟨Fintype.equivOfCardEq (by rw [Fintype.card_sum, Fintype.card_fin, hc])⟩
  set V₁ : Matrix n k ℝ := selectionMatrix (e ∘ Sum.inl) with hV₁def
  set V₂ : Matrix n (Fin c) ℝ := selectionMatrix (e ∘ Sum.inr) with hV₂def
  have hV : HasOrthonormalCols (Matrix.fromCols V₁ V₂) := by
    have : Matrix.fromCols V₁ V₂ = selectionMatrix e := by
      ext i (j | j) <;> simp [hV₁def, hV₂def, selectionMatrix_apply]
    rw [this]
    exact hasOrthonormalCols_selectionMatrix e.injective
  exact ⟨V₁, V₂, hasOrthonormalCols_selectionMatrix (e.injective.comp Sum.inl_injective),
    hasOrthonormalCols_selectionMatrix (e.injective.comp Sum.inr_injective),
    hV.mul_conjTranspose_add_mul_conjTranspose (by rw [Fintype.card_fin, hc])⟩

omit [Fintype p] [DecidableEq p] in
/-- **The complement of a Haar frame**: an event on `Uᴴ Q Qᴴ U` for an `n × k` Haar frame `Q`
has the probability of the same event on `Uᴴ U - Uᴴ Q⊥ Q⊥ᴴ U` for an `n × c` Haar frame `Q⊥`,
`card k + c = card n`: `Q ~ P V₁` and `Q⊥ ~ P V₂` for a square Haar frame `P`, and
`P V₁ (P V₁)ᴴ = 1 - P V₂ (P V₂)ᴴ`. -/
private theorem measureReal_haarFrame_eq_complement [Finite p] {c : ℕ}
    (hc : Fintype.card k + c = Fintype.card n) {C : Matrix p p ℝ} {r : ℝ} :
    (haarFrame n k).real {M | ¬ C ≤ r • (Uᴴ * (M * Mᴴ) * U)} =
      (haarFrame n (Fin c)).real {M | ¬ C ≤ r • (Uᴴ * U - Uᴴ * (M * Mᴴ) * U)} := by
  classical
  have := Fintype.ofFinite p
  obtain ⟨V₁, V₂, hV₁, hV₂, hsum⟩ := exists_complementary_frames (k := k) hc
  have hc1 : Continuous fun M : Matrix n k ℝ => r • (Uᴴ * (M * Mᴴ) * U) := by fun_prop
  have hT1 : MeasurableSet {M : Matrix n k ℝ | ¬ C ≤ r • (Uᴴ * (M * Mᴴ) * U)} :=
    (isClosed_le continuous_const hc1).measurableSet.compl
  have hc2 : Continuous fun M : Matrix n (Fin c) ℝ => r • (Uᴴ * U - Uᴴ * (M * Mᴴ) * U) := by
    fun_prop
  have hT2 : MeasurableSet {M : Matrix n (Fin c) ℝ | ¬ C ≤ r • (Uᴴ * U - Uᴴ * (M * Mᴴ) * U)} :=
    (isClosed_le continuous_const hc2).measurableSet.compl
  rw [← (hasLaw_mul_const_of_hasLaw_haarFrame HasLaw.id le_rfl hV₁).measureReal_eq hT1,
    ← (hasLaw_mul_const_of_hasLaw_haarFrame HasLaw.id le_rfl hV₂).measureReal_eq hT2]
  refine measureReal_congr ?_
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame
    (HasLaw.id (μ := haarFrame n n)) le_rfl] with P hP
  have hP' : HasOrthonormalCols P := hP
  have hPP : P * V₁ * (P * V₁)ᴴ = 1 - P * V₂ * (P * V₂)ᴴ := by
    rw [eq_sub_iff_add_eq, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
    calc P * V₁ * (V₁ᴴ * Pᴴ) + P * V₂ * (V₂ᴴ * Pᴴ) = P * (V₁ * V₁ᴴ + V₂ * V₂ᴴ) * Pᴴ := by
          simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hsum, Matrix.mul_one, hP'.mul_conjTranspose_self]
  change (¬ C ≤ r • (Uᴴ * (P * V₁ * (P * V₁)ᴴ) * U)) =
    (¬ C ≤ r • (Uᴴ * U - Uᴴ * (P * V₂ * (P * V₂)ᴴ) * U))
  rw [hPP, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]

omit [Fintype k] [DecidableEq k] [Fintype p] [DecidableEq p] in
/-- An event on `Uᴴ Q Qᴴ U` for a Haar frame `Q` with `card l ≤ card n` has the probability of
the same event on `Uᴴ P_G U` for a Gaussian `G` (`Q Qᴴ` is the range projector of `Q`). -/
private theorem measureReal_haarFrame_eq_gaussianMatrix [Finite p] {l : Type*} [Fintype l]
    [DecidableEq l]
    (hl : Fintype.card l ≤ Fintype.card n) {C : Matrix p p ℝ} {r : ℝ} :
    (haarFrame n l).real {M | ¬ C ≤ r • (Uᴴ * U - Uᴴ * (M * Mᴴ) * U)} =
      (gaussianMatrix n l).real {G | ¬ C ≤ r • (Uᴴ * U - Uᴴ * rangeProjector G * U)} := by
  classical
  have := Fintype.ofFinite p
  have hR : HasLaw (fun M : Matrix n l ℝ => rangeProjector M)
      ((gaussianMatrix n l).map fun G => rangeProjector G) (haarFrame n l) := by
    simpa only [Matrix.one_mul, id] using
      hasLaw_rangeProjector_mul_of_hasLaw_haarFrame (1 : Matrix n n ℝ)
        (HasLaw.id (μ := haarFrame n l))
  have hc3 : Continuous fun P : Matrix n n ℝ => r • (Uᴴ * U - Uᴴ * P * U) := by fun_prop
  have hT3 : MeasurableSet {P : Matrix n n ℝ | ¬ C ≤ r • (Uᴴ * U - Uᴴ * P * U)} :=
    (isClosed_le continuous_const hc3).measurableSet.compl
  rw [show (gaussianMatrix n l).real {G | ¬ C ≤ r • (Uᴴ * U - Uᴴ * rangeProjector G * U)} =
      ((gaussianMatrix n l).map fun G => rangeProjector G).real
        {P | ¬ C ≤ r • (Uᴴ * U - Uᴴ * P * U)} from
    (map_measureReal_apply measurable_rangeProjector hT3).symm, ← hR.measureReal_eq hT3]
  refine measureReal_congr ?_
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame
    (HasLaw.id (μ := haarFrame n l)) hl] with M hM
  have hM' : HasOrthonormalCols M := hM
  change (¬ C ≤ r • (Uᴴ * U - Uᴴ * (M * Mᴴ) * U)) =
    (¬ C ≤ r • (Uᴴ * U - Uᴴ * rangeProjector M * U))
  rw [hM'.rangeProjector_eq]

/-- **Haar subspace injection near `k = n`**: with `c` the codimension, `card k + c = card n`,
and `U` with orthonormal columns, the Haar sketch is a subspace injection for `range U` with
constant `(n/k)(1 - (√c + √p + t)² / (√n - √c - s)²)` outside probability
`e^{-t²/2} + e^{-s²/2}`, for `t ≥ 0` and `0 ≤ s < √n - √c`. The complement route:
`Q ~ P V₁` and `Q⊥ := P V₂` for a square Haar frame `P` and the selection matrices of a split of
its columns (`NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`), `Uᴴ Q Qᴴ U = 1 - Uᴴ Q⊥ Q⊥ᴴ U`, and
the inverse-Gram step on the `n × c` Gaussian behind `Q⊥`. The constant tends to `1` as
`c / n → 0` and is vacuous for `k ≤ n/2`; incomparable with the `a_H` of
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame` (rule 4). -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq
    (hU : HasOrthonormalCols U) (hQ : HasLaw Q (haarFrame n k) μ) {c : ℕ}
    (hc : Fintype.card k + c = Fintype.card n) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hsc : s < √(Fintype.card n : ℝ) - √(c : ℝ)) :
    HasSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((Fintype.card n / Fintype.card k : ℝ) *
        (1 - (√(c : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2 /
          (√(Fintype.card n : ℝ) - √(c : ℝ) - s) ^ 2))
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  classical
  have hk : Fintype.card k ≤ Fintype.card n := hc ▸ Nat.le_add_right _ _
  set a := (Fintype.card n / Fintype.card k : ℝ) *
    (1 - (√(c : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2 / (√(Fintype.card n : ℝ) - √(c : ℝ) - s) ^ 2)
    with hadef
  set r := (Fintype.card n / Fintype.card k : ℝ) with hrdef
  have hr : 0 ≤ r := by positivity
  have hc1 : Continuous fun M : Matrix n k ℝ => r • (Uᴴ * (M * Mᴴ) * U) := by fun_prop
  have hT1 : MeasurableSet {M : Matrix n k ℝ | ¬ a • (Uᴴ * U) ≤ r • (Uᴴ * (M * Mᴴ) * U)} :=
    (isClosed_le continuous_const hc1).measurableSet.compl
  have h1 : μ.real {ω | ¬ IsSubspaceInjection (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ)
      U a} = (haarFrame n k).real {M | ¬ a • (Uᴴ * U) ≤ r • (Uᴴ * (M * Mᴴ) * U)} := by
    rw [← hQ.measureReal_eq hT1]
    simp only [IsSubspaceInjection, gram_smul_conjTranspose, hrdef]
  -- Step 4: the Gaussian upper bound on `Uᴴ P_G U`.
  have hup := measureReal_not_conjTranspose_mul_rangeProjector_mul_le_smul_one_le (l := Fin c)
    hU ht hs (by rwa [Fintype.card_fin])
  simp only [Fintype.card_fin] at hup
  unfold HasSubspaceInjection
  rw [h1, measureReal_haarFrame_eq_complement hc, measureReal_haarFrame_eq_gaussianMatrix
    (by rw [Fintype.card_fin, ← hc]; exact Nat.le_add_left _ _)]
  refine (measureReal_mono (fun G hG => ?_) (measure_ne_top _ _)).trans hup
  simp only [Set.mem_ofPred_eq] at hG ⊢
  intro hle
  apply hG
  rw [hU.conjTranspose_mul_self, hadef, ← smul_smul]
  refine smul_le_smul_loewner ?_ hr
  rw [Matrix.le_iff] at hle ⊢
  rw [sub_smul, one_smul]
  convert hle using 1
  abel

/-- **Haar subspace embedding near `k = n`**: the lower constant of
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq` and the
deterministic upper constant `n/k`, outside probability `e^{-t²/2} + e^{-s²/2}`, for `t ≥ 0`
and `0 ≤ s < √n - √c`, `c` the codimension. Both constants tend to `1` as `c / n → 0`.
Result: haar-sketch-ose -/
theorem HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq
    (hU : HasOrthonormalCols U) (hQ : HasLaw Q (haarFrame n k) μ) {c : ℕ}
    (hc : Fintype.card k + c = Fintype.card n) (ht : 0 ≤ t) (hs : 0 ≤ s)
    (hsc : s < √(Fintype.card n : ℝ) - √(c : ℝ)) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((Fintype.card n / Fintype.card k : ℝ) *
        (1 - (√(c : ℝ) + √(Fintype.card p : ℝ) + t) ^ 2 /
          (√(Fintype.card n : ℝ) - √(c : ℝ) - s) ^ 2))
      (Fintype.card n / Fintype.card k : ℝ)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  have h := (hU.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq hQ hc ht hs
    hsc).hasSubspaceEmbedding (b := (Fintype.card n / Fintype.card k : ℝ)) (δ' := 0) (le_of_eq ?_)
  · rwa [add_zero] at h
  · rw [Measure.real, ae_iff.1 (ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame hQ U),
      ENNReal.toReal_zero]

/-! ### Oblivious forms -/

omit [Fintype k] [DecidableEq k] [Fintype p] [DecidableEq p] in
/-- `(1 - (√d + t)/√k)²` is antitone in `d` while `√d + t ≤ √k`. -/
private theorem one_sub_div_sq_le {d d' : ℕ} (hdd : d' ≤ d) {K : ℝ}
    (htd : t ≤ √K - √(d : ℝ)) :
    (1 - (√(d : ℝ) + t) / √K) ^ 2 ≤ (1 - (√(d' : ℝ) + t) / √K) ^ 2 := by
  have hs : √(d' : ℝ) ≤ √(d : ℝ) := Real.sqrt_le_sqrt (Nat.cast_le.2 hdd)
  have h0 : (√(d : ℝ) + t) / √K ≤ 1 := by
    rcases (Real.sqrt_nonneg K).eq_or_lt with h | h
    · rw [← h, div_zero]
      exact zero_le_one
    · rw [div_le_one h]
      linarith
  have h1 : (√(d' : ℝ) + t) / √K ≤ (√(d : ℝ) + t) / √K :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg K)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

omit [Fintype k] [DecidableEq k] [Fintype p] [DecidableEq p] in
/-- `(1 + (√d + t)/√k)²` is monotone in `d`. -/
private theorem one_add_div_sq_le {d d' : ℕ} (hdd : d' ≤ d) (ht : 0 ≤ t) {K : ℝ} :
    (1 + (√(d' : ℝ) + t) / √K) ^ 2 ≤ (1 + (√(d : ℝ) + t) / √K) ^ 2 := by
  have hs : √(d' : ℝ) ≤ √(d : ℝ) := Real.sqrt_le_sqrt (Nat.cast_le.2 hdd)
  have h1 : (√(d' : ℝ) + t) / √K ≤ (√(d : ℝ) + t) / √K :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg K)
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **The Haar OSI**: the Haar sketch is an oblivious subspace injection for dimension `d` with
constant `(1 - (√d + t)/√k)² / (1 + (√k + s)/√n)²` and failure probability
`e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √d` and `s ≥ 0`.
Result: haar-sketch-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_haarFrame [DecidableEq n] [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ)
    (ht : 0 ≤ t) (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) (hs : 0 ≤ s) :
    IsObliviousSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  set d' := min d (Fintype.card n) with hd'
  have hdd : d' ≤ d := min_le_left _ _
  have htd' : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card (Fin d') : ℝ) := by
    rw [Fintype.card_fin]
    have := Real.sqrt_le_sqrt (Nat.cast_le (α := ℝ).2 hdd)
    linarith
  have h := IsObliviousSubspaceInjection.of_hasOrthonormalCols (p := Fin d')
    (isIsotropicSketch_of_hasLaw_haarFrame hQ hk) (by rw [Fintype.card_fin]; exact min_le_right _ _)
    fun V hV => hV.hasSubspaceInjection_of_hasLaw_haarFrame hQ hk ht htd' hs
  rw [Fintype.card_fin] at h
  refine ⟨h.isotropic, fun V hV => (h.injection V (le_min hV V.rank_le_card_width)).mono ?_ le_rfl⟩
  exact div_le_div_of_nonneg_right (one_sub_div_sq_le hdd htd) (sq_nonneg _)

/-- **The Haar OSE, deterministic upper half**: an oblivious subspace embedding for dimension
`d` with constants `(1 - (√d + t)/√k)² / (1 + (√k + s)/√n)²` and `n/k`, failure probability
`e^{-t²/2} + e^{-s²/2}`, for `0 ≤ t ≤ √k - √d` and `s ≥ 0`. Incomparable with
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt` (rule 4).
Result: haar-sketch-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ) (ht : 0 ≤ t)
    (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) (hs : 0 ≤ s) :
    IsObliviousSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Fintype.card n / Fintype.card k : ℝ)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  classical
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  set d' := min d (Fintype.card n) with hd'
  have hdd : d' ≤ d := min_le_left _ _
  have htd' : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card (Fin d') : ℝ) := by
    rw [Fintype.card_fin]
    have := Real.sqrt_le_sqrt (Nat.cast_le (α := ℝ).2 hdd)
    linarith
  have h := IsObliviousSubspaceEmbedding.of_hasOrthonormalCols (S := fun ω =>
    √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) (p := Fin d')
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
    fun V hV => hV.hasSubspaceEmbedding_of_hasLaw_haarFrame hQ hk ht htd' hs
  rw [Fintype.card_fin] at h
  refine fun V hV => (h V (le_min hV V.rank_le_card_width)).mono ?_ le_rfl le_rfl
  exact div_le_div_of_nonneg_right (one_sub_div_sq_le hdd htd) (sq_nonneg _)

/-- **The Haar OSE, Gaussian upper half**: an oblivious subspace embedding for dimension `d`
with constants `(1 ∓ (√d + t)/√k)² / (1 ± (√k + s)/√n)²` and failure probability
`2 e^{-t²/2} + 2 e^{-s²/2}`, for `0 ≤ t ≤ √k - √d` and `0 ≤ s < √n - √k`. Better than
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` for `k` small against `n` (rule 4).
Result: haar-sketch-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ)
    (ht : 0 ≤ t) (htd : t ≤ √(Fintype.card k : ℝ) - √(d : ℝ)) (hs : 0 ≤ s)
    (hsk : s < √(Fintype.card n : ℝ) - √(Fintype.card k : ℝ)) :
    IsObliviousSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) d
      ((1 - (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      ((1 + (√(d : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 - (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (2 * Real.exp (-t ^ 2 / 2) + 2 * Real.exp (-s ^ 2 / 2)) μ := by
  classical
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  set d' := min d (Fintype.card n) with hd'
  have hdd : d' ≤ d := min_le_left _ _
  have htd' : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card (Fin d') : ℝ) := by
    rw [Fintype.card_fin]
    have := Real.sqrt_le_sqrt (Nat.cast_le (α := ℝ).2 hdd)
    linarith
  have h := IsObliviousSubspaceEmbedding.of_hasOrthonormalCols (S := fun ω =>
    √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) (p := Fin d')
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
    fun V hV => hV.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt hQ hk ht htd' hs hsk
  rw [Fintype.card_fin] at h
  refine fun V hV => (h V (le_min hV V.rank_le_card_width)).mono ?_ ?_ le_rfl
  · exact div_le_div_of_nonneg_right (one_sub_div_sq_le hdd htd) (sq_nonneg _)
  · exact div_le_div_of_nonneg_right (one_add_div_sq_le hdd ht) (sq_nonneg _)

/-! ### Johnson–Lindenstrauss -/

omit [DecidableEq k] in
/-- `‖Qᴴ x‖ ≤ ‖x‖` almost surely, in every shape. -/
private theorem ae_norm_conjTranspose_mulVec_le [DecidableEq k] (hQ : HasLaw Q (haarFrame n k) μ)
    (x : n → ℝ) : ∀ᵐ ω ∂μ, ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ] with ω hω
  refine (norm_toLp_mulVec_le _ x).trans ?_
  rw [specNorm_conjTranspose]
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

/-- The powers of `‖Qᴴ x‖` are integrable (they are bounded by those of `‖x‖`). -/
private theorem integrable_norm_conjTranspose_mulVec_pow (hQ : HasLaw Q (haarFrame n k) μ)
    (x : n → ℝ) (m : ℕ) : Integrable (fun ω => ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ m) μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hc : Continuous fun M : Matrix n k ℝ => ‖WithLp.toLp 2 (Mᴴ *ᵥ x)‖ ^ m := by fun_prop
  refine Integrable.of_bound (hc.measurable.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable
    (‖WithLp.toLp 2 x‖ ^ m) ?_
  filter_upwards [ae_norm_conjTranspose_mulVec_le hQ x] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hω m

/-- **The fourth moment of `‖Qᴴ x‖`**: `E ‖Qᴴ x‖⁴ = ‖x‖⁴ k (k + 2) / (n (n + 2))`, from the law
of `Qᴴ x` and the fourth moment of a projected uniform unit vector. -/
private theorem integral_norm_conjTranspose_mulVec_pow_four [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (x : n → ℝ) :
    ∫ ω, ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 4 ∂μ = ‖WithLp.toLp 2 x‖ ^ 4 *
      (Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))) := by
  classical
  have : Nonempty n := by
    rw [← Fintype.card_pos_iff]
    exact Fintype.card_pos.trans_le hk
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0]
  set r := ‖WithLp.toLp 2 x‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  set y := r⁻¹ • x with hydef
  have hy : ‖WithLp.toLp 2 y‖ = 1 := by
    rw [hydef, WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hxy (M : Matrix n k ℝ) : ‖WithLp.toLp 2 (Mᴴ *ᵥ x)‖ ^ 4 =
      r ^ 4 * ‖WithLp.toLp 2 (Mᴴ *ᵥ y)‖ ^ 4 := by
    rw [hydef, Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, mul_pow,
      inv_pow, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  simp only [hxy]
  rw [integral_const_mul]
  congr 1
  obtain ⟨e⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  have hV := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) e.injective
  have hlaw := hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame hQ hV hy
  have hF : Continuous fun w : k → ℝ => ‖WithLp.toLp 2 w‖ ^ 4 := by fun_prop
  have h1 := hlaw.integral_comp hF.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  have hmv : Measurable fun v : n → ℝ => (selectionMatrix e : Matrix n k ℝ)ᴴ *ᵥ v :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [h1, integral_map hmv.aemeasurable hF.aestronglyMeasurable]
  exact integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector HasLaw.id hV

/-- **Distributional Johnson–Lindenstrauss for a Haar sketch**, with the Gaussian's constants:
`P(ε ≤ |‖S x‖² - 1|) ≤ 2 exp (-k (ε²/4 - ε³/6))` for every unit `x` and `ε ≥ 0`;
`‖S x‖² = (n/k) ‖Vᴴ u‖²` for `u` uniform on the sphere
(`NLAlib.hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame`) and the relative-deviation tail of
`NLAlib/RandomMatrix/Haar/Sphere.lean`. [Vershynin2018, Lemma 5.3.2 (2020 draft)], there with
an unspecified constant `c`; the exponent of Dasgupta and Gupta (2003). -/
theorem hasJLProperty_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  classical
  intro x hx
  obtain ⟨e⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  have hV := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) e.injective
  have hlaw := hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame hQ hV hx
  have hT : MeasurableSet {w : k → ℝ | ε ≤ |(Fintype.card n / Fintype.card k : ℝ) *
      ‖WithLp.toLp 2 w‖ ^ 2 - 1|} := measurableSet_le measurable_const (by fun_prop)
  have hmv : Measurable fun v : n → ℝ => (selectionMatrix e : Matrix n k ℝ)ᴴ *ᵥ v :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  simp only [norm_smul_conjTranspose_mulVec_sq]
  rw [hlaw.measureReal_eq (p := fun w => ε ≤ |(Fintype.card n / Fintype.card k : ℝ) *
      ‖WithLp.toLp 2 w‖ ^ 2 - 1|) hT, map_measureReal_apply hmv hT]
  exact
    measureReal_abs_div_mul_norm_conjTranspose_mulVec_sq_sub_one_ge_le_of_hasLaw_uniformSphereVector
      HasLaw.id hV hε

/-- The squared distortion `(‖S x‖² - ‖x‖²)²` of a Haar sketch is integrable (it is bounded). -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame n k) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2
      ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hc : Continuous fun M : Matrix n k ℝ => (‖WithLp.toLp 2
      ((√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ) *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 := by
    fun_prop
  refine Integrable.of_bound (hc.measurable.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable
    (((Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 x‖ ^ 2 +
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) ?_
  filter_upwards [ae_norm_conjTranspose_mulVec_le hQ x] with ω hω
  rw [norm_smul_conjTranspose_mulVec_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hr : (0 : ℝ) ≤ Fintype.card n / Fintype.card k := by positivity
  have h3 : (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2 ≤
      (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h2 hr
  have h4 : 0 ≤ (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2 := by
    positivity
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 ⟨by nlinarith [sq_nonneg ‖WithLp.toLp 2 x‖],
    by nlinarith [sq_nonneg ‖WithLp.toLp 2 x‖]⟩) 2

/-- **The JL variance of a Haar sketch**: `E (‖S x‖² - ‖x‖²)² = 2 (n - k) / (k (n + 2)) ‖x‖⁴`
exactly, below the Gaussian's `2 / k` and `0` at `k = n`; from `E ‖Vᴴ u‖² = k / n` and the
fourth moment `NLAlib.integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector`.
-/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
      2 * ((Fintype.card n : ℝ) - Fintype.card k) / (Fintype.card k * (Fintype.card n + 2)) *
        ‖WithLp.toLp 2 x‖ ^ 4 := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hN : (0 : ℝ) < Fintype.card n := hK.trans_le (Nat.cast_le.2 hk)
  have hexp (ω : Ω) : (‖WithLp.toLp 2 ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ
      x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 =
      (Fintype.card n / Fintype.card k : ℝ) ^ 2 * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 4 -
        2 * ‖WithLp.toLp 2 x‖ ^ 2 * ((Fintype.card n / Fintype.card k : ℝ) *
          ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2) + ‖WithLp.toLp 2 x‖ ^ 4 := by
    rw [norm_smul_conjTranspose_mulVec_sq]
    ring
  classical
  have hY := (isIsotropicSketch_of_hasLaw_haarFrame hQ hk).integral_norm_mulVec_sq x
  simp only [norm_smul_conjTranspose_mulVec_sq] at hY
  simp only [hexp]
  have i4 := integrable_norm_conjTranspose_mulVec_pow hQ x 4
  have i2 := integrable_norm_conjTranspose_mulVec_pow hQ x 2
  have hA : Integrable (fun ω => (Fintype.card n / Fintype.card k : ℝ) ^ 2 *
      ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 4 - 2 * ‖WithLp.toLp 2 x‖ ^ 2 *
        ((Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2)) μ :=
    (i4.const_mul _).sub ((i2.const_mul _).const_mul _)
  rw [integral_add hA (integrable_const _),
    integral_sub (i4.const_mul _) ((i2.const_mul _).const_mul _), integral_const_mul,
    integral_const_mul, hY, integral_const, probReal_univ, one_smul,
    integral_norm_conjTranspose_mulVec_pow_four hQ hk]
  field_simp
  ring

/-- **The JL moment property of a Haar sketch** at `p = 2`, with
`δ = 2 (n - k) / (k (n + 2) ε²)`, from the exact variance. [Woodruff2014, Definition 12], the
property there. -/
theorem hasJLMoment_of_hasLaw_haarFrame [Nonempty k] (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε) :
    HasJLMoment (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε
      (2 * ((Fintype.card n : ℝ) - Fintype.card k) /
        (Fintype.card k * (Fintype.card n + 2) * ε ^ 2)) 2 μ := by
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h := integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame hQ x
    rw [hx, one_pow] at h
    simpa only [Real.rpow_two, sq_abs] using h
  · have h := integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame hQ hk x
    rw [hx, one_pow, one_pow, mul_one] at h
    simp only [Real.rpow_two, sq_abs]
    rw [h]
    apply le_of_eq
    field_simp

/-- **Haar distributional JL, sample-size form**: `k ≥ jlDim ε δ` rows give the JL property with
distortion `ε` and failure probability `δ`, for `0 < ε < 3/2` and `δ > 0`. -/
theorem hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ)
    (hk' : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε δ μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  refine (hasJLProperty_of_hasLaw_haarFrame hQ hk hε.le).mono le_rfl ?_
  have hD : 0 < ε ^ 2 / 4 - ε ^ 3 / 6 := by
    have : ε ^ 2 / 4 - ε ^ 3 / 6 = ε ^ 2 * (3 - 2 * ε) / 12 := by ring
    rw [this]
    exact div_pos (mul_pos (by positivity) (by linarith)) (by norm_num)
  rw [jlDim_def, div_le_iff₀ hD] at hk'
  have h2 : Real.log (2 / δ) = -Real.log (δ / 2) := by
    rw [← Real.log_inv, inv_div]
  have : Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6))) ≤ δ / 2 := by
    rw [← Real.exp_log (by positivity : 0 < δ / 2)]
    exact Real.exp_le_exp.2 (by linarith)
  linarith

end NLAlib
