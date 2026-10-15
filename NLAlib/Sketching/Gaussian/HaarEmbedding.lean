/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Sketching.Gaussian.Haar

/-!
# Haar sketches as subspace embeddings

Fixed-subspace and oblivious subspace embeddings for the Haar sketch
$\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert} \, \mathbf{Q}^{\mathsf{H}}$ of
`NLAlib/Sketching/Gaussian/Haar.lean`. The Gram matrix of $\mathbf{S}$ on $\mathbf{U}$ has the law
of $(\lvert n \rvert / \lvert k \rvert) \, \mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}}
\mathbf{U}$ for an $n \times k$ Gaussian $\mathbf{G}$
(`NLAlib.hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame`); the inverse-Gram identity
$$\mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}
= (\mathbf{G}^{\mathsf{H}}\mathbf{U})^{\mathsf{H}} (\mathbf{G}^{\mathsf{H}}\mathbf{G})^{-1}
(\mathbf{G}^{\mathsf{H}}\mathbf{U})$$
and Gordon's tails then give the lower constant
$$a_{\mathrm{H}} = \frac{(1 - (\sqrt{\lvert p \rvert} + t)/\sqrt{\lvert k \rvert})^2}
{(1 + (\sqrt{\lvert k \rvert} + s)/\sqrt{\lvert n \rvert})^2} \,,$$
with a tail in $t$ for the subspace and one in $s$ for the frame, and the upper constant
$$b_{\mathrm{H}} = \frac{(1 + (\sqrt{\lvert p \rvert} + t)/\sqrt{\lvert k \rvert})^2}
{(1 - (\sqrt{\lvert k \rvert} + s)/\sqrt{\lvert n \rvert})^2}$$
for $s < \sqrt{\lvert n \rvert} - \sqrt{\lvert k \rvert}$. Both are lossy near
$\lvert k \rvert = \lvert n \rvert$; there the complement route is sharp: with $c$ the codimension
($\lvert k \rvert + c = \lvert n \rvert$), $\mathbf{Q} \sim \mathbf{P}\mathbf{V}_1$ and
$\mathbf{Q}_{\perp} := \mathbf{P}\mathbf{V}_2$ for a square Haar frame $\mathbf{P}$,
$\mathbf{U}^{\mathsf{H}}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{U} = \mathbf{I} -
\mathbf{U}^{\mathsf{H}}\mathbf{Q}_{\perp}\mathbf{Q}_{\perp}^{\mathsf{H}}\mathbf{U}$, and the
inverse-Gram step on the $n \times c$ Gaussian behind $\mathbf{Q}_{\perp}$ gives
$$a = \frac{\lvert n \rvert}{\lvert k \rvert}
\Bigl(1 - \frac{(\sqrt{c} + \sqrt{\lvert p \rvert} + t)^2}
{(\sqrt{\lvert n \rvert} - \sqrt{c} - s)^2}\Bigr) \,,$$
which tends to $1$ as $c / \lvert n \rvert \to 0$. The upper half
$(\lvert n \rvert / \lvert k \rvert) \, \mathbf{U}^{\mathsf{H}}\mathbf{U}$ holds almost surely
(`NLAlib.ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`).

Degenerate cases: for empty $p$ every event is null; for empty $k$ the sketch is $\mathbf{0}$,
hence `[Nonempty k]` on the OSI. Split from `NLAlib/Sketching/Gaussian/Haar.lean` at the
Sketching wrap-up (2026-10-15). Design: `docs/design/Sketching-S2.md` §3.4, §8.

## Main results

* `NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame`: the lower constant
  $a_{\mathrm{H}}$.
* `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame`,
  `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`,
  `NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq`: three
  incomparable fixed-subspace embeddings.
* `NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame`,
  `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame`,
  `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n p : Type*} [Fintype k]
  [Fintype n] [Fintype p] [DecidableEq k] {Q : Ω → Matrix n k ℝ} {U : Matrix n p ℝ}
  {t s ε δ : ℝ}

omit [Fintype k] [DecidableEq k] [Fintype p] in
/-- The inverse-Gram identity $\mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}
= (\mathbf{G}^{\mathsf{H}}\mathbf{U})^{\mathsf{H}} (\mathbf{G}^{\mathsf{H}}\mathbf{G})^{-1}
(\mathbf{G}^{\mathsf{H}}\mathbf{U})$ for invertible $\mathbf{G}^{\mathsf{H}}\mathbf{G}$. -/
private theorem conjTranspose_mul_rangeProjector_mul_eq {l : Type*} [Fintype l] [DecidableEq l]
    {G : Matrix n l ℝ} (hG : IsUnit (Gᴴ * G)) (U : Matrix n p ℝ) :
    Uᴴ * rangeProjector G * U = (Gᴴ * U)ᴴ * (Gᴴ * G)⁻¹ * (Gᴴ * U) := by
  rw [rangeProjector_eq_mul_inv_mul_conjTranspose hG, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  simp only [Matrix.mul_assoc]

/-! ### A fixed subspace -/

variable [DecidableEq p]

omit [Fintype k] [DecidableEq k] [Fintype p] [DecidableEq p] in
/-- $\mathbf{X}^{\mathsf{H}} (c \, \mathbf{I}) \mathbf{X} = c \, \mathbf{X}^{\mathsf{H}}\mathbf{X}$.
-/
private theorem conjTranspose_mul_smul_one_mul {l : Type*} [Fintype l] [DecidableEq l]
    (X : Matrix l p ℝ) (c : ℝ) : Xᴴ * (c • (1 : Matrix l l ℝ)) * X = c • (Xᴴ * X) := by
  rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]

omit [Fintype k] [DecidableEq k] in
/-- **The Gaussian lower bound on $\mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}$**:
for an $n \times l$ Gaussian $\mathbf{G}$, $\lvert l \rvert \le \lvert n \rvert$,
$$\frac{(\sqrt{\lvert l \rvert} - \sqrt{\lvert p \rvert} - t)^2}
{(\sqrt{\lvert n \rvert} + \sqrt{\lvert l \rvert} + s)^2} \, \mathbf{I}
\preceq \mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}$$
outside probability $e^{-t^2/2} + e^{-s^2/2}$: Gordon's lower tail for the $l \times p$ Gaussian
$\mathbf{G}^{\mathsf{H}}\mathbf{U}$, the upper tail of $\mathbf{G}^{\mathsf{H}}\mathbf{G}$, and the
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
        refine le_trans (smul_le_smul_of_nonneg_left h1 (inv_nonneg.2 hβ.le)) ?_
        rw [← conjTranspose_mul_smul_one_mul]
        exact conjTranspose_mul_mul_le_conjTranspose_mul_mul hinv _
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := by
        rw [hN, add_zero]
        exact (measureReal_union_le _ _).trans (add_le_add hA hB)

omit [Fintype k] [DecidableEq k] in
/-- **The Gaussian upper bound on $\mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}$**:
for an $n \times l$ Gaussian $\mathbf{G}$,
$$\mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}
\preceq \frac{(\sqrt{\lvert l \rvert} + \sqrt{\lvert p \rvert} + t)^2}
{(\sqrt{\lvert n \rvert} - \sqrt{\lvert l \rvert} - s)^2} \, \mathbf{I}$$
outside probability $e^{-t^2/2} + e^{-s^2/2}$, for $t \ge 0$ and
$0 \le s < \sqrt{\lvert n \rvert} - \sqrt{\lvert l \rvert}$: Gordon's upper tail for
$\mathbf{G}^{\mathsf{H}}\mathbf{U}$, the lower tail of $\mathbf{G}^{\mathsf{H}}\mathbf{G}$, and the
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
        exact smul_le_smul_of_nonneg_left h1 (inv_nonneg.2 hγ.le)
    _ ≤ _ := (measureReal_union_le _ _).trans (add_le_add hA hB)

omit [Fintype p] [DecidableEq p] in
/-- The failure event of the injection, transferred to a Gaussian $\mathbf{G}$. -/
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
/-- The failure event of an upper bound, transferred to a Gaussian $\mathbf{G}$. -/
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

/-- The lower constant in the two normalisations:
$(b^2/a^2) (a - x)^2/(b + y)^2 = (1 - x/a)^2/(1 + y/b)^2$. -/
private theorem div_sq_mul_sub_sq_div_add_sq {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : 0 ≤ y) : b ^ 2 / a ^ 2 * ((a - x) ^ 2 / (b + y) ^ 2) =
      (1 - x / a) ^ 2 / (1 + y / b) ^ 2 := by
  have : b + y ≠ 0 := by linarith
  field_simp

/-- The upper constant in the two normalisations:
$(b^2/a^2) (a + x)^2/(b - y)^2 = (1 + x/a)^2/(1 - y/b)^2$ for $y < b$. -/
private theorem div_sq_mul_add_sq_div_sub_sq {a b x y : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hy : y < b) : b ^ 2 / a ^ 2 * ((a + x) ^ 2 / (b - y) ^ 2) =
      (1 + x / a) ^ 2 / (1 - y / b) ^ 2 := by
  have : b - y ≠ 0 := by linarith
  field_simp

omit [DecidableEq k] [DecidableEq p] in
/-- With a nonempty $p$ and $t \le \sqrt{\lvert k \rvert} - \sqrt{\lvert p \rvert}$, both
$\sqrt{\lvert k \rvert}$ and $\sqrt{\lvert n \rvert}$ are positive. -/
private theorem sqrt_card_pos_of_le [Nonempty p] (hk : Fintype.card k ≤ Fintype.card n)
    (ht : 0 ≤ t) (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) :
    0 < √(Fintype.card k : ℝ) ∧ 0 < √(Fintype.card n : ℝ) := by
  have hp1 : (1 : ℝ) ≤ √(Fintype.card p : ℝ) :=
    Real.one_le_sqrt.2 (Nat.one_le_cast.2 Fintype.card_pos)
  have hK : 0 < √(Fintype.card k : ℝ) := by linarith
  exact ⟨hK, hK.trans_le (Real.sqrt_le_sqrt (Nat.cast_le.2 hk))⟩

/-- **Haar subspace injection**: for $\mathbf{U}$ with orthonormal columns, the Haar sketch is a
subspace injection for $\operatorname{range} \mathbf{U}$ with constant
$$a_{\mathrm{H}} = \frac{(1 - (\sqrt{\lvert p \rvert} + t)/\sqrt{\lvert k \rvert})^2}
{(1 + (\sqrt{\lvert k \rvert} + s)/\sqrt{\lvert n \rvert})^2}$$
outside probability $e^{-t^2/2} + e^{-s^2/2}$, for
$0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{\lvert p \rvert}$ and $s \ge 0$. By the transfer and
$\mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}
= (\mathbf{G}^{\mathsf{H}}\mathbf{U})^{\mathsf{H}} (\mathbf{G}^{\mathsf{H}}\mathbf{G})^{-1}
(\mathbf{G}^{\mathsf{H}}\mathbf{U})$ with $\mathbf{G}^{\mathsf{H}}\mathbf{U}$ a $k \times p$
Gaussian: Gordon's lower tail for $\mathbf{G}^{\mathsf{H}}\mathbf{U}$ ($t$), the upper tail of
$\|\mathbf{G}\|_2$ ($s$), a union bound (no independence needed). Lossy near
$\lvert k \rvert = \lvert n \rvert$ ($a_{\mathrm{H}} \approx (1 -
\sqrt{\lvert p \rvert / \lvert n \rvert})^2 / 4$ there);
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq` is better when
the codimension is small, this one when $\lvert k \rvert \le \lvert n \rvert / 2$ (rule 4). -/
theorem HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame (hU : HasOrthonormalCols U)
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (ht : 0 ≤ t)
    (htk : t ≤ √(Fintype.card k : ℝ) - √(Fintype.card p : ℝ)) (hs : 0 ≤ s) :
    HasSubspaceInjection (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U
      ((1 - (√(Fintype.card p : ℝ) + t) / √(Fintype.card k : ℝ)) ^ 2 /
        (1 + (√(Fintype.card k : ℝ) + s) / √(Fintype.card n : ℝ)) ^ 2)
      (Real.exp (-t ^ 2 / 2) + Real.exp (-s ^ 2 / 2)) μ := by
  classical
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  rcases isEmpty_or_nonempty p with hp | hp
  · exact (hasSubspaceEmbedding_of_rank_eq_zero (b := 0)
      (Matrix.rank_eq_zero.2 (Matrix.ext fun _ j => isEmptyElim j))
      (by positivity)).hasSubspaceInjection
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
  exact smul_le_smul_of_nonneg_left hle (by positivity)

/-- **Haar subspace embedding, deterministic upper half**: for $\mathbf{U}$ with orthonormal
columns, the lower constant $a_{\mathrm{H}}$ of
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame` and the upper constant
$\lvert n \rvert / \lvert k \rvert$, outside probability $e^{-t^2/2} + e^{-s^2/2}$, for
$0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{\lvert p \rvert}$ and $s \ge 0$; no condition on $s$ and
$\lvert k \rvert < \lvert n \rvert$ not needed. The upper half is
`NLAlib.ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`. Its upper constant is exact at
$\lvert k \rvert = \lvert n \rvert$ and incomparable with the $b_{\mathrm{H}}$ of
`NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_lt_sqrt_sub_sqrt`, which is
better for $\lvert k \rvert$ small against $\lvert n \rvert$ (rule 4).
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

/-- **Haar subspace embedding, Gaussian upper half**: for $\mathbf{U}$ with orthonormal columns,
constants $a_{\mathrm{H}}$ and
$$b_{\mathrm{H}} = \frac{(1 + (\sqrt{\lvert p \rvert} + t)/\sqrt{\lvert k \rvert})^2}
{(1 - (\sqrt{\lvert k \rvert} + s)/\sqrt{\lvert n \rvert})^2}$$
outside probability $2 e^{-t^2/2} + 2 e^{-s^2/2}$, for
$0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{\lvert p \rvert}$ and
$0 \le s < \sqrt{\lvert n \rvert} - \sqrt{\lvert k \rvert}$; four tails, two for
$\mathbf{G}^{\mathsf{H}}\mathbf{U}$ and two for $\mathbf{G}$, with
`NLAlib.Matrix.PosDef.inv_le_inv_of_le` on $\mathbf{G}^{\mathsf{H}}\mathbf{G}$. Better than the
upper constant $\lvert n \rvert / \lvert k \rvert$ of
`NLAlib.HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame` for $\lvert k \rvert$ small
against $\lvert n \rvert$, worse near $\lvert k \rvert = \lvert n \rvert$ (rule 4).
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
  · exact hasSubspaceEmbedding_of_rank_eq_zero
      (Matrix.rank_eq_zero.2 (Matrix.ext fun _ j => isEmptyElim j)) (by positivity)
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
    exact smul_le_smul_of_nonneg_left hle (by positivity)
  have h := (hU.hasSubspaceInjection_of_hasLaw_haarFrame hQ hk ht htk hs).hasSubspaceEmbedding hup
  convert h using 1
  ring

omit [Fintype p] [DecidableEq p] in
/-- **Complementary coordinate frames**: for $\lvert k \rvert + c = \lvert n \rvert$ there are
frames $\mathbf{V}_1$ ($n \times k$) and $\mathbf{V}_2$ ($n \times c$) with
$\mathbf{V}_1\mathbf{V}_1^{\mathsf{H}} + \mathbf{V}_2\mathbf{V}_2^{\mathsf{H}} = \mathbf{I}$
(selection matrices of a split of $n$). -/
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
/-- **The complement of a Haar frame**: an event on
$\mathbf{U}^{\mathsf{H}}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{U}$ for an $n \times k$ Haar frame
$\mathbf{Q}$ has the probability of the same event on $\mathbf{U}^{\mathsf{H}}\mathbf{U} -
\mathbf{U}^{\mathsf{H}}\mathbf{Q}_{\perp}\mathbf{Q}_{\perp}^{\mathsf{H}}\mathbf{U}$ for an
$n \times c$ Haar frame $\mathbf{Q}_{\perp}$, $\lvert k \rvert + c = \lvert n \rvert$:
$\mathbf{Q} \sim \mathbf{P}\mathbf{V}_1$ and $\mathbf{Q}_{\perp} \sim \mathbf{P}\mathbf{V}_2$ for a
square Haar frame $\mathbf{P}$, and $\mathbf{P}\mathbf{V}_1 (\mathbf{P}\mathbf{V}_1)^{\mathsf{H}}
= \mathbf{I} - \mathbf{P}\mathbf{V}_2 (\mathbf{P}\mathbf{V}_2)^{\mathsf{H}}$. -/
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
/-- An event on $\mathbf{U}^{\mathsf{H}}\mathbf{U} -
\mathbf{U}^{\mathsf{H}}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{U}$ for an $n \times l$ Haar frame
$\mathbf{Q}$ with $\lvert l \rvert \le \lvert n \rvert$ has the probability of the same event on
$\mathbf{U}^{\mathsf{H}}\mathbf{U} - \mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}$ for
a Gaussian $\mathbf{G}$ ($\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ is the range projector of
$\mathbf{Q}$). -/
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

/-- **Haar subspace injection near $\lvert k \rvert = \lvert n \rvert$**: with $c$ the codimension,
$\lvert k \rvert + c = \lvert n \rvert$, and $\mathbf{U}$ with orthonormal columns, the Haar sketch
is a subspace injection for $\operatorname{range} \mathbf{U}$ with constant
$$\frac{\lvert n \rvert}{\lvert k \rvert} \Bigl(1 - \frac{(\sqrt{c} + \sqrt{\lvert p \rvert} + t)^2}
{(\sqrt{\lvert n \rvert} - \sqrt{c} - s)^2}\Bigr)$$
outside probability $e^{-t^2/2} + e^{-s^2/2}$, for $t \ge 0$ and
$0 \le s < \sqrt{\lvert n \rvert} - \sqrt{c}$. The complement route:
$\mathbf{Q} \sim \mathbf{P}\mathbf{V}_1$ and $\mathbf{Q}_{\perp} := \mathbf{P}\mathbf{V}_2$ for a
square Haar frame $\mathbf{P}$ and the selection matrices of a split of its columns
(`NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`),
$\mathbf{U}^{\mathsf{H}}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{U} = \mathbf{I} -
\mathbf{U}^{\mathsf{H}}\mathbf{Q}_{\perp}\mathbf{Q}_{\perp}^{\mathsf{H}}\mathbf{U}$, and the
inverse-Gram step on the $n \times c$ Gaussian behind $\mathbf{Q}_{\perp}$. The constant tends to
$1$ as $c / \lvert n \rvert \to 0$ and is vacuous for $\lvert k \rvert \le \lvert n \rvert / 2$;
incomparable with the $a_{\mathrm{H}}$ of
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
    simp only [IsSubspaceInjection, conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul,
      hrdef]
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
  refine smul_le_smul_of_nonneg_left ?_ hr
  rw [Matrix.le_iff] at hle ⊢
  rw [sub_smul, one_smul]
  convert hle using 1
  abel

/-- **Haar subspace embedding near $\lvert k \rvert = \lvert n \rvert$**: the lower constant of
`NLAlib.HasOrthonormalCols.hasSubspaceInjection_of_hasLaw_haarFrame_of_card_add_eq` and the
deterministic upper constant $\lvert n \rvert / \lvert k \rvert$, outside probability
$e^{-t^2/2} + e^{-s^2/2}$, for $t \ge 0$ and $0 \le s < \sqrt{\lvert n \rvert} - \sqrt{c}$, $c$ the
codimension. Both constants tend to $1$ as $c / \lvert n \rvert \to 0$.
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
/-- $(1 - (\sqrt{d} + t)/\sqrt{K})^2$ is antitone in $d$ while $\sqrt{d} + t \le \sqrt{K}$. -/
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
/-- $(1 + (\sqrt{d} + t)/\sqrt{K})^2$ is monotone in $d$, for $t \ge 0$. -/
private theorem one_add_div_sq_le {d d' : ℕ} (hdd : d' ≤ d) (ht : 0 ≤ t) {K : ℝ} :
    (1 + (√(d' : ℝ) + t) / √K) ^ 2 ≤ (1 + (√(d : ℝ) + t) / √K) ^ 2 := by
  have hs : √(d' : ℝ) ≤ √(d : ℝ) := Real.sqrt_le_sqrt (Nat.cast_le.2 hdd)
  have h1 : (√(d' : ℝ) + t) / √K ≤ (√(d : ℝ) + t) / √K :=
    div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg K)
  exact pow_le_pow_left₀ (by positivity) (by linarith) 2

/-- **The Haar OSI**: the Haar sketch is an oblivious subspace injection for dimension $d$ with
constant
$$\frac{(1 - (\sqrt{d} + t)/\sqrt{\lvert k \rvert})^2}
{(1 + (\sqrt{\lvert k \rvert} + s)/\sqrt{\lvert n \rvert})^2}$$
and failure probability $e^{-t^2/2} + e^{-s^2/2}$, for
$0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{d}$ and $s \ge 0$.
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

/-- **The Haar OSE, deterministic upper half**: an oblivious subspace embedding for dimension $d$
with constants
$$\frac{(1 - (\sqrt{d} + t)/\sqrt{\lvert k \rvert})^2}
{(1 + (\sqrt{\lvert k \rvert} + s)/\sqrt{\lvert n \rvert})^2}
\quad \text{and} \quad \frac{\lvert n \rvert}{\lvert k \rvert} \,,$$
failure probability $e^{-t^2/2} + e^{-s^2/2}$, for $0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{d}$
and $s \ge 0$. Incomparable with
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

/-- **The Haar OSE, Gaussian upper half**: an oblivious subspace embedding for dimension $d$ with
constants
$$\frac{(1 \mp (\sqrt{d} + t)/\sqrt{\lvert k \rvert})^2}
{(1 \pm (\sqrt{\lvert k \rvert} + s)/\sqrt{\lvert n \rvert})^2}$$
and failure probability $2 e^{-t^2/2} + 2 e^{-s^2/2}$, for
$0 \le t \le \sqrt{\lvert k \rvert} - \sqrt{d}$ and
$0 \le s < \sqrt{\lvert n \rvert} - \sqrt{\lvert k \rvert}$. Better than
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` for $\lvert k \rvert$ small against
$\lvert n \rvert$ (rule 4).
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

end NLAlib
