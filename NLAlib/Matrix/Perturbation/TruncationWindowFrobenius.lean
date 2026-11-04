/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.TruncationWindow

/-!
# Frobenius control outside a singular-value window

The reciprocal-window bound retains the misalignment energy and the rank-deficit term.
The full singular frame completes the chosen SVD, so ties preserve the chosen truncations.
Design: docs/design/research/Nystrom-Constants.md.

## Main results

* `NLAlib.frobNorm_sub_mul_mul_sq_le_of_one_lt`: the reciprocal-window estimate.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
private theorem sum_norm_sub_diagonal_apply_sq
    {Z : Matrix n n 𝕜} (hZ : IsStarProjection Z) (p : n → Prop)
    [DecidablePred p] (i : n) :
    (∑ j, ‖(Z - Matrix.diagonal (fun j => if p j then (1 : 𝕜) else 0)) i j‖ ^ 2) =
      if p i then 1 - RCLike.re (Z i i) else RCLike.re (Z i i) := by
  let P : Matrix n n 𝕜 := Matrix.diagonal (fun j => if p j then 1 else 0)
  have hP : IsStarProjection P := by
    rw [Matrix.isStarProjection_iff]
    refine ⟨?_, Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext j; simp)⟩
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases hp : p j <;> simp [hp]
  have hΔ := hZ.isHermitian.sub hP.isHermitian
  change (∑ j, ‖(Z - P) i j‖ ^ 2) = _
  rw [hΔ.sum_norm_apply_sq_eq_re_mul_self_apply]
  have hsquare : (Z - P) * (Z - P) = Z + P - Z * P - P * Z := by
    rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hZ.mul_self, hP.mul_self]
    abel
  rw [hsquare]
  by_cases hp : p i
  · rw [if_pos hp]
    calc RCLike.re ((Z + P - Z * P - P * Z) i i)
        = RCLike.re (Z i i) + 1 - RCLike.re (Z i i) - RCLike.re (Z i i) := by
          simp [P, hp, map_sub]
      _ = 1 - RCLike.re (Z i i) := by ring
  · rw [if_neg hp]
    simp [P, hp]
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq r]
private theorem rangeProjector_truncatedSVD_eq_fromCols_diagonal_mul
    {p : Type*} [Fintype p] [DecidableEq p] (B : Matrix m n 𝕜) (U' : Matrix m p 𝕜) (k : ℕ) :
    rangeProjector (truncatedSVD B k) =
      Matrix.fromCols (svdU B) U' *
        Matrix.diagonal (Sum.elim
          (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
            if (i : ℕ) < k ∧ singularValues B i ≠ 0 then (1 : 𝕜) else 0)
          (fun _ => 0)) * (Matrix.fromCols (svdU B) U')ᴴ := by
  have h := isSVD_svdU_svdV B
  let s : Fin (min (Fintype.card m) (Fintype.card n)) → 𝕜 :=
    fun i => if (i : ℕ) < k then ((singularValues B i : ℝ) : 𝕜) else 0
  let e : Fin (min (Fintype.card m) (Fintype.card n)) → 𝕜 :=
    fun i => if (i : ℕ) < k ∧ singularValues B i ≠ 0 then 1 else 0
  have he : (fun i => if s i = 0 then (0 : 𝕜) else 1) = e := by
    funext i
    by_cases hi : (i : ℕ) < k <;> by_cases hσ : singularValues B i = 0 <;>
      simp [s, e, hi, hσ]
  have hP : rangeProjector (truncatedSVD B k) =
      svdU B * Matrix.diagonal e * (svdU B)ᴴ := by
    rw [truncatedSVD_def, Matrix.mul_assoc, h.hasOrthonormalCols_left.rangeProjector_mul,
      h.hasOrthonormalCols_right.rangeProjector_diagonal_mul_conjTranspose, he]
  rw [hP, ← Matrix.fromBlocks_diagonal, Matrix.diagonal_zero,
    Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose,
    Matrix.fromCols_mul_fromBlocks, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rfl
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
private theorem frobNorm_projection_mul_diagonal_sq_eq
    {P : Matrix n n 𝕜} (hP : IsStarProjection P) (d : n → ℝ) :
    frobNorm (P * Matrix.diagonal (fun i => (d i : 𝕜))) ^ 2 =
      ∑ i, d i ^ 2 * RCLike.re (P i i) := by
  let D : Matrix n n 𝕜 := Matrix.diagonal (fun i => (d i : 𝕜))
  have hgram : (P * D)ᴴ * (P * D) = D * P * D := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_diagonal_ofReal, hP.conjTranspose_eq]
    calc D * P * (P * D) = (D * (P * P)) * D := by simp only [Matrix.mul_assoc]
      _ = D * P * D := by rw [hP.mul_self]
  rw [frobNorm_sq_eq_re_trace, hgram]
  simp only [D, Matrix.trace, Matrix.diag, Matrix.mul_diagonal, Matrix.diagonal_mul, map_sum,
    RCLike.re_mul_ofReal, RCLike.re_ofReal_mul]
  exact Finset.sum_congr rfl fun i _ => by ring
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
private theorem sum_abs_mul_sum_norm_sub_diagonal_sq_le
    {Z : Matrix n n 𝕜} (hZ : IsStarProjection Z) (p : n → Prop)
    [DecidablePred p] (d : n → ℝ) {θ : ℝ} (hθ : 0 ≤ θ)
    (hd : ∀ i, 0 ≤ d i) (hhead : ∀ i, p i → θ ≤ d i)
    (htail : ∀ i, ¬ p i → d i ≤ θ)
    (hgap0 : 0 ≤ θ ^ 2 *
      (frobNorm (Matrix.diagonal (fun i => if p i then (1 : 𝕜) else 0)) ^ 2 -
        frobNorm Z ^ 2)) :
    (∑ i, |d i ^ 2 - θ ^ 2| *
      ∑ j, ‖(Z - Matrix.diagonal (fun j => if p j then (1 : 𝕜) else 0)) i j‖ ^ 2) ≤
      frobNorm ((1 - Z) * Matrix.diagonal (fun i => (d i : 𝕜))) ^ 2 -
        frobNorm ((1 - Matrix.diagonal (fun i => if p i then (1 : 𝕜) else 0)) *
          Matrix.diagonal (fun i => (d i : 𝕜))) ^ 2 := by
  let P : Matrix n n 𝕜 := Matrix.diagonal (fun i => if p i then 1 else 0)
  let e : n → ℝ := fun i => if p i then 1 else 0
  have hP : IsStarProjection P := by
    rw [Matrix.isStarProjection_iff]
    refine ⟨?_, Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext j; simp)⟩
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    by_cases hp : p j <;> simp [hp]
  have hreP (i : n) : RCLike.re (P i i) = e i := by
    by_cases hp : p i <;> simp [P, e, hp]
  have htraceZ : (∑ i, RCLike.re (Z i i)) = frobNorm Z ^ 2 := by
    have h := (frobNorm_projection_mul_diagonal_sq_eq hZ (fun _ => 1)).symm
    simpa only [RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one, one_pow, one_mul] using h
  have htraceP : (∑ i, e i) = frobNorm P ^ 2 := by
    have h := (frobNorm_projection_mul_diagonal_sq_eq hP (fun _ => 1)).symm
    simpa only [RCLike.ofReal_one, Matrix.diagonal_one, Matrix.mul_one, one_pow, one_mul,
      hreP] using h
  have hgap : 0 ≤ θ ^ 2 * ∑ i, (e i - RCLike.re (Z i i)) := by
    rw [Finset.sum_sub_distrib, htraceP, htraceZ]
    exact hgap0
  have hW : (∑ i, |d i ^ 2 - θ ^ 2| *
      ∑ j, ‖(Z - P) i j‖ ^ 2) =
      ∑ i, (d i ^ 2 - θ ^ 2) * (e i - RCLike.re (Z i i)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [sum_norm_sub_diagonal_apply_sq hZ p i]
    by_cases hp : p i
    · have hs := pow_le_pow_left₀ hθ (hhead i hp) 2
      rw [if_pos hp, abs_of_nonneg (sub_nonneg.mpr hs)]
      simp only [e, if_pos hp]
    · have hs := pow_le_pow_left₀ (hd i) (htail i hp) 2
      rw [if_neg hp, abs_of_nonpos (sub_nonpos.mpr hs)]
      simp only [e, if_neg hp]
      ring
  have hD : frobNorm ((1 - Z) * Matrix.diagonal (fun i => (d i : 𝕜))) ^ 2 -
      frobNorm ((1 - P) * Matrix.diagonal (fun i => (d i : 𝕜))) ^ 2 =
      ∑ i, d i ^ 2 * (e i - RCLike.re (Z i i)) := by
    rw [frobNorm_projection_mul_diagonal_sq_eq hZ.one_sub,
      frobNorm_projection_mul_diagonal_sq_eq hP.one_sub, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Matrix.sub_apply, Matrix.one_apply_eq, map_sub, RCLike.one_re, hreP]
    ring
  change (∑ i, |d i ^ 2 - θ ^ 2| * ∑ j, ‖(Z - P) i j‖ ^ 2) ≤ _
  rw [hW, hD]
  have heq : (∑ i, d i ^ 2 * (e i - RCLike.re (Z i i))) -
      (∑ i, (d i ^ 2 - θ ^ 2) * (e i - RCLike.re (Z i i))) =
      θ ^ 2 * ∑ i, (e i - RCLike.re (Z i i)) := by
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith [hgap]
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
private theorem mul_add_le_mul_abs_sub_add_abs_sub
    {r x y t : ℝ} (hr : 1 < r) (hx0 : 0 ≤ x) (ht : 0 ≤ t)
    (hx : r * x ≤ t ∨ r * t ≤ x) :
    (r - 1) * (x + y) ≤ (r + 1) * (|x - t| + |y - t|) := by
  have hr0 : 0 ≤ r := by linarith
  rcases hx with hx | hx
  · have hxt : x ≤ t := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.le) hx0]
    rw [abs_of_nonpos (sub_nonpos.mpr hxt)]
    rcases le_total y t with hyt | hty
    · rw [abs_of_nonpos (sub_nonpos.mpr hyt)]
      nlinarith [mul_le_mul_of_nonneg_left hyt hr0]
    · rw [abs_of_nonneg (sub_nonneg.mpr hty)]
      nlinarith
  · have htx : t ≤ x := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hr.le) ht]
    rw [abs_of_nonneg (sub_nonneg.mpr htx)]
    rcases le_total y t with hyt | hty
    · rw [abs_of_nonpos (sub_nonpos.mpr hyt)]
      nlinarith [mul_le_mul_of_nonneg_left hyt hr0]
    · rw [abs_of_nonneg (sub_nonneg.mpr hty)]
      nlinarith

private theorem frobNorm_sub_diagonal_mul_mul_diagonal_mul_diagonal_sq_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (p : n → Prop) [DecidablePred p]
    (d : n → ℝ) {θ c : ℝ} (hθ : 0 ≤ θ) (hc : 1 < c)
    (hd : ∀ i, 0 ≤ d i)
    (hout : ∀ i, ¬ p i → c * d i ≤ θ ∨ c * θ ≤ d i) :
    frobNorm ((A - Matrix.diagonal (fun i => if p i then (1 : 𝕜) else 0) * A *
        Matrix.diagonal (fun i => if p i then (1 : 𝕜) else 0)) *
      Matrix.diagonal (fun i => (d i : 𝕜))) ^ 2 ≤
      ((c ^ 2 + 1) / (c ^ 2 - 1)) *
        ∑ i, |d i ^ 2 - θ ^ 2| * ∑ j, ‖A i j‖ ^ 2 := by
  have hc0 : 0 ≤ c := by linarith
  have hc2 : 1 < c ^ 2 := by nlinarith
  have hden : 0 < c ^ 2 - 1 := by linarith
  let W : Matrix n n 𝕜 := Matrix.diagonal (fun i => if p i then 1 else 0)
  let K : Matrix n n 𝕜 := A - W * A * W
  let e : n → ℝ := fun i => ((c ^ 2 + 1) / (c ^ 2 - 1)) * |d i ^ 2 - θ ^ 2|
  have hW : W.IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hK : K.IsHermitian := hA.sub (by
    simpa only [hW.eq] using Matrix.isHermitian_conjTranspose_mul_mul W hA)
  have hKij (i j : n) : K i j = if p i ∧ p j then 0 else A i j := by
    simp only [K, W, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    by_cases hi : p i <;> by_cases hj : p j <;> simp [hi, hj]
  have hscalar (i j : n) (hi : ¬ p i) :
      (c ^ 2 - 1) * (d i ^ 2 + d j ^ 2) ≤
        (c ^ 2 + 1) * (|d i ^ 2 - θ ^ 2| + |d j ^ 2 - θ ^ 2|) := by
    apply mul_add_le_mul_abs_sub_add_abs_sub hc2 (sq_nonneg _) (sq_nonneg _)
    rcases hout i hi with hi | hi
    · left
      simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hc0 (hd i)) hi 2
    · right
      simpa only [mul_pow] using pow_le_pow_left₀ (mul_nonneg hc0 hθ) hi 2
  have hde (i j : n) (hij : K i j ≠ 0) : d i ^ 2 + d j ^ 2 ≤ e i + e j := by
    have hnot : ¬ (p i ∧ p j) := by
      intro hp
      exact hij (by rw [hKij, if_pos hp])
    have hpair : (c ^ 2 - 1) * (d i ^ 2 + d j ^ 2) ≤
        (c ^ 2 + 1) * (|d i ^ 2 - θ ^ 2| + |d j ^ 2 - θ ^ 2|) := by
      by_cases hi : p i
      · simpa only [add_comm] using hscalar j i (fun hj => hnot ⟨hi, hj⟩)
      · exact hscalar i j hi
    dsimp only [e]
    rw [← mul_add, div_mul_eq_mul_div, le_div_iff₀ hden]
    simpa only [mul_comm] using hpair
  have hrow (i : n) : (∑ j, ‖K i j‖ ^ 2) ≤ ∑ j, ‖A i j‖ ^ 2 := by
    refine Finset.sum_le_sum fun j _ => ?_
    rw [hKij]
    split_ifs
    · simpa only [norm_zero, zero_pow two_ne_zero] using sq_nonneg ‖A i j‖
    · exact le_rfl
  calc frobNorm (K * Matrix.diagonal (fun i => (d i : 𝕜))) ^ 2
      ≤ ∑ i, e i * ∑ j, ‖K i j‖ ^ 2 :=
        hK.frobNorm_mul_diagonal_sq_le_sum d e hde
    _ ≤ ∑ i, e i * ∑ j, ‖A i j‖ ^ 2 := by
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrow i) ?_
      exact mul_nonneg (div_nonneg (by positivity) hden.le) (abs_nonneg _)
    _ = _ := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by dsimp only [e]; ring
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m r : Type*}
  [Fintype m] [Fintype r] [DecidableEq m] [DecidableEq r]
private theorem hasOrthonormalCols_conjTranspose_of_card_eq
    {Q : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card r = Fintype.card m) : HasOrthonormalCols Qᴴ := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose,
    hQ.mul_conjTranspose_self_of_card_eq hcard.symm]
omit [DecidableEq m] in
private theorem frobNorm_conjTranspose_mul_mul_eq
    {Q : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card r = Fintype.card m) (X : Matrix m m 𝕜) :
    frobNorm (Qᴴ * X * Q) = frobNorm X := by
  classical
  have hQH := hasOrthonormalCols_conjTranspose_of_card_eq hQ hcard
  simpa only [Matrix.conjTranspose_conjTranspose] using
    (hQH.frobNorm_mul_conjTranspose_right (Qᴴ * X)).trans (hQH.frobNorm_mul_left X)
omit [DecidableEq m] in
private theorem conjTranspose_mul_mul_mul_of_card_eq
    {Q : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card r = Fintype.card m) (X Y : Matrix m m 𝕜) :
    Qᴴ * (X * Y) * Q = (Qᴴ * X * Q) * (Qᴴ * Y * Q) := by
  classical
  have hQQ := hQ.mul_conjTranspose_self_of_card_eq hcard.symm
  symm
  calc (Qᴴ * X * Q) * (Qᴴ * Y * Q) = Qᴴ * X * (Q * Qᴴ) * Y * Q := by
        simp only [Matrix.mul_assoc]
    _ = Qᴴ * (X * Y) * Q := by
      rw [hQQ, Matrix.mul_one]
      simp only [Matrix.mul_assoc]
omit [DecidableEq m] in
private theorem isStarProjection_conjTranspose_mul_mul_of_card_eq
    {Q : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card r = Fintype.card m)
    {Z : Matrix m m 𝕜} (hZ : IsStarProjection Z) :
    IsStarProjection (Qᴴ * Z * Q) := by
  classical
  rw [Matrix.isStarProjection_iff]
  refine ⟨?_, Matrix.isHermitian_conjTranspose_mul_mul Q hZ.isHermitian⟩
  rw [← conjTranspose_mul_mul_mul_of_card_eq hQ hcard, hZ.mul_self]
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n r : Type*}
  [Fintype m] [Fintype n] [Fintype r] [DecidableEq m] [DecidableEq r]
private theorem frobNorm_sub_mul_mul_sq_le_of_diagonalization
    (B : Matrix m n 𝕜) {Q : Matrix m r 𝕜} (hQ : HasOrthonormalCols Q)
    (hcard : Fintype.card r = Fintype.card m) (d : r → ℝ)
    (hG : B * Bᴴ * Q = Q * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : 𝕜)))
    (p w : r → Prop) [DecidablePred p] [DecidablePred w]
    {P L Z : Matrix m m 𝕜} (hZ : IsStarProjection Z)
    (hP : P = Q * Matrix.diagonal (fun i => if p i then (1 : 𝕜) else 0) * Qᴴ)
    (hL : L = Q * Matrix.diagonal (fun i => if w i then (1 : 𝕜) else 0) * Qᴴ)
    {θ c : ℝ} (hθ : 0 ≤ θ) (hc : 1 < c)
    (hd : ∀ i, 0 ≤ d i) (hhead : ∀ i, p i → θ ≤ d i)
    (htail : ∀ i, ¬ p i → d i ≤ θ)
    (hout : ∀ i, ¬ w i → c * d i ≤ θ ∨ c * θ ≤ d i)
    (hgap : 0 ≤ θ ^ 2 * (frobNorm P ^ 2 - frobNorm Z ^ 2)) :
    frobNorm (((Z - P) - L * (Z - P) * L) * B) ^ 2 ≤
      ((c ^ 2 + 1) / (c ^ 2 - 1)) *
        (frobNorm ((1 - Z) * B) ^ 2 - frobNorm ((1 - P) * B) ^ 2) := by
  let C : Matrix m m 𝕜 → Matrix r r 𝕜 := fun X => Qᴴ * X * Q
  let D : Matrix r r 𝕜 := Matrix.diagonal (fun i => (d i : 𝕜))
  let DP : Matrix r r 𝕜 := Matrix.diagonal (fun i => if p i then 1 else 0)
  let DW : Matrix r r 𝕜 := Matrix.diagonal (fun i => if w i then 1 else 0)
  let Z' := C Z
  have hCmul (X Y : Matrix m m 𝕜) : C (X * Y) = C X * C Y :=
    conjTranspose_mul_mul_mul_of_card_eq hQ hcard X Y
  have hCsub (X Y : Matrix m m 𝕜) : C (X - Y) = C X - C Y := by
    simp only [C, Matrix.mul_sub, Matrix.sub_mul]
  have hC1 : C 1 = 1 := by simp only [C, Matrix.mul_one, hQ.conjTranspose_mul_self]
  have hCP : C P = DP := by
    dsimp only [C]
    rw [hP, Matrix.mul_assoc Q _ Qᴴ, hQ.conjTranspose_mul_cancel_left,
      hQ.mul_conjTranspose_mul_cancel_right]
  have hCL : C L = DW := by
    dsimp only [C]
    rw [hL, Matrix.mul_assoc Q _ Qᴴ, hQ.conjTranspose_mul_cancel_left,
      hQ.mul_conjTranspose_mul_cancel_right]
  have hZ' : IsStarProjection Z' := isStarProjection_conjTranspose_mul_mul_of_card_eq hQ hcard hZ
  have hDP : DP.IsHermitian :=
    Matrix.isHermitian_diagonal_of_self_adjoint _ (by ext i; simp)
  have hQH := hasOrthonormalCols_conjTranspose_of_card_eq hQ hcard
  have hN (X : Matrix m m 𝕜) :
      frobNorm (X * B) ^ 2 = frobNorm (C X * D) ^ 2 := by
    rw [hQ.frobNorm_mul_sq_eq_mul_mul_diagonal_sq hcard B d hG]
    simpa only [C, D, Matrix.mul_assoc] using
      congrArg (fun x : ℝ => x ^ 2) (hQH.frobNorm_mul_left (X * Q * D)).symm
  have hPnorm : frobNorm P = frobNorm DP := by
    rw [hP, hQ.frobNorm_mul_conjTranspose_right, hQ.frobNorm_mul_left]
  have hZnorm : frobNorm Z' = frobNorm Z :=
    frobNorm_conjTranspose_mul_mul_eq hQ hcard Z
  have hgap' : 0 ≤ θ ^ 2 * (frobNorm DP ^ 2 - frobNorm Z' ^ 2) := by
    rw [← hPnorm, hZnorm]
    exact hgap
  have hR : C ((Z - P) - L * (Z - P) * L) =
      (Z' - DP) - DW * (Z' - DP) * DW := by
    rw [hCsub, hCmul, hCmul, hCsub, hCP, hCL]
  have hMask := frobNorm_sub_diagonal_mul_mul_diagonal_mul_diagonal_sq_le
    (hZ'.isHermitian.sub hDP) w d hθ hc hd hout
  have hEnergy := sum_abs_mul_sum_norm_sub_diagonal_sq_le hZ' p d hθ hd hhead htail hgap'
  have hpos : 0 ≤ (c ^ 2 + 1) / (c ^ 2 - 1) :=
    div_nonneg (by positivity) (by nlinarith)
  calc frobNorm (((Z - P) - L * (Z - P) * L) * B) ^ 2
      = frobNorm (C ((Z - P) - L * (Z - P) * L) * D) ^ 2 := hN _
    _ = frobNorm (((Z' - DP) - DW * (Z' - DP) * DW) * D) ^ 2 := by rw [hR]
    _ ≤ ((c ^ 2 + 1) / (c ^ 2 - 1)) *
        (frobNorm ((1 - Z') * D) ^ 2 - frobNorm ((1 - DP) * D) ^ 2) :=
      hMask.trans (mul_le_mul_of_nonneg_left hEnergy hpos)
    _ = _ := by
      rw [hN (1 - Z), hN (1 - P), hCsub, hCsub, hC1, hCP]
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
private theorem singularValues_window_coordinate_properties
    {t : Type*} (B : Matrix m n 𝕜) {k a b : ℕ} {c : ℝ} (hc : 1 < c)
    (ha : ∀ i < a, c * singularValues B (k - 1) ≤ singularValues B i)
    (hb : singularValues B b ≤ singularValues B (k - 1) / c) :
    let J := Fin (min (Fintype.card m) (Fintype.card n)) ⊕ t
    let d : J → ℝ := Sum.elim (fun i => singularValues B i) (fun _ => 0)
    let p : J → Prop := Sum.elim
      (fun i => (i : ℕ) < k ∧ singularValues B i ≠ 0) (fun _ => False)
    let w : J → Prop := Sum.elim
      (fun i => a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ singularValues B i ≠ 0) (fun _ => False)
    let θ := singularValues B (k - 1)
    (∀ i, 0 ≤ d i) ∧ (∀ i, p i → θ ≤ d i) ∧ (∀ i, ¬ p i → d i ≤ θ) ∧
      (∀ i, ¬ w i → c * d i ≤ θ ∨ c * θ ≤ d i) := by
  classical
  let J := Fin (min (Fintype.card m) (Fintype.card n)) ⊕ t
  let d : J → ℝ := Sum.elim (fun i => singularValues B i) (fun _ => 0)
  let p : ℕ → J → Prop := fun l => Sum.elim
    (fun i => (i : ℕ) < l ∧ singularValues B i ≠ 0) (fun _ => False)
  let w : J → Prop := Sum.elim
    (fun i => a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ singularValues B i ≠ 0) (fun _ => False)
  let θ := singularValues B (k - 1)
  have hd (i : J) : 0 ≤ d i := by
    cases i with
    | inl i => exact singularValues_nonneg B i
    | inr i => exact le_rfl
  have hhead (i : J) (hi : p k i) : θ ≤ d i := by
    cases i with
    | inl i =>
      change (i : ℕ) < k ∧ singularValues B i ≠ 0 at hi
      exact singularValues_antitone B (by omega)
    | inr i => exact False.elim hi
  have htail (i : J) (hi : ¬ p k i) : d i ≤ θ := by
    cases i with
    | inl i =>
      change ¬ ((i : ℕ) < k ∧ singularValues B i ≠ 0) at hi
      by_cases hσ : singularValues B i = 0
      · change singularValues B i ≤ θ
        rw [hσ]
        exact singularValues_nonneg B (k - 1)
      · have hki : k ≤ (i : ℕ) := by
          by_contra hki
          exact hi ⟨by omega, hσ⟩
        exact singularValues_antitone B (by omega)
    | inr i => exact singularValues_nonneg B (k - 1)
  have hout (i : J) (hi : ¬ w i) : c * d i ≤ θ ∨ c * θ ≤ d i := by
    cases i with
    | inl i =>
      change ¬ (a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ singularValues B i ≠ 0) at hi
      by_cases hσ : singularValues B i = 0
      · left
        change c * singularValues B i ≤ θ
        rw [hσ, mul_zero]
        exact singularValues_nonneg B (k - 1)
      · by_cases hia : (i : ℕ) < a
        · exact Or.inr (ha i hia)
        · have hbi : b ≤ (i : ℕ) := by
            by_contra hbi
            exact hi ⟨by omega, by omega, hσ⟩
          left
          simpa only [d, Sum.elim_inl, θ, mul_comm] using (le_div_iff₀ (lt_trans zero_lt_one hc)).mp
            ((singularValues_antitone B hbi).trans hb)
    | inr i =>
      left
      change c * 0 ≤ θ
      simpa only [mul_zero] using singularValues_nonneg B (k - 1)
  exact ⟨hd, hhead, htail, hout⟩
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
open scoped Classical in
private theorem rangeProjector_truncatedSVD_eq_fromCols_diagonal_ite
    {t : Type*} [Fintype t] [DecidableEq t] (B : Matrix m n 𝕜) (U' : Matrix m t 𝕜) (k : ℕ) :
    rangeProjector (truncatedSVD B k) = Matrix.fromCols (svdU B) U' *
      Matrix.diagonal (fun j : Fin (min (Fintype.card m) (Fintype.card n)) ⊕ t =>
        if Sum.elim
          (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
            (i : ℕ) < k ∧ singularValues B i ≠ 0) (fun _ => False) j
        then (1 : 𝕜) else 0) * (Matrix.fromCols (svdU B) U')ᴴ := by
  classical
  have hE : Matrix.diagonal
      (fun j : Fin (min (Fintype.card m) (Fintype.card n)) ⊕ t =>
        if Sum.elim
          (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
            (i : ℕ) < k ∧ singularValues B i ≠ 0) (fun _ => False) j
        then (1 : 𝕜) else 0) = Matrix.diagonal (Sum.elim
      (fun i : Fin (min (Fintype.card m) (Fintype.card n)) =>
        if (i : ℕ) < k ∧ singularValues B i ≠ 0 then (1 : 𝕜) else 0) (fun _ : t => 0)) := by
    congr 1
    funext j
    cases j with
    | inl j =>
      by_cases hj : (j : ℕ) < k ∧ singularValues B j ≠ 0 <;> simp [hj]
    | inr j => simp
  rw [hE]
  exact rangeProjector_truncatedSVD_eq_fromCols_diagonal_mul B U' k

open scoped Classical in
private theorem diagonal_sum_prefix_sub_eq
    {t : Type*} [DecidableEq t] {μ : ℕ}
    (s : Fin μ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    Matrix.diagonal (fun j : Fin μ ⊕ t =>
      if Sum.elim (fun i : Fin μ => (i : ℕ) < b ∧ s i ≠ 0) (fun _ => False) j
      then (1 : 𝕜) else 0) -
    Matrix.diagonal (fun j : Fin μ ⊕ t =>
      if Sum.elim (fun i : Fin μ => (i : ℕ) < a ∧ s i ≠ 0) (fun _ => False) j
      then (1 : 𝕜) else 0) =
    Matrix.diagonal (fun j : Fin μ ⊕ t =>
      if Sum.elim (fun i : Fin μ => a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ s i ≠ 0) (fun _ => False) j
      then (1 : 𝕜) else 0) := by
  classical
  rw [Matrix.diagonal_sub]
  congr 1
  funext j
  cases j with
  | inl j =>
    by_cases hja : (j : ℕ) < a
    · have hjb : (j : ℕ) < b := lt_of_lt_of_le hja hab
      by_cases hs : s j = 0 <;> simp [hja, hjb, hs, Nat.not_le.mpr hja]
    · have haj : a ≤ (j : ℕ) := Nat.le_of_not_gt hja
      by_cases hjb : (j : ℕ) < b <;> by_cases hs : s j = 0 <;>
        simp [hja, hjb, haj, hs]
  | inr j => simp
end NLAlib


namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]
/-- For a matrix $\mathbf{B}$, $k \ge 1$, $c>1$ and $a \le k \le b$, put
$\theta=\sigma_{k-1}(\mathbf{B})$. Assume $c\theta\le\sigma_i(\mathbf{B})$ for $i<a$ and
$\sigma_b(\mathbf{B})\le\theta/c$. For any orthogonal projector of rank at most $k$, the
off-window squared Frobenius energy is at most $(c^2+1)/(c^2-1)$ times the projection excess.
Both window projectors come from the chosen truncations of the same SVD. Zero thresholds,
ties and rank deficiency are allowed. No printed source. -/
theorem frobNorm_sub_mul_mul_sq_le_of_one_lt (B : Matrix m n 𝕜) {k : ℕ}
    (hk : 1 ≤ k) {c : ℝ} (hc : 1 < c) {a b : ℕ} (hak : a ≤ k) (hkb : k ≤ b)
    (ha : ∀ i < a, c * singularValues B (k - 1) ≤ singularValues B i)
    (hb : singularValues B b ≤ singularValues B (k - 1) / c)
    {Z : Matrix m m 𝕜} (hZ : IsStarProjection Z) (hZk : Z.rank ≤ k) :
    frobNorm ((Z - rangeProjector (truncatedSVD B k)) * B -
        (rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)) *
          (Z - rangeProjector (truncatedSVD B k)) * B *
          (rangeProjector ((truncatedSVD B b)ᴴ) -
            rangeProjector ((truncatedSVD B a)ᴴ))) ^ 2 ≤
      ((c ^ 2 + 1) / (c ^ 2 - 1)) *
        (frobNorm ((1 - Z) * B) ^ 2 -
          frobNorm ((1 - rangeProjector (truncatedSVD B k)) * B) ^ 2) := by
  classical
  let μ := min (Fintype.card m) (Fintype.card n)
  let t := Fin (Fintype.card m - μ)
  let J := Fin μ ⊕ t
  have hdim : Fintype.card (Fin μ) + Fintype.card t = Fintype.card m := by
    simp only [t, Fintype.card_fin]
    have : μ ≤ Fintype.card m := min_le_left _ _
    omega
  have h := isSVD_svdU_svdV B
  obtain ⟨U', hQ, hG⟩ :=
    h.exists_fromCols_mul_conjTranspose_self_mul_eq_mul_diagonal (p := t) hdim
  let Q : Matrix m J 𝕜 := Matrix.fromCols (svdU B) U'
  let d : J → ℝ := Sum.elim (fun i => singularValues B i) (fun _ => 0)
  let p : ℕ → J → Prop := fun l => Sum.elim
    (fun i => (i : ℕ) < l ∧ singularValues B i ≠ 0) (fun _ => False)
  let w : J → Prop := Sum.elim
    (fun i => a ≤ (i : ℕ) ∧ (i : ℕ) < b ∧ singularValues B i ≠ 0) (fun _ => False)
  let E : ℕ → Matrix J J 𝕜 := fun l => Matrix.diagonal (fun i => if p l i then 1 else 0)
  let W : Matrix J J 𝕜 := Matrix.diagonal (fun i => if w i then 1 else 0)
  let P := rangeProjector (truncatedSVD B k)
  let L := rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a)
  let L' := rangeProjector ((truncatedSVD B b)ᴴ) - rangeProjector ((truncatedSVD B a)ᴴ)
  have hcard : Fintype.card J = Fintype.card m := by rw [Fintype.card_sum]; exact hdim
  have hweights : (fun i : J => ((d i ^ 2 : ℝ) : 𝕜)) =
      Sum.elim (fun i : Fin μ => ((singularValues B i ^ 2 : ℝ) : 𝕜)) (fun _ : t => 0) := by
    funext i
    cases i <;> simp [d]
  have hG' : B * Bᴴ * Q = Q * Matrix.diagonal (fun i => ((d i ^ 2 : ℝ) : 𝕜)) := by
    rw [hweights]
    exact hG
  have hPi (l : ℕ) : rangeProjector (truncatedSVD B l) = Q * E l * Qᴴ :=
    rangeProjector_truncatedSVD_eq_fromCols_diagonal_ite B U' l
  have hL : L = Q * W * Qᴴ := by
    change rangeProjector (truncatedSVD B b) - rangeProjector (truncatedSVD B a) = _
    rw [hPi b, hPi a, ← Matrix.sub_mul, ← Matrix.mul_sub]
    congr 2
    exact diagonal_sum_prefix_sub_eq (𝕜 := 𝕜) (t := t)
      (fun i : Fin μ => singularValues B i) a b (hak.trans hkb)
  obtain ⟨hd, hhead, htail, hout⟩ :=
    singularValues_window_coordinate_properties (t := t) B hc ha hb
  have hBL : B * L' = L * B := by
    simp only [L, L', Matrix.mul_sub, Matrix.sub_mul,
      mul_rangeProjector_conjTranspose_truncatedSVD, rangeProjector_truncatedSVD_mul]
  have hR : (Z - P) * B - L * (Z - P) * B * L' =
      ((Z - P) - L * (Z - P) * L) * B := by
    calc (Z - P) * B - L * (Z - P) * B * L' =
        (Z - P) * B - L * (Z - P) * (B * L') := by simp only [Matrix.mul_assoc]
      _ = (Z - P) * B - L * (Z - P) * (L * B) := by rw [hBL]
      _ = _ := by simp only [Matrix.sub_mul, Matrix.mul_assoc]
  change frobNorm ((Z - P) * B - L * (Z - P) * B * L') ^ 2 ≤ _
  rw [hR]
  exact frobNorm_sub_mul_mul_sq_le_of_diagonalization B hQ hcard d hG' (p k) w hZ
    (hPi k) hL (singularValues_nonneg B (k - 1)) hc hd hhead htail hout
    (singularValues_sq_mul_frobNorm_sq_sub_nonneg B hk hZ hZk)
end NLAlib
