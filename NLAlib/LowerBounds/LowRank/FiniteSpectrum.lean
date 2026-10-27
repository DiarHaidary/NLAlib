/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.FewPasses
public import NLAlib.Polynomial.Interpolation.DividedDifference
public import NLAlib.Polynomial.Chebyshev.ExtremaEvaluation

/-!
# Finite-spectrum hard instances for low-rank approximation

Numerical factors for the equispaced positive-spectrum family with a head at $r+2$ and tails
at $1,\ldots,r+1$. Design: `docs/design/LowerBounds-FixedBatches.md`; the design is approved.

## Main definitions

* `NLAlib.equispacedGaussianFactor`: sufficient width separation for Gaussian head capture.
* `NLAlib.equispacedTailFactor`: optimal squared Frobenius loss per tail multiplicity.
* `NLAlib.equispacedNuclearTailFactor`: optimal nuclear loss per tail multiplicity.

For natural $r$, the width factor is <!-- value equispacedGaussianFactor r -->
$64\cdot4^{r+1}$, and the tail factor is <!-- value equispacedTailFactor r -->
$(r+1)(r+2)(2r+3)/6$.
The nuclear tail factor is <!-- value equispacedNuclearTailFactor r -->
$(r+1)(r+2)/2$.

## Main results

The theorems below give the exact optimum, loss from missed head mass, positive semidefiniteness,
and the arbitrary-degree block Krylov interpolation bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

/-- **Gaussian width factor for equispaced spectra**: for a natural batch count $r$, the
Gaussian head-capture argument uses <!-- value equispacedGaussianFactor r -->
$$64\cdot4^{r+1} \,.$$
It is the square of the deviation parameter $8\cdot2^{r+1}$. -/
noncomputable irreducible_def equispacedGaussianFactor (r : ℕ) : ℝ := 64 * 4 ^ (r + 1)

/-- **Tail energy of the equispaced spectrum**: each tail multiplicity contributes its squared
energy. Its value is <!-- value equispacedTailFactor r -->
$$(r+1)(r+2)(2r+3)/6 \,.$$
This is the sum of the squared levels $1,\ldots,r+1$. -/
noncomputable irreducible_def equispacedTailFactor (r : ℕ) : ℝ :=
  ((r : ℝ) + 1) * (r + 2) * (2 * r + 3) / 6

/-- Tail mass per multiplicity. Its value is <!-- value equispacedNuclearTailFactor r -->
$$(r+1)(r+2)/2 \,.$$
This is the sum of the levels $1,\ldots,r+1$. -/
noncomputable irreducible_def equispacedNuclearTailFactor (r : ℕ) : ℝ :=
  ((r : ℝ) + 1) * (r + 2) / 2

/-- The positive tail levels sum to the nuclear tail mass. -/
theorem sum_eq_equispacedNuclearTailFactor (r : ℕ) :
    (∑ j : Fin (r + 1), ((j : ℝ) + 1)) = equispacedNuclearTailFactor r := by
  induction r with
  | zero => norm_num [equispacedNuclearTailFactor_def]
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, equispacedNuclearTailFactor_def, equispacedNuclearTailFactor_def]
    push_cast
    ring

/-- Multiplicity scales the nuclear tail mass. -/
theorem sum_prod_eq_mul_equispacedNuclearTailFactor {m : Type*} [Fintype m] (r : ℕ) :
    (∑ x : Fin (r + 1) × m, ((x.1 : ℝ) + 1)) =
      Fintype.card m * equispacedNuclearTailFactor r := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_eq_equispacedNuclearTailFactor]

/-- The squared tail levels sum to the equispaced tail energy. -/
theorem sum_sq_eq_equispacedTailFactor (r : ℕ) :
    (∑ j : Fin (r + 1), ((j : ℝ) + 1) ^ 2) = equispacedTailFactor r := by
  induction r with
  | zero => norm_num [equispacedTailFactor_def]
  | succ r ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, equispacedTailFactor_def, equispacedTailFactor_def]
    push_cast
    ring

/-- Multiplicity scales the squared tail energy. -/
theorem sum_prod_sq_eq_mul_equispacedTailFactor {m : Type*} [Fintype m] (r : ℕ) :
    (∑ x : Fin (r + 1) × m, ((x.1 : ℝ) + 1) ^ 2) =
      Fintype.card m * equispacedTailFactor r := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_sq_eq_equispacedTailFactor]


/-- The **level spectrum** with head value $L$ on $k$ and tail level $\nu_j$ of multiplicity
$\lvert m\rvert$ for $j = 0, \dots, r$. The fixed-batch hard instances are its orthogonal
conjugates. -/
def levelSpectrum (k m : Type*) {r : ℕ} (L : ℝ) (ν : Fin (r + 1) → ℝ) :
    k ⊕ (Fin (r + 1) × m) → ℝ :=
  Sum.elim (fun _ => L) fun x => ν x.1

/-- The equispaced spectrum is the level spectrum with head $r+2$ and levels $j+1$. -/
theorem equispacedLevelSpectrum_eq_levelSpectrum (k m : Type*) (r : ℕ) :
    equispacedLevelSpectrum k m r =
      levelSpectrum k m ((r : ℝ) + 2) fun j : Fin (r + 1) => (j : ℝ) + 1 :=
  rfl

/-- **Extrapolation control** of a head value by tail levels: every real polynomial $p$ of
degree at most $r$ satisfies
$$p(L)^2 \le C\sum_{j=0}^{r} p(\nu_j)^2 \,.$$
Degree-$r$ Krylov polynomials then cannot be large at the head unless they are large on the
tail levels. -/
def IsExtrapolationControl {r : ℕ} (L : ℝ) (ν : Fin (r + 1) → ℝ) (C : ℝ) : Prop :=
  ∀ p : Polynomial ℝ, p.natDegree < r + 1 → p.eval L ^ 2 ≤ C * ∑ j, p.eval (ν j) ^ 2

/-- An extrapolation constant is positive: the constant polynomial gives $1 \le (r+1)C$. -/
theorem IsExtrapolationControl.pos {r : ℕ} {L C : ℝ} {ν : Fin (r + 1) → ℝ}
    (h : IsExtrapolationControl L ν C) : 0 < C := by
  have h1 := h 1 (by simp)
  simp only [Polynomial.eval_one, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at h1
  by_contra hC
  have : C * ((r : ℝ) + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hC) (by positivity)
  push_cast at h1
  linarith

/-- The equispaced levels have extrapolation control with the factor
$C =$ <!-- value equispacedInterpolationFactor r --> $4^{r+1}$. -/
theorem isExtrapolationControl_equispacedInterpolationFactor (r : ℕ) :
    IsExtrapolationControl ((r : ℝ) + 2) (fun j : Fin (r + 1) => (j : ℝ) + 1)
      (equispacedInterpolationFactor r) :=
  fun _ hp => eval_sq_le_equispacedInterpolationFactor_mul_sum_eval_sq_of_natDegree_lt r hp

/-- Summed over a finite polynomial family, an extrapolation bound gives
$\sum_c p_c(L)^2 \le C\sum_j\sum_c p_c(\nu_j)^2$. -/
theorem IsExtrapolationControl.sum_eval_sq_le {r : ℕ} {L C : ℝ} {ν : Fin (r + 1) → ℝ}
    (h : IsExtrapolationControl L ν C) {b : Type*} [Fintype b] {f : b → Polynomial ℝ}
    (hdeg : ∀ c, (f c).natDegree < r + 1) :
    (∑ c, (f c).eval L ^ 2) ≤ C * ∑ j, ∑ c, (f c).eval (ν j) ^ 2 := by
  have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => h (f c) (hdeg c)
  rw [← Finset.mul_sum, Finset.sum_comm] at hs
  exact hs

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

omit [DecidableEq k] [DecidableEq m] in
/-- A tail sum over the level index and the multiplicity. -/
private theorem sum_prod_fst_eq_mul_sum {r : ℕ} (f : Fin (r + 1) → ℝ) :
    (∑ x : Fin (r + 1) × m, f x.1) = Fintype.card m * ∑ j, f j := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.mul_sum]

/-- Every congruence of a nonnegative level spectrum is positive semidefinite. -/
theorem posSemidef_mul_diagonal_levelSpectrum_mul_conjTranspose {r : ℕ} {L : ℝ}
    {ν : Fin (r + 1) → ℝ} (hL : 0 ≤ L) (hν : ∀ j, 0 ≤ ν j)
    (U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ) :
    (U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  rintro (a | ⟨j, i⟩)
  · exact hL
  · exact hν j

/-- Every congruence of the equispaced positive diagonal is positive semidefinite. -/
theorem posSemidef_mul_diagonal_equispacedLevelSpectrum_mul_conjTranspose
    (r : ℕ) (U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ) :
    (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ).PosSemidef := by
  rw [equispacedLevelSpectrum_eq_levelSpectrum]
  exact posSemidef_mul_diagonal_levelSpectrum_mul_conjTranspose (by positivity)
    (fun j => by positivity) U

/-- The squared norm of a level diagonal splits into its head and tail energies. -/
private theorem frobNorm_diagonal_levelSpectrum_sq {r : ℕ} (L : ℝ) (ν : Fin (r + 1) → ℝ) :
    frobNorm (Matrix.diagonal (levelSpectrum k m L ν)) ^ 2 =
      L ^ 2 * Fintype.card k + Fintype.card m * ∑ j, ν j ^ 2 := by
  rw [frobNorm_diagonal_sq, Fintype.sum_sum_type]
  simp only [levelSpectrum, Sum.elim_inl, Sum.elim_inr, Real.norm_eq_abs, sq_abs]
  rw [sum_prod_fst_eq_mul_sum (m := m) (fun j => ν j ^ 2)]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The head-only diagonal has rank at most the target rank. -/
private theorem rank_mul_diagonal_head_mul_conjTranspose_le {r : ℕ} {L : ℝ} (hL : 0 < L)
    (U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ) :
    (U * Matrix.diagonal (Sum.elim (fun _ : k => L)
      (fun _ : Fin (r + 1) × m => 0)) * Uᴴ).rank ≤ Fintype.card k := by
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
  rw [Matrix.rank_diagonal]
  refine Fintype.card_le_of_surjective
    (fun a : k => ⟨Sum.inl a, by simp only [Sum.elim_inl]; exact hL.ne'⟩) ?_
  rintro ⟨a | x, hx⟩
  · exact ⟨a, rfl⟩
  · exact (hx rfl).elim

/-- Singular values of an orthogonal conjugate of a level diagonal do not exceed its head. -/
private theorem singularValues_mul_diagonal_levelSpectrum_le {r : ℕ} {L : ℝ}
    {ν : Fin (r + 1) → ℝ} (hL : 0 ≤ L) (hν0 : ∀ j, 0 ≤ ν j) (hνL : ∀ j, ν j ≤ L)
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasOrthonormalCols U) (i : ℕ) :
    singularValues (U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ) i ≤ L := by
  refine (singularValues_le_specNorm _ i).trans ?_
  rw [hU.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left]
  refine specNorm_diagonal_le hL ?_
  rintro (a | ⟨j, b⟩)
  · simp only [levelSpectrum, Sum.elim_inl, Real.norm_eq_abs, abs_of_nonneg hL, le_refl]
  · simpa only [levelSpectrum, Sum.elim_inr, Real.norm_eq_abs, abs_of_nonneg (hν0 j)] using hνL j

/-- The optimum for an orthogonal conjugate of a nonnegative level spectrum with a positive head
dominating every level is its tail energy $\lvert m\rvert\sum_j \nu_j^2$. -/
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_sq_eq_mul_sum_sq {r : ℕ} {L : ℝ}
    {ν : Fin (r + 1) → ℝ} (hL : 0 < L) (hν0 : ∀ j, 0 ≤ ν j) (hνL : ∀ j, ν j ≤ L)
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasOrthonormalCols U) :
    frobNorm (U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ -
      truncatedSVD (U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ)
        (Fintype.card k)) ^ 2 = Fintype.card m * ∑ j, ν j ^ 2 := by
  let d := levelSpectrum k m L ν
  let A := U * Matrix.diagonal d * Uᴴ
  let h : k ⊕ (Fin (r + 1) × m) → ℝ := Sum.elim (fun _ => L) 0
  have hcard : Fintype.card k ≤ Fintype.card (k ⊕ (Fin (r + 1) × m)) := by simp
  have hT : frobNorm (Matrix.diagonal (d - h)) ^ 2 = Fintype.card m * ∑ j, ν j ^ 2 := by
    rw [frobNorm_diagonal_sq, Fintype.sum_sum_type]
    simp only [Real.norm_eq_abs, sq_abs, d, h, Pi.sub_apply, Pi.zero_apply,
      levelSpectrum, Sum.elim_inl, Sum.elim_inr, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_add, sub_zero]
    exact sum_prod_fst_eq_mul_sum (m := m) (fun j => ν j ^ 2)
  refine le_antisymm ?_ ?_
  · rw [← hT]
    refine pow_le_pow_left₀ (frobNorm_nonneg _)
      ((frobNorm_sub_truncatedSVD_le_of_rank_le A
        (rank_mul_diagonal_head_mul_conjTranspose_le hL U)).trans_eq ?_) 2
    change frobNorm (A - U * Matrix.diagonal h * Uᴴ) = frobNorm (Matrix.diagonal (d - h))
    rw [show A - U * Matrix.diagonal h * Uᴴ = U * Matrix.diagonal (d - h) * Uᴴ by
      dsimp only [A]
      rw [show d - h = fun i => d i - h i from rfl,
        ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul],
      hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left]
  · have hA : frobNorm A ^ 2 = L ^ 2 * Fintype.card k + Fintype.card m * ∑ j, ν j ^ 2 := by
      rw [hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left]
      exact frobNorm_diagonal_levelSpectrum_sq L ν
    have hhead : ∑ i ∈ Finset.range (Fintype.card k), singularValues A i ^ 2 ≤
        L ^ 2 * Fintype.card k := by
      calc _ ≤ ∑ i ∈ Finset.range (Fintype.card k), L ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (singularValues_nonneg A i)
              (singularValues_mul_diagonal_levelSpectrum_le hL.le hν0 hνL hU i) 2
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    change Fintype.card m * ∑ j, ν j ^ 2 ≤ frobNorm (A - truncatedSVD A _) ^ 2
    rw [frobNorm_sub_truncatedSVD_sq, min_self]
    rw [frobNorm_sq_eq_sum_singularValues_sq, ← Finset.sum_range_add_sum_Ico _ hcard] at hA
    linarith

/-- The optimum for an orthogonal conjugate of the equispaced spectrum is its tail energy.
For natural $r$, this is the tail multiplicity times its energy.
Its value is <!-- value equispacedTailFactor r -->
$$(r+1)(r+2)(2r+3)/6 \,.$$
The head consists of the largest $\lvert k\rvert$ singular values, including empty index types. -/
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_sq_eq_mul_equispacedTailFactor
    (r : ℕ) {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasOrthonormalCols U) :
    frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ -
      truncatedSVD (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ)
        (Fintype.card k)) ^ 2 = Fintype.card m * equispacedTailFactor r := by
  rw [equispacedLevelSpectrum_eq_levelSpectrum,
    hU.frobNorm_sub_truncatedSVD_sq_eq_mul_sum_sq (by positivity) (fun j => by positivity)
      (fun j => by have := (Nat.cast_le (α := ℝ)).2 (Nat.lt_succ_iff.mp j.is_lt); linarith),
    sum_sq_eq_equispacedTailFactor]

omit [DecidableEq k] [DecidableEq m] in
/-- The linear mass of a level spectrum splits into head and tail mass. -/
private theorem sum_levelSpectrum {r : ℕ} (L : ℝ) (ν : Fin (r + 1) → ℝ) :
    (∑ i, levelSpectrum k m L ν i) = L * Fintype.card k + Fintype.card m * ∑ j, ν j := by
  rw [Fintype.sum_sum_type]
  simp only [levelSpectrum, Sum.elim_inl, Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [sum_prod_fst_eq_mul_sum (m := m) ν]
  ring

/-- The nuclear optimum of an orthogonal conjugate of a nonnegative level spectrum with a
positive head dominating every level is its tail mass $\lvert m\rvert\sum_j\nu_j$. -/
theorem HasOrthonormalCols.nuclearNorm_sub_truncatedSVD_eq_mul_sum {r : ℕ} {L : ℝ}
    {ν : Fin (r + 1) → ℝ} (hL : 0 < L) (hν0 : ∀ j, 0 ≤ ν j) (hνL : ∀ j, ν j ≤ L)
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasOrthonormalCols U) :
    nuclearNorm (U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ -
      truncatedSVD (U * Matrix.diagonal (levelSpectrum k m L ν) * Uᴴ)
        (Fintype.card k)) = Fintype.card m * ∑ j, ν j := by
  let d := levelSpectrum k m L ν
  let A := U * Matrix.diagonal d * Uᴴ
  let h : k ⊕ (Fin (r + 1) × m) → ℝ := Sum.elim (fun _ => L) 0
  have hd : (Matrix.diagonal d).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    rintro (a | ⟨j, i⟩)
    · exact hL.le
    · exact hν0 j
  have htail : (Matrix.diagonal (d - h)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    rintro (a | ⟨j, i⟩)
    · simp only [d, h, Pi.sub_apply, levelSpectrum, Sum.elim_inl, sub_self, le_refl]
    · simpa only [d, h, Pi.sub_apply, levelSpectrum, Sum.elim_inr, Pi.zero_apply,
        sub_zero] using hν0 j
  have hT : nuclearNorm (Matrix.diagonal (d - h)) = Fintype.card m * ∑ j, ν j := by
    rw [htail.nuclearNorm_eq_re_trace, Matrix.trace_diagonal]
    change (∑ i, (d - h) i) = _
    rw [Fintype.sum_sum_type]
    simp only [d, h, Pi.sub_apply, Pi.zero_apply, levelSpectrum,
      Sum.elim_inl, Sum.elim_inr, sub_self, Finset.sum_const_zero, zero_add, sub_zero]
    exact sum_prod_fst_eq_mul_sum (m := m) ν
  refine le_antisymm ?_ ?_
  · have hbest := (lpGauge 1).matrixNorm_sub_truncatedSVD_le_of_rank_le A
      (rank_mul_diagonal_head_mul_conjTranspose_le hL U)
    rw [lpGauge_one_matrixNorm, lpGauge_one_matrixNorm] at hbest
    refine hbest.trans_eq ?_
    change nuclearNorm (A - U * Matrix.diagonal h * Uᴴ) = _
    rw [show A - U * Matrix.diagonal h * Uᴴ = U * Matrix.diagonal (d - h) * Uᴴ by
      dsimp only [A]
      rw [show d - h = fun i => d i - h i from rfl,
        ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul],
      hU.nuclearNorm_mul_conjTranspose_right, hU.nuclearNorm_mul_left, hT]
  · have hA : nuclearNorm A = L * Fintype.card k + Fintype.card m * ∑ j, ν j := by
      rw [hU.nuclearNorm_mul_conjTranspose_right, hU.nuclearNorm_mul_left,
        hd.nuclearNorm_eq_re_trace, Matrix.trace_diagonal]
      exact sum_levelSpectrum L ν
    have hhead : nuclearNorm (truncatedSVD A (Fintype.card k)) ≤ L * Fintype.card k := by
      rw [nuclearNorm_eq_sum_range _ (rank_truncatedSVD_le A (Fintype.card k))]
      calc _ ≤ ∑ i ∈ Finset.range (Fintype.card k), L := by
            refine Finset.sum_le_sum fun i hi => ?_
            rw [singularValues_truncatedSVD, if_pos (Finset.mem_range.mp hi)]
            exact singularValues_mul_diagonal_levelSpectrum_le hL.le hν0 hνL hU i
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    have htriangle := nuclearNorm_add_le (A - truncatedSVD A (Fintype.card k))
      (truncatedSVD A (Fintype.card k))
    rw [sub_add_cancel, hA] at htriangle
    change _ ≤ nuclearNorm (A - truncatedSVD A (Fintype.card k))
    linarith

/-- The nuclear optimum of an orthogonal conjugate of the equispaced spectrum equals the
multiplicity times the sum of its tail levels, including empty head and tail index types. -/
theorem HasOrthonormalCols.nuclearNorm_sub_truncatedSVD_eq_mul_equispacedNuclearTailFactor
    (r : ℕ) {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasOrthonormalCols U) :
    nuclearNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ -
      truncatedSVD (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ)
        (Fintype.card k)) = Fintype.card m * equispacedNuclearTailFactor r := by
  rw [equispacedLevelSpectrum_eq_levelSpectrum,
    hU.nuclearNorm_sub_truncatedSVD_eq_mul_sum (by positivity) (fun j => by positivity)
      (fun j => by have := (Nat.cast_le (α := ℝ)).2 (Nat.lt_succ_iff.mp j.is_lt); linarith),
    sum_eq_equispacedNuclearTailFactor]

/-- Missed head mass forces nuclear excess on a level spectrum whose levels lie in $[0,\tau]$:
the excess coefficient is $L - \tau$. The output factor may be rank deficient, and the
approximation residual need not be positive semidefinite. -/
theorem le_nuclearNorm_diagonal_levelSpectrum_sub_mul {r : ℕ} {L τ : ℝ} {ν : Fin (r + 1) → ℝ}
    (hν0 : ∀ j, 0 ≤ ν j) (hντ : ∀ j, ν j ≤ τ)
    (W : Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ) :
    Fintype.card m * ∑ j, ν j +
      (L - τ) * (Fintype.card k - ∑ i : k, rangeProjector W (Sum.inl i) (Sum.inl i)) ≤
      nuclearNorm (Matrix.diagonal (levelSpectrum k m L ν) - W * M) := by
  let P := rangeProjector W
  let H := ∑ a : k, P (Sum.inl a) (Sum.inl a)
  let T := ∑ x : Fin (r + 1) × m, P (Sum.inr x) (Sum.inr x)
  let d := levelSpectrum k m L ν
  have hτ : 0 ≤ τ := (hν0 0).trans (hντ 0)
  have hP : IsStarProjection P := isStarProjection_rangeProjector W
  have hPnn (i) : 0 ≤ P i i := by
    rw [← hP.norm_toLp_mulVec_single_sq i]
    positivity
  have htr : H + T ≤ Fintype.card k := by
    have h1 : ∑ i, P i i = (W.rank : ℝ) := trace_rangeProjector W
    have h2 : (W.rank : ℝ) ≤ Fintype.card k := by
      exact_mod_cast Matrix.rank_le_card_width W
    rw [Fintype.sum_sum_type] at h1
    linarith
  have htail : ∑ x : Fin (r + 1) × m, ν x.1 * P (Sum.inr x) (Sum.inr x) ≤ τ * T := by
    dsimp only [T]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right (hντ x.1) (hPnn _)
  have hcap : ∑ i, d i * P i i ≤ τ * Fintype.card k + (L - τ) * H := by
    rw [Fintype.sum_sum_type]
    have hhead : ∑ a : k, d (Sum.inl a) * P (Sum.inl a) (Sum.inl a) = L * H := by
      simp only [d, levelSpectrum, Sum.elim_inl, H, Finset.mul_sum]
    rw [hhead]
    change L * H + ∑ x : Fin (r + 1) × m, ν x.1 * P (Sum.inr x) (Sum.inr x) ≤ _
    have htr' := mul_le_mul_of_nonneg_left htr hτ
    nlinarith
  have herr := re_trace_sub_rangeProjector_mul_le_nuclearNorm_sub_mul
    (Matrix.diagonal d) W M
  have heq : (Matrix.diagonal d - P * Matrix.diagonal d).trace =
      (∑ i, d i) - ∑ i, d i * P i i := by
    rw [Matrix.trace_sub, Matrix.trace_diagonal]
    congr 1
    simp only [Matrix.trace, Matrix.mul_diagonal, Matrix.diag_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  change (Matrix.diagonal d - P * Matrix.diagonal d).trace ≤ _ at herr
  rw [heq, sum_levelSpectrum] at herr
  change Fintype.card m * ∑ j, ν j + (L - τ) * (Fintype.card k - H) ≤ _
  linarith

/-- Projection onto the output range bounds the captured diagonal energy of any approximation. -/
private theorem sum_sq_sub_sum_sq_mul_le_frobNorm_diagonal_sub_mul_sq
    {n b : Type*} [Fintype n] [Fintype b] [DecidableEq n]
    (d : n → ℝ) (W : Matrix n b ℝ) (M : Matrix b n ℝ) :
    (∑ j, d j ^ 2) - (∑ j, d j ^ 2 * rangeProjector W j j) ≤
      frobNorm (Matrix.diagonal d - W * M) ^ 2 := by
  let P := rangeProjector W
  have hP : IsStarProjection P := isStarProjection_rangeProjector W
  have hQ : IsStarProjection (1 - P) := isStarProjection_one_sub_rangeProjector W
  have hkill : (1 - P) * W = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]
  have heq : Matrix.diagonal d - P * Matrix.diagonal d =
      (1 - P) * (Matrix.diagonal d - W * M) := by
    rw [Matrix.mul_sub, ← Matrix.mul_assoc _ W, hkill, Matrix.zero_mul, sub_zero,
      Matrix.sub_mul, Matrix.one_mul]
  have hcontr := pow_le_pow_left₀ (frobNorm_nonneg _)
    (hQ.frobNorm_mul_le (Matrix.diagonal d - W * M)) 2
  rw [← heq] at hcontr
  have hcalc : frobNorm (Matrix.diagonal d - P * Matrix.diagonal d) ^ 2 =
      (∑ j, d j ^ 2) - ∑ j, d j ^ 2 * P j j := by
    rw [hP.frobNorm_sub_mul_sq_eq_sub_frobInner, frobNorm_diagonal_sq, frobInner_eq_sum_mul,
      Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    simp only [Real.norm_eq_abs, sq_abs, Matrix.diagonal_apply, mul_ite, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.star_apply, star_trivial]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  rwa [hcalc] at hcontr

/-- Missing head mass forces Frobenius excess on a level spectrum whose levels lie in
$[0,\tau]$: the excess coefficient is $L^2-\tau^2$, and the tail optimum is
$\lvert m\rvert\sum_j\nu_j^2$. The output factors can be rank deficient; no full-rank output
hypothesis is required. -/
theorem le_frobNorm_diagonal_levelSpectrum_sub_mul_sq {r : ℕ} {L τ : ℝ} {ν : Fin (r + 1) → ℝ}
    (hν0 : ∀ j, 0 ≤ ν j) (hντ : ∀ j, ν j ≤ τ)
    (W : Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ) :
    Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) * (Fintype.card k -
      ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) ≤
      frobNorm (Matrix.diagonal (levelSpectrum k m L ν) - W * M) ^ 2 := by
  let P := rangeProjector W
  let H := ∑ a : k, P (Sum.inl a) (Sum.inl a)
  let T := ∑ x : Fin (r + 1) × m, P (Sum.inr x) (Sum.inr x)
  let d := levelSpectrum k m L ν
  have hP : IsStarProjection P := isStarProjection_rangeProjector W
  have hPnn (i) : 0 ≤ P i i := by
    rw [← hP.norm_toLp_mulVec_single_sq i]
    positivity
  have ht : ∑ a : k, ‖WithLp.toLp 2 (P *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2 = H :=
    Finset.sum_congr rfl fun a _ => hP.norm_toLp_mulVec_single_sq _
  have htr : H + T ≤ Fintype.card k := by
    have h1 : ∑ i, P i i = (W.rank : ℝ) := trace_rangeProjector W
    have h2 : (W.rank : ℝ) ≤ Fintype.card k := by exact_mod_cast Matrix.rank_le_card_width W
    rw [Fintype.sum_sum_type] at h1
    linarith
  have htail : ∑ x : Fin (r + 1) × m, ν x.1 ^ 2 * P (Sum.inr x) (Sum.inr x) ≤ τ ^ 2 * T := by
    dsimp only [T]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (hν0 x.1) (hντ x.1) 2) (hPnn _)
  have hcap : ∑ i, d i ^ 2 * P i i ≤ L ^ 2 * H + τ ^ 2 * (Fintype.card k - H) := by
    rw [Fintype.sum_sum_type]
    have hhead : ∑ a : k, d (Sum.inl a) ^ 2 * P (Sum.inl a) (Sum.inl a) = L ^ 2 * H := by
      simp only [d, levelSpectrum, Sum.elim_inl, H, Finset.mul_sum]
    rw [hhead]
    have htr' := mul_le_mul_of_nonneg_left htr (sq_nonneg τ)
    change L ^ 2 * H + ∑ x : Fin (r + 1) × m, ν x.1 ^ 2 * P (Sum.inr x) (Sum.inr x) ≤ _
    nlinarith
  have htotal : ∑ i, d i ^ 2 = L ^ 2 * Fintype.card k + Fintype.card m * ∑ j, ν j ^ 2 := by
    have h := frobNorm_diagonal_levelSpectrum_sq (k := k) (m := m) L ν
    rw [frobNorm_diagonal_sq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have herr := sum_sq_sub_sum_sq_mul_le_frobNorm_diagonal_sub_mul_sq d W M
  change Fintype.card m * ∑ j, ν j ^ 2 + (L ^ 2 - τ ^ 2) *
    (Fintype.card k - ∑ a : k, ‖WithLp.toLp 2 (P *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) ≤ _
  rw [ht]
  rw [htotal] at herr
  nlinarith

/-- At Krylov depth $r+1$, an extrapolation bound with constant $C$ converts tail Gram lower
bounds and a head spectral-norm bound into a uniform head-mass bound
$$s^2\sum_a z_a^2\le C S^2\|z\|^2 \,.$$
The statement includes empty head, tail-multiplicity and column index types. -/
theorem mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace_of_isExtrapolationControl
    {r : ℕ} {L C : ℝ}
    {ν : Fin (r + 1) → ℝ} (hI : IsExtrapolationControl L ν C) {b : Type*} [Fintype b]
    [DecidableEq b] {G : Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ} {s S : ℝ}
    (hs : ∀ j : Fin (r + 1), s ^ 2 • (1 : Matrix b b ℝ) ≤
      (G.submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        G.submatrix (fun i : m => Sum.inr (j, i)) id)
    (hS : specNorm (G.submatrix Sum.inl id) ≤ S) {z : k ⊕ (Fin (r + 1) × m) → ℝ}
    (hz : z ∈ blockKrylovSpace (Matrix.diagonal (levelSpectrum k m L ν)) G (r + 1)) :
    s ^ 2 * ∑ a : k, z (Sum.inl a) ^ 2 ≤ C * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
  obtain ⟨f, hf, hz'⟩ := mem_blockKrylovSpace_iff.1 hz
  have hzi : ∀ x, z x = ∑ c, (f c).eval (levelSpectrum k m L ν x) * G x c := by
    intro x
    rw [← hz']
    simp only [Finset.sum_apply, aeval_diagonal_self, Matrix.mulVec_diagonal, Matrix.col_apply]
  have hdeg : ∀ c, (f c).natDegree < r + 1 := by
    intro c
    by_cases h0 : f c = 0
    · simp only [h0, Polynomial.natDegree_zero]; omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 (by exact_mod_cast hf c)
  have hH : ∑ a : k, z (Sum.inl a) ^ 2 ≤ S ^ 2 * ∑ c, (f c).eval L ^ 2 := by
    have hw : ∀ a : k, z (Sum.inl a) =
        (G.submatrix Sum.inl id *ᵥ fun c => (f c).eval L) a := by
      intro a
      rw [hzi]
      simp only [levelSpectrum, Sum.elim_inl, Matrix.mulVec, dotProduct,
        Matrix.submatrix_apply, id_eq]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    have h1 : ‖WithLp.toLp 2 (G.submatrix Sum.inl id *ᵥ fun c => (f c).eval L)‖ ≤
        S * ‖WithLp.toLp 2 (fun c => (f c).eval L)‖ :=
      (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
      EuclideanSpace.norm_toLp_sq_eq_sum_sq] at h2
    simp only [hw]
    exact h2
  have hL (j : Fin (r + 1)) : s ^ 2 * ∑ c, (f c).eval (ν j) ^ 2 ≤
      ∑ i : m, z (Sum.inr (j, i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr (j, i)) =
        (G.submatrix (fun i : m => Sum.inr (j, i)) id *ᵥ fun c => (f c).eval (ν j)) i := by
      intro i
      rw [hzi]
      simp only [levelSpectrum, Sum.elim_inr, Matrix.mulVec, dotProduct,
        Matrix.submatrix_apply, id_eq]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs j) _
  have hN := hI.sum_eval_sq_le hdeg
  have hLs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hL j
  rw [← Finset.mul_sum] at hLs
  have hnorm : ‖WithLp.toLp 2 z‖ ^ 2 = ∑ a : k, z (Sum.inl a) ^ 2 +
      ∑ j : Fin (r + 1), ∑ i : m, z (Sum.inr (j, i)) ^ 2 := by
    rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hC : 0 ≤ C := hI.pos.le
  calc
    _ ≤ s ^ 2 * (S ^ 2 * ∑ c, (f c).eval L ^ 2) :=
      mul_le_mul_of_nonneg_left hH (sq_nonneg s)
    _ ≤ s ^ 2 * (S ^ 2 * (C * ∑ j : Fin (r + 1), ∑ c, (f c).eval (ν j) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN (sq_nonneg S)) (sq_nonneg s)
    _ = C * S ^ 2 * (s ^ 2 * ∑ j : Fin (r + 1), ∑ c, (f c).eval (ν j) ^ 2) := by ring
    _ ≤ C * S ^ 2 * (∑ j : Fin (r + 1), ∑ i : m, z (Sum.inr (j, i)) ^ 2) :=
      mul_le_mul_of_nonneg_left hLs (mul_nonneg hC (sq_nonneg S))
    _ ≤ C * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (sq_nonneg S))
      rw [hnorm]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun a _ => sq_nonneg _)

/-- The **Chebyshev head gap** $\delta_r = 1/(8(r+1)^2)$: the head of the Chebyshev hard
spectrum sits at $1+\delta_r$, just above the tail levels in $[1/2, 1]$. -/
noncomputable def chebyshevHeadGap (r : ℕ) : ℝ := 1 / (8 * ((r : ℝ) + 1) ^ 2)

/-- **Chebyshev tail levels**: $\nu_j = 1 + \delta_r - \xi_j$, with $\xi_j$ the Chebyshev
extrema of $[\delta_r, \delta_r + 1/2]$ (`chebyshevExtremum`) and $\delta_r$ =
`chebyshevHeadGap r`. The levels lie in $[1/2, 1]$, and $\nu_0 = 1$. -/
noncomputable def chebyshevTailLevel (r : ℕ) (j : Fin (r + 1)) : ℝ :=
  1 + chebyshevHeadGap r -
    chebyshevExtremum (chebyshevHeadGap r) (1 / 2 + chebyshevHeadGap r) r j

/-- The **Chebyshev hard spectrum**: the level spectrum with head $1+\delta_r$ and the Chebyshev
tail levels (`chebyshevTailLevel`). -/
noncomputable def chebyshevLevelSpectrum (k m : Type*) (r : ℕ) : k ⊕ (Fin (r + 1) × m) → ℝ :=
  levelSpectrum k m (1 + chebyshevHeadGap r) (chebyshevTailLevel r)

/-- The Chebyshev head gap is positive. -/
theorem chebyshevHeadGap_pos (r : ℕ) : 0 < chebyshevHeadGap r := by
  rw [chebyshevHeadGap]
  positivity

/-- The Chebyshev tail levels are at least one half. -/
theorem le_chebyshevTailLevel (r : ℕ) (j : Fin (r + 1)) : 1 / 2 ≤ chebyshevTailLevel r j := by
  have h := (chebyshevExtremum_mem_Icc (by linarith : chebyshevHeadGap r ≤
    1 / 2 + chebyshevHeadGap r) r j).2
  rw [chebyshevTailLevel]
  linarith

/-- The Chebyshev tail levels are at most one. -/
theorem chebyshevTailLevel_le (r : ℕ) (j : Fin (r + 1)) : chebyshevTailLevel r j ≤ 1 := by
  have h := (chebyshevExtremum_mem_Icc (by linarith : chebyshevHeadGap r ≤
    1 / 2 + chebyshevHeadGap r) r j).1
  rw [chebyshevTailLevel]
  linarith

/-- The Chebyshev tail levels have extrapolation constant four: every real polynomial $p$ of degree
at most $r$ satisfies
$$p(1+\delta_r)^2 \le 4\sum_{j=0}^{r} p(\nu_j)^2$$
on the Chebyshev tail levels. Reflecting $x \mapsto 1+\delta_r-x$ moves the head to zero and
the levels to the Chebyshev extrema of $[\delta_r, \delta_r+1/2]$, whose Chebyshev value is at
most two (`NLAlib.eval_T_real_le_two`). -/
theorem isExtrapolationControl_chebyshevTailLevel (r : ℕ) :
    IsExtrapolationControl (1 + chebyshevHeadGap r) (chebyshevTailLevel r) 4 := by
  intro p hp
  set δ := chebyshevHeadGap r
  have hδ : 0 < δ := chebyshevHeadGap_pos r
  have haa : δ < 1 / 2 + δ := by linarith
  set p' := p.comp (Polynomial.C (1 + δ) - Polynomial.X)
  have hdeg : p'.degree ≤ r := by
    refine Polynomial.degree_le_of_natDegree_le ?_
    refine Polynomial.natDegree_comp_le.trans ?_
    have h1 : (Polynomial.C (1 + δ) - Polynomial.X).natDegree ≤ 1 :=
      (Polynomial.natDegree_sub_le _ _).trans (by simp)
    calc p.natDegree * (Polynomial.C (1 + δ) - Polynomial.X).natDegree ≤ p.natDegree * 1 :=
          Nat.mul_le_mul_left _ h1
      _ ≤ r := by omega
  have hext := eval_zero_sq_le_eval_T_real_sq_mul_sum_eval_chebyshevExtremum_sq
    hδ haa hdeg
  have hT2 := eval_T_real_le_two (a' := 1 / 2 + δ) hδ r (by
    have : (2 * ((r : ℝ) + 1)) ^ 2 * δ = 1 / 2 := by
      simp only [δ, chebyshevHeadGap]
      field_simp
      ring
    linarith)
  have hT1 : 1 ≤ (Polynomial.Chebyshev.T ℝ (r : ℤ)).eval ((1 / 2 + δ + δ) / (1 / 2 + δ - δ)) :=
    Polynomial.Chebyshev.one_le_eval_T_real (r : ℤ) (by
      rw [le_div_iff₀ (by linarith)]
      linarith)
  have hsq : (Polynomial.Chebyshev.T ℝ (r : ℤ)).eval ((1 / 2 + δ + δ) / (1 / 2 + δ - δ)) ^ 2 ≤
      4 := by nlinarith
  simp only [p', Polynomial.eval_comp, Polynomial.eval_sub, Polynomial.eval_C,
    Polynomial.eval_X, sub_zero] at hext
  refine hext.trans ?_
  exact mul_le_mul_of_nonneg_right hsq (Finset.sum_nonneg fun _ _ => sq_nonneg _)

end NLAlib
