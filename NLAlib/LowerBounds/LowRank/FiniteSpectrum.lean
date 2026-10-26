/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.FewPasses
public import NLAlib.Polynomial.Interpolation.DividedDifference

/-!
# Finite-spectrum hard instances for low-rank approximation

Numerical factors for the equispaced positive-spectrum family with a head at $r+2$ and tails
at $1,\ldots,r+1$. Design: `docs/design/LowerBounds-FixedBatches.md`; the design is approved.

## Main definitions

* `NLAlib.equispacedGaussianFactor`: sufficient width separation for Gaussian head capture.
* `NLAlib.equispacedTailFactor`: optimal squared Frobenius loss per tail multiplicity.

For natural $r$, the width factor is <!-- value equispacedGaussianFactor r -->
$64\cdot4^{r+1}$, and the tail factor is <!-- value equispacedTailFactor r -->
$(r+1)(r+2)(2r+3)/6$.

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

/-- Every congruence of the equispaced positive diagonal is positive semidefinite. -/
theorem posSemidef_mul_diagonal_equispacedLevelSpectrum_mul_conjTranspose
    {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
    (r : ℕ) (U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ) :
    (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  rintro (a | ⟨j, i⟩) <;> simp only [equispacedLevelSpectrum, Sum.elim_inl, Sum.elim_inr]
    <;> positivity

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

/-- The squared norm of the full equispaced diagonal splits into its head and tail energies. -/
private theorem frobNorm_diagonal_equispacedLevelSpectrum_sq (r : ℕ) :
    frobNorm (Matrix.diagonal (equispacedLevelSpectrum k m r)) ^ 2 =
      ((r : ℝ) + 2) ^ 2 * Fintype.card k + Fintype.card m * equispacedTailFactor r := by
  rw [frobNorm_diagonal_sq, Fintype.sum_sum_type]
  simp only [equispacedLevelSpectrum, Sum.elim_inl, Sum.elim_inr, Real.norm_eq_abs, sq_abs]
  rw [sum_prod_sq_eq_mul_equispacedTailFactor]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The head-only diagonal has rank at most the target rank. -/
private theorem rank_mul_diagonal_head_mul_conjTranspose_le (r : ℕ)
    (U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ) :
    (U * Matrix.diagonal (Sum.elim (fun _ : k => (r : ℝ) + 2)
      (fun _ : Fin (r + 1) × m => 0)) * Uᴴ).rank ≤ Fintype.card k := by
  refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
  rw [Matrix.rank_diagonal]
  refine Fintype.card_le_of_surjective
    (fun a : k => ⟨Sum.inl a, by simp only [Sum.elim_inl]; positivity⟩) ?_
  rintro ⟨a | x, hx⟩
  · exact ⟨a, rfl⟩
  · exact (hx rfl).elim

/-- Singular values of an orthogonal conjugate of the hard diagonal do not exceed its head. -/
private theorem singularValues_mul_diagonal_equispaced_le (r : ℕ)
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasOrthonormalCols U) (i : ℕ) :
    singularValues (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ) i ≤
      (r : ℝ) + 2 := by
  refine (singularValues_le_specNorm _ i).trans ?_
  rw [hU.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left]
  refine specNorm_diagonal_le (by positivity) ?_
  rintro (a | ⟨j, b⟩)
  · simp only [equispacedLevelSpectrum, Sum.elim_inl, Real.norm_eq_abs]
    rw [abs_of_nonneg (by positivity)]
  · have hj : (j : ℝ) ≤ r := by exact_mod_cast Fin.is_le j
    have hj0 : 0 ≤ (j : ℝ) + 1 := by positivity
    simpa only [equispacedLevelSpectrum, Sum.elim_inr, Real.norm_eq_abs,
      abs_of_nonneg hj0] using (show (j : ℝ) + 1 ≤ (r : ℝ) + 2 by linarith)

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
  let d := equispacedLevelSpectrum k m r
  let A := U * Matrix.diagonal d * Uᴴ
  let h : k ⊕ (Fin (r + 1) × m) → ℝ := Sum.elim (fun _ => (r : ℝ) + 2) 0
  have hcard : Fintype.card k ≤ Fintype.card (k ⊕ (Fin (r + 1) × m)) := by simp
  have hT : frobNorm (Matrix.diagonal (d - h)) ^ 2 =
      Fintype.card m * equispacedTailFactor r := by
    rw [frobNorm_diagonal_sq, Fintype.sum_sum_type]
    simp only [Real.norm_eq_abs, sq_abs, d, h, Pi.sub_apply, Pi.zero_apply,
      equispacedLevelSpectrum, Sum.elim_inl, Sum.elim_inr, sub_self,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), Finset.sum_const_zero, zero_add, sub_zero]
    exact sum_prod_sq_eq_mul_equispacedTailFactor (m := m) r
  refine le_antisymm ?_ ?_
  · rw [← hT]
    refine pow_le_pow_left₀ (frobNorm_nonneg _)
      ((frobNorm_sub_truncatedSVD_le_of_rank_le A
        (rank_mul_diagonal_head_mul_conjTranspose_le r U)).trans_eq ?_) 2
    change frobNorm (A - U * Matrix.diagonal h * Uᴴ) = frobNorm (Matrix.diagonal (d - h))
    rw [show A - U * Matrix.diagonal h * Uᴴ = U * Matrix.diagonal (d - h) * Uᴴ by
      dsimp only [A]
      rw [show d - h = fun i => d i - h i from rfl,
        ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul],
      hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left]
  · have hA : frobNorm A ^ 2 = ((r : ℝ) + 2) ^ 2 * Fintype.card k +
        Fintype.card m * equispacedTailFactor r := by
      rw [hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left]
      exact frobNorm_diagonal_equispacedLevelSpectrum_sq r
    have hhead : ∑ i ∈ Finset.range (Fintype.card k), singularValues A i ^ 2 ≤
        ((r : ℝ) + 2) ^ 2 * Fintype.card k := by
      calc _ ≤ ∑ i ∈ Finset.range (Fintype.card k), ((r : ℝ) + 2) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (singularValues_nonneg A i)
              (singularValues_mul_diagonal_equispaced_le r hU i) 2
        _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
    change Fintype.card m * equispacedTailFactor r ≤ frobNorm (A - truncatedSVD A _) ^ 2
    rw [frobNorm_sub_truncatedSVD_sq, min_self]
    rw [frobNorm_sq_eq_sum_singularValues_sq, ← Finset.sum_range_add_sum_Ico _ hcard] at hA
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

/-- Missing head mass forces Frobenius excess on the equispaced hard spectrum.
For natural $r$, the excess coefficient is $2r+3$, and the tail optimum is the multiplicity
scaled by <!-- value equispacedTailFactor r -->
$$(r+1)(r+2)(2r+3)/6 \,.$$
The output factors can be rank deficient; no full-rank output hypothesis is required. -/
theorem le_frobNorm_diagonal_sub_mul_sq_of_equispacedLevelSpectrum (r : ℕ)
    (W : Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ) :
    Fintype.card m * equispacedTailFactor r + (2 * (r : ℝ) + 3) * (Fintype.card k -
      ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) ≤
      frobNorm (Matrix.diagonal (equispacedLevelSpectrum k m r) - W * M) ^ 2 := by
  let P := rangeProjector W
  let H := ∑ a : k, P (Sum.inl a) (Sum.inl a)
  let T := ∑ x : Fin (r + 1) × m, P (Sum.inr x) (Sum.inr x)
  let d := equispacedLevelSpectrum k m r
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
  have htail : ∑ x : Fin (r + 1) × m,
      ((x.1 : ℝ) + 1) ^ 2 * P (Sum.inr x) (Sum.inr x) ≤ ((r : ℝ) + 1) ^ 2 * T := by
    dsimp only [T]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have hx : (x.1 : ℝ) ≤ r := by exact_mod_cast Fin.is_le x.1
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (by positivity) (by linarith : (x.1 : ℝ) + 1 ≤ (r : ℝ) + 1) 2)
      (hPnn _)
  have hcap : ∑ i, d i ^ 2 * P i i ≤
      ((r : ℝ) + 2) ^ 2 * H + ((r : ℝ) + 1) ^ 2 * (Fintype.card k - H) := by
    rw [Fintype.sum_sum_type]
    have hhead : ∑ a : k, d (Sum.inl a) ^ 2 * P (Sum.inl a) (Sum.inl a) =
        ((r : ℝ) + 2) ^ 2 * H := by
      simp only [d, equispacedLevelSpectrum, Sum.elim_inl, H, Finset.mul_sum]
    rw [hhead]
    have htr' := mul_le_mul_of_nonneg_left htr (sq_nonneg ((r : ℝ) + 1))
    change ((r : ℝ) + 2) ^ 2 * H +
      ∑ x : Fin (r + 1) × m, ((x.1 : ℝ) + 1) ^ 2 * P (Sum.inr x) (Sum.inr x) ≤ _
    nlinarith
  have htotal : ∑ i, d i ^ 2 = ((r : ℝ) + 2) ^ 2 * Fintype.card k +
      Fintype.card m * equispacedTailFactor r := by
    have h := frobNorm_diagonal_equispacedLevelSpectrum_sq (k := k) (m := m) r
    rw [frobNorm_diagonal_sq] at h
    simpa only [Real.norm_eq_abs, sq_abs] using h
  have herr := sum_sq_sub_sum_sq_mul_le_frobNorm_diagonal_sub_mul_sq d W M
  change Fintype.card m * equispacedTailFactor r + (2 * (r : ℝ) + 3) *
    (Fintype.card k - ∑ a : k, ‖WithLp.toLp 2 (P *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) ≤ _
  rw [ht]
  rw [htotal] at herr
  nlinarith
/-- At Krylov depth $r+1$, the equispaced interpolation bound converts tail Gram lower bounds
and a head spectral-norm bound into a uniform head-mass bound.
Its factor is <!-- value equispacedInterpolationFactor r -->
$$s^2\sum_a z_a^2\le4^{r+1}S^2\|z\|^2 \,.$$
The statement includes empty head, tail-multiplicity and column index types. -/
theorem mul_sum_sq_le_equispacedInterpolationFactor_mul_norm_sq_of_mem_blockKrylovSpace
    (r : ℕ) {b : Type*} [Fintype b] [DecidableEq b]
    {G : Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ} {s S : ℝ}
    (hs : ∀ j : Fin (r + 1), s ^ 2 • (1 : Matrix b b ℝ) ≤
      (G.submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        G.submatrix (fun i : m => Sum.inr (j, i)) id)
    (hS : specNorm (G.submatrix Sum.inl id) ≤ S) {z : k ⊕ (Fin (r + 1) × m) → ℝ}
    (hz : z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m r)) G (r + 1)) :
    s ^ 2 * ∑ a : k, z (Sum.inl a) ^ 2 ≤
      equispacedInterpolationFactor r * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
  obtain ⟨f, hf, hz'⟩ := mem_blockKrylovSpace_iff.1 hz
  have hzi : ∀ x, z x = ∑ c, (f c).eval (equispacedLevelSpectrum k m r x) * G x c := by
    intro x
    rw [← hz']
    simp only [Finset.sum_apply, aeval_diagonal_self, Matrix.mulVec_diagonal, Matrix.col_apply]
  have hdeg : ∀ c, (f c).natDegree < r + 1 := by
    intro c
    by_cases h0 : f c = 0
    · simp only [h0, Polynomial.natDegree_zero]; omega
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 (by exact_mod_cast hf c)
  have hH : ∑ a : k, z (Sum.inl a) ^ 2 ≤
      S ^ 2 * ∑ c, (f c).eval ((r : ℝ) + 2) ^ 2 := by
    have hw : ∀ a : k, z (Sum.inl a) =
        (G.submatrix Sum.inl id *ᵥ fun c => (f c).eval ((r : ℝ) + 2)) a := by
      intro a
      rw [hzi]
      simp only [equispacedLevelSpectrum, Sum.elim_inl, Matrix.mulVec, dotProduct,
        Matrix.submatrix_apply, id_eq]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    have h1 : ‖WithLp.toLp 2 (G.submatrix Sum.inl id *ᵥ
        fun c => (f c).eval ((r : ℝ) + 2))‖ ≤
        S * ‖WithLp.toLp 2 (fun c => (f c).eval ((r : ℝ) + 2))‖ :=
      (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
      EuclideanSpace.norm_toLp_sq_eq_sum_sq] at h2
    simp only [hw]
    exact h2
  have hL (j : Fin (r + 1)) : s ^ 2 * ∑ c, (f c).eval ((j : ℝ) + 1) ^ 2 ≤
      ∑ i : m, z (Sum.inr (j, i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr (j, i)) =
        (G.submatrix (fun i : m => Sum.inr (j, i)) id *ᵥ
          fun c => (f c).eval ((j : ℝ) + 1)) i := by
      intro i
      rw [hzi]
      simp only [equispacedLevelSpectrum, Sum.elim_inr, Matrix.mulVec, dotProduct,
        Matrix.submatrix_apply, id_eq]
      exact Finset.sum_congr rfl fun c _ => mul_comm _ _
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs j) _
  have hN := sum_eval_sq_le_equispacedInterpolationFactor_mul_sum_eval_sq_of_natDegree_lt r hdeg
  have hLs := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hL j
  rw [← Finset.mul_sum] at hLs
  have hnorm : ‖WithLp.toLp 2 z‖ ^ 2 = ∑ a : k, z (Sum.inl a) ^ 2 +
      ∑ j : Fin (r + 1), ∑ i : m, z (Sum.inr (j, i)) ^ 2 := by
    rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hC : 0 ≤ equispacedInterpolationFactor r := by
    rw [equispacedInterpolationFactor_def]
    positivity
  calc
    _ ≤ s ^ 2 * (S ^ 2 * ∑ c, (f c).eval ((r : ℝ) + 2) ^ 2) :=
      mul_le_mul_of_nonneg_left hH (sq_nonneg s)
    _ ≤ s ^ 2 * (S ^ 2 * (equispacedInterpolationFactor r *
        ∑ j : Fin (r + 1), ∑ c, (f c).eval ((j : ℝ) + 1) ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hN (sq_nonneg S)) (sq_nonneg s)
    _ = equispacedInterpolationFactor r * S ^ 2 *
        (s ^ 2 * ∑ j : Fin (r + 1), ∑ c, (f c).eval ((j : ℝ) + 1) ^ 2) := by ring
    _ ≤ equispacedInterpolationFactor r * S ^ 2 *
        (∑ j : Fin (r + 1), ∑ i : m, z (Sum.inr (j, i)) ^ 2) :=
      mul_le_mul_of_nonneg_left hLs (mul_nonneg hC (sq_nonneg S))
    _ ≤ equispacedInterpolationFactor r * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (sq_nonneg S))
      rw [hnorm]
      exact le_add_of_nonneg_left (Finset.sum_nonneg fun a _ => sq_nonneg _)

end NLAlib
