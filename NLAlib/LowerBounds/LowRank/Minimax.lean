/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.FiniteSpectrum

/-!
# Minimax lower bounds for low-rank approximation

Frobenius minimax lower bounds for any fixed natural batch count. The positive equispaced hard
spectrum has a head at $r+2$ and $r+1$ tail levels. Gaussian overlap estimates and the general
Krylov coupling give a distributional failure bound, a randomized worst-case hard input, and
an explicit query lower bound in the specified dimension. Design:
`docs/design/LowerBounds-FixedBatches.md`.

## Main definitions

* `NLAlib.equispacedQueryFactor`: denominator of the query lower bound.
* `NLAlib.equispacedAccuracyBound`: admissible squared-error accuracy.

For natural $r$, the query factor is <!-- value equispacedQueryFactor r -->
$256\cdot4^{r+1}(r+1)(r+2)$, and the accuracy cutoff is
set to <!-- value equispacedAccuracyBound r -->
$1/(512\cdot4^{r+1}(r+1)(r+2)^2)$.

## Main results

* In `QueryAlgorithm.IsPassStructured`,
  `measureReal_frobNorm_sub_mul_sq_lt_le_of_pass_lt_of_hasLaw_haarFrame` bounds success on Haar
  rotations of the fixed spectrum.
* `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge_of_pass_lt`: a randomized worst-case bound.
* `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt`: the explicit
  fixed-batch query lower bound.
-/

@[expose] public section

namespace NLAlib

/-- **Query factor for fixed-batch Frobenius approximation**: for natural $r$, the
query lower bound uses <!-- value equispacedQueryFactor r -->
$$256\cdot4^{r+1}(r+1)(r+2) \,.$$
Its reciprocal is a conservative fixed-$r$ coefficient of $k/\varepsilon$. -/
noncomputable irreducible_def equispacedQueryFactor (r : ℕ) : ℝ :=
  256 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2)

/-- **Accuracy cutoff for fixed-batch Frobenius approximation**: natural $r$ permits squared
relative-error accuracy at most <!-- value equispacedAccuracyBound r -->
$$1/(512\cdot4^{r+1}(r+1)(r+2)^2) \,.$$
This suffices for the floor and Gaussian dimension conditions for every positive target rank. -/
noncomputable irreducible_def equispacedAccuracyBound (r : ℕ) : ℝ :=
  1 / (512 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2) ^ 2)

end NLAlib

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

section GaussianCapture

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- Scalar comparison used after the interpolation estimate and Gaussian norm bounds. -/
private theorem false_of_interpolation_lt {r : ℕ} {γ t s N sumH : ℝ} (hγ : 2 < γ)
    (ht : 0 < t) (hs : (γ - 2) * t ≤ s) (hN : 0 ≤ N)
    (key : s ^ 2 * sumH ≤ equispacedInterpolationFactor r * (3 * t) ^ 2 * N)
    (hlt : 9 * equispacedInterpolationFactor r / (γ - 2) ^ 2 * N < sumH) : False := by
  let C := equispacedInterpolationFactor r
  have hC : 0 ≤ C := by dsimp [C]; rw [equispacedInterpolationFactor_def]; positivity
  change s ^ 2 * sumH ≤ C * (3 * t) ^ 2 * N at key
  change 9 * C / (γ - 2) ^ 2 * N < sumH at hlt
  have hγ2 : 0 < γ - 2 := by linarith
  have hsp : 0 < s := lt_of_lt_of_le (mul_pos hγ2 ht) hs
  have h1 := mul_lt_mul_of_pos_left hlt (pow_pos hsp 2)
  have hs2 := pow_le_pow_left₀ (mul_nonneg hγ2.le ht.le) hs 2
  have h3 : t ^ 2 ≤ s ^ 2 / (γ - 2) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hγ2 2)]; rw [mul_pow] at hs2; linarith [hs2]
  have h2 : 9 * C * t ^ 2 * N ≤ s ^ 2 * (9 * C / (γ - 2) ^ 2 * N) := by
    calc 9 * C * t ^ 2 * N = 9 * C * N * t ^ 2 := by ring
      _ ≤ 9 * C * N * (s ^ 2 / (γ - 2) ^ 2) := by gcongr
      _ = s ^ 2 * (9 * C / (γ - 2) ^ 2 * N) := by ring
  have key' : C * (3 * t) ^ 2 * N = 9 * C * t ^ 2 * N := by ring
  linarith [h1, key, h2, key']

omit [DecidableEq k] [DecidableEq m] in
/-- Lower Gram bound for an arbitrary tail block. -/
private theorem measureReal_not_gram_tail_le_of_pass_lt {r : ℕ}
    {b : Type*} [Fintype b] [DecidableEq b]
    {G : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) b) μ)
    (j : Fin (r + 1)) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card b : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) - √(Fintype.card b : ℝ) - t) ^ 2 •
      (1 : Matrix b b ℝ) ≤ ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id} ≤ Real.exp (-t ^ 2 / 2) :=
  measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG (fun i i' h => by simpa using h)
      Function.injective_id) ht htn

/-- Gaussian head-capture estimate with a free deviation parameter. -/
private theorem
measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_pass_lt_of_hasLaw_gaussianMatrix
    (r : ℕ)
    {b : Type*} [Fintype b] {G : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) b) μ)
    {γ : ℝ} (hγ : 2 < γ)
    (hkb : Fintype.card k ≤ Fintype.card b) (hbm : γ ^ 2 * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace
      (Matrix.diagonal (equispacedLevelSpectrum k m r)) (G ω) (r + 1),
        9 * equispacedInterpolationFactor r / (γ - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 <
          ∑ a : k, z (Sum.inl a) ^ 2} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  classical
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hγ0 : 0 < γ := by linarith
  set a : ℝ := √(Fintype.card m : ℝ) with ha_def
  set c : ℝ := √(Fintype.card b : ℝ) with hc_def
  set d : ℝ := √(Fintype.card k : ℝ) with hd_def
  set t : ℝ := a / γ with ht_def
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = Fintype.card m := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc2 : c ^ 2 = Fintype.card b := Real.sq_sqrt (Nat.cast_nonneg _)
  have ht0 : 0 ≤ t := div_nonneg ha0 hγ0.le
  have hat : a = γ * t := by rw [ht_def]; field_simp
  have hct : c ≤ t := by
    have h1 : (c * γ) ^ 2 ≤ a ^ 2 := by
      rw [mul_pow, ha2, hc2]; linarith [hbm]
    rw [ht_def, le_div_iff₀ hγ0]
    nlinarith [mul_nonneg hc0 hγ0.le]
  have htn : t ≤ a - c := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ γ - 2) ht0]
  have hdc : d ≤ c := Real.sqrt_le_sqrt (Nat.cast_le.mpr hkb)
  have hexp : Real.exp (-t ^ 2 / 2) = Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
    congr 1
    rw [ht_def, div_pow, ha2]
    ring
  -- tail blocks: the lower Gram bound fails with probability at most `exp (-t^2/2)` each
  have hA : μ.real (⋃ j : Fin (r + 1), {ω | ¬ (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
      ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ≤ (r + 1) * Real.exp (-t ^ 2 / 2) := by
    refine (measureReal_iUnion_fintype_le _).trans ((Finset.sum_le_sum fun j _ =>
      measureReal_not_gram_tail_le_of_pass_lt hG j ht0 htn).trans ?_)
    simp
  -- head block: the spectral norm is large with probability at most `exp (-t^2/2)`
  have hB : μ.real {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)} ≤
      Real.exp (-t ^ 2 / 2) :=
    measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
      (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG Sum.inl_injective Function.injective_id) ht0
  refine le_trans (measureReal_mono (s₂ := (⋃ j : Fin (r + 1), {ω | ¬ (a - c - t) ^ 2 •
      (1 : Matrix b b ℝ) ≤ ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ∪
      {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)}) (fun ω hω => ?_))
    ((measureReal_union_le _ _).trans ?_)
  · obtain ⟨z, hz, hlt⟩ := hω
    by_contra hnot
    have hs : ∀ j : Fin (r + 1), (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
        ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
          (G ω).submatrix (fun i : m => Sum.inr (j, i)) id := by
      intro j
      by_contra h
      exact hnot (Or.inl (Set.mem_iUnion.2 ⟨j, h⟩))
    have hS : specNorm ((G ω).submatrix Sum.inl id) ≤ 3 * t := by
      by_contra h
      have hB' : d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id) := by
        linarith [not_le.1 h]
      exact hnot (Or.inr hB')
    have key :=
      mul_sum_sq_le_equispacedInterpolationFactor_mul_norm_sq_of_mem_blockKrylovSpace r hs hS hz
    have hsum : 0 < ∑ a : k, z (Sum.inl a) ^ 2 :=
      lt_of_le_of_lt (by rw [equispacedInterpolationFactor_def]; positivity) hlt
    have hne : Nonempty k := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hsum
    have hb1 : 1 ≤ Fintype.card b := le_trans (Fintype.card_pos (α := k)) hkb
    have hb1' : (1 : ℝ) ≤ Fintype.card b := by exact_mod_cast hb1
    have hm : (0 : ℝ) < Fintype.card m :=
      lt_of_lt_of_le (pow_pos hγ0 2) ((le_mul_of_one_le_right (sq_nonneg γ) hb1').trans hbm)
    have ha_pos : 0 < a := Real.sqrt_pos.2 hm
    have ht_pos : 0 < t := div_pos ha_pos hγ0
    have hs_lb : (γ - 2) * t ≤ a - c - t := by linarith [hat, hct]
    exact false_of_interpolation_lt hγ ht_pos hs_lb (sq_nonneg _) key hlt
  · rw [← hexp]
    linarith [hA, hB]


/-- The numerical Gaussian deviation used in the fixed-batch theorem. -/
private theorem equispaced_deviation (r : ℕ) :
    2 < 8 * (2 : ℝ) ^ (r + 1) ∧
      (8 * (2 : ℝ) ^ (r + 1)) ^ 2 = equispacedGaussianFactor r ∧
      9 * equispacedInterpolationFactor r / (8 * (2 : ℝ) ^ (r + 1) - 2) ^ 2 ≤ 1 / 4 := by
  have hp : (1 : ℝ) ≤ 2 ^ (r + 1) := one_le_pow₀ (by norm_num)
  have hpow : ((2 : ℝ) ^ (r + 1)) ^ 2 = 4 ^ (r + 1) := by
    rw [pow_two, ← mul_pow]
    norm_num
  have hγ : 2 < 8 * (2 : ℝ) ^ (r + 1) := by linarith
  refine ⟨hγ, ?_, ?_⟩
  · rw [equispacedGaussianFactor_def, mul_pow, hpow]
    norm_num
  · rw [div_le_iff₀ (sq_pos_of_pos (sub_pos.mpr hγ)), equispacedInterpolationFactor_def]
    nlinarith [sq_nonneg (2 * (2 : ℝ) ^ (r + 1) - 2)]

/-- Under the selected width condition, a Gaussian Krylov space rarely captures a quarter of
its norm in the head eigenspace. -/
private theorem measureReal_exists_mem_blockKrylovSpace_gt_quarter_le
    (r : ℕ) {b : Type*} [Fintype b]
    {G : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) b) μ)
    (hkb : Fintype.card k ≤ Fintype.card b)
    (hbm : equispacedGaussianFactor r * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace
      (Matrix.diagonal (equispacedLevelSpectrum k m r)) (G ω) (r + 1),
      1 / 4 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r))) := by
  have := hG.isProbabilityMeasure
  obtain ⟨hγ, hγsq, hcoeff⟩ := equispaced_deviation r
  have hbad :=
    measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_pass_lt_of_hasLaw_gaussianMatrix
    r hG hγ hkb (by rwa [hγsq])
  rw [hγsq] at hbad
  refine (measureReal_mono fun ω hω => ?_).trans hbad
  obtain ⟨z, hz, hlt⟩ := hω
  exact ⟨z, hz, (mul_le_mul_of_nonneg_right hcoeff (sq_nonneg _)).trans_lt hlt⟩

end GaussianCapture

/-- Orthogonal change of coordinates and small head capture force excess Frobenius loss. -/
private theorem le_frobNorm_of_orthonormal_range_of_pass_lt (r : ℕ) {b : Type*} [Fintype b]
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    {W : Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ}
    {M : Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ}
    {G : Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ} (hU : HasOrthonormalCols U)
    (hr : LinearMap.range (Uᴴ * W).mulVecLin ≤
      blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m r)) G (r + 1))
    (hgood : ∀ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m r)) G (r + 1),
      ¬ (1 / 4 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2)) :
    Fintype.card m * equispacedTailFactor r + (2 * (r : ℝ) + 3) * Fintype.card k / 2 ≤
      frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ - W * M) ^ 2 := by
  classical
  set D := Matrix.diagonal (equispacedLevelSpectrum k m r)
  have heq : U * D * Uᴴ - W * M = U * (D - (Uᴴ * W) * (M * U)) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc U (Uᴴ * W),
      ← Matrix.mul_assoc U Uᴴ, hU.mul_conjTranspose_self, Matrix.one_mul,
      Matrix.mul_assoc W, Matrix.mul_assoc M, hU.mul_conjTranspose_self,
      Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, hU.conjTranspose.frobNorm_mul_right, hU.frobNorm_mul_left]
  have hle := le_frobNorm_diagonal_sub_mul_sq_of_equispacedLevelSpectrum r (Uᴴ * W) (M * U)
  have ht : ∑ a : k, ‖WithLp.toLp 2 (rangeProjector (Uᴴ * W) *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2
      ≤ 1 / 4 * Fintype.card k := by
    let P := rangeProjector (Uᴴ * W)
    have hP : IsStarProjection P := isStarProjection_rangeProjector _
    have hsum := hP.sum_head_mass_sq_le (c := 1 / 4) (by norm_num) (fun a => by
      have hz : P *ᵥ Pi.single (Sum.inl a) 1 ∈ LinearMap.range (Uᴴ * W).mulVecLin := by
        rw [← range_rangeProjector]
        exact ⟨_, rfl⟩
      have h1 := hgood _ (hr hz)
      rw [not_lt, EuclideanSpace.norm_toLp_sq_eq_sum_sq] at h1
      simpa only [Matrix.mulVec_single_one, Matrix.col_apply] using h1)
    simpa only [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Matrix.mulVec_single_one,
      Matrix.col_apply, P] using hsum
  have hkn : (0 : ℝ) ≤ Fintype.card k := Nat.cast_nonneg _
  have hrn : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hnon := mul_nonneg (by positivity : 0 ≤ 2 * (r : ℝ) + 3)
    (sub_nonneg.mpr ht)
  dsimp only [D] at *
  nlinarith

/-- A deterministic measurable algorithm using at most $r$ batches cannot attain the optimum
plus $(2r+3)\lvert k\rvert/2$ on most Haar rotations of the equispaced hard instance.
The width condition is <!-- value equispacedGaussianFactor r -->
$$64\cdot4^{r+1}(q+\lvert k\rvert)\le\lvert m\rvert \,.$$
Its success probability is at most <!-- value equispacedGaussianFactor r -->
$$(r+2)\exp\bigl(-\lvert m\rvert/(2\cdot64\cdot4^{r+1})\bigr) \,.$$ -/
theorem
QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_pass_lt_of_hasLaw_haarFrame
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r q : ℕ}
    {alg : QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      ((k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < r)
    (halg : alg.IsMeasurable)
    {U : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin (r + 1) × m))
      (k ⊕ (Fin (r + 1) × m))) μ)
    (hwidth : equispacedGaussianFactor r * (q + Fintype.card k) ≤ Fintype.card m) :
    μ.real {ω | frobNorm
      (U ω * Matrix.diagonal (equispacedLevelSpectrum k m r) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).2) ^ 2 <
      Fintype.card m * equispacedTailFactor r + (2 * (r : ℝ) + 3) * Fintype.card k / 2} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r))) := by
  have := hU.isProbabilityMeasure
  set D := Matrix.diagonal (equispacedLevelSpectrum k m r)
  set μ' := μ.prod (gaussianMatrix (k ⊕ (Fin (r + 1) × m)) (Fin q ⊕ k))
  have hU₁ : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin (r + 1) × m)) (Fin q ⊕ k) ℝ => U p.1)
      (haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m))) μ' :=
    hU.comp measurePreserving_fst.hasLaw
  obtain ⟨G, hG⟩ := (hpass.mapOutput Prod.fst).exists_isKrylovCoupling_of_hasLaw_haarFrame
    hp (halg.mapOutput measurable_fst) D
    (0 : Matrix (k ⊕ (Fin (r + 1) × m)) (Fin 0) ℝ) hU₁
    measurePreserving_snd.hasLaw (indepFun_prod₀ hU.aemeasurable aemeasurable_id)
  have hbad := measureReal_exists_mem_blockKrylovSpace_gt_quarter_le r hG.hasLaw_gaussianMatrix
    (by simp) (by simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hwidth)
  calc _ = μ'.real (Prod.fst ⁻¹' {ω | frobNorm (U ω * D * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) D)).1 * (alg.run (hiddenRotationOracle (U ω) D)).2)
          ^ 2 < Fintype.card m * equispacedTailFactor r +
            (2 * (r : ℝ) + 3) * Fintype.card k / 2}) := by
        rw [← Set.prod_univ, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ,
          mul_one]
    _ ≤ _ := measureReal_mono_ae ?_
    _ ≤ _ := hbad
  filter_upwards [hG.ae_range_le_of_isEmpty, ae_hasOrthonormalCols_of_hasLaw_haarFrame hU₁ le_rfl]
    with ω hω hUω hlt
  change frobNorm _ ^ 2 < _ at hlt
  change ∃ z ∈ _, _ < _
  by_contra hne
  push Not at hne
  rw [QueryAlgorithm.run_mapOutput] at hω
  exact absurd hlt (not_lt.2 (le_frobNorm_of_orthonormal_range_of_pass_lt r hUω hω
    (fun z hz => not_lt.mpr (hne z hz))))


/-- A scalar lower-tail bound and almost-sure orthogonality give a joint lower bound. -/
private theorem le_measureReal_orthogonal_and_ge {n : Type*} [Fintype n] [DecidableEq n]
    (F : Matrix n n ℝ → ℝ) (hF : Measurable F) (a δ : ℝ)
    (hbad : (haarFrame n n).real {U | F U < a} ≤ δ) :
    1 - δ ≤ (haarFrame n n).real {U | HasOrthonormalCols U ∧ a ≤ F U} := by
  have hBm : MeasurableSet {U | F U < a} := measurableSet_lt hF measurable_const
  have hcomp := probReal_compl_eq_one_sub (μ := haarFrame n n) hBm
  have hmono : (haarFrame n n).real {U | F U < a}ᶜ ≤
      (haarFrame n n).real {U | HasOrthonormalCols U ∧ a ≤ F U} := by
    refine measureReal_mono_ae ?_ (measure_ne_top _ _)
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame
      (HasLaw.id (μ := haarFrame n n)) le_rfl] with U hU hnot
    exact ⟨hU, not_lt.mp hnot⟩
  rw [hcomp] at hmono
  linarith

-- Indexed query families require extra elaboration work when transferred through Yao.
set_option maxHeartbeats 800000 in
-- The indexed seed family and its stronger-oracle reduction require extra elaboration work.
/-- A measurable randomized algorithm using at most $r$ batches has an orthogonal hard rotation
on which its squared Frobenius error is at least the optimum plus $(2r+3)\lvert k\rvert/2$ with
probability
at least one minus the distributional exceptional probability. The hard input is PSD. -/
theorem exists_le_measureReal_frobNorm_sub_mul_sq_ge_of_pass_lt
    {r q : ℕ} (hwidth : equispacedGaussianFactor r * (q + Fintype.card k) ≤ Fintype.card m)
    {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ∃ U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      HasOrthonormalCols U ∧
      1 - ((r : ℝ) + 2) *
        Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r))) ≤
      ρ.real {s | let A := U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ
        let output := (alg s).run A.mulVec
        equispacedTailFactor r * Fintype.card m +
          ((2 * r + 3 : ℕ) : ℝ) / 2 * Fintype.card k ≤
            frobNorm (A - output.1 * output.2) ^ 2} := by
  let D := Matrix.diagonal (equispacedLevelSpectrum k m r)
  let threshold := equispacedTailFactor r * Fintype.card m +
    ((2 * r + 3 : ℕ) : ℝ) / 2 * Fintype.card k
  let δ := ((r : ℝ) + 2) * Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r)))
  let B : Set (Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)) :=
    {p | HasOrthonormalCols p.1 ∧ threshold ≤ frobNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2) ^ 2}
  have hF : Measurable fun p : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ) =>
      frobNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2) ^ 2 := by
    exact ((measurable_frobNorm).comp (by fun_prop)).pow_const 2
  have hB : MeasurableSet B :=
    (measurable_fst isClosed_setOf_hasOrthonormalCols.measurableSet).inter
      (measurableSet_le measurable_const hF)
  have hO : Measurable (Function.uncurry fun
      (U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ)
      (x : k ⊕ (Fin (r + 1) × m) → ℝ) => hiddenRotationOracle U D x) :=
    Measurable.hiddenRotationOracle measurable_fst measurable_snd _
  have hA : QueryAlgorithm.IsMeasurableFamily fun s => (alg s).comapResponse
      (R' := (k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) Prod.fst :=
    halg.comapResponse measurable_fst
  have hsucc : ∀ s, 1 - δ ≤
      (haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m))).real
        {U | (U, ((alg s).comapResponse Prod.fst).run (hiddenRotationOracle U D)) ∈ B} := by
    intro s
    let A' := (alg s).comapResponse
      (R' := (k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) Prod.fst
    have hrun : Measurable fun U => A'.run (hiddenRotationOracle U D) :=
      ((halg.isMeasurable s).comapResponse measurable_fst).measurable_run hO
    have hpass' := (hpass s).comapResponse
      (R' := (k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) Prod.fst
    have hbad := hpass'.measureReal_frobNorm_sub_mul_sq_lt_le_of_pass_lt_of_hasLaw_haarFrame
      (hp s)
      ((halg.isMeasurable s).comapResponse measurable_fst)
      (HasLaw.id (μ := haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)))) hwidth
    change 1 - δ ≤ (haarFrame (k ⊕ (Fin (r + 1) × m))
      (k ⊕ (Fin (r + 1) × m))).real {U | HasOrthonormalCols U ∧
        threshold ≤ frobNorm (U * D * Uᴴ - (A'.run (hiddenRotationOracle U D)).1 *
          (A'.run (hiddenRotationOracle U D)).2) ^ 2}
    have hErr : Measurable fun U :
        Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ =>
        frobNorm (U * D * Uᴴ - (A'.run (hiddenRotationOracle U D)).1 *
          (A'.run (hiddenRotationOracle U D)).2) ^ 2 := by
      refine (measurable_frobNorm.comp ?_).pow_const 2
      exact ((measurable_id.matrix_mul measurable_const).matrix_mul
        (Measurable.matrix_conjTranspose (by fun_prop) measurable_id)).sub
        ((measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun))
    have hthreshold : threshold = Fintype.card m * equispacedTailFactor r +
        (2 * (r : ℝ) + 3) * Fintype.card k / 2 := by
      dsimp only [threshold]
      push_cast
      ring
    apply le_measureReal_orthogonal_and_ge _ hErr threshold δ
    change _ ≤ δ at hbad
    rw [← hthreshold] at hbad
    exact hbad
  obtain ⟨U, hU⟩ := hA.exists_le_measureReal_run_mem_of_forall (ρ := ρ)
    (ν := haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m))) hO hB hsucc
  by_cases hUo : HasOrthonormalCols U
  · refine ⟨U, hUo, hU.trans (measureReal_mono fun s hs => ?_)⟩
    have h := hs.2
    rw [QueryAlgorithm.run_comapResponse] at h
    exact h
  · exact ⟨1, hasOrthonormalCols_one, hU.trans (measureReal_mono fun s hs => absurd hs.1 hUo)⟩


/-- Numerical floor conditions forced by the selected accuracy cutoff. -/
private theorem equispaced_floor_width {r : ℕ} {ε K : ℝ} {q m : ℕ}
    (hK : 1 ≤ K) (hε : 0 < ε) (hεr : ε ≤ equispacedAccuracyBound r)
    (hm : m = ⌊K / (ε * ((r : ℝ) + 1) * (r + 2))⌋₊)
    (hq : (q : ℝ) ≤ K / (equispacedQueryFactor r * ε)) :
    equispacedGaussianFactor r * (q + K) ≤ m ∧
      4 * equispacedGaussianFactor r * (r + 2) ≤ m := by
  let A := equispacedGaussianFactor r
  let T := ((r : ℝ) + 1) * (r + 2)
  let x := K / (ε * T)
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hC : (0 : ℝ) < 4 ^ (r + 1) := pow_pos (by norm_num) _
  have hA : 0 < A := by dsimp [A]; rw [equispacedGaussianFactor_def]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hcut : ε * T * (8 * A * (r + 2)) ≤ 1 := by
    rw [equispacedAccuracyBound_def, le_div_iff₀ (by positivity)] at hεr
    dsimp [T, A]
    rw [equispacedGaussianFactor_def]
    nlinarith [hεr]
  have hx : 8 * A * (r + 2) * K ≤ x := by
    rw [le_div_iff₀ (mul_pos hε hT)]
    calc 8 * A * (r + 2) * K * (ε * T) = K * (ε * T * (8 * A * (r + 2))) := by ring
      _ ≤ K * 1 := mul_le_mul_of_nonneg_left hcut (by linarith)
      _ = K := mul_one _
  have hA1 : 1 ≤ A := by
    dsimp [A]
    rw [equispacedGaussianFactor_def]
    have h4 : (1 : ℝ) ≤ 4 ^ (r + 1) := one_le_pow₀ (by norm_num)
    nlinarith
  have hx8 : 8 * A * (r + 2) ≤ x :=
    (le_mul_of_one_le_right (by positivity) hK).trans hx
  have hx2 : 2 ≤ x := by nlinarith
  have hmx : x / 2 ≤ (m : ℝ) := by
    have hf : x - 1 < (m : ℝ) := by
      rw [hm]
      simpa [x, T, mul_assoc] using Nat.sub_one_lt_floor x
    linarith
  have hqx : (q : ℝ) ≤ x / (4 * A) := by
    convert hq using 1
    dsimp [x, A, T]
    rw [div_div]
    congr 1
    rw [equispacedQueryFactor_def, equispacedGaussianFactor_def]
    ring
  have hqmul : A * q ≤ x / 4 := by
    rw [le_div_iff₀ (by positivity : 0 < 4 * A)] at hqx
    nlinarith
  have hKmul : A * K ≤ x / 4 := by
    have hpos : 0 ≤ (8 * A * (r + 2) - 4 * A) * K :=
      mul_nonneg (by nlinarith [mul_nonneg hA.le hR]) (by linarith)
    nlinarith
  exact ⟨by nlinarith, by nlinarith⟩

/-- The chosen tail multiplicity makes the admissible excess strictly smaller than the hard
instance's lower-error threshold. -/
private theorem mul_equispacedTailFactor_lt {r : ℕ} {ε K : ℝ} {m : ℕ}
    (hK : 0 < K) (hε : 0 < ε)
    (hm : m = ⌊K / (ε * ((r : ℝ) + 1) * (r + 2))⌋₊) :
    ε * (m * equispacedTailFactor r) < (2 * (r : ℝ) + 3) * K / 2 := by
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hT : 0 < ((r : ℝ) + 1) * (r + 2) := by positivity
  have hmle : (m : ℝ) ≤ K / (ε * ((r : ℝ) + 1) * (r + 2)) := by
    rw [hm]
    exact Nat.floor_le (by positivity)
  have htail : 0 ≤ equispacedTailFactor r := by rw [equispacedTailFactor_def]; positivity
  calc ε * (m * equispacedTailFactor r) ≤
      ε * ((K / (ε * ((r : ℝ) + 1) * (r + 2))) * equispacedTailFactor r) := by gcongr
    _ = K * (2 * (r : ℝ) + 3) / 6 := by
      rw [equispacedTailFactor_def]
      field_simp
    _ < (2 * (r : ℝ) + 3) * K / 2 := by nlinarith

/-- A sufficiently large tail makes the Gaussian exceptional probability less than one half. -/
private theorem equispaced_exceptional_lt_half {r m : ℕ}
    (hm : 4 * equispacedGaussianFactor r * (r + 2) ≤ m) :
    ((r : ℝ) + 2) * Real.exp (-(m / (2 * equispacedGaussianFactor r))) < 1 / 2 := by
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hA : 0 < equispacedGaussianFactor r := by rw [equispacedGaussianFactor_def]; positivity
  have hy : 2 * ((r : ℝ) + 2) ≤ m / (2 * equispacedGaussianFactor r) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hexp : 2 * ((r : ℝ) + 2) < Real.exp (m / (2 * equispacedGaussianFactor r)) := by
    have h := Real.add_one_le_exp (m / (2 * equispacedGaussianFactor r))
    linarith
  have hinv : Real.exp (-(m / (2 * equispacedGaussianFactor r))) *
      Real.exp (m / (2 * equispacedGaussianFactor r)) = 1 := by rw [← Real.exp_add]; simp
  nlinarith [mul_pos (Real.exp_pos (-(m / (2 * equispacedGaussianFactor r))))
    (sub_pos.mpr hexp)]

omit [DecidableEq k] [DecidableEq m] in
/-- **Fixed-batch Frobenius query lower bound**: for every natural $r$, positive target rank,
$0<\varepsilon$ at most <!-- value equispacedAccuracyBound r -->
$$1/(512\cdot4^{r+1}(r+1)(r+2)^2) \,,$$
and $\lvert m\rvert=\lfloor \lvert k\rvert/(\varepsilon(r+1)(r+2))\rfloor$, every measurable
randomized algorithm
using at most $r$ batches and attaining squared relative Frobenius error $1+\varepsilon$ with
probability at least $1/2$ on every PSD input of dimension $\lvert k\rvert+(r+1)\lvert m\rvert$.
The query lower bound is <!-- value equispacedQueryFactor r -->
$$q>\frac{\lvert k\rvert}{256\cdot4^{r+1}(r+1)(r+2)\varepsilon} \,.$$
Constants are conservative and no optimized dependence on the batch count is asserted.
No printed source.
Result: fixed-batch-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
    [Nonempty k] {r : ℕ} {ε : ℝ} {q : ℕ} (hε : 0 < ε)
    (hεr : ε ≤ equispacedAccuracyBound r)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) /
      (ε * ((r : ℝ) + 1) * (r + 2))⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      A.PosSemidef → 1 / 2 ≤ ρ.real {s |
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
          (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (equispacedQueryFactor r * ε) < q := by
  classical
  have hk1 : (1 : ℝ) ≤ Fintype.card k := Nat.one_le_cast.mpr Fintype.card_pos
  have hkpos : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  by_contra hcon
  obtain ⟨hwidth, hmLarge⟩ := equispaced_floor_width hk1 hε hεr hm (not_lt.mp hcon)
  obtain ⟨U, hU, hfail⟩ := exists_le_measureReal_frobNorm_sub_mul_sq_ge_of_pass_lt
    hwidth halg hpass hp ρ
  have hsmall := equispaced_exceptional_lt_half hmLarge
  set A := U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ
  have hApsd : A.PosSemidef := posSemidef_mul_diagonal_equispacedLevelSpectrum_mul_conjTranspose r U
  have hopt : frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2 =
      Fintype.card m * equispacedTailFactor r :=
    HasOrthonormalCols.frobNorm_sub_truncatedSVD_sq_eq_mul_equispacedTailFactor r hU
  have hsuccess := hsucc A hApsd
  rw [hopt] at hsuccess
  have hexcess := mul_equispacedTailFactor_lt hkpos hε hm
  have hrun : Measurable fun s => (alg s).run A.mulVec := by
    have hO : Measurable fun p :
        Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
          (k ⊕ (Fin (r + 1) × m) → ℝ) => p.1.mulVec p.2 := by fun_prop
    exact (halg.measurable_run
      (O := fun B : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ => B.mulVec)
      hO).comp (measurable_id.prodMk measurable_const)
  let F : Set S := {s | Fintype.card m * equispacedTailFactor r +
      (2 * (r : ℝ) + 3) * Fintype.card k / 2 ≤
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2}
  have hFm : MeasurableSet F := by
    exact measurableSet_le measurable_const
      ((measurable_frobNorm.comp (measurable_const.sub
        ((measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun)))).pow_const 2)
  have hsub : {s : S | frobNorm (A - ((alg s).run A.mulVec).1 *
      ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * (Fintype.card m * equispacedTailFactor r)} ⊆ Fᶜ := by
    intro s hs hc
    change frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
      (1 + ε) * (Fintype.card m * equispacedTailFactor r) at hs
    change Fintype.card m * equispacedTailFactor r +
      (2 * (r : ℝ) + 3) * Fintype.card k / 2 ≤
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 at hc
    nlinarith
  have hcompl := probReal_compl_eq_one_sub (μ := ρ) hFm
  have hmono := measureReal_mono (μ := ρ) hsub
  have hfail' : 1 - ((r : ℝ) + 2) *
      Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r))) ≤ ρ.real F := by
    simpa only [F, A, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_comm,
      mul_left_comm, mul_assoc, div_eq_mul_inv] using hfail
  linarith


end NLAlib
