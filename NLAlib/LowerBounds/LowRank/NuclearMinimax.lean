/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.Minimax
public import NLAlib.Matrix.Perturbation.Continuity

/-!
# Nuclear-norm minimax lower bounds

Fixed-batch nuclear-norm lower bounds on the positive equispaced hard spectrum.
The unchanged Gaussian overlap and hidden-rotation coupling control missed nuclear mass.
Design: `docs/design/LowerBounds-Nuclear.md`.

## Main results

* In `QueryAlgorithm.IsPassStructured`,
  `measureReal_nuclearNorm_sub_mul_lt_le_of_pass_lt_of_hasLaw_haarFrame`:
  a distributional success bound on Haar rotations.
* `NLAlib.exists_le_measureReal_nuclearNorm_sub_mul_ge_of_pass_lt`: a worst-case hard input.
* `NLAlib.div_lt_of_forall_le_measureReal_nuclearNorm_sub_mul_le_of_pass_lt`:
  the explicit query lower bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]

/-- Orthogonal change of coordinates and small head capture force excess nuclear-norm loss. -/
private theorem le_nuclearNorm_of_orthonormal_range_of_pass_lt (r : ℕ) {b : Type*} [Fintype b]
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    {W : Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ}
    {M : Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ}
    {G : Matrix (k ⊕ (Fin (r + 1) × m)) b ℝ} (hU : HasOrthonormalCols U)
    (hr : LinearMap.range (Uᴴ * W).mulVecLin ≤
      blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m r)) G (r + 1))
    (hgood : ∀ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m r)) G (r + 1),
      ¬ (1 / 4 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2)) :
    Fintype.card m * equispacedNuclearTailFactor r + 2 * (Fintype.card k : ℝ) / 3 ≤
      nuclearNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ - W * M) := by
  classical
  set D := Matrix.diagonal (equispacedLevelSpectrum k m r)
  have heq : U * D * Uᴴ - W * M = U * (D - (Uᴴ * W) * (M * U)) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc U (Uᴴ * W),
      ← Matrix.mul_assoc U Uᴴ, hU.mul_conjTranspose_self, Matrix.one_mul,
      Matrix.mul_assoc W, Matrix.mul_assoc M, hU.mul_conjTranspose_self,
      Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, hU.nuclearNorm_mul_conjTranspose_right, hU.nuclearNorm_mul_left]
  have hle := le_nuclearNorm_diagonal_sub_mul_of_equispacedLevelSpectrum r (Uᴴ * W) (M * U)
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
  have ht' : ∑ a : k, rangeProjector (Uᴴ * W) (Sum.inl a) (Sum.inl a) ≤
      1 / 4 * Fintype.card k := by
    simpa only [(isStarProjection_rangeProjector (Uᴴ * W)).norm_toLp_mulVec_single_sq] using ht
  have hkn : (0 : ℝ) ≤ Fintype.card k := Nat.cast_nonneg _
  dsimp only [D] at *
  nlinarith

/-- A deterministic measurable algorithm using at most $r$ batches cannot attain the optimum
plus $2\lvert k\rvert/3$ on most Haar rotations of the equispaced hard instance.
The width condition is <!-- value equispacedGaussianFactor r -->
$$64\cdot4^{r+1}(q+\lvert k\rvert)\le\lvert m\rvert \,.$$
Its success probability is at most <!-- value equispacedGaussianFactor r -->
$$(r+2)\exp\bigl(-\lvert m\rvert/(2\cdot64\cdot4^{r+1})\bigr) \,.$$ -/
theorem
QueryAlgorithm.IsPassStructured.measureReal_nuclearNorm_sub_mul_lt_le_of_pass_lt_of_hasLaw_haarFrame
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
    μ.real {ω | nuclearNorm
      (U ω * Matrix.diagonal (equispacedLevelSpectrum k m r) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).2) <
      Fintype.card m * equispacedNuclearTailFactor r + 2 * (Fintype.card k : ℝ) / 3} ≤
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
  have hbad :=
    measureReal_exists_mem_blockKrylovSpace_gt_quarter_le_of_hasLaw_gaussianMatrix
      r hG.hasLaw_gaussianMatrix
    (by simp) (by simpa only [Fintype.card_sum, Fintype.card_fin, Nat.cast_add] using hwidth)
  calc _ = μ'.real (Prod.fst ⁻¹' {ω | nuclearNorm (U ω * D * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) D)).1 * (alg.run (hiddenRotationOracle (U ω) D)).2)
          < Fintype.card m * equispacedNuclearTailFactor r +
            2 * (Fintype.card k : ℝ) / 3}) := by
        rw [← Set.prod_univ, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ,
          mul_one]
    _ ≤ _ := measureReal_mono_ae ?_
    _ ≤ _ := hbad
  filter_upwards [hG.ae_range_le_of_isEmpty, ae_hasOrthonormalCols_of_hasLaw_haarFrame hU₁ le_rfl]
    with ω hω hUω hlt
  change nuclearNorm _ < _ at hlt
  change ∃ z ∈ _, _ < _
  by_contra hne
  push Not at hne
  rw [QueryAlgorithm.run_mapOutput] at hω
  exact absurd hlt (not_lt.2 (le_nuclearNorm_of_orthonormal_range_of_pass_lt r hUω hω
    (fun z hz => not_lt.mpr (hne z hz))))


-- Indexed query families require extra elaboration work when transferred through Yao.
set_option maxHeartbeats 800000 in
-- The indexed seed family and its stronger-oracle reduction require extra elaboration work.
/-- A measurable randomized algorithm using at most $r$ batches has an orthogonal hard rotation
on which its nuclear-norm error is at least the optimum plus $2\lvert k\rvert/3$ with
probability
at least one minus the distributional exceptional probability. The hard input is PSD. -/
theorem exists_le_measureReal_nuclearNorm_sub_mul_ge_of_pass_lt
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
        equispacedNuclearTailFactor r * Fintype.card m +
          2 * (Fintype.card k : ℝ) / 3 ≤
            nuclearNorm (A - output.1 * output.2)} := by
  let D := Matrix.diagonal (equispacedLevelSpectrum k m r)
  let threshold := equispacedNuclearTailFactor r * Fintype.card m +
    2 * (Fintype.card k : ℝ) / 3
  let δ := ((r : ℝ) + 2) * Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r)))
  let B : Set (Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)) :=
    {p | HasOrthonormalCols p.1 ∧ threshold ≤ nuclearNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2)}
  have hF : Measurable fun p : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ) =>
      nuclearNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2) := by
    exact (continuous_nuclearNorm.measurable).comp (by fun_prop)
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
    have hbad := hpass'.measureReal_nuclearNorm_sub_mul_lt_le_of_pass_lt_of_hasLaw_haarFrame
      (hp s)
      ((halg.isMeasurable s).comapResponse measurable_fst)
      (HasLaw.id (μ := haarFrame (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)))) hwidth
    change 1 - δ ≤ (haarFrame (k ⊕ (Fin (r + 1) × m))
      (k ⊕ (Fin (r + 1) × m))).real {U | HasOrthonormalCols U ∧
        threshold ≤ nuclearNorm (U * D * Uᴴ - (A'.run (hiddenRotationOracle U D)).1 *
          (A'.run (hiddenRotationOracle U D)).2)}
    have hErr : Measurable fun U :
        Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ =>
        nuclearNorm (U * D * Uᴴ - (A'.run (hiddenRotationOracle U D)).1 *
          (A'.run (hiddenRotationOracle U D)).2) := by
      refine continuous_nuclearNorm.measurable.comp ?_
      exact ((measurable_id.matrix_mul measurable_const).matrix_mul
        (Measurable.matrix_conjTranspose (by fun_prop) measurable_id)).sub
        ((measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun))
    have hthreshold : threshold = Fintype.card m * equispacedNuclearTailFactor r +
        2 * (Fintype.card k : ℝ) / 3 := by
      dsimp only [threshold]
      ring
    apply le_measureReal_hasOrthonormalCols_and_ge _ hErr threshold δ
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


/-- The chosen tail multiplicity makes the admissible excess strictly smaller than the hard
instance's lower-error threshold. -/
private theorem mul_equispacedNuclearTailFactor_lt {r : ℕ} {ε K : ℝ} {m : ℕ}
    (hK : 0 < K) (hε : 0 < ε)
    (hm : m = ⌊K / (ε * ((r : ℝ) + 1) * (r + 2))⌋₊) :
    ε * (m * equispacedNuclearTailFactor r) < 2 * K / 3 := by
  have hR : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hT : 0 < ((r : ℝ) + 1) * (r + 2) := by positivity
  have hmle : (m : ℝ) ≤ K / (ε * ((r : ℝ) + 1) * (r + 2)) := by
    rw [hm]
    exact Nat.floor_le (by positivity)
  have htail : 0 ≤ equispacedNuclearTailFactor r := by
    rw [equispacedNuclearTailFactor_def]
    positivity
  calc ε * (m * equispacedNuclearTailFactor r) ≤
      ε * ((K / (ε * ((r : ℝ) + 1) * (r + 2))) * equispacedNuclearTailFactor r) := by
        gcongr
    _ = K / 2 := by
      rw [equispacedNuclearTailFactor_def]
      field_simp
    _ < 2 * K / 3 := by linarith


omit [DecidableEq k] [DecidableEq m] in
/-- **Fixed-batch nuclear-norm query lower bound**: for every natural $r$, positive target rank,
$0<\varepsilon$ at most <!-- value equispacedAccuracyBound r -->
$$1/(512\cdot4^{r+1}(r+1)(r+2)^2) \,,$$
and $\lvert m\rvert=\lfloor \lvert k\rvert/(\varepsilon(r+1)(r+2))\rfloor$, every measurable
randomized algorithm
using at most $r$ batches and attaining relative nuclear-norm error $1+\varepsilon$ with
probability at least $1/2$ on every PSD input of dimension $\lvert k\rvert+(r+1)\lvert m\rvert$.
The query lower bound is <!-- value equispacedQueryFactor r -->
$$q>\frac{\lvert k\rvert}{256\cdot4^{r+1}(r+1)(r+2)\varepsilon} \,.$$
Constants are conservative and no optimized dependence on the batch count is asserted.
No printed source.
Result: fixed-batch-nuclear-lower-bound -/
theorem div_lt_of_forall_le_measureReal_nuclearNorm_sub_mul_le_of_pass_lt
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
        nuclearNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ≤
          (1 + ε) * nuclearNorm (A - truncatedSVD A (Fintype.card k))}) :
    Fintype.card k / (equispacedQueryFactor r * ε) < q := by
  classical
  have hk1 : (1 : ℝ) ≤ Fintype.card k := Nat.one_le_cast.mpr Fintype.card_pos
  have hkpos : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  by_contra hcon
  obtain ⟨hwidth, hmLarge⟩ :=
    equispacedGaussianFactor_mul_add_le_and_mul_le_of_floor hk1 hε hεr hm (not_lt.mp hcon)
  obtain ⟨U, hU, hfail⟩ := exists_le_measureReal_nuclearNorm_sub_mul_ge_of_pass_lt
    hwidth halg hpass hp ρ
  have hsmall := mul_exp_neg_div_lt_half hmLarge
  set A := U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ
  have hApsd : A.PosSemidef := posSemidef_mul_diagonal_equispacedLevelSpectrum_mul_conjTranspose r U
  have hopt : nuclearNorm (A - truncatedSVD A (Fintype.card k)) =
      Fintype.card m * equispacedNuclearTailFactor r :=
    HasOrthonormalCols.nuclearNorm_sub_truncatedSVD_eq_mul_equispacedNuclearTailFactor r hU
  have hsuccess := hsucc A hApsd
  rw [hopt] at hsuccess
  have hexcess := mul_equispacedNuclearTailFactor_lt hkpos hε hm
  have hrun : Measurable fun s => (alg s).run A.mulVec := by
    have hO : Measurable fun p :
        Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ ×
          (k ⊕ (Fin (r + 1) × m) → ℝ) => p.1.mulVec p.2 := by fun_prop
    exact (halg.measurable_run
      (O := fun B : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ => B.mulVec)
      hO).comp (measurable_id.prodMk measurable_const)
  let F : Set S := {s | Fintype.card m * equispacedNuclearTailFactor r +
      2 * (Fintype.card k : ℝ) / 3 ≤
        nuclearNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2)}
  have hFm : MeasurableSet F := by
    exact measurableSet_le measurable_const
      ((continuous_nuclearNorm.measurable.comp (measurable_const.sub
        ((measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun)))))
  have hsub : {s : S | nuclearNorm (A - ((alg s).run A.mulVec).1 *
      ((alg s).run A.mulVec).2) ≤
        (1 + ε) * (Fintype.card m * equispacedNuclearTailFactor r)} ⊆ Fᶜ := by
    intro s hs hc
    change nuclearNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ≤
      (1 + ε) * (Fintype.card m * equispacedNuclearTailFactor r) at hs
    change Fintype.card m * equispacedNuclearTailFactor r +
      2 * (Fintype.card k : ℝ) / 3 ≤
        nuclearNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) at hc
    nlinarith
  have hcompl := probReal_compl_eq_one_sub (μ := ρ) hFm
  have hmono := measureReal_mono (μ := ρ) hsub
  have hfail' : 1 - ((r : ℝ) + 2) *
      Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r))) ≤ ρ.real F := by
    simpa only [F, A, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, mul_comm,
      mul_left_comm, mul_assoc, div_eq_mul_inv] using hfail
  linarith



end NLAlib
