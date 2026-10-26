/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.FewPasses
public import NLAlib.LowerBounds.QueryModel.Yao
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Polynomial.Interpolation.DividedDifference
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlibScaffold.LowerBounds.QueryModel.HiddenRotation

/-!
# Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ products (scaffold)

Every randomized algorithm that makes its matrix–vector products in two passes (two blocks, the
second chosen from the responses to the first) and returns a rank-$k$ approximation within
$(1 + \varepsilon)$ of the best in Frobenius norm needs more than $k/(6400\varepsilon)$ products in
the worst case; one pass is a special case, and in spectral norm two passes need a number of
products proportional to the dimension. Randomized SVD meets the Frobenius rate with two passes,
so it is rate-optimal among two-pass algorithms. Stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.6; research note OP5
(`~/nlalib-harness/reports/OP5-TwoPassMinimax.md`, Theorems A and C, Corollary B).

The hard instance is $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$, $\mathbf{U}$ Haar,
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$
(`NLAlib.equispacedLevelSpectrum k m 2`). Three steps: the error is at least the optimum
$14m$ plus $7(k - t)$, $t$ the head mass captured by the output range; by the Krylov coupling the
rotated output range lies in $\mathcal{K}_3(\mathbf{D}, \mathbf{G})$ for a Gaussian $\mathbf{G}$
with $q + k$ columns; a vector of that space is $\mathbf{G}_\lambda\mathbf{p}(\lambda)$ on level
$\lambda$ with $\deg\mathbf{p} \le 2$, and $\mathbf{p}(4) = \mathbf{p}(1) - 3\mathbf{p}(2) +
3\mathbf{p}(3)$, so the head part is small unless $q + k$ is of the order of $m$.

## Main results

* one deterministic two-pass algorithm, Frobenius and spectral:
  `NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
  `NLAlib.QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
* `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`: randomized, worst case.
* `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`,
  `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one`,
  `NLAlib.lt_of_forall_le_measureReal_specNorm_sub_mul_le`: the query counts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k m : Type*} [Fintype k]
  [Fintype m] [DecidableEq k] [DecidableEq m]

/-- Head mass of a projector: if every column $\mathbf{P}\mathbf{e}_a$ ($a$ in the head)
has head mass at most $c$ times its norm, then
$\sum_a \|\mathbf{P}\mathbf{e}_a\|^2 \le c\,\lvert\kappa\rvert$.
Proof: $\|\mathbf{P}\mathbf{e}_a\|^2 = \mathbf{P}_{aa}$; the head block satisfies
$\sum_{a,b} \mathbf{P}_{ba}^2 \ge (\operatorname{tr})^2/\lvert\kappa\rvert$ (Cauchy–Schwarz) and
$\le c\operatorname{tr}$. -/
private lemma sum_head_mass_sq_le {κ r : Type*} [Fintype κ] [Fintype r]
    (P : Matrix (κ ⊕ r) (κ ⊕ r) ℝ) (hP : IsStarProjection P) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2 ≤ c * ∑ i, P i (Sum.inl a) ^ 2) :
    ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 ≤ c * Fintype.card κ := by
  have hsymm : ∀ i j, P j i = P i j := fun i j => by
    have h := congrFun (congrFun hP.conjTranspose_eq j) i
    have h' : P i j = P j i := by simpa [Matrix.conjTranspose_apply] using h
    exact h'.symm
  have hdiag : ∀ a : κ, ∑ i, P i (Sum.inl a) ^ 2 = P (Sum.inl a) (Sum.inl a) := by
    intro a
    have key : ∀ i, P (Sum.inl a) i = P i (Sum.inl a) := fun i => (hsymm (Sum.inl a) i).symm
    have h := congrFun (congrFun hP.mul_self (Sum.inl a)) (Sum.inl a)
    rw [Matrix.mul_apply] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [key i, sq]
  have hT : ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 = ∑ a : κ, P (Sum.inl a) (Sum.inl a) :=
    Finset.sum_congr rfl fun a _ => hdiag a
  have hS2 : ∑ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2
      ≤ c * ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => h a
  have hsq : ∑ a : κ, P (Sum.inl a) (Sum.inl a) ^ 2
      ≤ ∑ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2 :=
    Finset.sum_le_sum fun a _ => Finset.single_le_sum (f := fun b : κ =>
      P (Sum.inl b) (Sum.inl a) ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ a)
  have hCS : (∑ a : κ, P (Sum.inl a) (Sum.inl a)) ^ 2
      ≤ Fintype.card κ * ∑ a : κ, ∑ b : κ, P (Sum.inl b) (Sum.inl a) ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := Finset.univ)
      (f := fun a : κ => P (Sum.inl a) (Sum.inl a))
    simp only [Finset.card_univ] at this
    exact this.trans (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
  rw [← hT] at hCS
  have hT0 : 0 ≤ ∑ a : κ, ∑ i, P i (Sum.inl a) ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hk : (0 : ℝ) ≤ Fintype.card κ := Nat.cast_nonneg _
  rcases hT0.eq_or_lt with h0 | h0
  · rw [← h0]; exact mul_nonneg hc hk
  · nlinarith [mul_le_mul_of_nonneg_left hS2 hk]

/-- Measure of a set pulled back along the first factor of a product with a probability law:
$\mu(S) \le (\mu\otimes\nu)(\mathrm{fst}^{-1}S)$. -/
private lemma measureReal_le_prod_fst {Ω₂ : Type*} [MeasurableSpace Ω₂] (ν : Measure Ω₂)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (S : Set Ω) :
    μ.real S ≤ (μ.prod ν).real (Prod.fst ⁻¹' S) := by
  set H := toMeasurable (μ.prod ν) (Prod.fst ⁻¹' S) with hH
  have hHm : MeasurableSet H := measurableSet_toMeasurable _ _
  have hsub : Prod.fst ⁻¹' S ⊆ H := subset_toMeasurable _ _
  have hfH : (μ.prod ν) H = (μ.prod ν) (Prod.fst ⁻¹' S) := measure_toMeasurable _
  have hsec : ∀ x ∈ S, (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H) := by
    intro x hx
    have huniv : Prod.mk x ⁻¹' H = Set.univ := by
      ext y
      exact ⟨fun _ => trivial, fun _ => hsub (show (x, y) ∈ Prod.fst ⁻¹' S from hx)⟩
    rw [huniv, measure_univ]
  have hAm : MeasurableSet {x | (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H)} :=
    measurableSet_le measurable_const (measurable_measure_prodMk_left hHm)
  have hmarkov := mul_meas_ge_le_lintegral₀
    (μ := μ) (f := fun x => ν (Prod.mk x ⁻¹' H))
    (measurable_measure_prodMk_left hHm).aemeasurable 1
  have hle : μ S ≤ (μ.prod ν) (Prod.fst ⁻¹' S) := by
    rw [← hfH, Measure.prod_apply hHm]
    calc μ S ≤ μ {x | (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H)} :=
          measure_mono fun x hx => hsec x hx
      _ = 1 * μ {x | (1 : ENNReal) ≤ ν (Prod.mk x ⁻¹' H)} := (one_mul _).symm
      _ ≤ _ := hmarkov
  rw [measureReal_def, measureReal_def]
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- Deterministic error bound: for orthogonal $\mathbf{U}$, if the range of $\mathbf{U}^{\mathsf{H}}
\mathbf{W}$ lies in $\mathcal{K}_3(\mathbf{D}, \mathbf{G})$ and no vector of that space has head
mass above $19/36$ of its squared norm, then $\|\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}} -
\mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \ge 14\lvert m \rvert + \tfrac{33}{10}\lvert k \rvert$.
Proof: unitary invariance (`NLAlib.HasOrthonormalCols.frobNorm_mul_left`, `frobNorm_mul_right`)
turns the error into $\|\mathbf{D} - (\mathbf{U}^{\mathsf{H}}\mathbf{W})(\mathbf{M}\mathbf{U})\|$;
`NLAlib.le_frobNorm_diagonal_sub_mul_sq` gives $14\lvert m\rvert + 7(\lvert k\rvert - t)$ and
`sum_head_mass_sq_le` (with $\mathbf{P}$ the range projector of $\mathbf{U}^{\mathsf{H}}\mathbf{W}$,
whose columns lie in the range) gives $t \le \tfrac{19}{36}\lvert k\rvert$. -/
private lemma le_frobNorm_of_orthonormal_range {b : Type*} [Fintype b]
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    {W : Matrix (k ⊕ (Fin 3 × m)) k ℝ} {M : Matrix k (k ⊕ (Fin 3 × m)) ℝ}
    {G : Matrix (k ⊕ (Fin 3 × m)) b ℝ} (hU : HasOrthonormalCols U)
    (hr : LinearMap.range (Uᴴ * W).mulVecLin ≤
      blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3)
    (hgood : ∀ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3,
      ¬ (171 / (20 - 2 : ℝ) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2)) :
    14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
      frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ - W * M) ^ 2 := by
  classical
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2) with hD
  have hfrob : frobNorm (U * D * Uᴴ - W * M) = frobNorm (D - (Uᴴ * W) * (M * U)) := by
    have hU1 : Uᴴ * U = 1 := hU
    have hUU : U * Uᴴ = 1 := mul_eq_one_comm.mp hU1
    have hUh : HasOrthonormalCols Uᴴ := by
      unfold HasOrthonormalCols
      rw [Matrix.conjTranspose_conjTranspose]
      exact hUU
    have hkey : U * (D - (Uᴴ * W) * (M * U)) * Uᴴ = U * D * Uᴴ - W * M := by
      have h2 : U * (D - (Uᴴ * W) * (M * U)) * Uᴴ
          = U * D * Uᴴ - (U * Uᴴ) * W * (M * (U * Uᴴ)) := by
        simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      rw [h2, hUU]
      simp only [Matrix.one_mul, Matrix.mul_one]
    rw [← hkey, hUh.frobNorm_mul_right, hU.frobNorm_mul_left]
  have hle := le_frobNorm_diagonal_sub_mul_sq (Uᴴ * W) (M * U)
  have ht : ∑ a : k, ‖WithLp.toLp 2 (rangeProjector (Uᴴ * W) *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2
      ≤ 19 / 36 * Fintype.card k := by
    set P := rangeProjector (Uᴴ * W) with hPdef
    have hP : IsStarProjection P := isStarProjection_rangeProjector _
    have hnorm : ∀ z : k ⊕ (Fin 3 × m) → ℝ, ‖WithLp.toLp 2 z‖ ^ 2 = ∑ i, z i ^ 2 := by
      intro z
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have hsum := sum_head_mass_sq_le P hP (c := 19 / 36) (by norm_num) (fun a => by
      have hz : P *ᵥ Pi.single (Sum.inl a) 1 ∈ LinearMap.range (Uᴴ * W).mulVecLin := by
        rw [← range_rangeProjector]
        exact ⟨_, rfl⟩
      have h1 := hgood _ (hr hz)
      rw [hnorm, not_lt] at h1
      simp only [Matrix.mulVec_single_one] at h1
      rw [show (171 : ℝ) / (20 - 2) ^ 2 = 19 / 36 by norm_num] at h1
      exact h1)
    simp only [hnorm, Matrix.mulVec_single_one]
    exact hsum
  rw [hfrob]
  linarith [hle, ht, (Nat.cast_nonneg (Fintype.card k) : (0 : ℝ) ≤ Fintype.card k)]

/-- **Two-pass Frobenius lower bound for one deterministic algorithm**: let $\mathbf{U}$ be Haar,
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, and let a measurable algorithm make $q$ queries in at most
two passes to $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$ and
output $\mathbf{W} \in \mathbb{R}^{n \times k}$, $\mathbf{M} \in \mathbb{R}^{k \times n}$. If
$400(q + \lvert k \rvert) \le \lvert m \rvert$, then
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 < 14\lvert m \rvert +
3.3\lvert k \rvert\Bigr] \le 4e^{-\lvert m \rvert/800} \,,$$
and $14\lvert m \rvert = \|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$.
OP5, Theorem A.
Proof: extend the space by an independent standard Gaussian $n \times (q + k)$ matrix; apply
`NLAlib.QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame` to
`alg.mapOutput Prod.fst` with no initial block (`Fin 0` columns,
`NLAlib.IsKrylovCoupling.ae_range_le_of_isEmpty`), depth $3$. On orthogonal $\mathbf{U}$,
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}} = \|\mathbf{D} - (\mathbf{U}^{\mathsf{H}}
\mathbf{W})(\mathbf{M}\mathbf{U})\|_{\mathsf{F}}$; by `NLAlib.le_frobNorm_diagonal_sub_mul_sq` the
error is at least $14\lvert m \rvert + 7(\lvert k \rvert - t)$, and $t$ is the sum over an
orthonormal basis of the range of $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ (at most $\lvert k \rvert$
vectors, in $\mathcal{K}_3$) of their head mass, at most $\tfrac{19}{36}\lvert k \rvert$ outside
the event of `NLAlib.measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix`
with $\gamma = 20$; $7 \cdot \tfrac{17}{36} > 3.3$. M, about 80 lines. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | frobNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 <
        14 * Fintype.card m + 33 / 10 * Fintype.card k} ≤
      4 * Real.exp (-(Fintype.card m / 800)) := by
  classical
  have := hU.isProbabilityMeasure
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2) with hD
  set ν := gaussianMatrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) with hν
  have : IsProbabilityMeasure ν := isProbabilityMeasure_gaussianMatrix
  -- extend the space by an independent Gaussian block Z
  have hZ : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => p.2) ν (μ.prod ν) :=
    measurePreserving_snd.hasLaw
  have hUp : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => U p.1)
      (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) (μ.prod ν) :=
    hU.comp (measurePreserving_fst.hasLaw)
  have hUZ : IndepFun (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => U p.1)
      (fun p => p.2) (μ.prod ν) :=
    ProbabilityTheory.indepFun_prod₀ hU.aemeasurable aemeasurable_id
  -- Krylov coupling for the output, with no initial block
  obtain ⟨G, hG⟩ :=
    QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame
      (alg := alg.mapOutput Prod.fst) (hpass.mapOutput Prod.fst) hp
      (halg.mapOutput measurable_fst) D
      (0 : Matrix (k ⊕ (Fin 3 × m)) (Fin 0) ℝ) hUp hZ hUZ
  have hae : ∀ᵐ p ∂(μ.prod ν), HasOrthonormalCols (U p.1) :=
    (Measure.quasiMeasurePreserving_fst).ae
      (ae_hasOrthonormalCols_of_hasLaw_haarFrame hU (by
        simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega))
  have hrange := hG.ae_range_le_of_isEmpty
  simp only [QueryAlgorithm.run_mapOutput] at hrange
  -- Gaussian head capture
  have hkb : Fintype.card k ≤ Fintype.card (Fin q ⊕ k) := by
    rw [Fintype.card_sum, Fintype.card_fin]; omega
  have hbm : (20 : ℝ) ^ 2 * Fintype.card (Fin q ⊕ k) ≤ Fintype.card m := by
    rw [Fintype.card_sum, Fintype.card_fin]
    have h400 : (400 : ℝ) * ((q : ℝ) + Fintype.card k) ≤ Fintype.card m := by
      exact_mod_cast hm
    push_cast
    linarith
  have hL3 := measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    hG.hasLaw_gaussianMatrix (γ := 20) (by norm_num) hkb hbm
  have hN : (μ.prod ν).real {p | ¬ (HasOrthonormalCols (U p.1) ∧
      LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
        blockKrylovSpace D (G p) 3)} = 0 := by
    have h0 : (μ.prod ν) {p | ¬ (HasOrthonormalCols (U p.1) ∧
        LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
          blockKrylovSpace D (G p) 3)} = 0 :=
      ae_iff.mp (hae.and hrange)
    rw [measureReal_def, h0]
    simp
  refine (measureReal_le_prod_fst ν _).trans ?_
  calc (μ.prod ν).real _ ≤ (μ.prod ν).real
        ({p | ∃ z ∈ blockKrylovSpace D (G p) 3,
          171 / (20 - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ∪
          {p | ¬ (HasOrthonormalCols (U p.1) ∧
            LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
              blockKrylovSpace D (G p) 3)}) := by
        refine measureReal_mono fun p hpS => ?_
        by_cases hgo : HasOrthonormalCols (U p.1) ∧
            LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
              blockKrylovSpace D (G p) 3
        · left
          by_contra hE
          have hb := le_frobNorm_of_orthonormal_range
            (M := (alg.run (hiddenRotationOracle (U p.1) D)).2) hgo.1 hgo.2
            (fun z hz hlt => hE ⟨z, hz, hlt⟩)
          exact (not_lt.mpr hb) hpS
        · exact Or.inr hgo
    _ ≤ (μ.prod ν).real {p | ∃ z ∈ blockKrylovSpace D (G p) 3,
          171 / (20 - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} +
        (μ.prod ν).real {p | ¬ (HasOrthonormalCols (U p.1) ∧
            LinearMap.range ((U p.1)ᴴ * (alg.run (hiddenRotationOracle (U p.1) D)).1).mulVecLin ≤
              blockKrylovSpace D (G p) 3)} := measureReal_union_le _ _
    _ = _ := by rw [hN, add_zero]
    _ ≤ 4 * Real.exp (-(Fintype.card m / (2 * 20 ^ 2))) := hL3
    _ = _ := by norm_num

/-- Head mass of a range inside a subspace with small head mass: if every $\mathbf{z} \in S$ has
$\sum_{a \in k} z_a^2 \le c\|\mathbf{z}\|^2$ and the range of $\mathbf{W}$ lies in $S$, then
$\sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \le c\lvert k \rvert$. -/
private theorem sum_norm_rangeProjector_mulVec_single_sq_le {W : Matrix (k ⊕ (Fin 3 × m)) k ℝ}
    {S : Submodule ℝ (k ⊕ (Fin 3 × m) → ℝ)} {c : ℝ} (hc : 0 ≤ c)
    (hW : LinearMap.range W.mulVecLin ≤ S)
    (hS : ∀ z ∈ S, ∑ a : k, z (Sum.inl a) ^ 2 ≤ c * ‖WithLp.toLp 2 z‖ ^ 2) :
    ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2 ≤
      c * Fintype.card k := by
  set P := rangeProjector W
  have hsymm : ∀ i j, P i j = P j i := fun i j => by
    simpa using congrFun (congrFun (conjTranspose_rangeProjector W) j) i
  have hcol : ∀ j, P.col j ∈ S := fun j => hW <| (range_rangeProjector W) ▸
    ⟨Pi.single j 1, by simp [P]⟩
  calc ∑ a : k, ‖WithLp.toLp 2 (P *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2
      = ∑ i, ∑ a : k, P.col i (Sum.inl a) ^ 2 := by
        simp only [Matrix.mulVec_single_one, EuclideanSpace.norm_toLp_sq_eq_sum_sq,
          Matrix.col_apply]
        rw [Finset.sum_comm]
        simp only [hsymm]
    _ ≤ ∑ i, c * ‖WithLp.toLp 2 (P.col i)‖ ^ 2 := Finset.sum_le_sum fun i _ => hS _ (hcol i)
    _ = c * frobNorm P ^ 2 := by rw [frobNorm_sq_eq_sum_col, Finset.mul_sum]
    _ ≤ c * (P.rank * specNorm P ^ 2) := by gcongr; exact frobNorm_sq_le_rank_mul_specNorm_sq P
    _ ≤ c * (Fintype.card k * 1 ^ 2) := by
        gcongr
        · rw [rank_rangeProjector]; exact_mod_cast W.rank_le_card_width
        · exact (isStarProjection_rangeProjector W).specNorm_le_one
    _ = c * Fintype.card k := by ring

/-- The deterministic step of the spectral two-pass bound: for orthogonal $\mathbf{U}$, if the
range of $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ lies in a subspace whose vectors have head mass at
most $\tfrac{19}{64}\|\mathbf{z}\|^2$, then
$\|\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}} - \mathbf{W}\mathbf{M}\|_2^2 \ge \tfrac{45}{4}$. -/
private theorem le_specNorm_mul_diagonal_mul_sub_mul_sq [Nonempty k]
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U)
    {W : Matrix (k ⊕ (Fin 3 × m)) k ℝ} {M : Matrix k (k ⊕ (Fin 3 × m)) ℝ}
    {S : Submodule ℝ (k ⊕ (Fin 3 × m) → ℝ)} (hW : LinearMap.range (Uᴴ * W).mulVecLin ≤ S)
    (hS : ∀ z ∈ S, ∑ a : k, z (Sum.inl a) ^ 2 ≤ 19 / 64 * ‖WithLp.toLp 2 z‖ ^ 2) :
    45 / 4 ≤ specNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ - W * M) ^ 2 := by
  have heq : U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ - W * M =
      U * (Matrix.diagonal (equispacedLevelSpectrum k m 2) - (Uᴴ * W) * (M * U)) * Uᴴ := by
    rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc U (Uᴴ * W), ← Matrix.mul_assoc U Uᴴ,
      hU.mul_conjTranspose_self, Matrix.one_mul, Matrix.mul_assoc W, Matrix.mul_assoc M,
      hU.mul_conjTranspose_self, Matrix.mul_one, Matrix.mul_assoc]
  rw [heq, hU.conjTranspose.specNorm_mul_right, hU.specNorm_mul_left]
  refine le_trans ?_ (le_specNorm_diagonal_sub_mul_sq _ _)
  have ht := sum_norm_rangeProjector_mulVec_single_sq_le (by norm_num) hW hS
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  rw [le_div_iff₀ hk]
  nlinarith

/-- **Two-pass spectral lower bound for one deterministic algorithm**: in the setting of
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
($\mathbf{U}$ Haar, $\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m,
2\mathbf{I}_m, 3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, a measurable algorithm with $q$ queries in at
most two passes to the hidden-rotation oracle, output $\mathbf{W}\mathbf{M}$ of rank at most
$\lvert k \rvert$), with $k$ nonempty and $676(q + \lvert k \rvert) \le \lvert m \rvert$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2^2 < \tfrac{45}{4}\Bigr] \le
4e^{-\lvert m \rvert/1352} \,,$$
while $\sigma_{k+1}(\mathbf{A})^2 = 9$: no $(1 + \varepsilon)\sigma_{k+1}$ approximation for
$\varepsilon \le 0.1$.
OP5, Theorem C.
Proof: as the Frobenius form, with `NLAlib.le_specNorm_diagonal_sub_mul_sq` and $\gamma = 26$
($t \le \tfrac{19}{64}\lvert k \rvert$, $16 \cdot \tfrac{45}{64} = \tfrac{45}{4}$). M, about 60
lines. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    [Nonempty k] {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 676 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | specNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 < 45 / 4} ≤
      4 * Real.exp (-(Fintype.card m / 1352)) := by
  have := hU.isProbabilityMeasure
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2)
  -- extend by an independent Gaussian matrix
  set μ' := μ.prod (gaussianMatrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k))
  have hU₁ : HasLaw (fun p : Ω × Matrix (k ⊕ (Fin 3 × m)) (Fin q ⊕ k) ℝ => U p.1)
      (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ' :=
    hU.comp measurePreserving_fst.hasLaw
  obtain ⟨G, hG⟩ := (hpass.mapOutput Prod.fst).exists_isKrylovCoupling_of_hasLaw_haarFrame
    (p := 2) hp (halg.mapOutput measurable_fst) D (0 : Matrix (k ⊕ (Fin 3 × m)) (Fin 0) ℝ) hU₁
    measurePreserving_snd.hasLaw (indepFun_prod₀ hU.aemeasurable aemeasurable_id)
  have hbad := measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    hG.hasLaw_gaussianMatrix (γ := 26) (by norm_num) (by simp) (by
      simp only [Fintype.card_sum, Fintype.card_fin]; push_cast; norm_num; exact_mod_cast hm)
  calc _ = μ'.real (Prod.fst ⁻¹' {ω | specNorm (U ω * D * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) D)).1 * (alg.run (hiddenRotationOracle (U ω) D)).2)
          ^ 2 < 45 / 4}) := by
        rw [← Set.prod_univ, measureReal_def, measureReal_def, Measure.prod_prod, measure_univ,
          mul_one]
    _ ≤ _ := measureReal_mono_ae ?_
    _ ≤ _ := hbad.trans_eq (by norm_num)
  filter_upwards [hG.ae_range_le_of_isEmpty, ae_hasOrthonormalCols_of_hasLaw_haarFrame hU₁ le_rfl]
    with ω hω hUω hlt
  change specNorm _ ^ 2 < 45 / 4 at hlt
  change ∃ z ∈ _, _ < _
  by_contra hne
  push Not at hne
  rw [QueryAlgorithm.run_mapOutput] at hω
  refine absurd hlt (not_lt.2 (le_specNorm_mul_diagonal_mul_sub_mul_sq hUω hω fun z hz => ?_))
  have := hne z hz
  norm_num at this ⊢
  linarith

/-- **Two-pass Frobenius lower bound, randomized worst case**: for every randomized algorithm (a
measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at most two passes
(per seed) with output $\mathbf{W}\mathbf{M}$, $\mathbf{W} \in \mathbb{R}^{n \times k}$, and
$400(q + \lvert k \rvert) \le \lvert m \rvert$, there is an orthogonal $\mathbf{U}$ such that for
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$
$$\mathbb{P}_s\Bigl[\|\mathbf{A} - \mathbf{W}_s\mathbf{M}_s\|_{\mathsf{F}}^2 \ge
14\lvert m \rvert + 3.3\lvert k \rvert\Bigr] \ge 1 - 4e^{-\lvert m \rvert/800} \,.$$
OP5, Corollary B(i).
Proof: Yao's principle for a class of algorithms,
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall`, for the
family `fun s => (alg s).comapResponse Prod.fst` against the hidden-rotation oracle
(`NLAlib.QueryAlgorithm.run_comapResponse`,
`NLAlib.QueryAlgorithm.IsMeasurableFamily.comapResponse`,
`NLAlib.Measurable.hiddenRotationOracle`), failure set restricted to orthogonal $\mathbf{U}$
(`NLAlib.isClosed_setOf_hasOrthonormalCols`); each deterministic member fails by
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
(`NLAlib.QueryAlgorithm.IsPassStructured.comapResponse`). M, about 40 lines. -/
theorem exists_le_measureReal_frobNorm_sub_mul_sq_ge {q : ℕ}
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ∃ U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, HasOrthonormalCols U ∧
      1 - 4 * Real.exp (-(Fintype.card m / 800)) ≤
        ρ.real {s | 14 * Fintype.card m + 33 / 10 * Fintype.card k ≤
          frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).1 *
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).2) ^ 2}
    := by
  -- the good set of (input, output) pairs
  let B : Set (Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ ×
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)) :=
    {p | HasOrthonormalCols p.1 ∧ 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
      frobNorm (p.1 * Matrix.diagonal (equispacedLevelSpectrum k m 2) * p.1ᴴ -
        p.2.1 * p.2.2) ^ 2}
  have hC : MeasurableSet {Q : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ |
      HasOrthonormalCols Q} :=
    isClosed_setOf_hasOrthonormalCols.measurableSet
  have hF : Measurable fun p : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ ×
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ) =>
      frobNorm (p.1 * Matrix.diagonal (equispacedLevelSpectrum k m 2) * p.1ᴴ -
        p.2.1 * p.2.2) ^ 2 := by
    refine ((measurable_frobNorm).comp ?_).pow_const 2
    fun_prop
  have hB : MeasurableSet B := (measurable_fst hC).inter (measurableSet_le measurable_const hF)
  have hO : Measurable (Function.uncurry fun (U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ)
      (x : k ⊕ (Fin 3 × m) → ℝ) => hiddenRotationOracle U
        (Matrix.diagonal (equispacedLevelSpectrum k m 2)) x) :=
    Measurable.hiddenRotationOracle measurable_fst measurable_snd _
  have hA : QueryAlgorithm.IsMeasurableFamily fun s => (alg s).comapResponse
      (R' := (k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) Prod.fst :=
    halg.comapResponse measurable_fst
  have hsucc : ∀ s, 1 - 4 * Real.exp (-(Fintype.card m / 800 : ℝ)) ≤
      (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real
        {x | (x, ((alg s).comapResponse Prod.fst).run
          (hiddenRotationOracle x (Matrix.diagonal (equispacedLevelSpectrum k m 2)))) ∈ B} := by
    intro s
    set A' := (alg s).comapResponse (R' := (k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ))
      Prod.fst with hA'
    set D := Matrix.diagonal (equispacedLevelSpectrum k m 2) with hD
    set G := {x : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ |
      (x, A'.run (hiddenRotationOracle x D)) ∈ B} with hG
    set B1 := {x : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ |
      frobNorm (x * D * xᴴ - (A'.run (hiddenRotationOracle x D)).1 *
        (A'.run (hiddenRotationOracle x D)).2) ^ 2 <
        14 * Fintype.card m + 33 / 10 * Fintype.card k} with hB1
    set B2 := {x : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ | ¬HasOrthonormalCols x}
      with hB2
    have h203 : (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real B1 ≤
        4 * Real.exp (-(Fintype.card m / 800)) :=
      QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
        ((hpass s).comapResponse Prod.fst) (hp s)
        ((halg.isMeasurable s).comapResponse measurable_fst) hm
        (HasLaw.id (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))))
    have hortho : ∀ᵐ x ∂haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)),
        HasOrthonormalCols x :=
      ae_hasOrthonormalCols_of_hasLaw_haarFrame HasLaw.id le_rfl
    have hB20 : (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real B2 = 0 := by
      rw [measureReal_def, hB2, ae_iff.1 hortho]
      simp
    have hcover : (Set.univ : Set (Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ)) ⊆
        G ∪ (B1 ∪ B2) := by
      intro x _
      by_cases h1 : HasOrthonormalCols x
      · by_cases h2 : 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
            frobNorm (x * D * xᴴ - (A'.run (hiddenRotationOracle x D)).1 *
              (A'.run (hiddenRotationOracle x D)).2) ^ 2
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr (Or.inl (not_le.1 h2))
      · exact Or.inr (Or.inr h1)
    have h1 := measureReal_mono (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) hcover
    have h2 := measureReal_union_le (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) G
      (B1 ∪ B2)
    have h3 := measureReal_union_le (μ := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) B1 B2
    rw [probReal_univ] at h1
    linarith
  obtain ⟨U, hU⟩ := hA.exists_le_measureReal_run_mem_of_forall (ρ := ρ)
    (ν := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) hO hB hsucc
  by_cases hUo : HasOrthonormalCols U
  · refine ⟨U, hUo, hU.trans (measureReal_mono fun s hs => ?_)⟩
    have h := hs.2
    rw [QueryAlgorithm.run_comapResponse] at h
    exact h
  · exact ⟨1, hasOrthonormalCols_one, hU.trans (measureReal_mono fun s hs => absurd hs.1 hUo)⟩

omit [DecidableEq k] [DecidableEq m] in
/-- **Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: let
$k$ be nonempty, $0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, so the dimension is
$n = \lvert k \rvert + 3\lvert m \rvert < \lvert k \rvert/(2\varepsilon)$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$ with probability at least
$\tfrac12$ for every symmetric $\mathbf{A}$, then
$$q > \frac{\lvert k \rvert}{6400\,\varepsilon} \,.$$
Two passes of randomized SVD with $O(k/\varepsilon)$ products achieve this accuracy in
expectation, so the rate $k/\varepsilon$ is optimal for two-pass algorithms.
No printed source; research note OP5, Corollary B(i), there $q \ge k/(3200\varepsilon) - k$.
Proof: suppose $q \le \lvert k \rvert/(6400\varepsilon)$; then $400(q + \lvert k \rvert) \le
\lvert m \rvert$ and $\lvert m \rvert \ge 1750$ (`Nat.floor` bounds, `Nat.lt_floor_add_one`). Take
the $\mathbf{U}$ of `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`; the optimum is
$14\lvert m \rvert$ (`NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`)
and $14\varepsilon\lvert m \rvert \le 1.75\lvert k \rvert < 3.3\lvert k \rvert$, so success and
failure are disjoint, while $1 - 4e^{-1750/800} > \tfrac12$ (`Real.exp_le_exp`, numerical bound on
$e^{-2}$). S, about 40 lines.
Result: two-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q := by
  classical
  have hk1 : (1 : ℝ) ≤ Fintype.card k := Nat.one_le_cast.mpr Fintype.card_pos
  have hk0 : (0 : ℝ) ≤ Fintype.card k := by positivity
  have hxpos : (0 : ℝ) < (Fintype.card k : ℝ) / (8 * ε) := by positivity
  have hx1750 : (1750 : ℝ) ≤ (Fintype.card k : ℝ) / (8 * ε) := by
    rw [le_div_iff₀ (by positivity)]; linarith
  have hmx : (Fintype.card k : ℝ) / (8 * ε) - 1 < (Fintype.card m : ℝ) := by
    rw [hm]; exact Nat.sub_one_lt_floor _
  have hm1750 : (1750 : ℝ) ≤ Fintype.card m := by
    rw [hm]
    exact_mod_cast Nat.le_floor (show ((1750 : ℕ) : ℝ) ≤ (Fintype.card k : ℝ) / (8 * ε) by
      exact_mod_cast hx1750)
  by_contra hcon
  replace hcon := not_lt.mp hcon
  have hq : (400 : ℝ) * (q + Fintype.card k) ≤ Fintype.card m := by
    have h1 : (q : ℝ) * (6400 * ε) ≤ Fintype.card k := by
      rwa [le_div_iff₀ (by positivity)] at hcon
    have h2 : (400 : ℝ) * (q + Fintype.card k) * (8 * ε) + 8 * ε ≤ Fintype.card k := by
      nlinarith [mul_le_mul_of_nonneg_left hε₁ hk0]
    have h3 : (400 : ℝ) * (q + Fintype.card k) + 1 ≤ (Fintype.card k : ℝ) / (8 * ε) := by
      rw [le_div_iff₀ (by positivity)]; linarith
    linarith
  have hq' : 400 * (q + Fintype.card k) ≤ Fintype.card m := by exact_mod_cast hq
  obtain ⟨U, hU, hfail⟩ := exists_le_measureReal_frobNorm_sub_mul_sq_ge hq' halg hpass hp ρ
  have hexp : (8 : ℝ) < Real.exp (Fintype.card m / 800) := by
    have hy : (2.1875 : ℝ) ≤ Fintype.card m / 800 := by linarith
    have e1 := Real.exp_one_gt_d9
    have e2 := Real.add_one_le_exp (0.1875 : ℝ)
    have e3 : Real.exp 2.1875 = Real.exp 1 * Real.exp 1 * Real.exp 0.1875 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    have e4 := Real.exp_le_exp.mpr hy
    nlinarith [mul_lt_mul'' e1 e1 (by norm_num) (by norm_num)]
  have hinv : Real.exp (-(Fintype.card m / 800)) * Real.exp (Fintype.card m / 800) = 1 := by
    rw [← Real.exp_add]; simp
  have hsmall : 4 * Real.exp (-(Fintype.card m / 800)) < 1 / 2 := by
    nlinarith [mul_pos (Real.exp_pos (-(Fintype.card m / 800 : ℝ))) (sub_pos.mpr hexp)]
  set A := U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ with hA
  have hAherm : A.IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose _ (Matrix.isHermitian_diagonal _)
  have hopt : frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2 = 14 * Fintype.card m :=
    HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq hU
  have hsub := hsucc A hAherm
  rw [hopt] at hsub
  have hmle : (Fintype.card m : ℝ) ≤ (Fintype.card k : ℝ) / (8 * ε) := by
    rw [hm]; exact Nat.floor_le hxpos.le
  have hεm : ε * Fintype.card m ≤ (Fintype.card k : ℝ) / 8 := by
    calc ε * Fintype.card m ≤ ε * ((Fintype.card k : ℝ) / (8 * ε)) :=
          mul_le_mul_of_nonneg_left hmle hε.le
      _ = (Fintype.card k : ℝ) / 8 := by field_simp
  have hrun : Measurable fun s => (alg s).run A.mulVec := by
    have hO : Measurable fun p : Matrix (k ⊕ Fin 3 × m) (k ⊕ Fin 3 × m) ℝ ×
        (k ⊕ Fin 3 × m → ℝ) => p.1.mulVec p.2 :=
      (by fun_prop : Continuous fun p : Matrix (k ⊕ Fin 3 × m) (k ⊕ Fin 3 × m) ℝ ×
        (k ⊕ Fin 3 × m → ℝ) => p.1.mulVec p.2).measurable
    exact (halg.measurable_run
      (O := fun B : Matrix (k ⊕ Fin 3 × m) (k ⊕ Fin 3 × m) ℝ => B.mulVec) hO).comp
      (measurable_id.prodMk measurable_const)
  have hmeas : MeasurableSet {s : S | 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
      frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2} := by
    refine measurableSet_le measurable_const ?_
    refine Measurable.pow_const ?_ 2
    refine measurable_frobNorm.comp (Measurable.sub measurable_const ?_)
    exact (measurable_fst.comp hrun).matrix_mul (measurable_snd.comp hrun)
  have hsubset : {s : S | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
      (1 + ε) * (14 * (Fintype.card m : ℝ))} ⊆
      {s : S | 14 * (Fintype.card m : ℝ) + 33 / 10 * Fintype.card k ≤
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2}ᶜ := by
    intro s hs hc
    simp only [Set.mem_ofPred_eq] at hs hc
    nlinarith
  have hcompl := MeasureTheory.probReal_compl_eq_one_sub (μ := ρ) hmeas
  have hmono := MeasureTheory.measureReal_mono (μ := ρ) hsubset
  linarith

omit [DecidableEq k] [DecidableEq m] in
/-- **One-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: the
statement of `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le` for algorithms whose
products are all chosen in advance (one pass): with $k$ nonempty,
$0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, an algorithm that is within
$(1 + \varepsilon)$ of the best rank-$k$ Frobenius error with probability at least $\tfrac12$ on
every symmetric input makes $q > \lvert k \rvert/(6400\varepsilon)$ products. The best one-pass
upper bound is $O(k/\varepsilon^2)$ (generalized Nyström); the gap is open.
No printed source; research note OP5, Corollary B(iii).
Proof: a one-pass algorithm is a two-pass one (`Nat.lt_succ_of_lt`); apply
`NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`. S, 3 lines.
Result: one-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one [Nonempty k] {ε : ℝ}
    {q : ℕ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 1)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q :=
  div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le hε hε₁ hεk hm halg hpass
    (fun s i hi => (hp s i hi).trans one_lt_two) ρ hsucc

omit [DecidableEq k] [DecidableEq m] in
/-- **Two-pass spectral low-rank approximation needs products proportional to the dimension**:
let $k$ be nonempty, $\lvert m \rvert \ge 2812$ and $0 \le \varepsilon \le 1/10$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with $\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2 \le (1 + \varepsilon)\sigma_{k+1}(\mathbf{A})$
with probability at least $\tfrac12$ for every symmetric $\mathbf{A} \in \mathbb{R}^{n \times n}$,
$n = \lvert k \rvert + 3\lvert m \rvert$, then
$$\lvert m \rvert < 676\,(q + \lvert k \rvert) \,,$$
i.e. $q > (n - \lvert k \rvert)/2028 - \lvert k \rvert$, whatever $\varepsilon \le 0.1$.
OP5, Theorem C.
Proof: by contradiction with Yao's principle
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall` as in
`NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`, from
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`;
$\sigma_{k+1} = 3$ (`NLAlib.HasOrthonormalCols.singularValues_mul_diagonal_mul_card`),
$(1.1 \cdot 3)^2 = 10.89 < 11.25$, and $1 - 4e^{-2812/1352} > \tfrac12$. M, about 50 lines. -/
theorem lt_of_forall_le_measureReal_specNorm_sub_mul_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1 / 10) (hm : 2812 ≤ Fintype.card m) {S : Type*}
    [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | specNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ≤
        (1 + ε) * singularValues A (Fintype.card k)}) :
    Fintype.card m < 676 * (q + Fintype.card k) := by
  classical
  by_contra hcon
  replace hcon := not_lt.mp hcon
  set D := Matrix.diagonal (equispacedLevelSpectrum k m 2)
  set δ : ℝ := 1 - 4 * Real.exp (-(Fintype.card m / 1352))
  have hO : Measurable (Function.uncurry fun (U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ)
      (x : k ⊕ (Fin 3 × m) → ℝ) => (U * D * Uᴴ) *ᵥ x) :=
    (Measurable.hiddenRotationOracle measurable_fst measurable_snd D).fst
  set B : Set (Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ ×
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)) :=
    {p | HasOrthonormalCols p.1 ∧ 45 / 4 ≤ specNorm (p.1 * D * p.1ᴴ - p.2.1 * p.2.2) ^ 2}
  have hB : MeasurableSet B :=
    (isClosed_setOf_hasOrthonormalCols.measurableSet.preimage measurable_fst).inter
      (measurableSet_le measurable_const ((measurable_specNorm.comp
        (((measurable_fst.matrix_mul measurable_const).matrix_mul
          (continuous_star.measurable.matrix_conjTranspose measurable_fst)).matrix_sub
          (measurable_snd.fst.matrix_mul measurable_snd.snd))).pow_const 2))
  have hfail : ∀ s, δ ≤ (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))).real
      {U | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B} := by
    intro s
    set ν := haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))
    have hL :=
      QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
      ((hpass s).comapResponse Prod.fst) (hp s) ((halg.isMeasurable s).comapResponse measurable_fst)
      hcon (U := id) HasLaw.id
    simp only [QueryAlgorithm.run_comapResponse] at hL
    have hNO : ν.real {U | ¬HasOrthonormalCols U} = 0 := by
      have h := ae_iff.mp (ae_hasOrthonormalCols_of_hasLaw_haarFrame (HasLaw.id (μ := ν)) le_rfl)
      exact (congrArg ENNReal.toReal h).trans ENNReal.toReal_zero
    have hT : MeasurableSet {U | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B} :=
      hB.preimage (measurable_id.prodMk ((halg.measurable_run hO).comp measurable_prodMk_left))
    have hsub : {U | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B}ᶜ ⊆
        {ω | specNorm (id ω * D * (id ω)ᴴ -
          ((alg s).run (Prod.fst ∘ hiddenRotationOracle (id ω) D)).1 *
          ((alg s).run (Prod.fst ∘ hiddenRotationOracle (id ω) D)).2) ^ 2 < 45 / 4} ∪
        {U | ¬HasOrthonormalCols U} := by
      intro U hU
      by_cases hUo : HasOrthonormalCols U
      · exact Or.inl (lt_of_not_ge fun h => hU ⟨hUo, h⟩)
      · exact Or.inr hUo
    have := (measureReal_mono (μ := ν) hsub).trans (measureReal_union_le _ _)
    rw [probReal_compl_eq_one_sub hT] at this
    linarith
  obtain ⟨U, hU⟩ := halg.exists_le_measureReal_run_mem_of_forall hO ρ _ hB hfail
  have hA : (U * D * Uᴴ).IsHermitian :=
    Matrix.isHermitian_mul_mul_conjTranspose U (Matrix.isHermitian_diagonal _)
  set succ := {s | specNorm (U * D * Uᴴ - ((alg s).run (U * D * Uᴴ).mulVec).1 *
      ((alg s).run (U * D * Uᴴ).mulVec).2) ≤
      (1 + ε) * singularValues (U * D * Uᴴ) (Fintype.card k)}
  have hsucc' : 1 / 2 ≤ ρ.real succ := hsucc _ hA
  have hmeas : MeasurableSet succ := by
    have hf : Measurable fun s => (alg s).run (U * D * Uᴴ).mulVec :=
      (halg.measurable_run (O := fun (_ : Unit) => (U * D * Uᴴ).mulVec)
        (measurable_const.matrix_mulVec measurable_snd)).comp
        (measurable_id.prodMk (measurable_const (a := ())))
    exact measurableSet_le (measurable_specNorm.comp
      (measurable_const.matrix_sub (hf.fst.matrix_mul hf.snd))) measurable_const
  have hsub : {s | (U, (alg s).run ((U * D * Uᴴ) *ᵥ ·)) ∈ B} ⊆ succᶜ := by
    rintro s ⟨hUo, hs⟩ h
    have : Nonempty m := Fintype.card_pos_iff.mp (by omega)
    have h3 : singularValues (U * D * Uᴴ) (Fintype.card k) = 3 :=
      HasOrthonormalCols.singularValues_mul_diagonal_mul_card hUo
    set E := U * D * Uᴴ - ((alg s).run (U * D * Uᴴ).mulVec).1 *
      ((alg s).run (U * D * Uᴴ).mulVec).2
    replace h : specNorm E ≤ (1 + ε) * 3 := h3 ▸ h
    replace hs : 45 / 4 ≤ specNorm E ^ 2 := hs
    nlinarith [specNorm_nonneg E]
  have hexp : Real.exp (-(Fintype.card m / 1352)) < 1 / 8 := by
    have hm' : (2812 : ℝ) ≤ Fintype.card m := by exact_mod_cast hm
    calc Real.exp (-(Fintype.card m / 1352)) ≤ Real.exp (-(2812 / 1352)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ < 1 / 8 := by
          rw [← Real.exp_log (by norm_num : (0:ℝ) < 1 / 8), one_div, Real.log_inv,
            show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
          exact Real.exp_lt_exp.mpr (by push_cast; linarith [Real.log_two_lt_d9])
  have := (hU.trans (measureReal_mono hsub)).trans_eq (probReal_compl_eq_one_sub hmeas)
  linarith

end NLAlib
