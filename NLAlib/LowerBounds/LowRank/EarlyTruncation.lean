/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.EarlyTruncation
public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlib.ForMathlib.Probability.Moments.PaleyZygmund
public import NLAlib.Probability.Distributions.ChiSquareMoments

/-!
# The early-truncated randomized SVD needs $\Theta(k/\varepsilon^2)$ samples

The early-truncated randomized SVD $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$
(`NLAlib.earlyTruncatedRSVD`) projects $\mathbf{A}$ onto $k$ dominant left singular vectors of the
sketch $\mathbf{A}\mathbf{\Omega}$. With a standard Gaussian $\mathbf{\Omega}$ it reaches
$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}\|_{\mathsf{F}}^2 \le (1+\varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with $\ell \ge 900k/\varepsilon^2$
samples
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`).
This file and its two siblings show the rate $\varepsilon^{-2}$ cannot be improved to
$\varepsilon^{-1}$:

* for $k = 1$ on $\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with
  $\delta = 1/(4\sqrt{\ell})$, the expected error is at least $(1 + 1/(100\sqrt{\ell}))$ times the
  optimum for every $\ell \ge 100$, and with probability at least $1/12$ the error exceeds
  $(1 + \delta)$ times the optimum. The sketch ranks the head direction below the tail one when
  $\|\mathbf{\omega}_1\|^2 < (1-\delta)^2\|\mathbf{\omega}_2\|^2$, which by Paley–Zygmund happens
  with constant probability at this gap (this file);
* for large $k$ on $\operatorname{diag}(\mathbf{I}_k, (1 - \delta)\mathbf{I}_k)$ with
  $\delta = \sqrt{k/\ell}/4$ the expected excess is at least $c\sqrt{k/\ell}$ (absolute constants,
  existential), so $\ell \ge c^2 k/\varepsilon^2$ is necessary
  (`NLAlib.LowerBounds.LowRank.EarlyTruncationBlock` for the deterministic step,
  `NLAlib.LowerBounds.LowRank.EarlyTruncationBlockGaussian` for the expectation bound).

These results are new: no printed source states a lower bound for this estimator (research note
`reports/OP1-EarlyTruncatedRSVD.md` of the NLAlib workflow, 2026-10-25). Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.1. Real throughout.

## Main results

* `NLAlib.add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq`: a misranking sketch costs
  half the gap.
* `NLAlib.le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix`: a Gaussian sketch misranks with
  probability at least $1/12$.
* `NLAlib.le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix`:
  the $k = 1$ expectation bound.
* `NLAlib.le_measureReal_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_gt_of_hasLaw_gaussianMatrix`:
  the $k = 1$ probability bound.
* `NLAlib.one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le`,
  `NLAlib.not_exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`
  :
  $\ell \ge 10^{-4}/\varepsilon^2$ is necessary, and $O(k/\varepsilon)$ samples do not suffice.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l : Type*} [Fintype l]

/-! ### The case $k = 1$: the $2 \times 2$ instance -/

/-- Pointwise form of the Frobenius identity of `frobNorm_sq_diagonal_mul_sub_eq`. -/
private lemma sum_sq_pointwise_aux (M : Matrix (Fin 2) (Fin 2) ℝ) (s x y : ℝ)
    (hsym : M 0 1 = M 1 0)
    (e00 : M 0 0 = M 0 0 * M 0 0 + M 0 1 * M 1 0)
    (e01 : M 0 1 = M 0 0 * M 0 1 + M 0 1 * M 1 1)
    (e11 : M 1 1 = M 1 0 * M 0 1 + M 1 1 * M 1 1) :
    (x - (M 0 0 * x + M 0 1 * (s * y))) ^ 2 + (s * y - (M 1 0 * x + M 1 1 * (s * y))) ^ 2 =
      x ^ 2 + (s * y) ^ 2 - (M 0 0 * x ^ 2 + 2 * M 0 1 * (x * (s * y)) + M 1 1 * (s * y) ^ 2) := by
  rw [← hsym] at e00 e11 ⊢
  linear_combination (-x ^ 2) * e00 + (-2 * s * x * y) * e01 + (-(s * y) ^ 2) * e11

/-- For a symmetric idempotent `M`, the residual `Y - M * Y` of `Y = diag(1, s) * Ω'` has squared
Frobenius norm `a + s² b - (M₀₀ a + 2 M₀₁ s c + M₁₁ s² b)`. -/
private lemma frobNorm_sq_diagonal_mul_sub_eq (s : ℝ) (Ω' : Matrix (Fin 2) l ℝ)
    (M : Matrix (Fin 2) (Fin 2) ℝ) (hsym : M 0 1 = M 1 0) (hidem : M * M = M) :
    frobNorm (diagonal ![1, s] * Ω' - M * (diagonal ![1, s] * Ω')) ^ 2 =
      ∑ j, Ω' 0 j ^ 2 + s ^ 2 * ∑ j, Ω' 1 j ^ 2 -
        (M 0 0 * ∑ j, Ω' 0 j ^ 2 + 2 * M 0 1 * (s * ∑ j, Ω' 0 j * Ω' 1 j) +
          M 1 1 * (s ^ 2 * ∑ j, Ω' 1 j ^ 2)) := by
  have e00 := congrFun (congrFun hidem 0) 0
  have e01 := congrFun (congrFun hidem 0) 1
  have e11 := congrFun (congrFun hidem 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  have hpt : ∀ j, ∑ i, (diagonal ![1, s] * Ω' - M * (diagonal ![1, s] * Ω')) i j ^ 2 =
      Ω' 0 j ^ 2 + (s * Ω' 1 j) ^ 2 -
        (M 0 0 * Ω' 0 j ^ 2 + 2 * M 0 1 * (Ω' 0 j * (s * Ω' 1 j)) +
          M 1 1 * (s * Ω' 1 j) ^ 2) := by
    intro j
    simp [Fin.sum_univ_two, Matrix.sub_apply, Matrix.mul_apply, Matrix.diagonal_apply]
    linear_combination sum_sq_pointwise_aux M s (Ω' 0 j) (Ω' 1 j) hsym e00.symm e01.symm e11.symm
  rw [frobNorm_sq_eq_sum_sq, Finset.sum_comm, Finset.sum_congr rfl fun j _ => hpt j]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- A swapped ranking costs half the gap: for $\mathbf{A} = \operatorname{diag}(1, s)$ with
$0 \le s \le 1$ and a test matrix $\mathbf{\Omega} \in \mathbb{R}^{2 \times \ell}$ with rows
$\mathbf{\omega}_1, \mathbf{\omega}_2$, if the sketch ranks the head row below the tail row,
$\|\mathbf{\omega}_1\|^2 < s^2\|\mathbf{\omega}_2\|^2$, then
$$s^2 + \frac{1 - s^2}{2} \le
\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)\|_{\mathsf{F}}^2\,,$$
against the optimum $s^2$. Deterministic; for the choice `truncatedSVD` makes. -/
theorem add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {Ω' : Matrix (Fin 2) l ℝ}
    (hab : ∑ j, Ω' 0 j ^ 2 < s ^ 2 * ∑ j, Ω' 1 j ^ 2) :
    s ^ 2 + (1 - s ^ 2) / 2 ≤
      frobNorm (Matrix.diagonal ![1, s] - earlyTruncatedRSVD (Matrix.diagonal ![1, s]) Ω' 1) ^ 2
      := by
  classical
  rw [sub_earlyTruncatedRSVD]
  have hP := isStarProjection_rangeProjector (truncatedSVD (diagonal ![1, s] * Ω') 1)
  have hPY := rangeProjector_truncatedSVD_mul (diagonal ![1, s] * Ω') 1
  have hrank : (rangeProjector (truncatedSVD (diagonal ![1, s] * Ω') 1)).rank ≤ 1 :=
    (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ 1)
  have htr : (rangeProjector (truncatedSVD (diagonal ![1, s] * Ω') 1)).trace ≤ 1 := by
    rw [trace_rangeProjector]
    exact_mod_cast rank_truncatedSVD_le _ 1
  generalize rangeProjector (truncatedSVD (diagonal ![1, s] * Ω') 1) = P at hP hPY hrank htr ⊢
  have hsym : P 0 1 = P 1 0 := by
    have := congrFun (congrFun hP.isSelfAdjoint 0) 1
    simpa [Matrix.star_apply] using this.symm
  have hidem : P * P = P := hP.isIdempotentElem
  have e00 := congrFun (congrFun hidem 0) 0
  have e11 := congrFun (congrFun hidem 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e11
  have hsum : P 0 0 + P 1 1 ≤ 1 := by rwa [Matrix.trace_fin_two] at htr
  obtain ⟨S, hS⟩ : ∃ S : Matrix (Fin 2) (Fin 2) ℝ, S = !![0, 1; 1, 0] := ⟨_, rfl⟩
  have hSS : S * S = 1 := by
    subst hS
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hmax : P 0 0 ≤ P 1 1 := by
    have hidem' : S * P * S * (S * P * S) = S * P * S := by
      calc S * P * S * (S * P * S) = S * P * (S * S) * (P * S) := by simp only [Matrix.mul_assoc]
        _ = S * (P * P) * S := by rw [hSS, Matrix.mul_one]; simp only [Matrix.mul_assoc]
        _ = S * P * S := by rw [hidem]
    have hsymS : (S * P * S) 0 1 = (S * P * S) 1 0 := by
      subst hS
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hsym]
    have hP00 : (S * P * S) 0 0 = P 1 1 := by
      subst hS
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have hP11 : (S * P * S) 1 1 = P 0 0 := by
      subst hS
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
    have hP01 : (S * P * S) 0 1 = P 0 1 := by
      subst hS
      simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two, hsym]
    have hB : ((S * P * S) * (diagonal ![1, s] * Ω')).rank ≤ 1 :=
      (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_mul_le_right _ _).trans hrank))
    have hEY := frobNorm_sub_truncatedSVD_le_of_rank_le (diagonal ![1, s] * Ω') hB
    rw [← hPY] at hEY
    have hsq := pow_le_pow_left₀ (frobNorm_nonneg _) hEY 2
    rw [frobNorm_sq_diagonal_mul_sub_eq s Ω' P hsym hidem,
      frobNorm_sq_diagonal_mul_sub_eq s Ω' (S * P * S) hsymS hidem', hP00, hP11, hP01] at hsq
    by_contra h
    push Not at h
    nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hab)]
  have h1s : 0 ≤ 1 - s ^ 2 := by nlinarith
  have h12 : 0 ≤ 1 / 2 - P 0 0 := by linarith
  rw [frobNorm_sq_eq_sum_sq]
  simp only [mul_diagonal, Matrix.sub_apply, Fin.sum_univ_two, Fin.isValue, cons_val_zero,
    mul_one, cons_val_one, cons_val_fin_one, one_apply_eq, ne_eq, zero_ne_one, not_false_eq_true,
    one_apply_ne, zero_sub, neg_mul, even_two, Even.neg_pow, one_ne_zero]
  rw [← hsym] at e00 e11 ⊢
  have hq : (0:ℝ) ≤ 1 - P 0 0 - P 1 1 := by linarith
  nlinarith [mul_nonneg h1s h12, mul_nonneg (sq_nonneg s) hq]

/-- Paley–Zygmund for the squared difference $D = \|\mathbf{\omega}_1\|^2 - \|\mathbf{\omega}_2\|^2$
of the two row energies: $9\ell^2 \le \mathbb{P}[D^2 > \ell]\,(48\ell^2 + 96\ell)$. -/
private lemma le_measureReal_card_lt_sq_of_hasLaw_gaussianMatrix {X : Ω → Matrix (Fin 2) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ) (hl : 0 < Fintype.card l) :
    9 * (Fintype.card l : ℝ) ^ 2 ≤
      μ.real {ω | (Fintype.card l : ℝ) < (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2} *
        (48 * (Fintype.card l : ℝ) ^ 2 + 96 * Fintype.card l) := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hℓ : (0 : ℝ) < Fintype.card l := by exact_mod_cast hl
  have hind : IndepFun (fun ω => X ω 0) (fun ω => X ω 1) μ :=
    hX.iIndepFun_eval.indepFun zero_ne_one
  have hconv : ∀ ω, ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 =
      ‖WithLp.toLp 2 (X ω 0)‖ ^ 2 - ‖WithLp.toLp 2 (X ω 1)‖ ^ 2 := fun ω => by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  have hI2 : ∫ ω, (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2 ∂μ = 4 * Fintype.card l := by
    simp_rw [hconv]
    exact integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector (hX.eval 0) (hX.eval 1) hind
  have hI4 : ∫ ω, ((∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2) ^ 2 ∂μ =
      48 * (Fintype.card l : ℝ) ^ 2 + 96 * Fintype.card l := by
    simp_rw [← pow_mul, hconv]
    exact integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector (hX.eval 0) (hX.eval 1)
      hind
  have hint : Integrable (fun ω => ((∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2) ^ 2) μ := by
    by_contra h
    rw [integral_undef h] at hI4
    nlinarith
  have hD : Measurable fun A : Matrix (Fin 2) l ℝ => (∑ j, A 0 j ^ 2 - ∑ j, A 1 j ^ 2) ^ 2 := by
    fun_prop
  have hPZ := sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt
    (ae_of_all _ fun ω => sq_nonneg _)
    ((memLp_two_iff_integrable_sq (hD.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable).2
      hint) (θ := 1 / 4) (by norm_num) (by norm_num)
  rw [hI2, hI4, show 1 / 4 * (4 * (Fintype.card l : ℝ)) = Fintype.card l by ring] at hPZ
  nlinarith [hPZ]

/-- The difference of the two row energies is symmetric: swapping the independent rows of a
standard Gaussian matrix preserves its law. -/
private lemma measureReal_lt_sub_eq_measureReal_sub_lt_neg {X : Ω → Matrix (Fin 2) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ) (t : ℝ) :
    μ.real {ω | t < ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2} =
      μ.real {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -t} := by
  have := hX.isProbabilityMeasure
  have hG : AEMeasurable (fun ω => X ω 0) μ := (hX.eval 0).aemeasurable
  have hH : AEMeasurable (fun ω => X ω 1) μ := (hX.eval 1).aemeasurable
  have hlaw : μ.map (fun ω => (X ω 0, X ω 1)) = (gaussianVector l).prod (gaussianVector l) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hG hH).1 (hX.iIndepFun_eval.indepFun zero_ne_one),
      (hX.eval 0).map_eq, (hX.eval 1).map_eq]
  have hlaw' : μ.map (fun ω => (X ω 1, X ω 0)) = (gaussianVector l).prod (gaussianVector l) := by
    rw [show (fun ω => (X ω 1, X ω 0)) = Prod.swap ∘ (fun ω => (X ω 0, X ω 1)) from rfl,
      ← AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable (hG.prodMk hH), hlaw,
      Measure.prod_swap]
  have hS : MeasurableSet {p : (l → ℝ) × (l → ℝ) | t < ∑ j, p.1 j ^ 2 - ∑ j, p.2 j ^ 2} :=
    measurableSet_lt measurable_const (by fun_prop)
  have e : {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -t} =
      (fun ω => (X ω 1, X ω 0)) ⁻¹' {p | t < ∑ j, p.1 j ^ 2 - ∑ j, p.2 j ^ 2} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    constructor <;> intro h <;> linarith
  rw [e, measureReal_def, measureReal_def, ← Measure.map_apply_of_aemeasurable (hH.prodMk hG) hS,
    hlaw', ← hlaw, Measure.map_apply_of_aemeasurable (hG.prodMk hH) hS]
  rfl

/-- The head row loses by at least $\sqrt{\ell}$ with probability at least $1/11$: Paley–Zygmund
and the symmetry of the difference. -/
private lemma one_div_eleven_le_measureReal_sub_lt_neg_sqrt {X : Ω → Matrix (Fin 2) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ) (hl : 100 ≤ Fintype.card l) :
    1 / 11 ≤ μ.real {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hℓ : (100 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
  have hPZ := le_measureReal_card_lt_sq_of_hasLaw_gaussianMatrix hX (by omega)
  have hsub : {ω | (Fintype.card l : ℝ) < (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2} ⊆
      {ω | √(Fintype.card l : ℝ) < ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2} ∪
        {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} := by
    intro ω hω
    have h := Real.sqrt_lt_sqrt (Nat.cast_nonneg _) hω
    rw [Real.sqrt_sq_eq_abs] at h
    rcases lt_abs.mp h with h | h
    · exact Or.inl h
    · right
      simp only [Set.mem_ofPred_eq]
      linarith
  have h2 := (measureReal_mono hsub (measure_ne_top μ _)).trans (measureReal_union_le _ _)
  rw [measureReal_lt_sub_eq_measureReal_sub_lt_neg hX] at h2
  have hA : 0 ≤ 48 * (Fintype.card l : ℝ) ^ 2 + 96 * Fintype.card l := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h2 hA]

/-- The chi-square upper tail at twice the mean: $\mathbb{P}[\|\mathbf{g}\|^2 \ge 2\ell] \le 1/132$
for a standard Gaussian vector with $\ell \ge 100$ entries. -/
private lemma measureReal_two_mul_card_le_sum_sq_le {g : Ω → l → ℝ}
    (hg : HasLaw g (gaussianVector l) μ) (hl : 100 ≤ Fintype.card l) :
    μ.real {ω | 2 * (Fintype.card l : ℝ) ≤ ∑ j, g ω j ^ 2} ≤ 1 / 132 := by
  have hℓ : (100 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
  have hT := measureReal_norm_sq_ge_mul_card_le_of_hasLaw_gaussianVector hg (β := 2)
    (by norm_num)
  simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs] at hT
  have hx : (Fintype.card l : ℝ) / 2 * (1 - 2 + Real.log 2) ≤ -15 := by
    nlinarith [Real.log_two_lt_d9]
  have h132 : (132 : ℝ) ≤ Real.exp 15 :=
    calc (132 : ℝ) ≤ 2 ^ 15 := by norm_num
      _ ≤ Real.exp 1 ^ 15 := by gcongr; linarith [Real.add_one_le_exp (1 : ℝ)]
      _ = Real.exp 15 := by rw [← Real.exp_nat_mul]; norm_num
  calc μ.real {ω | 2 * (Fintype.card l : ℝ) ≤ ∑ j, g ω j ^ 2}
      ≤ Real.exp ((Fintype.card l : ℝ) / 2 * (1 - 2 + Real.log 2)) := hT
    _ ≤ Real.exp (-15) := Real.exp_le_exp.2 hx
    _ = (Real.exp 15)⁻¹ := Real.exp_neg 15
    _ ≤ 1 / 132 := by rw [one_div]; exact inv_anti₀ (by norm_num) h132

/-- The arithmetic of the misranking event: $U - V < -t$ and $V < 2t^2$ give
$U < (1 - 1/(4t))^2 V$. -/
private lemma lt_one_sub_sq_mul_of_sub_lt_neg {U V t : ℝ} (ht : 0 < t) (hV : 0 ≤ V)
    (h : U - V < -t) (hV2 : V < 2 * t ^ 2) : U < (1 - 1 / (4 * t)) ^ 2 * V := by
  have hq : 1 / (4 * t) * V < t / 2 := by
    rw [one_div_mul_eq_div, div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_nonneg (sq_nonneg (1 / (4 * t))) hV]

/-- The sketch misranks the two rows with constant probability: for a standard Gaussian
$2 \times \ell$ test matrix with rows $\mathbf{\omega}_1, \mathbf{\omega}_2$, $\ell \ge 100$ and
$\delta = 1/(4\sqrt{\ell})$,
$$\mathbb{P}\bigl[\|\mathbf{\omega}_1\|^2 < (1 - \delta)^2\|\mathbf{\omega}_2\|^2\bigr] \ge
\frac{1}{12}\,.$$
No printed source. New (research note OP1, §1). -/
theorem le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix {X : Ω → Matrix (Fin 2) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ) (hl : 100 ≤ Fintype.card l) :
    1 / 12 ≤ μ.real {ω | ∑ j, X ω 0 j ^ 2 <
      (1 - 1 / (4 * √(Fintype.card l : ℝ))) ^ 2 * ∑ j, X ω 1 j ^ 2} := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hℓ : (100 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
  have hincl : {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} ⊆
      {ω | ∑ j, X ω 0 j ^ 2 < (1 - 1 / (4 * √(Fintype.card l : ℝ))) ^ 2 * ∑ j, X ω 1 j ^ 2} ∪
        {ω | 2 * (Fintype.card l : ℝ) ≤ ∑ j, X ω 1 j ^ 2} := by
    intro ω hω
    by_cases hc : 2 * (Fintype.card l : ℝ) ≤ ∑ j, X ω 1 j ^ 2
    · exact Or.inr hc
    · refine Or.inl (lt_one_sub_sq_mul_of_sub_lt_neg (Real.sqrt_pos.2 (by linarith))
        (Finset.sum_nonneg fun j _ => sq_nonneg _) hω ?_)
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]
      linarith
  have h1 := one_div_eleven_le_measureReal_sub_lt_neg_sqrt hX hl
  have h2 := measureReal_two_mul_card_le_sum_sq_le (hX.eval 1) hl
  have h3 := (measureReal_mono hincl (measure_ne_top μ _)).trans (measureReal_union_le _ _)
  linarith

/-- The optimum of the $2 \times 2$ diagonal instance is $s^2$. -/
private lemma frobNorm_sub_truncatedSVD_diagonal_one_sq {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    frobNorm (Matrix.diagonal ![1, s] - truncatedSVD (Matrix.diagonal ![1, s]) 1) ^ 2 = s ^ 2 := by
  have h0 := frobNorm_sub_truncatedSVD_sq (Matrix.diagonal ![1, s]) 0
  have h1 := frobNorm_sub_truncatedSVD_sq (Matrix.diagonal ![1, s]) 1
  have hσ0 := singularValues_zero_eq_specNorm (Matrix.diagonal ![1, s])
  have hn : ‖(![1, s] : Fin 2 → ℝ)‖ = 1 := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg zero_le_one).mpr fun i => by
        fin_cases i <;> simp [abs_of_nonneg hs0, hs1]
    · simpa using norm_le_pi_norm (![1, s] : Fin 2 → ℝ) 0
  rw [specNorm_diagonal, hn] at hσ0
  have hF : frobNorm (Matrix.diagonal ![1, s]) ^ 2 = 1 + s ^ 2 := by
    rw [frobNorm_sq_eq_sum]
    simp [Fin.sum_univ_two, Matrix.diagonal_apply]
  rw [truncatedSVD_zero, sub_zero, hF] at h0
  rw [h1]
  simp [Finset.sum_range_succ, hσ0] at h0 ⊢
  linarith

/-- Eckart–Young at the diagonal instance: a rank-one matrix errs at least $s^2$. -/
private lemma sq_le_frobNorm_diagonal_sub_sq_of_rank_le {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    {B : Matrix (Fin 2) (Fin 2) ℝ} (hB : B.rank ≤ 1) :
    s ^ 2 ≤ frobNorm (Matrix.diagonal ![1, s] - B) ^ 2 :=
  calc s ^ 2 = frobNorm (Matrix.diagonal ![1, s] - truncatedSVD (Matrix.diagonal ![1, s]) 1) ^ 2 :=
        (frobNorm_sub_truncatedSVD_diagonal_one_sq hs0 hs1).symm
    _ ≤ frobNorm (Matrix.diagonal ![1, s] - B) ^ 2 :=
        pow_le_pow_left₀ (frobNorm_nonneg _)
          (frobNorm_sub_truncatedSVD_le_of_rank_le _ hB) 2

/-- The arithmetic of the excess: $\delta/25 \cdot s^2 \le (1 - s^2)/24$ for $s = 1 - \delta$. -/
private lemma div_twentyfive_mul_sq_le {δ s : ℝ} (hs : s = 1 - δ) (h0 : 0 < δ) (h1 : δ ≤ 1 / 40) :
    δ / 25 * s ^ 2 ≤ (1 - s ^ 2) / 24 := by
  subst hs
  have hb : 0 ≤ (2 - δ) / 24 - (1 - δ) ^ 2 / 25 := by
    nlinarith [mul_nonneg h0.le (sub_nonneg.2 h1)]
  nlinarith [mul_nonneg h0.le hb]

/-- **The early-truncated randomized SVD has excess $\Omega(1/\sqrt{\ell})$ at $k = 1$**: for
$\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with $\delta = 1/(4\sqrt{\ell})$, a standard
Gaussian $2 \times \ell$ test matrix $\mathbf{\Omega}$ and $\ell \ge 100$,
$$\Bigl(1 + \frac{1}{100\sqrt{\ell}}\Bigr)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1
\|_{\mathsf{F}}^2 \le \mathbb{E}\|\mathbf{A} -
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)\|_{\mathsf{F}}^2\,,$$
with $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1\|_{\mathsf{F}}^2 = (1 - \delta)^2$. So
relative error $1 + \varepsilon$ in expectation needs $\ell \ge 10^{-4}/\varepsilon^2$
(`NLAlib.one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le`), matching the
$\varepsilon^{-2}$ of
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`. The
constant $1/100$ is safe, not sharp: the proof gives about $0.0206$, and the excess on this instance
is about $0.5/\sqrt{\ell}$ (research note OP1, §2).
No printed source. New (research note OP1, §1).
Result: early-truncated-rsvd-lower-bound -/
theorem le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix
    {X : Ω → Matrix (Fin 2) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ)
    (hl : 100 ≤ Fintype.card l) :
    (1 + 1 / (100 * √(Fintype.card l : ℝ))) *
        frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
          truncatedSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) 1) ^ 2 ≤
      ∫ ω, frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
        earlyTruncatedRSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) (X ω)
          1) ^ 2
        ∂μ := by
  classical
  have hL : (100 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
  have hr2 : √(Fintype.card l : ℝ) ^ 2 = Fintype.card l := Real.sq_sqrt (by positivity)
  have hr0 := Real.sqrt_nonneg (Fintype.card l : ℝ)
  have hr10 : 10 ≤ √(Fintype.card l : ℝ) := by nlinarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = 1 - 1 / (4 * √(Fintype.card l : ℝ)) := ⟨_, rfl⟩
  rw [← hs]
  have hδ : 1 / (4 * √(Fintype.card l : ℝ)) ≤ 1 / 40 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hδpos : 0 < 1 / (4 * √(Fintype.card l : ℝ)) := by positivity
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hc : 1 / (100 * √(Fintype.card l : ℝ)) = 1 / (4 * √(Fintype.card l : ℝ)) / 25 := by
    field_simp
    ring
  have hkey : 1 / (100 * √(Fintype.card l : ℝ)) * s ^ 2 ≤ (1 - s ^ 2) / 24 := by
    rw [hc]
    exact div_twentyfive_mul_sq_le hs hδpos hδ
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure
  have hE := le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix hX hl
  rw [← hs] at hE
  have hS : MeasurableSet {M : Matrix (Fin 2) l ℝ |
      ∑ j, M 0 j ^ 2 < s ^ 2 * ∑ j, M 1 j ^ 2} :=
    (isOpen_lt (by fun_prop) (by fun_prop)).measurableSet
  have hEm : NullMeasurableSet {ω | ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2} μ :=
    hX.aemeasurable.nullMeasurableSet_preimage hS
  have hg :=
    integrable_frobNorm_sub_earlyTruncatedRSVD_sq (Matrix.diagonal ![1, s]) hX.aemeasurable 1
  have hfg : ∀ ω, s ^ 2 + (1 - s ^ 2) / 2 *
      Set.indicator {ω | ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2} (fun _ => (1 : ℝ)) ω ≤
      frobNorm (Matrix.diagonal ![1, s] -
        earlyTruncatedRSVD (Matrix.diagonal ![1, s]) (X ω) 1) ^ 2 := by
    intro ω
    by_cases hω : ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2
    · rw [Set.indicator_of_mem (show ω ∈ {ω | ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2} from hω)]
      simp only [mul_one]
      exact add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq hs0 hs1 hω
    · rw [Set.indicator_of_notMem
        (show ω ∉ {ω | ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2} from hω)]
      simp only [mul_zero, add_zero]
      exact sq_le_frobNorm_diagonal_sub_sq_of_rank_le hs0 hs1 (rank_earlyTruncatedRSVD_le _ (X ω) 1)
  have hf : Integrable (fun ω => s ^ 2 + (1 - s ^ 2) / 2 *
      Set.indicator {ω | ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2} (fun _ => (1 : ℝ)) ω) μ :=
    (integrable_const _).add (((integrable_const (1 : ℝ)).indicator₀ hEm).const_mul _)
  have hf_eq : ∫ ω, (s ^ 2 + (1 - s ^ 2) / 2 *
      Set.indicator {ω | ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2} (fun _ => (1 : ℝ)) ω) ∂μ =
      s ^ 2 + (1 - s ^ 2) / 2 * μ.real {ω | ∑ j, X ω 0 j ^ 2 < s ^ 2 * ∑ j, X ω 1 j ^ 2} := by
    rw [integral_add (integrable_const _) (((integrable_const (1 : ℝ)).indicator₀ hEm).const_mul _),
      MeasureTheory.integral_const_mul, integral_const, integral_indicator₀ hEm]
    simp
  have hmono := integral_mono hf hg hfg
  rw [hf_eq] at hmono
  have hE' := mul_le_mul_of_nonneg_left hE (by nlinarith : (0 : ℝ) ≤ (1 - s ^ 2) / 2)
  rw [frobNorm_sub_truncatedSVD_diagonal_one_sq hs0 hs1, add_mul, one_mul]
  linarith

/-- Constant-probability $(1+\varepsilon)$ also needs $\varepsilon^{-2}$ samples at $k = 1$: for
$\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with $\delta = 1/(4\sqrt{\ell})$, a standard
Gaussian $2 \times \ell$ test matrix $\mathbf{\Omega}$, $\ell \ge 100$ and
$16\varepsilon^2\ell < 1$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)
\|_{\mathsf{F}}^2 > (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1\|_{\mathsf{F}}^2
\Bigr] \ge \frac{1}{12}\,.$$
No printed source. New (research note OP1, §1). -/
theorem
    le_measureReal_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_gt_of_hasLaw_gaussianMatrix
    {X : Ω → Matrix (Fin 2) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ)
    (hl : 100 ≤ Fintype.card l) {ε : ℝ} (hε : 16 * ε ^ 2 * Fintype.card l < 1) :
    1 / 12 ≤ μ.real {ω | (1 + ε) *
        frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
          truncatedSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) 1) ^ 2 <
      frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
        earlyTruncatedRSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) (X ω)
          1) ^ 2}
      := by
  have := hX.isProbabilityMeasure
  have h100 : (100 : ℝ) ≤ (Fintype.card l : ℝ) := by exact_mod_cast hl
  have hr2 : √(Fintype.card l : ℝ) ^ 2 = (Fintype.card l : ℝ) := Real.sq_sqrt (by positivity)
  have hr0 : 0 ≤ √(Fintype.card l : ℝ) := Real.sqrt_nonneg _
  have hr10 : 10 ≤ √(Fintype.card l : ℝ) := by nlinarith
  have hE := le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix hX hl
  set r := √(Fintype.card l : ℝ) with hr
  set δ : ℝ := 1 / (4 * r) with hδ
  have hδpos : 0 < δ := by positivity
  have hδ40 : δ ≤ 1 / 40 := by
    rw [hδ, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hεδ : |ε| < δ := by
    have h4 : (4 * |ε| * r) ^ 2 < 1 := by
      have : (4 * |ε| * r) ^ 2 = 16 * ε ^ 2 * (Fintype.card l : ℝ) := by
        rw [mul_pow, mul_pow, sq_abs, ← hr2]; ring
      linarith
    have h5 : 4 * |ε| * r < 1 := by nlinarith [abs_nonneg ε, mul_nonneg (abs_nonneg ε) hr0]
    rw [hδ, lt_div_iff₀ (by positivity)]
    linarith
  have hs0 : 0 ≤ 1 - δ := by linarith
  have hs1 : 1 - δ ≤ 1 := by linarith
  have hsq : 0 < (1 - δ) ^ 2 := by nlinarith
  refine hE.trans (measureReal_mono fun ω hω => ?_)
  have hA := add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq (Ω' := X ω) (l := l)
    hs0 hs1 hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rw [frobNorm_sub_truncatedSVD_diagonal_one_sq hs0 hs1]
  have h2 : ε * (1 - δ) ^ 2 < δ * (1 - δ) ^ 2 :=
    mul_lt_mul_of_pos_right (lt_of_le_of_lt (le_abs_self ε) hεδ) hsq
  have h3 : δ * (1 - δ) ^ 2 ≤ (1 - (1 - δ) ^ 2) / 2 := by
    nlinarith [mul_nonneg (sq_nonneg δ) (by linarith : (0:ℝ) ≤ 3 / 2 - δ)]
  nlinarith

/-- Relative error $1 + \varepsilon$ in expectation needs $\ell \ge 10^{-4}/\varepsilon^2$
samples: if a standard Gaussian test matrix $\mathbf{\Omega}$ with $\ell \ge 100$ columns gives
$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)
\|_{\mathsf{F}}^2 \le (1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1
\|_{\mathsf{F}}^2$ for every real $2 \times 2$ matrix $\mathbf{A}$, then
$1 \le 10^4\varepsilon^2\ell$. The library's sufficient condition is $\ell \ge 900k/\varepsilon^2$
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`):
the rate is $\Theta(\varepsilon^{-2})$.
No printed source. New (research note OP1). -/
theorem one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le
    {X : Ω → Matrix (Fin 2) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ)
    (hl : 100 ≤ Fintype.card l) {ε : ℝ}
    (h : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) 1) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A 1) ^ 2) :
    1 ≤ 10 ^ 4 * ε ^ 2 * Fintype.card l := by
  set t : ℝ := √(Fintype.card l : ℝ) with ht
  have hl' : (100 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t ^ 2 = Fintype.card l := Real.sq_sqrt (by linarith)
  have ht10 : 10 ≤ t := by nlinarith
  have hδ : 1 / (4 * t) ≤ 1 / 40 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hδpos : 0 < 1 / (4 * t) := by positivity
  set s : ℝ := 1 - 1 / (4 * t) with hs
  have hs0 : 0 < s := by linarith
  have hE := le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix hX hl
  have hH := h (Matrix.diagonal ![1, s])
  rw [frobNorm_sub_truncatedSVD_diagonal_one_sq hs0.le (by linarith)] at hE hH
  have hkey : 1 / (100 * t) ≤ ε := by
    have := le_of_mul_le_mul_right (hE.trans hH) (pow_pos hs0 2)
    linarith
  have h1 : 1 ≤ 100 * t * ε := by
    rw [div_le_iff₀ (by positivity)] at hkey
    linarith
  nlinarith [ht2]

/-- $O(k/\varepsilon)$ samples do not suffice for the early-truncated randomized SVD: there are
no constants $C, \varepsilon_0 > 0$ such that for every standard Gaussian $n \times \ell$ test
matrix $\mathbf{\Omega}$, every $\mathbf{A}$, $k$ and $0 < \varepsilon \le \varepsilon_0$ with
$\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The negation of the $\varepsilon^{-1}$ analogue of
`NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`
(which holds with $\ell \ge Ck/\varepsilon^2$).
No printed source. New (research note OP1). -/
theorem
    not_exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix :
    ¬ ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ)
      (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  rintro ⟨C, ε₀, hC, hε₀, H⟩
  set ε : ℝ := min ε₀ (min (1 / (10 ^ 5 * (C + 1))) (1 / 10 ^ 4)) with hε_def
  have hεpos : 0 < ε := lt_min hε₀ (lt_min (by positivity) (by norm_num))
  have hε₀le : ε ≤ ε₀ := min_le_left _ _
  have hεle : ε ≤ 1 / (10 ^ 5 * (C + 1)) := (min_le_right _ _).trans (min_le_left _ _)
  have hε4 : ε ≤ 1 / 10 ^ 4 := (min_le_right _ _).trans (min_le_right _ _)
  set L : ℕ := ⌈max (C / ε) 100⌉₊ with hL
  have hCL : C / ε ≤ (L : ℝ) := (le_max_left _ _).trans (Nat.le_ceil _)
  have h100 : (100 : ℝ) ≤ L := (le_max_right _ _).trans (Nat.le_ceil _)
  have hLlt : (L : ℝ) < max (C / ε) 100 + 1 :=
    Nat.ceil_lt_add_one (le_max_of_le_right (by norm_num))
  have hcard : Fintype.card (Fin L) = L := Fintype.card_fin L
  have hX : HasLaw (id : Matrix (Fin 2) (Fin L) ℝ → Matrix (Fin 2) (Fin L) ℝ)
      (gaussianMatrix (Fin 2) (Fin L)) (gaussianMatrix (Fin 2) (Fin L)) :=
    ⟨aemeasurable_id, Measure.map_id⟩
  have hcond : C * (((1 : ℕ) : ℝ) / ε) ≤ Fintype.card (Fin L) := by
    rw [hcard, Nat.cast_one, mul_one_div]; exact hCL
  have hbound : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (id ω) 1) ^ 2 ∂(gaussianMatrix (Fin 2) (Fin L)) ≤
        (1 + ε) * frobNorm (A - truncatedSVD A 1) ^ 2 :=
    fun A => H (gaussianMatrix (Fin 2) (Fin L)) A id 1 ε hX hεpos hε₀le hcond
  have hl : 100 ≤ Fintype.card (Fin L) := by rw [hcard]; exact_mod_cast h100
  have hone := one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le
    hX hl hbound
  rw [hcard] at hone
  have hmax : max (C / ε) 100 ≤ C / ε + 100 :=
    have hCε : 0 < C / ε := div_pos hC hεpos
    max_le (by linarith) (by linarith)
  have hLε : (L : ℝ) * ε < C + 101 * ε := by
    have h1 : (L : ℝ) < C / ε + 101 := by linarith
    have h2 := mul_lt_mul_of_pos_right h1 hεpos
    rw [add_mul, div_mul_cancel₀ _ hεpos.ne'] at h2
    linarith
  have hεC : ε * (10 ^ 5 * (C + 1)) ≤ 1 := (le_div_iff₀ (by positivity)).mp hεle
  have hεC' : ε * C ≤ 1 / 10 ^ 5 := by nlinarith
  have key := mul_lt_mul_of_pos_left hLε (by positivity : (0 : ℝ) < 10 ^ 4 * ε)
  have h5 : ε * ε ≤ ε * (1 / 10 ^ 4) := mul_le_mul_of_nonneg_left hε4 hεpos.le
  nlinarith [key, h5, hεC', hone]

end NLAlib
