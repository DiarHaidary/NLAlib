/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.EarlyTruncation
public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlib.RandomMatrix.Gaussian.FourthMoment
public import NLAlibScaffold.ForMathlib.Probability.Moments.PaleyZygmund
public import NLAlibScaffold.Probability.Distributions.ChiSquareMoments

/-!
# The early-truncated randomized SVD needs $\Theta(k/\varepsilon^2)$ samples

The early-truncated randomized SVD $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$
(`NLAlib.earlyTruncatedRSVD`) projects $\mathbf{A}$ onto $k$ dominant left singular vectors of the
sketch $\mathbf{A}\mathbf{\Omega}$. With a standard Gaussian $\mathbf{\Omega}$ it reaches
$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}\|_{\mathsf{F}}^2 \le (1+\varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with $\ell \ge 900k/\varepsilon^2$
samples
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`).
This file shows the rate $\varepsilon^{-2}$ cannot be improved to $\varepsilon^{-1}$:

* for $k = 1$ on $\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with
  $\delta = 1/(4\sqrt{\ell})$, the expected error is at least $(1 + 1/(100\sqrt{\ell}))$ times the
  optimum for every $\ell \ge 100$, and with probability at least $1/12$ the error exceeds
  $(1 + \delta)$ times the optimum. The sketch ranks the head direction below the tail one when
  $\|\mathbf{\omega}_1\|^2 < (1-\delta)^2\|\mathbf{\omega}_2\|^2$, which by Paley–Zygmund happens
  with constant probability at this gap;
* for large $k$ on $\operatorname{diag}(\mathbf{I}_k, (1 - \delta)\mathbf{I}_k)$ with
  $\delta = \sqrt{k/\ell}/4$ the expected excess is at least $c\sqrt{k/\ell}$ (absolute constants,
  existential), so $\ell \ge c^2 k/\varepsilon^2$ is necessary.

These results are new: no printed source states a lower bound for this estimator (research note
`reports/OP1-EarlyTruncatedRSVD.md` of the NLAlib workflow, 2026-10-25). Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.1. Real throughout. Proofs deferred.

## Main results

* `NLAlib.le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix`:
  the $k = 1$ expectation bound.
* `NLAlib.le_measureReal_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_gt_of_hasLaw_gaussianMatrix`:
  the $k = 1$ probability bound.
* `NLAlib.one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le`,
  `NLAlib.not_exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`
  :
  $\ell \ge 10^{-4}/\varepsilon^2$ is necessary, and $O(k/\varepsilon)$ samples do not suffice.
* `NLAlib.exists_forall_le_integral_frobNorm_sub_earlyTruncatedRSVD_sq_of_hasLaw_gaussianMatrix`:
  the general-$k$ instance.
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

/-- **A swapped ranking costs half the gap**: for $\mathbf{A} = \operatorname{diag}(1, s)$ with
$0 \le s \le 1$ and a test matrix $\mathbf{\Omega} \in \mathbb{R}^{2 \times \ell}$ with rows
$\mathbf{\omega}_1, \mathbf{\omega}_2$, if the sketch ranks the head row below the tail row,
$\|\mathbf{\omega}_1\|^2 < s^2\|\mathbf{\omega}_2\|^2$, then
$$s^2 + \frac{1 - s^2}{2} \le
\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)\|_{\mathsf{F}}^2\,,$$
against the optimum $s^2$. Deterministic; for the choice `truncatedSVD` makes.
Proof: M, about 50 lines. Let $\mathbf{P}$ be the range projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_1$ (`rangeProjector`, rank at most $1$, so
$p_1 + p_2 = \operatorname{tr}\mathbf{P} \le 1$ with $p_i = \mathbf{P}_{i,i} \ge 0$). The error is
$\|\mathbf{A}\|_{\mathsf{F}}^2 - \|\mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 = 1 + s^2 - p_1 - s^2 p_2
\ge 1 - (1 - s^2) p_1$ (`sub_earlyTruncatedRSVD`, Pythagoras for an orthogonal projector). With
$\mathbf{S}$ the swap permutation matrix, $\mathbf{S}\mathbf{P}\mathbf{S}$ is again an orthogonal
projector of rank at most $1$, and $\mathbf{P}$ maximises $\|\mathbf{P}'\mathbf{Y}\|_{\mathsf{F}}$
over those ($\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$, Eckart–Young
`frobNorm_sub_truncatedSVD_le_of_rank_le` through `rangeProjector_truncatedSVD_mul`); the
difference is
$\operatorname{tr}((\mathbf{S}\mathbf{P}\mathbf{S} - \mathbf{P})\mathbf{Y}\mathbf{Y}^{\mathsf{T}})
= (b - a)(p_1 - p_2)$ with $a = \|\mathbf{\omega}_1\|^2$, $b = s^2\|\mathbf{\omega}_2\|^2$. So
$a < b$ forces $p_1 \le p_2$, hence $p_1 \le 1/2$. All on $2 \times 2$ matrices
(`Matrix.trace_fin_two`, `Fin.sum_univ_two`). -/
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
  generalize rangeProjector (truncatedSVD (diagonal ![1, s] * Ω') 1) = P at hP hPY hrank ⊢
  have hsym : P 0 1 = P 1 0 := by
    have := congrFun (congrFun hP.isSelfAdjoint 0) 1
    simpa [Matrix.star_apply] using this.symm
  have hidem : P * P = P := hP.isIdempotentElem
  have e00 := congrFun (congrFun hidem 0) 0
  have e01 := congrFun (congrFun hidem 0) 1
  have e11 := congrFun (congrFun hidem 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two] at e00 e01 e11
  have hdet : P 0 0 * P 1 1 - P 0 1 * P 1 0 = 0 := by
    by_contra hne
    have hu : IsUnit P := by
      refine (Matrix.isUnit_iff_isUnit_det P).mpr (isUnit_iff_ne_zero.mpr ?_)
      rwa [Matrix.det_fin_two]
    have := Matrix.rank_of_isUnit P hu
    rw [Fintype.card_fin] at this
    omega
  have hsum : P 0 0 + P 1 1 ≤ 1 := by
    by_cases hx : P 0 1 = 0
    · rw [hx] at e00 e11 hdet
      have hp : P 0 0 * (P 0 0 - 1) = 0 := by linear_combination e00
      have hq : P 1 1 * (P 1 1 - 1) = 0 := by linear_combination e11
      rcases mul_eq_zero.mp hp with hp | hp <;> rcases mul_eq_zero.mp hq with hq | hq <;>
        nlinarith
    · have h1 : P 0 1 * (P 0 0 + P 1 1 - 1) = 0 := by linear_combination e01
      have := (mul_eq_zero.mp h1).resolve_left hx
      linarith
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
    push_neg at h
    nlinarith [mul_pos (sub_pos.2 h) (sub_pos.2 hab)]
  have h1s : 0 ≤ 1 - s ^ 2 := by nlinarith
  have h12 : 0 ≤ 1 / 2 - P 0 0 := by linarith
  rw [frobNorm_sq_eq_sum_sq]
  simp [Fin.sum_univ_two, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.one_apply]
  rw [← hsym] at e00 e11 ⊢
  have hq : (0:ℝ) ≤ 1 - P 0 0 - P 1 1 := by linarith
  nlinarith [mul_nonneg h1s h12, mul_nonneg (sq_nonneg s) hq]

/-- **The sketch misranks the two rows with constant probability**: for a standard Gaussian
$2 \times \ell$ test matrix with rows $\mathbf{\omega}_1, \mathbf{\omega}_2$, $\ell \ge 100$ and
$\delta = 1/(4\sqrt{\ell})$,
$$\mathbb{P}\bigl[\|\mathbf{\omega}_1\|^2 < (1 - \delta)^2\|\mathbf{\omega}_2\|^2\bigr] \ge
\frac{1}{12}\,.$$
No printed source. New (research note OP1, §1).
Proof: M, about 70 lines. Let $X = \|\mathbf{\omega}_1\|^2 - \|\mathbf{\omega}_2\|^2$. The rows
are independent standard Gaussian vectors (`hasLaw_uncurry_of_hasLaw_gaussianMatrix`, then the
row maps and `iIndepFun` of the coordinates, or the transpose and
`iIndepFun_col_of_hasLaw_gaussianMatrix`). Paley–Zygmund
(`ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt`) on $Z = X^2$ with
$\theta = 1/4$, $\mathbb{E}Z = 4\ell$, $\mathbb{E}Z^2 = 48\ell^2 + 96\ell$
(`integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector`,
`integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector`) gives
$\mathbb{P}[X^2 > \ell] \ge 9\ell/(48\ell + 96)$. $X$ and $-X$ have the same law (swap the rows:
the law `gaussianMatrix` is invariant under the row permutation), so
$\mathbb{P}[X \le -\sqrt{\ell}] \ge 9\ell/(96\ell + 192) \ge 0.0919$ at $\ell \ge 100$. On
$\{X \le -\sqrt{\ell}\} \cap \{\|\mathbf{\omega}_2\|^2 < 2\ell\}$ the event holds, since
$1 - (1-\delta)^2 < 2\delta = 1/(2\sqrt{\ell})$. The chi-square upper tail at $\beta = 2$
(`measureReal_norm_sq_ge_mul_card_le_of_hasLaw_gaussianVector`) bounds the complement by
$e^{(\ell/2)(\log 2 - 1)} \le e^{-15}$. Then $0.0919 - e^{-15} \ge 1/12$ (`norm_num`, with
`Real.exp_le_one_div` or `Real.add_one_le_exp`-type estimates for $e^{-15}$). -/
theorem le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix {X : Ω → Matrix (Fin 2) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ) (hl : 100 ≤ Fintype.card l) :
    1 / 12 ≤ μ.real {ω | ∑ j, X ω 0 j ^ 2 <
      (1 - 1 / (4 * √(Fintype.card l : ℝ))) ^ 2 * ∑ j, X ω 1 j ^ 2} := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have hℓ : (100 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
  have hrow0 : HasLaw (fun ω => X ω 0) (gaussianVector l) μ := hX.eval 0
  have hrow1 : HasLaw (fun ω => X ω 1) (gaussianVector l) μ := hX.eval 1
  have hind : IndepFun (fun ω => X ω 0) (fun ω => X ω 1) μ :=
    hX.iIndepFun_eval.indepFun (show (0 : Fin 2) ≠ 1 by decide)
  have hconvD : ∀ ω, ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 =
      ‖WithLp.toLp 2 (X ω 0)‖ ^ 2 - ‖WithLp.toLp 2 (X ω 1)‖ ^ 2 := by
    intro ω
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  have hI2 : ∫ ω, (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2 ∂μ = 4 * Fintype.card l := by
    simp_rw [hconvD]
    exact integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector hrow0 hrow1 hind
  have hI4 : ∫ ω, (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 4 ∂μ =
      48 * (Fintype.card l : ℝ) ^ 2 + 96 * Fintype.card l := by
    simp_rw [hconvD]
    exact integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector hrow0 hrow1 hind
  have hint4 : Integrable (fun ω => (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 4) μ := by
    by_contra h
    rw [integral_undef h] at hI4
    nlinarith
  have hPZ : μ.real {ω | (Fintype.card l : ℝ) < (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2} *
      (48 * (Fintype.card l : ℝ) ^ 2 + 96 * Fintype.card l) ≥ 9 * (Fintype.card l : ℝ) ^ 2 := by
    have hD : Continuous fun A : Matrix (Fin 2) l ℝ =>
        (∑ j, A 0 j ^ 2 - ∑ j, A 1 j ^ 2) ^ 2 := by fun_prop
    have hZ2 : MemLp (fun ω => (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2) 2 μ := by
      refine (memLp_two_iff_integrable_sq
        (hD.measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable).2 ?_
      refine hint4.congr (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Function.comp_apply]
      ring
    have hPZ0 := sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt (μ := μ)
      (Z := fun ω => (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2)
      (Filter.Eventually.of_forall fun ω => sq_nonneg _) hZ2 (θ := 1 / 4) (by norm_num)
      (by norm_num)
    have hZ4 : ∫ ω, ((∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2) ^ 2 ∂μ =
        48 * (Fintype.card l : ℝ) ^ 2 + 96 * Fintype.card l := by
      simp only [← pow_mul]
      exact hI4
    have hset : {ω | 1 / 4 * ∫ ω', (∑ j, X ω' 0 j ^ 2 - ∑ j, X ω' 1 j ^ 2) ^ 2 ∂μ <
        (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2} =
        {ω | (Fintype.card l : ℝ) < (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2} := by
      have hI : ∫ ω', (∑ j, X ω' 0 j ^ 2 - ∑ j, X ω' 1 j ^ 2) ^ 2 ∂μ = 4 * Fintype.card l := hI2
      rw [hI]
      congr 1
      ext ω
      constructor <;> intro h <;> linarith
    rw [hset, hZ4, hI2] at hPZ0
    nlinarith [hPZ0]
  have hsymm : μ.real {ω | √(Fintype.card l : ℝ) < ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2} =
      μ.real {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} := by
    have hG : AEMeasurable (fun ω => X ω 0) μ := hrow0.aemeasurable
    have hH : AEMeasurable (fun ω => X ω 1) μ := hrow1.aemeasurable
    have hpair : AEMeasurable (fun ω => (X ω 0, X ω 1)) μ := hG.prodMk hH
    have hlaw : μ.map (fun ω => (X ω 0, X ω 1)) = (gaussianVector l).prod (gaussianVector l) := by
      rw [(indepFun_iff_map_prod_eq_prod_map_map hG hH).1 hind, hrow0.map_eq, hrow1.map_eq]
    have hlaw' : μ.map (fun ω => (X ω 1, X ω 0)) = (gaussianVector l).prod (gaussianVector l) := by
      have e : (fun ω => (X ω 1, X ω 0)) = Prod.swap ∘ (fun ω => (X ω 0, X ω 1)) := rfl
      rw [e, ← AEMeasurable.map_map_of_aemeasurable measurable_swap.aemeasurable hpair, hlaw,
        Measure.prod_swap]
    have hS : MeasurableSet {p : (l → ℝ) × (l → ℝ) |
        √(Fintype.card l : ℝ) < ∑ j, p.1 j ^ 2 - ∑ j, p.2 j ^ 2} :=
      measurableSet_lt measurable_const (by fun_prop)
    have e1 : {ω | √(Fintype.card l : ℝ) < ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2} =
        (fun ω => (X ω 0, X ω 1)) ⁻¹' {p : (l → ℝ) × (l → ℝ) |
          √(Fintype.card l : ℝ) < ∑ j, p.1 j ^ 2 - ∑ j, p.2 j ^ 2} := rfl
    have e2 : {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} =
        (fun ω => (X ω 1, X ω 0)) ⁻¹' {p : (l → ℝ) × (l → ℝ) |
          √(Fintype.card l : ℝ) < ∑ j, p.1 j ^ 2 - ∑ j, p.2 j ^ 2} := by
      ext ω
      simp only [Set.mem_setOf_eq, Set.mem_preimage]
      constructor <;> intro h <;> linarith
    rw [e1, e2, measureReal_def, measureReal_def,
      ← Measure.map_apply_of_aemeasurable hpair hS,
      ← Measure.map_apply_of_aemeasurable (hH.prodMk hG) hS, hlaw, hlaw']
  have hsub : {ω | (Fintype.card l : ℝ) < (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) ^ 2} ⊆
      {ω | √(Fintype.card l : ℝ) < ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2} ∪
        {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have ht : √(Fintype.card l : ℝ) ^ 2 = Fintype.card l := Real.sq_sqrt (by positivity)
    have htpos : 0 ≤ √(Fintype.card l : ℝ) := Real.sqrt_nonneg _
    rcases le_or_gt 0 (∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2) with h | h
    · left; nlinarith
    · right; nlinarith
  have hneg : 1 / 11 ≤
      μ.real {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} := by
    have hmono := measureReal_mono (μ := μ) hsub (measure_ne_top μ _)
    have hun := measureReal_union_le (μ := μ)
      {ω | √(Fintype.card l : ℝ) < ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2}
      {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)}
    rw [hsymm] at hun
    have hA : 0 < 48 * (Fintype.card l : ℝ) ^ 2 + 96 * Fintype.card l := by positivity
    by_contra hlt
    push_neg at hlt
    have h1 := mul_le_mul_of_nonneg_right (show μ.real _ ≤ 2 *
      μ.real {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} by linarith) hA.le
    have h2 := mul_lt_mul_of_pos_right hlt hA
    nlinarith
  have htail : μ.real {ω | 2 * (Fintype.card l : ℝ) ≤ ∑ j, X ω 1 j ^ 2} ≤ 1 / 132 := by
    have hconv : ∀ ω, ‖WithLp.toLp 2 (X ω 1)‖ ^ 2 = ∑ j, X ω 1 j ^ 2 := by
      intro ω
      rw [EuclideanSpace.norm_sq_eq]
      simp [Real.norm_eq_abs, sq_abs]
    have hT := measureReal_norm_sq_ge_mul_card_le_of_hasLaw_gaussianVector hrow1 (β := 2)
      (by norm_num)
    simp only [hconv] at hT
    have hlog := Real.log_two_lt_d9
    have h5 : (6 : ℝ) ≤ Real.exp 5 := by linarith [Real.add_one_le_exp (5 : ℝ)]
    have h15 : Real.exp 15 = Real.exp 5 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have hx : (Fintype.card l : ℝ) / 2 * (1 - 2 + Real.log 2) ≤ -15 := by
      have : (1 - 2 + Real.log 2) ≤ -(3 / 10) := by norm_num at hlog ⊢; linarith
      nlinarith
    have hexp := Real.exp_le_exp.2 hx
    have h132 : (132 : ℝ) ≤ Real.exp 15 := by
      rw [h15]; exact (by norm_num : (132 : ℝ) ≤ 6 ^ 3).trans (pow_le_pow_left₀ (by norm_num) h5 3)
    have hneg15 : Real.exp (-15) ≤ 1 / 132 := by
      calc Real.exp (-15) = (Real.exp 15)⁻¹ := Real.exp_neg 15
        _ ≤ (132 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h132
        _ = 1 / 132 := by norm_num
    linarith
  have hincl : {ω | ∑ j, X ω 0 j ^ 2 - ∑ j, X ω 1 j ^ 2 < -√(Fintype.card l : ℝ)} ⊆
      {ω | ∑ j, X ω 0 j ^ 2 < (1 - 1 / (4 * √(Fintype.card l : ℝ))) ^ 2 * ∑ j, X ω 1 j ^ 2} ∪
        {ω | 2 * (Fintype.card l : ℝ) ≤ ∑ j, X ω 1 j ^ 2} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    have hU : 0 ≤ ∑ j, X ω 0 j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have hV : 0 ≤ ∑ j, X ω 1 j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    have ht : √(Fintype.card l : ℝ) ^ 2 = Fintype.card l := Real.sq_sqrt (by positivity)
    have htpos : 0 < √(Fintype.card l : ℝ) := Real.sqrt_pos.2 (by linarith)
    by_cases hc : 2 * (Fintype.card l : ℝ) ≤ ∑ j, X ω 1 j ^ 2
    · exact Or.inr hc
    · left
      push_neg at hc
      have hqt : 1 / (4 * √(Fintype.card l : ℝ)) * √(Fintype.card l : ℝ) = 1 / 4 := by
        field_simp
      have hqpos : 0 < 1 / (4 * √(Fintype.card l : ℝ)) := by positivity
      have h1 : 1 / (4 * √(Fintype.card l : ℝ)) * ∑ j, X ω 1 j ^ 2 ≤
          1 / (4 * √(Fintype.card l : ℝ)) * (2 * √(Fintype.card l : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (by rw [ht]; linarith) hqpos.le
      have h2 : 1 / (4 * √(Fintype.card l : ℝ)) * (2 * √(Fintype.card l : ℝ) ^ 2) =
          √(Fintype.card l : ℝ) / 2 := by
        have : 1 / (4 * √(Fintype.card l : ℝ)) * (2 * √(Fintype.card l : ℝ) ^ 2) =
            2 * √(Fintype.card l : ℝ) *
              (1 / (4 * √(Fintype.card l : ℝ)) * √(Fintype.card l : ℝ)) := by
          ring
        rw [this, hqt]; ring
      have h3 := mul_nonneg (sq_nonneg (1 / (4 * √(Fintype.card l : ℝ)))) hV
      have key : (1 - 1 / (4 * √(Fintype.card l : ℝ))) ^ 2 * ∑ j, X ω 1 j ^ 2 =
          ∑ j, X ω 1 j ^ 2 - (2 * (1 / (4 * √(Fintype.card l : ℝ))) -
            (1 / (4 * √(Fintype.card l : ℝ))) ^ 2) * ∑ j, X ω 1 j ^ 2 := by ring
      rw [key]
      nlinarith [h1, h2, h3]
  have h1 := measureReal_mono (μ := μ) hincl (measure_ne_top μ _)
  have h2 := measureReal_union_le (μ := μ) {ω | ∑ j, X ω 0 j ^ 2 <
    (1 - 1 / (4 * √(Fintype.card l : ℝ))) ^ 2 * ∑ j, X ω 1 j ^ 2}
    {ω | 2 * (Fintype.card l : ℝ) ≤ ∑ j, X ω 1 j ^ 2}
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
Proof: M, about 60 lines. Write $s = 1 - \delta$; the error is at least $s^2$ everywhere
(Eckart–Young: `frobNorm_sub_truncatedSVD_le_of_rank_le` for the rank-one `earlyTruncatedRSVD`,
`rank_earlyTruncatedRSVD_le`) and at least $s^2 + (1 - s^2)/2$ on the misranking event
(`add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq`), whose probability is at least
$1/12$ (`le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix`). Integrate the pointwise bound
$s^2 + \frac{1-s^2}{2}\mathbf{1}_E$ (`integral_mono`, integrability from
`integrable_frobNorm_sub_earlyTruncatedRSVD_sq`-type boundedness: the error is at most
$\|\mathbf{A}\|_{\mathsf{F}}^2 = 1 + s^2$). Then $(1 - s^2)/24 \ge s^2/(100\sqrt{\ell})$ since
$1 - s^2 = \delta(2 - \delta) \ge 1.97\,\delta$ and $\delta \le 1/40$. The optimum:
`frobNorm_sub_truncatedSVD_sq` with the singular values $1, s$ of the diagonal matrix.
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

/-- **Constant-probability $(1+\varepsilon)$ also needs $\varepsilon^{-2}$ samples at $k = 1$**: for
$\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with $\delta = 1/(4\sqrt{\ell})$, a standard
Gaussian $2 \times \ell$ test matrix $\mathbf{\Omega}$, $\ell \ge 100$ and
$16\varepsilon^2\ell < 1$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)
\|_{\mathsf{F}}^2 > (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1\|_{\mathsf{F}}^2
\Bigr] \ge \frac{1}{12}\,.$$
No printed source. New (research note OP1, §1).
Proof: S, about 30 lines. On the misranking event of
`le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix` the error is at least
$s^2 + (1 - s^2)/2 \ge (1 + \delta)s^2$
(`add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq`; $2 - \delta \ge 2(1-\delta)^2$),
and $\delta > \varepsilon$ when $16\varepsilon^2\ell < 1$ (for $\varepsilon \le 0$ trivially); the
optimum is $s^2 > 0$. `measureReal_mono`. -/
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
  have hOPT : frobNorm (Matrix.diagonal ![1, 1 - δ] -
      truncatedSVD (Matrix.diagonal ![1, 1 - δ]) 1) ^ 2 ≤ (1 - δ) ^ 2 := by
    have hrank : (Matrix.diagonal (![1, 0] : Fin 2 → ℝ)).rank ≤ 1 := by
      rw [Matrix.rank_diagonal, Fintype.card_subtype, Finset.card_le_one]
      intro a ha b hb
      fin_cases a <;> fin_cases b <;> simp_all
    have h := frobNorm_sub_truncatedSVD_le_of_rank_le (Matrix.diagonal ![1, 1 - δ]) hrank
    have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
    rw [Matrix.diagonal_sub, frobNorm_diagonal_sq] at h2
    simpa [Fin.sum_univ_two] using h2
  refine hE.trans (measureReal_mono fun ω hω => ?_)
  have hA := add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq (Ω' := X ω) (l := l)
    hs0 hs1 hω
  simp only [Set.mem_ofPred_eq] at hω ⊢
  have h1 : (1 + ε) * frobNorm (Matrix.diagonal ![1, 1 - δ] -
      truncatedSVD (Matrix.diagonal ![1, 1 - δ]) 1) ^ 2 ≤ (1 + ε) * (1 - δ) ^ 2 :=
    mul_le_mul_of_nonneg_left hOPT (by linarith [neg_abs_le ε])
  have h2 : ε * (1 - δ) ^ 2 < δ * (1 - δ) ^ 2 :=
    mul_lt_mul_of_pos_right (lt_of_le_of_lt (le_abs_self ε) hεδ) hsq
  have h3 : δ * (1 - δ) ^ 2 ≤ (1 - (1 - δ) ^ 2) / 2 := by
    nlinarith [mul_nonneg (sq_nonneg δ) (by linarith : (0:ℝ) ≤ 3 / 2 - δ)]
  nlinarith

/-- **Relative error $1 + \varepsilon$ in expectation needs $\ell \ge 10^{-4}/\varepsilon^2$
samples**: if a standard Gaussian test matrix $\mathbf{\Omega}$ with $\ell \ge 100$ columns gives
$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)
\|_{\mathsf{F}}^2 \le (1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1
\|_{\mathsf{F}}^2$ for every real $2 \times 2$ matrix $\mathbf{A}$, then
$1 \le 10^4\varepsilon^2\ell$. The library's sufficient condition is $\ell \ge 900k/\varepsilon^2$
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`):
the rate is $\Theta(\varepsilon^{-2})$.
No printed source. New (research note OP1).
Proof: S, about 20 lines. Apply the hypothesis to the instance of
`le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix`; the optimum
$(1 - \delta)^2$ is positive, so $1/(100\sqrt{\ell}) \le \varepsilon$; square
(`Real.sq_sqrt`). -/
theorem one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le
    {X : Ω → Matrix (Fin 2) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ)
    (hl : 100 ≤ Fintype.card l) {ε : ℝ}
    (h : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) 1) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A 1) ^ 2) :
    1 ≤ 10 ^ 4 * ε ^ 2 * Fintype.card l := by
  set δ : ℝ := 1 / (4 * √(Fintype.card l : ℝ)) with hδ
  set t : ℝ := √(Fintype.card l : ℝ) with ht
  have hl' : (100 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have ht2 : t ^ 2 = Fintype.card l := Real.sq_sqrt (by linarith)
  have hδpos : 0 < δ := by positivity
  have ht10 : 10 ≤ t := by nlinarith
  have hδ1 : δ ≤ 1 / 40 := by
    rw [hδ]
    exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  set s : ℝ := 1 - δ with hs
  have hs0 : s ≠ 0 := by intro h0; linarith
  have hE := le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix hX hl
  have hH := h (Matrix.diagonal ![1, s])
  have hσ : 0 < singularValues (Matrix.diagonal ![(1 : ℝ), s]) 1 := by
    rw [singularValues_pos_iff]
    have hrank : 1 < (Matrix.diagonal ![(1 : ℝ), s]).rank := by
      rw [Matrix.rank_diagonal]
      have : ∀ i, ![(1 : ℝ), s] i ≠ 0 := by
        intro i; fin_cases i <;> simp [hs0]
      simp only [this, ne_eq, not_false_eq_true, Fintype.card_subtype_true]
      simp
    exact hrank
  have hOPT : 0 < frobNorm (Matrix.diagonal ![(1 : ℝ), s] -
      truncatedSVD (Matrix.diagonal ![(1 : ℝ), s]) 1) ^ 2 := by
    rw [frobNorm_sub_truncatedSVD_sq]
    have h1 : (1 : ℕ) ∈ Finset.Ico 1 (min (Fintype.card (Fin 2)) (Fintype.card (Fin 2))) := by
      simp
    exact lt_of_lt_of_le (pow_pos hσ 2)
      (Finset.single_le_sum (f := fun i => singularValues (Matrix.diagonal ![(1 : ℝ), s]) i ^ 2)
        (fun i _ => sq_nonneg _) h1)
  have hc : 1 + 1 / (100 * t) ≤ 1 + ε := by
    have hle := (hE.trans hH)
    exact le_of_mul_le_mul_right hle hOPT
  have hkey : 1 / (100 * t) ≤ ε := by linarith
  have h1 : 1 ≤ 100 * t * ε := by
    rw [div_le_iff₀ (by positivity)] at hkey
    linarith
  have h2 : 1 ≤ (100 * t * ε) ^ 2 := by
    nlinarith
  nlinarith [ht2]

/-- **$O(k/\varepsilon)$ samples do not suffice for the early-truncated randomized SVD**: there are
no constants $C, \varepsilon_0 > 0$ such that for every standard Gaussian $n \times \ell$ test
matrix $\mathbf{\Omega}$, every $\mathbf{A}$, $k$ and $0 < \varepsilon \le \varepsilon_0$ with
$\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The negation of the $\varepsilon^{-1}$ analogue of
`NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`
(which holds with $\ell \ge Ck/\varepsilon^2$).
No printed source. New (research note OP1).
Proof: S, about 30 lines. Given $C, \varepsilon_0$, take $k = 1$, $\mathbf{A}$ the
$2 \times 2$ instance, $\Omega = $ `Matrix (Fin 2) (Fin L) ℝ` with $\mu = $ `gaussianMatrix` and
$\mathbf{X} = \mathrm{id}$ (`ProbabilityTheory.HasLaw.id`), $\varepsilon$ small with
$\max(C/\varepsilon, 100) + 1 < 10^{-4}/\varepsilon^2$ and $\varepsilon \le \varepsilon_0$, and
$L = \lceil\max(C/\varepsilon, 100)\rceil$ (`Nat.le_ceil`); then
`one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le` contradicts
$10^4\varepsilon^2 L < 1$. -/
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

/-! ### General $k$: the block instance -/

/-- The two frame blocks carry the trace of the frame:
$\operatorname{tr}\mathbf{U}_h\mathbf{U}_h^{\mathsf{H}} +
\operatorname{tr}\mathbf{U}_t\mathbf{U}_t^{\mathsf{H}} = k$ for orthonormal $k$ columns. -/
private theorem trace_toRows_mul_conjTranspose_add {k : ℕ} {U : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ}
    (hU : HasOrthonormalCols U) :
    (U.toRows₁ * U.toRows₁ᴴ).trace + (U.toRows₂ * U.toRows₂ᴴ).trace = k := by
  have h1 : (U * Uᴴ).trace = k := by
    rw [Matrix.trace_mul_comm, HasOrthonormalCols.conjTranspose_mul_self hU, Matrix.trace_one,
      Fintype.card_fin]
  have h2 : (U * Uᴴ).trace =
      (U.toRows₁ * U.toRows₁ᴴ).trace + (U.toRows₂ * U.toRows₂ᴴ).trace := by
    simp [Matrix.trace, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.toRows₁, Matrix.toRows₂]
  rw [← h2, h1]

/-- The Frobenius norm of a projector times a diagonal matrix:
$\|\mathbf{P}\mathbf{D}\|_{\mathsf{F}}^2 = \sum_j d_j^2 \mathbf{P}_{jj}$ for a real star
projection $\mathbf{P}$. -/
private theorem frobNorm_mul_diagonal_sq_of_isStarProjection {n : Type*} [Fintype n]
    [DecidableEq n] {P : Matrix n n ℝ} (hP : IsStarProjection P) (d : n → ℝ) :
    frobNorm (P * Matrix.diagonal d) ^ 2 = ∑ j, d j ^ 2 * P j j := by
  have hsym : ∀ x j, P x j = P j x := fun x j => by
    have h := congrFun (congrFun hP.isHermitian.eq x) j
    simpa [Matrix.conjTranspose_apply] using h.symm
  have hcol : ∀ j, ∑ x, P x j ^ 2 = P j j := fun j => by
    have h := congrFun (congrFun hP.mul_self j) j
    rw [Matrix.mul_apply] at h
    rw [← h]
    exact Finset.sum_congr rfl fun x _ => by rw [hsym j x]; ring
  rw [frobNorm_sq_eq_sum_sq]
  simp only [Matrix.mul_diagonal, mul_pow]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hcol j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- The tail of the head block of a frame:
$\|\mathbf{U}_h^{\mathsf{T}}\mathbf{\Omega}_1\|_{\mathsf{F}}^2
\le \|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2 (k - \operatorname{tr}
\mathbf{U}_h\mathbf{U}_h^{\mathsf{T}})$, from $\mathbf{I} - \mathbf{U}_h\mathbf{U}_h^{\mathsf{T}}
\succeq 0$ and $\mathbf{\Omega}_1\mathbf{\Omega}_1^{\mathsf{T}} \succeq $\sigma_{k-1}^2 \mathbf{I}$. -/
private theorem frobNorm_conjTranspose_mul_sq_le_of_posSemidef {k : ℕ} {l : Type*} [Fintype l]
    (Ω : Matrix (Fin k) l ℝ) (Uh : Matrix (Fin k) (Fin k) ℝ)
    (hPSD : (1 - Uh * Uhᴴ).PosSemidef) (T : ℝ) (hT : (Uh * Uhᴴ).trace = k - T) :
    frobNorm (Uhᴴ * Ω) ^ 2 ≤ frobNorm Ω ^ 2 - singularValues Ω (k - 1) ^ 2 * T := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hT0 : T = 0 := by simpa using hT.symm
    rw [hT0, mul_zero, sub_zero, frobNorm_sq_eq_sum]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (sq_nonneg _).trans_eq' (by simp) |>.trans_eq' rfl
  have hG : (Ω * Ωᴴ - singularValues Ω (k - 1) ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef :=
    by
    have h := (Matrix.isHermitian_mul_conjTranspose_self Ω).eigenvalue_last_smul_one_le
      (k := k - 1) (by simp; omega)
    rw [singularValues_sq_eq_eigenvalue_mul_conjTranspose_self]
    exact Matrix.le_iff.mp h
  have htr := hPSD.trace_mul_nonneg hG
  have e1 : frobNorm (Uhᴴ * Ω) ^ 2 = ((Uh * Uhᴴ) * (Ω * Ωᴴ)).trace := by
    rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc, RCLike.re_to_real]
  have e2: frobNorm Ω ^ 2 = (Ω * Ωᴴ).trace := by
    rw [frobNorm_sq_eq_re_trace, RCLike.re_to_real, Matrix.trace_mul_comm]
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hT, Fintype.card_fin]
    at htr e1 e2 ⊢
  have h3 : singularValues Ω (k - 1) ^ 2 * ((k : ℝ) - ((k : ℝ) - T)) =
      singularValues Ω (k - 1) ^ 2 * T := by ring
  linarith

/-- A frame of the dominant $k$-dimensional range: $\mathbf{P}_{\llbracket \mathbf{Y}\rrbracket_k} =
\mathbf{U}\mathbf{U}^{\mathsf{H}}$ with $\mathbf{U}$ having orthonormal columns, when
$\operatorname{rank}\mathbf{Y} \ge k$. -/
private theorem exists_orthonormalCols_rangeProjector_truncatedSVD {n l : Type*} [Fintype n]
    [DecidableEq n] [Fintype l] (Y : Matrix n l ℝ) (k : ℕ) (hr : k ≤ Y.rank) :
    ∃ U : Matrix n (Fin k) ℝ, HasOrthonormalCols U ∧
      rangeProjector (truncatedSVD Y k) = U * Uᴴ := by
  obtain ⟨U, hU, hrange⟩ := exists_hasOrthonormalCols_range_eq (truncatedSVD Y k) (p := Fin k)
    (by rw [rank_truncatedSVD, min_eq_left hr]; simp)
  refine ⟨U, hU, ?_⟩
  rw [← hU.rangeProjector_eq]
  exact rangeProjector_inj.mpr hrange.symm

/-- The Gram matrix of a block column matrix splits into its two blocks:
$\mathbf{V}^{\mathsf{H}}\mathbf{V} = \mathbf{V}_1^{\mathsf{H}}\mathbf{V}_1 +
\mathbf{V}_2^{\mathsf{H}}\mathbf{V}_2$. -/
private theorem conjTranspose_mul_self_eq_toRows {k : ℕ} (V : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) :
    Vᴴ * V = V.toRows₁ᴴ * V.toRows₁ + V.toRows₂ᴴ * V.toRows₂ := by
  ext i j
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.toRows₁, Matrix.toRows₂]

/-- The block form of $\mathbf{V}^{\mathsf{H}}\mathbf{D}\mathbf{\Omega}$ for the diagonal weight
$\mathbf{D} = \operatorname{diag}(\mathbf{I}, s\mathbf{I})$:
$\mathbf{V}^{\mathsf{H}}\mathbf{D}\mathbf{\Omega} = \mathbf{V}_1^{\mathsf{H}}\mathbf{\Omega}_1 +
s\,\mathbf{V}_2^{\mathsf{H}}\mathbf{\Omega}_2$. -/
private theorem conjTranspose_mul_diagonal_mul_eq_toRows {k : ℕ} {l : Type*} [Fintype l] (s : ℝ)
    (V : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) (Ω : Matrix (Fin k ⊕ Fin k) l ℝ) :
    Vᴴ * (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω) =
      V.toRows₁ᴴ * Ω.toRows₁ + s • (V.toRows₂ᴴ * Ω.toRows₂) := by
  ext i j
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [Fintype.sum_sum_type, Matrix.mul_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.toRows₁, Matrix.toRows₂, Matrix.conjTranspose_apply,
    Sum.elim_inl, Sum.elim_inr, smul_eq_mul, Matrix.of_apply, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> ring

/-- An orthogonal matrix that realises the nuclear norm against the second block:
$\langle \mathbf{R}\mathbf{\Omega}_1, \mathbf{\Omega}_2\rangle_{\mathsf{F}} =
\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_*$, from an SVD of
$\mathbf{\Omega}_2\mathbf{\Omega}_1^{\mathsf{T}}$. -/
private theorem exists_orthogonal_frobInner_eq_nuclearNorm {k : ℕ} {l : Type*} [Fintype l]
    (Ω₁ Ω₂ : Matrix (Fin k) l ℝ) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, Rᴴ * R = 1 ∧
      frobInner Ω₁ (Rᴴ * Ω₂) = nuclearNorm (Ω₁ * Ω₂ᴴ) := by
  obtain ⟨Us, Vs, hS⟩ := exists_isSVD (Ω₂ * Ω₁ᴴ) (k := k)
    (by simpa using (Ω₂ * Ω₁ᴴ).rank_le_card_height) (by simp) (by simp)
  have hUU : Usᴴ * Us = 1 := hS.hasOrthonormalCols_left
  have hVV : Vsᴴ * Vs = 1 := hS.hasOrthonormalCols_right
  have hVV' : Vs * Vsᴴ = 1 := mul_eq_one_comm.mp hVV
  refine ⟨Us * Vsᴴ, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Usᴴ, hUU, Matrix.one_mul, hVV']
  · have hN : nuclearNorm (Ω₁ * Ω₂ᴴ) = ∑ i : Fin k, singularValues (Ω₂ * Ω₁ᴴ) (i : ℕ) := by
      rw [← nuclearNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      exact hS.nuclearNorm_eq_sum
    rw [hN, ← frobInner_mul_left, frobInner_eq_re_trace, RCLike.re_to_real]
    have t1 : ((Us * Vsᴴ * Ω₁)ᴴ * Ω₂).trace = (Vs * (Usᴴ * (Ω₂ * Ω₁ᴴ))).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have t2 : Usᴴ * (Ω₂ * Ω₁ᴴ) =
        Matrix.diagonal (fun i : Fin k => singularValues (Ω₂ * Ω₁ᴴ) (i : ℕ)) * Vsᴴ := by
      conv_lhs => rw [hS.eq]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Usᴴ Us, hUU, Matrix.one_mul]
      rfl
    rw [t1, t2, Matrix.trace_mul_comm, Matrix.mul_assoc, hVV, Matrix.mul_one, Matrix.trace_diagonal]

/-- The cross term of two frame blocks: $|\langle \mathbf{U}_h^{\mathsf{T}}\mathbf{\Omega}_1,
\mathbf{U}_t^{\mathsf{T}}\mathbf{\Omega}_2\rangle_{\mathsf{F}}| \le
\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{k\|\mathbf{U}_t\|_{\mathsf{F}}^2}$
when $\|\mathbf{U}_h\|_{\mathsf{F}}^2 \le k$. -/
private theorem abs_frobInner_conjTranspose_mul_le {k : ℕ} {l : Type*} [Fintype l]
    (Ω₁ Ω₂ : Matrix (Fin k) l ℝ) (Uh Ut : Matrix (Fin k) (Fin k) ℝ)
    (hUh : frobNorm Uh ^ 2 ≤ k) :
    |frobInner (Uhᴴ * Ω₁) (Utᴴ * Ω₂)| ≤ specNorm (Ω₁ * Ω₂ᴴ) * √(k * frobNorm Ut ^ 2) := by
  have e : frobInner (Uhᴴ * Ω₁) (Utᴴ * Ω₂) = frobInner (Uh * Utᴴ) (Ω₁ * Ω₂ᴴ) := by
    rw [frobInner_mul_left, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc]
    rw [frobInner_eq_re_trace_mul_conjTranspose, frobInner_eq_re_trace_mul_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have h := Matrix.trace_conjTranspose (Ω₁ * (Ω₂ᴴ * (Ut * Uhᴴ)))
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      star_trivial] at h
    rw [h]
  have hnuc : nuclearNorm (Uh * Utᴴ) ≤ frobNorm Uh * frobNorm Ut := by
    have := nuclearNorm_mul_le_frobNorm_mul_frobNorm Uh Utᴴ
    rwa [frobNorm_conjTranspose] at this
  have hfr : frobNorm Uh * frobNorm Ut ≤ √(k * frobNorm Ut ^ 2) := by
    calc frobNorm Uh * frobNorm Ut = √((frobNorm Uh * frobNorm Ut) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(k * frobNorm Ut ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hUh (sq_nonneg _))
  rw [e]
  refine (abs_frobInner_le_nuclearNorm_mul_specNorm _ _).trans ?_
  exact (mul_le_mul_of_nonneg_right (hnuc.trans hfr) (specNorm_nonneg _)).trans_eq (mul_comm _ _)

/-- The residual of a projector on a diagonal matrix:
$\|\mathbf{D} - \mathbf{P}\mathbf{D}\|_{\mathsf{F}}^2 =
\sum_j d_j^2 - \sum_j d_j^2 \mathbf{P}_{jj}$. -/
private theorem frobNorm_diagonal_sub_mul_diagonal_sq {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) (d : n → ℝ) :
    frobNorm (Matrix.diagonal d - P * Matrix.diagonal d) ^ 2 =
      ∑ j, d j ^ 2 - ∑ j, d j ^ 2 * P j j := by
  have h := hP.frobNorm_sq_eq_add (Matrix.diagonal d)
  rw [frobNorm_mul_diagonal_sq_of_isStarProjection hP] at h
  have e : Matrix.diagonal d - P * Matrix.diagonal d = (1 - P) * Matrix.diagonal d := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  have hD : frobNorm (Matrix.diagonal d) ^ 2 = ∑ j, d j ^ 2 := by
    rw [frobNorm_diagonal_sq]
    simp [Real.norm_eq_abs, sq_abs]
  rw [e]
  linarith

/-- Ky Fan maximality of the truncated SVD, in the Frobenius norm: a projection onto $k$
orthonormal columns captures at most the energy of the dominant $k$-frame of $\mathbf{Y}$. -/
private theorem frobNorm_conjTranspose_mul_le_rangeProjector_truncatedSVD {n l : Type*}
    [Fintype n] [DecidableEq n] [Fintype l] (Y : Matrix n l ℝ) (k : ℕ)
    {V : Matrix n (Fin k) ℝ} (hV : HasOrthonormalCols V) :
    frobNorm (Vᴴ * Y) ^ 2 ≤ frobNorm (rangeProjector (truncatedSVD Y k) * Y) ^ 2 := by
  have hB : (V * (Vᴴ * Y)).rank ≤ k :=
    (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_mul_le_left _ _).trans
      (by simpa using Matrix.rank_le_card_height Vᴴ))
  have h1 := frobNorm_sub_truncatedSVD_le_of_rank_le Y hB
  have e1 : Y - rangeProjector (truncatedSVD Y k) * Y =
      (1 - rangeProjector (truncatedSVD Y k)) * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  have e2 : Y - V * (Vᴴ * Y) = (1 - V * Vᴴ) * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [← rangeProjector_truncatedSVD_mul Y k, e1, e2] at h1
  have hP := (isStarProjection_rangeProjector (truncatedSVD Y k)).frobNorm_sq_eq_add Y
  have hV' := (hV.isStarProjection_mul_conjTranspose).frobNorm_sq_eq_add Y
  rw [Matrix.mul_assoc, hV.frobNorm_mul_left] at hV'
  have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
  linarith

/-- The competitor frame $\mathbf{V} = [\cos\theta\,\mathbf{I}; \sin\theta\,\mathbf{R}]$ has
orthonormal columns when $\mathbf{R}$ does. -/
private theorem hasOrthonormalCols_fromRows_cos_sin {k : ℕ} {θ : ℝ}
    {R : Matrix (Fin k) (Fin k) ℝ} (hR : HasOrthonormalCols R) :
    HasOrthonormalCols
      (Matrix.fromRows (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ)) (Real.sin θ • R)) := by
  unfold HasOrthonormalCols at hR ⊢
  rw [conjTranspose_mul_self_eq_toRows, Matrix.toRows₁_fromRows, Matrix.toRows₂_fromRows]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, hR, ← add_smul]
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    nlinarith [Real.sin_sq_add_cos_sq θ]
  rw [h, one_smul]

/-- The Frobenius norm of the competitor's projected sketch:
$\|\mathbf{V}^{\mathsf{T}}\mathbf{D}\mathbf{\Omega}\|_{\mathsf{F}}^2 = \cos^2\theta\,
\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 + 2\cos\theta\, s\sin\theta\,
\langle\mathbf{\Omega}_1, \mathbf{R}^{\mathsf{T}}\mathbf{\Omega}_2\rangle_{\mathsf{F}} +
s^2\sin^2\theta\,\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_fromRows_cos_sin_mul_diagonal_sq {k : ℕ} {l : Type*} [Fintype l] {s : ℝ}
    (θ : ℝ) {R : Matrix (Fin k) (Fin k) ℝ} (hR : HasOrthonormalCols R)
    (Ω : Matrix (Fin k ⊕ Fin k) l ℝ) :
    frobNorm ((Matrix.fromRows (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ)) (Real.sin θ • R))ᴴ *
        (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω)) ^ 2 =
      Real.cos θ ^ 2 * frobNorm Ω.toRows₁ ^ 2 +
        2 * (Real.cos θ * (s * Real.sin θ)) * frobInner Ω.toRows₁ (Rᴴ * Ω.toRows₂) +
        (s * Real.sin θ) ^ 2 * frobNorm Ω.toRows₂ ^ 2 := by
  have hRH : HasOrthonormalCols Rᴴ := by
    unfold HasOrthonormalCols at hR ⊢
    rw [Matrix.conjTranspose_conjTranspose]
    exact mul_eq_one_comm.mp hR
  rw [conjTranspose_mul_diagonal_mul_eq_toRows, Matrix.toRows₁_fromRows, Matrix.toRows₂_fromRows]
  have e : (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ))ᴴ * Ω.toRows₁ +
      s • ((Real.sin θ • R)ᴴ * Ω.toRows₂) =
      Real.cos θ • Ω.toRows₁ + (s * Real.sin θ) • (Rᴴ * Ω.toRows₂) := by
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial, Matrix.smul_mul,
      Matrix.one_mul, smul_smul, mul_comm, mul_assoc, mul_left_comm]
  rw [e, frobNorm_add_sq, frobInner_smul_left, frobInner_smul_right, frobNorm_real_smul,
    frobNorm_real_smul, hRH.frobNorm_mul_left, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- A real Frobenius norm squared is the trace of $\mathbf{A}\mathbf{A}^{\mathsf{T}}$. -/
private theorem frobNorm_sq_eq_trace_mul_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : frobNorm A ^ 2 = (A * Aᴴ).trace := by
  rw [frobNorm_sq_eq_re_trace, RCLike.re_to_real, Matrix.trace_mul_comm]

/-- The upper bound on the frame energy: with $\mathbf{U}_h, \mathbf{U}_t$ the two blocks of a
frame,
$\|\mathbf{U}_h^{\mathsf{T}}\mathbf{\Omega}_1 +
s\mathbf{U}_t^{\mathsf{T}}\mathbf{\Omega}_2\|_{\mathsf{F}}^2
\le \|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2 T +
2s\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{kT} + s^2\|\mathbf{\Omega}_2\|_2^2 T$
where $T = \|\mathbf{U}_t\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_add_smul_conjTranspose_mul_sq_le {k : ℕ} {l : Type*} [Fintype l] {s : ℝ}
    (hs : 0 ≤ s) (Ω₁ Ω₂ : Matrix (Fin k) l ℝ) (Uh Ut : Matrix (Fin k) (Fin k) ℝ)
    (hPSD : (1 - Uh * Uhᴴ).PosSemidef) {T : ℝ} (hT : (Uh * Uhᴴ).trace = k - T)
    (hTt : frobNorm Ut ^ 2 = T) :
    frobNorm (Uhᴴ * Ω₁ + s • (Utᴴ * Ω₂)) ^ 2 ≤
      frobNorm Ω₁ ^ 2 - singularValues Ω₁ (k - 1) ^ 2 * T +
        2 * s * specNorm (Ω₁ * Ω₂ᴴ) * √(k * T) + s ^ 2 * specNorm Ω₂ ^ 2 * T := by
  have hT0 : 0 ≤ T := by rw [← hTt]; positivity
  have hUh : frobNorm Uh ^ 2 ≤ k := by
    rw [frobNorm_sq_eq_trace_mul_conjTranspose, hT]
    linarith
  have h1 := frobNorm_conjTranspose_mul_sq_le_of_posSemidef Ω₁ Uh hPSD T hT
  have h2 := abs_frobInner_conjTranspose_mul_le Ω₁ Ω₂ Uh Ut hUh
  rw [hTt] at h2
  have h3 : frobNorm (Utᴴ * Ω₂) ^ 2 ≤ T * specNorm Ω₂ ^ 2 := by
    have h := frobNorm_mul_le_frobNorm_mul_specNorm Utᴴ Ω₂
    rw [frobNorm_conjTranspose] at h
    have h' := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
    rw [mul_pow, hTt] at h'
    exact h'
  rw [frobNorm_add_sq, frobInner_smul_right, frobNorm_real_smul, mul_pow, sq_abs]
  have hcross : s * frobInner (Uhᴴ * Ω₁) (Utᴴ * Ω₂) ≤ s * (specNorm (Ω₁ * Ω₂ᴴ) * √(k * T)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hs
  have htail : s ^ 2 * frobNorm (Utᴴ * Ω₂) ^ 2 ≤ s ^ 2 * (T * specNorm Ω₂ ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg s)
  linarith

/-- The first conjunct, in the frame: the error is $k s^2 + (1 - s^2) T$ up to the inequality. -/
private theorem k_mul_sq_add_le_frobNorm_sub_diagonal {k : ℕ} {s : ℝ}
    {U : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ} (hU : HasOrthonormalCols U) {T : ℝ}
    (hT : T = (U.toRows₂ * U.toRows₂ᴴ).trace) :
    (k : ℝ) * s ^ 2 + (1 - s ^ 2) * T ≤
      frobNorm (Matrix.diagonal (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s)) -
        (U * Uᴴ) * Matrix.diagonal
          (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s))) ^ 2 := by
  rw [frobNorm_diagonal_sub_mul_diagonal_sq hU.isStarProjection_mul_conjTranspose]
  have htr := trace_toRows_mul_conjTranspose_add hU
  have hd1 : ∑ j : Fin k ⊕ Fin k, (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s) j) ^ 2
      = k + k * s ^ 2 := by
    simp [Fintype.sum_sum_type]
  have hd2 : ∑ j : Fin k ⊕ Fin k,
      (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s) j) ^ 2 * (U * Uᴴ) j j =
      (U.toRows₁ * U.toRows₁ᴴ).trace + s ^ 2 * (U.toRows₂ * U.toRows₂ᴴ).trace := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, one_pow, one_mul]
    rw [← Finset.mul_sum]
    rfl
  rw [hd1, hd2, hT]
  linarith

/-- The second conjunct, in the frame: the competitor $\mathbf{V}_\theta$ is beaten by the frame
and the frame energy is bounded by its blocks. -/
private theorem conjunct_two_of_frame {k : ℕ} {l : Type*} [Fintype l] {s θ : ℝ} (hs : 0 ≤ s)
    (Ω : Matrix (Fin k ⊕ Fin k) l ℝ) {U : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ}
    (hU : HasOrthonormalCols U) (hPSD : (1 - U.toRows₁ * U.toRows₁ᴴ).PosSemidef) {T : ℝ}
    (hTU : T = (U.toRows₂ * U.toRows₂ᴴ).trace) {R : Matrix (Fin k) (Fin k) ℝ}
    (hR : HasOrthonormalCols R)
    (hcross : frobInner Ω.toRows₁ (Rᴴ * Ω.toRows₂) = nuclearNorm (Ω.toRows₁ * Ω.toRows₂ᴴ))
    (hKF : frobNorm ((Matrix.fromRows (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ))
        (Real.sin θ • R))ᴴ * (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω)) ^ 2 ≤
      frobNorm (Uᴴ * (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω)) ^ 2) :
    2 * s * Real.sin θ * Real.cos θ * nuclearNorm (Ω.toRows₁ * Ω.toRows₂ᴴ) -
        Real.sin θ ^ 2 * (frobNorm Ω.toRows₁ ^ 2 - s ^ 2 * frobNorm Ω.toRows₂ ^ 2) ≤
      T * (s ^ 2 * specNorm Ω.toRows₂ ^ 2 - singularValues Ω.toRows₁ (k - 1) ^ 2) +
        2 * s * specNorm (Ω.toRows₁ * Ω.toRows₂ᴴ) * √(k * T) := by
  rw [frobNorm_fromRows_cos_sin_mul_diagonal_sq θ hR Ω, hcross] at hKF
  rw [conjTranspose_mul_diagonal_mul_eq_toRows] at hKF
  have hT_Uh := trace_toRows_mul_conjTranspose_add hU
  have hT' : (U.toRows₁ * U.toRows₁ᴴ).trace = k - T := by linarith
  have hTt : frobNorm U.toRows₂ ^ 2 = T := by
    rw [frobNorm_sq_eq_trace_mul_conjTranspose, hTU]
  have hup := frobNorm_add_smul_conjTranspose_mul_sq_le hs Ω.toRows₁ Ω.toRows₂ U.toRows₁
    U.toRows₂ hPSD hT' hTt
  have hca : Real.cos θ ^ 2 * frobNorm Ω.toRows₁ ^ 2 =
      frobNorm Ω.toRows₁ ^ 2 - Real.sin θ ^ 2 * frobNorm Ω.toRows₁ ^ 2 := by
    linear_combination frobNorm Ω.toRows₁ ^ 2 * Real.cos_sq_add_sin_sq θ
  linarith [hKF, hup, hca]

/-- **The tail content of the sketch's dominant frame controls the error**, deterministic: for
$\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, s\mathbf{I}_k)$ with $0 \le s \le 1$, any
$\mathbf{\Omega} = [\mathbf{\Omega}_1; \mathbf{\Omega}_2] \in \mathbb{R}^{2k \times \ell}$ with
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \ge k$, $\mathbf{P}$ the range projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$, $T = \operatorname{tr}\mathbf{P}_{22}$ its tail
content, and any $\theta$: the error is at least $ks^2 + (1 - s^2)T$, and
$$\begin{aligned}
&T\bigl(s^2\|\mathbf{\Omega}_2\|_2^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2\bigr) +
2s\,\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{kT} \\
&\quad\ge 2s\sin\theta\cos\theta\,\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_* -
\sin^2\theta\,\bigl(\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 -
s^2\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2\bigr)\,.
\end{aligned}$$
No printed source. New (research note OP1, §4 steps 1–3).
Proof: M, about 90 lines (split the two conjuncts). Write
$\mathbf{P} = \mathbf{U}\mathbf{U}^{\mathsf{T}}$
with $\mathbf{U} = [\mathbf{U}_h; \mathbf{U}_t]$ an orthonormal $k$-frame
(`rangeProjector_truncatedSVD_mul`, rank exactly $k$), so $T = \|\mathbf{U}_t\|_{\mathsf{F}}^2$ and
$\|\mathbf{U}_h\|_{\mathsf{F}}^2 = k - T$. (1) Error:
$\|\mathbf{A}\|_{\mathsf{F}}^2 - \operatorname{tr}(\mathbf{P}\mathbf{A}^2) =
k + ks^2 - (k - T) - s^2T$.
(2) Upper bound on $f(\mathbf{U}) = \|\mathbf{U}^{\mathsf{T}}\mathbf{Y}\|_{\mathsf{F}}^2$,
$\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$, with
$\mathbf{W}_{ij} = \mathbf{\Omega}_i\mathbf{\Omega}_j^{\mathsf{T}}$:
$f(\mathbf{U}) \le \operatorname{tr}\mathbf{W}_{11} - \lambda_{\min}(\mathbf{W}_{11})T +
2s\|\mathbf{W}_{12}\|_2\sqrt{kT} + s^2\lambda_{\max}(\mathbf{W}_{22})T$ (Loewner
$\mathbf{I} - \mathbf{U}_h\mathbf{U}_h^{\mathsf{T}} \succeq \mathbf{0}$, Cauchy–Schwarz
`frobInner_le`-type bound, `specNorm` of a product). (3) Competitor
$\mathbf{V} = [\cos\theta\,\mathbf{I}; \sin\theta\,\mathbf{R}]$, $\mathbf{R}$ the orthogonal polar
factor with $\operatorname{tr}(\mathbf{W}_{12}\mathbf{R}) = \|\mathbf{W}_{12}\|_*$
(`exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm` at full rank, or the polar factor);
$f(\mathbf{U}) \ge f(\mathbf{V})$ is Ky Fan maximality of the truncated SVD (Eckart–Young on
$\mathbf{Y}$ via `rangeProjector_truncatedSVD_mul`). Subtract. $\lambda_{\max}(\mathbf{W}_{22}) =
\|\mathbf{\Omega}_2\|_2^2$,
$\lambda_{\min}(\mathbf{W}_{11}) = \sigma_{k-1}(\mathbf{\Omega}_1)^2$. -/
theorem frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational {k : ℕ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ}
    (hA : A = Matrix.fromBlocks 1 0 0 (s • 1)) {Ω' : Matrix (Fin k ⊕ Fin k) l ℝ}
    (hr : k ≤ (A * Ω').rank) (θ : ℝ) {T : ℝ}
    (hT : T = ∑ i : Fin k, rangeProjector (truncatedSVD (A * Ω') k) (Sum.inr i) (Sum.inr i)) :
    k * s ^ 2 + (1 - s ^ 2) * T ≤ frobNorm (A - earlyTruncatedRSVD A Ω' k) ^ 2 ∧
      2 * s * Real.sin θ * Real.cos θ * nuclearNorm (Ω'.toRows₁ * Ω'.toRows₂ᵀ) -
          Real.sin θ ^ 2 * (frobNorm Ω'.toRows₁ ^ 2 - s ^ 2 * frobNorm Ω'.toRows₂ ^ 2) ≤
        T * (s ^ 2 * specNorm Ω'.toRows₂ ^ 2 - singularValues Ω'.toRows₁ (k - 1) ^ 2) +
          2 * s * specNorm (Ω'.toRows₁ * Ω'.toRows₂ᵀ) * √(k * T) := by
  classical
  subst hA
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (s • 1)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, Matrix.diagonal]
  rw [hD] at hr hT ⊢
  obtain ⟨U, hU, hPU⟩ := exists_orthonormalCols_rangeProjector_truncatedSVD _ k hr
  have hPSD : (1 - U.toRows₁ * U.toRows₁ᴴ).PosSemidef := by
    have hQ : IsStarProjection (1 - U * Uᴴ) := by
      rw [← hPU]
      exact isStarProjection_one_sub_rangeProjector _
    have e : (1 - U * Uᴴ).submatrix Sum.inl Sum.inl = 1 - U.toRows₁ * U.toRows₁ᴴ := by
      ext i j
      simp [Matrix.mul_apply, Matrix.toRows₁, Matrix.one_apply]
    rw [← e]
    exact hQ.posSemidef.submatrix Sum.inl
  have hTU : T = (U.toRows₂ * U.toRows₂ᴴ).trace := by
    rw [hT, hPU]
    rfl
  constructor
  · rw [earlyTruncatedRSVD, hPU]
    exact k_mul_sq_add_le_frobNorm_sub_diagonal hU hTU
  · simp only [← Matrix.conjTranspose_eq_transpose_of_trivial]
    obtain ⟨R, hR, hcross⟩ := exists_orthogonal_frobInner_eq_nuclearNorm Ω'.toRows₁ Ω'.toRows₂
    have hKF := frobNorm_conjTranspose_mul_le_rangeProjector_truncatedSVD
      (Matrix.diagonal (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s)) * Ω') k
      (hasOrthonormalCols_fromRows_cos_sin (θ := θ) hR)
    rw [hPU, Matrix.mul_assoc U, hU.frobNorm_mul_left] at hKF
    exact conjunct_two_of_frame hs0 Ω' hU hPSD hTU hR hcross hKF

/-- The arithmetic of the block instance: the concentration bounds and the variational inequality
at $\theta = \arctan(1/40)$ force the tail content $T \ge 10^{-7}k$ (with $v = \sqrt{k}$,
$u = \sqrt{\ell}$). -/
private theorem le_of_variational_arith {u v s T sx py b a F fx fy : ℝ} (hu : 0 < u)
    (hv : 0 < v) (hvu : 100 * v ≤ u) (hs : s = 1 - v / (4 * u)) (hT : 0 ≤ T) (hpy0 : 0 ≤ py)
    (hpy : py < u + 5 / 4 * v) (hsx : u - 5 / 4 * v < sx)
    (hfx : fx ≤ v ^ 2 * (u + 5 / 4 * v) ^ 2) (hfy : v ^ 2 * (u - 5 / 4 * v) ^ 2 ≤ fy)
    (hF : 1 / 2 * (v ^ 2 * fy) < F) (hb0 : 0 ≤ b) (hb : b < 3 * v * py) (hab : F ≤ a * b)
    (hE7 : 2 * s * (40 / 1601) * a - 1 / 1601 * (fx - s ^ 2 * fy) ≤
      T * (s ^ 2 * py ^ 2 - sx ^ 2) + 2 * s * b * √(v ^ 2 * T)) :
    1 / 10 ^ 7 * v ^ 2 ≤ T := by
  have huv : 0 < u * v := mul_pos hu hv
  set q := v / (4 * u) with hqdef
  have hq : q ≤ 1 / 400 := by
    rw [hqdef, div_le_iff₀ (by positivity)]; linarith
  have hq0 : 0 ≤ q := by positivity
  have hs0 : 399 / 400 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hd : 0 ≤ u - 5 / 4 * v := by linarith
  have hsx2 : (u - 5 / 4 * v) ^ 2 ≤ sx ^ 2 := pow_le_pow_left₀ hd hsx.le 2
  have hpy2 : py ^ 2 ≤ (u + 5 / 4 * v) ^ 2 := pow_le_pow_left₀ hpy0 hpy.le 2
  have hvv : v * v ≤ v * (u / 100) := mul_le_mul_of_nonneg_left (by linarith) hv.le
  have huv' : u * v ≤ u * (u / 100) := mul_le_mul_of_nonneg_left (by linarith) hu.le
  have hd2 : 39 / 40 * u ^ 2 ≤ (u - 5 / 4 * v) ^ 2 := by
    have : (u - 5 / 4 * v) ^ 2 = u ^ 2 - 5 / 2 * (u * v) + 25 / 16 * v ^ 2 := by ring
    linarith [sq_nonneg v]
  have hv4u2 : 0 < v ^ 4 * u ^ 2 := by positivity
  have hFlow : 39 / 80 * (v ^ 4 * u ^ 2) < F := by
    have e1 := mul_le_mul_of_nonneg_left hfy (sq_nonneg v)
    have e2 := mul_le_mul_of_nonneg_left hd2 (by positivity : 0 ≤ v ^ 2 * v ^ 2)
    linarith
  have hbup : b < 3.0375 * (u * v) := by
    have := mul_lt_mul_of_pos_left hpy (by positivity : 0 < 3 * v)
    linarith
  have ha0 : 0 < a := by
    by_contra h
    push Not at h
    linarith [mul_nonpos_of_nonpos_of_nonneg h hb0]
  have halow : 39 / 80 * (v ^ 4 * u ^ 2) < a * (3.0375 * (u * v)) := by
    have := mul_le_mul_of_nonneg_left hbup.le ha0.le
    linarith
  have halow' : 0.16 * (v ^ 3 * u) ≤ a := by
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 3.0375 * (u * v))
    have : 0.16 * (v ^ 3 * u) * (3.0375 * (u * v)) = 0.486 * (v ^ 4 * u ^ 2) := by ring
    linarith
  have hss : 1 - 2 * q ≤ s ^ 2 := by
    have : s ^ 2 = 1 - 2 * q + q ^ 2 := by rw [hs]; ring
    linarith [sq_nonneg q]
  have hD : fx - s ^ 2 * fy ≤ 5.5 * (v ^ 3 * u) := by
    have h1 : s ^ 2 * (v ^ 2 * (u - 5 / 4 * v) ^ 2) ≤ s ^ 2 * fy :=
      mul_le_mul_of_nonneg_left hfy (sq_nonneg s)
    have h2 : (1 - 2 * q) * (u - 5 / 4 * v) ^ 2 ≤ s ^ 2 * (u - 5 / 4 * v) ^ 2 :=
      mul_le_mul_of_nonneg_right hss (sq_nonneg _)
    have h3 : q * (u - 5 / 4 * v) ^ 2 ≤ q * u ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd (by linarith) 2) hq0
    have h4 : q * u ^ 2 = u * v / 4 := by rw [hqdef]; field_simp
    have h5 := mul_le_mul_of_nonneg_left h2 (sq_nonneg v)
    have h6 := mul_le_mul_of_nonneg_left h3 (sq_nonneg v)
    rw [h4] at h6
    have h7 : v ^ 2 * (u + 5 / 4 * v) ^ 2 - v ^ 2 * (u - 5 / 4 * v) ^ 2 = 5 * (v ^ 3 * u) := by
      ring
    have h8 : v ^ 2 * (u * v / 4) = v ^ 3 * u / 4 := by ring
    linarith
  set w := √(v ^ 2 * T) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = v ^ 2 * T := Real.sq_sqrt (by positivity)
  have hL1 : T * (s ^ 2 * py ^ 2 - sx ^ 2) ≤ T * (5 * (u * v)) := by
    apply mul_le_mul_of_nonneg_left _ hT
    have h1 : s ^ 2 * py ^ 2 ≤ py ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg py) (pow_le_one₀ (by linarith) hs1)
    have h2 : (u + 5 / 4 * v) ^ 2 - (u - 5 / 4 * v) ^ 2 = 5 * (u * v) := by ring
    linarith
  have hL2 : 2 * s * b * w ≤ 2 * (3.0375 * (u * v)) * w := by
    have h1 : s * b ≤ b := mul_le_of_le_one_left hb0 hs1
    exact mul_le_mul_of_nonneg_right (by linarith) hw0
  have hR : 0.0045 * (v ^ 3 * u) ≤ 2 * s * (40 / 1601) * a - 1 / 1601 * (fx - s ^ 2 * fy) := by
    have := mul_le_mul hs0 halow' (by positivity) (by linarith)
    have e : 2 * s * (40 / 1601) * a = 80 / 1601 * (s * a) := by ring
    rw [e]
    norm_num at this hD ⊢
    linarith [(by positivity : 0 ≤ v ^ 3 * u)]
  have hkey : 0.0045 * v ^ 2 ≤ 5 * T + 6.075 * w := by
    refine le_of_mul_le_mul_left ?_ huv
    have : (u * v) * (0.0045 * v ^ 2) = 0.0045 * (v ^ 3 * u) := by ring
    linarith
  by_contra hcon
  push Not at hcon
  have hw' : w < 0.000317 * v ^ 2 := by
    by_contra h
    push Not at h
    have := mul_le_mul h h (by positivity) hw0
    have h2 : 0.000317 * v ^ 2 * (0.000317 * v ^ 2) = 0.000317 ^ 2 * (v ^ 2 * v ^ 2) := by ring
    have h3 := mul_lt_mul_of_pos_left hcon (by positivity : 0 < v ^ 2)
    nlinarith
  linarith

/-- The two row blocks of a standard Gaussian matrix are independent standard Gaussians. -/
private theorem hasLaw_toRows_indepFun {k : ℕ} {X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ) :
    HasLaw (fun ω => (X ω).toRows₁) (gaussianMatrix (Fin k) l) μ ∧
      HasLaw (fun ω => (X ω).toRows₂) (gaussianMatrix (Fin k) l) μ ∧
      IndepFun (fun ω => (X ω).toRows₁) (fun ω => (X ω).toRows₂) μ := by
  classical
  have h1 : HasOrthonormalCols (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) :=
    hasOrthonormalCols_selectionMatrix Sum.inl_injective
  have h2 : HasOrthonormalCols (selectionMatrix Sum.inr : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) :=
    hasOrthonormalCols_selectionMatrix Sum.inr_injective
  have h12 : (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ *
      (selectionMatrix Sum.inr : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) = 0 := by
    rw [conjTranspose_selectionMatrix_mul]
    ext i j
    rw [Matrix.submatrix_apply, selectionMatrix_apply]
    simp
  have e1 : (fun ω => (X ω).toRows₁) =
      fun ω => (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ * X ω := by
    funext ω; rw [conjTranspose_selectionMatrix_mul]; rfl
  have e2 : (fun ω => (X ω).toRows₂) =
      fun ω => (selectionMatrix Sum.inr : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ * X ω := by
    funext ω; rw [conjTranspose_selectionMatrix_mul]; rfl
  rw [e1, e2]
  exact ⟨hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX h1,
    hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX h2,
    indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX h1 h2 h12⟩

/-- The extreme singular value tails of a $k \times \ell$ Gaussian at deviation
$\sqrt{k}/4$. -/
private theorem gaussian_tails {k : ℕ} (hk : 1 ≤ k) {Y : Ω → Matrix (Fin k) l ℝ}
    (hY : HasLaw Y (gaussianMatrix (Fin k) l) μ) :
    μ.real {ω | √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ≤ specNorm (Y ω)} ≤
        Real.exp (-(k : ℝ) / 32) ∧
      μ.real {ω | singularValues (Y ω)ᴴ (k - 1) ≤
        √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ)} ≤ Real.exp (-(k : ℝ) / 32) := by
  have := hY.isProbabilityMeasure
  have ht : (0 : ℝ) ≤ √(k : ℝ) / 4 := by positivity
  have hsq : -(√(k : ℝ) / 4) ^ 2 / 2 = -(k : ℝ) / 32 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  constructor
  · have h := measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix hY ht
    rw [hsq, Fintype.card_fin] at h
    refine (measureReal_mono fun ω hω => ?_).trans h
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  · have h := measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix
      (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hY) (k := k - 1)
      (by rw [Fintype.card_fin]; omega) ht
    rw [hsq, Fintype.card_fin] at h
    refine (measureReal_mono fun ω hω => ?_).trans h
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith


/-- The section bound for the cross term at a fixed $\mathbf{y}$ of full row rank:
Paley–Zygmund for $\|\mathbf{\Omega}_1\mathbf{y}^{\mathsf{T}}\|_{\mathsf{F}}^2$ and the Chevet
tail. -/
private theorem measureReal_section_le {k : ℕ} (hk : 1 ≤ k) {Y : Ω → Matrix (Fin k) l ℝ}
    (hY : HasLaw Y (gaussianMatrix (Fin k) l) μ) (hYm : Measurable Y) {y : Matrix (Fin k) l ℝ}
    (hy : 0 < singularValues yᴴ (k - 1)) :
    μ.real {ω |
      ¬ (1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm yᵀ ^ 2) <
        frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) ^ 2) ∨
      ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} ≤
      11 / 12 + Real.exp (-(k : ℝ) / 2) := by
  have := hY.isProbabilityMeasure
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hTy : yᵀ = yᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial y).symm
  have hsp : 0 < specNorm yᵀ := hTy ▸ hy.trans_le (singularValues_le_specNorm _ _)
  have hfr : 0 < frobNorm yᵀ := hsp.trans_le (specNorm_le_frobNorm _)
  set m := frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm yᵀ ^ 2 with hm
  have hm0 : 0 < m := by
    rw [hm, frobNorm_one_sq, Fintype.card_fin]
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  set Z : Ω → ℝ := fun ω => frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) ^ 2 with hZ
  have hZm : Measurable Z :=
    (measurable_frobNorm.comp ((measurable_const.matrix_mul hYm).matrix_mul
      measurable_const)).pow_const 2
  have hZ1 : ∫ ω, Z ω ∂μ = m := integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix hY _ _
  have hZ4 : ∫ ω, Z ω ^ 2 ∂μ ≤ 3 * m ^ 2 := by
    have h := integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix hY
      (1 : Matrix (Fin k) (Fin k) ℝ) yᵀ
    simpa only [hZ, ← pow_mul] using h
  have hZ2 : MemLp Z 2 μ := by
    rw [memLp_two_iff_integrable_sq hZm.aestronglyMeasurable]
    simpa only [hZ, ← pow_mul] using
      integrable_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix hY
        (1 : Matrix (Fin k) (Fin k) ℝ) yᵀ
  have hPZ := sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt
    (ae_of_all _ fun ω => sq_nonneg _) hZ2 (θ := 1 / 2) (by norm_num) (by norm_num)
  rw [hZ1] at hPZ
  set p := μ.real {ω | 1 / 2 * m < Z ω} with hp
  have hp1 : 1 / 12 ≤ p := by
    have hp0 : 0 ≤ p := measureReal_nonneg
    have h3 : (∫ ω, Z ω ^ 2 ∂μ) * p ≤ 3 * m ^ 2 * p := mul_le_mul_of_nonneg_right hZ4 hp0
    have hm2 : 0 < m ^ 2 := by positivity
    nlinarith
  have hA : μ.real {ω | ¬ (1 / 2 * m < Z ω)} ≤ 11 / 12 := by
    have hmeas : MeasurableSet {ω | 1 / 2 * m < Z ω} := measurableSet_lt measurable_const hZm
    have := probReal_compl_eq_one_sub (μ := μ) hmeas
    rw [Set.compl_ofPred] at this
    linarith
  have hB : μ.real {ω | ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} ≤
      Real.exp (-(k : ℝ) / 2) := by
    have h := measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix hY
      (1 : Matrix (Fin k) (Fin k) ℝ) yᵀ (t := √(k : ℝ) * specNorm yᵀ) (by positivity)
    have e : -(√(k : ℝ) * specNorm yᵀ) ^ 2 /
        (2 * (specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ) ^ 2) = -(k : ℝ) / 2 := by
      rw [specNorm_one, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      field_simp
    rw [e] at h
    refine (measureReal_mono fun ω hω => ?_).trans h
    simp only [Set.mem_ofPred_eq, not_lt] at hω ⊢
    exact hω
  have hU : {ω | ¬ (1 / 2 * m < Z ω) ∨ ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} =
      {ω | ¬ (1 / 2 * m < Z ω)} ∪ {ω | ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} :=
    Set.ofPred_or
  rw [hU]
  exact (measureReal_union_le _ _).trans (add_le_add hA hB)


/-- The good event of the block instance has probability at least $1/24$. -/
private theorem le_measureReal_good_of_hasLaw_gaussianMatrix {k : ℕ} (hk : 4000 ≤ k)
    (hl : (10 ^ 4 : ℝ) * k ≤ Fintype.card l)
    {X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ)
    (hXm : Measurable X) :
    1 / 24 ≤ μ.real {ω |
      specNorm (X ω).toRows₁ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ∧
      √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues (X ω).toRows₁ᴴ (k - 1) ∧
      specNorm (X ω).toRows₂ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ∧
      √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues (X ω).toRows₂ᴴ (k - 1) ∧
      1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm (X ω).toRows₂ᵀ ^ 2) <
        frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * (X ω).toRows₁ * (X ω).toRows₂ᵀ) ^ 2 ∧
      specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * (X ω).toRows₁ * (X ω).toRows₂ᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm (X ω).toRows₂ᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm (X ω).toRows₂ᵀ +
          √(k : ℝ) * specNorm (X ω).toRows₂ᵀ} := by
  have := hX.isProbabilityMeasure
  obtain ⟨hY₁, hY₂, hind⟩ := hasLaw_toRows_indepFun hX
  have hk1 : 1 ≤ k := by omega
  have hK : (4000 : ℝ) ≤ k := by exact_mod_cast hk
  have hY₁m : Measurable fun ω => (X ω).toRows₁ :=
    Matrix.measurable_iff.2 fun i j => (Matrix.measurable_apply (Sum.inl i) j).comp hXm
  have hY₂m : Measurable fun ω => (X ω).toRows₂ :=
    Matrix.measurable_iff.2 fun i j => (Matrix.measurable_apply (Sum.inr i) j).comp hXm
  have hpos : 0 < √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) := by
    have h1 : √((10 ^ 4 : ℝ) * k) ≤ √(Fintype.card l : ℝ) := Real.sqrt_le_sqrt hl
    rw [Real.sqrt_mul (by norm_num), show √((10 ^ 4 : ℝ)) = 100 by
      rw [show (10 ^ 4 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h1
    have : 0 < √(k : ℝ) := Real.sqrt_pos.2 (by linarith)
    linarith
  obtain ⟨t1a, t1b⟩ := gaussian_tails hk1 hY₁
  obtain ⟨t2a, t2b⟩ := gaussian_tails hk1 hY₂
  have hH : Measurable fun M : Matrix (Fin k) l ℝ => singularValues Mᴴ (k - 1) :=
    ((continuous_singularValues _).comp continuous_id.matrix_conjTranspose).measurable
  set G₂ : Set (Matrix (Fin k) l ℝ) := {y | specNorm y < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ)
    ∧ √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues yᴴ (k - 1)} with hG₂
  have hG₂m : MeasurableSet G₂ :=
    (measurableSet_lt measurable_specNorm measurable_const).inter
      (measurableSet_lt measurable_const hH)
  set E : Set (Matrix (Fin k) l ℝ × Matrix (Fin k) l ℝ) := {p | p.2 ∉ G₂ ∨
      ¬ (1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm p.2ᵀ ^ 2) <
        frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * p.1 * p.2ᵀ) ^ 2) ∨
      ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * p.1 * p.2ᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm p.2ᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm p.2ᵀ + √(k : ℝ) * specNorm p.2ᵀ)}
    with hE
  have hEm : MeasurableSet E := by
    have hT : Measurable fun p : Matrix (Fin k) l ℝ × Matrix (Fin k) l ℝ => p.2ᵀ :=
      measurable_snd.matrix_transpose
    have hW : Measurable fun p : Matrix (Fin k) l ℝ × Matrix (Fin k) l ℝ =>
        (1 : Matrix (Fin k) (Fin k) ℝ) * p.1 * p.2ᵀ :=
      (measurable_const.matrix_mul measurable_fst).matrix_mul hT
    refine (hG₂m.preimage measurable_snd).compl.union
      ((measurableSet_lt ?_ ((measurable_frobNorm.comp hW).pow_const 2)).compl.union
      (measurableSet_lt (measurable_specNorm.comp hW) ?_).compl)
    · exact (((measurable_frobNorm.comp hT).pow_const 2).const_mul _).const_mul _
    · exact (((measurable_frobNorm.comp hT).const_mul _).add
        ((measurable_specNorm.comp hT).const_mul _)).add
        ((measurable_specNorm.comp hT).const_mul _)
  have hC := hind.measureReal_mem_le_add hY₁m.aemeasurable hY₂m.aemeasurable hEm hG₂m
    (δ₁ := 11 / 12 + Real.exp (-(k : ℝ) / 2)) (δ₂ := Real.exp (-(k : ℝ) / 32) +
      Real.exp (-(k : ℝ) / 32)) (by positivity)
    (fun y hy => by
      refine (measureReal_mono fun ω hω => ?_).trans
        (measureReal_section_le hk1 hY₁ hY₁m (hpos.trans hy.2))
      simp only [hE, Set.mem_ofPred_eq] at hω ⊢
      rcases hω with h | h
      · exact absurd hy h
      · exact h)
    (by
      refine (measureReal_mono fun ω hω => ?_).trans ((measureReal_union_le _ _).trans
        (add_le_add t2a t2b))
      simp only [hG₂, Set.mem_ofPred_eq, not_and_or, not_lt, Set.mem_union] at hω ⊢
      exact hω)
  have he : ∀ x : ℝ, 125 ≤ x → Real.exp (-x) ≤ 1 / 126 := fun x hx => by
    rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by norm_num)]
    linarith [Real.add_one_le_exp x]
  have he1 : Real.exp (-(k : ℝ) / 32) ≤ 1 / 126 := by
    rw [neg_div]; exact he _ (by linarith)
  have he2 : Real.exp (-(k : ℝ) / 2) ≤ 1 / 126 := by
    rw [neg_div]; exact he _ (by linarith)
  suffices h : ∀ S : Set Ω, Sᶜ ⊆
      {ω | √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ≤ specNorm (X ω).toRows₁} ∪
      {ω | singularValues (X ω).toRows₁ᴴ (k - 1) ≤ √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ)} ∪
      {ω | ((X ω).toRows₁, (X ω).toRows₂) ∈ E} → 1 / 24 ≤ μ.real S by
    refine h _ fun ω hω => ?_
    simp only [hE, hG₂, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    by_contra hc
    push Not at hc
    exact hω ⟨hc.1.1, hc.1.2, hc.2.1.1, hc.2.1.2, hc.2.2.1, hc.2.2.2⟩
  intro S hS
  have hu : 1 ≤ μ.real S + μ.real Sᶜ := by
    have := measureReal_union_le (μ := μ) S Sᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  have hc := (measureReal_mono hS).trans ((measureReal_union_le _ _).trans
    (add_le_add ((measureReal_union_le _ _).trans (add_le_add t1a t1b)) hC))
  linarith

/-- On the good event the error exceeds the optimum by $(1 - s^2)10^{-7}k$. -/
private theorem le_frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_of_good {k : ℕ}
    (hk : 4000 ≤ k) (hl : (10 ^ 4 : ℝ) * k ≤ Fintype.card l) {Ω' : Matrix (Fin k ⊕ Fin k) l ℝ}
    {A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ} {s : ℝ}
    (hs : s = 1 - √((k : ℝ) / Fintype.card l) / 4) (hA : A = Matrix.fromBlocks 1 0 0 (s • 1))
    (h1 : specNorm Ω'.toRows₁ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ))
    (h2 : √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues Ω'.toRows₁ᴴ (k - 1))
    (h3 : specNorm Ω'.toRows₂ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ))
    (h4 : √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues Ω'.toRows₂ᴴ (k - 1))
    (h5 : 1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm Ω'.toRows₂ᵀ ^ 2) <
        frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Ω'.toRows₁ * Ω'.toRows₂ᵀ) ^ 2)
    (h6 : specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Ω'.toRows₁ * Ω'.toRows₂ᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm Ω'.toRows₂ᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm Ω'.toRows₂ᵀ +
          √(k : ℝ) * specNorm Ω'.toRows₂ᵀ) :
    k * s ^ 2 + (1 - s ^ 2) * (1 / 10 ^ 7 * k) ≤ frobNorm (A - earlyTruncatedRSVD A Ω' k) ^ 2 := by
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  set u := √(Fintype.card l : ℝ) with hu
  set v := √(k : ℝ) with hv
  have hK : (4000 : ℝ) ≤ k := by exact_mod_cast hk
  have hv0 : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hv2 : v ^ 2 = k := Real.sq_sqrt (by linarith)
  have hvu : 100 * v ≤ u := by
    have h := Real.sqrt_le_sqrt hl
    rw [Real.sqrt_mul (by norm_num), show √((10 ^ 4 : ℝ)) = 100 by
      rw [show (10 ^ 4 : ℝ) = 100 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]] at h
    exact h
  have hu0 : 0 < u := by linarith
  have hs' : s = 1 - v / (4 * u) := by
    rw [hs, Real.sqrt_div' _ (Nat.cast_nonneg _), ← hu, ← hv]
    field_simp
  have hq : v / (4 * u) ≤ 1 / 400 := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hq0 : 0 ≤ v / (4 * u) := by positivity
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hd : 0 < u - 5 / 4 * v := by linarith
  -- rank
  have hr : k ≤ (A * Ω').rank := by
    have hpos := hd.trans h2
    rw [singularValues_pos_iff, Matrix.rank_conjTranspose] at hpos
    have e : (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ * (A * Ω') =
        Ω'.toRows₁ := by
      rw [conjTranspose_selectionMatrix_mul, hA]
      ext i j
      simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toRows₁]
    have := Matrix.rank_mul_le_right
      (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ (A * Ω')
    rw [e] at this
    omega
  set T := ∑ i : Fin k, rangeProjector (truncatedSVD (A * Ω') k) (Sum.inr i) (Sum.inr i) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ =>
    ((isStarProjection_rangeProjector (truncatedSVD (A * Ω') k)).posSemidef.diag_nonneg)
  obtain ⟨hE1, hE2⟩ := frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational hs0 hs1
    hA hr (Real.arctan (1 / 40)) hT
  have hsq : √(1 + (1 / 40 : ℝ) ^ 2) * √(1 + (1 / 40 : ℝ) ^ 2) = 1 + (1 / 40 : ℝ) ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  have hsc : Real.sin (Real.arctan (1 / 40)) * Real.cos (Real.arctan (1 / 40)) = 40 / 1601 := by
    rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, hsq]
    norm_num
  have hs2 : Real.sin (Real.arctan (1 / 40)) ^ 2 = 1 / 1601 := by
    rw [Real.sin_arctan, div_pow, sq (√_), hsq]
    norm_num
  set W := Ω'.toRows₁ * Ω'.toRows₂ᵀ with hW
  have hsx : u - 5 / 4 * v < singularValues Ω'.toRows₁ (k - 1) := by simpa using h2
  have hfx : frobNorm Ω'.toRows₁ ^ 2 ≤ v ^ 2 * (u + 5 / 4 * v) ^ 2 := by
    have h := frobNorm_sq_le_card_mul_specNorm_sq Ω'.toRows₁ᵀ
    rw [frobNorm_transpose, specNorm_transpose, Fintype.card_fin, ← hv2] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (specNorm_nonneg _) h1.le 2) (sq_nonneg v))
  have hfy : v ^ 2 * (u - 5 / 4 * v) ^ 2 ≤ frobNorm Ω'.toRows₂ ^ 2 := by
    have e := frobNorm_sq_eq_sum_singularValues_sq Ω'.toRows₂ᴴ
    rw [frobNorm_conjTranspose, Fintype.card_fin] at e
    have h := Finset.card_nsmul_le_sum (Finset.range k)
      (fun i => singularValues Ω'.toRows₂ᴴ i ^ 2) ((u - 5 / 4 * v) ^ 2) fun i hi =>
        pow_le_pow_left₀ hd.le ((h4.le).trans (singularValues_antitone _
          (by rw [Finset.mem_range] at hi; omega))) 2
    rw [Finset.card_range, nsmul_eq_mul, ← hv2] at h
    rw [e]
    exact h
  have hF : 1 / 2 * (v ^ 2 * frobNorm Ω'.toRows₂ ^ 2) < frobNorm W ^ 2 := by
    rw [frobNorm_one_sq, Fintype.card_fin, frobNorm_transpose, Matrix.one_mul, ← hv2] at h5
    exact h5
  have hf1 : frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) = v := by
    rw [← Real.sqrt_sq (frobNorm_nonneg _), frobNorm_one_sq, Fintype.card_fin]
  have hb : specNorm W < 3 * v * specNorm Ω'.toRows₂ := by
    rw [Matrix.one_mul, specNorm_one, one_mul, specNorm_transpose, hf1] at h6
    have h := frobNorm_le_sqrt_card_mul_specNorm Ω'.toRows₂ᵀ
    rw [Fintype.card_fin, specNorm_transpose] at h
    linarith
  have hab : frobNorm W ^ 2 ≤ nuclearNorm W * specNorm W := by
    have h := abs_frobInner_le_nuclearNorm_mul_specNorm W W
    rwa [frobInner_self, abs_of_nonneg (sq_nonneg _)] at h
  have hE7 : 2 * s * (40 / 1601) * nuclearNorm W - 1 / 1601 *
      (frobNorm Ω'.toRows₁ ^ 2 - s ^ 2 * frobNorm Ω'.toRows₂ ^ 2) ≤
      T * (s ^ 2 * specNorm Ω'.toRows₂ ^ 2 - singularValues Ω'.toRows₁ (k - 1) ^ 2) +
        2 * s * specNorm W * √(v ^ 2 * T) := by
    rw [← hsc, ← hs2, hv2]
    linarith [hE2]
  have hTk := le_of_variational_arith hu0 hv0 hvu hs' hT0 (specNorm_nonneg _) h3 hsx hfx hfy hF
    (specNorm_nonneg _) hb hab hE7
  rw [hv2] at hTk
  have h1s : 0 ≤ 1 - s ^ 2 := sub_nonneg.2 (pow_le_one₀ hs0 hs1)
  have := mul_le_mul_of_nonneg_left hTk h1s
  linarith only [this, hE1]

/-- **The early-truncated randomized SVD has excess $\Omega(\sqrt{k/\ell})$**: there are absolute
constants $c, C > 0$ and $K_0$ such that for every $k \ge K_0$, a standard Gaussian
$2k \times \ell$ test matrix $\mathbf{\Omega}$ with $\ell \ge Ck$, and
$\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, (1 - \delta)\mathbf{I}_k)$ with
$\delta = \sqrt{k/\ell}/4$,
$$\Bigl(1 + c\sqrt{k/\ell}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2\,.$$
So relative error $1 + \varepsilon$ needs $\ell \ge c^2k/\varepsilon^2$: the $k$-dependence of
the library's $900k/\varepsilon^2$ is also sharp. The constants are existential: the proof gives
$c \approx 10^{-4}$ with large $C$, $K_0$ (Chebyshev-level concentration); numerically
$c \approx 0.2$ for every $k \ge 1$ (research note OP1, §2(b)). $k \ge K_0$ is where the proof's
concentration events have probability at least $1/2$; for $2 \le k < K_0$ the statement is
expected but not proved (design note, OQ3).
No printed source. New (research note OP1, §4).
Proof: H, about 300 lines. On the event $G$ where (i)
$\|\mathbf{\Omega}_2\|_2 \le \sqrt{\ell} + \tfrac54\sqrt{k}$,
$\sigma_{k-1}(\mathbf{\Omega}_1) \ge \sqrt{\ell} - \tfrac54\sqrt{k}$
(`measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix`,
`measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix`), (ii)
$\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2 \le 2.2\sqrt{k\ell}$
(`measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix`), (iii)
$\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_{\mathsf{F}}^2 \ge 0.9k^2\ell$ (Chebyshev
conditionally on $\mathbf{\Omega}_2$, `ProbabilityTheory.IndepFun.measureReal_mem_le_add`: for fixed
$\mathbf{\Omega}_2$ satisfying (i) and (iv), the conditional
mean is $k\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2$
(`integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix`) and the conditional variance
$2k\|\mathbf{\Omega}_2\mathbf{\Omega}_2^{\mathsf{T}}\|_{\mathsf{F}}^2 \le
2k\|\mathbf{\Omega}_2\|_2^2\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2$, from the exact
`integral_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix` with $\mathbf{A} = \mathbf{I}$,
$\mathbf{B} = \mathbf{\Omega}_2^{\mathsf{T}}$; failure $O(1/k^2)$; the bound
`integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix` is too weak for Chebyshev), so
$\|\cdot\|_* \ge \|\cdot\|_{\mathsf{F}}^2/\|\cdot\|_2 \ge 0.4k\sqrt{k\ell}$, (iv)
$\lvert\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - \|\mathbf{\Omega}_2\|_{\mathsf{F}}^2\rvert \le
0.01k\sqrt{k\ell}$ and
$\lvert\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2 - k\ell\rvert \le 0.01k\ell$ (Chebyshev on chi-square
sums, variance $2k\ell$ of $\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2$, so $2k^3\ell$ of
$k\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2$;
`integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector`), each failing with probability
$O(1/k)$ or $O(e^{-ck})$ for $\ell \ge Ck$, so $\mathbb{P}[G] \ge 1/2$ for $k \ge K_0$.
On $G$, `frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational` at $\theta = 1/4$ gives
$5T + 4.5\sqrt{kT} \ge 0.09k$, hence $T \ge 10^{-4}k$ (if $T < 10^{-4}k$ the left side is below
$0.046k$). The error is $\ge ks^2$ everywhere (first conjunct, $T \ge 0$) and
$\ge ks^2 + (1 - s^2)10^{-4}k$ on $G$; integrate, $1 - s^2 \ge \delta$, the optimum is $ks^2$
(`frobNorm_sub_truncatedSVD_sq`; singular values $1$ ($k$ times) and $s$). Take
$c = 10^{-4}/8$.
Result: early-truncated-rsvd-lower-bound -/
theorem
    exists_forall_le_integral_frobNorm_sub_earlyTruncatedRSVD_sq_of_hasLaw_gaussianMatrix :
    ∃ c C : ℝ, ∃ K₀ : ℕ, 0 < c ∧ 0 < C ∧ ∀ {Ω l : Type} [MeasurableSpace Ω] [Fintype l]
      (μ : Measure Ω) (k : ℕ) (X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ)
      (A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ),
      HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ → K₀ ≤ k → C * k ≤ Fintype.card l →
      A = Matrix.fromBlocks 1 0 0 ((1 - √((k : ℝ) / Fintype.card l) / 4) • 1) →
      (1 + c * √((k : ℝ) / Fintype.card l)) *
          frobNorm (A - truncatedSVD A k) ^ 2 ≤
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
  refine ⟨1 / (10 ^ 7 * 96), 10 ^ 4, 4000, by norm_num, by norm_num, ?_⟩
  intro Ω l _ _ μ k X₀ A hX₀ hk hl hA
  obtain ⟨X, hXm, hXX⟩ := hX₀.aemeasurable
  have hX : HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ := hX₀.congr hXX.symm
  rw [integral_congr_ae (g := fun ω => frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2)
    (hXX.mono fun ω h => by simp only [h])]
  clear hXX hX₀
  have hP := hX.isProbabilityMeasure
  set K : ℝ := (k : ℝ) with hKdef
  set L : ℝ := (Fintype.card l : ℝ) with hLdef
  set r := √(K / L) with hr
  set s := 1 - r / 4 with hs
  have hK : (4000 : ℝ) ≤ K := by rw [hKdef]; exact_mod_cast hk
  have hL0 : 0 < L := by linarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 / 100 := by
    rw [hr, Real.sqrt_le_left (by norm_num), div_le_iff₀ hL0]
    linarith
  set G := {ω | specNorm (X ω).toRows₁ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ∧
      √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues (X ω).toRows₁ᴴ (k - 1) ∧
      specNorm (X ω).toRows₂ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ∧
      √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues (X ω).toRows₂ᴴ (k - 1) ∧
      1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm (X ω).toRows₂ᵀ ^ 2) <
        frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * (X ω).toRows₁ * (X ω).toRows₂ᵀ) ^ 2 ∧
      specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * (X ω).toRows₁ * (X ω).toRows₂ᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm (X ω).toRows₂ᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm (X ω).toRows₂ᵀ +
          √(k : ℝ) * specNorm (X ω).toRows₂ᵀ} with hGdef
  have hG : 1 / 24 ≤ μ.real G := le_measureReal_good_of_hasLaw_gaussianMatrix hk hl hX hXm
  have hGm : MeasurableSet G := by
    have hR1 : Measurable fun ω => (X ω).toRows₁ :=
      Matrix.measurable_iff.2 fun i j => (Matrix.measurable_apply (Sum.inl i) j).comp hXm
    have hR2 : Measurable fun ω => (X ω).toRows₂ :=
      Matrix.measurable_iff.2 fun i j => (Matrix.measurable_apply (Sum.inr i) j).comp hXm
    have hH : Measurable fun M : Matrix (Fin k) l ℝ => singularValues Mᴴ (k - 1) :=
      ((continuous_singularValues _).comp continuous_id.matrix_conjTranspose).measurable
    have hR2T : Measurable fun ω => (X ω).toRows₂ᵀ := hR2.matrix_transpose
    have hW : Measurable fun ω =>
        (1 : Matrix (Fin k) (Fin k) ℝ) * (X ω).toRows₁ * (X ω).toRows₂ᵀ :=
      (measurable_const.matrix_mul hR1).matrix_mul hR2T
    have m5 : Measurable fun ω => 1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 *
        frobNorm (X ω).toRows₂ᵀ ^ 2) :=
      (((measurable_frobNorm.comp hR2T).pow_const 2).const_mul _).const_mul _
    have m6 : Measurable fun ω => specNorm (1 : Matrix (Fin k) (Fin k) ℝ) *
        frobNorm (X ω).toRows₂ᵀ + frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) *
        specNorm (X ω).toRows₂ᵀ + √(k : ℝ) * specNorm (X ω).toRows₂ᵀ :=
      (((measurable_frobNorm.comp hR2T).const_mul _).add
        ((measurable_specNorm.comp hR2T).const_mul _)).add
        ((measurable_specNorm.comp hR2T).const_mul _)
    exact (measurableSet_lt (measurable_specNorm.comp hR1) measurable_const).inter
      ((measurableSet_lt measurable_const (hH.comp hR1)).inter
      ((measurableSet_lt (measurable_specNorm.comp hR2) measurable_const).inter
      ((measurableSet_lt measurable_const (hH.comp hR2)).inter
      ((measurableSet_lt m5 ((measurable_frobNorm.comp hW).pow_const 2)).inter
      (measurableSet_lt (measurable_specNorm.comp hW) m6)))))
  set O := frobNorm (A - truncatedSVD A k) ^ 2 with hO
  set β := (1 - s ^ 2) * (1 / 10 ^ 7 * K) with hβ
  have hopt : O ≤ K * s ^ 2 := by
    set V : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ := selectionMatrix Sum.inl with hV
    have hB : (V * Vᴴ).rank ≤ k :=
      (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width V).trans (by simp))
    have hVV : V * Vᴴ = Matrix.fromBlocks 1 0 0 0 := by
      ext i j
      rw [Matrix.mul_apply]
      simp only [hV, selectionMatrix_apply, Matrix.conjTranspose_apply, star_trivial]
      rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, eq_comm]
    have hAB : A - V * Vᴴ = Matrix.fromBlocks 0 0 0 (s • 1) := by
      rw [hA, hVV]
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp
    have hF : frobNorm (A - V * Vᴴ) ^ 2 = K * s ^ 2 := by
      have hD : (Matrix.fromBlocks 0 0 0 (s • 1) : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ) =
          Matrix.diagonal (Sum.elim (fun _ : Fin k => (0 : ℝ)) (fun _ : Fin k => s)) := by
        ext i j
        rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, Matrix.diagonal]
      rw [hAB, hD, frobNorm_diagonal_sq]
      simp [Fintype.sum_sum_type, Real.norm_eq_abs, sq_abs, hKdef]
    rw [hO, ← hF]
    exact pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_sub_truncatedSVD_le_of_rank_le A hB) 2
  have hlow : ∀ ω, O ≤ frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 := fun ω =>
    pow_le_pow_left₀ (frobNorm_nonneg _)
      (frobNorm_sub_truncatedSVD_le_of_rank_le A (rank_earlyTruncatedRSVD_le A (X ω) k)) 2
  have hgood : ∀ ω ∈ G, K * s ^ 2 + β ≤ frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 :=
    fun ω hω => le_frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_of_good hk hl hs hA hω.1
      hω.2.1 hω.2.2.1 hω.2.2.2.1 hω.2.2.2.2.1 hω.2.2.2.2.2
  have hβ0 : 0 ≤ β := by
    have : s ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have : 0 ≤ 1 - s ^ 2 := by linarith
    positivity
  have hint := integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX.aemeasurable k
  have hmono : ∫ ω, (O + G.indicator (fun _ => β) ω) ∂μ ≤
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
    refine integral_mono ((integrable_const _).add ((integrable_const β).indicator hGm)) hint
      fun ω => ?_
    by_cases hω : ω ∈ G
    · simp only [Set.indicator_of_mem hω]
      linarith [hgood ω hω]
    · simp only [Set.indicator_of_notMem hω, add_zero]
      exact hlow ω
  rw [integral_add (integrable_const _) ((integrable_const β).indicator hGm), integral_const,
    integral_indicator_const _ hGm, probReal_univ, one_smul, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  have h1s : r / 4 ≤ 1 - s ^ 2 := by
    rw [hs]; nlinarith
  have hO0 : 0 ≤ O := sq_nonneg _
  have hOK : O ≤ K := by nlinarith
  have hb : 1 / 24 * (r / 4 * (1 / 10 ^ 7 * K)) ≤ μ.real G * β := by
    rw [hβ]
    exact mul_le_mul hG (mul_le_mul_of_nonneg_right h1s (by positivity)) (by positivity)
      measureReal_nonneg
  have : 1 / (10 ^ 7 * 96) * r * O ≤ 1 / (10 ^ 7 * 96) * r * K :=
    mul_le_mul_of_nonneg_left hOK (by positivity)
  nlinarith

end NLAlib
