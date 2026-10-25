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
  sorry

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
  sorry

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
  sorry

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
  sorry

end NLAlib
