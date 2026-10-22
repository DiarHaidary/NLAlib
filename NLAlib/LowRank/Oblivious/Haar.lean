/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.EarlyTruncation
public import NLAlib.Sketching.Gaussian.HaarEmbedding

/-!
# Early truncation with a Haar test matrix, through injection and approximate multiplication

The Haar instance of `NLAlib.LowRank.Oblivious.EarlyTruncation`, for the family of
`NLAlib.Sketching.Gaussian.Haar`: for an $n \times \ell$ Haar frame $\mathbf{\Omega}$,
$\ell \le \lvert n\rvert$, the early-truncated randomized SVD
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ reaches error
$(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with
probability $1 - \delta$ at $\ell = O(k\log(1/\delta)/\varepsilon^2)$. The family's predicates are
about the normalised sketch $\sqrt{\lvert n\rvert/\ell}\,\mathbf{\Omega}^{\mathsf{H}}$: its OSI at
constant $1 - \varepsilon/6$ by JL and a net
(`NLAlib.isObliviousSubspaceInjection_of_hasLaw_haarFrame_of_jlDim_le`) and its JL moment at
$p = \max(2, \log(3/\delta))$ (`NLAlib.hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le`) for
the two multiplication tails; the conclusion is about the output the user computes from the raw
frame. Real throughout.

The Haar randomized SVD to relative error by this route is dominated by Tropp and Webber's bound
through the range transfer (`NLAlib.LowRank.Gaussian.RangeFinderTailHaar`) and is not stated.
Design: `docs/design/LowRank-S7.md` §3.5, D3; `docs/design/Sketching-Moments.md` §4.3.

## Main results

* `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`: the explicit
  tail, and its asymptotic form
  `exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq l] {Q : Ω → Matrix n l ℝ}

/-- **Early-truncated randomized SVD with a Haar test matrix, tail**: for an $n \times \ell$ Haar
frame $\mathbf{\Omega}$, $\ell \le \lvert n\rvert$, $0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value jlDim (2\varepsilon/15) (\delta/3/21^k) -->
$\ell \ge \log(2/(\delta/3/21^k))/((2\varepsilon/15)^2/4 - (2\varepsilon/15)^3/6)$ and at
least <!-- value jlMomentDim (\varepsilon/(6\sqrt{k})) (\delta/3) -->
$\ell \ge 128\max(2, \log(1/(\delta/3)))/(\varepsilon/(6\sqrt{k}))^2$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the sizes are `jlDim (2 * ε / 15) (δ / 3 / 21 ^ k)` (the OSI at
constant $1 - \varepsilon/6$ and failure $\delta/3$) and `jlMomentDim (ε / (6 * √k)) (δ / 3)`
(the JL moment for each multiplication tail, failure $\delta/3$). The route of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`, through
`NLAlib.HasJLMoment.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le`.
Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for dense random sign matrices,
with unspecified constants; the Haar instance is not stated there.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame
    (A : Matrix m n ℝ) (hQ : HasLaw Q (haarFrame n l) μ) (hl : Fintype.card l ≤ Fintype.card n)
    {k : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hl₁ : jlDim (2 * ε / 15) (δ / 3 / 21 ^ k) ≤ Fintype.card l)
    (hl₂ : jlMomentDim (ε / (6 * √(k : ℝ))) (δ / 3) ≤ Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (Q ω) k) ^ 2} ≤ δ := by
  classical
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (Q ω) 0) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul] at hω'
    nlinarith [sq_nonneg (frobNorm A)]
  have hk1 : (1 : ℝ) ≤ √(k : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hk)
  have hεJ : 0 < ε / (6 * √(k : ℝ)) := by positivity
  have hεJ1 : ε / (6 * √(k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hl0 : (0 : ℝ) < Fintype.card l := by
    refine lt_of_lt_of_le ?_ hl₂
    rw [jlMomentDim_def]
    have : (0 : ℝ) < max 2 (Real.log (1 / (δ / 3))) := lt_max_of_lt_left two_pos
    positivity
  have : Nonempty l := Fintype.card_pos_iff.1 (by exact_mod_cast hl0)
  have hS : (fun ω => √(Fintype.card n / Fintype.card l : ℝ) • (Q ω)ᴴ) =
      fun ω => (√(Fintype.card n / Fintype.card l : ℝ) • Q ω)ᴴ := by
    funext ω
    rw [Matrix.conjTranspose_smul, star_trivial]
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_haarFrame_of_jlDim_le (d := k) hQ hl
    (by positivity : 0 < ε / 6) (by linarith) (by positivity : 0 < δ / 3)
    (by rwa [show 4 * (ε / 6) / 5 = 2 * ε / 15 by ring])
  have hJL := hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le hQ hl hεJ hεJ1 (by positivity) hl₂
  rw [hS] at hOSI hJL
  exact (hJL.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    ((continuous_const_smul _).measurable.comp_aemeasurable hQ.aemeasurable)
    hε hε1 (le_max_left _ _) (by positivity)).trans (by linarith)

/-- **$O(k\log(1/\delta)/\varepsilon^2)$ Haar columns suffice for early truncation**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for an $n \times \ell$ Haar frame
$\mathbf{\Omega}$, $\ell \le \lvert n\rvert$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell \ge Ck\log(1/\delta)/\varepsilon^2$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$ ($k = 0$ is trivial). The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame`, proved from it
with $\varepsilon_0 = 1$; the injection size $O((k + \log(1/\delta))/\varepsilon^2)$ is dominated
by the multiplication size for $k \ge 1$. [CohenElderMuscoMuscoPersu2015, Theorem 12 and
Lemma 3].
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame
Result: etrsvd -/
theorem exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq l] (μ : Measure Ω) (A : Matrix m n ℝ) (Q : Ω → Matrix n l ℝ)
      (k : ℕ) (ε δ : ℝ),
      HasLaw Q (haarFrame n l) μ → Fintype.card l ≤ Fintype.card n →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((k : ℝ) * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (Q ω) k) ^ 2} ≤ δ := by
  refine ⟨41472, 1, by norm_num, one_pos, fun μ A Q k ε δ hQ hln hε hε1 hδ hδ2 hl => ?_⟩
  classical
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (Q ω) 0) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul] at hω'
    nlinarith [sq_nonneg (frobNorm A)]
  have h2 : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_gt_d9
  have hL : 0 ≤ Real.log (1 / δ) := by linarith
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h3 : Real.log (1 / (δ / 3)) ≤ 3 * Real.log (1 / δ) := by
    rw [show 1 / (δ / 3) = 3 * (1 / δ) by field_simp, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkL : Real.log (1 / δ) ≤ k * Real.log (1 / δ) := le_mul_of_one_le_left hL hk1
  have hkL2 : (k : ℝ) ≤ 2 * (k * Real.log (1 / δ)) := by nlinarith
  have h21 : (1 : ℝ) ≤ 21 ^ k := one_le_pow₀ (by norm_num)
  have hlj : Real.log (2 / (δ / 3 / 21 ^ k)) =
      Real.log 2 + Real.log 3 + k * Real.log 21 + Real.log (1 / δ) := by
    rw [show 2 / (δ / 3 / 21 ^ k) = 2 * 3 * 21 ^ k * (1 / δ) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hd21 : (k : ℝ) * Real.log 21 ≤ k * (61 / 20) :=
    mul_le_mul_of_nonneg_left Real.log_twentyOne_le_sixtyOne_div_twenty (Nat.cast_nonneg k)
  refine measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_haarFrame A hQ hln hε hε1
    hδ ?_ ?_
  · refine (jlDim_le (by linarith) (by positivity)
      ((div_le_self (by positivity) h21).trans (by linarith))).trans (le_trans ?_ hl)
    rw [hlj, show 12 * (Real.log 2 + Real.log 3 + k * Real.log 21 + Real.log (1 / δ)) /
        (2 * ε / 15) ^ 2 = 675 * (Real.log 2 + Real.log 3 + k * Real.log 21 + Real.log (1 / δ)) /
          ε ^ 2 by field_simp; ring, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg ε)
  · refine (jlMomentDim_le (by positivity) (by linarith)).trans (le_trans ?_ hl)
    generalize Real.log (1 / (δ / 3)) = t at h3 ⊢
    rw [show 384 * t / (ε / (6 * √(k : ℝ))) ^ 2 = 13824 * ((k : ℝ) * t) / ε ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]; field_simp; ring, mul_div_assoc']
    exact div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α := ℝ) k)]) (sq_nonneg ε)

end NLAlib
