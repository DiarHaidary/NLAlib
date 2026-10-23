/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.EarlyTruncation
public import NLAlib.Sketching.Gaussian.Gaussian

/-!
# Early truncation with a Gaussian test matrix, through injection and approximate multiplication

The Gaussian instance of `NLAlib.LowRank.Oblivious.EarlyTruncation`, for the family of
`NLAlib.Sketching.Gaussian.Gaussian`: for a standard Gaussian $n \times \ell$ test matrix
$\mathbf{\Omega}$, the early-truncated randomized SVD
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ reaches error
$(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with
probability $1 - \delta$ at $\ell = O((k/\delta + \log(1/\delta))/\varepsilon^2)$ through the
second JL moment, and at $\ell = O(k\log(1/\delta)/\varepsilon^2)$ through the JL moment at
$p = \log(1/\delta)$. The family's
predicates are about the normalised sketch $\ell^{-1/2}\mathbf{\Omega}^{\mathsf{H}}$ (the
transpose of a Gaussian matrix is Gaussian, `NLAlib.hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`);
the generic theorem runs there with the projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ computed at the raw test matrix, so the
conclusion is about the output the user computes. Real throughout.

**Statements with no per-family form.** The randomized SVD itself with a Gaussian test matrix has
the sharper tails of `NLAlib.LowRank.Gaussian.RangeFinderTail`. The generic Nyström, generalized
Nyström and truncation tails apply to the Gaussian sketch through its OSI and JL moment property,
for `hX : HasLaw X (gaussianMatrix n l) μ` and
`hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX`:
```
isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le hG hε hε2 hδ
  hδ1 hl
hasJLMoment_of_hasLaw_gaussianMatrix hG hε
```
both about `fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ`, which is
`fun ω => ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ` by `Matrix.conjTranspose_smul`; a statement about
`rsvd` at the rescaled test matrix is one about the raw one by `NLAlib.rsvd_smul_right` (the
library has no such identity for the other outputs yet, and early truncation needs none: the
projector form takes the projector of the raw output). Design: `docs/design/LowRank-S7.md` §3.5,
§8.

## Main results

* `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`: the
  explicit tail;
  `measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`,
  its $\log(1/\delta)$ twin, and the asymptotic form
  `exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

/-- **Early-truncated randomized SVD with a Gaussian test matrix, tail**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{\Omega}$, $0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value gaussianInjectionDim k (\varepsilon/6) (\delta/3) -->
$\ell \ge 4 (\sqrt{k} + \sqrt{2 \log(1/(\delta/3))})^2/(\varepsilon/6)^2$ and
$\ell \ge 216k/(\varepsilon^2\delta)$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the first size is `gaussianInjectionDim k (ε / 6) (δ / 3)`.
The route: the OSI at constant $1 - \varepsilon/6$ and failure $\delta/3$, the JL moment property
at $\varepsilon/(6\sqrt{k})$ for the two multiplication tails, and
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le`. Its expectation
twin, at $\ell \ge 900k/\varepsilon^2$, is
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`; a
tail from that by Markov's inequality needs $\ell$ of order $k/(\varepsilon\delta)^2$.
Incomparable with its $\log(1/\delta)$ twin
`measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`
(rule 4): this one needs fewer columns at constant $\delta$, the twin for small $\delta$; the
asymptotic form
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix` is
proved from the twin.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for dense random sign matrices,
with unspecified constants.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hl : gaussianInjectionDim k (ε / 6) (δ / 3) ≤ Fintype.card l)
    (hl' : 216 * (k : ℝ) ≤ ε ^ 2 * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) 0) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul] at hω'
    nlinarith [sq_nonneg (frobNorm A)]
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX
  have hl0 : 0 < Fintype.card l := by
    exact_mod_cast (gaussianInjectionDim_pos k (by positivity : ε / 6 ≠ 0) (by positivity)
      (by linarith : δ / 3 < 1)).trans_le hl
  have : Nonempty l := Fintype.card_pos_iff.1 hl0
  have hS : (fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) =
      fun ω => ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ := by
    funext ω
    rw [Matrix.conjTranspose_smul, star_trivial]
  have hk0 : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  have hεJ : 0 < ε / (6 * √(k : ℝ)) := by positivity
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    (d := k) hG (by positivity) (by linarith) (by positivity) (by linarith) hl
  have hJL := hasJLMoment_of_hasLaw_gaussianMatrix hG hεJ
  rw [hS] at hOSI hJL
  refine (hJL.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    ((continuous_const_smul _).measurable.comp_aemeasurable hX.aemeasurable)
    hε hε1 le_rfl (by positivity)).trans ?_
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 hl0
  have e : 2 / (Fintype.card l * (ε / (6 * √(k : ℝ))) ^ 2) =
      72 * k / (Fintype.card l * ε ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    field_simp
    ring
  have h3 : 72 * (k : ℝ) / (Fintype.card l * ε ^ 2) ≤ δ / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [e]
  linarith

/-- **Early-truncated randomized SVD with a Gaussian test matrix, tail**, $\log(1/\delta)$ size
form: for a standard Gaussian $n \times \ell$ test matrix $\mathbf{\Omega}$,
$0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value gaussianInjectionDim k (\varepsilon/6) (\delta/3) -->
$\ell \ge 4 (\sqrt{k} + \sqrt{2 \log(1/(\delta/3))})^2/(\varepsilon/6)^2$ and at
least <!-- value jlMomentDim (\varepsilon/(6\sqrt{k})) (\delta/3) -->
$\ell \ge 128\max(2, \log(1/(\delta/3)))/(\varepsilon/(6\sqrt{k}))^2$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the sizes are `gaussianInjectionDim k (ε / 6) (δ / 3)` and
`jlMomentDim (ε / (6 * √k)) (δ / 3)`, the second $4608k\max(2, \log(3/\delta))/\varepsilon^2$.
The route of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`, with the
JL moment at $p = \max(2, \log(3/\delta))$
(`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`) in place of the second moment,
each multiplication tail failing with probability $\delta/3$; incomparable with it (rule 4).
Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for dense random sign matrices,
with unspecified constants.
Result: etrsvd -/
theorem
    measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hl : gaussianInjectionDim k (ε / 6) (δ / 3) ≤ Fintype.card l)
    (hl' : jlMomentDim (ε / (6 * √(k : ℝ))) (δ / 3) ≤ Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  classical
  have := hX.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) 0) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul] at hω'
    nlinarith [sq_nonneg (frobNorm A)]
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX
  have hl0 : 0 < Fintype.card l := by
    exact_mod_cast (gaussianInjectionDim_pos k (by positivity : ε / 6 ≠ 0) (by positivity)
      (by linarith : δ / 3 < 1)).trans_le hl
  have : Nonempty l := Fintype.card_pos_iff.1 hl0
  have hS : (fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) =
      fun ω => ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ := by
    funext ω
    rw [Matrix.conjTranspose_smul, star_trivial]
  have hk1 : (1 : ℝ) ≤ √(k : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hk)
  have hεJ : 0 < ε / (6 * √(k : ℝ)) := by positivity
  have hεJ1 : ε / (6 * √(k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    (d := k) hG (by positivity) (by linarith) (by positivity) (by linarith) hl
  have hJL := hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le hG hεJ hεJ1 (by positivity) hl'
  rw [hS] at hOSI hJL
  exact (hJL.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    ((continuous_const_smul _).measurable.comp_aemeasurable hX.aemeasurable)
    hε hε1 (le_max_left _ _) (by positivity)).trans (by linarith)

-- The explicit theorem's full name in the `Asymptotic:` tag exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(k\log(1/\delta)/\varepsilon^2)$ Gaussian columns suffice for early truncation**: there
are absolute constants $C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$
test matrix $\mathbf{\Omega}$, $0 < \varepsilon \le \varepsilon_0$, $0 < \delta \le 1/2$ and
$\ell \ge Ck\log(1/\delta)/\varepsilon^2$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$ ($k = 0$ is trivial). The asymptotic form of
`measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`,
proved from it with $\varepsilon_0 = 1$; the injection size
$O((k + \log(1/\delta))/\varepsilon^2)$ is dominated by the multiplication size for $k \ge 1$.
Asymptotic:
NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
Result: etrsvd -/
theorem
    exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε δ : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((k : ℝ) * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  refine ⟨41472, 1, by norm_num, one_pos, fun μ A X k ε δ hX hε hε1 hδ hδ2 hl => ?_⟩
  classical
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) 0) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul] at hω'
    nlinarith [sq_nonneg (frobNorm A)]
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hl2 := Real.log_two_gt_d9
  have hL : 0 ≤ Real.log (1 / δ) := by linarith
  have h3 : Real.log (1 / (δ / 3)) ≤ 3 * Real.log (1 / δ) := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
    rw [show 1 / (δ / 3) = 3 * (1 / δ) by field_simp, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkL : Real.log (1 / δ) ≤ k * Real.log (1 / δ) := le_mul_of_one_le_left hL hk1
  have hkL2 : (k : ℝ) ≤ 2 * (k * Real.log (1 / δ)) := by nlinarith
  refine
    measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
    A hX hε hε1 hδ ?_ ?_
  · refine (gaussianInjectionDim_le k _ (by positivity) (by linarith)).trans (le_trans ?_ hl)
    generalize Real.log (1 / (δ / 3)) = t at h3 ⊢
    rw [show 8 * ((k : ℝ) + 2 * t) / (ε / 6) ^ 2 = 288 * ((k : ℝ) + 2 * t) / ε ^ 2 by
      field_simp; ring, mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg ε)
  · refine (jlMomentDim_le (by positivity) (by linarith)).trans (le_trans ?_ hl)
    generalize Real.log (1 / (δ / 3)) = t at h3 ⊢
    rw [show 384 * t / (ε / (6 * √(k : ℝ))) ^ 2 = 13824 * ((k : ℝ) * t) / ε ^ 2 by
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]; field_simp; ring, mul_div_assoc']
    exact div_le_div_of_nonneg_right
      (by nlinarith [mul_le_mul_of_nonneg_left h3 (Nat.cast_nonneg (α := ℝ) k)]) (sq_nonneg ε)

end NLAlib
