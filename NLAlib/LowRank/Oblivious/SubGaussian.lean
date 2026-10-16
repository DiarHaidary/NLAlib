/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.EarlyTruncation
public import NLAlib.Sketching.Gaussian.SubGaussian

/-!
# The randomized SVD and early truncation with a sub-Gaussian test matrix

The sub-Gaussian instances of `NLAlib.LowRank.Oblivious.RangeFinder` and
`NLAlib.LowRank.Oblivious.EarlyTruncation`, for the family of
`NLAlib.Sketching.Gaussian.SubGaussian`: a random test matrix $\mathbf{\Omega} \in
\mathbb{R}^{n \times \ell}$ whose sketch $\mathbf{\Omega}^{\mathsf{H}}$ has independent, isotropic,
sub-Gaussian rows with proxy $c$ (the columns of $\mathbf{\Omega}$; hypotheses `hind`, `hsub`,
`hiso` on `fun ω => (X ω)ᴴ`, in that order). The randomized SVD
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ reaches error
$(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with probability
$1 - \delta$ at $\ell = O(c^2(k/(\varepsilon\delta) + \log(1/\delta)))$, and the early-truncated
randomized SVD $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ at
$\ell = O(c^2(k/\delta + \log(1/\delta))/\varepsilon^2)$. The family's predicates are about the
normalised sketch $\ell^{-1/2}\mathbf{\Omega}^{\mathsf{H}}$; the generic theorems run there and
`NLAlib.rsvd_smul_right` (respectively the projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ at the raw test matrix) returns to the output
the user computes. Isotropy forces $c \ge 1$ (`NLAlib.IsSubgaussianVector.one_le_of_isIsotropic`),
which covers the family's side condition $\varepsilon \le 2c$ at the accuracies used here. Real
throughout.

**Rademacher test matrices** are the case $c = 1$ (CONTRIBUTING's one statement per interface;
no Rademacher file): for `hX : HasLaw (fun ω => (X ω)ᴴ) (rademacherMatrix l n) μ` the three
hypotheses are
```
hX.iIndepFun_eval
fun i => isSubgaussianVector_of_hasLaw_rademacherVector (hX.eval i)
fun i => isIsotropic_of_hasLaw_rademacherVector (hX.eval i)
```
(`rademacherMatrix l n` is the product of `rademacherVector n` over the rows), and every statement
here applies at proxy $1$, with $16c^2 - 1 = 15$.

**Statements with no per-family form.** Nyström, generalized Nyström and the truncations apply
through the family's OSI and JL moment property:
```
isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le hind hsub hiso
  hε hεc hδ hl
hasJLMoment_of_isSubgaussianVector hind hsub hiso hε
```
both about `fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ`, which is
`fun ω => ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ` by `Matrix.conjTranspose_smul`. Design:
`docs/design/LowRank-S7.md` §3.5, §8.

## Main results

* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`: the randomized SVD,
  and its asymptotic form
  `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`.
* `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`: early
  truncation, and its asymptotic form
  `exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l ℝ}

omit [DecidableEq n] in
/-- With no columns every error is $\mathbf{0}$, so every error event against a factor
$1 + \varepsilon \ge 1$ is empty. -/
private theorem setOf_one_add_mul_frobNorm_sub_lt_eq_empty_of_isEmpty [IsEmpty n]
    (A B : Matrix m n ℝ) (C : Ω → Matrix m n ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    {ω | (1 + ε) * frobNorm (A - B) ^ 2 < frobNorm (A - C ω) ^ 2} = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun ω hω => ?_
  have hω' : (1 + ε) * frobNorm (A - B) ^ 2 < frobNorm (A - C ω) ^ 2 := hω
  rw [show A - C ω = A - B from Matrix.ext fun _ j => isEmptyElim j] at hω'
  nlinarith [sq_nonneg (frobNorm (A - B))]

omit [Fintype n] [DecidableEq n] in
/-- The normalised sketch of the family, as the sketch of the rescaled test matrix. -/
private theorem inv_sqrt_card_smul_conjTranspose (X : Ω → Matrix n l ℝ) :
    (fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) =
      fun ω => ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ := by
  funext ω
  rw [Matrix.conjTranspose_smul, star_trivial]

omit [DecidableEq n] in
/-- Sub-Gaussian rows of the sketch make the rescaled test matrix measurable. -/
private theorem aemeasurable_inv_sqrt_card_smul_of_isSubgaussianVector {c : ℝ≥0}
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ) :
    AEMeasurable (fun ω => (√(Fintype.card l : ℝ))⁻¹ • X ω) μ := by
  have h : AEMeasurable (fun ω => (X ω)ᴴ) μ :=
    aemeasurable_pi_lambda _ fun i => (hsub i).aemeasurable
  refine (((continuous_const_smul (√(Fintype.card l : ℝ))⁻¹).comp
    continuous_id.matrix_conjTranspose).measurable
    |>.comp_aemeasurable h).congr (ae_of_all _ fun ω => ?_)
  simp only [Function.comp_apply, id, Matrix.conjTranspose_conjTranspose]

/-- **The randomized SVD with a sub-Gaussian test matrix, relative error**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has independent, isotropic, sub-Gaussian rows with proxy $c$,
$\varepsilon, \delta > 0$, <!-- value subgaussianEmbeddingDim c k (1/2) (\delta/2) -->
$\ell \ge 4 c^2 (k \log 9 + \log(2/(\delta/2)))/(C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/64$, and
$\ell \ge 8(16c^2 - 1)k/(\varepsilon\delta)$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the first size is `subgaussianEmbeddingDim c k (1 / 2) (δ / 2)`
and $C$ is `subgaussianJLConstant`. The route: the OSI at constant $1/2$ and failure $\delta/2$,
the JL moment property at $\sqrt{\varepsilon/(4k)}$ and
`NLAlib.HasJLMoment.measure_frobNorm_sub_rsvd_sq_gt_le`. Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`.
[Woodruff2014, Lemma 45 and Remark 46]; there for dense sign and Gaussian sketches, constants
unspecified.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector [Nonempty l]
    (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hl : subgaussianEmbeddingDim c k (1 / 2) (δ / 2) ≤ Fintype.card l)
    (hl' : 8 * (16 * (c : ℝ) ^ 2 - 1) * k ≤ ε * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  classical
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [setOf_one_add_mul_frobNorm_sub_lt_eq_empty_of_isEmpty _ _ _ hε.le, measureReal_empty]
    exact hδ.le
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2 := hω
    rw [truncatedSVD_zero, sub_zero, sub_rsvd] at hω'
    have h := frobNorm_one_sub_rangeProjector_mul_le (A * X ω) A
    nlinarith [sq_nonneg (frobNorm A), frobNorm_nonneg ((1 - rangeProjector (A * X ω)) * A)]
  have hc1 : (1 : ℝ) ≤ c := (hsub (Classical.arbitrary l)).one_le_of_isIsotropic
    (hiso (Classical.arbitrary l))
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hεJ : 0 < √(ε / (4 * k)) := Real.sqrt_pos.2 (by positivity)
  have hOSI := isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (d := k) hind hsub hiso (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) (half_pos hδ) hl
  have hJL := hasJLMoment_of_isSubgaussianVector hind hsub hiso hεJ
  rw [inv_sqrt_card_smul_conjTranspose] at hOSI hJL
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 Fintype.card_pos
  have hδJ : (0 : ℝ) ≤ (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card l * √(ε / (4 * k)) ^ 2) := by
    have : (0 : ℝ) ≤ 16 * (c : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have h := hJL.measure_frobNorm_sub_rsvd_sq_gt_le (A := A) (hOSI.hasSubspaceInjection
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    (aemeasurable_inv_sqrt_card_smul_of_isSubgaussianVector hsub) (by norm_num) hεJ le_rfl hδJ
  have hsq : √(ε / (4 * k)) ^ 2 = ε / (4 * k) := Real.sq_sqrt (by positivity)
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans ?_)
  · have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 < frobNorm (A - rsvd A (X ω)) ^ 2 :=
      hω
    change _ < frobNorm (A - rsvd A ((√(Fintype.card l : ℝ))⁻¹ • X ω)) ^ 2
    rw [rsvd_smul_right _ _ (inv_ne_zero (Real.sqrt_pos.2 hL).ne'), hsq]
    refine lt_of_eq_of_lt ?_ hω'
    field_simp
    ring
  · rw [hsq]
    have e : (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card l * (ε / (4 * k))) =
        4 * (16 * (c : ℝ) ^ 2 - 1) * k / (Fintype.card l * ε) := by
      field_simp
    have h2 : 4 * (16 * (c : ℝ) ^ 2 - 1) * k / (Fintype.card l * ε) ≤ δ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [e]
    linarith

/-- **$O(c^2(k/(\varepsilon\delta) + \log(1/\delta)))$ sub-Gaussian columns suffice for the
randomized SVD**: there are absolute constants $C, \varepsilon_0 > 0$ such that if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ of an $n \times \ell$ test matrix $\mathbf{\Omega}$ has independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell \ge Cc^2(k/(\varepsilon\delta) + \log(1/\delta))$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the proxy stays in the threshold. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`, proved from it with
$C = 6912$ and $\varepsilon_0 = 1$.
Asymptotic: NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] [Nonempty l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (c : ℝ≥0) (k : ℕ) (ε δ : ℝ),
      iIndepFun (fun i ω => (X ω)ᴴ i) μ → (∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ) →
      (∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * ((k : ℝ) / (ε * δ) + Real.log (1 / δ))) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  refine ⟨6912, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ _ μ A X c k ε δ hind hsub hiso hε hε1 hδ hδ2 hl
  have hL1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hεδ : 0 < ε * δ := mul_pos hε hδ
  have hkεδ : (k : ℝ) ≤ k / (ε * δ) :=
    le_div_self (Nat.cast_nonneg k) hεδ (by nlinarith)
  have hc2 := sq_nonneg (c : ℝ)
  have hk : (k : ℝ) / (ε * δ) * (ε * δ) = k := div_mul_cancel₀ _ hεδ.ne'
  refine measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector A hind hsub hiso hε hδ
    ((subgaussianEmbeddingDim_le c k (1 / 2) (half_pos hδ) (by linarith)).trans ?_) ?_
  · have hlog : Real.log (2 / (δ / 2)) ≤ 3 * Real.log (1 / δ) := by
      rw [show (3 : ℝ) * Real.log (1 / δ) = Real.log ((1 / δ) ^ 3) by
        rw [Real.log_pow]; norm_num]
      refine Real.log_le_log (by positivity) ?_
      rw [div_pow, one_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hδ 2, pow_pos hδ 3]
    rw [show 576 * (c : ℝ) ^ 2 * (k + Real.log (2 / (δ / 2))) / (1 / 2) ^ 2 =
      2304 * ((c : ℝ) ^ 2 * (k + Real.log (2 / (δ / 2)))) by ring]
    refine le_trans ?_ hl
    nlinarith [mul_le_mul_of_nonneg_left hlog hc2, mul_le_mul_of_nonneg_left hkεδ hc2,
      mul_nonneg hc2 hL1]
  · nlinarith [mul_le_mul_of_nonneg_left hl hεδ.le, mul_nonneg hc2 hL1,
      mul_nonneg (mul_nonneg hc2 hL1) hεδ.le, mul_nonneg hc2 (Nat.cast_nonneg (α := ℝ) k)]

/-- **Early-truncated randomized SVD with a sub-Gaussian test matrix, tail**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has independent, isotropic, sub-Gaussian rows with proxy $c$,
$0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value subgaussianEmbeddingDim c k (\varepsilon/8) (\delta/3) -->
$\ell \ge 4 c^2 (k \log 9 + \log(2/(\delta/3)))/(C (\varepsilon/8)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/64$, and
$\ell \ge 192(16c^2 - 1)k/(\varepsilon^2\delta)$, then
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the first size is
`subgaussianEmbeddingDim c k (ε / 8) (δ / 3)` and $C$ is `subgaussianJLConstant`. The route of
the Gaussian statement
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`, with the
family's OSI and JL moment property. Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`.
[CohenElderMuscoMuscoPersu2015, §7.2]; there with unspecified constants.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector [Nonempty l]
    (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hl : subgaussianEmbeddingDim c k (ε / 8) (δ / 3) ≤ Fintype.card l)
    (hl' : 192 * (16 * (c : ℝ) ^ 2 - 1) * k ≤ ε ^ 2 * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  classical
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [setOf_one_add_mul_frobNorm_sub_lt_eq_empty_of_isEmpty _ _ _ hε.le, measureReal_empty]
    exact hδ.le
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) 0) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul] at hω'
    nlinarith [sq_nonneg (frobNorm A)]
  have hc1 : (1 : ℝ) ≤ c := (hsub (Classical.arbitrary l)).one_le_of_isIsotropic
    (hiso (Classical.arbitrary l))
  have hk0 : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  have hεJ : 0 < ε / (8 * √(k : ℝ)) := by positivity
  have hOSI := isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (d := k) hind hsub hiso (by positivity) (by linarith) (by positivity) hl
  have hJL := hasJLMoment_of_isSubgaussianVector hind hsub hiso hεJ
  rw [inv_sqrt_card_smul_conjTranspose] at hOSI hJL
  have hX' := aemeasurable_inv_sqrt_card_smul_of_isSubgaussianVector hsub
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 Fintype.card_pos
  have hc16 : (0 : ℝ) ≤ 16 * (c : ℝ) ^ 2 - 1 := by nlinarith
  have hδJ : (0 : ℝ) ≤ (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card l * (ε / (8 * √(k : ℝ))) ^ 2) := by
    positivity
  have hχ := hJL.measure_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le
    (A := A) (k := k) hX' hεJ le_rfl hδJ
  rw [show ε / (8 * √(k : ℝ)) * √(k : ℝ) = ε / 8 by field_simp] at hχ
  have h := (hOSI.hasSubspaceInjection (U := (truncatedSVD A k)ᴴ)
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)
    ).measure_frobNorm_sub_mul_sq_gt_one_add_mul_le hε hε1
    (P := fun ω => rangeProjector (truncatedSVD (A * X ω) k))
    (fun ω => isStarProjection_rangeProjector _)
    (fun ω => (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k))
    (fun ω => by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, ← smul_sub, frobNorm_smul,
        frobNorm_smul, rangeProjector_truncatedSVD_mul, Matrix.sub_mul]
      exact mul_le_mul_of_nonneg_left (frobNorm_sub_truncatedSVD_le_of_rank_le (A * X ω)
        ((Matrix.rank_mul_le_left _ _).trans (rank_truncatedSVD_le A k))) (norm_nonneg _))
    (hJL.measure_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_conjTranspose_sub_gt_le hX'
      hεJ le_rfl hδJ) hχ
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans ?_)
  · have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, Matrix.sub_mul, Matrix.one_mul] at hω'
    exact hω'
  · have e : (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card l * (ε / (8 * √(k : ℝ))) ^ 2) =
        64 * (16 * (c : ℝ) ^ 2 - 1) * k / (Fintype.card l * ε ^ 2) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      field_simp
      ring
    have h3 : 64 * (16 * (c : ℝ) ^ 2 - 1) * k / (Fintype.card l * ε ^ 2) ≤ δ / 3 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [e]
    linarith

/-- **$O(c^2(k/\delta + \log(1/\delta))/\varepsilon^2)$ sub-Gaussian columns suffice for early
truncation**: there are absolute constants $C, \varepsilon_0 > 0$ such that if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ of an $n \times \ell$ test matrix $\mathbf{\Omega}$ has independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell \ge Cc^2(k/\delta + \log(1/\delta))/\varepsilon^2$, then
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`, proved
from it with $C = 147456$ and $\varepsilon_0 = 1$.
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector
Result: etrsvd -/
theorem exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] [Nonempty l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (c : ℝ≥0) (k : ℕ) (ε δ : ℝ),
      iIndepFun (fun i ω => (X ω)ᴴ i) μ → (∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ) →
      (∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * ((k : ℝ) / δ + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  refine ⟨147456, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ _ μ A X c k ε δ hind hsub hiso hε hε1 hδ hδ2 hl
  have hL1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hkδ : (k : ℝ) ≤ k / δ := le_div_self (Nat.cast_nonneg k) hδ (by linarith)
  have hc2 := sq_nonneg (c : ℝ)
  have hk : (k : ℝ) / δ * δ = k := div_mul_cancel₀ _ hδ.ne'
  have hl' := hl
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hl'
  refine measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector A hind hsub
    hiso hε hε1 hδ ((subgaussianEmbeddingDim_le c k (ε / 8) (by positivity) (by linarith)).trans
      ?_) ?_
  · have hlog : Real.log (2 / (δ / 3)) ≤ 4 * Real.log (1 / δ) := by
      rw [show (4 : ℝ) * Real.log (1 / δ) = Real.log ((1 / δ) ^ 4) by
        rw [Real.log_pow]; norm_num]
      refine Real.log_le_log (by positivity) ?_
      rw [div_pow, one_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hδ 2, pow_pos hδ 3, pow_pos hδ 4]
    rw [div_le_iff₀ (by positivity)]
    have e : (Fintype.card l : ℝ) * (ε / 8) ^ 2 = Fintype.card l * ε ^ 2 / 64 := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left hlog hc2, mul_le_mul_of_nonneg_left hkδ hc2,
      mul_nonneg hc2 hL1]
  · nlinarith [mul_le_mul_of_nonneg_left hl' hδ.le, mul_nonneg hc2 hL1,
      mul_nonneg (mul_nonneg hc2 hL1) hδ.le, mul_nonneg hc2 (Nat.cast_nonneg (α := ℝ) k)]

end NLAlib
