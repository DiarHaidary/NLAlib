/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.EarlyTruncation
public import NLAlib.Matrix.Structured.Kronecker
public import NLAlib.Probability.SubGaussianVector.Norm
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
$1 - \delta$ at $\ell = O(c^2(k/(\varepsilon\delta) + \log(1/\delta)))$ through the second JL
moment and at $\ell = O(c^2k\log(1/\delta)/\varepsilon)$ through the JL moment at
$p = \log(1/\delta)$, and the early-truncated
randomized SVD $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ at
$\ell = O(c^2(k/\delta + \log(1/\delta))/\varepsilon^2)$, respectively
$O(c^2k\log(1/\delta)/\varepsilon^2)$. To a constant
factor, <!-- value subgaussianRangeFinderFactor c -->$1 + 5c/2$, the randomized SVD needs
only $\ell = O(c^2(k + \log(1/\delta)))$, the range-finder step of Hutch++. The family's
predicates are about the normalised sketch $\ell^{-1/2}\mathbf{\Omega}^{\mathsf{H}}$; the
generic theorems run there and `NLAlib.rsvd_smul_right` (respectively the projector of
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

## Main definitions

* `NLAlib.subgaussianRangeFinderFactor c`: the constant factor of the sub-Gaussian range
  finder, <!-- value subgaussianRangeFinderFactor c -->$1 + 5c/2$.

## Main results

* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`: the randomized SVD,
  its $\log(1/\delta)$ twin
  `measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`
  and the asymptotic form
  `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`.
* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`: the randomized SVD
  to that constant factor at $\ell = O(c^2(k + \log(1/\delta)))$, with $\log(1/\delta)$ in
  place of $1/\delta$ (the Hsu–Kakade–Zhang tail in place of the JL moment), and its
  asymptotic form
  `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`.
* `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`: early
  truncation, its $\log(1/\delta)$ twin (`…_of_subgaussianJLMomentDim_le`) and the asymptotic form
  `exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal Kronecker

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
$\ell \ge 25 c^2 (k \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, and
$\ell \ge 8(16c^2 - 1)k/(\varepsilon\delta)$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the first size is `subgaussianEmbeddingDim c k (1 / 2) (δ / 2)`
and $C$ is `subgaussianJLConstant`. The route: the OSI at constant $1/2$ and failure $\delta/2$,
the JL moment property at $\sqrt{\varepsilon/(4k)}$ and
`NLAlib.HasJLMoment.measureReal_frobNorm_sub_rsvd_sq_gt_le`. Incomparable with its
$\log(1/\delta)$ twin
`measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`
(rule 4): this one needs fewer columns at constant $\delta$, the twin for small $\delta$; the
asymptotic form `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector` is
proved from the twin.
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
  have hεJ : 0 < √(ε / (4 * k)) := Real.sqrt_pos.2 (by positivity)
  have hOSI := isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (d := k) hind hsub hiso (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) (half_pos hδ) hl
  have hJL := hasJLMoment_of_isSubgaussianVector hind hsub hiso hεJ
  rw [inv_sqrt_card_smul_conjTranspose] at hOSI hJL
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 Fintype.card_pos
  have hδJ : (0 : ℝ) ≤ (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card l * √(ε / (4 * k)) ^ 2) := by
    have : (0 : ℝ) ≤ 16 * (c : ℝ) ^ 2 - 1 := by nlinarith
    positivity
  have h := hJL.measureReal_frobNorm_sub_rsvd_sq_gt_le (A := A) (hOSI.hasSubspaceInjection
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

/-- **The randomized SVD with a sub-Gaussian test matrix, relative error**, $\log(1/\delta)$
size form: for $0 < \varepsilon \le 4$, $\delta > 0$ and a sketch
$\mathbf{\Omega}^{\mathsf{H}}$ with independent, isotropic, sub-Gaussian rows with proxy $c$,
if <!-- value subgaussianEmbeddingDim c k (1/2) (\delta/2) -->
$\ell \ge 25 c^2 (k \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$
and <!-- value subgaussianJLMomentDim c {\sqrt{\varepsilon/(4k)}} (\delta/2) -->
$\ell \ge 16c^2\max(2, \log(1/(\delta/2)))/(C\sqrt{\varepsilon/(4k)}^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the sizes are `subgaussianEmbeddingDim c k (1 / 2) (δ / 2)` and
`subgaussianJLMomentDim c (√(ε / (4 * k))) (δ / 2)`, and $C$ is `subgaussianJLConstant`. The route
of `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`, with the JL moment at
$p = \max(2, \log(2/\delta))$
(`NLAlib.hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`, whose budget
$\sqrt{\varepsilon/(4k)} \le 1 \le c$ needs $\varepsilon \le 4$); incomparable with it (rule 4).
Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`.
[Woodruff2014, Lemma 45 and Remark 46]; there for dense sign and Gaussian sketches, constants
unspecified.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
    [Nonempty l] (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε4 : ε ≤ 4) (hδ : 0 < δ) (hl : subgaussianEmbeddingDim c k (1 / 2) (δ / 2) ≤ Fintype.card l)
    (hl' : subgaussianJLMomentDim c (√(ε / (4 * k))) (δ / 2) ≤ Fintype.card l) :
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
  have hεJ : 0 < √(ε / (4 * k)) := Real.sqrt_pos.2 (by positivity)
  have hεJ1 : √(ε / (4 * k)) ≤ 1 := by
    refine Real.sqrt_le_one.2 ((div_le_one (by positivity)).2 ?_)
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hOSI := isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (d := k) hind hsub hiso (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) (half_pos hδ) hl
  have hJL := hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le hind hsub hiso hεJ
    (hεJ1.trans hc1) (half_pos hδ) hl'
  rw [inv_sqrt_card_smul_conjTranspose] at hOSI hJL
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 Fintype.card_pos
  have h := hJL.measureReal_frobNorm_sub_rsvd_sq_gt_le (A := A) (hOSI.hasSubspaceInjection
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    (aemeasurable_inv_sqrt_card_smul_of_isSubgaussianVector hsub) (by norm_num) hεJ
    (le_max_left _ _) (by positivity)
  have hsq : √(ε / (4 * k)) ^ 2 = ε / (4 * k) := Real.sq_sqrt (by positivity)
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans (by linarith))
  have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 < frobNorm (A - rsvd A (X ω)) ^ 2 :=
    hω
  change _ < frobNorm (A - rsvd A ((√(Fintype.card l : ℝ))⁻¹ • X ω)) ^ 2
  rw [rsvd_smul_right _ _ (inv_ne_zero (Real.sqrt_pos.2 hL).ne'), hsq]
  refine lt_of_eq_of_lt ?_ hω'
  field_simp
  ring

/-- **$O(c^2k\log(1/\delta)/\varepsilon)$ sub-Gaussian columns suffice for the randomized SVD**:
there are absolute constants $C, \varepsilon_0 > 0$ such that if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ of an $n \times \ell$ test matrix $\mathbf{\Omega}$ has independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell \ge Cc^2k\log(1/\delta)/\varepsilon$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$ ($k = 0$ is trivial); the proxy stays in the threshold. The
asymptotic form of
`measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`,
proved from it with $\varepsilon_0 = 1$; the injection size $O(c^2(k + \log(1/\delta)))$ is
dominated there for $k \ge 1$. [Woodruff2014, Lemma 45 and Remark 46]; there $O(k/\varepsilon)$
i.i.d. normal rows at constant failure probability; here any isotropic sub-Gaussian rows.
Asymptotic:
NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] [Nonempty l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (c : ℝ≥0) (k : ℕ) (ε δ : ℝ),
      iIndepFun (fun i ω => (X ω)ᴴ i) μ → (∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ) →
      (∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * (k : ℝ) * Real.log (1 / δ) / ε) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  refine ⟨13824, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ _ μ A X c k ε δ hind hsub hiso hε hε1 hδ hδ2 hl
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
  have h2 : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_gt_d9
  have hL : 0 ≤ Real.log (1 / δ) := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkL : Real.log (1 / δ) ≤ k * Real.log (1 / δ) := le_mul_of_one_le_left hL hk1
  have hkL2 : (k : ℝ) ≤ 2 * (k * Real.log (1 / δ)) := by nlinarith
  have hc2 : 0 ≤ (c : ℝ) ^ 2 := sq_nonneg _
  have hcε : (c : ℝ) ^ 2 * k * Real.log (1 / δ) ≤ (c : ℝ) ^ 2 * k * Real.log (1 / δ) / ε :=
    le_div_self (by positivity) hε hε1
  have hl4 : Real.log (2 / (δ / 2)) = Real.log 2 + Real.log 2 + Real.log (1 / δ) := by
    rw [show 2 / (δ / 2) = 2 * 2 * (1 / δ) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by norm_num)]
  have hlh : Real.log (1 / (δ / 2)) = Real.log 2 + Real.log (1 / δ) := by
    rw [show 1 / (δ / 2) = 2 * (1 / δ) by field_simp, Real.log_mul (by norm_num) (by positivity)]
  refine measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
    A hind hsub hiso hε (by linarith) hδ ?_ ?_
  · refine (subgaussianEmbeddingDim_le _ _ _ (half_pos hδ) (by linarith)).trans (le_trans ?_ hl)
    rw [hl4, div_le_iff₀ (by norm_num)]
    nlinarith [mul_le_mul_of_nonneg_left hkL2 hc2, mul_le_mul_of_nonneg_left h2 hc2,
      mul_le_mul_of_nonneg_left hkL hc2, mul_nonneg hc2 hL]
  · refine (subgaussianJLMomentDim_le _ _ (half_pos hδ) (by linarith)).trans (le_trans ?_ hl)
    rw [Real.sq_sqrt (by positivity), hlh]
    rw [show 1728 * (c : ℝ) ^ 2 * (Real.log 2 + Real.log (1 / δ)) / (ε / (4 * k)) =
      6912 * ((c : ℝ) ^ 2 * k * (Real.log 2 + Real.log (1 / δ))) / ε by field_simp; ring,
      mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ hε.le
    nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ 2 * k)]

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Early-truncated randomized SVD with a sub-Gaussian test matrix, tail**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has independent, isotropic, sub-Gaussian rows with proxy $c$,
$0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value subgaussianEmbeddingDim c k (\varepsilon/6) (\delta/3) -->
$\ell \ge 25 c^2 (k \log 21 + \log(2/(\delta/3)))/(16C (\varepsilon/6)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, and
$\ell \ge 108(16c^2 - 1)k/(\varepsilon^2\delta)$, then
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the first size is
`subgaussianEmbeddingDim c k (ε / 6) (δ / 3)` and $C$ is `subgaussianJLConstant`. The route of
the Gaussian statement
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`, with the
family's OSI and JL moment property. Incomparable with its $\log(1/\delta)$ twin
`measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`
(rule 4); the asymptotic form
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector` is
proved from the twin.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for dense random sign matrices,
with unspecified constants.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector [Nonempty l]
    (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hl : subgaussianEmbeddingDim c k (ε / 6) (δ / 3) ≤ Fintype.card l)
    (hl' : 108 * (16 * (c : ℝ) ^ 2 - 1) * k ≤ ε ^ 2 * δ * Fintype.card l) :
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
  have hεJ : 0 < ε / (6 * √(k : ℝ)) := by positivity
  have hOSI := isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (d := k) hind hsub hiso (by positivity) (by linarith) (by positivity) hl
  have hJL := hasJLMoment_of_isSubgaussianVector hind hsub hiso hεJ
  have hc16 : (0 : ℝ) ≤ 16 * (c : ℝ) ^ 2 - 1 := by nlinarith
  rw [inv_sqrt_card_smul_conjTranspose] at hOSI hJL
  refine (hJL.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    (aemeasurable_inv_sqrt_card_smul_of_isSubgaussianVector hsub) hε hε1 le_rfl
    (div_nonneg hc16 (by positivity))).trans ?_
  have e : (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card l * (ε / (6 * √(k : ℝ))) ^ 2) =
      36 * (16 * (c : ℝ) ^ 2 - 1) * k / (Fintype.card l * ε ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    field_simp
    ring
  have h3 : 36 * (16 * (c : ℝ) ^ 2 - 1) * k / (Fintype.card l * ε ^ 2) ≤ δ / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [e]
  linarith

-- A backticked declaration name in the docstring exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Early-truncated randomized SVD with a sub-Gaussian test matrix, tail**, $\log(1/\delta)$
size form: if the sketch $\mathbf{\Omega}^{\mathsf{H}}$ has independent, isotropic, sub-Gaussian
rows with proxy $c$, $0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value subgaussianEmbeddingDim c k (\varepsilon/6) (\delta/3) -->
$\ell \ge 25 c^2 (k \log 21 + \log(2/(\delta/3)))/(16C (\varepsilon/6)^2)$ and at
least <!-- value subgaussianJLMomentDim c (\varepsilon/(6\sqrt{k})) (\delta/3) -->
$\ell \ge 16c^2\max(2, \log(1/(\delta/3)))/(C(\varepsilon/(6\sqrt{k}))^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, then
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the sizes are `subgaussianEmbeddingDim c k (ε / 6) (δ / 3)` and
`subgaussianJLMomentDim c (ε / (6 * √k)) (δ / 3)`, and $C$ is `subgaussianJLConstant`. The route
of `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`, with the
JL moment at $p = \max(2, \log(3/\delta))$
(`NLAlib.hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`, budget
$\varepsilon/(6\sqrt{k}) \le 1 \le c$); incomparable with it (rule 4). Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector`.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for dense random sign matrices,
with unspecified constants.
Result: etrsvd -/
theorem
    measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
    [Nonempty l] (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hl : subgaussianEmbeddingDim c k (ε / 6) (δ / 3) ≤ Fintype.card l)
    (hl' : subgaussianJLMomentDim c (ε / (6 * √(k : ℝ))) (δ / 3) ≤ Fintype.card l) :
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
  have hk1 : (1 : ℝ) ≤ √(k : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hk)
  have hεJ : 0 < ε / (6 * √(k : ℝ)) := by positivity
  have hεJ1 : ε / (6 * √(k : ℝ)) ≤ 1 := by
    rw [div_le_one (by positivity)]
    linarith
  have hOSI := isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (d := k) hind hsub hiso (by positivity) (by linarith) (by positivity) hl
  have hJL := hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le hind hsub hiso hεJ
    (hεJ1.trans hc1) (by positivity) hl'
  rw [inv_sqrt_card_smul_conjTranspose] at hOSI hJL
  exact (hJL.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    (aemeasurable_inv_sqrt_card_smul_of_isSubgaussianVector hsub) hε hε1 (le_max_left _ _)
    (by positivity)).trans (by linarith)

-- The explicit theorem's full name in the `Asymptotic:` tag exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(c^2k\log(1/\delta)/\varepsilon^2)$ sub-Gaussian columns suffice for early
truncation**: there are absolute constants $C, \varepsilon_0 > 0$ such that if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ of an $n \times \ell$ test matrix $\mathbf{\Omega}$ has independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell \ge Cc^2k\log(1/\delta)/\varepsilon^2$, then
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$ ($k = 0$ is trivial). The asymptotic form of
`measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`,
proved from it with $\varepsilon_0 = 1$. [CohenElderMuscoMuscoPersu2015, Theorem 12 and
Lemma 3]; there $\mathbf{A}\mathbf{\Omega}$ is a projection-cost-preserving sketch with error
$O(\varepsilon)$ for the dense sign matrices of Lemma 11 (family 1) with
$O((k + \log(1/\delta))/\varepsilon^2)$ rows; here any isotropic sub-Gaussian rows, with the
product $k\log(1/\delta)$ from the route through JL moments.
Asymptotic:
NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
Result: etrsvd -/
theorem exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] [Nonempty l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (c : ℝ≥0) (k : ℕ) (ε δ : ℝ),
      iIndepFun (fun i ω => (X ω)ᴴ i) μ → (∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ) →
      (∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * (k : ℝ) * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  refine ⟨186624, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ _ μ A X c k ε δ hind hsub hiso hε hε1 hδ hδ2 hl
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
  have h2 : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; linarith)
  have hl2 := Real.log_two_gt_d9
  have hL : 0 ≤ Real.log (1 / δ) := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hkL : Real.log (1 / δ) ≤ k * Real.log (1 / δ) := le_mul_of_one_le_left hL hk1
  have hkL2 : (k : ℝ) ≤ 2 * (k * Real.log (1 / δ)) := by nlinarith
  have hc2 : 0 ≤ (c : ℝ) ^ 2 := sq_nonneg _
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have h34 : Real.log 3 ≤ Real.log 4 := Real.log_le_log (by norm_num) (by norm_num)
  have h3 : Real.log (1 / (δ / 3)) ≤ 3 * Real.log (1 / δ) := by
    rw [show 1 / (δ / 3) = 3 * (1 / δ) by field_simp, Real.log_mul (by norm_num) (by positivity)]
    linarith
  have h6 : Real.log (2 / (δ / 3)) ≤ 4 * Real.log (1 / δ) := by
    rw [show 2 / (δ / 3) = 2 * 3 * (1 / δ) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by norm_num) (by norm_num)]
    linarith
  refine
    measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
    A hind hsub hiso hε hε1 hδ ?_ ?_
  · refine (subgaussianEmbeddingDim_le _ _ _ (by positivity) (by linarith)).trans
      (le_trans ?_ hl)
    generalize Real.log (2 / (δ / 3)) = t at h6 ⊢
    rw [show 172 * (c : ℝ) ^ 2 * ((k : ℝ) + t) / (ε / 6) ^ 2 =
      6192 * ((c : ℝ) ^ 2 * ((k : ℝ) + t)) / ε ^ 2 by field_simp; ring, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
    nlinarith [mul_le_mul_of_nonneg_left hkL2 hc2, mul_le_mul_of_nonneg_left h6 hc2,
      mul_le_mul_of_nonneg_left hkL hc2]
  · refine (subgaussianJLMomentDim_le _ _ (by positivity) (by linarith)).trans (le_trans ?_ hl)
    generalize Real.log (1 / (δ / 3)) = t at h3 ⊢
    rw [show 1728 * (c : ℝ) ^ 2 * t / (ε / (6 * √(k : ℝ))) ^ 2 =
      62208 * ((c : ℝ) ^ 2 * k * t) / ε ^ 2 by
        rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]; field_simp; ring,
      mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
    nlinarith [mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ (c : ℝ) ^ 2 * k)]

/-! ### The constant-factor range finder -/

/-- **The sub-Gaussian range-finder factor** <!-- value subgaussianRangeFinderFactor c -->
$1 + 5c/2$: the constant factor in front of
$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ in the error of the randomized
SVD with a sub-Gaussian test matrix with proxy $c$, at failure probability $\delta$ and
$\ell = O(c^2(k + \log(1/\delta)))$ columns
(`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`). The proof (a
subspace injection with constant $1/2$ and the Hsu–Kakade–Zhang tail of
$\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\mathbf{\Omega}\|_{\mathsf{F}}^2$ at
$t = \log(2/\delta) \le \ell/225$, which the size gives) reaches
$1 + 2c(1 + 2/15 + 2/225) \le 1 + 5c/2$, at least $7/2$ since isotropy forces $c \ge 1$; the
route cannot go below $1 + 2c$. Smaller is better; consumers use only
`one_le_subgaussianRangeFinderFactor`, `subgaussianRangeFinderFactor_mono` and
`subgaussianRangeFinderFactor_le`.
[MeyerMuscoMuscoWoodruff2021, §3, proof of Theorem 1]; there the factor $2$ at an unspecified
sample size, citing Musco and Musco (2020, Corollary 7 and Claim 1). -/
noncomputable irreducible_def subgaussianRangeFinderFactor (c : ℝ) : ℝ := 1 + 5 / 2 * c

/-- The sub-Gaussian range-finder factor is at least $1$ for $c \ge 0$. -/
theorem one_le_subgaussianRangeFinderFactor {c : ℝ} (hc : 0 ≤ c) :
    1 ≤ subgaussianRangeFinderFactor c := by
  rw [subgaussianRangeFinderFactor_def]
  linarith

/-- The sub-Gaussian range-finder factor is monotone in the proxy $c$. -/
theorem subgaussianRangeFinderFactor_mono {c c' : ℝ} (hcc' : c ≤ c') :
    subgaussianRangeFinderFactor c ≤ subgaussianRangeFinderFactor c' := by
  rw [subgaussianRangeFinderFactor_def, subgaussianRangeFinderFactor_def]
  linarith

/-- The explicit upper bound $1 + 5c/2$ on the sub-Gaussian range-finder factor, whose value
is <!-- value subgaussianRangeFinderFactor c -->$1 + 5c/2$. -/
theorem subgaussianRangeFinderFactor_le (c : ℝ) :
    subgaussianRangeFinderFactor c ≤ 1 + 5 / 2 * c := by
  rw [subgaussianRangeFinderFactor_def]

omit [DecidableEq n] in
/-- $\|(\mathbf{I}_\ell \otimes \mathbf{B})\mathbf{v}\|^2 = \sum_i \|\mathbf{B}\mathbf{v}_i\|^2$,
with $\mathbf{v}_i$ the $i$-th block of $\mathbf{v}$. -/
private theorem norm_one_kronecker_mulVec_sq [DecidableEq l] (B : Matrix m n ℝ)
    (v : l × n → ℝ) :
    ‖WithLp.toLp 2 (((1 : Matrix l l ℝ) ⊗ₖ B) *ᵥ v)‖ ^ 2 =
      ∑ i, ‖WithLp.toLp 2 (B *ᵥ fun j => v (i, j))‖ ^ 2 := by
  have e : ∀ i r, (((1 : Matrix l l ℝ) ⊗ₖ B) *ᵥ v) (i, r) = (B *ᵥ fun j => v (i, j)) r := by
    intro i r
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.one_apply, ite_mul]
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, e]

omit [DecidableEq n] in
/-- The injection step of `measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`: on
the subspace injection event of the normalised sketch, the error of the randomized SVD is at most
$\|\mathbf{E}\|_{\mathsf{F}}^2 + 2\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2/\ell$,
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$. -/
private theorem frobNorm_sub_rsvd_sq_le_add_of_isSubspaceInjection [Nonempty l] {p : Type*}
    [Fintype p] [DecidableEq p] {A : Matrix m n ℝ} {k : ℕ} {Z : Matrix n p ℝ}
    (hZ : HasOrthonormalCols Z) (hAZ : A * Z * Zᴴ = truncatedSVD A k) {Y : Matrix n l ℝ}
    (h : IsSubspaceInjection ((√(Fintype.card l : ℝ))⁻¹ • Y)ᴴ Z (1 - 1 / 2)) :
    frobNorm (A - rsvd A Y) ^ 2 ≤ frobNorm (A - truncatedSVD A k) ^ 2 +
      2 * frobNorm ((A - truncatedSVD A k) * Y) ^ 2 / Fintype.card l := by
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 Fintype.card_pos
  have h1 := h.frobNorm_sub_rsvd_sq_le hZ (by norm_num) A
  rw [hAZ, rsvd_smul_right _ _ (inv_ne_zero (Real.sqrt_pos.2 hL).ne'), Matrix.mul_smul,
    frobNorm_smul, mul_pow, norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _), inv_pow,
    Real.sq_sqrt hL.le] at h1
  refine h1.trans (le_of_eq ?_)
  field_simp
  ring

/-- The size step of `measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`: for
$c \ge 1$ and $0 < \delta < 1$, the embedding size at constant $1/2$ and failure $\delta/2$ is
at least $225\log(2/\delta)$. -/
private theorem mul_log_two_div_le_of_subgaussianEmbeddingDim_le {c : ℝ≥0} {k : ℕ} {δ L : ℝ}
    (hc1 : (1 : ℝ) ≤ c) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hl : subgaussianEmbeddingDim c k (1 / 2) (δ / 2) ≤ L) : 225 * Real.log (2 / δ) ≤ L := by
  set t := Real.log (2 / δ)
  have ht0 : 0 ≤ t := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  rw [subgaussianEmbeddingDim_def, subgaussianJLConstant_def] at hl
  have h4 : t ≤ Real.log (2 / (δ / 2)) :=
    Real.log_le_log (by positivity) (div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (by linarith))
  have h21 : 0 ≤ (k : ℝ) * Real.log 21 :=
    mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num))
  have hc2 : (1 : ℝ) ≤ (c : ℝ) ^ 2 := by nlinarith
  have e : 25 * (c : ℝ) ^ 2 * (k * Real.log 21 + Real.log (2 / (δ / 2))) /
      (16 * (1 / 36) * (1 / 2) ^ 2) =
        225 * ((c : ℝ) ^ 2 * (k * Real.log 21 + Real.log (2 / (δ / 2)))) := by
    ring
  rw [e] at hl
  nlinarith

omit [DecidableEq n] in
/-- The Hsu–Kakade–Zhang threshold step of
`measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`: for
$\mathbf{M} = \mathbf{I}_\ell \otimes \mathbf{E}$, $t \ge 0$ and $225t \le \ell$,
$c(\|\mathbf{M}\|_{\mathsf{F}}^2 + 2\|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_{\mathsf{F}}\sqrt t
+ 2\|\mathbf{M}\|_2^2t) \le (5/4)c\ell\|\mathbf{E}\|_{\mathsf{F}}^2$, since
$1 + 2/15 + 2/225 \le 5/4$. -/
private theorem mul_frobNorm_one_kronecker_add_le [DecidableEq l] (E : Matrix m n ℝ) (c : ℝ≥0)
    {t : ℝ} (ht0 : 0 ≤ t) (htL : 225 * t ≤ Fintype.card l) :
    (c : ℝ) * (frobNorm ((1 : Matrix l l ℝ) ⊗ₖ E) ^ 2 +
        2 * frobNorm (((1 : Matrix l l ℝ) ⊗ₖ E)ᴴ * ((1 : Matrix l l ℝ) ⊗ₖ E)) * √t +
        2 * specNorm ((1 : Matrix l l ℝ) ⊗ₖ E) ^ 2 * t) ≤
      5 / 4 * c * (Fintype.card l : ℝ) * frobNorm E ^ 2 := by
  set L : ℝ := (Fintype.card l : ℝ)
  have hL0 : 0 ≤ L := Nat.cast_nonneg _
  set M : Matrix (l × m) (l × n) ℝ := (1 : Matrix l l ℝ) ⊗ₖ E with hM
  have hFM : frobNorm M ^ 2 = L * frobNorm E ^ 2 := by
    rw [hM, frobNorm_kronecker, mul_pow, frobNorm_one_sq]
  have hEF : frobNorm (Eᴴ * E) ≤ frobNorm E ^ 2 := by
    have := frobNorm_mul_le Eᴴ E
    rwa [frobNorm_conjTranspose, ← sq] at this
  have hG : 15 * (frobNorm (Mᴴ * M) * √t) ≤ L * frobNorm E ^ 2 := by
    have e : Mᴴ * M = (1 : Matrix l l ℝ) ⊗ₖ (Eᴴ * E) := by
      rw [hM, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
        ← Matrix.mul_kronecker_mul, Matrix.one_mul]
    have hF2 : frobNorm (Mᴴ * M) = √L * frobNorm (Eᴴ * E) := by
      rw [e, frobNorm_kronecker, ← Real.sqrt_sq (frobNorm_nonneg (1 : Matrix l l ℝ)),
        frobNorm_one_sq]
    have hst : 15 * √t ≤ √L := by
      rw [Real.le_sqrt (by positivity) hL0, mul_pow, Real.sq_sqrt ht0]
      linarith
    rw [hF2]
    calc 15 * (√L * frobNorm (Eᴴ * E) * √t) = √L * frobNorm (Eᴴ * E) * (15 * √t) := by ring
      _ ≤ √L * frobNorm E ^ 2 * √L := by
          gcongr
      _ = L * frobNorm E ^ 2 := by
          rw [mul_comm, ← mul_assoc, Real.mul_self_sqrt hL0]
  have hS : 225 * (specNorm M ^ 2 * t) ≤ L * frobNorm E ^ 2 := by
    have h1 : specNorm M ≤ frobNorm E := by
      rw [hM, specNorm_kronecker]
      exact (mul_le_of_le_one_left (specNorm_nonneg E) specNorm_one_le).trans
        (specNorm_le_frobNorm E)
    have h2 : specNorm M ^ 2 ≤ frobNorm E ^ 2 := pow_le_pow_left₀ (specNorm_nonneg _) h1 2
    calc 225 * (specNorm M ^ 2 * t) = specNorm M ^ 2 * (225 * t) := by ring
      _ ≤ frobNorm E ^ 2 * L := by
          gcongr
      _ = L * frobNorm E ^ 2 := mul_comm _ _
  have : frobNorm M ^ 2 + 2 * frobNorm (Mᴴ * M) * √t + 2 * specNorm M ^ 2 * t ≤
      5 / 4 * (L * frobNorm E ^ 2) := by
    nlinarith [sq_nonneg (frobNorm E), hL0]
  calc (c : ℝ) * (frobNorm M ^ 2 + 2 * frobNorm (Mᴴ * M) * √t + 2 * specNorm M ^ 2 * t)
      ≤ c * (5 / 4 * (L * frobNorm E ^ 2)) := mul_le_mul_of_nonneg_left this c.2
    _ = 5 / 4 * c * L * frobNorm E ^ 2 := by ring

/-- **The randomized SVD with a sub-Gaussian test matrix, constant factor**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ has independent, isotropic, sub-Gaussian rows with proxy $c$,
$\delta > 0$ and <!-- value subgaussianEmbeddingDim c k (1/2) (\delta/2) -->
$\ell \ge 25 c^2 (k \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$,
then <!-- value subgaussianRangeFinderFactor c -->
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 5c/2)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the size is `subgaussianEmbeddingDim c k (1 / 2) (δ / 2)`, $C$
is `subgaussianJLConstant` and the factor is `subgaussianRangeFinderFactor c`. That is
$\ell = O(c^2(k + \log(1/\delta)))$ columns for a constant factor, against the $1/\delta$ in the
size of the relative-error form
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`. The route, with
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$: the OSI at constant $1/2$ and
failure $\delta/2$ for the normalised sketch $\ell^{-1/2}\mathbf{\Omega}^{\mathsf{H}}$; the
structural bound `NLAlib.IsSubspaceInjection.frobNorm_sub_rsvd_sq_le`, giving
$\|\mathbf{E}\|_{\mathsf{F}}^2 + 2\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2/\ell$; and the
Hsu–Kakade–Zhang tail `NLAlib.IsSubgaussianVector.measureReal_norm_mulVec_sq_ge_le` for
$\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2 = \|(\mathbf{I}_\ell \otimes \mathbf{E})
\operatorname{vec}\mathbf{\Omega}\|^2$ at $t = \log(2/\delta)$ (the vectorization has proxy $c$
by `NLAlib.IsSubgaussianVector.uncurry_of_iIndepFun`), which gives
$\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2 < (5/4)c\ell\|\mathbf{E}\|_{\mathsf{F}}^2$ except with
probability $\delta/2$. The condition $225\log(2/\delta) \le \ell$ that step needs follows from
the size hypothesis, since isotropy forces $c \ge 1$
(`NLAlib.IsSubgaussianVector.one_le_of_isIsotropic`). Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`.
[MeyerMuscoMuscoWoodruff2021, §3, proof of Theorem 1]; there as the range-finder step of
Hutch++, with the factor $2$ at an unspecified sample size, citing Musco and Musco (2020,
Corollary 7 and Claim 1); here by a different route, with the factor and the size explicit (the
route's floor is $1 + 2c$).
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector [Nonempty l]
    (A : Matrix m n ℝ) {c : ℝ≥0} (hind : iIndepFun (fun i ω => (X ω)ᴴ i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hl : subgaussianEmbeddingDim c k (1 / 2) (δ / 2) ≤ Fintype.card l) :
    μ.real {ω | subgaussianRangeFinderFactor c * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  classical
  have := hind.isProbabilityMeasure
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact measureReal_le_one.trans hδ1
  rw [subgaussianRangeFinderFactor_def]
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [setOf_one_add_mul_frobNorm_sub_lt_eq_empty_of_isEmpty _ _ _ (by positivity),
      measureReal_empty]
    exact hδ.le
  have hc1 : (1 : ℝ) ≤ c := (hsub (Classical.arbitrary l)).one_le_of_isIsotropic
    (hiso (Classical.arbitrary l))
  set E := A - truncatedSVD A k
  set L : ℝ := (Fintype.card l : ℝ)
  have hL : (0 : ℝ) < L := Nat.cast_pos.2 Fintype.card_pos
  -- The injection event, for a frame of the head.
  obtain ⟨Z, hZ, -, -, hAZ⟩ :=
    exists_hasOrthonormalCols_range_eq_range_conjTranspose_truncatedSVD (p := Fin _) A k
      (Fintype.card_fin _)
  have hZk : Z.rank ≤ k := by
    rw [hZ.rank_eq, Fintype.card_fin]
    exact rank_truncatedSVD_le A k
  have hOSI := isObliviousSubspaceInjection_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    (d := k) hind hsub hiso (by norm_num : (0 : ℝ) < 1 / 2) (by linarith) (half_pos hδ) hl
  rw [inv_sqrt_card_smul_conjTranspose] at hOSI
  have hinj : μ.real {ω | ¬ IsSubspaceInjection ((√L)⁻¹ • X ω)ᴴ Z (1 - 1 / 2)} ≤ δ / 2 :=
    hOSI.hasSubspaceInjection hZk
  have hgood : ∀ ω, IsSubspaceInjection ((√L)⁻¹ • X ω)ᴴ Z (1 - 1 / 2) →
      frobNorm (A - rsvd A (X ω)) ^ 2 ≤ frobNorm E ^ 2 + 2 * frobNorm (E * X ω) ^ 2 / L :=
    fun ω h => frobNorm_sub_rsvd_sq_le_add_of_isSubspaceInjection hZ hAZ h
  by_cases hE0 : E = 0
  · refine (measureReal_mono fun ω hω => ?_).trans (hinj.trans (by linarith))
    intro h
    have h1 := hgood ω h
    have hω' : (1 + 5 / 2 * (c : ℝ)) * frobNorm E ^ 2 < frobNorm (A - rsvd A (X ω)) ^ 2 := hω
    simp only [hE0, Matrix.zero_mul, frobNorm_zero, zero_pow two_ne_zero, mul_zero, zero_div,
      add_zero] at h1 hω'
    linarith
  -- The Hsu–Kakade–Zhang event, on the vectorization of the test matrix.
  set t := Real.log (2 / δ)
  have ht0 : 0 ≤ t := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have htL : 225 * t ≤ L := mul_log_two_div_le_of_subgaussianEmbeddingDim_le hc1 hδ hδ1 hl
  set M : Matrix (l × m) (l × n) ℝ := (1 : Matrix l l ℝ) ⊗ₖ E with hM
  have hFM : frobNorm M ^ 2 = L * frobNorm E ^ 2 := by
    rw [hM, frobNorm_kronecker, mul_pow, frobNorm_one_sq]
  have hM0 : M ≠ 0 := by
    intro h
    apply hE0
    rw [← frobNorm_eq_zero_iff, ← pow_eq_zero_iff two_ne_zero]
    rw [h, frobNorm_zero, zero_pow two_ne_zero] at hFM
    exact (mul_eq_zero.1 hFM.symm).resolve_left hL.ne'
  have hHKZ := (IsSubgaussianVector.uncurry_of_iIndepFun hind hsub).measureReal_norm_mulVec_sq_ge_le
    (by rintro rfl; norm_num at hc1) hM0 ht0
  have hexp : Real.exp (-t) = δ / 2 := by
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  rw [hexp] at hHKZ
  have hvecE : ∀ ω, ‖WithLp.toLp 2 (M *ᵥ fun p => Function.uncurry (X ω)ᴴ p)‖ ^ 2 =
      frobNorm (E * X ω) ^ 2 := by
    intro ω
    rw [hM, norm_one_kronecker_mulVec_sq, frobNorm_sq_eq_sum_col]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 3
  have hT := mul_frobNorm_one_kronecker_add_le E c ht0 htL
  -- Outside both events the error is at most `(1 + 5c/2)‖E‖²`.
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _))
    ((measureReal_union_le _ _).trans ((add_le_add hinj hHKZ).trans_eq (add_halves δ)))
  intro ω hω
  by_contra hc
  simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_not, not_le] at hc
  obtain ⟨h1, h2⟩ := hc
  simp only [RCLike.ofReal_real_eq_id, id_eq] at h2
  rw [hvecE] at h2
  have hg := hgood ω h1
  have hω' : (1 + 5 / 2 * (c : ℝ)) * frobNorm E ^ 2 < frobNorm (A - rsvd A (X ω)) ^ 2 := hω
  have h3 : 2 * frobNorm (E * X ω) ^ 2 / L ≤ 5 / 2 * c * frobNorm E ^ 2 := by
    rw [div_le_iff₀ hL]
    linarith [h2.le.trans hT]
  linarith

/-- **$O(c^2(k + \log(1/\delta)))$ sub-Gaussian columns suffice for the randomized SVD to a
constant factor**: there is an absolute constant $C > 0$ such that if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ of an $n \times \ell$ test matrix $\mathbf{\Omega}$ has independent,
isotropic, sub-Gaussian rows with proxy $c$, $0 < \delta \le 1/2$ and
$\ell \ge Cc^2(k + \log(1/\delta))$, then <!-- value subgaussianRangeFinderFactor c -->
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 5c/2)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the factor is `subgaussianRangeFinderFactor c`, and the proxy
stays in the threshold. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector`, proved from it with
$C = 2064$. [MeyerMuscoMuscoWoodruff2021, §3, proof of Theorem 1]; there for a random sign sketch
with $O(k + \log(1/\delta))$ columns and the factor $2$, citing Musco and Musco (2020).
Asymptotic: NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] [Nonempty l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (c : ℝ≥0) (k : ℕ) (δ : ℝ),
      iIndepFun (fun i ω => (X ω)ᴴ i) μ → (∀ i, IsSubgaussianVector (fun ω => (X ω)ᴴ i) c μ) →
      (∀ i, IsIsotropic (fun ω => (X ω)ᴴ i) μ) → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * (k + Real.log (1 / δ))) ≤ Fintype.card l →
      μ.real {ω | subgaussianRangeFinderFactor c * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  refine ⟨2064, by norm_num, ?_⟩
  intro Ω m n l _ _ _ _ _ _ μ A X c k δ hind hsub hiso hδ hδ2 hl
  have hL1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hc2 := sq_nonneg (c : ℝ)
  refine measureReal_frobNorm_sub_rsvd_sq_gt_le_mul_of_isSubgaussianVector A hind hsub hiso hδ
    ((subgaussianEmbeddingDim_le c k (1 / 2) (half_pos hδ) (by linarith)).trans ?_)
  have hlog : Real.log (2 / (δ / 2)) ≤ 3 * Real.log (1 / δ) := by
    rw [show (3 : ℝ) * Real.log (1 / δ) = Real.log ((1 / δ) ^ 3) by
      rw [Real.log_pow]; norm_num]
    refine Real.log_le_log (by positivity) ?_
    rw [div_pow, one_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hδ 2, pow_pos hδ 3]
  rw [show 172 * (c : ℝ) ^ 2 * (k + Real.log (2 / (δ / 2))) / (1 / 2) ^ 2 =
    688 * ((c : ℝ) ^ 2 * (k + Real.log (2 / (δ / 2)))) by ring]
  refine le_trans ?_ hl
  nlinarith [mul_le_mul_of_nonneg_left hlog hc2, mul_nonneg hc2 hL1,
    mul_nonneg hc2 (Nat.cast_nonneg (α := ℝ) k)]

end NLAlib
