/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.EarlyTruncation
public import NLAlib.Sketching.Sparse.CountSketchEmbedding

/-!
# The randomized SVD and early truncation with a CountSketch test matrix

The CountSketch instances of `NLAlib.LowRank.Oblivious.RangeFinder` and
`NLAlib.LowRank.Oblivious.EarlyTruncation`, for the family of `NLAlib.Sketching.Sparse.CountSketch`
and `NLAlib.Sketching.Sparse.CountSketchEmbedding`: a test matrix
$\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ whose sketch $\mathbf{\Omega}^{\mathsf{H}}$ is a
CountSketch (`hX : HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ`), unnormalised and over any
`RCLike` field. The randomized SVD $\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ reaches error
$(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with probability
$1 - \delta$ at $\ell = O((k^2 + k/\varepsilon)/\delta)$, and the early-truncated randomized SVD
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ at
$\ell = O(k^2/(\varepsilon^2\delta))$. Both run the injection of the family at the head with the
CountSketch's own approximate-multiplication tail
(`NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch`, failure
$2/(\ell\varepsilon^2)$, over any field), through the generic forms that take a multiplication
tail: `NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le` and
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le`.

**Statements with no per-family form.** Nyström, generalized Nyström and the truncations apply
through the family's OSI:
```
isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le hX k hε hδ hl
```
about `fun ω => (X ω)ᴴ` itself (the CountSketch is isotropic unscaled). Design:
`docs/design/LowRank-S7.md` §3.5, §8.

## Main results

* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch`: the randomized SVD, and
  its asymptotic form `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch`.
* `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch`: early
  truncation, and its asymptotic form
  `exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq l] {X : Ω → Matrix n l 𝕜}

/-- The tail–head multiplication error of a CountSketch:
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
\mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k^{\mathsf{H}}}\|_{\mathsf{F}} \le
\varepsilon\sqrt{k}\,\|\mathbf{E}\|_{\mathsf{F}}$ except with probability
$2/(\ell\varepsilon^2)$, $\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$. -/
private theorem measureReal_frobNorm_tail_head_gt_le_of_hasLaw_countSketch
    (hX : HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ) (A : Matrix m n 𝕜) (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    μ.real {ω | ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * rangeProjector (truncatedSVD A k)ᴴ)} ≤
      2 / (Fintype.card l * ε ^ 2) := by
  classical
  have : IsFiniteMeasure μ := hX.isFiniteMeasure_iff.2 inferInstance
  have hEP : (A - truncatedSVD A k) * rangeProjector (truncatedSVD A k)ᴴ = 0 := by
    have h := conjTranspose_mul_rangeProjector (truncatedSVD A k)ᴴ
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [Matrix.sub_mul, mul_rangeProjector_conjTranspose_truncatedSVD, h, sub_self]
  have h2 : (0 : ℝ) ≤ 2 / (Fintype.card l * ε ^ 2) := by positivity
  by_cases h0 : A - truncatedSVD A k = 0
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) h2
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) < frobNorm ((A - truncatedSVD A k) *
        X ω * (X ω)ᴴ * rangeProjector (truncatedSVD A k)ᴴ) := hω
    simp [h0] at hω'
  by_cases hP : rangeProjector (truncatedSVD A k)ᴴ = 0
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) h2
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) < frobNorm ((A - truncatedSVD A k) *
        X ω * (X ω)ᴴ * rangeProjector (truncatedSVD A k)ᴴ) := hω
    rw [hP, Matrix.mul_zero, frobNorm_zero] at hω'
    have : 0 ≤ ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) := by positivity
    linarith
  have h0' : (A - truncatedSVD A k)ᴴ ≠ 0 := by rwa [Ne, Matrix.conjTranspose_eq_zero]
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch hX hε h0' hP)
  have hω' : ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) < frobNorm ((A - truncatedSVD A k) *
      X ω * (X ω)ᴴ * rangeProjector (truncatedSVD A k)ᴴ) := hω
  change ε * frobNorm (A - truncatedSVD A k)ᴴ * frobNorm (rangeProjector (truncatedSVD A k)ᴴ) ≤
    frobNorm ((A - truncatedSVD A k)ᴴᴴ * ((X ω)ᴴ)ᴴ * (X ω)ᴴ *
      rangeProjector (truncatedSVD A k)ᴴ - (A - truncatedSVD A k)ᴴᴴ *
        rangeProjector (truncatedSVD A k)ᴴ)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose, hEP, sub_zero,
    frobNorm_conjTranspose]
  have hPk : frobNorm (rangeProjector (truncatedSVD A k)ᴴ) ≤ √(k : ℝ) := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [frobNorm_rangeProjector_sq, Matrix.rank_conjTranspose]
    exact_mod_cast rank_truncatedSVD_le A k
  calc ε * frobNorm (A - truncatedSVD A k) * frobNorm (rangeProjector (truncatedSVD A k)ᴴ)
      ≤ ε * frobNorm (A - truncatedSVD A k) * √(k : ℝ) := by gcongr
    _ = ε * √(k : ℝ) * frobNorm (A - truncatedSVD A k) := by ring
    _ ≤ _ := hω'.le

/-- The tail–tail multiplication error of a CountSketch:
$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}} \le \varepsilon\|\mathbf{E}\|_{\mathsf{F}}^2$
except with probability $2/(\ell\varepsilon^2)$. -/
private theorem measureReal_frobNorm_tail_tail_gt_le_of_hasLaw_countSketch
    (hX : HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ) (A : Matrix m n 𝕜) (k : ℕ) {ε : ℝ}
    (hε : 0 < ε) :
    μ.real {ω | ε * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
        (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)} ≤ 2 / (Fintype.card l * ε ^ 2) := by
  classical
  have : IsFiniteMeasure μ := hX.isFiniteMeasure_iff.2 inferInstance
  have h2 : (0 : ℝ) ≤ 2 / (Fintype.card l * ε ^ 2) := by positivity
  by_cases h0 : A - truncatedSVD A k = 0
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) h2
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : ε * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
          (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ) := hω
    simp [h0] at hω'
  have h0' : (A - truncatedSVD A k)ᴴ ≠ 0 := by rwa [Ne, Matrix.conjTranspose_eq_zero]
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch hX hε h0' h0')
  have hω' : ε * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm ((A - truncatedSVD A k) * X ω * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
        (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ) := hω
  change ε * frobNorm (A - truncatedSVD A k)ᴴ * frobNorm (A - truncatedSVD A k)ᴴ ≤
    frobNorm ((A - truncatedSVD A k)ᴴᴴ * ((X ω)ᴴ)ᴴ * (X ω)ᴴ * (A - truncatedSVD A k)ᴴ -
      (A - truncatedSVD A k)ᴴᴴ * (A - truncatedSVD A k)ᴴ)
  rw [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_conjTranspose,
    frobNorm_conjTranspose, mul_assoc, ← sq]
  exact hω'.le

/-- **The randomized SVD with a CountSketch test matrix, relative error**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ is a CountSketch, $\varepsilon, \delta > 0$, $\ell$ is at
least <!-- value countSketchEmbeddingDim k (1/2) (\delta/2) -->
$(k^2 + k)/((\delta/2)(1/2)^2)$ (`countSketchEmbeddingDim k (1 / 2) (δ / 2)`) and
$\ell \ge 16k/(\varepsilon\delta)$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$, over any `RCLike` field. The route: the OSI at constant $1/2$
and failure $\delta/2$, the tail–head multiplication tail at accuracy $\sqrt{\varepsilon/(4k)}$ and
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le`. Asymptotic
form: `NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch`.
[Woodruff2014, Remark 46]; there $O(k^2 + k/\varepsilon)$ rows at constant probability, real.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch (A : Matrix m n 𝕜)
    (hX : HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hδ : 0 < δ) (hl : countSketchEmbeddingDim k (1 / 2) (δ / 2) ≤ Fintype.card l)
    (hl' : 16 * (k : ℝ) ≤ ε * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  classical
  have : IsFiniteMeasure μ := hX.isFiniteMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2 := hω
    rw [truncatedSVD_zero, sub_zero, sub_rsvd] at hω'
    have h := frobNorm_one_sub_rangeProjector_mul_le (A * X ω) A
    nlinarith [sq_nonneg (frobNorm A), frobNorm_nonneg ((1 - rangeProjector (A * X ω)) * A)]
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hl0 : (0 : ℝ) < Fintype.card l := by
    refine lt_of_lt_of_le ?_ hl
    rw [countSketchEmbeddingDim_def]
    positivity
  have : Nonempty l := Fintype.card_pos_iff.1 (by exact_mod_cast hl0)
  have hεJ : 0 < √(ε / (4 * k)) := Real.sqrt_pos.2 (by positivity)
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le hX k
    (by norm_num) (half_pos hδ) hl
  have h := (hOSI.hasSubspaceInjection (U := (truncatedSVD A k)ᴴ)
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)
    ).measureReal_frobNorm_sub_truncatedSVD_rsvd_sq_gt_add_le (by norm_num)
    (measureReal_frobNorm_tail_head_gt_le_of_hasLaw_countSketch hX A k hεJ)
  have hsq : √(ε / (4 * k)) ^ 2 = ε / (4 * k) := Real.sq_sqrt (by positivity)
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans ?_)
  · have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2 := hω
    have h1 := frobNorm_sub_truncatedSVD_rsvd_sq A (X ω) k
    have h2 := sq_nonneg (frobNorm (rsvd A (X ω) - truncatedSVD (rsvd A (X ω)) k))
    have e : frobNorm (A - truncatedSVD A k) ^ 2 +
        (√(ε / (4 * k)) * √(k : ℝ) * frobNorm (A - truncatedSVD A k)) ^ 2 / (1 - 1 / 2) ^ 2 =
          (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
      rw [mul_pow, mul_pow, hsq, Real.sq_sqrt hk'.le]
      field_simp
      ring
    change _ < frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2
    rw [e]
    linarith
  · rw [hsq]
    have e : 2 / (Fintype.card l * (ε / (4 * k))) = 8 * k / (Fintype.card l * ε) := by
      field_simp
      ring
    have h3 : 8 * (k : ℝ) / (Fintype.card l * ε) ≤ δ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [e]
    linarith

/-- **$O((k^2 + k/\varepsilon)/\delta)$ CountSketch columns suffice for the randomized SVD**:
there are absolute constants $C, \varepsilon_0 > 0$ such that if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ of an $n \times \ell$ test matrix $\mathbf{\Omega}$ is a
CountSketch, $0 < \varepsilon \le \varepsilon_0$, $\delta > 0$ and
$\ell \ge C(k^2 + k + k/\varepsilon)/\delta$, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$, over any `RCLike` field. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch`, proved from it with
$C = 16$ and $\varepsilon_0 = 1$. [Woodruff2014, Remark 46]; there $O(k^2 + k/\varepsilon)$ rows of
a sparse embedding matrix at constant failure probability, real.
Asymptotic: NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n l : Type} [MeasurableSpace Ω] [RCLike 𝕜]
      [Fintype m] [Fintype n] [Fintype l] [DecidableEq l] (μ : Measure Ω) (A : Matrix m n 𝕜)
      (X : Ω → Matrix n l 𝕜) (k : ℕ) (ε δ : ℝ),
      HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
      C * ((((k : ℝ) ^ 2 + k) + k / ε) / δ) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  refine ⟨16, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 m n l _ _ _ _ _ _ μ A X k ε δ hX hε _ hδ hl
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkε : (k : ℝ) / ε * ε = k := div_mul_cancel₀ _ hε.ne'
  have hl' := hl
  rw [mul_div_assoc', div_le_iff₀ hδ] at hl'
  refine measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_countSketch A hX hε hδ
    ((countSketchEmbeddingDim_le k (1 / 2) (δ / 2)).trans (le_trans ?_ hl)) ?_
  · rw [show ((k : ℝ) ^ 2 + k) / (δ / 2 * (1 / 2) ^ 2) = 8 * (((k : ℝ) ^ 2 + k) / δ) by
      field_simp; ring]
    have : 0 ≤ (k : ℝ) / ε := by positivity
    have h1 : ((k : ℝ) ^ 2 + k) / δ ≤ (((k : ℝ) ^ 2 + k) + k / ε) / δ :=
      div_le_div_of_nonneg_right (by linarith) hδ.le
    have h2 : 0 ≤ ((k : ℝ) ^ 2 + k) / δ := by positivity
    linarith
  · have : 0 ≤ (k : ℝ) / ε := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hl' hε.le, sq_nonneg (k : ℝ)]

/-- **Early-truncated randomized SVD with a CountSketch test matrix, tail**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ is a CountSketch, $0 < \varepsilon \le 1$, $\delta > 0$, $\ell$ is at
least <!-- value countSketchEmbeddingDim k (\varepsilon/6) (\delta/3) -->
$(k^2 + k)/((\delta/3)(\varepsilon/6)^2)$ (`countSketchEmbeddingDim k (ε / 6) (δ / 3)`) and
$\ell \ge 216k/(\varepsilon^2\delta)$, then
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$, over any `RCLike` field. The route: the OSI at constant
$1 - \varepsilon/6$ and failure $\delta/3$, the two multiplication tails of the CountSketch at
accuracy $\varepsilon/(6\sqrt{k})$, and
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le`. Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch`.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for sparse sketches with
unspecified constants, real.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch
    (A : Matrix m n 𝕜) (hX : HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ) {k : ℕ} {ε δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hl : countSketchEmbeddingDim k (ε / 6) (δ / 3) ≤ Fintype.card l)
    (hl' : 216 * (k : ℝ) ≤ ε ^ 2 * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  classical
  have : IsFiniteMeasure μ := hX.isFiniteMeasure_iff.2 inferInstance
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ.le
    refine measure_mono_null (fun ω hω => ?_) measure_empty
    have hω' : (1 + ε) * frobNorm (A - truncatedSVD A 0) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) 0) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul] at hω'
    nlinarith [sq_nonneg (frobNorm A)]
  have hl0 : (0 : ℝ) < Fintype.card l := by
    refine lt_of_lt_of_le ?_ hl
    rw [countSketchEmbeddingDim_def]
    positivity
  have : Nonempty l := Fintype.card_pos_iff.1 (by exact_mod_cast hl0)
  have hk0 : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  have hεJ : 0 < ε / (6 * √(k : ℝ)) := by positivity
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchEmbeddingDim_le hX k
    (by positivity) (by positivity) hl
  have hχ := measureReal_frobNorm_tail_head_gt_le_of_hasLaw_countSketch hX A k hεJ
  rw [show ε / (6 * √(k : ℝ)) * √(k : ℝ) = ε / 6 by field_simp] at hχ
  have h := (hOSI.hasSubspaceInjection (U := (truncatedSVD A k)ᴴ)
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)
    ).measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le hε hε1
    (P := fun ω => rangeProjector (truncatedSVD (A * X ω) k))
    (fun ω => isStarProjection_rangeProjector _)
    (fun ω => (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k))
    (fun ω => by
      rw [rangeProjector_truncatedSVD_mul, Matrix.sub_mul]
      exact frobNorm_sub_truncatedSVD_le_of_rank_le (A * X ω)
        ((Matrix.rank_mul_le_left _ _).trans (rank_truncatedSVD_le A k)))
    (measureReal_frobNorm_tail_tail_gt_le_of_hasLaw_countSketch hX A k hεJ) hχ
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans ?_)
  · have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, Matrix.sub_mul, Matrix.one_mul] at hω'
    exact hω'
  · have e : 2 / (Fintype.card l * (ε / (6 * √(k : ℝ))) ^ 2) =
        72 * k / (Fintype.card l * ε ^ 2) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      field_simp
      ring
    have h3 : 72 * (k : ℝ) / (Fintype.card l * ε ^ 2) ≤ δ / 3 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [e]
    linarith

/-- **$O(k^2/(\varepsilon^2\delta))$ CountSketch columns suffice for early truncation**: there are
absolute constants $C, \varepsilon_0 > 0$ such that if the sketch $\mathbf{\Omega}^{\mathsf{H}}$
of an $n \times \ell$ test matrix $\mathbf{\Omega}$ is a CountSketch,
$0 < \varepsilon \le \varepsilon_0$, $\delta > 0$ and $\ell \ge C(k^2 + k)/(\varepsilon^2\delta)$,
then
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$, over any `RCLike` field. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch`, proved from
it with $C = 216$ and $\varepsilon_0 = 1$. [CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3];
there $\mathbf{A}\mathbf{\Omega}$ is a projection-cost-preserving sketch with error
$O(\varepsilon)$ for the fully sparse embedding of Lemma 11 (family 2) with
$O(k^2/(\varepsilon^2\delta))$ rows, and Lemma 3 carries the sketch's best rank-$k$ projection
over to $\mathbf{A}$; real.
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch
Result: etrsvd -/
theorem exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n l : Type} [MeasurableSpace Ω] [RCLike 𝕜]
      [Fintype m] [Fintype n] [Fintype l] [DecidableEq l] (μ : Measure Ω) (A : Matrix m n 𝕜)
      (X : Ω → Matrix n l 𝕜) (k : ℕ) (ε δ : ℝ),
      HasLaw (fun ω => (X ω)ᴴ) (countSketch l n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
      C * (((k : ℝ) ^ 2 + k) / (ε ^ 2 * δ)) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  refine ⟨216, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 m n l _ _ _ _ _ _ μ A X k ε δ hX hε hε1 hδ hl
  have hl' := hl
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hl'
  refine measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_countSketch A hX hε hε1 hδ
    ((countSketchEmbeddingDim_le k (ε / 6) (δ / 3)).trans (le_trans ?_ hl)) ?_
  · rw [show ((k : ℝ) ^ 2 + k) / (δ / 3 * (ε / 6) ^ 2) = 108 * (((k : ℝ) ^ 2 + k) / (ε ^ 2 * δ)) by
      field_simp; ring]
    have : 0 ≤ ((k : ℝ) ^ 2 + k) / (ε ^ 2 * δ) := by positivity
    linarith
  · nlinarith [sq_nonneg (k : ℝ)]

end NLAlib
