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
probability $1 - \delta$ at $\ell = O((k/\delta + \log(1/\delta))/\varepsilon^2)$. The family's
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
  explicit tail, and its asymptotic form
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
least <!-- value gaussianInjectionDim k (\varepsilon/8) (\delta/3) -->
$\ell \ge 4 (\sqrt{k} + \sqrt{2 \log(1/(\delta/3))})^2/(\varepsilon/8)^2$ and
$\ell \ge 384k/(\varepsilon^2\delta)$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the first size is `gaussianInjectionDim k (ε / 8) (δ / 3)`.
The route: the OSI at constant $1 - \varepsilon/8$ and failure $\delta/3$, the JL moment property
at $\varepsilon/(8\sqrt{k})$ for the two multiplication tails, and
`NLAlib.HasSubspaceInjection.measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le`. Its expectation
twin, at $\ell \ge 900k/\varepsilon^2$, is
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`; a
tail from that by Markov's inequality needs $\ell$ of order $k/(\varepsilon\delta)^2$.
Asymptotic form:
`exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`.
[CohenElderMuscoMuscoPersu2015, §7.2]; there with unspecified constants.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ) (hl : gaussianInjectionDim k (ε / 8) (δ / 3) ≤ Fintype.card l)
    (hl' : 384 * (k : ℝ) ≤ ε ^ 2 * δ * Fintype.card l) :
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
    exact_mod_cast (gaussianInjectionDim_pos k (by positivity : ε / 8 ≠ 0) (by positivity)
      (by linarith : δ / 3 < 1)).trans_le hl
  have : Nonempty l := Fintype.card_pos_iff.1 hl0
  have hS : (fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) =
      fun ω => ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ := by
    funext ω
    rw [Matrix.conjTranspose_smul, star_trivial]
  have hk0 : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  have hεJ : 0 < ε / (8 * √(k : ℝ)) := by positivity
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix_of_gaussianInjectionDim_le
    (d := k) hG (by positivity) (by linarith) (by positivity) (by linarith) hl
  have hJL := hasJLMoment_of_hasLaw_gaussianMatrix hG hεJ
  rw [hS] at hOSI hJL
  have hX' : AEMeasurable (fun ω => (√(Fintype.card l : ℝ))⁻¹ • X ω) μ :=
    (continuous_const_smul _).measurable.comp_aemeasurable hX.aemeasurable
  have hδJ : (0 : ℝ) ≤ 2 / (Fintype.card l * (ε / (8 * √(k : ℝ))) ^ 2) := by positivity
  have hχ :=
    hJL.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_rangeProjector_gt_le
    (A := A) (k := k) hX' hεJ le_rfl hδJ
  rw [show ε / (8 * √(k : ℝ)) * √(k : ℝ) = ε / 8 by field_simp] at hχ
  have h := (hOSI.hasSubspaceInjection (U := (truncatedSVD A k)ᴴ)
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)
    ).measureReal_frobNorm_sub_mul_sq_gt_one_add_mul_le hε hε1
    (P := fun ω => rangeProjector (truncatedSVD (A * X ω) k))
    (fun ω => isStarProjection_rangeProjector _)
    (fun ω => (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k))
    (fun ω => by
      rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_smul, ← smul_sub, frobNorm_smul,
        frobNorm_smul, rangeProjector_truncatedSVD_mul, Matrix.sub_mul]
      exact mul_le_mul_of_nonneg_left (frobNorm_sub_truncatedSVD_le_of_rank_le (A * X ω)
        ((Matrix.rank_mul_le_left _ _).trans (rank_truncatedSVD_le A k))) (norm_nonneg _))
    (hJL.measureReal_frobNorm_sub_truncatedSVD_mul_mul_conjTranspose_mul_conjTranspose_sub_gt_le hX'
      hεJ le_rfl hδJ) hχ
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans ?_)
  · have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 := hω
    rw [sub_earlyTruncatedRSVD, Matrix.sub_mul, Matrix.one_mul] at hω'
    exact hω'
  · have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 hl0
    have e : 2 / (Fintype.card l * (ε / (8 * √(k : ℝ))) ^ 2) =
        128 * k / (Fintype.card l * ε ^ 2) := by
      rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      field_simp
      ring
    have h3 : 128 * (k : ℝ) / (Fintype.card l * ε ^ 2) ≤ δ / 3 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [e]
    linarith

/-- **$O((k/\delta + \log(1/\delta))/\varepsilon^2)$ Gaussian columns suffice for early
truncation**: there are absolute constants $C, \varepsilon_0 > 0$ such that for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{\Omega}$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell \ge C(k/\delta + \log(1/\delta))/\varepsilon^2$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$. The asymptotic form of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`, proved
from it with $C = 3072$ and $\varepsilon_0 = 1$.
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix
Result: etrsvd -/
theorem
    exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε δ : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (((k : ℝ) / δ + Real.log (1 / δ)) / ε ^ 2) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  refine ⟨3072, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ μ A X k ε δ hX hε hε1 hδ hδ2 hl
  have hL1 : 0 ≤ Real.log (1 / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; linarith)
  have hkδ : (k : ℝ) ≤ k / δ := le_div_self (Nat.cast_nonneg k) hδ (by linarith)
  have hl' := hl
  rw [mul_div_assoc', div_le_iff₀ (by positivity)] at hl'
  refine measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix A hX hε hε1
    hδ ((gaussianInjectionDim_le k (ε / 8) (by positivity) (by linarith)).trans ?_) ?_
  · have hlog : Real.log (1 / (δ / 3)) ≤ 3 * Real.log (1 / δ) := by
      rw [show (3 : ℝ) * Real.log (1 / δ) = Real.log ((1 / δ) ^ 3) by
        rw [Real.log_pow]; norm_num]
      refine Real.log_le_log (by positivity) ?_
      rw [div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [pow_pos hδ 2, pow_pos hδ 3]
    rw [div_le_iff₀ (by positivity)]
    have e : (Fintype.card l : ℝ) * (ε / 8) ^ 2 = Fintype.card l * ε ^ 2 / 64 := by ring
    rw [e]
    nlinarith
  · have e : (k : ℝ) / δ * δ = k := div_mul_cancel₀ _ hδ.ne'
    nlinarith [mul_le_mul_of_nonneg_left hl' hδ.le, mul_nonneg hδ.le hL1]

end NLAlib
