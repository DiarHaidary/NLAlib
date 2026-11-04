/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Random.RangeFinder

/-!
# Nyström with any random test matrix

Facts about the Nyström approximation $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$
(`NLAlib.nystrom`) of a positive semidefinite $\mathbf{H}$ that hold for every random test matrix
$\mathbf{X}$, whatever its law, over any `RCLike` field: the integrability companions of the
Nyström expectations, and the reduction of a spectral bound for truncated Nyström to a trace bound.

**The Gram correspondence.** Every proof here and in the Gaussian and rotation-invariant Nyström
files writes $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ for some factor $\mathbf{F}$
(`CStarAlgebra.nonneg_iff_eq_star_mul_self`) and moves the statement to the randomized SVD of
$\mathbf{F}$ by choice-free identities:
$\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})$ is the Gram matrix of
$\mathbf{F} - \mathsf{rsvd}(\mathbf{F}, \mathbf{X})$ (`NLAlib.conjTranspose_mul_self_sub_nystrom`),
and the trace error of `truncatedSVD (nystrom H (X ω)) k` is the squared Frobenius error of
`truncatedSVD (rsvd F (X ω)) k`
(`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`). No square root appears.

**Integrability.** Every error of Nyström is a measurable function of the test matrix and is
bounded, so it is integrable for every measurable test matrix and every finite measure. The trace
error of truncated Nyström is integrable too: it does not depend on the choice the truncation
makes, which is what makes it measurable.

**Measurability of the truncated output.** The spectral error of truncated Nyström depends on the
choice `truncatedSVD` makes. Statements about it are stated for any measurable choice
$\mathbf{Y}$ of best approximations, `hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)` with
`hYm : AEStronglyMeasurable Y μ`, and each has its direct form at `truncatedSVD`, which is Borel
measurable (`NLAlib.measurable_truncatedSVD`), with
`hYm := ((measurable_truncatedSVD k).comp_aemeasurable
((measurable_nystrom H).comp_aemeasurable hX)).aestronglyMeasurable`.


## Main results

* `NLAlib.SymmetricGauge.integrable_matrixNorm_sub_nystrom`,
  `Matrix.PosSemidef.integrable_schattenNorm_sub_nystrom`,
  `Matrix.PosSemidef.integrable_nuclearNorm_sub_nystrom`,
  `Matrix.PosSemidef.integrable_frobNorm_sub_nystrom`,
  `Matrix.PosSemidef.integrable_specNorm_sub_nystrom`: integrability of the error.
* `Matrix.PosSemidef.integrable_nuclearNorm_sub_truncatedSVD_nystrom`: truncated Nyström, trace.
* `Matrix.PosSemidef.integrable_specNorm_sub_of_isBestRankApprox_nystrom`: truncated Nyström,
  spectral, for a measurable selector;
  `Matrix.PosSemidef.integrable_specNorm_sub_truncatedSVD_nystrom`, its direct form.
* reverse Eckart–Young in expectation, for a measurable selector, in the `Matrix.PosSemidef`
  namespace:
  `integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom`, and its
  direct form
  `integral_specNorm_sub_truncatedSVD_nystrom_add_nuclearNorm_sub_truncatedSVD_le`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {n l : Type*} [Fintype n] [Fintype l] {H : Matrix n n 𝕜} {X : Ω → Matrix n l 𝕜}

/-! ### Integrability of the error -/

/-- The Nyström error of a positive semidefinite $\mathbf{H}$ is integrable in every unitarily
invariant norm, for every measurable test matrix $\mathbf{X}$ and finite measure:
$\omega \mapsto \|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi}$ is measurable and
bounded by $\|\mathbf{H}\|_{\Phi}$. With $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ it is the
Gram-form integrand of the randomized SVD of $\mathbf{F}$
(`NLAlib.SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd`). -/
theorem SymmetricGauge.integrable_matrixNorm_sub_nystrom (Φ : SymmetricGauge) [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm (H - nystrom H (X ω))) μ := by
  classical
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom]
  exact Φ.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd F hX

/-- The Schatten $q$-norm of the Nyström error, $q \ge 1$,
$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{S_q}$, is integrable for positive
semidefinite $\mathbf{H}$, every measurable test matrix $\mathbf{X}$ and finite measure. -/
theorem _root_.Matrix.PosSemidef.integrable_schattenNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) {q : ℝ≥0∞} (hq : 1 ≤ q) (hX : AEMeasurable X μ) :
    Integrable (fun ω => schattenNorm q (H - nystrom H (X ω))) μ := by
  have := Fact.mk hq
  simpa only [lpGauge_matrixNorm] using (lpGauge q).integrable_matrixNorm_sub_nystrom hH hX

/-- The trace error of Nyström,
$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_*$, is integrable for positive
semidefinite $\mathbf{H}$, every measurable test matrix $\mathbf{X}$ and finite measure. -/
theorem _root_.Matrix.PosSemidef.integrable_nuclearNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => nuclearNorm (H - nystrom H (X ω))) μ := by
  simpa only [lpGauge_one_matrixNorm] using
    (lpGauge 1).integrable_matrixNorm_sub_nystrom hH hX

/-- The Frobenius error of Nyström,
$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\mathsf{F}}$, is integrable for
positive semidefinite $\mathbf{H}$, every measurable test matrix $\mathbf{X}$ and finite
measure. -/
theorem _root_.Matrix.PosSemidef.integrable_frobNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => frobNorm (H - nystrom H (X ω))) μ := by
  simpa only [lpGauge_two_matrixNorm] using
    (lpGauge 2).integrable_matrixNorm_sub_nystrom hH hX

/-- The spectral error of Nyström,
$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_2$, is integrable for positive
semidefinite $\mathbf{H}$, every measurable test matrix $\mathbf{X}$ and finite measure. -/
theorem _root_.Matrix.PosSemidef.integrable_specNorm_sub_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) :
    Integrable (fun ω => specNorm (H - nystrom H (X ω))) μ := by
  simpa only [lpGauge_top_matrixNorm] using
    (lpGauge ⊤).integrable_matrixNorm_sub_nystrom hH hX

/-! ### Truncated Nyström -/

/-- The trace error of truncated Nyström,
$\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*$, is
integrable for positive semidefinite $\mathbf{H}$, every measurable test matrix $\mathbf{X}$ and
finite measure. It does not depend on the choice made by `truncatedSVD`
(`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`), which is what makes it
measurable: with $\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ it is the squared Frobenius
error of the truncated randomized SVD of $\mathbf{F}$
(`NLAlib.integrable_frobNorm_sub_truncatedSVD_rsvd_sq`). -/
theorem _root_.Matrix.PosSemidef.integrable_nuclearNorm_sub_truncatedSVD_nystrom
    [IsFiniteMeasure μ] (hH : H.PosSemidef) (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k)) μ := by
  classical
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom]
  exact integrable_frobNorm_sub_truncatedSVD_rsvd_sq F hX k

/-- For positive semidefinite $\mathbf{H}$ and a measurable choice $\mathbf{Y}$ of best rank-$k$
approximations of $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$, the spectral error
$\|\mathbf{H} - \mathbf{Y}\|_2$ is integrable for every finite measure; it is bounded by
$\|\mathbf{H}\|_*$. No measurability of $\mathbf{X}$ is needed.
Direct form at `truncatedSVD`:
`Matrix.PosSemidef.integrable_specNorm_sub_truncatedSVD_nystrom`. -/
theorem _root_.Matrix.PosSemidef.integrable_specNorm_sub_of_isBestRankApprox_nystrom
    [IsFiniteMeasure μ] (hH : H.PosSemidef) {k : ℕ} {Y : Ω → Matrix n n 𝕜}
    (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω)) (hYm : AEStronglyMeasurable Y μ) :
    Integrable (fun ω => specNorm (H - Y ω)) μ := by
  have hm : AEStronglyMeasurable (fun ω => specNorm (H - Y ω)) μ :=
    (continuous_specNorm.comp (continuous_const.sub continuous_id)).comp_aestronglyMeasurable hYm
  refine Integrable.of_bound hm (nuclearNorm H) (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (specNorm_nonneg _)]
  have hT := Matrix.le_iff.mp (hH.truncatedSVD_nystrom_le (X ω) k)
  have h0 : 0 ≤ RCLike.re (truncatedSVD (nystrom H (X ω)) k).trace := by
    rw [← ((hH.nystrom (X ω)).truncatedSVD k).nuclearNorm_eq_re_trace]
    exact nuclearNorm_nonneg _
  calc specNorm (H - Y ω) ≤ nuclearNorm (H - Y ω) := specNorm_le_nuclearNorm _
    _ ≤ nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) :=
      hH.nuclearNorm_sub_le_nuclearNorm_sub_truncatedSVD_nystrom_of_isBestRankApprox (hY ω)
    _ ≤ nuclearNorm H := by
      rw [hT.nuclearNorm_eq_re_trace, hH.nuclearNorm_eq_re_trace, Matrix.trace_sub, map_sub]
      linarith

/-- For positive semidefinite $\mathbf{H}$, a measurable test matrix $\mathbf{X}$ and every
finite measure, the spectral error of truncated Nyström,
$\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_2$, is
integrable. The direct form of
`Matrix.PosSemidef.integrable_specNorm_sub_of_isBestRankApprox_nystrom`. -/
theorem _root_.Matrix.PosSemidef.integrable_specNorm_sub_truncatedSVD_nystrom [IsFiniteMeasure μ]
    (hH : H.PosSemidef) (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => specNorm (H - truncatedSVD (nystrom H (X ω)) k)) μ :=
  hH.integrable_specNorm_sub_of_isBestRankApprox_nystrom
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_nystrom H).comp_aemeasurable hX)).aestronglyMeasurable

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Reverse Eckart–Young for truncated Nyström, in expectation**: for positive semidefinite
$\mathbf{H}$, every measurable test matrix $\mathbf{X}$ and a measurable choice $\mathbf{Y}$ of
best rank-$k$ approximations of $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$,
$$\mathbb{E}\|\mathbf{H} - \mathbf{Y}\|_2 + \|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*
\le \sigma_k(\mathbf{H}) + \mathbb{E}\|\mathbf{H} -
\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*\,,$$
for every law: a trace bound for truncated Nyström becomes a spectral one at no cost, for every
choice of the truncation.
Direct form at `truncatedSVD`:
`Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_add_nuclearNorm_sub_truncatedSVD_le`.
[TroppYurtseverUdellCevher2017a, Proposition A.8 and App. A.6]; [Gu2015, Theorem 3.4]; there a
deterministic step inside a Gaussian proof, here in expectation for every law, under a selector,
subtraction-free, indices from $0$.
Result: reverse-eckart-young -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom
    [IsProbabilityMeasure μ] (hH : H.PosSemidef) (hX : AEMeasurable X μ) {k : ℕ}
    {Y : Ω → Matrix n n 𝕜} (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (H - Y ω) ∂μ + nuclearNorm (H - truncatedSVD H k) ≤
      singularValues H k + ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ := by
  have hpt : ∀ ω, specNorm (H - Y ω) ≤
      (singularValues H k - nuclearNorm (H - truncatedSVD H k)) +
        nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) := by
    intro ω
    have h1 := specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le H (hY ω).rank_le
    have h2 := hH.nuclearNorm_sub_le_nuclearNorm_sub_truncatedSVD_nystrom_of_isBestRankApprox (hY ω)
    linarith
  have hF := hH.integrable_nuclearNorm_sub_truncatedSVD_nystrom hX k
  have hI : Integrable (fun ω => (singularValues H k - nuclearNorm (H - truncatedSVD H k)) +
      nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k)) μ := (integrable_const _).add hF
  have hle := integral_mono (hH.integrable_specNorm_sub_of_isBestRankApprox_nystrom hY hYm) hI hpt
  rw [integral_add (integrable_const _) hF, integral_const, probReal_univ, one_smul] at hle
  linarith

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Reverse Eckart–Young for truncated Nyström, in expectation**, direct form: for positive
semidefinite $\mathbf{H}$ and every measurable test matrix $\mathbf{X}$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_2 +
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_* \le \sigma_k(\mathbf{H}) +
\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*\,,$$
for every law. The direct form of
`Matrix.PosSemidef.integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom`.
[TroppYurtseverUdellCevher2017a, Proposition A.8 and App. A.6]; [Gu2015, Theorem 3.4]; there a
deterministic step inside a Gaussian proof, here in expectation for every law, subtraction-free,
indices from $0$.
Result: reverse-eckart-young -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_add_nuclearNorm_sub_truncatedSVD_le
    [IsProbabilityMeasure μ] (hH : H.PosSemidef) (hX : AEMeasurable X μ) (k : ℕ) :
    ∫ ω, specNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ + nuclearNorm (H - truncatedSVD H k) ≤
      singularValues H k + ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ :=
  hH.integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom hX
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    ((measurable_truncatedSVD k).comp_aemeasurable
      ((measurable_nystrom H).comp_aemeasurable hX)).aestronglyMeasurable

end NLAlib
