/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import NLAlib.LowRank.Structural.Truncation
public import NLAlib.Probability.Measurability.Matrix

/-!
# The randomized SVD with any random test matrix

Facts about the randomized SVD $\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}$ (`NLAlib.rsvd`) that
hold for every random test matrix $\mathbf{X}$, whatever its law, over any `RCLike` field. They are
the integrability companions of the expectation bounds of the Gaussian, rotation-invariant and
oblivious range finders, and the reduction of a spectral bound for the truncated output to a
Frobenius one.

**Integrability.** Every error of the randomized SVD is a measurable function of the test matrix
and is bounded by the same quantity for $\mathbf{A}$, so it is integrable for every measurable
test matrix and every finite measure. The squared Frobenius error of the late-truncated output
`truncatedSVD (rsvd A (X ω)) k` is integrable too: it does not depend on the choice the truncation
makes (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`), which is what makes it measurable.

**Measurability of the truncated output.** `truncatedSVD` is a choice, so
`fun ω => truncatedSVD (rsvd A (X ω)) k` is not known to be measurable, and its spectral error
depends on the choice. Statements about such errors take a measurable choice $\mathbf{Y}$ of best
approximations, `hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω)` with
`hYm : AEStronglyMeasurable Y μ`. No such selector can be exhibited yet: neither the library nor
Mathlib has a measurable-selection theorem, and the measurability of `truncatedSVD` is unknown.
These statements are the form a measurable selector will instantiate.

Design: `docs/design/LowRank-S3.md` §3.1, §8 items 6 and 8.

## Main results

* `NLAlib.SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd`,
  `NLAlib.SymmetricGauge.integrable_matrixNorm_sub_rsvd`,
  `NLAlib.integrable_schattenNorm_sub_rsvd_sq`,
  `NLAlib.integrable_frobNorm_sub_rsvd_sq`, `NLAlib.integrable_frobNorm_sub_rsvd`,
  `NLAlib.integrable_specNorm_sub_rsvd_sq`, `NLAlib.integrable_specNorm_sub_rsvd`: integrability of
  the error for any measurable test matrix.
* `NLAlib.integrable_frobNorm_sub_truncatedSVD_rsvd_sq`: the late-truncated output, Frobenius.
* `NLAlib.integrable_specNorm_sub_sq_of_isBestRankApprox`: the truncated output, spectral, for a
  measurable selector.
* `NLAlib.integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox`:
  reverse Eckart–Young in expectation, for a measurable selector.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] {X : Ω → Matrix n l 𝕜}

/-! ### Measurability and boundedness -/

/-- The error of the randomized SVD is a measurable function of the test matrix. -/
private theorem measurable_sub_rsvd (A : Matrix m n 𝕜) :
    Measurable fun Ω : Matrix n l 𝕜 => A - rsvd A Ω :=
  measurable_const.matrix_sub (measurable_rsvd A)

/-- A bounded measurable function of a measurable random matrix is integrable. -/
private theorem integrable_comp_of_abs_le {p q : Type*} [IsFiniteMeasure μ]
    {Z : Ω → Matrix p q 𝕜} (hZ : AEMeasurable Z μ) {g : Matrix p q 𝕜 → ℝ} (hg : Measurable g)
    (C : ℝ) (hC : ∀ M, |g M| ≤ C) : Integrable (fun ω => g (Z ω)) μ :=
  Integrable.of_bound (hg.comp_aemeasurable hZ).aestronglyMeasurable C
    (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact hC (Z ω))

/-- Every unitarily invariant norm of the error of the randomized SVD is at most that of
$\mathbf{A}$. -/
private theorem matrixNorm_sub_rsvd_le (Φ : SymmetricGauge) (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) : Φ.matrixNorm (A - rsvd A Ω) ≤ Φ.matrixNorm A :=
  Φ.matrixNorm_le_of_singularValues_le (singularValues_sub_rsvd_le A Ω)

/-! ### Integrability of the error -/

/-- The Gram matrix of the error of the randomized SVD is integrable in every unitarily invariant
norm, for every measurable test matrix $\mathbf{X}$ and finite measure: $\omega \mapsto
\|(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A})^{\mathsf{H}}(\mathbf{A} -
\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A})\|_{\Phi}$ is measurable and bounded by
$\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\Phi}$. The companion of the Gram-form expectations. -/
theorem SymmetricGauge.integrable_matrixNorm_conjTranspose_mul_self_sub_rsvd (Φ : SymmetricGauge)
    [IsFiniteMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))) μ := by
  refine integrable_comp_of_abs_le hX
    (g := fun Ω => Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω)))
    (Φ.measurable_matrixNorm.comp
      ((Measurable.matrix_conjTranspose continuous_star.measurable
        (measurable_sub_rsvd A)).matrix_mul (measurable_sub_rsvd A)))
    (Φ.matrixNorm (Aᴴ * A)) fun Ω => ?_
  rw [abs_of_nonneg (Φ.matrixNorm_nonneg _)]
  refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
  rw [singularValues_conjTranspose_mul_self, singularValues_conjTranspose_mul_self]
  exact pow_le_pow_left₀ (singularValues_nonneg _ _) (singularValues_sub_rsvd_le A Ω i) 2

/-- The error of the randomized SVD is integrable in every unitarily invariant norm, for every
measurable test matrix $\mathbf{X}$ and finite measure: $\omega \mapsto \|\mathbf{A} -
\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{\Phi}$ is measurable and bounded by
$\|\mathbf{A}\|_{\Phi}$. -/
theorem SymmetricGauge.integrable_matrixNorm_sub_rsvd (Φ : SymmetricGauge) [IsFiniteMeasure μ]
    (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => Φ.matrixNorm (A - rsvd A (X ω))) μ :=
  integrable_comp_of_abs_le hX (g := fun Ω => Φ.matrixNorm (A - rsvd A Ω))
    (Φ.measurable_matrixNorm.comp (measurable_sub_rsvd A)) (Φ.matrixNorm A) fun Ω => by
      rw [abs_of_nonneg (Φ.matrixNorm_nonneg _)]
      exact matrixNorm_sub_rsvd_le Φ A Ω

/-- The squared Schatten $q$-norm of the error of the randomized SVD, $q \ge 1$, is integrable for
every measurable test matrix $\mathbf{X}$ and finite measure: $\omega \mapsto \|\mathbf{A} -
\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{S_q}^2$ is bounded by
$\|\mathbf{A}\|_{S_q}^2$. -/
theorem integrable_schattenNorm_sub_rsvd_sq [IsFiniteMeasure μ] {q : ℝ≥0∞} (hq : 1 ≤ q)
    (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) :
    Integrable (fun ω => schattenNorm q (A - rsvd A (X ω)) ^ 2) μ := by
  have hg : Measurable fun M : Matrix m n 𝕜 => schattenNorm q M := by
    rw [show (fun M : Matrix m n 𝕜 => schattenNorm q M) = (lpGauge q hq).matrixNorm from
      funext fun M => (lpGauge_matrixNorm hq M).symm]
    exact (lpGauge q hq).measurable_matrixNorm
  refine integrable_comp_of_abs_le hX (g := fun Ω => schattenNorm q (A - rsvd A Ω) ^ 2)
    ((hg.comp (measurable_sub_rsvd A)).pow_const 2) (schattenNorm q A ^ 2) fun Ω => ?_
  rw [abs_of_nonneg (sq_nonneg _)]
  have h := matrixNorm_sub_rsvd_le (lpGauge q hq) A Ω
  rw [lpGauge_matrixNorm, lpGauge_matrixNorm] at h
  exact pow_le_pow_left₀ (schattenNorm_nonneg _ _) h 2

/-- The squared Frobenius error of the randomized SVD,
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{\mathsf{F}}^2$, is integrable for
every measurable test matrix $\mathbf{X}$ and finite measure. -/
theorem integrable_frobNorm_sub_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => frobNorm (A - rsvd A (X ω)) ^ 2) μ := by
  simpa only [schattenNorm_two] using integrable_schattenNorm_sub_rsvd_sq one_le_two A hX

/-- The Frobenius error of the randomized SVD,
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{\mathsf{F}}$, is integrable for every
measurable test matrix $\mathbf{X}$ and finite measure. The companion of the expected Frobenius
error in its printed, unsquared form. -/
theorem integrable_frobNorm_sub_rsvd [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => frobNorm (A - rsvd A (X ω))) μ := by
  simpa only [lpGauge_two_matrixNorm] using
    (lpGauge 2 one_le_two).integrable_matrixNorm_sub_rsvd A hX

/-- The squared spectral error of the randomized SVD,
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_2^2$, is integrable for every
measurable test matrix $\mathbf{X}$ and finite measure. -/
theorem integrable_specNorm_sub_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => specNorm (A - rsvd A (X ω)) ^ 2) μ := by
  simpa only [schattenNorm_top] using integrable_schattenNorm_sub_rsvd_sq le_top A hX

/-- The spectral error of the randomized SVD,
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_2$, is integrable for every measurable
test matrix $\mathbf{X}$ and finite measure. -/
theorem integrable_specNorm_sub_rsvd [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) : Integrable (fun ω => specNorm (A - rsvd A (X ω))) μ := by
  simpa only [lpGauge_top_matrixNorm] using (lpGauge ⊤ le_top).integrable_matrixNorm_sub_rsvd A hX

/-! ### The truncated output -/

/-- The squared Frobenius error of the late-truncated randomized SVD,
$\|\mathbf{A} - \llbracket\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$,
is integrable for every measurable test matrix $\mathbf{X}$ and finite measure. It does not depend
on the choice made by `truncatedSVD` (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`): it is
$\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\|_{\mathsf{F}}^2$ plus the tail sum of
squared singular values of $\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}$, which is what makes it
measurable; it is bounded by
$\|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$.
-/
theorem integrable_frobNorm_sub_truncatedSVD_rsvd_sq [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2) μ := by
  have he : (fun Ω : Matrix n l 𝕜 => frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2) =
      fun Ω => frobNorm (A - rsvd A Ω) ^ 2 + ∑ i ∈ Finset.Ico k (min (Fintype.card m)
        (Fintype.card n)), singularValues (rsvd A Ω) i ^ 2 := by
    funext Ω
    rw [frobNorm_sub_truncatedSVD_rsvd_sq, frobNorm_sub_truncatedSVD_sq]
  have hr : Measurable fun Ω : Matrix n l 𝕜 => rsvd A Ω := measurable_rsvd A
  have hg : Measurable fun Ω : Matrix n l 𝕜 => frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 := by
    rw [he]
    exact ((measurable_frobNorm.comp (measurable_sub_rsvd A)).pow_const 2).add
      (Finset.measurable_sum _ fun i _ => ((measurable_singularValues i).comp hr).pow_const 2)
  refine integrable_comp_of_abs_le hX hg
    (frobNorm A ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2) fun Ω => ?_
  rw [abs_of_nonneg (sq_nonneg _), frobNorm_sub_truncatedSVD_rsvd_sq]
  have h1 := matrixNorm_sub_rsvd_le (lpGauge 2 one_le_two) A Ω
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h1
  have h2 := frobNorm_rsvd_sub_truncatedSVD_le A Ω k
  have h3 := pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
  have h4 := pow_le_pow_left₀ (frobNorm_nonneg _) h2 2
  linarith

/-- For a measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of the randomized SVD,
$\mathbf{Y}(\omega)$ a best approximation of $\mathbf{P}_{\mathbf{A}\mathbf{X}(\omega)}\mathbf{A}$
of rank at most $k$, the squared spectral error $\|\mathbf{A} - \mathbf{Y}\|_2^2$ is integrable for
every finite measure; it is bounded by
$\|\mathbf{A}\|_{\mathsf{F}}^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$.
No measurability of $\mathbf{X}$ is needed.
Not instantiable yet: no measurable selector can be exhibited, since neither the library nor
Mathlib has a measurable-selection theorem and `truncatedSVD (rsvd A (X ω)) k` is not known to be
measurable in $\omega$. This is the form a measurable selector will instantiate. -/
theorem integrable_specNorm_sub_sq_of_isBestRankApprox [IsFiniteMeasure μ] (A : Matrix m n 𝕜)
    {k : ℕ} {Y : Ω → Matrix m n 𝕜} (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) : Integrable (fun ω => specNorm (A - Y ω) ^ 2) μ := by
  have hm : AEStronglyMeasurable (fun ω => specNorm (A - Y ω) ^ 2) μ :=
    ((continuous_specNorm.comp (continuous_const.sub continuous_id)).pow
      2).comp_aestronglyMeasurable hYm
  refine Integrable.of_bound hm (frobNorm A ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2)
    (Filter.Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h1 := matrixNorm_sub_rsvd_le (lpGauge 2 one_le_two) A (X ω)
  rw [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h1
  have h2 : frobNorm (rsvd A (X ω) - Y ω) ≤ frobNorm (A - truncatedSVD A k) :=
    (hY ω).frobNorm_sub.trans_le (frobNorm_rsvd_sub_truncatedSVD_le A (X ω) k)
  have h3 := pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm (A - Y ω)) 2
  rw [(hY ω).frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add] at h3
  have h4 := pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
  have h5 := pow_le_pow_left₀ (frobNorm_nonneg _) h2 2
  linarith

/-- **Reverse Eckart–Young in expectation**: for a measurable test matrix $\mathbf{X}$ and a
measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of
$\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}$,
$$\mathbb{E}\|\mathbf{A} - \mathbf{Y}\|_2^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2 \le \sigma_k(\mathbf{A})^2 + \mathbb{E}\|\mathbf{A} -
\llbracket\mathbf{P}_{\mathbf{A}\mathbf{X}}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every law: a Frobenius bound for the truncated output becomes a spectral one at no cost.
Not instantiable yet: no measurable selector can be exhibited, since neither the library nor
Mathlib has a measurable-selection theorem and `truncatedSVD (rsvd A (X ω)) k` is not known to be
measurable in $\omega$. This is the form a measurable selector will instantiate.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a deterministic remark on truncated outputs, here in expectation
under a selector, subtraction-free, indices from $0$. -/
theorem integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox
    [IsProbabilityMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) {k : ℕ}
    {Y : Ω → Matrix m n 𝕜} (hY : ∀ ω, IsBestRankApprox (rsvd A (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (A - Y ω) ^ 2 ∂μ + frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ := by
  have hpt : ∀ ω, specNorm (A - Y ω) ^ 2 ≤
      (singularValues A k ^ 2 - frobNorm (A - truncatedSVD A k) ^ 2) +
        frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 := by
    intro ω
    have h := (hY ω).specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le
    linarith
  have hF := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX k
  have hI : Integrable (fun ω => (singularValues A k ^ 2 - frobNorm (A - truncatedSVD A k) ^ 2) +
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2) μ := (integrable_const _).add hF
  have hle := integral_mono (integrable_specNorm_sub_sq_of_isBestRankApprox A hY hYm) hI hpt
  rw [integral_add (integrable_const _) hF, integral_const, probReal_univ, one_smul] at hle
  linarith

end NLAlib
