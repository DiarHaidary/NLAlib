/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowRank.Random.RangeFinder
public import NLAlib.Sketching.Gaussian.LeastSquares

/-!
# Early-truncated generalized Nyström with a Haar co-range test matrix

For an $m \times p$ Haar co-range test matrix $\mathbf{\Psi}$ with $p \le m$, independent of the
range test matrix $\mathbf{\Omega}$, early-truncated generalized Nyström
$\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)$
(`NLAlib.earlyTruncatedGeneralizedNystrom`) costs the Haar completion factor at the rank $q \le k$
of the truncated sketch over the early-truncated randomized SVD; at most the factor at
$k$, <!-- value haarProjectionFactor m p k -->
$1 + (m - p)/(m - k) \cdot (k/(p - k - 1))$. The completion step is
`NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame`. Real throughout.

These are the Haar twins of the two composition statements of
`NLAlib.LowRank.Gaussian.EarlyTruncation`, which holds the Gaussian co-range test matrix, the
early-truncated randomized SVD in expectation and the $(1 + \varepsilon)$ forms; any bound on the
early-truncated randomized SVD there combines with the statement here for any law of
$\mathbf{\Omega}$ independent of $\mathbf{\Psi}$.

Design: `docs/design/LowRank-S6.md` §3.6, §8 items 4, 13 and 17.

## Main results

* `NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_haarFrame`: a fixed
  range test matrix.
* any law of the range test matrix: the same name with `_le_mul_integral` before
  `_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-- The squared error of early-truncated generalized Nyström with a fixed range test matrix and a
Haar co-range test matrix is integrable for $k + 2 \le p \le m$. -/
private theorem integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_fixed_haar
    [DecidableEq p] (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2) μ := by
  classical
  have hr := rank_truncatedSVD_le (A * X₀) k
  simp only [sub_earlyTruncatedGeneralizedNystrom]
  exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame hΨ hpm
    (truncatedSVD (A * X₀) k) (by omega) A

/-- **Early-truncated generalized Nyström conditionally on the range test matrix, Haar
co-range**: for a fixed $\mathbf{\Omega}$, an $m \times p$ Haar co-range test matrix
$\mathbf{\Psi}$ with $p \le m$,
$q = \operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k \le k$ and
$k + 2 \le p$, <!-- value haarProjectionFactor m p q -->
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{m - p}{m - q}\cdot\frac{q}{p - q - 1}\Bigr)
\|\mathbf{A}-\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2\,,$$
the factor at the actual rank $q$. The Gaussian twin is
`NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix`.
Proved without a literature source, as a composition: the completion step is
[EpperlyWebber2026, Theorem 2.1]; the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (truncatedSVD (A * X₀) k).rank *
        frobNorm (A - earlyTruncatedRSVD A X₀ k) ^ 2 := by
  classical
  have hr := rank_truncatedSVD_le (A * X₀) k
  simp only [sub_earlyTruncatedGeneralizedNystrom, sub_earlyTruncatedRSVD]
  exact integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame hΨ hpm
    (truncatedSVD (A * X₀) k) (by omega) A

/-- The Haar completion factor at the rank of the truncated sketch is measurable in the range
test matrix. -/
private theorem measurable_haarProjectionFactor_rank_truncatedSVD (A : Matrix m n ℝ)
    (k d c : ℕ) :
    Measurable fun x : Matrix n l ℝ => haarProjectionFactor d c (truncatedSVD (A * x) k).rank :=
  (measurable_from_nat (f := fun q => haarProjectionFactor d c q)).comp
    (measurable_rank.comp ((measurable_const.matrix_mul measurable_id).truncatedSVD k))

/-- The Haar completion factor at the rank of the truncated sketch lies in $[1, 1 + p]$. -/
private theorem haarProjectionFactor_rank_truncatedSVD_mem (A : Matrix m n ℝ)
    (x : Matrix n l ℝ) {k c d : ℕ} (h : k + 2 ≤ c) (hcd : c ≤ d) :
    1 ≤ haarProjectionFactor d c (truncatedSVD (A * x) k).rank ∧
      haarProjectionFactor d c (truncatedSVD (A * x) k).rank ≤ 1 + c := by
  have hr := rank_truncatedSVD_le (A * x) k
  have hq : (truncatedSVD (A * x) k).rank + 2 ≤ c := by omega
  refine ⟨one_le_haarProjectionFactor hq hcd,
    (haarProjectionFactor_le_gaussianProjectionFactor hq hcd).trans ?_⟩
  have h' : ((truncatedSVD (A * x) k).rank : ℝ) + 2 ≤ c := by exact_mod_cast hq
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ (by linarith)]
  nlinarith

/-- The right side of the conditional identity, integrated over $\mathbf{\Omega}$, is
integrable. -/
private theorem integrable_haarProjectionFactor_mul_earlyTruncatedRSVD [IsFiniteMeasure μ]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hpm : Fintype.card p ≤ Fintype.card m) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω =>
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (truncatedSVD (A * X ω) k).rank *
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) μ := by
  refine (integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX k).bdd_mul
    (c := 1 + Fintype.card p)
    ((measurable_haarProjectionFactor_rank_truncatedSVD A k _ _).comp_aemeasurable
      hX).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  obtain ⟨h1, h2⟩ := haarProjectionFactor_rank_truncatedSVD_mem A (X ω) hkp hpm
  rwa [Real.norm_of_nonneg (zero_le_one.trans h1)]

/-- The conditional identity as lower integrals, over the independent pair. -/
private theorem lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_haar [DecidableEq p]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    ∫⁻ ω, ENNReal.ofReal (frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2)
        ∂μ =
      ∫⁻ ω, ENNReal.ofReal
        (haarProjectionFactor (Fintype.card m) (Fintype.card p) (truncatedSVD (A * X ω) k).rank *
          frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hF : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      ENNReal.ofReal (frobNorm (A - earlyTruncatedGeneralizedNystrom A q.1 q.2 k) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_earlyTruncatedGeneralizedNystrom A k))).pow_const 2)
  have hG : Measurable fun x : Matrix n l ℝ =>
      ENNReal.ofReal (haarProjectionFactor (Fintype.card m) (Fintype.card p)
        (truncatedSVD (A * x) k).rank * frobNorm (A - earlyTruncatedRSVD A x k) ^ 2) :=
    ENNReal.measurable_ofReal.comp
      ((measurable_haarProjectionFactor_rank_truncatedSVD A k _ _).mul
        ((continuous_frobNorm.measurable.comp
          (measurable_const.sub (measurable_earlyTruncatedRSVD A k))).pow_const 2))
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (haarFrame m p) (haarFrame m p) := HasLaw.id
  rw [hXΨ.lintegral_comp_eq_lintegral_lintegral hX hΨ.aemeasurable hF, hΨ.map_eq,
    ← lintegral_map' hG.aemeasurable hX]
  refine lintegral_congr fun x => ?_
  dsimp only
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_fixed_haar A x hid hpm hkp)
      (ae_of_all _ fun _ => sq_nonneg _),
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_haarFrame A x hid hpm hkp]

-- The theorem's name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Early-truncated generalized Nyström = early-truncated randomized SVD × completion, Haar
co-range**: for any law of $\mathbf{\Omega}$ independent of an $m \times p$ Haar $\mathbf{\Psi}$
with $p \le m$, and $k + 2 \le p$, <!-- value haarProjectionFactor m p k -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{m - p}{m - k}\cdot\frac{k}{p - k - 1}\Bigr)\,
\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2\,.$$
The Gaussian twin is
`integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix`.
Proved without a literature source, as a composition: [EpperlyWebber2026, Theorem 2.1] for the
completion; the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      haarProjectionFactor (Fintype.card m) (Fintype.card p) k *
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hR := integrable_haarProjectionFactor_mul_earlyTruncatedRSVD A hX hpm hkp
  have hR0 : 0 ≤ᵐ[μ] fun ω =>
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (truncatedSVD (A * X ω) k).rank *
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 :=
    ae_of_all _ fun ω => mul_nonneg (zero_le_one.trans
      (haarProjectionFactor_rank_truncatedSVD_mem A (X ω) hkp hpm).1) (sq_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (aestronglyMeasurable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX
        hΨ.aemeasurable k),
    lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_haar A hX hΨ hpm hXΨ hkp,
    ← integral_eq_lintegral_of_nonneg_ae hR0 hR.aestronglyMeasurable, ← integral_const_mul]
  refine integral_mono_of_nonneg hR0
    ((integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX k).const_mul _)
    (ae_of_all _ fun ω => ?_)
  exact mul_le_mul_of_nonneg_right (haarProjectionFactor_le_haarProjectionFactor
    (rank_truncatedSVD_le _ k) hkp hpm) (sq_nonneg _)

end NLAlib
