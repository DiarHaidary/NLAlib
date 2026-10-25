/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Sketching.Gaussian.HaarEmbedding
public import NLAlib.Sketching.Gaussian.SubGaussian
public import NLAlib.Sketching.Properties.ProjectionCost

/-!
# Projection-cost-preserving sketches from dense families

The Gaussian, sub-Gaussian (Rademacher at proxy $1$) and Haar sketches as rank-$d$
projection-cost-preserving sketches with constants $1 \mp \varepsilon$, through the head–tail
constructor `NLAlib.IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment`: the
family's OSE at $(\varepsilon/2, \delta/2)$ for the head and its JL moment property at the budget
$\varepsilon/(8\sqrt{d+1})$ for the three tail events. Each family has two incomparable explicit
forms (CONTRIBUTING §5.2 rule 4): the JL moment at $p = 2$, whose second size
`NLAlib.projectionCostTailDim` is <!-- value projectionCostTailDim v d \varepsilon \delta -->
$384 \cdot v (d + 1)/(\varepsilon^2 \delta)$ for a family with JL variance $v/\lvert k\rvert$,
and the JL moment at
$p = \max(2, \log(1/\delta))$ (`_of_jlMomentDim_le`, `_of_subgaussianJLMomentDim_le`), whose second
size is $O((d+1)\log(1/\delta)/\varepsilon^2)$. The asymptotic forms are proved from the second.
The product form $(d + 1)\log(1/\delta)$ is what JL moments give through this constructor; the
additive $(d + \log(1/\delta))/\varepsilon^2$ of [CohenElderMuscoMuscoPersu2015] needs stable-rank
spectral approximate multiplication, not available for dense sketches.

The Gaussian and sub-Gaussian statements moved here from their family files at the
sketching-moments round (2026-10-22), names unchanged. Design: `docs/design/LowRank-S9.md` §6,
`docs/design/Sketching-Moments.md` §2.6, §4.3, §8 Q6.

## Main results

* `NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card`,
  `NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_jlMomentDim_le` and the
  asymptotic form `NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix`.
* `NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card`,
  `NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_subgaussianJLMomentDim_le` and
  `NLAlib.exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector`.
* `NLAlib.hasProjectionCostPreserving_of_hasLaw_haarFrame_of_le_card`,
  `NLAlib.hasProjectionCostPreserving_of_hasLaw_haarFrame_of_jlMomentDim_le` and
  `NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n : Type*} [Fintype k]
  [Fintype n] {ε δ : ℝ}

/-! ### The shared budget -/

/-- The tail distortion $\varepsilon/(8\sqrt{d+1})$ is at most $\varepsilon/8$. -/
private theorem div_eight_mul_sqrt_le (hε : 0 ≤ ε) (d : ℕ) :
    ε / (8 * √((d : ℝ) + 1)) ≤ ε / 8 := by
  have hs1 : 1 ≤ √((d : ℝ) + 1) :=
    Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) d])
  exact div_le_div_of_nonneg_left hε (by norm_num) (by linarith)

/-- The constants of the head–tail constructor at the head distortion $\varepsilon/2$ and the
tail distortion $\varepsilon/(8\sqrt{d+1})$ are within $1 \mp \varepsilon$. -/
private theorem one_sub_le_and_add_le (hε : 0 < ε) (d : ℕ) :
    1 - ε ≤ 1 - ε / 2 - 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ∧
      1 + ε / 2 + 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) + ε / (8 * √((d : ℝ) + 1)) ≤
        1 + ε := by
  have hJ0 : 0 < ε / (8 * √((d : ℝ) + 1)) := by positivity
  have hds : √(d : ℝ) ≤ √((d : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
  have hJ : ε / (8 * √((d : ℝ) + 1)) * √((d : ℝ) + 1) = ε / 8 := by field_simp
  have hJ1 := div_eight_mul_sqrt_le hε.le d
  have h3 : 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ≤ 3 * (ε / 8) := by
    rw [← hJ, mul_assoc]
    exact mul_le_mul_of_nonneg_left
      (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hds hJ0.le) (by norm_num)
  exact ⟨by linarith, by linarith⟩

/-- The head–tail constructor at the family budgets: an OSE at $(\varepsilon/2, \delta/2)$ and
the JL moment property at $\varepsilon/(8\sqrt{d+1})$ with failure $\delta'$,
$\delta/2 + 3\delta' \le \delta$, give constants $1 \mp \varepsilon$ and failure $\delta$. -/
private theorem hasProjectionCostPreserving_of_half [IsFiniteMeasure μ] {S : Ω → Matrix k n ℝ}
    {d : ℕ} {δ' p : ℝ} (h : IsObliviousSubspaceEmbedding S d (1 - ε / 2) (1 + ε / 2) (δ / 2) μ)
    (hJL : HasJLMoment S (ε / (8 * √((d : ℝ) + 1))) δ' p μ) (hS : AEMeasurable S μ)
    (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ') (hδδ' : δ / 2 + 3 * δ' ≤ δ) {m : Type*}
    [Fintype m] (A : Matrix m n ℝ) :
    HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ := by
  obtain ⟨h₁, h₂⟩ := one_sub_le_and_add_le hε d
  exact (h.hasProjectionCostPreserving_of_hasJLMoment hJL hS (by linarith) (by linarith)
    (by positivity) hp hδ' A).mono le_rfl h₁ h₂ hδδ'

/-- At least <!-- value projectionCostTailDim v d \varepsilon \delta -->
$384 \cdot v (d + 1)/(\varepsilon^2 \delta)$ rows (`projectionCostTailDim v d ε δ`) make the three
tail failures $v/(\lvert k\rvert\varepsilon_J^2)$ at $\varepsilon_J = \varepsilon/(8\sqrt{d+1})$
total at most $\delta/2$. -/
private theorem three_mul_div_le_of_projectionCostTailDim_le {v K : ℝ} {d : ℕ} (hε : 0 < ε)
    (hδ : 0 < δ) (hK : 0 < K) (hk : projectionCostTailDim v d ε δ ≤ K) :
    3 * (v / (K * (ε / (8 * √((d : ℝ) + 1))) ^ 2)) ≤ δ / 2 := by
  have hss : √((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
  rw [projectionCostTailDim_def, div_le_iff₀ (by positivity)] at hk
  have e : v / (K * (ε / (8 * √((d : ℝ) + 1))) ^ 2) =
      64 * v * ((d : ℝ) + 1) / (K * ε ^ 2) := by
    rw [div_pow, mul_pow, hss]
    field_simp
    ring
  rw [e, mul_div_assoc', div_le_iff₀ (by positivity)]
  nlinarith

/-- For $0 < \delta \le 1/2$, $d \le 2(d+1)\log(1/\delta)$. -/
private theorem natCast_le_two_mul_log (d : ℕ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    (d : ℝ) ≤ 2 * (((d : ℝ) + 1) * Real.log (1 / δ)) := by
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hl2 := Real.log_two_gt_d9
  nlinarith [mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)]

/-- For $0 < \delta \le 1/2$, $\log(2/(\delta/2)) \le 3\log(1/\delta)$. -/
private theorem log_two_div_half_le (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    Real.log (2 / (δ / 2)) ≤ 3 * Real.log (1 / δ) := by
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  rw [show 2 / (δ / 2) = 2 * 2 * (1 / δ) by field_simp,
    Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
  linarith

/-- For $0 < \delta \le 1/2$, $\log(1/(\delta/6)) \le 4\log(1/\delta)$. -/
private theorem log_one_div_sixth_le (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2) :
    Real.log (1 / (δ / 6)) ≤ 4 * Real.log (1 / δ) := by
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have h8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have h6 : Real.log 6 ≤ Real.log 8 := Real.log_le_log (by norm_num) (by norm_num)
  rw [show 1 / (δ / 6) = 6 * (1 / δ) by field_simp, Real.log_mul (by norm_num) (by positivity)]
  linarith

/-- The tail rows of the $\log(1/\delta)$ forms against the asymptotic threshold:
`jlMomentDim (ε / (8 * √(d + 1))) (δ / 6)`, which
is <!-- value jlMomentDim (\varepsilon/(8\sqrt{d+1})) (\delta/6) -->
$128\max(2, \log(1/(\delta/6)))/(\varepsilon/(8\sqrt{d+1}))^2$, is at most
$98304(d+1)\log(1/\delta)/\varepsilon^2$ for $0 < \delta \le 1/2$. -/
private theorem jlMomentDim_le_of_mul_le {d : ℕ} {K : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) (hK : 98304 * (((d : ℝ) + 1) * Real.log (1 / δ) / ε ^ 2) ≤ K) :
    jlMomentDim (ε / (8 * √((d : ℝ) + 1))) (δ / 6) ≤ K := by
  have hss : √((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
  have hl6 := log_one_div_sixth_le hδ hδ2
  refine (jlMomentDim_le (by positivity) (by linarith)).trans (le_trans ?_ hK)
  calc 384 * Real.log (1 / (δ / 6)) / (ε / (8 * √((d : ℝ) + 1))) ^ 2
      = 384 * 64 * (((d : ℝ) + 1) * Real.log (1 / (δ / 6))) / ε ^ 2 := by
        rw [div_pow, mul_pow, hss]
        field_simp
        ring
    _ ≤ 98304 * (((d : ℝ) + 1) * Real.log (1 / δ) / ε ^ 2) := by
        rw [mul_div_assoc']
        exact div_le_div_of_nonneg_right
          (by nlinarith [mul_le_mul_of_nonneg_left hl6 (by positivity : (0 : ℝ) ≤ (d : ℝ) + 1)])
          (sq_nonneg ε)

/-! ### Gaussian sketches -/

section Gaussian

variable {G : Ω → Matrix k n ℝ}

/-- **A Gaussian sketch is a projection-cost-preserving sketch**, size form: for
$0 < \varepsilon \le 2$, $\delta > 0$, at
least <!-- value gaussianEmbeddingDim d (\varepsilon/2) (\delta/2) -->
$9 (\sqrt{d} + \sqrt{2 \log(2/(\delta/2))})^2/(\varepsilon/2)^2$ rows
(`gaussianEmbeddingDim d (ε / 2) (δ / 2)`) and at
least <!-- value projectionCostTailDim 2 d \varepsilon \delta -->
$384 \cdot 2 (d + 1)/(\varepsilon^2 \delta)$ rows (`projectionCostTailDim 2 d ε δ`),
$\mathbf{S} = \lvert k \rvert^{-1/2}\mathbf{G}$ makes $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$
projection-cost-preserving sketch of $\mathbf{A}$ with constants $1 \mp \varepsilon$, for every
$\mathbf{A}$, except with probability $\delta$. The head is the OSE size form at
$(\varepsilon/2, \delta/2)$, the tail the JL moment at $\varepsilon/(8\sqrt{d+1})$, through
`NLAlib.IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment`.
[CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 1]; there sign matrices and
$O((k + \log(1/\delta))/\varepsilon^2)$ rows through stable-rank spectral approximate
multiplication, error $O(\varepsilon)$; here the Gaussian, explicit constants, and $1/\delta$ from
second moments. Incomparable with its $\log(1/\delta)$ twin
`NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_jlMomentDim_le` (rule 4): this one
needs fewer rows at constant $\delta$, the twin for small $\delta$; the asymptotic form
`NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix` is proved from the
twin.
Result: gaussian-pcp -/
theorem hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card
    (hG : HasLaw G (gaussianMatrix k n) μ) {m : Type*} [Fintype m] (A : Matrix m n ℝ) (d : ℕ)
    (hε : 0 < ε) (hε2 : ε ≤ 2) (hδ : 0 < δ)
    (hk₁ : gaussianEmbeddingDim d (ε / 2) (δ / 2) ≤ Fintype.card k)
    (hk₂ : projectionCostTailDim 2 d ε δ ≤ Fintype.card k) :
    HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) A d (1 - ε) (1 + ε) δ
      μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hpos : 0 < projectionCostTailDim 2 d ε δ := by
    rw [projectionCostTailDim_def]; positivity
  have hK : (0 : ℝ) < Fintype.card k := hpos.trans_le hk₂
  have : Nonempty k := Fintype.card_pos_iff.1 (by exact_mod_cast hK)
  have hJ0 : 0 < ε / (8 * √((d : ℝ) + 1)) := by positivity
  have hbud : 1 - ε ≤ 1 - ε / 2 - 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ∧
      1 + ε / 2 + 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) + ε / (8 * √((d : ℝ) + 1)) ≤
        1 + ε ∧
      δ / 2 + 3 * (2 / (Fintype.card k * (ε / (8 * √((d : ℝ) + 1))) ^ 2)) ≤ δ := by
    have hs1 : 1 ≤ √((d : ℝ) + 1) :=
      Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) d])
    have hds : √(d : ℝ) ≤ √((d : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hss : √((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hJ : ε / (8 * √((d : ℝ) + 1)) * √((d : ℝ) + 1) = ε / 8 := by field_simp
    have hJ1 : ε / (8 * √((d : ℝ) + 1)) ≤ ε / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 : 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ≤ 3 * (ε / 8) := by
      rw [← hJ, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hds hJ0.le) (by norm_num)
    refine ⟨by linarith, by linarith, ?_⟩
    have hk := hk₂
    rw [projectionCostTailDim_def, div_le_iff₀ (by positivity)] at hk
    have e : 2 / (Fintype.card k * (ε / (8 * √((d : ℝ) + 1))) ^ 2) =
        64 * 2 * ((d : ℝ) + 1) / (Fintype.card k * ε ^ 2) := by
      rw [div_pow, mul_pow, hss]
      field_simp
      ring
    have h4 : 3 * (64 * 2 * ((d : ℝ) + 1) / (Fintype.card k * ε ^ 2)) ≤ δ / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨h₁, h₂, h₃⟩ := hbud
  have hose := isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le
    hG (half_pos hε) (by linarith) (half_pos hδ) hk₁
  exact (hose.hasProjectionCostPreserving_of_hasJLMoment
    (hasJLMoment_of_hasLaw_gaussianMatrix hG hJ0)
    (hG.aemeasurable.const_smul ((√(Fintype.card k : ℝ))⁻¹)) (by linarith) (by linarith) hJ0
    le_rfl (by positivity) A).mono le_rfl h₁ h₂ h₃

/-- **A Gaussian sketch is a projection-cost-preserving sketch**, $\log(1/\delta)$ size form:
for $0 < \varepsilon \le 2$, $\delta > 0$, at
least <!-- value gaussianEmbeddingDim d (\varepsilon/2) (\delta/2) -->
$9 (\sqrt{d} + \sqrt{2 \log(2/(\delta/2))})^2/(\varepsilon/2)^2$ rows
(`gaussianEmbeddingDim d (ε / 2) (δ / 2)`) and at
least <!-- value jlMomentDim (\varepsilon/(8\sqrt{d+1})) (\delta/6) -->
$128\max(2, \log(1/(\delta/6)))/(\varepsilon/(8\sqrt{d+1}))^2$ rows
(`jlMomentDim (ε / (8 * √(d + 1))) (δ / 6)`), $\mathbf{S} = \lvert k \rvert^{-1/2}\mathbf{G}$ with
$\mathbf{G}$ standard Gaussian makes $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$
projection-cost-preserving sketch of $\mathbf{A}$ with constants $1 \mp \varepsilon$, for every
$\mathbf{A}$, except with probability $\delta$. The head is the OSE size form at
$(\varepsilon/2, \delta/2)$, the tail the JL moment
`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le` at $\varepsilon/(8\sqrt{d+1})$
with failure $\delta/6$, at exponent $\max(2, \log(6/\delta))$. Incomparable with
`NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card` (rule 4): the second
size is $O((d+1)\log(1/\delta)/\varepsilon^2)$ in place of $O((d+1)/(\varepsilon^2\delta))$.
[CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 1]; there sign matrices and
$O((k + \log(1/\delta))/\varepsilon^2)$ rows through stable-rank spectral approximate
multiplication; here the product form that JL moments give. Asymptotic form:
`NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix`.
Result: gaussian-pcp -/
theorem hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
    (hG : HasLaw G (gaussianMatrix k n) μ) {m : Type*} [Fintype m] (A : Matrix m n ℝ) (d : ℕ)
    (hε : 0 < ε) (hε2 : ε ≤ 2) (hδ : 0 < δ)
    (hk₁ : gaussianEmbeddingDim d (ε / 2) (δ / 2) ≤ Fintype.card k)
    (hk₂ : jlMomentDim (ε / (8 * √((d : ℝ) + 1))) (δ / 6) ≤ Fintype.card k) :
    HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) A d (1 - ε) (1 + ε) δ
      μ := by
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hJ1 := div_eight_mul_sqrt_le hε.le d
  exact hasProjectionCostPreserving_of_half
    (isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le hG
      (half_pos hε) (by linarith) (half_pos hδ) hk₁)
    (hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le hG (by positivity) (by linarith)
      (by positivity) hk₂)
    (hG.aemeasurable.const_smul ((√(Fintype.card k : ℝ))⁻¹)) hε (le_max_left _ _) (by positivity)
    (by linarith) A

/-- **Gaussian rows suffice for a rank-$d$ projection-cost-preserving sketch**:
$$O((d+1)\log(1/\delta)/\varepsilon^2)$$
rows give one, with constants $1 \mp \varepsilon$ and failure probability $\delta$, for
$\varepsilon$ and $\delta$ below absolute constants; the constants come before every dimension.
Proved from
`NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_jlMomentDim_le` with
$\varepsilon_0 = 1$ and $\delta \le 1/2$; the OSE size $O((d + \log(1/\delta))/\varepsilon^2)$ is
dominated by the tail size there. The literature's additive $(d + \log(1/\delta))/\varepsilon^2$
needs stable-rank spectral approximate multiplication. [CohenElderMuscoMuscoPersu2015,
Theorem 12].
Asymptotic: NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_jlMomentDim_le
Result: gaussian-pcp -/
theorem exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m]
      [Fintype n] (μ : Measure Ω) (G : Ω → Matrix k n ℝ) (A : Matrix m n ℝ) (d : ℕ) (ε δ : ℝ),
      HasLaw G (gaussianMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (((d : ℝ) + 1) * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) A d (1 - ε) (1 + ε)
        δ μ := by
  refine ⟨98304, 1, by norm_num, one_pos, fun μ G A d ε δ hG hε hε1 hδ hδ2 hk => ?_⟩
  have hl := log_two_div_half_le hδ hδ2
  have hd := natCast_le_two_mul_log d hδ hδ2
  have hL : 0 ≤ Real.log (1 / δ) := (Real.log_nonneg (by norm_num)).trans
    (Real.log_two_le_log_one_div hδ hδ2)
  refine hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_jlMomentDim_le hG A d hε
    (by linarith) hδ ((gaussianEmbeddingDim_le d _ (by positivity) (by linarith)).trans
      (le_trans ?_ hk)) (jlMomentDim_le_of_mul_le hε hδ hδ2 hk)
  generalize Real.log (2 / (δ / 2)) = t at hl ⊢
  rw [show 18 * ((d : ℝ) + 2 * t) / (ε / 2) ^ 2 = 72 * ((d : ℝ) + 2 * t) / ε ^ 2 by
    field_simp; ring, mul_div_assoc']
  exact div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg ε)

end Gaussian

/-! ### Sub-Gaussian sketches -/

section SubGaussian

variable [DecidableEq n] {X : Ω → Matrix k n ℝ} {c : ℝ≥0}

/-- **A sub-Gaussian sketch is a projection-cost-preserving sketch**, size form: for a sketch
$\mathbf{X}$ with independent isotropic rows, sub-Gaussian with proxy $c$, for $k$ nonempty,
$0 < \varepsilon \le 5c/2$, $\delta > 0$, at
least <!-- value subgaussianEmbeddingDim c d (\varepsilon/2) (\delta/2) -->
$25 c^2 (d \log 21 + \log(2/(\delta/2)))/(16 C (\varepsilon/2)^2)$ rows
(`subgaussianEmbeddingDim c d (ε / 2) (δ / 2)`,
with <!-- value subgaussianJLConstant -->$C = 1/36$ the constant `subgaussianJLConstant`) and at
least <!-- value projectionCostTailDim {(16c^2 - 1)} d \varepsilon \delta -->
$384 \cdot (16c^2 - 1) (d + 1)/(\varepsilon^2 \delta)$ rows
(`projectionCostTailDim (16 * c ^ 2 - 1) d ε δ`), $\mathbf{S} = \lvert k \rvert^{-1/2}\mathbf{X}$
makes $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$ projection-cost-preserving sketch of
$\mathbf{A}$ with constants $1 \mp \varepsilon$, for every $\mathbf{A}$, except with probability
$\delta$. A Rademacher sketch is the case $c = 1$
(`NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`,
`NLAlib.isIsotropic_of_hasLaw_rademacherVector`, `ProbabilityTheory.HasLaw.iIndepFun_eval`),
CEMMP's family 1; its constants are looser than a Rademacher-specific route would give, which
the asymptotic forms do not see. The route of [CohenElderMuscoMuscoPersu2015, proof of
Theorem 12]; the sub-Gaussian instance is not stated there. Incomparable with its
$\log(1/\delta)$ twin
`NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`
(rule 4): this one needs fewer rows at constant $\delta$, the twin for small $\delta$; the
asymptotic form `NLAlib.exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector` is
proved from the twin.
Result: subgaussian-pcp -/
theorem hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card [Nonempty k]
    (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {m : Type*} [Fintype m] (A : Matrix m n ℝ)
    (d : ℕ) (hε : 0 < ε) (hεc : ε ≤ 5 / 2 * c) (hδ : 0 < δ)
    (hk₁ : subgaussianEmbeddingDim c d (ε / 2) (δ / 2) ≤ Fintype.card k)
    (hk₂ : projectionCostTailDim (16 * (c : ℝ) ^ 2 - 1) d ε δ ≤ Fintype.card k) :
    HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) A d (1 - ε) (1 + ε)
      δ μ := by
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty n with hn | hn
  · exact hasProjectionCostPreserving_of_isEmpty _ A d _ _ hδ.le
  have hc : 1 ≤ (c : ℝ) :=
    (hsub (Classical.arbitrary k)).one_le_of_isIsotropic (hiso (Classical.arbitrary k))
  have hv : 0 ≤ 16 * (c : ℝ) ^ 2 - 1 := by nlinarith
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hJ0 : 0 < ε / (8 * √((d : ℝ) + 1)) := by positivity
  have hbud : 1 - ε ≤ 1 - ε / 2 - 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ∧
      1 + ε / 2 + 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) + ε / (8 * √((d : ℝ) + 1)) ≤
        1 + ε ∧
      δ / 2 + 3 * ((16 * (c : ℝ) ^ 2 - 1) / (Fintype.card k * (ε / (8 * √((d : ℝ) + 1))) ^ 2)) ≤
        δ := by
    have hs1 : 1 ≤ √((d : ℝ) + 1) :=
      Real.one_le_sqrt.2 (by linarith [Nat.cast_nonneg (α := ℝ) d])
    have hds : √(d : ℝ) ≤ √((d : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
    have hss : √((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
    have hJ : ε / (8 * √((d : ℝ) + 1)) * √((d : ℝ) + 1) = ε / 8 := by field_simp
    have hJ1 : ε / (8 * √((d : ℝ) + 1)) ≤ ε / 8 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have h3 : 3 * √(d : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ≤ 3 * (ε / 8) := by
      rw [← hJ, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (by rw [mul_comm]; exact mul_le_mul_of_nonneg_left hds hJ0.le) (by norm_num)
    refine ⟨by linarith, by linarith, ?_⟩
    have hk := hk₂
    rw [projectionCostTailDim_def, div_le_iff₀ (by positivity)] at hk
    have e : (16 * (c : ℝ) ^ 2 - 1) / (Fintype.card k * (ε / (8 * √((d : ℝ) + 1))) ^ 2) =
        64 * (16 * (c : ℝ) ^ 2 - 1) * ((d : ℝ) + 1) / (Fintype.card k * ε ^ 2) := by
      rw [div_pow, mul_pow, hss]
      field_simp
      ring
    have h4 : 3 * (64 * (16 * (c : ℝ) ^ 2 - 1) * ((d : ℝ) + 1) / (Fintype.card k * ε ^ 2)) ≤
        δ / 2 := by
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  obtain ⟨h₁, h₂, h₃⟩ := hbud
  have hose := isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le
    hind hsub hiso (half_pos hε) (by linarith) (half_pos hδ) hk₁
  have hX : AEMeasurable X μ := aemeasurable_pi_lambda X fun i => (hsub i).aemeasurable
  exact (hose.hasProjectionCostPreserving_of_hasJLMoment
    (hasJLMoment_of_isSubgaussianVector hind hsub hiso hJ0)
    (hX.const_smul ((√(Fintype.card k : ℝ))⁻¹)) (by linarith) (by linarith) hJ0 le_rfl
    (div_nonneg hv (by positivity)) A).mono le_rfl h₁ h₂ h₃

/-- **A sub-Gaussian sketch is a projection-cost-preserving sketch**, $\log(1/\delta)$ size
form: for a sketch $\mathbf{X}$ with independent isotropic rows, sub-Gaussian with proxy $c$, for
$0 < \varepsilon \le 5c/2$, $\delta > 0$, at
least <!-- value subgaussianEmbeddingDim c d (\varepsilon/2) (\delta/2) -->
$25 c^2 (d \log 21 + \log(2/(\delta/2)))/(16 C (\varepsilon/2)^2)$ rows
(`subgaussianEmbeddingDim c d (ε / 2) (δ / 2)`) and at
least <!-- value subgaussianJLMomentDim c (\varepsilon/(8\sqrt{d+1})) (\delta/6) -->
$16c^2\max(2, \log(1/(\delta/6)))/(C(\varepsilon/(8\sqrt{d+1}))^2)$ rows
(`subgaussianJLMomentDim c (ε / (8 * √(d + 1))) (δ / 6)`),
with <!-- value subgaussianJLConstant -->$C = 1/36$ the constant `subgaussianJLConstant`,
$\mathbf{S} = \lvert k \rvert^{-1/2}\mathbf{X}$ makes $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a
rank-$d$ projection-cost-preserving sketch of $\mathbf{A}$ with constants $1 \mp \varepsilon$, for
every $\mathbf{A}$, except with probability $\delta$. Sign sketches are the case $c = 1$. The
tail is the JL moment `NLAlib.hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le`
at $\varepsilon/(8\sqrt{d+1}) \le c$, failure $\delta/6$. Incomparable with
`NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card` (rule 4). The route of
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12]; the sub-Gaussian instance is not stated
there. Asymptotic form: `NLAlib.exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector`.
Result: subgaussian-pcp -/
theorem hasProjectionCostPreserving_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
    (hind : iIndepFun (fun i ω => X ω i) μ)
    (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
    (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) {m : Type*} [Fintype m] (A : Matrix m n ℝ)
    (d : ℕ) (hε : 0 < ε) (hεc : ε ≤ 5 / 2 * c) (hδ : 0 < δ)
    (hk₁ : subgaussianEmbeddingDim c d (ε / 2) (δ / 2) ≤ Fintype.card k)
    (hk₂ : subgaussianJLMomentDim c (ε / (8 * √((d : ℝ) + 1))) (δ / 6) ≤ Fintype.card k) :
    HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) A d (1 - ε) (1 + ε)
      δ μ := by
  have := hind.isProbabilityMeasure
  have hJ1 := div_eight_mul_sqrt_le hε.le d
  have hX : AEMeasurable X μ := aemeasurable_pi_lambda X fun i => (hsub i).aemeasurable
  exact hasProjectionCostPreserving_of_half
    (isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le hind hsub
      hiso (half_pos hε) (by linarith) (half_pos hδ) hk₁)
    (hasJLMoment_of_isSubgaussianVector_of_subgaussianJLMomentDim_le hind hsub hiso
      (by positivity) (by linarith [c.2]) (by positivity) hk₂)
    (hX.const_smul ((√(Fintype.card k : ℝ))⁻¹)) hε (le_max_left _ _) (by positivity)
    (by linarith) A

/-- **Sub-Gaussian rows suffice for a rank-$d$ projection-cost-preserving sketch**:
$$O(c^2 (d+1)\log(1/\delta)/\varepsilon^2)$$
independent isotropic rows, sub-Gaussian with proxy $c$, give one, with constants
$1 \mp \varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below absolute
constants; the constants come before every dimension and the proxy. At $c = 1$ this
covers Rademacher sketches. Proved from
`NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_subgaussianJLMomentDim_le` with
$\varepsilon_0 = 1$ and $\delta \le 1/2$; isotropy forces $c \ge 1$ once there is a column.
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Asymptotic:
NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_subgaussianJLMomentDim_le
Result: subgaussian-pcp -/
theorem exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k]
      [Fintype m] [Fintype n] [DecidableEq n] [Nonempty k] (μ : Measure Ω)
      (X : Ω → Matrix k n ℝ) (c : ℝ≥0) (A : Matrix m n ℝ) (d : ℕ) (ε δ : ℝ),
      iIndepFun (fun i ω => X ω i) μ → (∀ i, IsSubgaussianVector (fun ω => X ω i) c μ) →
      (∀ i, IsIsotropic (fun ω => X ω i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * ((c : ℝ) ^ 2 * ((d : ℝ) + 1) * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) A d (1 - ε)
        (1 + ε) δ μ := by
  refine ⟨442368, 1, by norm_num, one_pos, ?_⟩
  intro Ω k m n _ _ _ _ _ _ μ X c A d ε δ hind hsub hiso hε hε1 hδ hδ2 hk
  rcases isEmpty_or_nonempty n with hn | hn
  · exact hasProjectionCostPreserving_of_isEmpty _ A d _ _ hδ.le
  have := hind.isProbabilityMeasure
  have hc : 1 ≤ (c : ℝ) :=
    (hsub (Classical.arbitrary k)).one_le_of_isIsotropic (hiso (Classical.arbitrary k))
  have hl := log_two_div_half_le hδ hδ2
  have hl6 := log_one_div_sixth_le hδ hδ2
  have hd := natCast_le_two_mul_log d hδ hδ2
  have hL : 0 ≤ Real.log (1 / δ) := (Real.log_nonneg (by norm_num)).trans
    (Real.log_two_le_log_one_div hδ hδ2)
  have hc2 : 0 ≤ (c : ℝ) ^ 2 := sq_nonneg _
  have hss : √((d : ℝ) + 1) ^ 2 = (d : ℝ) + 1 := Real.sq_sqrt (by positivity)
  refine hasProjectionCostPreserving_of_isSubgaussianVector_of_subgaussianJLMomentDim_le hind
    hsub hiso A d hε (by linarith) hδ
    ((subgaussianEmbeddingDim_le c d _ (by positivity) (by linarith)).trans (le_trans ?_ hk))
    ((subgaussianJLMomentDim_le c _ (by positivity) (by linarith)).trans (le_trans ?_ hk))
  · generalize Real.log (2 / (δ / 2)) = t at hl ⊢
    rw [show 172 * (c : ℝ) ^ 2 * ((d : ℝ) + t) / (ε / 2) ^ 2 =
      688 * ((c : ℝ) ^ 2 * ((d : ℝ) + t)) / ε ^ 2 by field_simp; ring, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
    nlinarith [mul_le_mul_of_nonneg_left hl hc2, mul_le_mul_of_nonneg_left hd hc2,
      mul_nonneg hc2 hL, mul_nonneg (mul_nonneg hc2 hL) (Nat.cast_nonneg (α := ℝ) d)]
  · generalize Real.log (1 / (δ / 6)) = t at hl6 ⊢
    rw [show 1728 * (c : ℝ) ^ 2 * t / (ε / (8 * √((d : ℝ) + 1))) ^ 2 =
      1728 * 64 * ((c : ℝ) ^ 2 * ((d : ℝ) + 1) * t) / ε ^ 2 by
        rw [div_pow, mul_pow, hss]; field_simp; ring, mul_div_assoc']
    refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
    nlinarith [mul_le_mul_of_nonneg_left hl6 (by positivity : 0 ≤ (c : ℝ) ^ 2 * ((d : ℝ) + 1))]

end SubGaussian

/-! ### Haar sketches -/

section Haar

variable [DecidableEq k] {Q : Ω → Matrix n k ℝ}

/-- **A Haar sketch is a projection-cost-preserving sketch**, size form: for
$\lvert k\rvert \le \lvert n\rvert$, $0 < \varepsilon \le 2$, $\delta > 0$, at
least <!-- value jlDim (2\varepsilon/5) (\delta/2/21^d) -->
$\log(2/(\delta/2/21^d))/((2\varepsilon/5)^2/4 - (2\varepsilon/5)^3/6)$ rows
(`jlDim (2 * ε / 5) (δ / 2 / 21 ^ d)`) and at
least <!-- value projectionCostTailDim 2 d \varepsilon \delta -->
$384 \cdot 2 (d + 1)/(\varepsilon^2 \delta)$ rows (`projectionCostTailDim 2 d ε δ`), the Haar
sketch
$$\mathbf{S} = \sqrt{\lvert n\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}\,,$$
$\mathbf{Q}$ an $n \times k$ Haar frame, makes $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$
projection-cost-preserving sketch of $\mathbf{A}$ with constants $1 \mp \varepsilon$, for every
$\mathbf{A}$, except with probability $\delta$. The head is the OSE by JL and a net
(`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_jlDim_le`) at
$(\varepsilon/2, \delta/2)$, the tail the Haar JL moment at $p = 2$
(`NLAlib.hasJLMoment_of_hasLaw_haarFrame`, failure
$2(\lvert n\rvert - \lvert k\rvert)/(\lvert k\rvert(\lvert n\rvert + 2)\varepsilon_J^2) \le
2/(\lvert k\rvert\varepsilon_J^2)$, so $v = 2$). Incomparable with its $\log(1/\delta)$ twin
`NLAlib.hasProjectionCostPreserving_of_hasLaw_haarFrame_of_jlMomentDim_le` (rule 4); the
asymptotic form `NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_haarFrame` is proved
from the twin. [CohenElderMuscoMuscoPersu2015, proof of Theorem 12]; the Haar instance is not
stated there.
Result: haar-pcp -/
theorem hasProjectionCostPreserving_of_hasLaw_haarFrame_of_le_card
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n)
    {m : Type*} [Fintype m] (A : Matrix m n ℝ) (d : ℕ) (hε : 0 < ε) (hε2 : ε ≤ 2) (hδ : 0 < δ)
    (hk₁ : jlDim (2 * ε / 5) (δ / 2 / 21 ^ d) ≤ Fintype.card k)
    (hk₂ : projectionCostTailDim 2 d ε δ ≤ Fintype.card k) :
    HasProjectionCostPreserving (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) A d
      (1 - ε) (1 + ε) δ μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hpos : 0 < projectionCostTailDim 2 d ε δ := by
    rw [projectionCostTailDim_def]; positivity
  have hK : (0 : ℝ) < Fintype.card k := hpos.trans_le hk₂
  have : Nonempty k := Fintype.card_pos_iff.1 (by exact_mod_cast hK)
  have hN : (Fintype.card k : ℝ) ≤ Fintype.card n := Nat.cast_le.2 hk
  have hJ0 : 0 < ε / (8 * √((d : ℝ) + 1)) := by positivity
  have h3 := three_mul_div_le_of_projectionCostTailDim_le hε hδ hK hk₂
  have hδ' : 2 * ((Fintype.card n : ℝ) - Fintype.card k) /
      (Fintype.card k * (Fintype.card n + 2) * (ε / (8 * √((d : ℝ) + 1))) ^ 2) ≤
        2 / (Fintype.card k * (ε / (8 * √((d : ℝ) + 1))) ^ 2) := by
    have hKJ : 0 < (Fintype.card k : ℝ) * (ε / (8 * √((d : ℝ) + 1))) ^ 2 := by positivity
    rw [div_le_div_iff₀ (by positivity) hKJ]
    nlinarith [mul_le_mul_of_nonneg_right
      (show (Fintype.card n : ℝ) - Fintype.card k ≤ Fintype.card n + 2 by linarith) hKJ.le]
  have hS : AEMeasurable (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) μ :=
    (by fun_prop : Continuous fun M : Matrix n k ℝ =>
      √(Fintype.card n / Fintype.card k : ℝ) • Mᴴ).measurable.comp_aemeasurable hQ.aemeasurable
  exact hasProjectionCostPreserving_of_half
    (isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_jlDim_le hQ hk (half_pos hε)
      (by linarith) (half_pos hδ) (by rwa [show 4 * (ε / 2) / 5 = 2 * ε / 5 by ring]))
    (hasJLMoment_of_hasLaw_haarFrame hQ hk hJ0) hS hε le_rfl
    (div_nonneg (by linarith) (by positivity)) (by linarith) A

/-- **A Haar sketch is a projection-cost-preserving sketch**, $\log(1/\delta)$ size form: for
$\lvert k\rvert \le \lvert n\rvert$, $0 < \varepsilon \le 2$, $\delta > 0$, at
least <!-- value jlDim (2\varepsilon/5) (\delta/2/21^d) -->
$\log(2/(\delta/2/21^d))/((2\varepsilon/5)^2/4 - (2\varepsilon/5)^3/6)$ rows
(`jlDim (2 * ε / 5) (δ / 2 / 21 ^ d)`) and at
least <!-- value jlMomentDim (\varepsilon/(8\sqrt{d+1})) (\delta/6) -->
$128\max(2, \log(1/(\delta/6)))/(\varepsilon/(8\sqrt{d+1}))^2$ rows
(`jlMomentDim (ε / (8 * √(d + 1))) (δ / 6)`), the Haar sketch
$$\mathbf{S} = \sqrt{\lvert n\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}$$
makes
$\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$ projection-cost-preserving sketch of $\mathbf{A}$
with constants $1 \mp \varepsilon$, for every $\mathbf{A}$, except with probability $\delta$. The
tail is the JL moment `NLAlib.hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le` at
$\varepsilon/(8\sqrt{d+1})$, failure $\delta/6$. Incomparable with
`NLAlib.hasProjectionCostPreserving_of_hasLaw_haarFrame_of_le_card` (rule 4).
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12]; the Haar instance is not stated there.
Asymptotic form: `NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_haarFrame`.
Result: haar-pcp -/
theorem hasProjectionCostPreserving_of_hasLaw_haarFrame_of_jlMomentDim_le
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n)
    {m : Type*} [Fintype m] (A : Matrix m n ℝ) (d : ℕ) (hε : 0 < ε) (hε2 : ε ≤ 2) (hδ : 0 < δ)
    (hk₁ : jlDim (2 * ε / 5) (δ / 2 / 21 ^ d) ≤ Fintype.card k)
    (hk₂ : jlMomentDim (ε / (8 * √((d : ℝ) + 1))) (δ / 6) ≤ Fintype.card k) :
    HasProjectionCostPreserving (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) A d
      (1 - ε) (1 + ε) δ μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hJ1 := div_eight_mul_sqrt_le hε.le d
  have hS : AEMeasurable (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) μ :=
    (by fun_prop : Continuous fun M : Matrix n k ℝ =>
      √(Fintype.card n / Fintype.card k : ℝ) • Mᴴ).measurable.comp_aemeasurable hQ.aemeasurable
  exact hasProjectionCostPreserving_of_half
    (isObliviousSubspaceEmbedding_of_hasLaw_haarFrame_of_jlDim_le hQ hk (half_pos hε)
      (by linarith) (half_pos hδ) (by rwa [show 4 * (ε / 2) / 5 = 2 * ε / 5 by ring]))
    (hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le hQ hk (by positivity) (by linarith)
      (by positivity) hk₂) hS hε (le_max_left _ _) (by positivity) (by linarith) A

/-- **Haar rows suffice for a rank-$d$ projection-cost-preserving sketch**:
$$O((d+1)\log(1/\delta)/\varepsilon^2)$$
rows give one: for $\lvert k\rvert \le \lvert n\rvert$, the Haar sketch
$$\mathbf{S} = \sqrt{\lvert n\rvert/\lvert k\rvert}\,\mathbf{Q}^{\mathsf{H}}$$
makes
$\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$ projection-cost-preserving sketch with constants
$1 \mp \varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below absolute
constants; the constants come before every dimension. Proved from
`NLAlib.hasProjectionCostPreserving_of_hasLaw_haarFrame_of_jlMomentDim_le` with
$\varepsilon_0 = 1$ and $\delta \le 1/2$. [CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Asymptotic: NLAlib.hasProjectionCostPreserving_of_hasLaw_haarFrame_of_jlMomentDim_le
Result: haar-pcp -/
theorem exists_forall_hasProjectionCostPreserving_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m]
      [Fintype n] [DecidableEq k] (μ : Measure Ω) (Q : Ω → Matrix n k ℝ) (A : Matrix m n ℝ)
      (d : ℕ) (ε δ : ℝ),
      HasLaw Q (haarFrame n k) μ → Fintype.card k ≤ Fintype.card n →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (((d : ℝ) + 1) * Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasProjectionCostPreserving (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) A d
        (1 - ε) (1 + ε) δ μ := by
  refine ⟨98304, 1, by norm_num, one_pos, fun μ Q A d ε δ hQ hkn hε hε1 hδ hδ2 hk => ?_⟩
  have h2 := Real.log_two_le_log_one_div hδ hδ2
  have hd := natCast_le_two_mul_log d hδ hδ2
  have hL : 0 ≤ Real.log (1 / δ) := (Real.log_nonneg (by norm_num)).trans h2
  have h21 : (1 : ℝ) ≤ 21 ^ d := one_le_pow₀ (by norm_num)
  have hl : Real.log (2 / (δ / 2 / 21 ^ d)) =
      Real.log 2 + Real.log 2 + d * Real.log 21 + Real.log (1 / δ) := by
    rw [show 2 / (δ / 2 / 21 ^ d) = 2 * 2 * 21 ^ d * (1 / δ) by field_simp,
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_pow]
  have hd21 : (d : ℝ) * Real.log 21 ≤ d * (61 / 20) :=
    mul_le_mul_of_nonneg_left Real.log_twentyOne_le_sixtyOne_div_twenty (Nat.cast_nonneg d)
  refine hasProjectionCostPreserving_of_hasLaw_haarFrame_of_jlMomentDim_le hQ hkn A d hε
    (by linarith) hδ ((jlDim_le (by linarith) (by positivity)
      ((div_le_self (by positivity) h21).trans (by linarith))).trans (le_trans ?_ hk))
    (jlMomentDim_le_of_mul_le hε hδ hδ2 hk)
  rw [hl, show 12 * (Real.log 2 + Real.log 2 + d * Real.log 21 + Real.log (1 / δ)) /
      (2 * ε / 5) ^ 2 = 75 * (Real.log 2 + Real.log 2 + d * Real.log 21 + Real.log (1 / δ)) /
        ε ^ 2 by field_simp; ring, mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) d) hL]

end Haar

end NLAlib
