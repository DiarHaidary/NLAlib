/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Random.RangeFinder
public import NLAlib.LowRank.Structural.EarlyTruncation
public import NLAlib.RandomMatrix.Gaussian.ClippedInverseMoments
public import NLAlib.Sketching.Gaussian.Gaussian
public import NLAlib.Regression.SketchAndSolve
public import NLAlib.Sketching.Properties.MatrixMultiplication

/-!
# Early truncation in expectation with Gaussian test matrices

The early-truncated randomized SVD $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$
(`NLAlib.earlyTruncatedRSVD`) projects $\mathbf{A}$ onto the range of a best rank-$k$
approximation of the sketch $\mathbf{A}\mathbf{\Omega}$; early-truncated generalized Nyström
$\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)$
(`NLAlib.earlyTruncatedGeneralizedNystrom`) completes it by a sketch-and-solve step with the
co-range test matrix $\mathbf{\Psi}$. With standard Gaussian test matrices:

* the early-truncated randomized SVD has expected squared error at most a factor times the optimal
  one, the factor tending to $1$, and at most $1 + \varepsilon$ with
  $\ell \ge 900k/\varepsilon^2$ samples. The proof integrates the structural bound
  `NLAlib.IsSubspaceInjection.frobNorm_sub_mul_sq_le` with the clipped head constant, whose
  inverse moments are
  `NLAlib.integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix`;
* for a Gaussian $\mathbf{\Psi}$ independent of $\mathbf{\Omega}$ the completion costs exactly the
  Gaussian completion factor at the rank of the truncated sketch, for any law of
  $\mathbf{\Omega}$, so every bound on the early-truncated randomized SVD becomes one on
  early-truncated generalized Nyström with $p = O(k/\varepsilon)$ co-range samples;
* together, early-truncated generalized Nyström reaches relative error $1 + \varepsilon$ with
  $\ell \ge 3600k/\varepsilon^2$ and $p \ge k + 1 + (2 + \varepsilon)k/\varepsilon$, rank at most
  $k$, one pass.

The twins with a Haar co-range test matrix are in `NLAlib.LowRank.Gaussian.EarlyTruncationHaar`.
Design: `docs/design/LowRank-S6.md` §3.6, §8 items 4, 13 and 17. Real throughout.

## Main results

* `NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix`:
  a fixed range test matrix.
* [Gaussian completion bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix):
  completion for any law of the range test matrix.
* [relative-error composition bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le):
  relative error from an expected bound on early-truncated randomized SVD.
* `NLAlib.earlyTruncatedRSVDFactor k l`: the factor, at
  present <!-- value earlyTruncatedRSVDFactor k \ell -->
  $$\frac{(1 + \sqrt{2k/\ell})\bigl((1 - \sqrt{k/\ell})^{-2} + 10/\sqrt{\ell}\bigr) +
  \frac{1}{4}\sqrt{k/\ell}\sqrt{1 + 2/(k \ell)}\sqrt{(1 - \sqrt{k/\ell})^{-8} +
  263/\sqrt{\ell}}}{1 - 4\sqrt{k/\ell}}\,,$$
  with `NLAlib.one_le_earlyTruncatedRSVDFactor` and `NLAlib.earlyTruncatedRSVDFactor_le_one_add`.
* `NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`:
  the early-truncated randomized SVD; its asymptotic form is
  `NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`.
* [relative-error bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix):
  early-truncated generalized Nyström with $\varepsilon^{-2}$ range and
  $\varepsilon^{-1}$ co-range samples; its asymptotic form is
  [asymptotic form](https://nla-lib.org/explore/#d/NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_of_hasLaw_gaussianMatrix).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-! ### A fixed range test matrix -/

/-- The squared error of early-truncated generalized Nyström with a fixed range test matrix and
a Gaussian co-range test matrix is integrable for $k + 2 \le p$. -/
private theorem integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_fixed
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2) μ := by
  classical
  have hr := rank_truncatedSVD_le (A * X₀) k
  simp only [sub_earlyTruncatedGeneralizedNystrom]
  exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hΨ) (truncatedSVD (A * X₀) k) (by omega) A

/-- **Early-truncated generalized Nyström conditionally on the range test matrix**: for a fixed
$\mathbf{\Omega}$, a standard Gaussian $m \times p$ co-range test matrix $\mathbf{\Psi}$,
$q = \operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k \le k$ and
$k + 2 \le p$, <!-- value gaussianProjectionFactor q p -->
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{q}{p - q - 1}\Bigr)\|\mathbf{A}-
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2\,,$$
the factor at the actual rank $q$. Proved without a literature
source, as a composition: the completion step is [EpperlyWebber2026, Theorem 2.1]; the algorithm
is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) {k : ℕ}
    (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A X₀ (Ψ ω) k) ^ 2 ∂μ =
      gaussianProjectionFactor (truncatedSVD (A * X₀) k).rank (Fintype.card p) *
        frobNorm (A - earlyTruncatedRSVD A X₀ k) ^ 2 := by
  classical
  have hr := rank_truncatedSVD_le (A * X₀) k
  simp only [sub_earlyTruncatedGeneralizedNystrom, sub_earlyTruncatedRSVD]
  exact integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hΨ) (truncatedSVD (A * X₀) k) (by omega) A

/-! ### Any law of the range test matrix -/

/-- The completion factor at the rank of the truncated sketch is measurable in the range test
matrix. -/
private theorem measurable_gaussianProjectionFactor_rank_truncatedSVD (A : Matrix m n ℝ) (k c : ℕ) :
    Measurable fun x : Matrix n l ℝ =>
      gaussianProjectionFactor (truncatedSVD (A * x) k).rank c :=
  (measurable_from_nat (f := fun q => gaussianProjectionFactor q c)).comp
    (measurable_rank.comp ((measurable_truncatedSVD k).comp
      (measurable_const.matrix_mul measurable_id)))

/-- The completion factor at the rank of the truncated sketch lies in $[1, 1 + p]$. -/
private theorem gaussianProjectionFactor_rank_truncatedSVD_mem (A : Matrix m n ℝ)
    (x : Matrix n l ℝ) {k c : ℕ} (h : k + 2 ≤ c) :
    1 ≤ gaussianProjectionFactor (truncatedSVD (A * x) k).rank c ∧
      gaussianProjectionFactor (truncatedSVD (A * x) k).rank c ≤ 1 + c := by
  have hq : (truncatedSVD (A * x) k).rank + 2 ≤ c := by
    have := rank_truncatedSVD_le (A * x) k
    omega
  exact ⟨one_le_gaussianProjectionFactor hq, gaussianProjectionFactor_le_one_add hq⟩

/-- The right side of the conditional identity, integrated over $\mathbf{\Omega}$, is
integrable. -/
private theorem integrable_gaussianProjectionFactor_mul_earlyTruncatedRSVD [IsFiniteMeasure μ]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω =>
      gaussianProjectionFactor (truncatedSVD (A * X ω) k).rank (Fintype.card p) *
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) μ := by
  refine (integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX k).bdd_mul
    (c := 1 + Fintype.card p)
    ((measurable_gaussianProjectionFactor_rank_truncatedSVD A k _).comp_aemeasurable
      hX).aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  obtain ⟨h1, h2⟩ := gaussianProjectionFactor_rank_truncatedSVD_mem A (X ω) hkp
  rwa [Real.norm_of_nonneg (zero_le_one.trans h1)]

/-- The conditional identity as lower integrals, over the independent pair. -/
private theorem lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    ∫⁻ ω, ENNReal.ofReal (frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2)
        ∂μ =
      ∫⁻ ω, ENNReal.ofReal
        (gaussianProjectionFactor (truncatedSVD (A * X ω) k).rank (Fintype.card p) *
          frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2) ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  refine (hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX hΨ
    (F := fun q : Matrix n l ℝ × Matrix m p ℝ =>
      frobNorm (A - earlyTruncatedGeneralizedNystrom A q.1 q.2 k) ^ 2)
    ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_earlyTruncatedGeneralizedNystrom A k))).pow_const 2)
    (fun _ => sq_nonneg _) (ae_of_all _ fun ω =>
      integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_fixed A (X ω) hid hkp)).trans
    (lintegral_congr fun ω => congrArg ENNReal.ofReal
      (integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix A (X ω)
        hid hkp))

set_option linter.style.longLine false in
-- The theorem's name alone exceeds 100 characters.
/-- **Early-truncated generalized Nyström = early-truncated randomized SVD × completion**: for any
law of $\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$ and
$k + 2 \le p$, <!-- value gaussianProjectionFactor k p -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{p - k - 1}\Bigr)\,\mathbb{E}\|\mathbf{A}-
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2\,.$$
Every bound on the early-truncated randomized SVD (the subspace-embedding and
projection-cost-preserving routes, and its expectation) becomes one on early-truncated
generalized Nyström. Proved without a literature source, as a composition:
[EpperlyWebber2026, Theorem 2.1] for the completion; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card p) *
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hR := integrable_gaussianProjectionFactor_mul_earlyTruncatedRSVD A hX hkp
  have hR0 : 0 ≤ᵐ[μ] fun ω =>
      gaussianProjectionFactor (truncatedSVD (A * X ω) k).rank (Fintype.card p) *
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 :=
    ae_of_all _ fun ω => mul_nonneg (zero_le_one.trans
      (gaussianProjectionFactor_rank_truncatedSVD_mem A (X ω) hkp).1) (sq_nonneg _)
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (aestronglyMeasurable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX
        hΨ.aemeasurable k),
    lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX hΨ hXΨ hkp,
    ← integral_eq_lintegral_of_nonneg_ae hR0 hR.aestronglyMeasurable, ← integral_const_mul]
  refine integral_mono_of_nonneg hR0
    ((integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX k).const_mul _)
    (ae_of_all _ fun ω => ?_)
  exact mul_le_mul_of_nonneg_right (gaussianProjectionFactor_le_gaussianProjectionFactor
    (rank_truncatedSVD_le _ k) hkp) (sq_nonneg _)

/-- The squared error of $\mathsf{earlyTruncatedGeneralizedNystrom}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}, k)$ is integrable for any law of $\mathbf{\Omega}$ independent of a standard
Gaussian $\mathbf{\Psi}$ and $k + 2 \le p$. -/
theorem integrable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} (hkp : k + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2)
      μ := by
  have := hΨ.isProbabilityMeasure
  refine ⟨aestronglyMeasurable_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX
    hΨ.aemeasurable k, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _),
    lintegral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq A hX hΨ hXΨ hkp]
  exact (integrable_gaussianProjectionFactor_mul_earlyTruncatedRSVD A hX hkp).lintegral_lt_top

/-- The arithmetic of the $(1+\varepsilon)$ form: for $k \ge 1$, $\varepsilon > 0$ and
$p \ge k + 1 + (2+\varepsilon)k/\varepsilon$, $k + 2 \le p$ and
$(1 + \varepsilon/2)\,(1 + k/(p - k - 1)) \le 1 + \varepsilon$. -/
private theorem one_add_half_mul_gaussianProjectionFactor_le {k c : ℕ} {ε : ℝ} (hk : 1 ≤ k)
    (hε : 0 < ε) (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ c) :
    k + 2 ≤ c ∧ (1 + ε / 2) * gaussianProjectionFactor k c ≤ 1 + ε := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < (2 + ε) * k / ε := by positivity
  have hd : (2 + ε) * k / ε ≤ (c : ℝ) - k - 1 := by linarith
  have hd0 : 0 < (c : ℝ) - k - 1 := hpos.trans_le hd
  have hkc : k + 2 ≤ c := by
    have h1 : (1 : ℝ) < (2 + ε) * k / ε := by
      rw [lt_div_iff₀ hε]; nlinarith
    have : (k : ℝ) + 2 < c + 1 := by linarith
    have : k + 2 < c + 1 := by exact_mod_cast this
    omega
  refine ⟨hkc, ?_⟩
  rw [gaussianProjectionFactor_def]
  have hq : (k : ℝ) / ((c : ℝ) - k - 1) ≤ ε / (2 + ε) := by
    rw [div_le_div_iff₀ hd0 (by positivity)]
    rw [div_le_iff₀ hε] at hd
    nlinarith
  calc (1 + ε / 2) * (1 + (k : ℝ) / ((c : ℝ) - k - 1)) ≤ (1 + ε / 2) * (1 + ε / (2 + ε)) := by
        gcongr
    _ = 1 + ε := by field_simp; ring

set_option linter.style.longLine false in
-- The theorem's name alone exceeds 100 characters.
/-- **Early-truncated generalized Nyström reaches relative error $1 + \varepsilon$ from a bound
on the early-truncated randomized SVD**: for any law of
$\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$, if the early-truncated
randomized SVD with the same $\mathbf{\Omega}$ has expected error at most
$(1 + \varepsilon/2)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ and
$p \ge k + 1 + (2+\varepsilon)k/\varepsilon$, then
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The hypothesis holds for a Gaussian $\mathbf{\Omega}$ with $\ell \ge 3600k/\varepsilon^2$ columns
(`NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`);
in this form it composes with any other bound on the early-truncated randomized SVD. Proved
without a literature source; the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ Fintype.card p)
    (hRSVD : ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      (1 + ε / 2) * frobNorm (A - truncatedSVD A k) ^ 2) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hΨ.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) (ψ : Matrix m p ℝ) :
        earlyTruncatedGeneralizedNystrom A x ψ 0 = 0 := by
      simp only [earlyTruncatedGeneralizedNystrom, truncatedSVD_zero, obliqueProjector,
        Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  obtain ⟨hkp, hfac⟩ := one_add_half_mul_gaussianProjectionFactor_le hk hε hp
  have h1 :=
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
      A hX hΨ hXΨ hkp
  have hg : 0 ≤ gaussianProjectionFactor k (Fintype.card p) :=
    zero_le_one.trans (one_le_gaussianProjectionFactor hkp)
  calc _ ≤ _ := h1
    _ ≤ gaussianProjectionFactor k (Fintype.card p) *
          ((1 + ε / 2) * frobNorm (A - truncatedSVD A k) ^ 2) :=
        mul_le_mul_of_nonneg_left hRSVD hg
    _ = ((1 + ε / 2) * gaussianProjectionFactor k (Fintype.card p)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by ring
    _ ≤ (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 :=
        mul_le_mul_of_nonneg_right hfac (sq_nonneg _)

/-! ### The early-truncated randomized SVD factor -/

/-- **The early-truncated randomized SVD factor**: the multiplier of
$\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ in the expected error of the
early-truncated randomized SVD with a standard Gaussian $n \times \ell$ test matrix
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`), at
present <!-- value earlyTruncatedRSVDFactor k \ell -->
$$\frac{(1 + \sqrt{2k/\ell})\bigl((1 - \sqrt{k/\ell})^{-2} + 10/\sqrt{\ell}\bigr) +
\frac{1}{4}\sqrt{k/\ell}\sqrt{1 + 2/(k \ell)}\sqrt{(1 - \sqrt{k/\ell})^{-8} +
263/\sqrt{\ell}}}{1 - 4\sqrt{k/\ell}}\,.$$
It tends to $1$ as $\ell/k \to \infty$ and $\ell \to \infty$, and is at most $1 + \varepsilon$ at
$\ell \ge 900k/\varepsilon^2$ (`NLAlib.earlyTruncatedRSVDFactor_le_one_add`). Source value: none;
no published statement has an expectation bound for the early-truncated randomized SVD. Value
proved: as displayed, the constants of this library's proof (the $10$ and $263$ are
`NLAlib.gaussianClippedInvMomentConstant_one_le_10` and
`NLAlib.gaussianClippedInvMomentConstant_four_le_263`; the $4\sqrt{k/\ell}$ is the Young
parameter of the structural bound). Consumers use `NLAlib.one_le_earlyTruncatedRSVDFactor` and
`NLAlib.earlyTruncatedRSVDFactor_le_one_add`. Junk for $16k \ge \ell$, where the denominator is
at most $0$; the theorems carry `100 * k ≤ l`. Proved without a literature source. -/
noncomputable irreducible_def earlyTruncatedRSVDFactor (k l : ℕ) : ℝ :=
  ((1 + √(2 * k / l)) * (((1 - √(k / l)) ^ 2)⁻¹ + 10 / √l) +
      √(k / l) / 4 * √(1 + 2 / (k * l)) * √(((1 - √(k / l)) ^ 8)⁻¹ + 263 / √l)) /
    (1 - 4 * √(k / l))

/-- The sizes in the factor: for $100k \le \ell$, $y = \sqrt{k/\ell}$ satisfies
$0 \le y \le 1/10$. -/
private theorem sqrt_div_le_tenth {k l : ℕ} (h : 100 * k ≤ l) :
    0 ≤ √((k : ℝ) / l) ∧ √((k : ℝ) / l) ≤ 1 / 10 := by
  refine ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.2 ⟨by norm_num, ?_⟩⟩
  rcases Nat.eq_zero_or_pos l with hl | hl
  · simp [hl]
  have hl' : (0 : ℝ) < l := by exact_mod_cast hl
  have h' : 100 * (k : ℝ) ≤ l := by exact_mod_cast h
  rw [div_le_iff₀ hl']
  linarith

/-- The early-truncated randomized SVD factor is at least $1$: for
$100k \le \ell$, <!-- value earlyTruncatedRSVDFactor k \ell -->
$$1 \le \frac{(1 + \sqrt{2k/\ell})\bigl((1 - \sqrt{k/\ell})^{-2} + 10/\sqrt{\ell}\bigr) +
\frac{1}{4}\sqrt{k/\ell}\sqrt{1 + 2/(k \ell)}\sqrt{(1 - \sqrt{k/\ell})^{-8} +
263/\sqrt{\ell}}}{1 - 4\sqrt{k/\ell}}\,.$$ -/
theorem one_le_earlyTruncatedRSVDFactor {k l : ℕ} (h : 100 * k ≤ l) :
    1 ≤ earlyTruncatedRSVDFactor k l := by
  obtain ⟨hy0, hy⟩ := sqrt_div_le_tenth h
  rw [earlyTruncatedRSVDFactor_def]
  set y := √((k : ℝ) / l)
  have hd0 : 0 < 1 - 4 * y := by linarith
  have h1y : 0 < 1 - y := by linarith
  have hinv : 1 ≤ ((1 - y) ^ 2)⁻¹ :=
    one_le_inv₀ (by positivity) |>.2 (pow_le_one₀ h1y.le (by linarith))
  rw [le_div_iff₀ hd0, one_mul]
  have h2 : 0 ≤ √(2 * (k : ℝ) / l) := Real.sqrt_nonneg _
  have h3 : 0 ≤ 10 / √(l : ℝ) := by positivity
  have h4 : 0 ≤ y / 4 * √(1 + 2 / ((k : ℝ) * l)) * √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ)) := by
    positivity
  nlinarith

/-- The early-truncated randomized SVD factor at $\ell \ge 900k/\varepsilon^2$: for $k \ge 1$
and $0 < \varepsilon \le 1$, <!-- value earlyTruncatedRSVDFactor k \ell -->
$$\frac{(1 + \sqrt{2k/\ell})\bigl((1 - \sqrt{k/\ell})^{-2} + 10/\sqrt{\ell}\bigr) +
\frac{1}{4}\sqrt{k/\ell}\sqrt{1 + 2/(k \ell)}\sqrt{(1 - \sqrt{k/\ell})^{-8} +
263/\sqrt{\ell}}}{1 - 4\sqrt{k/\ell}} \le 1 + \varepsilon\,,$$
an explicit comparison that stays true when the factor improves. -/
theorem earlyTruncatedRSVDFactor_le_one_add {k l : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hl : 900 * (k : ℝ) ≤ ε ^ 2 * l) : earlyTruncatedRSVDFactor k l ≤ 1 + ε := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl0 : (0 : ℝ) < l := by
    by_contra h0
    have : (l : ℝ) = 0 := le_antisymm (not_lt.1 h0) (Nat.cast_nonneg _)
    rw [this, mul_zero] at hl
    linarith
  set t := ε / 30 with ht
  have ht0 : 0 < t := by positivity
  have hkl : (k : ℝ) / l ≤ t ^ 2 := by
    rw [div_le_iff₀ hl0, ht]; nlinarith
  have hl1 : 1 / (l : ℝ) ≤ t ^ 2 := by
    calc 1 / (l : ℝ) ≤ (k : ℝ) / l := div_le_div_of_nonneg_right hk' hl0.le
      _ ≤ t ^ 2 := hkl
  -- the three square roots and the inverse root
  have hy : √((k : ℝ) / l) ≤ t := Real.sqrt_le_iff.2 ⟨ht0.le, hkl⟩
  have hy2 : √(2 * (k : ℝ) / l) ≤ 3 / 2 * t := Real.sqrt_le_iff.2 ⟨by positivity, by
    rw [mul_div_assoc]; nlinarith⟩
  have hsl : 1 / √(l : ℝ) ≤ t := by
    rw [div_le_iff₀ (Real.sqrt_pos.2 hl0)]
    have h1 : 1 ≤ t ^ 2 * l := by rwa [div_le_iff₀ hl0] at hl1
    have h2 : √(t ^ 2 * l) = t * √(l : ℝ) := by
      rw [Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht0.le]
    calc (1 : ℝ) = √1 := Real.sqrt_one.symm
      _ ≤ √(t ^ 2 * l) := Real.sqrt_le_sqrt h1
      _ = t * √(l : ℝ) := h2
  have h10 : 10 / √(l : ℝ) ≤ 10 * t := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsl (by norm_num)
  have h263 : 263 / √(l : ℝ) ≤ 263 * t := by
    rw [div_eq_mul_one_div]; exact mul_le_mul_of_nonneg_left hsl (by norm_num)
  have hkl2 : 2 / ((k : ℝ) * l) ≤ 2 / 900 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have hε2 : ε ^ 2 ≤ 1 := by nlinarith
    have hl900 : (900 : ℝ) ≤ l := by nlinarith
    have : (900 : ℝ) ≤ k * l := by nlinarith
    linarith
  have hs2 : √(1 + 2 / ((k : ℝ) * l)) ≤ 1.01 := Real.sqrt_le_iff.2 ⟨by norm_num, by
    nlinarith [hkl2]⟩
  -- the two inverse powers
  set y := √((k : ℝ) / l)
  have h1y : 29 / 30 ≤ 1 - y := by linarith
  have hinv2 : ((1 - y) ^ 2)⁻¹ ≤ 1 + 2.2 * t := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : (1 - t) ^ 2 ≤ (1 - y) ^ 2 := pow_le_pow_left₀ (by linarith) (by linarith) 2
    nlinarith
  have hinv8 : ((1 - y) ^ 8)⁻¹ ≤ 1.32 := by
    rw [inv_le_iff_one_le_mul₀ (by positivity)]
    have : ((29 : ℝ) / 30) ^ 8 ≤ (1 - y) ^ 8 := pow_le_pow_left₀ (by norm_num) h1y 8
    nlinarith
  have hs8 : √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ)) ≤ 3.2 := Real.sqrt_le_iff.2 ⟨by norm_num, by
    nlinarith⟩
  -- the numerator and the denominator
  have hnum : (1 + √(2 * (k : ℝ) / l)) * (((1 - y) ^ 2)⁻¹ + 10 / √(l : ℝ)) +
      y / 4 * √(1 + 2 / ((k : ℝ) * l)) * √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ)) ≤
      1 + 15.2 * t := by
    have e1 : (1 + √(2 * (k : ℝ) / l)) * (((1 - y) ^ 2)⁻¹ + 10 / √(l : ℝ)) ≤
        (1 + 3 / 2 * t) * (1 + 12.2 * t) := by
      apply mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
    have e2 : y / 4 * √(1 + 2 / ((k : ℝ) * l)) * √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ)) ≤
        t / 4 * 1.01 * 3.2 := by
      apply mul_le_mul (mul_le_mul (by linarith) hs2 (Real.sqrt_nonneg _) (by positivity)) hs8
        (Real.sqrt_nonneg _) (by positivity)
    nlinarith
  rw [earlyTruncatedRSVDFactor_def, div_le_iff₀ (by linarith)]
  nlinarith

/-! ### The early-truncated randomized SVD in expectation -/

/-- **The structural bound at the normalised sketch**, pointwise: for a frame $\mathbf{Z}$ of
$k \ge 1$ columns with $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \llbracket\mathbf{A}
\rrbracket_k$, a fixed $\mathbf{\Omega}$, $c > 0$, $0 < a \le \min\{1,
c^2\sigma_{k-1}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})^2\}$ and $0 < \theta < 1$, with
$\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$ and $\mathbf{S} = c\mathbf{\Omega}$,
$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
((\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w)/(1 - \theta))a^{-1} +
(\chi^2/(\theta(1-\theta)))a^{-2}$, $w = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}
\mathbf{E}^{\mathsf{H}} - \mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$,
$\chi = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{Z}\|_{\mathsf{F}}$. The projector is
that of the unnormalised sketch, so no scale equivariance of the truncation is needed. -/
private theorem frobNorm_sub_earlyTruncatedRSVD_sq_le_inv {A : Matrix m n ℝ} {k : ℕ}
    (hk : 1 ≤ k) {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z)
    (hAZ : A * Z * Zᴴ = truncatedSVD A k) (X₀ : Matrix n l ℝ) {c a θ : ℝ} (hc : 0 < c)
    (ha : 0 < a) (ha1 : a ≤ 1) (haσ : a ≤ c ^ 2 * singularValues (X₀ᴴ * Z) (k - 1) ^ 2)
    (hθ : 0 < θ) (hθ1 : θ < 1) :
    frobNorm (A - earlyTruncatedRSVD A X₀ k) ^ 2 ≤
      (frobNorm (A - truncatedSVD A k) ^ 2 + √(k : ℝ) *
          frobNorm ((A - truncatedSVD A k) * (c • X₀) * (c • X₀)ᴴ * (A - truncatedSVD A k)ᴴ -
            (A - truncatedSVD A k) * (A - truncatedSVD A k)ᴴ)) / (1 - θ) * a⁻¹ +
        frobNorm ((A - truncatedSVD A k) * (c • X₀) * (c • X₀)ᴴ * Z) ^ 2 / (θ * (1 - θ)) *
          a⁻¹ ^ 2 := by
  classical
  have hinj : IsSubspaceInjection (c • X₀)ᴴ Z a := by
    rw [hZ.isSubspaceInjection_iff_le_singularValues_sq (j := k - 1)
      (by rw [Fintype.card_fin]; omega), Matrix.conjTranspose_smul, star_trivial,
      Matrix.smul_mul, singularValues_smul, Real.norm_of_nonneg hc.le, mul_pow]
    exact haσ
  have hP := isStarProjection_rangeProjector (truncatedSVD (A * X₀) k)
  have hPk : (rangeProjector (truncatedSVD (A * X₀) k)).rank ≤ k :=
    (rank_rangeProjector _).trans_le (rank_truncatedSVD_le _ k)
  have hopt : frobNorm (A * (c • X₀) - rangeProjector (truncatedSVD (A * X₀) k) *
      (A * (c • X₀))) ≤ frobNorm ((A - A * Z * Zᴴ) * (c • X₀)) := by
    have hr : (A * Z * Zᴴ * X₀).rank ≤ k :=
      ((Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_left _ _).trans
        (Matrix.rank_le_card_width _))).trans (by rw [Fintype.card_fin])
    simp only [Matrix.mul_smul, ← smul_sub, frobNorm_smul, Real.norm_of_nonneg hc.le]
    refine mul_le_mul_of_nonneg_left ?_ hc.le
    rw [rangeProjector_truncatedSVD_mul, Matrix.sub_mul]
    exact frobNorm_sub_truncatedSVD_le_of_rank_le (A * X₀) hr
  have hEZ : (A - A * Z * Zᴴ) * Z = 0 := by
    rw [Matrix.sub_mul, Matrix.mul_assoc (A * Z), hZ.conjTranspose_mul_self, Matrix.mul_one,
      sub_self]
  have h := hinj.frobNorm_sub_mul_sq_le hZ ha ha1 hθ hθ1 hP hPk hopt
  rw [hEZ, sub_zero, hAZ] at h
  refine h.trans_eq ?_
  have h1θ : 1 - θ ≠ 0 := by linarith
  field_simp

/-- The head of a Gaussian test matrix in a frame $\mathbf{Z}$,
$\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z}$, is a standard Gaussian $\ell \times k$ matrix. -/
private theorem hasLaw_conjTranspose_mul_frame (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z) :
    HasLaw (fun ω => (X ω)ᴴ * Z) (gaussianMatrix l (Fin k)) μ :=
  hasLaw_mul_const_of_hasLaw_gaussianMatrix (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX) hZ

/-- The clipped inverse power of the head is integrable for $2r + k \le \ell$. -/
private theorem integrable_min_one_inv_pow (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : 1 ≤ k) {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z) {r : ℕ}
    (hr : 2 * r + k ≤ Fintype.card l) :
    Integrable (fun ω =>
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ r) μ :=
  integrable_min_one_singularValues_sq_div_inv_pow_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_mul_frame hX hZ) (by rw [Fintype.card_fin]; omega)
    (by rwa [Fintype.card_fin])

/-- The clipped inverse of the head is a measurable function of the head. -/
private theorem measurable_min_one_inv {k : ℕ} (L : ℝ) :
    Measurable fun H : Matrix (Fin k) l ℝ => (min 1 (singularValues Hᴴ (k - 1) ^ 2 / L))⁻¹ :=
  (measurable_const.min ((((measurable_singularValues (k - 1)).comp
    (continuous_id.matrix_conjTranspose.measurable)).pow_const 2).div_const L)).inv

/-- The tail–tail term of the structural bound in expectation: with
$w = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$, $\mathbf{S} = \ell^{-1/2}\mathbf{\Omega}$, a
function of the tail block $\mathbf{V}^{\mathsf{H}}\mathbf{\Omega}$, and $u$ the clipped inverse of
the head, independent of it, $\mathbb{E}[wu] = \mathbb{E}w\,\mathbb{E}u \le
\sqrt{2/\ell}\,\|\mathbf{E}\|_{\mathsf{F}}^2\,\mathbb{E}u$ (approximate matrix multiplication at
$p = 2$). -/
private theorem integral_frobNorm_mul_inv_le {q : Type*} [Fintype q] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k)
    (hkl : 2 + k ≤ Fintype.card l) {Z : Matrix n (Fin k) ℝ} {V : Matrix n q ℝ}
    (hZ : HasOrthonormalCols Z) (hV : HasOrthonormalCols V) (hZV : Zᴴ * V = 0)
    {E : Matrix m n ℝ} (hEV : E * V * Vᴴ = E) :
    Integrable (fun ω => frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Eᴴ - E * Eᴴ) *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹) μ ∧
    ∫ ω, frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Eᴴ - E * Eᴴ) *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ∂μ ≤
      √(2 / Fintype.card l) * frobNorm E ^ 2 *
        ∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ∂μ := by
  have := hX.isProbabilityMeasure
  have hl0 : 0 < Fintype.card l := by omega
  have : Nonempty l := Fintype.card_pos_iff.1 hl0
  set L := (Fintype.card l : ℝ) with hL
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast hl0
  set c := (√L)⁻¹ with hc
  set U : Matrix (Fin k) l ℝ → ℝ := fun H => (min 1 (singularValues Hᴴ (k - 1) ^ 2 / L))⁻¹
  set W : Matrix q l ℝ → ℝ := fun G =>
    frobNorm ((E * V) * (c • G) * ((E * V) * (c • G))ᴴ - E * Eᴴ)
  have hU : Measurable U := measurable_min_one_inv L
  have hW : Measurable W := by
    have hSG : Measurable fun G : Matrix q l ℝ => (E * V) * (c • G) :=
      measurable_const.matrix_mul (measurable_id.const_smul c)
    exact measurable_frobNorm.comp ((hSG.matrix_mul
      ((continuous_id.matrix_conjTranspose.measurable).comp hSG)).matrix_sub measurable_const)
  have hw (ω : Ω) : frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Eᴴ - E * Eᴴ) = W (Vᴴ * X ω) := by
    have e : E * (c • X ω) = (E * V) * (c • (Vᴴ * X ω)) := by
      rw [Matrix.mul_smul, Matrix.mul_smul, ← Matrix.mul_assoc, hEV]
    simp only [W]
    rw [← e, Matrix.conjTranspose_mul, ← Matrix.mul_assoc]
  have hu (ω : Ω) : (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ = U (Zᴴ * X ω) := by
    simp only [U, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hVZ : Vᴴ * Z = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose (Vᴴ * Z), Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hZV, Matrix.conjTranspose_zero]
  have hind : IndepFun (fun ω => W (Vᴴ * X ω)) (fun ω => U (Zᴴ * X ω)) μ :=
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV hZ hVZ).comp hW hU
  have hXm := hX.aemeasurable
  have hWm : AEMeasurable (fun ω => W (Vᴴ * X ω)) μ :=
    hW.comp_aemeasurable (measurable_const.matrix_mul measurable_id |>.comp_aemeasurable hXm)
  have hUm : AEMeasurable (fun ω => U (Zᴴ * X ω)) μ :=
    hU.comp_aemeasurable (measurable_const.matrix_mul measurable_id |>.comp_aemeasurable hXm)
  -- the second moment of `w`, by approximate matrix multiplication
  have hXt := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hX
  have hJL := hasJLMoment_of_hasLaw_gaussianMatrix hXt (ε := 1) one_pos
  have hSm : AEMeasurable (fun ω => (√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) μ :=
    hXt.aemeasurable.const_smul ((√(Fintype.card l : ℝ))⁻¹)
  have he (ω : Ω) : frobNorm (Eᴴᴴ * ((√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ)ᴴ *
      ((√(Fintype.card l : ℝ))⁻¹ • (X ω)ᴴ) * Eᴴ - Eᴴᴴ * Eᴴ) ^ (2 : ℝ) =
      W (Vᴴ * X ω) ^ 2 := by
    rw [← hw, Real.rpow_two]
    simp only [Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul, star_trivial, hc,
      hL]
  have hint2 := hJL.integrable_frobNorm_conjTranspose_mul_sub_rpow le_rfl hSm Eᴴ Eᴴ
  have hamm := hJL.integral_frobNorm_conjTranspose_mul_sub_rpow_le zero_le_one le_rfl hSm Eᴴ Eᴴ
  simp only [he] at hint2 hamm
  have hmem : MemLp (fun ω => W (Vᴴ * X ω)) 2 μ :=
    (memLp_two_iff_integrable_sq hWm.aestronglyMeasurable).2 hint2
  have hWi : Integrable (fun ω => W (Vᴴ * X ω)) μ := hmem.integrable one_le_two
  have hUi : Integrable (fun ω => U (Zᴴ * X ω)) μ := by
    have h := integrable_min_one_inv_pow hX hk hZ (r := 1) (by omega)
    simp only [pow_one] at h
    exact h.congr (ae_of_all _ fun ω => hu ω)
  have hEw : ∫ ω, W (Vᴴ * X ω) ∂μ ≤ √(2 / L) * frobNorm E ^ 2 := by
    have hvar := variance_nonneg (fun ω => W (Vᴴ * X ω)) μ
    rw [variance_eq_sub hmem] at hvar
    simp only [Pi.pow_apply] at hvar
    have h2 : ∫ ω, W (Vᴴ * X ω) ^ 2 ∂μ ≤ (√(2 / L) * frobNorm E ^ 2) ^ 2 := by
      refine hamm.trans_eq ?_
      rw [frobNorm_conjTranspose, mul_pow, Real.sq_sqrt (by positivity), Real.rpow_two]
      ring
    have h0 : 0 ≤ ∫ ω, W (Vᴴ * X ω) ∂μ ∨ ∫ ω, W (Vᴴ * X ω) ∂μ < 0 := le_or_gt _ _
    rcases h0 with h0 | h0
    · exact (pow_le_pow_iff_left₀ h0 (by positivity) two_ne_zero).1 (by linarith)
    · exact h0.le.trans (by positivity)
  simp only [hw, hu]
  refine ⟨hind.integrable_mul hWi hUi, ?_⟩
  rw [hind.integral_fun_mul_eq_mul_integral hWm.aestronglyMeasurable hUm.aestronglyMeasurable]
  exact mul_le_mul_of_nonneg_right hEw (integral_nonneg fun ω => inv_nonneg.2
    (le_min zero_le_one (div_nonneg (sq_nonneg _) hL0.le)))

/-- The Gaussian-product identity of `integral_frobNorm_sq_mul_inv_sq_le`: for
$\mathbf{E}\mathbf{V}\mathbf{V}^{\mathsf{H}} = \mathbf{E}$ and $u \ge 0$,
$\|\mathbf{E}(c\mathbf{Y})(c\mathbf{Y})^{\mathsf{H}}\mathbf{Z}\|_{\mathsf{F}}^2u^2 =
\|\mathbf{E}\mathbf{V}(\mathbf{V}^{\mathsf{H}}\mathbf{Y})\,c^2u\,
(\mathbf{Z}^{\mathsf{H}}\mathbf{Y})^{\mathsf{H}}\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_mul_smul_mul_sq_mul_sq {q r : Type*} [Fintype q] [Fintype r]
    {E : Matrix m n ℝ} {V : Matrix n q ℝ} (hEV : E * V * Vᴴ = E) (c : ℝ) {u : ℝ} (hu : 0 ≤ u)
    (Y : Matrix n l ℝ) (Z : Matrix n r ℝ) :
    frobNorm (E * (c • Y) * (c • Y)ᴴ * Z) ^ 2 * u ^ 2 =
      frobNorm (E * V * (Vᴴ * Y) * ((c ^ 2 * u) • (Zᴴ * Y)ᴴ)) ^ 2 := by
  have e1 : E * (c • Y) * (c • Y)ᴴ * Z = c ^ 2 • ((E * V) * (Vᴴ * Y) * (Zᴴ * Y)ᴴ) := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_smul,
      star_trivial]
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Matrix.mul_assoc, hEV]
    ring_nf
  rw [e1, Matrix.mul_smul, frobNorm_smul, frobNorm_smul, Real.norm_of_nonneg (sq_nonneg c),
    Real.norm_of_nonneg (mul_nonneg (sq_nonneg c) hu)]
  ring

/-- A product of squares is integrable when both fourth powers are, by
$f^2g^2 \le (f^4 + g^4)/2$. -/
private theorem integrable_sq_mul_sq_of_integrable_pow_four {f g : Ω → ℝ}
    (hf : AEStronglyMeasurable (fun ω => f ω ^ 2) μ)
    (hg : AEStronglyMeasurable (fun ω => g ω ^ 2) μ)
    (hf4 : Integrable (fun ω => f ω ^ 4) μ) (hg4 : Integrable (fun ω => g ω ^ 4) μ) :
    Integrable (fun ω => f ω ^ 2 * g ω ^ 2) μ := by
  refine ((hf4.add hg4).div_const 2).mono' (hf.mul hg) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_of_nonneg (by positivity)]
  change f ω ^ 2 * g ω ^ 2 ≤ (f ω ^ 4 + g ω ^ 4) / 2
  nlinarith [sq_nonneg (f ω ^ 2 - g ω ^ 2)]

/-- The tail–head term of the structural bound in expectation: with
$\chi = \|\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{Z}\|_{\mathsf{F}}$,
$\mathbf{S} = \ell^{-1/2}\mathbf{\Omega}$, and $u$ the clipped inverse of the head
$\mathbf{G}_1 = \mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$, conditionally on $\mathbf{G}_1$ the
matrix $\ell\,u\,\mathbf{E}\mathbf{S}\mathbf{S}^{\mathsf{H}}\mathbf{Z}$ is a Gaussian product, and
$\mathbb{E}[\chi^2u^2] = \ell^{-2}\|\mathbf{E}\|_{\mathsf{F}}^2\,\mathbb{E}[u^2\|\mathbf{G}_1
\|_{\mathsf{F}}^2] \le \ell^{-2}\|\mathbf{E}\|_{\mathsf{F}}^2\sqrt{(k\ell)^2 + 2k\ell}\,
(\mathbb{E}u^4)^{1/2}$. -/
private theorem integral_frobNorm_sq_mul_inv_sq_le {q : Type*} [Fintype q] [DecidableEq q]
    (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} (hk : 1 ≤ k)
    (hkl : 8 + k ≤ Fintype.card l) {Z : Matrix n (Fin k) ℝ} {V : Matrix n q ℝ}
    (hZ : HasOrthonormalCols Z) (hV : HasOrthonormalCols V) (hZV : Zᴴ * V = 0)
    {E : Matrix m n ℝ} (hEV : E * V * Vᴴ = E) :
    Integrable (fun ω => frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Z) ^ 2 *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 2) μ ∧
    ∫ ω, frobNorm (E * ((√(Fintype.card l : ℝ))⁻¹ • X ω) *
        ((√(Fintype.card l : ℝ))⁻¹ • X ω)ᴴ * Z) ^ 2 *
      (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 2 ∂μ ≤
      frobNorm E ^ 2 / (Fintype.card l : ℝ) ^ 2 *
        √(((k * Fintype.card l : ℕ) : ℝ) ^ 2 + 2 * ((k * Fintype.card l : ℕ) : ℝ)) *
        √(∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 4 ∂μ) := by
  have := hX.isProbabilityMeasure
  have hl0 : 0 < Fintype.card l := by omega
  set L := (Fintype.card l : ℝ) with hL
  have hL0 : 0 < L := by rw [hL]; exact_mod_cast hl0
  set c := (√L)⁻¹ with hc
  have hc2 : c ^ 2 = L⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hL0.le]
  set U : Matrix (Fin k) l ℝ → ℝ := fun H => (min 1 (singularValues Hᴴ (k - 1) ^ 2 / L))⁻¹
  have hU : Measurable U := measurable_min_one_inv L
  have hU0 (H : Matrix (Fin k) l ℝ) : 0 ≤ U H :=
    inv_nonneg.2 (le_min zero_le_one (div_nonneg (sq_nonneg _) hL0.le))
  have hu (ω : Ω) : (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ = U (Zᴴ * X ω) := by
    simp only [U, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  set T : Matrix (Fin k) l ℝ → Matrix l (Fin k) ℝ := fun H => (c ^ 2 * U H) • Hᴴ
  have hT : Measurable T :=
    (measurable_const.mul hU).smul continuous_id.matrix_conjTranspose.measurable
  have hG₁ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hZ
  have hG₂ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV
  have hind := indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hZ hV hZV
  have hEVn : frobNorm (E * V) = frobNorm E := by
    conv_rhs => rw [← hEV]
    exact (hV.frobNorm_mul_conjTranspose_right _).symm
  -- the identity with the Gaussian product
  have hid (ω : Ω) : frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Z) ^ 2 * U (Zᴴ * X ω) ^ 2 =
      frobNorm ((fun _ : Matrix (Fin k) l ℝ => E * V) (Zᴴ * X ω) * (Vᴴ * X ω) *
        T (Zᴴ * X ω)) ^ 2 :=
    frobNorm_mul_smul_mul_sq_mul_sq hEV c (hU0 _) (X ω) Z
  have hTn (H : Matrix (Fin k) l ℝ) :
      frobNorm (E * V) ^ 2 * frobNorm (T H) ^ 2 =
        frobNorm E ^ 2 * L⁻¹ ^ 2 * (U H ^ 2 * frobNorm H ^ 2) := by
    simp only [T, frobNorm_smul, frobNorm_conjTranspose, Real.norm_of_nonneg
      (mul_nonneg (sq_nonneg c) (hU0 H)), hEVn, ← hc2]
    ring
  -- integrability
  have hG4i := integrable_frobNorm_pow_four_of_hasLaw_gaussianMatrix hG₁
  have hG4 := integral_frobNorm_pow_four_of_hasLaw_gaussianMatrix hG₁
  have hU4i : Integrable (fun ω => U (Zᴴ * X ω) ^ 4) μ :=
    (integrable_min_one_inv_pow hX hk hZ (r := 4) (by omega)).congr
      (ae_of_all _ fun ω => congrArg (· ^ 4) (hu ω))
  have hXm := hX.aemeasurable
  have hG₁m : AEMeasurable (fun ω => Zᴴ * X ω) μ :=
    (measurable_const.matrix_mul measurable_id).comp_aemeasurable hXm
  have hUm : AEStronglyMeasurable (fun ω => U (Zᴴ * X ω) ^ 2) μ :=
    ((hU.comp_aemeasurable hG₁m).pow_const 2).aestronglyMeasurable
  have hFm : AEStronglyMeasurable (fun ω => frobNorm (Zᴴ * X ω) ^ 2) μ :=
    ((measurable_frobNorm.comp_aemeasurable hG₁m).pow_const 2).aestronglyMeasurable
  have hprod : Integrable (fun ω => U (Zᴴ * X ω) ^ 2 * frobNorm (Zᴴ * X ω) ^ 2) μ :=
    integrable_sq_mul_sq_of_integrable_pow_four (f := fun ω => U (Zᴴ * X ω))
      (g := fun ω => frobNorm (Zᴴ * X ω)) hUm hFm hU4i hG4i
  have hR : Integrable (fun ω => frobNorm ((fun _ : Matrix (Fin k) l ℝ => E * V) (Zᴴ * X ω)) ^ 2 *
      frobNorm (T (Zᴴ * X ω)) ^ 2) μ := by
    simp only [hTn]
    exact hprod.const_mul _
  have hL' := (integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun hG₂ hG₁m
    hind measurable_const hT).2 hR
  have hval := integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun hG₂ hG₁m hind
    (S := fun _ : Matrix (Fin k) l ℝ => E * V) measurable_const hT
  simp only [hu, hid]
  refine ⟨hL', ?_⟩
  rw [hval]
  simp only [hTn]
  rw [integral_const_mul]
  -- Cauchy–Schwarz
  have hmem1 : MemLp (fun ω => U (Zᴴ * X ω) ^ 2) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num, memLp_two_iff_integrable_sq hUm]
    simpa only [← pow_mul] using hU4i
  have hmem2 : MemLp (fun ω => frobNorm (Zᴴ * X ω) ^ 2) (ENNReal.ofReal 2) μ := by
    rw [show ENNReal.ofReal 2 = 2 by norm_num, memLp_two_iff_integrable_sq hFm]
    simpa only [← pow_mul] using hG4i
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all _ fun ω => sq_nonneg (U (Zᴴ * X ω))) (ae_of_all _ fun ω => sq_nonneg _) hmem1 hmem2
  simp only [Real.rpow_two, ← pow_mul, ← Real.sqrt_eq_rpow, Nat.reduceMul] at hCS
  rw [hG4, Fintype.card_fin] at hCS
  have hE0 : 0 ≤ frobNorm E ^ 2 * L⁻¹ ^ 2 := by positivity
  calc frobNorm E ^ 2 * L⁻¹ ^ 2 * ∫ ω, U (Zᴴ * X ω) ^ 2 * frobNorm (Zᴴ * X ω) ^ 2 ∂μ ≤
        frobNorm E ^ 2 * L⁻¹ ^ 2 * (√(∫ ω, U (Zᴴ * X ω) ^ 4 ∂μ) *
          √(((k * Fintype.card l : ℕ) : ℝ) ^ 2 + 2 * ((k * Fintype.card l : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hCS hE0
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow]; ring

/-- The arithmetic of the assembly: the three expectations of the structural bound, with the
clipped inverse moments $\mathbb{E}u \le (1 - y)^{-2} + 10/\sqrt{\ell}$ and
$\mathbb{E}u^4 \le (1 - y)^{-8} + 263/\sqrt{\ell}$, $y = \sqrt{k/\ell}$ and $\theta = 4y$, add up
to the early-truncated randomized SVD factor. -/
private theorem add_le_earlyTruncatedRSVDFactor_mul {k l : ℕ} (hk : 1 ≤ k) (hkl : 100 * k ≤ l)
    {e Iu Iu4 : ℝ} (he : 0 ≤ e)
    (hIu : Iu ≤ ((1 - √((k : ℝ) / l)) ^ 2)⁻¹ + 10 / √(l : ℝ))
    (hIu4 : Iu4 ≤ ((1 - √((k : ℝ) / l)) ^ 8)⁻¹ + 263 / √(l : ℝ)) :
    e / (1 - 4 * √((k : ℝ) / l)) * Iu +
        √(k : ℝ) / (1 - 4 * √((k : ℝ) / l)) * (√(2 / (l : ℝ)) * e * Iu) +
      1 / (4 * √((k : ℝ) / l) * (1 - 4 * √((k : ℝ) / l))) *
        (e / (l : ℝ) ^ 2 * √(((k * l : ℕ) : ℝ) ^ 2 + 2 * ((k * l : ℕ) : ℝ)) * √Iu4) ≤
      earlyTruncatedRSVDFactor k l * e := by
  obtain ⟨hy0, hy1⟩ := sqrt_div_le_tenth hkl
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hl0 : (0 : ℝ) < l := by
    have : (100 : ℝ) ≤ l := by
      have : (100 * k : ℝ) ≤ l := by exact_mod_cast hkl
      nlinarith
    linarith
  set y := √((k : ℝ) / l) with hy
  have hypos : 0 < y := Real.sqrt_pos.2 (by positivity)
  have hyy : y ^ 2 = k / l := Real.sq_sqrt (by positivity)
  have hd : 0 < 1 - 4 * y := by linarith
  -- the cross term
  have h2 : √(k : ℝ) * √(2 / (l : ℝ)) = √(2 * k / l) := by
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]; congr 1; ring
  -- the chi term
  have hR : √(((k * l : ℕ) : ℝ) ^ 2 + 2 * ((k * l : ℕ) : ℝ)) =
      k * l * √(1 + 2 / (k * l)) := by
    have hkl0 : (0 : ℝ) < k * l := by positivity
    rw [show ((k * l : ℕ) : ℝ) ^ 2 + 2 * ((k * l : ℕ) : ℝ) = (k * l) ^ 2 * (1 + 2 / (k * l)) by
      push_cast; field_simp, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hkl0.le]
  have hchi : 1 / (4 * y * (1 - 4 * y)) * (e / (l : ℝ) ^ 2 * (k * l * √(1 + 2 / (k * l)))) =
      y / 4 * √(1 + 2 / (k * l)) * e / (1 - 4 * y) := by
    have hk2 : (k : ℝ) = y ^ 2 * l := by rw [hyy]; field_simp
    rw [hk2]
    field_simp
  rw [hR, earlyTruncatedRSVDFactor_def, ← hy]
  have hsI : √Iu4 ≤ √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ)) := Real.sqrt_le_sqrt hIu4
  calc e / (1 - 4 * y) * Iu + √(k : ℝ) / (1 - 4 * y) * (√(2 / (l : ℝ)) * e * Iu) +
        1 / (4 * y * (1 - 4 * y)) * (e / (l : ℝ) ^ 2 * (k * l * √(1 + 2 / (k * l))) * √Iu4) =
        ((1 + √(k : ℝ) * √(2 / (l : ℝ))) * Iu +
          y / 4 * √(1 + 2 / (k * l)) * √Iu4) / (1 - 4 * y) * e := by
        rw [show 1 / (4 * y * (1 - 4 * y)) * (e / (l : ℝ) ^ 2 * (k * l * √(1 + 2 / (k * l))) *
            √Iu4) = 1 / (4 * y * (1 - 4 * y)) * (e / (l : ℝ) ^ 2 * (k * l * √(1 + 2 / (k * l)))) *
            √Iu4 by ring, hchi]
        field_simp
    _ ≤ ((1 + √(2 * k / l)) * (((1 - y) ^ 2)⁻¹ + 10 / √(l : ℝ)) +
          y / 4 * √(1 + 2 / (k * l)) * √(((1 - y) ^ 8)⁻¹ + 263 / √(l : ℝ))) /
          (1 - 4 * y) * e := by
        rw [h2]
        gcongr

/-- The clipped inverse moments of the head at $q = 1$ and $q = 4$, with the constants of
`NLAlib.gaussianClippedInvMomentConstant_one_le_10` and
`NLAlib.gaussianClippedInvMomentConstant_four_le_263` in place. -/
private theorem integral_min_one_inv_pow_le (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : 1 ≤ k) (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l)
    {Z : Matrix n (Fin k) ℝ} (hZ : HasOrthonormalCols Z) :
    ∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ∂μ ≤
        ((1 - √((k : ℝ) / Fintype.card l)) ^ 2)⁻¹ + 10 / √(Fintype.card l : ℝ) ∧
      ∫ ω, (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / Fintype.card l))⁻¹ ^ 4 ∂μ ≤
        ((1 - √((k : ℝ) / Fintype.card l)) ^ 8)⁻¹ + 263 / √(Fintype.card l : ℝ) := by
  have hY := hasLaw_conjTranspose_mul_frame hX hZ
  have hk' : k - 1 + 1 = Fintype.card (Fin k) := by rw [Fintype.card_fin]; omega
  have hn : 100 * Fintype.card (Fin k) ≤ Fintype.card l := by rwa [Fintype.card_fin]
  have h1 := integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix hY hk' hn
    hl (q := 1) (by norm_num)
  have h4 := integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix hY hk' hn
    hl (q := 4) le_rfl
  simp only [pow_one, Fintype.card_fin, Nat.reduceMul] at h1 h4
  refine ⟨h1.trans ?_, h4.trans ?_⟩
  · gcongr
    exact gaussianClippedInvMomentConstant_one_le_10
  · gcongr
    exact gaussianClippedInvMomentConstant_four_le_263

/-- The main case of the expectation bound, $1 \le k \le \lvert n \rvert$, in a frame
$\mathbf{Z}$ of the top-$k$ right singular subspace and its completion $\mathbf{V}$. -/
private theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_frame {q : Type*} [Fintype q]
    [DecidableEq q] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : 1 ≤ k) (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l)
    {Z : Matrix n (Fin k) ℝ} {V : Matrix n q ℝ} (hZ : HasOrthonormalCols Z)
    (hV : HasOrthonormalCols V) (hZV : Zᴴ * V = 0) (hAZ : A * Z * Zᴴ = truncatedSVD A k)
    (hEV : (A - truncatedSVD A k) * V * Vᴴ = A - truncatedSVD A k) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      earlyTruncatedRSVDFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  obtain ⟨hy0, hy1⟩ := sqrt_div_le_tenth hkl
  have hL0 : (0 : ℝ) < Fintype.card l := by
    have : (900 : ℝ) ≤ Fintype.card l := by exact_mod_cast hl
    linarith
  have hypos : 0 < √((k : ℝ) / Fintype.card l) :=
    Real.sqrt_pos.2 (div_pos (by exact_mod_cast hk) hL0)
  set E := A - truncatedSVD A k
  set L := (Fintype.card l : ℝ)
  set y := √((k : ℝ) / L)
  set c := (√L)⁻¹ with hc
  have hc0 : 0 < c := inv_pos.2 (Real.sqrt_pos.2 hL0)
  have hc2 : c ^ 2 = L⁻¹ := by rw [hc, inv_pow, Real.sq_sqrt hL0.le]
  have hθ0 : 0 < 4 * y := by linarith
  have hθ1 : 4 * y < 1 := by linarith
  have hY := hasLaw_conjTranspose_mul_frame hX hZ
  have hσ : ∀ᵐ ω ∂μ, 0 < singularValues ((X ω)ᴴ * Z) (k - 1) := by
    filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hY] with ω hω
    rw [singularValues_pos_iff, hω, Fintype.card_fin, min_eq_right (by omega)]
    omega
  have hpt : ∀ᵐ ω ∂μ, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ≤
      frobNorm E ^ 2 / (1 - 4 * y) *
          (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ +
        √(k : ℝ) / (1 - 4 * y) *
          (frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Eᴴ - E * Eᴴ) *
            (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹) +
        1 / (4 * y * (1 - 4 * y)) *
          (frobNorm (E * (c • X ω) * (c • X ω)ᴴ * Z) ^ 2 *
            (min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))⁻¹ ^ 2) := by
    filter_upwards [hσ] with ω hσω
    have h := frobNorm_sub_earlyTruncatedRSVD_sq_le_inv hk hZ hAZ (X ω) hc0
      (a := min 1 (singularValues ((X ω)ᴴ * Z) (k - 1) ^ 2 / L))
      (lt_min one_pos (div_pos (pow_pos hσω 2) hL0)) (min_le_left _ _)
      (by rw [hc2, inv_mul_eq_div]; exact min_le_right _ _) hθ0 hθ1
    refine h.trans_eq ?_
    ring
  obtain ⟨hIu, hIu4⟩ := integral_min_one_inv_pow_le hX hk hkl hl hZ
  have hu1i := integrable_min_one_inv_pow hX hk hZ (r := 1) (by omega)
  simp only [pow_one] at hu1i
  obtain ⟨hwui, hwu⟩ := integral_frobNorm_mul_inv_le hX hk (by omega) hZ hV hZV hEV
  obtain ⟨hχui, hχu⟩ := integral_frobNorm_sq_mul_inv_sq_le hX hk (by omega) hZ hV hZV hEV
  have hRi := ((hu1i.const_mul (frobNorm E ^ 2 / (1 - 4 * y))).add
    (hwui.const_mul (√(k : ℝ) / (1 - 4 * y)))).add
      (hχui.const_mul (1 / (4 * y * (1 - 4 * y))))
  refine (integral_mono_ae (integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX.aemeasurable k)
    hRi hpt).trans ?_
  rw [integral_add' (hu1i.const_mul _ |>.add (hwui.const_mul _)) (hχui.const_mul _),
    integral_add' (hu1i.const_mul _) (hwui.const_mul _), integral_const_mul, integral_const_mul,
    integral_const_mul]
  refine le_trans ?_ (add_le_earlyTruncatedRSVDFactor_mul hk hkl (sq_nonneg (frobNorm E)) hIu
    hIu4)
  gcongr

/-- **The expected error of the early-truncated randomized SVD**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{\Omega}$, $100k \le \ell$ and
$900 \le \ell$, <!-- value earlyTruncatedRSVDFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le \frac{(1 + \sqrt{2k/\ell})\bigl((1 - \sqrt{k/\ell})^{-2} +
10/\sqrt{\ell}\bigr) + \frac{1}{4}\sqrt{k/\ell}\sqrt{1 + 2/(k \ell)}\sqrt{(1 - \sqrt{k/\ell})^{-8} +
263/\sqrt{\ell}}}{1 - 4\sqrt{k/\ell}}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Every rank and shape; every choice of the
truncation. Proved without a literature source: the structural bound
`NLAlib.IsSubspaceInjection.frobNorm_sub_mul_sq_le` at $\theta = 4\sqrt{k/\ell}$ with the clipped
head constant, whose inverse moments are
`NLAlib.integral_min_one_singularValues_sq_div_inv_pow_le_of_hasLaw_gaussianMatrix`, the
independence of the head and tail blocks, approximate matrix multiplication for the tail and the
conditional Gaussian second moment for the cross term. The sketch quantities are those of
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12]; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1].
Result: etrsvd -/
theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hkl : 100 * k ≤ Fintype.card l) (hl : 900 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      earlyTruncatedRSVDFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  classical
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) : earlyTruncatedRSVD A x 0 = 0 := by
      rw [earlyTruncatedRSVD, truncatedSVD_zero, rangeProjector_zero, Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    exact le_mul_of_one_le_left (sq_nonneg _) (one_le_earlyTruncatedRSVDFactor hkl)
  by_cases hkn : Fintype.card n < k
  · have hr : A.rank ≤ k := A.rank_le_card_width.trans hkn.le
    have hE : A - truncatedSVD A k = 0 := by rw [truncatedSVD_of_rank_le A hr, sub_self]
    have hae : ∀ᵐ ω ∂μ, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 = 0 := by
      filter_upwards [ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hX (by omega)] with ω hω
      rw [earlyTruncatedRSVD_of_rank_le ((Matrix.rank_mul_le_left _ _).trans hr), hω, sub_self,
        frobNorm_zero]
      norm_num
    rw [integral_congr_ae hae, hE, frobNorm_zero]
    simp
  push Not at hkn
  obtain ⟨Z, V, hZ, hV, hZV, hAZ, hEV⟩ :=
    exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD_completion
      (p := Fin k) (q := Fin (Fintype.card n - k)) A (Fintype.card_fin k)
      (by simp only [Fintype.card_fin]; omega)
  exact integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_frame A hX hk hkl hl hZ hV hZV hAZ hEV

/-- **The early-truncated randomized SVD reaches relative error $1 + \varepsilon$** with
$\ell \ge 900k/\varepsilon^2$ standard Gaussian samples, $0 < \varepsilon \le 1$:
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
with $\ell$ products with $\mathbf{A}$, at most $k$ with $\mathbf{A}^{\mathsf{H}}$, and output
rank at most $k$. Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`.
Proved without a literature source; the algorithm is [TroppYurtseverUdellCevher2017, §7.3.1].
Result: etrsvd -/
theorem integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hl : 900 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l) :
    ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have h0 (x : Matrix n l ℝ) : earlyTruncatedRSVD A x 0 = 0 := by
      rw [earlyTruncatedRSVD, truncatedSVD_zero, rangeProjector_zero, Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hε2 : ε ^ 2 ≤ 1 := by nlinarith
  have hl900 : (900 : ℝ) * k ≤ Fintype.card l := by nlinarith
  have hkl : 100 * k ≤ Fintype.card l := by
    have : (100 : ℝ) * k ≤ Fintype.card l := by linarith
    exact_mod_cast this
  have hl' : 900 ≤ Fintype.card l := by
    have : (900 : ℝ) ≤ Fintype.card l := by linarith
    exact_mod_cast this
  exact (integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix A hX hkl hl').trans
    (mul_le_mul_of_nonneg_right (earlyTruncatedRSVDFactor_le_one_add hk hε hε1 hl) (sq_nonneg _))

/-- **$O(k/\varepsilon^2)$ samples suffice for the early-truncated randomized SVD**: there are
absolute constants $C, \varepsilon_0 > 0$ such that for a standard Gaussian $n \times \ell$ test
matrix $\mathbf{\Omega}$, $0 < \varepsilon \le \varepsilon_0$ and $\ell \ge Ck/\varepsilon^2$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`; the
proof takes $C = 900$ and $\varepsilon_0 = 1$.
Asymptotic:
NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: etrsvd -/
theorem exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε ^ 2) ≤ Fintype.card l →
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨900, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ μ A X k ε hX hε hε1 hl
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at hl
  exact integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix A hX hε
    hε1 (by linarith)

set_option linter.style.longLine false in
-- The theorem's name alone exceeds 100 characters.
/-- **Early-truncated generalized Nyström reaches relative error $1 + \varepsilon$**: for
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($m \times p$) with $\ell \ge 3600k/\varepsilon^2$,
$p \ge k + 1 + (2+\varepsilon)k/\varepsilon$ and $0 < \varepsilon \le 1$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi},
k)\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,:$$
one pass, output rank at most $k$. The early-truncated randomized SVD at accuracy
$\varepsilon/2$
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`)
composed with the Gaussian completion
(`NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le`).
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_of_hasLaw_gaussianMatrix`.
Proved without a literature source; the algorithm is
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)].
Result: etgn -/
theorem
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hl : 3600 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l)
    (hp : (k : ℝ) + 1 + (2 + ε) * k / ε ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 :=
  integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix_of_integral_le
    A hX.aemeasurable hΨ hXΨ hε hp
    (integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix A hX
      (half_pos hε) (by linarith) (by nlinarith))

-- A docstring line names a declaration whose name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(k/\varepsilon^2)$ and $O(k/\varepsilon)$ samples suffice for early-truncated generalized
Nyström**: there are absolute constants $C, \varepsilon_0 > 0$ such that for independent standard
Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$),
$0 < \varepsilon \le \varepsilon_0$, $\ell \ge Ck/\varepsilon^2$ and $p \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi},
k)\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The asymptotic form of
`NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`;
the proof takes $C = 3600$ and $\varepsilon_0 = 1$.
Asymptotic:
NLAlib.integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: etgn -/
theorem
    exists_forall_integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l p : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [Fintype l] [Fintype p] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (Ψ : Ω → Matrix m p ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → HasLaw Ψ (gaussianMatrix m p) μ → IndepFun X Ψ μ →
      0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε ^ 2) ≤ Fintype.card l →
      C * ((k : ℝ) / ε) ≤ Fintype.card p →
      ∫ ω, frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨3600, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l p _ _ _ _ _ μ A X Ψ k ε hX hΨ hXΨ hε hε1 hl hp
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := hX.isProbabilityMeasure
    have h0 (x : Matrix n l ℝ) (ψ : Matrix m p ℝ) :
        earlyTruncatedGeneralizedNystrom A x ψ 0 = 0 := by
      simp only [earlyTruncatedGeneralizedNystrom, truncatedSVD_zero, obliqueProjector,
        Matrix.zero_mul]
    simp only [h0, sub_zero, truncatedSVD_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have ht : (k : ℝ) ≤ k / ε := (le_div_iff₀ hε).2 (by nlinarith)
  have he : (2 + ε) * k / ε = 2 * (k / ε) + k := by
    rw [add_mul, add_div, mul_div_assoc, mul_div_cancel_left₀ _ hε.ne']
  rw [← mul_div_assoc, div_le_iff₀ (by positivity)] at hl
  exact
    integral_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
      A hX hΨ hXΨ hε hε1 (by linarith) (by rw [he]; linarith)

end NLAlib
