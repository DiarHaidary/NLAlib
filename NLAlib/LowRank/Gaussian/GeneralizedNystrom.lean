/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Gaussian.RotationInvariant
public import NLAlib.Regression.SketchAndSolve

/-!
# Generalized Nyström in expectation with a Gaussian or Haar co-range test matrix

For a range test matrix $\mathbf{\Omega}$ (the Lean `X`, `X₀` when fixed) and an independent
standard Gaussian co-range test matrix $\mathbf{\Psi}$, the expected squared Frobenius error of
generalized Nyström $\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})$
(`NLAlib.generalizedNystrom`) is that of the randomized SVD
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ times the completion factor
$1 + q/(p - q - 1)$ at the rank $q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$,
inside the expectation:
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 =
\mathbb{E}\Bigl[\Bigl(1 + \frac{q}{p-q-1}\Bigr)
\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2\Bigr]\,.$$
The residual of generalized Nyström is a sketch-and-solve residual
(`NLAlib.sub_generalizedNystrom`), so for fixed $\mathbf{\Omega}$ this is the Gaussian completion
identity `NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix` with
the sketch $\mathbf{\Psi}^{\mathsf{H}}$; the iterated integral over the independent pair
(`ProbabilityTheory.IndepFun.lintegral_comp_eq_lintegral_lintegral`) integrates it over
$\mathbf{\Omega}$, whose law is arbitrary. Any bound on the randomized SVD thus becomes a bound on
generalized Nyström; with a Gaussian $\mathbf{\Omega}$ this is Tropp, Yurtsever, Udell and Cevher's
Theorem 4.3.

For an $m \times p$ Haar co-range test matrix with $p \le m$ the factor is the Haar
one, <!-- value haarProjectionFactor m p q -->
$1 + (m - p)/(m - q) \cdot (q/(p - q - 1))$, through
`NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame`. With a
rotation-invariant $\mathbf{\Omega}$ of full column rank, Epperly and Webber's sharp bound for the
randomized SVD (`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le`)
gives their Theorem 4.2(a), for a Gaussian and for a Haar co-range test matrix. Real throughout.
Design: `docs/design/LowRank-S6.md` §3.4, §8.

## Main results

* `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix`: fixed range test
  matrix.
* `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix`:
  any law of the range test matrix.
* `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`: Gaussian test
  matrices (TYUC Theorem 4.3), and the asymptotic form of the second ($O(k/\varepsilon)$ and
  $O(\ell/\varepsilon)$ samples), `NLAlib.exists_forall_` followed by its name.
* `NLAlib.ae_generalizedNystrom_eq_self_of_hasLaw_gaussianMatrix`: exact recovery at low rank.
* Haar co-range: `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame` (fixed
  range test matrix),
  `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_haarFrame` with
  `NLAlib.integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame` (any law of the range
  test matrix), and for a Gaussian range test matrix
  `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_haarFrame`.
* Epperly and Webber's Theorem 4.2(a), with a rank parameter $r \ge \operatorname{rank}\mathbf{A}$:
  `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant` followed by
  `_of_hasLaw_gaussianMatrix_of_rank_le` (Gaussian co-range) or `_of_hasLaw_haarFrame_of_rank_le`
  (Haar co-range).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-! ### A fixed range test matrix -/

/-- The squared error of generalized Nyström with a fixed range test matrix and a Gaussian
co-range test matrix is integrable for
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 2 \le p$. -/
private theorem integrable_frobNorm_sub_generalizedNystrom_sq_of_fixed (A : Matrix m n ℝ)
    (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hr : (A * X₀).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - generalizedNystrom A X₀ (Ψ ω)) ^ 2) μ := by
  classical
  simp only [sub_generalizedNystrom]
  exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hΨ) (A * X₀) hr A

/-- **Generalized Nyström conditionally on the range test matrix**: for a fixed test matrix
$\mathbf{\Omega}$, a standard Gaussian $m \times p$ co-range test matrix $\mathbf{\Psi}$ and
$q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$ with
$q + 2 \le p$, <!-- value gaussianProjectionFactor q p -->
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{q}{p - q - 1}\Bigr)\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, proof of Theorem 4.2]; [TroppYurtseverUdellCevher2017, Lemmas A.3, A.5]; there
with $q$ the sketch size (full rank).
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hr : (A * X₀).rank + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A X₀ (Ψ ω)) ^ 2 ∂μ =
      gaussianProjectionFactor (A * X₀).rank (Fintype.card p) * frobNorm (A - rsvd A X₀) ^ 2 := by
  classical
  simp only [sub_generalizedNystrom, sub_rsvd]
  exact integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hΨ) (A * X₀) hr A

/-! ### Any law of the range test matrix -/

omit [Fintype m] in
/-- The completion factor at the rank is measurable in the range test matrix. -/
private theorem measurable_gaussianProjectionFactor_rank [Finite m] (A : Matrix m n ℝ) (c : ℕ) :
    Measurable fun x : Matrix n l ℝ => gaussianProjectionFactor (A * x).rank c :=
  (measurable_from_nat (f := fun q => gaussianProjectionFactor q c)).comp
    (measurable_rank.comp (measurable_const.matrix_mul measurable_id))

/-- The right side of the identity, $(1 + q/(p-q-1))\|\mathbf{A} - \mathsf{rsvd}\|^2$ at the
random rank, is integrable. -/
private theorem integrable_gaussianProjectionFactor_mul [IsFiniteMeasure μ] (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => gaussianProjectionFactor (A * X ω).rank (Fintype.card p) *
      frobNorm (A - rsvd A (X ω)) ^ 2) μ := by
  refine (integrable_frobNorm_sub_rsvd_sq A hX).bdd_mul (c := 1 + Fintype.card p)
    ((measurable_gaussianProjectionFactor_rank A _).comp_aemeasurable hX).aestronglyMeasurable ?_
  filter_upwards [hr] with ω hω
  rw [Real.norm_of_nonneg (zero_le_one.trans (one_le_gaussianProjectionFactor hω))]
  exact gaussianProjectionFactor_le_one_add hω

/-- The identity as lower integrals: the iterated integral over the independent pair, with the
fixed-$\mathbf{\Omega}$ identity inside. -/
private theorem lintegral_frobNorm_sub_generalizedNystrom_sq (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    ∫⁻ ω, ENNReal.ofReal (frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (gaussianProjectionFactor (A * X ω).rank (Fintype.card p) *
        frobNorm (A - rsvd A (X ω)) ^ 2) ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  refine (hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX hΨ
    (F := fun q : Matrix n l ℝ × Matrix m p ℝ => frobNorm (A - generalizedNystrom A q.1 q.2) ^ 2)
    ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_generalizedNystrom A))).pow_const 2)
    (fun _ => sq_nonneg _) (hr.mono fun ω hω =>
      integrable_frobNorm_sub_generalizedNystrom_sq_of_fixed A (X ω) hid hω)).trans ?_
  refine lintegral_congr_ae (hr.mono fun ω hω => ?_)
  exact congrArg ENNReal.ofReal
    (integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A (X ω) hid hω)

/-- The squared error of generalized Nyström is almost everywhere strongly measurable. -/
private theorem aestronglyMeasurable_frobNorm_sub_generalizedNystrom_sq (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hΨ : AEMeasurable Ψ μ) :
    AEStronglyMeasurable (fun ω => frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) μ :=
  (((continuous_frobNorm.measurable.comp (measurable_const.sub
    (measurable_generalizedNystrom A))).pow_const 2).comp_aemeasurable
      (hX.prodMk hΨ)).aestronglyMeasurable

/-- **Generalized Nyström = randomized SVD × completion, for any law of the range test matrix**:
for $\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$, and
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 2 \le p$ almost surely, writing
$q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, <!-- value gaussianProjectionFactor q p -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 =
\mathbb{E}\Bigl[\Bigl(1 + \frac{q}{p - q - 1}\Bigr)\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})\|_{\mathsf{F}}^2\Bigr]\,:$$
the rank stays inside the expectation.
[EpperlyWebber2026, proof of Theorem 4.2]; [TroppYurtseverUdellCevher2017, §A.3.4].
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      ∫ ω, gaussianProjectionFactor (A * X ω).rank (Fintype.card p) *
        frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hR := integrable_gaussianProjectionFactor_mul A hX hr
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (aestronglyMeasurable_frobNorm_sub_generalizedNystrom_sq A hX hΨ.aemeasurable),
    integral_eq_lintegral_of_nonneg_ae (hr.mono fun ω hω => mul_nonneg
      (zero_le_one.trans (one_le_gaussianProjectionFactor hω)) (sq_nonneg _))
      hR.aestronglyMeasurable,
    lintegral_frobNorm_sub_generalizedNystrom_sq A hX hΨ hXΨ hr]

/-- The squared Frobenius error
$\|\mathbf{A}-\mathsf{generalizedNystrom}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\|_{\mathsf{F}}^2$ is integrable under a Gaussian co-range test matrix independent
of the range test matrix, when $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 2 \le p$ almost
surely. It need not be otherwise: at $p = \operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 1$ the
expectation is infinite unless $\mathbf{A} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$. -/
theorem integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) μ := by
  have := hΨ.isProbabilityMeasure
  refine ⟨aestronglyMeasurable_frobNorm_sub_generalizedNystrom_sq A hX hΨ.aemeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _),
    lintegral_frobNorm_sub_generalizedNystrom_sq A hX hΨ hXΨ hr]
  exact (integrable_gaussianProjectionFactor_mul A hX hr).lintegral_lt_top

/-- **Generalized Nyström = randomized SVD × completion, bound form**, for any law of
$\mathbf{\Omega}$ independent of a standard Gaussian $\mathbf{\Psi}$ and
$\ell + 2 \le p$: <!-- value gaussianProjectionFactor \ell p -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{\ell}{p - \ell - 1}\Bigr)\,\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
Any bound on the randomized SVD (Gaussian,
rotation-invariant, oblivious subspace injection) becomes a bound on generalized Nyström.
[CamanoEpperlyMeyerTropp2025, proof of Corollary 2.8]; [TroppYurtseverUdellCevher2017, §A.3.4].
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hrl (ω : Ω) : (A * X ω).rank ≤ Fintype.card l := Matrix.rank_le_card_width _
  have hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p :=
    ae_of_all _ fun ω => by have := hrl ω; omega
  rw [integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix A hX hΨ hXΨ
    hr, ← integral_const_mul]
  refine integral_mono_of_nonneg (hr.mono fun ω hω => mul_nonneg
    (zero_le_one.trans (one_le_gaussianProjectionFactor hω)) (sq_nonneg _))
    ((integrable_frobNorm_sub_rsvd_sq A hX).const_mul _) (ae_of_all _ fun ω => ?_)
  exact mul_le_mul_of_nonneg_right
    (gaussianProjectionFactor_le_gaussianProjectionFactor (hrl ω) hlp) (sq_nonneg _)

/-! ### Gaussian test matrices -/

/-- **The generalized Nyström identity, Gaussian test matrices**: for independent
test matrices, with
$\ell' = \min(\operatorname{rank}\mathbf{A}, \ell)$, the almost sure rank of the sketch, and
$\ell' + 2 \le p$, <!-- value gaussianProjectionFactor {\ell'} p -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 =
\Bigl(1 + \frac{\ell'}{p - \ell' - 1}\Bigr)\,\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
[EpperlyWebber2026, proof of Theorem 4.2(a)], with $\gamma = 1$; there for
$\operatorname{rank}\mathbf{A} \ge p$.
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hr : min A.rank (Fintype.card l) + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      gaussianProjectionFactor (min A.rank (Fintype.card l)) (Fintype.card p) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  have hrk := ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX
  rw [integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix A
    hX.aemeasurable hΨ hXΨ (hrk.mono fun ω hω => by rw [hω]; exact hr), ← integral_const_mul]
  exact integral_congr_ae (hrk.mono fun ω hω => by simp only [hω])

/-- **The expected error of generalized Nyström** (Gaussian test matrices): for independent
standard Gaussian test matrices, $k + 2 \le \ell$ and $\ell + 2 \le p$,
so <!-- value gaussianProjectionFactor \ell p --> <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{\ell}{p - \ell - 1}\Bigr)\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`.
[TroppYurtseverUdellCevher2017, Theorem 4.3]; there with a minimum over $k$, not stated here
(one comparison rank per statement).
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  rw [mul_assoc]
  exact (integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix A
    hX.aemeasurable hΨ hXΨ hlp).trans (mul_le_mul_of_nonneg_left
      (integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk)
      (zero_le_one.trans (one_le_gaussianProjectionFactor hlp)))

/-- **$O(k/\varepsilon)$ and $O(\ell/\varepsilon)$ samples suffice for generalized Nyström**:
there are absolute constants $C, \varepsilon_0 > 0$ such that for independent standard Gaussian
test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$), $k \ge 1$,
$0 < \varepsilon \le \varepsilon_0$, $\ell \ge Ck/\varepsilon$ and $p \ge C\ell/\varepsilon$,
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2
\le (1 + \varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
so $O(k/\varepsilon^2)$ products in all. The asymptotic form of
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`; the proof takes
$C = 9$ and $\varepsilon_0 = 1$.
[TroppYurtseverUdellCevher2017, Remark 4.4]; [Woodruff2014, Theorem 47];
[EpperlyWebber2026, §4.2]; there as scalings $\Theta(\cdot)$, and (Woodruff) with constant
probability and a subspace embedding for the co-range sketch.
Asymptotic: NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix
Result: generalized-nystrom-expected-error -/
theorem exists_forall_integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l p : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [Fintype l] [Fintype p] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (Ψ : Ω → Matrix m p ℝ) (k : ℕ) (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → HasLaw Ψ (gaussianMatrix m p) μ → IndepFun X Ψ μ →
      0 < k → 0 < ε → ε ≤ ε₀ → C * ((k : ℝ) / ε) ≤ Fintype.card l →
      C * ((Fintype.card l : ℝ) / ε) ≤ Fintype.card p →
      ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine ⟨9, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l p _ _ _ _ _ μ A X Ψ k ε hX hΨ hXΨ hk hε hε1 hl hp
  have h3 (a b : ℝ) (h : 9 * (a / ε) ≤ b) : 3 * (a / (ε / 3)) ≤ b := by
    have : 3 * (a / (ε / 3)) = 9 * (a / ε) := by rw [div_div_eq_mul_div]; ring
    rwa [this]
  have hε3 : 0 < ε / 3 := by positivity
  obtain ⟨hkl, hg⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le hk hε3
    (by linarith) (h3 _ _ hl)
  obtain ⟨hlp, hh⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le
    (by omega : 0 < Fintype.card l) hε3 (by linarith) (h3 _ _ hp)
  refine (integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix A hX hΨ hXΨ hkl
    hlp).trans (mul_le_mul_of_nonneg_right ?_ (sq_nonneg _))
  have hg1 := one_le_gaussianProjectionFactor hkl
  calc gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        gaussianProjectionFactor k (Fintype.card l) ≤ (1 + ε / 3) * (1 + ε / 3) :=
        mul_le_mul hh hg (by linarith) (by linarith)
    _ ≤ 1 + ε := by nlinarith

/-- Gaussian test matrices at least as wide as the rank make generalized Nyström exact: if
$\operatorname{rank}\mathbf{A} \le \min(\ell, p)$ then $\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi}) = \mathbf{A}$ almost surely. No independence of the two test matrices is needed. -/
theorem ae_generalizedNystrom_eq_self_of_hasLaw_gaussianMatrix (A : Matrix m n ℝ)
    (hX : HasLaw X (gaussianMatrix n l) μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hAl : A.rank ≤ Fintype.card l) (hAp : A.rank ≤ Fintype.card p) :
    ∀ᵐ ω ∂μ, generalizedNystrom A (X ω) (Ψ ω) = A := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX,
    ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix A hΨ hAp] with ω hX' hΨ'
  have hAX : (A * X ω).rank = A.rank := hX'.trans (min_eq_left hAl)
  refine generalizedNystrom_eq_self_of_rank_eq hAX ?_
  have hinj := Matrix.rank_mul_eq_iff_injOn.mp hΨ'
  refine Matrix.rank_mul_eq_iff_injOn.mpr (hinj.mono ?_)
  exact range_le_iff_exists_mul.mpr ⟨X ω, rfl⟩

/-! ### A Haar co-range test matrix -/

/-- **Generalized Nyström conditionally on the range test matrix, Haar co-range**: for a fixed
test matrix $\mathbf{\Omega}$, an $m \times p$ Haar co-range test matrix $\mathbf{\Psi}$ with
$p \le m$ and $q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$ with
$q + 2 \le p$, <!-- value haarProjectionFactor m p q -->
$$\mathbb{E}_{\mathbf{\Psi}}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{m - p}{m - q}\cdot\frac{q}{p - q - 1}\Bigr)
\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
The Gaussian twin is
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix`.
[EpperlyWebber2026, proof of Theorem 4.2]; there with $q$ the sketch size.
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame [DecidableEq p]
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hr : (A * X₀).rank + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A X₀ (Ψ ω)) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (A * X₀).rank *
        frobNorm (A - rsvd A X₀) ^ 2 := by
  classical
  simp only [sub_generalizedNystrom, sub_rsvd]
  exact integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame hΨ hpm (A * X₀) hr A

/-- The squared error with a fixed range test matrix and a Haar co-range test matrix is
integrable for $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 2 \le p \le m$. -/
private theorem integrable_frobNorm_sub_generalizedNystrom_sq_of_fixed_haar [DecidableEq p]
    (A : Matrix m n ℝ) (X₀ : Matrix n l ℝ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hr : (A * X₀).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - generalizedNystrom A X₀ (Ψ ω)) ^ 2) μ := by
  classical
  simp only [sub_generalizedNystrom]
  exact integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame hΨ hpm (A * X₀)
    hr A

omit [Fintype m] in
/-- The Haar completion factor at the rank is measurable in the range test matrix. -/
private theorem measurable_haarProjectionFactor_rank [Finite m] (A : Matrix m n ℝ) (d c : ℕ) :
    Measurable fun x : Matrix n l ℝ => haarProjectionFactor d c (A * x).rank :=
  (measurable_from_nat (f := fun q => haarProjectionFactor d c q)).comp
    (measurable_rank.comp (measurable_const.matrix_mul measurable_id))

/-- The right side of the identity at the random rank is integrable. -/
private theorem integrable_haarProjectionFactor_mul [IsFiniteMeasure μ] (A : Matrix m n ℝ)
    (hX : AEMeasurable X μ) (hpm : Fintype.card p ≤ Fintype.card m)
    (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => haarProjectionFactor (Fintype.card m) (Fintype.card p) (A * X ω).rank *
      frobNorm (A - rsvd A (X ω)) ^ 2) μ := by
  refine (integrable_frobNorm_sub_rsvd_sq A hX).bdd_mul (c := 1 + Fintype.card p)
    ((measurable_haarProjectionFactor_rank A _ _).comp_aemeasurable hX).aestronglyMeasurable ?_
  filter_upwards [hr] with ω hω
  rw [Real.norm_of_nonneg (zero_le_one.trans (one_le_haarProjectionFactor hω hpm))]
  exact haarProjectionFactor_le_one_add hω hpm

/-- The identity as lower integrals: the iterated integral over the independent pair, with the
fixed-$\mathbf{\Omega}$ identity inside. -/
private theorem lintegral_frobNorm_sub_generalizedNystrom_sq_haar [DecidableEq p]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ)
    (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    ∫⁻ ω, ENNReal.ofReal (frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) ∂μ =
      ∫⁻ ω, ENNReal.ofReal (haarProjectionFactor (Fintype.card m) (Fintype.card p)
        (A * X ω).rank * frobNorm (A - rsvd A (X ω)) ^ 2) ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (haarFrame m p) (haarFrame m p) := HasLaw.id
  refine (hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX hΨ
    (F := fun q : Matrix n l ℝ × Matrix m p ℝ => frobNorm (A - generalizedNystrom A q.1 q.2) ^ 2)
    ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_generalizedNystrom A))).pow_const 2)
    (fun _ => sq_nonneg _) (hr.mono fun ω hω =>
      integrable_frobNorm_sub_generalizedNystrom_sq_of_fixed_haar A (X ω) hid hpm hω)).trans ?_
  refine lintegral_congr_ae (hr.mono fun ω hω => ?_)
  exact congrArg ENNReal.ofReal
    (integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame A (X ω) hid hpm hω)

/-- The identity with the rank inside the expectation, Haar co-range. -/
private theorem integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_haar [DecidableEq p]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ)
    (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      ∫ ω, haarProjectionFactor (Fintype.card m) (Fintype.card p) (A * X ω).rank *
        frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hR := integrable_haarProjectionFactor_mul A hX hpm hr
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _)
      (aestronglyMeasurable_frobNorm_sub_generalizedNystrom_sq A hX hΨ.aemeasurable),
    integral_eq_lintegral_of_nonneg_ae (hr.mono fun ω hω => mul_nonneg
      (zero_le_one.trans (one_le_haarProjectionFactor hω hpm)) (sq_nonneg _))
      hR.aestronglyMeasurable,
    lintegral_frobNorm_sub_generalizedNystrom_sq_haar A hX hΨ hpm hXΨ hr]

/-- The squared Frobenius error
$\|\mathbf{A}-\mathsf{generalizedNystrom}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\|_{\mathsf{F}}^2$ is integrable under a Haar co-range test matrix with $p \le m$
independent of the range test matrix, when $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) + 2 \le
p$ almost surely. -/
theorem integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame [DecidableEq p]
    (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ)
    (hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p) :
    Integrable (fun ω => frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) μ := by
  have := hΨ.isProbabilityMeasure
  refine ⟨aestronglyMeasurable_frobNorm_sub_generalizedNystrom_sq A hX hΨ.aemeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun _ => sq_nonneg _),
    lintegral_frobNorm_sub_generalizedNystrom_sq_haar A hX hΨ hpm hXΨ hr]
  exact (integrable_haarProjectionFactor_mul A hX hpm hr).lintegral_lt_top

/-- **Generalized Nyström = randomized SVD × completion, Haar co-range, bound form**, for any law
of $\mathbf{\Omega}$ independent of an $m \times p$ Haar $\mathbf{\Psi}$ with $p \le m$ and
$\ell + 2 \le p$: <!-- value haarProjectionFactor m p \ell -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{m - p}{m - \ell}\cdot\frac{\ell}{p - \ell - 1}\Bigr)\,
\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
Any bound on the randomized SVD becomes a bound on
generalized Nyström with a Haar co-range test matrix.
[EpperlyWebber2026, proof of Theorem 4.2].
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (hX : AEMeasurable X μ) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hrl (ω : Ω) : (A * X ω).rank ≤ Fintype.card l := Matrix.rank_le_card_width _
  have hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p :=
    ae_of_all _ fun ω => by have := hrl ω; omega
  rw [integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_haar A hX hΨ hpm hXΨ hr,
    ← integral_const_mul]
  refine integral_mono_of_nonneg (hr.mono fun ω hω => mul_nonneg
    (zero_le_one.trans (one_le_haarProjectionFactor hω hpm)) (sq_nonneg _))
    ((integrable_frobNorm_sub_rsvd_sq A hX).const_mul _) (ae_of_all _ fun ω => ?_)
  exact mul_le_mul_of_nonneg_right
    (haarProjectionFactor_le_haarProjectionFactor (hrl ω) hlp hpm) (sq_nonneg _)

/-- **The generalized Nyström identity, Gaussian range and Haar co-range test matrices**:
for independent test matrices, with
$\ell' = \min(\operatorname{rank}\mathbf{A}, \ell)$, the almost sure rank of the sketch,
$\ell' + 2 \le p \le m$, <!-- value haarProjectionFactor m p {\ell'} -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 =
\Bigl(1 + \frac{m - p}{m - \ell'}\cdot\frac{\ell'}{p - \ell' - 1}\Bigr)\,
\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2\,,$$
Epperly and Webber's factor
$1 + \gamma\ell'/(p - \ell' - 1)$ with $\gamma = (m - p)/(m - \ell')$.
[EpperlyWebber2026, proof of Theorem 4.2(a), random orthonormal co-range]; there for
$\operatorname{rank}\mathbf{A} \ge p$.
Result: generalized-nystrom-expected-error -/
theorem integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_haarFrame
    [DecidableEq p] (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    (hXΨ : IndepFun X Ψ μ) (hr : min A.rank (Fintype.card l) + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (min A.rank (Fintype.card l)) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  have hrk := ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix A hX
  rw [integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_haar A hX.aemeasurable hΨ hpm hXΨ
    (hrk.mono fun ω hω => by rw [hω]; exact hr), ← integral_const_mul]
  exact integral_congr_ae (hrk.mono fun ω hω => by simp only [hω])

/-! ### Rotation-invariant range test matrices: Epperly and Webber's Theorem 4.2(a) -/

variable [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
  [IsLeftUnitarilyInvariant ν]

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The sharp upper bound for generalized Nyström, Gaussian co-range**: for $\mathbf{A}$ of rank
at most $r$, a test matrix $\mathbf{\Omega}$ with a left unitarily invariant law and full column
rank almost surely, a standard Gaussian $\mathbf{\Psi}$ independent of it, $\ell \le r$,
$\ell + 2 \le p$ and $q + 2 \le \ell$,
so <!-- value gaussianProjectionFactor \ell p --> <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2\,.$$
The instance
$r = \lvert n\rvert$ needs no knowledge of the rank.
[EpperlyWebber2026, Theorem 4.2(a)], with $\gamma = 1$; there
$r = \operatorname{rank}\mathbf{A} \ge p$
and a minimum over $q$.
Result: generalized-nystrom-expected-error -/
theorem
    integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix_of_rank_le
    (A : Matrix m n ℝ) (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {r q : ℕ} (hr : A.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
        rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2 := by
  rw [mul_assoc]
  exact (integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix A
    hX.aemeasurable hΨ hXΨ hlp).trans (mul_le_mul_of_nonneg_left
      (integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le A hX hXr hr hlr hq)
      (zero_le_one.trans (one_le_gaussianProjectionFactor hlp)))

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The sharp upper bound for generalized Nyström, random orthonormal co-range**: for
$\mathbf{A}$ of rank at most $r$, a test matrix $\mathbf{\Omega}$ with a left unitarily invariant
law and full column rank almost surely, an $m \times p$ Haar $\mathbf{\Psi}$ independent of it,
$\ell \le r$, $\ell + 2 \le p \le m$ and $q + 2 \le \ell$,
so <!-- value haarProjectionFactor m p \ell --> <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{m - p}{m - \ell}\cdot\frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2\,,$$
smaller than
the Gaussian co-range bound by the ratio of the completion factors.
[EpperlyWebber2026, Theorem 4.2(a)], with $\gamma = (d - k)/(d - \ell)$ in their letters; there
$r = \operatorname{rank}\mathbf{A} \ge p$ and a minimum over $q$.
Result: generalized-nystrom-expected-error -/
theorem
    integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame_of_rank_le
    [DecidableEq p] (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) (hΨ : HasLaw Ψ (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (hXΨ : IndepFun X Ψ μ) {r q : ℕ} (hr : A.rank ≤ r)
    (hlr : Fintype.card l ≤ r) (hq : q + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ ≤
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
        rotationInvariantFactor r (Fintype.card l) q * frobNorm (A - truncatedSVD A q) ^ 2 := by
  rw [mul_assoc]
  exact (integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_haarFrame A
    hX.aemeasurable hΨ hpm hXΨ hlp).trans (mul_le_mul_of_nonneg_left
      (integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le A hX hXr hr hlr hq)
      (zero_le_one.trans (one_le_haarProjectionFactor hlp hpm)))

end NLAlib
