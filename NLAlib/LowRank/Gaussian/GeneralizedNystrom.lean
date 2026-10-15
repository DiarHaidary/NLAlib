/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.Sketching.Gaussian.LeastSquares

/-!
# Generalized Nyström in expectation with a Gaussian co-range test matrix

For a range test matrix $\mathbf{\Omega}$ (the Lean `X`, `X₀` when fixed) and an independent
standard Gaussian co-range test matrix $\mathbf{\Psi}$, the expected squared Frobenius error of
generalized Nyström $\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})$
(`NLAlib.generalizedNystrom`) is that of the randomized SVD
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ times the completion factor
$1 + \frac{q}{p - q - 1}$ at the rank $q = \operatorname{rank}(\mathbf{A}\mathbf{\Omega})$,
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
Theorem 4.3. Real throughout. Design: `docs/design/LowRank-S6.md` §3.4, §8 (the Gaussian half;
the rotation-invariant bound and the Haar co-range statements follow in a later section).

## Main results

* `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix`: fixed range test
  matrix.
* `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_mul_integral_of_hasLaw_gaussianMatrix`:
  any law of the range test matrix.
* `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`: Gaussian test
  matrices (TYUC Theorem 4.3).
* `NLAlib.ae_generalizedNystrom_eq_self_of_hasLaw_gaussianMatrix`: exact recovery at low rank.
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
\mathbf{\Omega})\|_{\mathsf{F}}^2\,,$$
the factor being `gaussianProjectionFactor q p`.
[EpperlyWebber2026, proof of Theorem 4.2]; [TroppYurtseverUdellCevher2017, Lemmas A.3, A.5]; there
with $q$ the sketch size (full rank). Result: generalized-nystrom-expected-error -/
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

/-- The completion factor at a rank $q$ with $q + 2 \le p$ lies in $[1, 1 + p]$. -/
private theorem gaussianProjectionFactor_le_one_add {q c : ℕ} (h : q + 2 ≤ c) :
    gaussianProjectionFactor q c ≤ 1 + c := by
  have h' : (q : ℝ) + 2 ≤ c := by exact_mod_cast h
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ (by linarith)]
  nlinarith

/-- The right side of the identity, $(1 + \frac{q}{p-q-1})\|\mathbf{A} - \mathsf{rsvd}\|^2$ at the
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
  have hF : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      ENNReal.ofReal (frobNorm (A - generalizedNystrom A q.1 q.2) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_generalizedNystrom A))).pow_const 2)
  have hrank : Measurable fun x : Matrix n l ℝ => (A * x).rank :=
    measurable_rank.comp (measurable_const.matrix_mul measurable_id)
  have hG : Measurable fun x : Matrix n l ℝ =>
      ENNReal.ofReal (gaussianProjectionFactor (A * x).rank (Fintype.card p) *
        frobNorm (A - rsvd A x) ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_gaussianProjectionFactor_rank A _).mul
      ((continuous_frobNorm.measurable.comp
        (measurable_const.sub (measurable_rsvd A))).pow_const 2))
  have hr' : ∀ᵐ x ∂(μ.map X), (A * x).rank + 2 ≤ Fintype.card p :=
    (ae_map_iff hX (hrank (MeasurableSet.of_discrete
      (s := {q : ℕ | q + 2 ≤ Fintype.card p})))).mpr hr
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  rw [hXΨ.lintegral_comp_eq_lintegral_lintegral hX hΨ.aemeasurable hF, hΨ.map_eq,
    ← lintegral_map' hG.aemeasurable hX]
  refine lintegral_congr_ae (hr'.mono fun x hx => ?_)
  dsimp only
  rw [← ofReal_integral_eq_lintegral_ofReal
      (integrable_frobNorm_sub_generalizedNystrom_sq_of_fixed A x hid hx)
      (ae_of_all _ fun _ => sq_nonneg _),
    integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix A x hid hx]

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
the rank stays inside the expectation, with the factor `gaussianProjectionFactor q p`.
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

/-- The generalized Nyström error is integrable under a Gaussian co-range test matrix independent
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
\mathbf{\Omega})\|_{\mathsf{F}}^2\,,$$
the factor being `gaussianProjectionFactor ℓ p`. Any bound on the randomized SVD (Gaussian,
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

/-- **The generalized Nyström identity, Gaussian test matrices**: with
$\ell' = \min(\operatorname{rank}\mathbf{A}, \ell)$, the almost sure rank of the sketch, and
$\ell' + 2 \le p$, <!-- value gaussianProjectionFactor {\ell'} p -->
$$\mathbb{E}\|\mathbf{A}-\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\|_{\mathsf{F}}^2 =
\Bigl(1 + \frac{\ell'}{p - \ell' - 1}\Bigr)\,\mathbb{E}\|\mathbf{A}-\mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})\|_{\mathsf{F}}^2\,,$$
the factor being `gaussianProjectionFactor ℓ' p`.
[EpperlyWebber2026, proof of Theorem 4.2(a), $\gamma = 1$]; there for
$\operatorname{rank}\mathbf{A} \ge p$. Result: generalized-nystrom-expected-error -/
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
\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
the factors being `gaussianProjectionFactor ℓ p` and `gaussianProjectionFactor k ℓ`.
[TroppYurtseverUdellCevher2017, Theorem 4.3]; there with a minimum over $k$, not stated here
(one comparison rank per statement). Result: generalized-nystrom-expected-error -/
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

/-- **Gaussian test matrices at least as wide as the rank make generalized Nyström exact**: if
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
  exact range_mulVecLin_le_iff_exists_mul.mpr ⟨X ω, rfl⟩

end NLAlib
