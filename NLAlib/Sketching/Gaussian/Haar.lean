/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Haar.Moments
public import NLAlib.RandomMatrix.Haar.Sphere
public import NLAlib.RandomMatrix.Haar.Transfer
public import NLAlib.Sketching.Gaussian.Gaussian

/-!
# Haar sketches

The Haar sketch is $\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert}
\, \mathbf{Q}^{\mathsf{H}}$ for an $n \times k$ Haar frame $\mathbf{Q}$,
$\lvert k \rvert \le \lvert n \rvert$: $\lvert k \rvert$ orthonormal rows, scaled. It is written out
in each statement, `fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ`, with the hypothesis
`HasLaw Q (haarFrame n k) μ`; there is no named sketch law.

It is exactly isotropic, like a Gaussian sketch, and unlike it has a deterministic norm
$\|\mathbf{S}\|_2 = \sqrt{\lvert n \rvert / \lvert k \rvert}$. Its upper half is deterministic:
$(\mathbf{S}\mathbf{U})^{\mathsf{H}} (\mathbf{S}\mathbf{U})
\preceq (\lvert n \rvert / \lvert k \rvert) \, \mathbf{U}^{\mathsf{H}}\mathbf{U}$ almost surely, and
at $\lvert k \rvert = \lvert n \rvert$ the sketch is orthogonal, an exact embedding. Its Gram matrix
on $\mathbf{U}$ has the law of $(\lvert n \rvert / \lvert k \rvert) \, \mathbf{U}^{\mathsf{H}}
\mathbf{P}_{\mathbf{G}} \mathbf{U}$ for the range projector $\mathbf{P}_{\mathbf{G}}$ of an
$n \times k$ Gaussian $\mathbf{G}$ (the transfer of `NLAlib/RandomMatrix/Haar/Transfer.lean`); the
subspace embeddings built on it are in `NLAlib/Sketching/Gaussian/HaarEmbedding.lean`.

The JL tails are the projection tails of a uniform unit vector
(`NLAlib/RandomMatrix/Haar/Sphere.lean`), with the Gaussian's constants; the JL variance is
$2 (\lvert n \rvert - \lvert k \rvert) / (\lvert k \rvert (\lvert n \rvert + 2))$, below the
Gaussian's $2 / \lvert k \rvert$ and $0$ at $\lvert k \rvert = \lvert n \rvert$. The one-sided
projection tails give the JL moment property at every exponent, with the Gaussian's parameters,
and $O(\log(1/\delta)/\varepsilon^2)$ rows give it at $p = \max(2, \log(1/\delta))$.

Degenerate cases: for empty $k$, $\sqrt{\lvert n \rvert / 0} = 0$ and $\mathbf{S} = \mathbf{0}$,
hence `[Nonempty k]` on isotropy and the moments.

## Main results

* `NLAlib.isIsotropicSketch_of_hasLaw_haarFrame`, `NLAlib.ae_specNorm_eq_of_hasLaw_haarFrame`.
* `NLAlib.hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame`: the Gaussian transfer.
* `NLAlib.ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame`: the upper half.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_eq`: exact at
  $\lvert k \rvert = \lvert n \rvert$.
* `NLAlib.hasJLProperty_of_hasLaw_haarFrame`, `NLAlib.hasJLMoment_of_hasLaw_haarFrame`.
* `NLAlib.hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le` and its asymptotic form
  `NLAlib.exists_forall_hasJLProperty_of_hasLaw_haarFrame`.
* `NLAlib.hasJLMoment_subexponentialMomentBound_of_hasLaw_haarFrame`: the JL moment property at
  every $p > 0$; its size form `NLAlib.hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le` and
  asymptotic form `NLAlib.exists_forall_hasJLMoment_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k n p : Type*} [Fintype k]
  [Fintype n] [Fintype p] [DecidableEq k] {Q : Ω → Matrix n k ℝ} {U : Matrix n p ℝ}
  {t s ε δ : ℝ}

/-! ### Helpers -/

omit [DecidableEq k] in
/-- The scaling of the Haar sketch squares to $\lvert n \rvert / \lvert k \rvert$. -/
private theorem sqrt_mul_sqrt_card_div :
    √(Fintype.card n / Fintype.card k : ℝ) * √(Fintype.card n / Fintype.card k : ℝ) =
      (Fintype.card n / Fintype.card k : ℝ) :=
  Real.mul_self_sqrt (by positivity)

omit [DecidableEq k] in
/-- The squared length of $\mathbf{S}\mathbf{x}$: $\|\mathbf{S}\mathbf{x}\|^2
= (\lvert n \rvert / \lvert k \rvert) \|\mathbf{Q}^{\mathsf{H}}\mathbf{x}\|^2$. -/
private theorem norm_smul_conjTranspose_mulVec_sq (M : Matrix n k ℝ) (x : n → ℝ) :
    ‖WithLp.toLp 2 ((√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ) *ᵥ x)‖ ^ 2 =
      (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 (Mᴴ *ᵥ x)‖ ^ 2 := by
  rw [Matrix.smul_mulVec, WithLp.toLp_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by positivity)]

/-! ### Isotropy, norm and the Gaussian transfer -/

open scoped Matrix.Norms.L2Operator in
/-- **A Haar sketch is isotropic**: $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}]
= (\lvert n \rvert / \lvert k \rvert) \, \mathbb{E}[\mathbf{Q}\mathbf{Q}^{\mathsf{H}}] = \mathbf{I}$
(`NLAlib.integral_mul_conjTranspose_of_hasLaw_haarFrame`), exactly for $k$ nonempty,
as for a Gaussian sketch.
[MartinssonTropp2020, §8.9]. -/
theorem isIsotropicSketch_of_hasLaw_haarFrame [DecidableEq n] [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    IsIsotropicSketch (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  refine ⟨fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.conjTranspose_apply, star_trivial, smul_eq_mul]
    exact (memLp_apply_of_hasLaw_haarFrame hQ j i 2).const_mul _
  · have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
    have hN : (0 : ℝ) < Fintype.card n := hK.trans_le (Nat.cast_le.2 hk)
    have h (ω : Ω) : (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) =
        (Fintype.card n / Fintype.card k : ℝ) • (Q ω * (Q ω)ᴴ) := by
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.conjTranspose_conjTranspose,
        Matrix.smul_mul, Matrix.mul_smul, smul_smul, sqrt_mul_sqrt_card_div]
    simp only [h]
    rw [integral_smul, integral_mul_conjTranspose_of_hasLaw_haarFrame hQ hk, smul_smul,
      div_mul_div_comm, mul_comm (Fintype.card n : ℝ), div_self (by positivity), one_smul]

/-- **The norm of a Haar sketch is deterministic**:
$\|\mathbf{S}\|_2 = \sqrt{\lvert n \rvert / \lvert k \rvert}$ almost surely, since $\mathbf{Q}$ has
orthonormal columns (`NLAlib.HasOrthonormalCols.specNorm_eq_one`); for empty $k$ both sides are $0$.
[MartinssonTropp2020, §8.9]. -/
theorem ae_specNorm_eq_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    ∀ᵐ ω ∂μ, specNorm (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) =
      √(Fintype.card n / Fintype.card k : ℝ) := by
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hk] with ω hω
  rw [specNorm_smul, specNorm_conjTranspose, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rcases isEmpty_or_nonempty k with hk0 | hk0
  · rw [Fintype.card_eq_zero (α := k), Nat.cast_zero, div_zero, Real.sqrt_zero, zero_mul]
  · rw [hω.specNorm_eq_one, mul_one]

omit [Fintype p] in
/-- Gaussian transfer of the Haar Gram matrix:
$(\mathbf{S}\mathbf{U})^{\mathsf{H}} (\mathbf{S}\mathbf{U})$ has the law of
$(\lvert n \rvert / \lvert k \rvert) \, \mathbf{U}^{\mathsf{H}} \mathbf{P}_{\mathbf{G}} \mathbf{U}$,
$\mathbf{P}_{\mathbf{G}}$ the range projector of an $n \times k$ standard Gaussian $\mathbf{G}$, for
every $\mathbf{U}$; $\mathbf{Q}\mathbf{Q}^{\mathsf{H}}$ is the range projector of $\mathbf{Q}$
almost surely (`NLAlib.HasOrthonormalCols.rangeProjector_eq`), and
`NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{I}$ transfers it. -/
theorem hasLaw_conjTranspose_mul_self_mul_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (U : Matrix n p ℝ) :
    HasLaw (fun ω => (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U))
      ((gaussianMatrix n k).map fun G =>
        (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * rangeProjector G * U)) μ := by
  classical
  have hP := hasLaw_rangeProjector_mul_of_hasLaw_haarFrame (1 : Matrix n n ℝ) hQ
  simp only [Matrix.one_mul] at hP
  have hf : Measurable fun M : Matrix n n ℝ =>
      (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * M * U) :=
    ((measurable_const.matrix_mul measurable_id).matrix_mul measurable_const).matrix_const_smul _
  have h := HasLaw.fun_comp (Y := fun M : Matrix n n ℝ =>
    (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * M * U)) ⟨hf.aemeasurable, rfl⟩ hP
  rw [Measure.map_map hf measurable_rangeProjector] at h
  refine h.congr ?_
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hk] with ω hω
  rw [conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul, hω.rangeProjector_eq]

/-! ### Deterministic halves -/

omit [Fintype p] in
/-- The upper half of a Haar sketch is deterministic: $(\mathbf{S}\mathbf{U})^{\mathsf{H}}
(\mathbf{S}\mathbf{U}) \preceq (\lvert n \rvert / \lvert k \rvert)
\, \mathbf{U}^{\mathsf{H}}\mathbf{U}$ almost surely, for every $\mathbf{U}$, every shape, with no
parameter: $\mathbf{Q}\mathbf{Q}^{\mathsf{H}} \preceq \mathbf{I}$ because $\|\mathbf{Q}\|_2 \le 1$
(`NLAlib.ae_specNorm_le_one_of_hasLaw_haarFrame`,
`NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le`). -/
theorem ae_conjTranspose_mul_self_mul_le_smul_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame n k) μ) (U : Matrix n p ℝ) :
    ∀ᵐ ω ∂μ, (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U) ≤
      (Fintype.card n / Fintype.card k : ℝ) • (Uᴴ * U) := by
  classical
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ] with ω hω
  rw [conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul]
  have h1 : Q ω * (Q ω)ᴴ ≤ (1 : ℝ) • (1 : Matrix n n ℝ) := by
    have := (specNorm_sq_le_iff_conjTranspose_mul_self_le (T := (Q ω)ᴴ) zero_le_one).1
      (by rw [specNorm_conjTranspose]; nlinarith [specNorm_nonneg (Q ω)])
    rwa [Matrix.conjTranspose_conjTranspose] at this
  rw [one_smul] at h1
  have h2 := conjTranspose_mul_mul_le_conjTranspose_mul_mul h1 U
  rw [Matrix.mul_one] at h2
  rw [Matrix.le_iff] at h2 ⊢
  rw [← smul_sub]
  exact h2.smul (by positivity)

omit [Fintype p] in
/-- A square Haar sketch is an exact embedding: for $\lvert k \rvert = \lvert n \rvert$,
$\mathbf{S} = \mathbf{Q}^{\mathsf{H}}$ is orthogonal almost surely, so it is a subspace embedding
for every $\operatorname{range} \mathbf{U}$ with constants $1$, $1$ and failure probability $0$. -/
theorem hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_eq (hQ : HasLaw Q (haarFrame n k) μ)
    (hkn : Fintype.card k = Fintype.card n) (U : Matrix n p ℝ) :
    HasSubspaceEmbedding (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) U 1 1 0 μ := by
  classical
  have hae : ∀ᵐ ω ∂μ, IsSubspaceEmbedding (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ)
      U 1 1 := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hkn.le] with ω hω
    have hg : (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U)ᴴ *
        (√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ * U) = (1 : ℝ) • (Uᴴ * U) := by
      rw [conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul,
        hω.mul_conjTranspose_self_of_card_eq hkn.symm, Matrix.mul_one, hkn]
      rcases isEmpty_or_nonempty n with hn | hn
      · have : Uᴴ * U = 0 := by
          ext i j
          simp only [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty, Matrix.zero_apply]
        rw [this, smul_zero, smul_zero]
      · rw [div_self (by positivity)]
    exact ⟨by rw [IsSubspaceInjection, hg], by rw [hg]⟩
  unfold HasSubspaceEmbedding
  rw [Measure.real, ae_iff.1 hae, ENNReal.toReal_zero]

/-! ### Johnson–Lindenstrauss -/

omit [DecidableEq k] in
/-- $\|\mathbf{Q}^{\mathsf{H}}\mathbf{x}\| \le \|\mathbf{x}\|$ almost surely, in every shape. -/
private theorem ae_norm_conjTranspose_mulVec_le [DecidableEq k] (hQ : HasLaw Q (haarFrame n k) μ)
    (x : n → ℝ) : ∀ᵐ ω ∂μ, ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ] with ω hω
  refine (norm_toLp_mulVec_le _ x).trans ?_
  rw [specNorm_conjTranspose]
  nlinarith [norm_nonneg (WithLp.toLp 2 x)]

/-- The powers of $\|\mathbf{Q}^{\mathsf{H}}\mathbf{x}\|$ are integrable (they are bounded by those
of $\|\mathbf{x}\|$). -/
private theorem integrable_norm_conjTranspose_mulVec_pow (hQ : HasLaw Q (haarFrame n k) μ)
    (x : n → ℝ) (m : ℕ) : Integrable (fun ω => ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ m) μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hc : Continuous fun M : Matrix n k ℝ => ‖WithLp.toLp 2 (Mᴴ *ᵥ x)‖ ^ m := by fun_prop
  refine Integrable.of_bound (hc.measurable.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable
    (‖WithLp.toLp 2 x‖ ^ m) ?_
  filter_upwards [ae_norm_conjTranspose_mulVec_le hQ x] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) hω m

/-- **The fourth moment of $\|\mathbf{Q}^{\mathsf{H}}\mathbf{x}\|$**:
$$\mathbb{E}\|\mathbf{Q}^{\mathsf{H}}\mathbf{x}\|^4
= \|\mathbf{x}\|^4 \, \frac{\lvert k \rvert (\lvert k \rvert + 2)}
{\lvert n \rvert (\lvert n \rvert + 2)} \,,$$
from the law of $\mathbf{Q}^{\mathsf{H}}\mathbf{x}$ and the fourth moment of a projected uniform
unit vector. -/
private theorem integral_norm_conjTranspose_mulVec_pow_four [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (x : n → ℝ) :
    ∫ ω, ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 4 ∂μ = ‖WithLp.toLp 2 x‖ ^ 4 *
      (Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))) := by
  classical
  have : Nonempty n := by
    rw [← Fintype.card_pos_iff]
    exact Fintype.card_pos.trans_le hk
  rcases eq_or_ne x 0 with hx0 | hx0
  · simp [hx0]
  set r := ‖WithLp.toLp 2 x‖ with hrdef
  have hr : 0 < r := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  set y := r⁻¹ • x with hydef
  have hy : ‖WithLp.toLp 2 y‖ = 1 := by
    rw [hydef, WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hr.ne']
  have hxy (M : Matrix n k ℝ) : ‖WithLp.toLp 2 (Mᴴ *ᵥ x)‖ ^ 4 =
      r ^ 4 * ‖WithLp.toLp 2 (Mᴴ *ᵥ y)‖ ^ 4 := by
    rw [hydef, Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, norm_inv, norm_norm, mul_pow,
      inv_pow, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]
  simp only [hxy]
  rw [integral_const_mul]
  congr 1
  obtain ⟨e⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  have hV := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) e.injective
  have hlaw := hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame hQ hV hy
  have hF : Continuous fun w : k → ℝ => ‖WithLp.toLp 2 w‖ ^ 4 := by fun_prop
  have h1 := hlaw.integral_comp hF.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  have hmv : Measurable fun v : n → ℝ => (selectionMatrix e : Matrix n k ℝ)ᴴ *ᵥ v :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [h1, integral_map hmv.aemeasurable hF.aestronglyMeasurable]
  exact integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector HasLaw.id hV

/-- **Distributional Johnson–Lindenstrauss for a Haar sketch**, with the Gaussian's constants:
$$\mathbb{P}\bigl[\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert\bigr]
\le 2 e^{-\lvert k \rvert (\varepsilon^2/4 - \varepsilon^3/6)}$$
for every unit $\mathbf{x}$ and $\varepsilon \ge 0$; $\|\mathbf{S}\mathbf{x}\|^2
= (\lvert n \rvert / \lvert k \rvert) \|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2$ for $\mathbf{u}$
uniform on the sphere (`NLAlib.hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame`) and the
relative-deviation tail of `NLAlib/RandomMatrix/Haar/Sphere.lean`.
[Vershynin2018, Lemma 5.3.2], there with an unspecified constant $c$; the exponent of
Dasgupta and Gupta (2003). -/
theorem hasJLProperty_of_hasLaw_haarFrame (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 ≤ ε) :
    HasJLProperty (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε
      (2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6)))) μ := by
  classical
  intro x hx
  obtain ⟨e⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  have hV := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) e.injective
  have hlaw := hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame hQ hV hx
  have hT : MeasurableSet {w : k → ℝ | ε ≤ |(Fintype.card n / Fintype.card k : ℝ) *
      ‖WithLp.toLp 2 w‖ ^ 2 - 1|} := measurableSet_le measurable_const (by fun_prop)
  have hmv : Measurable fun v : n → ℝ => (selectionMatrix e : Matrix n k ℝ)ᴴ *ᵥ v :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  simp only [norm_smul_conjTranspose_mulVec_sq]
  rw [hlaw.measureReal_eq (p := fun w => ε ≤ |(Fintype.card n / Fintype.card k : ℝ) *
      ‖WithLp.toLp 2 w‖ ^ 2 - 1|) hT, map_measureReal_apply hmv hT]
  exact
    measureReal_abs_div_mul_norm_conjTranspose_mulVec_sq_sub_one_ge_le_of_hasLaw_uniformSphereVector
      HasLaw.id hV hε

/-- The squared distortion $(\|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2)^2$ of a Haar sketch is
integrable (it is bounded). -/
theorem integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame
    (hQ : HasLaw Q (haarFrame n k) μ) (x : n → ℝ) :
    Integrable (fun ω => (‖WithLp.toLp 2
      ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hc : Continuous fun M : Matrix n k ℝ => (‖WithLp.toLp 2
      ((√(Fintype.card n / Fintype.card k : ℝ) • Mᴴ) *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 := by
    fun_prop
  refine Integrable.of_bound (hc.measurable.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable
    (((Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 x‖ ^ 2 +
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2) ?_
  filter_upwards [ae_norm_conjTranspose_mulVec_le hQ x] with ω hω
  rw [norm_smul_conjTranspose_mulVec_sq, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), ← sq_abs]
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hω 2
  have hr : (0 : ℝ) ≤ Fintype.card n / Fintype.card k := by positivity
  have h3 : (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2 ≤
      (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 x‖ ^ 2 :=
    mul_le_mul_of_nonneg_left h2 hr
  have h4 : 0 ≤ (Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2 := by
    positivity
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_le.2 ⟨by nlinarith [sq_nonneg ‖WithLp.toLp 2 x‖],
    by nlinarith [sq_nonneg ‖WithLp.toLp 2 x‖]⟩) 2

/-- The JL variance of a Haar sketch:
$$\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2)^2
= \frac{2 (\lvert n \rvert - \lvert k \rvert)}
{\lvert k \rvert (\lvert n \rvert + 2)} \|\mathbf{x}\|^4$$
exactly for $k$ nonempty, below the Gaussian's $2 / \lvert k \rvert$ and $0$ at
$\lvert k \rvert = \lvert n \rvert$;
from $\mathbb{E}\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 = \lvert k \rvert / \lvert n \rvert$ and the
fourth moment `NLAlib.integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector`. -/
theorem integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (x : n → ℝ) :
    ∫ ω, (‖WithLp.toLp 2 ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ x)‖ ^ 2 -
      ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 ∂μ =
      2 * ((Fintype.card n : ℝ) - Fintype.card k) / (Fintype.card k * (Fintype.card n + 2)) *
        ‖WithLp.toLp 2 x‖ ^ 4 := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hN : (0 : ℝ) < Fintype.card n := hK.trans_le (Nat.cast_le.2 hk)
  have hexp (ω : Ω) : (‖WithLp.toLp 2 ((√(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) *ᵥ
      x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2) ^ 2 =
      (Fintype.card n / Fintype.card k : ℝ) ^ 2 * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 4 -
        2 * ‖WithLp.toLp 2 x‖ ^ 2 * ((Fintype.card n / Fintype.card k : ℝ) *
          ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2) + ‖WithLp.toLp 2 x‖ ^ 4 := by
    rw [norm_smul_conjTranspose_mulVec_sq]
    ring
  classical
  have hY := (isIsotropicSketch_of_hasLaw_haarFrame hQ hk).integral_norm_mulVec_sq x
  simp only [norm_smul_conjTranspose_mulVec_sq] at hY
  simp only [hexp]
  have i4 := integrable_norm_conjTranspose_mulVec_pow hQ x 4
  have i2 := integrable_norm_conjTranspose_mulVec_pow hQ x 2
  have hA : Integrable (fun ω => (Fintype.card n / Fintype.card k : ℝ) ^ 2 *
      ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 4 - 2 * ‖WithLp.toLp 2 x‖ ^ 2 *
        ((Fintype.card n / Fintype.card k : ℝ) * ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2)) μ :=
    (i4.const_mul _).sub ((i2.const_mul _).const_mul _)
  rw [integral_add hA (integrable_const _),
    integral_sub (i4.const_mul _) ((i2.const_mul _).const_mul _), integral_const_mul,
    integral_const_mul, hY, integral_const, probReal_univ, one_smul,
    integral_norm_conjTranspose_mulVec_pow_four hQ hk]
  field_simp
  ring

/-- **The JL moment property of a Haar sketch** at $p = 2$, for $k$ nonempty, with
$\delta = 2 (\lvert n \rvert -
\lvert k \rvert) / (\lvert k \rvert (\lvert n \rvert + 2) \varepsilon^2)$, from the exact variance.
[Woodruff2014, Definition 12], the property there. -/
theorem hasJLMoment_of_hasLaw_haarFrame [Nonempty k] (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε) :
    HasJLMoment (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε
      (2 * ((Fintype.card n : ℝ) - Fintype.card k) /
        (Fintype.card k * (Fintype.card n + 2) * ε ^ 2)) 2 μ := by
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · have h := integrable_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame hQ x
    rw [hx, one_pow] at h
    simpa only [Real.rpow_two, sq_abs] using h
  · have h := integral_norm_mulVec_sq_sub_norm_sq_sq_of_hasLaw_haarFrame hQ hk x
    rw [hx, one_pow, one_pow, mul_one] at h
    simp only [Real.rpow_two, sq_abs]
    rw [h]
    apply le_of_eq
    field_simp

/-- **The JL moment property of a Haar sketch at every order**: for $k$ nonempty,
$\lvert k\rvert \le \lvert n\rvert$, $\varepsilon > 0$, $p > 0$ and
$\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$ with $\mathbf{Q}$
an $n \times k$ Haar frame, the JL moment property holds with exponent $p$ and failure
probability <!-- value subexponentialMomentBound {(4/\lvert k \rvert)} {(4/\lvert k \rvert)} p -->
$$\delta = \frac{p(2(4/\lvert k \rvert))^{p/2}\Gamma(p/2) +
2p(2(4/\lvert k \rvert))^{p}\Gamma(p)}{\varepsilon^p}\,,$$
the numerator being `NLAlib.subexponentialMomentBound` at $v = b = 4/\lvert k\rvert$, the
Gaussian's: the one-sided projection tails of a uniform unit vector
(`NLAlib.measureReal_norm_conjTranspose_mulVec_sq_ge_mul_div_le_of_hasLaw_uniformSphereVector`,
`NLAlib.measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector`)
at $a = \lvert k\rvert/\lvert n\rvert$ give the sub-exponential JL tail
(`NLAlib.measureReal_abs_div_sub_one_ge_le_two_mul_exp`), which
`NLAlib.hasJLMoment_of_forall_hasJLProperty` integrates. Incomparable with
`NLAlib.hasJLMoment_of_hasLaw_haarFrame` (the exact variance, better at $p = 2$).
[Woodruff2014, Definition 12] for the property; [Vershynin2018, Lemma 5.3.2] for the Haar JL
tail, unspecified constant. -/
theorem hasJLMoment_subexponentialMomentBound_of_hasLaw_haarFrame [Nonempty k]
    (hQ : HasLaw Q (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε)
    {p : ℝ} (hp : 0 < p) :
    HasJLMoment (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε
      (subexponentialMomentBound (4 / Fintype.card k) (4 / Fintype.card k) p / ε ^ p) p μ := by
  classical
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hN : (0 : ℝ) < Fintype.card n := hK.trans_le (Nat.cast_le.2 hk)
  have hc : Continuous fun M : Matrix n k ℝ => √(Fintype.card n / Fintype.card k : ℝ) • Mᴴ := by
    fun_prop
  refine hasJLMoment_of_forall_hasJLProperty
    (S := fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ)
    (hc.measurable.comp_aemeasurable hQ.aemeasurable) (by positivity) (by positivity)
    (fun t ht => ?_) hε hp
  intro x hx
  obtain ⟨e⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  have hV := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) e.injective
  have hlaw := hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame hQ hV hx
  have hmv : Measurable fun v : n → ℝ => (selectionMatrix e : Matrix n k ℝ)ᴴ *ᵥ v :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  set a : ℝ := Fintype.card k / Fintype.card n with ha_def
  have ha : 0 < a := by positivity
  have hup : ∀ β : ℝ, 1 ≤ β → μ.real {ω | β * a ≤ ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β)) := by
    intro β hβ
    have hT : MeasurableSet {w : k → ℝ | β * a ≤ ‖WithLp.toLp 2 w‖ ^ 2} :=
      measurableSet_le measurable_const (by fun_prop)
    rw [hlaw.measureReal_eq (p := fun w => β * a ≤ ‖WithLp.toLp 2 w‖ ^ 2) hT,
      map_measureReal_apply hmv hT]
    exact measureReal_norm_conjTranspose_mulVec_sq_ge_mul_div_le_of_hasLaw_uniformSphereVector
      HasLaw.id hV hβ
  have hlow : ∀ β : ℝ, 0 < β → β ≤ 1 → μ.real {ω | ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2 ≤ β * a} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β)) := by
    intro β hβ0 hβ
    have hT : MeasurableSet {w : k → ℝ | ‖WithLp.toLp 2 w‖ ^ 2 ≤ β * a} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [hlaw.measureReal_eq (p := fun w => ‖WithLp.toLp 2 w‖ ^ 2 ≤ β * a) hT,
      map_measureReal_apply hmv hT]
    exact measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector
      HasLaw.id hV hβ0 hβ
  have h := measureReal_abs_div_sub_one_ge_le_two_mul_exp
    (Y := fun ω => ‖WithLp.toLp 2 ((Q ω)ᴴ *ᵥ x)‖ ^ 2) ha hK.le hup hlow ht.le
  have eY : ∀ y : ℝ, y / a = (Fintype.card n / Fintype.card k : ℝ) * y := by
    intro y
    rw [ha_def]
    field_simp
  simp only [eY] at h
  simp only [norm_smul_conjTranspose_mulVec_sq]
  refine h.trans (le_of_eq ?_)
  have e1 : t ^ 2 / (2 * (4 / (Fintype.card k : ℝ))) = Fintype.card k / 8 * t ^ 2 := by
    field_simp
    ring
  have e2 : t / (2 * (4 / (Fintype.card k : ℝ))) = Fintype.card k / 8 * t := by
    field_simp
    ring
  rw [e1, e2, ← mul_min_of_nonneg _ _ (by positivity)]

/-- **Haar JL moments, sample-size form**: for $\lvert k\rvert \le \lvert n\rvert$,
$0 < \varepsilon \le 1$, $\delta > 0$ and at
least <!-- value jlMomentDim \varepsilon \delta -->$128\max(2, \log(1/\delta))/\varepsilon^2$
rows (`jlMomentDim ε δ`), the Haar sketch
$\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$ has the JL moment
property with distortion $\varepsilon$, failure probability $\delta$ and exponent
$$\max(2, \log(1/\delta)) \,,$$
with the Gaussian sketch's size
(`NLAlib.hasJLMoment_of_hasLaw_gaussianMatrix_of_jlMomentDim_le`); approximate matrix
multiplication with failure probability $\delta$ follows
(`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le`). [Woodruff2014,
Definition 12 and Theorem 13], the property and AMM from it; the constants are this proof's.
Asymptotic form: `NLAlib.exists_forall_hasJLMoment_of_hasLaw_haarFrame`.
Result: jl-moment-haar -/
theorem hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk' : jlMomentDim ε δ ≤ Fintype.card k) :
    HasJLMoment (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε δ
      (max 2 (Real.log (1 / δ))) μ := by
  set p := max 2 (Real.log (1 / δ)) with hpdef
  have hp2 : 2 ≤ p := le_max_left _ _
  have hp0 : 0 < p := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hK : 128 * p ≤ ε ^ 2 * Fintype.card k := by
    rw [jlMomentDim_def, div_le_iff₀ hε2] at hk'
    linarith
  have hK0 : (0 : ℝ) < Fintype.card k := by
    by_contra h
    push Not at h
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hε2.le h]
  have : Nonempty k := Fintype.card_pos_iff.1 (by exact_mod_cast hK0)
  have hεp : 0 < ε ^ p := Real.rpow_pos_of_pos hε p
  have hb := subexponentialMomentBound_le_mul_exp_neg (v := 4 / (Fintype.card k : ℝ))
    (b := 4 / (Fintype.card k : ℝ)) (by positivity) (by positivity) hp2 hε
    (by rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hK0]; linarith)
    (by rw [div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hK0]; nlinarith)
  refine (hasJLMoment_subexponentialMomentBound_of_hasLaw_haarFrame hQ hk hε hp0).mono le_rfl
    ?_ hε.le hp0.le (div_nonneg (subexponentialMomentBound_nonneg (by positivity)
      (by positivity) hp0.le) hεp.le)
  rw [div_le_iff₀ hεp, mul_comm δ]
  refine hb.trans (mul_le_mul_of_nonneg_left ?_ hεp.le)
  calc Real.exp (-p) ≤ Real.exp (-Real.log (1 / δ)) :=
        Real.exp_le_exp.2 (neg_le_neg (le_max_right _ _))
    _ = δ := by rw [Real.exp_neg, Real.exp_log (by positivity), one_div, inv_inv]

/-- **Haar JL moments, asymptotic form**: $O(\log(1/\delta)/\varepsilon^2)$ rows suffice for the
Haar sketch $\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$,
$\lvert k\rvert \le \lvert n\rvert$, to have the JL moment property with distortion
$\varepsilon$, failure probability $\delta$ and exponent
$$\max(2, \log(1/\delta)) \,,$$
for $\varepsilon$ and $\delta$ below absolute constants; the constants come before every dimension.
Proved from `NLAlib.hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le` with $C = 384$,
$\varepsilon_0 = 1$ and $\delta \le 1/2$. [Woodruff2014, Definition 12 and Theorem 13].
Asymptotic: NLAlib.hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le
Result: jl-moment-haar -/
theorem exists_forall_hasJLMoment_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      [DecidableEq k] (μ : Measure Ω) (Q : Ω → Matrix n k ℝ) (ε δ : ℝ),
      HasLaw Q (haarFrame n k) μ → Fintype.card k ≤ Fintype.card n →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLMoment (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε δ
        (max 2 (Real.log (1 / δ))) μ := by
  refine ⟨384, 1, by norm_num, one_pos, fun μ Q ε δ hQ hkn hε hε1 hδ hδ2 hk => ?_⟩
  refine hasJLMoment_of_hasLaw_haarFrame_of_jlMomentDim_le hQ hkn hε hε1 hδ
    ((jlMomentDim_le hδ hδ2).trans (le_of_eq_of_le ?_ hk))
  ring

/-- **Haar distributional JL, sample-size form**: at
least <!-- value jlDim \varepsilon \delta -->$\log(2/\delta)/(\varepsilon^2/4 - \varepsilon^3/6)$
rows (`jlDim ε δ`) give the JL property of
$$\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert}\,\mathbf{Q}^{\mathsf{H}}$$
with distortion $\varepsilon$ and failure probability $\delta$, for $0 < \varepsilon < 3/2$ and
$\delta > 0$. [Vershynin2018, Lemma 5.3.2] (the tail form: for the projection $\mathbf{P}$ onto
a uniformly random $m$-dimensional subspace of $\mathbb{R}^n$ and a fixed $\mathbf{z}$,
$\|\mathbf{P}\mathbf{z}\| = (1 \pm \varepsilon)\sqrt{m/n}\,\|\mathbf{z}\|$ outside probability
$2e^{-c\varepsilon^2 m}$, with an unspecified constant $c$); here solved for the row
count, with the Gaussian's exponent. Asymptotic form:
`NLAlib.exists_forall_hasJLProperty_of_hasLaw_haarFrame`.
Result: jl-haar -/
theorem hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le (hQ : HasLaw Q (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hε : 0 < ε) (hε1 : ε < 3 / 2) (hδ : 0 < δ)
    (hk' : jlDim ε δ ≤ Fintype.card k) :
    HasJLProperty (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε δ μ := by
  have := hQ.isProbabilityMeasure_iff.2 inferInstance
  exact (hasJLProperty_of_hasLaw_haarFrame hQ hk hε.le).mono le_rfl
    (two_mul_exp_le_of_jlDim_le hε hε1 hδ hk')

/-- Haar distributional JL, asymptotic form: $O(\log(1/\delta)/\varepsilon^2)$ rows suffice
for the Haar sketch to have the JL property with distortion $\varepsilon$ and failure probability
$\delta$, for $\varepsilon$ and $\delta$ below absolute constants; the constants come before every
dimension. Proved from `NLAlib.hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le` with $C = 24$,
$\varepsilon_0 = 1$ and $\delta \le 1/2$.
Asymptotic: NLAlib.hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le -/
theorem exists_forall_hasJLProperty_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype n]
      [DecidableEq k] (μ : Measure Ω) (Q : Ω → Matrix n k ℝ) (ε δ : ℝ),
      HasLaw Q (haarFrame n k) μ → Fintype.card k ≤ Fintype.card n →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (Real.log (1 / δ) / ε ^ 2) ≤ Fintype.card k →
      HasJLProperty (fun ω => √(Fintype.card n / Fintype.card k : ℝ) • (Q ω)ᴴ) ε δ μ := by
  refine ⟨24, 1, by norm_num, one_pos, fun μ Q ε δ hQ hkn hε hε1 hδ hδ2 hk => ?_⟩
  have hl2 := Real.log_two_div_le_two_mul_log_one_div hδ hδ2
  refine hasJLProperty_of_hasLaw_haarFrame_of_jlDim_le hQ hkn hε (by linarith) hδ
    ((jlDim_le hε1 hδ (by linarith)).trans (le_trans ?_ hk))
  rw [mul_div_assoc']
  exact div_le_div_of_nonneg_right (by linarith) (sq_nonneg ε)

end NLAlib
