/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlib.RandomMatrix.Haar.Uniqueness
public import NLAlib.ForMathlib.Probability.Distributions.Beta

/-!
# Projections of a uniform unit vector

For $\mathbf{u}$ uniform on the unit sphere of $\mathbb{R}^n$ and `V : Matrix n k ℝ` with
orthonormal columns, $\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2$ is the squared length of the
projection of $\mathbf{u}$ onto a fixed $\lvert k \rvert$-dimensional subspace. Its law does not
depend on $\mathbf{V}$, and it is the law of $\|\mathbf{Q}^{\mathsf{H}}\mathbf{x}\|^2$ for an
$n \times k$ Haar frame $\mathbf{Q}$ and a fixed unit $\mathbf{x}$: this is the Haar sketch's
Johnson–Lindenstrauss variable. This file gives the law, the Chernoff tails of Dasgupta and Gupta
(2003) around the mean $\lvert k \rvert / \lvert n \rvert$, on either side, and the exact fourth
moment
$$\mathbb{E}\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^4
= \frac{\lvert k \rvert (\lvert k \rvert + 2)}{\lvert n \rvert (\lvert n \rvert + 2)} \,.$$

The tails go through $\mathbf{u} = \mathbf{g} / \|\mathbf{g}\|$ for a standard Gaussian
$\mathbf{g}$
(`NLAlib.hasLaw_inv_norm_smul_of_hasLaw_gaussianVector`), the orthogonal
$\mathbf{W} = \begin{bmatrix} \mathbf{V} & \mathbf{V}_{\perp} \end{bmatrix}^{\mathsf{H}}$ from
`NLAlib.HasOrthonormalCols.exists_fromCols` and `NLAlib.hasLaw_mulVec_of_hasLaw_gaussianVector`,
which reduce $\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 \le c$ to the event
$0 \le \sum_i \theta_i \mathbf{g}_i^2$ with two weights, and Chernoff's bound with
`NLAlib.integral_exp_sum_mul_sq_of_hasLaw_gaussianVector`. The fourth moment uses invariance
alone (`NLAlib.HasOrthonormalCols.uniformSphereVector_map_conjTranspose_mulVec_eq`: the law of
$\mathbf{V}^{\mathsf{H}}\mathbf{u}$ depends only on the column type of $\mathbf{V}$):
$\sum_i \mathbf{u}_i^2 = 1$ and a $45^\circ$ rotation give
$\mathbb{E}\,\mathbf{u}_1^4 = 3 \, \mathbb{E}\,\mathbf{u}_1^2 \mathbf{u}_2^2$ when
$\lvert n \rvert \ge 2$; for $\lvert n \rvert = 1$, $\mathbf{u} = \pm 1$.

For $0 < k < n$, $\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 \sim \mathrm{Beta}(k/2, (n-k)/2)$: the
two blocks of $\mathbf{W}^{\mathsf{H}}\mathbf{g}$ give independent chi-square laws, whose ratio is
Beta. With the Beta sub-Gaussian proxy [MarchalArbel2017],
$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 - k/n$ has variance proxy $1/(2(n+2))$ for every
$0 \le k \le n$, and Hoeffding gives the tail $2e^{-m(n+2)\tau^2}$ of the mean of $m$ independent
copies (the last theorem of the file; its name is too long for the list below).

## Main results

* `NLAlib.hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame`: $\mathbf{Q}^{\mathsf{H}}\mathbf{x}$ has
  the law of $\mathbf{V}^{\mathsf{H}}\mathbf{u}$.
* `NLAlib.measureReal_norm_conjTranspose_mulVec_sq_ge_mul_div_le_of_hasLaw_uniformSphereVector`,
  `NLAlib.measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector`:
  the two Chernoff tails.
* The relative deviation (in namespace `NLAlib`):
  `measureReal_abs_div_mul_norm_conjTranspose_mulVec_sq_sub_one_ge_le_of_hasLaw_uniformSphereVector`
* `NLAlib.ae_norm_eq_one_uniformSphereVector`: a uniform unit vector has norm $1$ almost surely.
* `NLAlib.HasOrthonormalCols.uniformSphereVector_map_conjTranspose_mulVec_eq`: sphere invariance.
* `NLAlib.integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector`: the fourth
  moment.
* `NLAlib.hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector`: the Beta law.
* `NLAlib.hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector`:
  the sub-Gaussian proxy $1/(2(n+2))$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] [DecidableEq k] {u : Ω → n → ℝ} {V : Matrix n k ℝ} {ε β : ℝ}

/-! ### Helpers -/

omit [DecidableEq k] in
/-- The projected length of a normalised vector. -/
private theorem norm_conjTranspose_mulVec_inv_norm_smul_sq (V : Matrix n k ℝ) (g : n → ℝ) :
    ‖WithLp.toLp 2 (Vᴴ *ᵥ (‖WithLp.toLp 2 g‖⁻¹ • g))‖ ^ 2 =
      ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 / ‖WithLp.toLp 2 g‖ ^ 2 := by
  rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, mul_pow, norm_inv, norm_norm, inv_pow,
    inv_mul_eq_div]

/-- The two blocks of $\mathbf{W}^{\mathsf{H}}\mathbf{g}$ for a square
$\mathbf{W} = \begin{bmatrix} \mathbf{V} & \mathbf{V}' \end{bmatrix}$ with orthonormal columns
($\lvert k\rvert + \lvert p\rvert = \lvert n\rvert$): the first carries
$\|\mathbf{V}^{\mathsf{H}}\mathbf{g}\|^2$, and the two together carry $\|\mathbf{g}\|^2$. -/
private theorem norm_sq_conjTranspose_mulVec_eq_sum_inl_and_norm_sq_eq_add {p : Type*}
    [Fintype p] [DecidableEq p] {V' : Matrix n p ℝ}
    (hVV' : HasOrthonormalCols (Matrix.fromCols V V'))
    (hcard : Fintype.card k + Fintype.card p = Fintype.card n) (g : n → ℝ) :
    ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 = ∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2 ∧
      ‖WithLp.toLp 2 g‖ ^ 2 = ∑ i, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) ^ 2 +
        ∑ j, ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inr j) ^ 2 := by
  classical
  have hWn : HasOrthonormalCols (Matrix.fromCols V V')ᴴ :=
    hVV'.conjTranspose_of_card_eq (by rw [Fintype.card_sum]; exact hcard.symm)
  have hWl (i : k) : ((Matrix.fromCols V V')ᴴ *ᵥ g) (Sum.inl i) = (Vᴴ *ᵥ g) i := by
    simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Matrix.fromCols_apply_inl]
  refine ⟨by simp only [EuclideanSpace.real_norm_sq_eq, hWl], ?_⟩
  rw [← Fintype.sum_sum_type (fun x => ((Matrix.fromCols V V')ᴴ *ᵥ g) x ^ 2),
    ← hWn.norm_toLp_mulVec g, EuclideanSpace.real_norm_sq_eq]

/-- A probability law of $\mathbf{u}$ transfers an event to the normalised Gaussian
vector. -/
private theorem measureReal_mem_eq_gaussianVector (hu : HasLaw u (uniformSphereVector n) μ)
    {S : Set (n → ℝ)} (hS : MeasurableSet S) :
    μ.real {ω | u ω ∈ S} = (gaussianVector n).real {g | ‖WithLp.toLp 2 g‖⁻¹ • g ∈ S} := by
  rw [hu.measureReal_eq (p := (· ∈ S)) hS, uniformSphereVector]
  exact map_measureReal_apply measurable_inv_norm_smul hS

/-- **Chernoff's bound for a weighted sum of squared Gaussians**: for a standard Gaussian
vector $\mathbf{g}$ and weights $\varphi_i < 1/2$,
$\mathbb{P}[0 \le \sum_i \varphi_i \mathbf{g}_i^2] \le \prod_i (1 - 2\varphi_i)^{-1/2}$, in
exponential form. -/
private theorem measureReal_nonneg_sum_mul_sq_le {ι : Type*} [Fintype ι] {g : Ω → ι → ℝ}
    (hg : HasLaw g (gaussianVector ι) μ) {φ : ι → ℝ} (hφ : ∀ i, 2 * φ i < 1) :
    μ.real {ω | 0 ≤ ∑ i, φ i * g ω i ^ 2} ≤
      Real.exp (-(1 / 2) * ∑ i, Real.log (1 - 2 * φ i)) := by
  have := hg.isProbabilityMeasure_iff.2 inferInstance
  have hI := integral_exp_sum_mul_sq_of_hasLaw_gaussianVector hg hφ
  have hprod : ∏ i, (1 - 2 * φ i) ^ (-(1 / 2 : ℝ)) =
      Real.exp (-(1 / 2) * ∑ i, Real.log (1 - 2 * φ i)) := by
    rw [Finset.mul_sum, Real.exp_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Real.rpow_def_of_pos (by linarith [hφ i]), mul_comm]
  have hint : Integrable (fun ω => Real.exp (1 * ∑ i, φ i * g ω i ^ 2)) μ := by
    by_contra h
    simp only [one_mul] at h
    rw [integral_undef h, hprod] at hI
    exact (Real.exp_pos _).ne hI
  have h := measure_ge_le_exp_mul_mgf (X := fun ω => ∑ i, φ i * g ω i ^ 2) 0 zero_le_one hint
  simp only [mul_zero, Real.exp_zero, one_mul, mgf] at h
  rwa [hI, hprod] at h

/-- **The two-weight Chernoff bound for a projected uniform unit vector**: an event $S$ on which
$0 \le \varphi_1 \|\mathbf{V}^{\mathsf{H}}\mathbf{g}\|^2 +
\varphi_2 (\|\mathbf{g}\|^2 - \|\mathbf{V}^{\mathsf{H}}\mathbf{g}\|^2)$ for the unnormalised
$\mathbf{g}$ has probability at most
$$\exp\bigl(-\bigl(\lvert k \rvert \log(1 - 2\varphi_1) +
(\lvert n \rvert - \lvert k \rvert) \log(1 - 2\varphi_2)\bigr)/2\bigr) \,.$$
The orthogonal $\begin{bmatrix} \mathbf{V} & \mathbf{V}_{\perp} \end{bmatrix}^{\mathsf{H}}$ turns
$\|\mathbf{V}^{\mathsf{H}}\mathbf{g}\|^2$ and
$\|\mathbf{g}\|^2 - \|\mathbf{V}^{\mathsf{H}}\mathbf{g}\|^2$ into sums of $\lvert k \rvert$ and
$\lvert n \rvert - \lvert k \rvert$ independent squared Gaussians. -/
private theorem measureReal_mem_le_of_two_weights (hu : HasLaw u (uniformSphereVector n) μ)
    (hV : HasOrthonormalCols V) {S : Set (n → ℝ)} (hS : MeasurableSet S) {φ₁ φ₂ : ℝ}
    (h₁ : 2 * φ₁ < 1) (h₂ : Fintype.card k < Fintype.card n → 2 * φ₂ < 1)
    (hSφ : ∀ g : n → ℝ, ‖WithLp.toLp 2 g‖⁻¹ • g ∈ S →
      0 ≤ φ₁ * ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 +
        φ₂ * (‖WithLp.toLp 2 g‖ ^ 2 - ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2)) :
    μ.real {ω | u ω ∈ S} ≤ Real.exp (-(1 / 2) * (Fintype.card k * Real.log (1 - 2 * φ₁) +
      ((Fintype.card n : ℝ) - Fintype.card k) * Real.log (1 - 2 * φ₂))) := by
  classical
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hV.card_le
  have hcard : Fintype.card k + Fintype.card (Fin c) = Fintype.card n := by
    rw [Fintype.card_fin]
    exact hc.symm
  obtain ⟨V', hV'⟩ := hV.exists_fromCols (p := Fin c) hcard
  set W : Matrix (k ⊕ Fin c) n ℝ := (Matrix.fromCols V V')ᴴ with hWdef
  have hW : HasOrthonormalCols Wᴴ := by
    rwa [hWdef, Matrix.conjTranspose_conjTranspose]
  have hsplit (g : n → ℝ) : ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 = ∑ i, (W *ᵥ g) (Sum.inl i) ^ 2 ∧
      ‖WithLp.toLp 2 g‖ ^ 2 - ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 =
        ∑ j, (W *ᵥ g) (Sum.inr j) ^ 2 := by
    obtain ⟨h1, h2⟩ := norm_sq_conjTranspose_mulVec_eq_sum_inl_and_norm_sq_eq_add hV' hcard g
    rw [← hWdef] at h1 h2
    exact ⟨h1, by rw [h2, h1]; ring⟩
  have hWg : HasLaw (fun g : n → ℝ => W *ᵥ g) (gaussianVector (k ⊕ Fin c)) (gaussianVector n) :=
    hasLaw_mulVec_of_hasLaw_gaussianVector HasLaw.id hW
  set φ : k ⊕ Fin c → ℝ := Sum.elim (fun _ => φ₁) (fun _ => φ₂) with hφdef
  have hφ : ∀ j, 2 * φ j < 1 := by
    rintro (i | j)
    · exact h₁
    · refine h₂ ?_
      rw [hc]
      have := j.pos
      omega
  rw [measureReal_mem_eq_gaussianVector hu hS]
  calc _ ≤ (gaussianVector n).real {g | 0 ≤ ∑ j, φ j * (W *ᵥ g) j ^ 2} := by
        refine measureReal_mono (fun g hg => ?_) (measure_ne_top _ _)
        have h := hSφ g hg
        obtain ⟨h1, h2⟩ := hsplit g
        rw [h2, h1] at h
        simp only [Set.mem_ofPred_eq, Fintype.sum_sum_type, hφdef, Sum.elim_inl, Sum.elim_inr,
          ← Finset.mul_sum]
        exact h
    _ ≤ _ := measureReal_nonneg_sum_mul_sq_le hWg hφ
    _ = _ := by
        simp only [Fintype.sum_sum_type, hφdef, Sum.elim_inl, Sum.elim_inr, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc, Nat.cast_add]
        ring_nf

/-- Bessel's inequality for $\mathbf{V}^{\mathsf{H}}\mathbf{g}$, squared, and its consequence
at $\mathbf{g} = \mathbf{0}$. -/
private theorem norm_conjTranspose_mulVec_sq_le (hV : HasOrthonormalCols V) (g : n → ℝ) :
    ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 ≤ ‖WithLp.toLp 2 g‖ ^ 2 ∧
      (‖WithLp.toLp 2 g‖ ^ 2 = 0 → ‖WithLp.toLp 2 (Vᴴ *ᵥ g)‖ ^ 2 = 0) := by
  have h := pow_le_pow_left₀ (norm_nonneg _) (hV.norm_toLp_conjTranspose_mulVec_le g) 2
  exact ⟨h, fun h0 => le_antisymm (h0 ▸ h) (sq_nonneg _)⟩

/-- The two Chernoff weights at $\beta$, $\varphi_1 = (1 - 1/\beta)/2$ and
$\varphi_2 = -a \varphi_1 / (1 - a)$ with $a = \beta \lvert k \rvert / \lvert n \rvert < 1$, make
the event $0 \le \varphi_1 X + \varphi_2 (G - X)$ the event $0 \le \varphi_1 (X - a G)$, for reals
$X$ and $G$. -/
private theorem nonneg_two_weights {a φ₁ X G : ℝ} (ha : a < 1) (h : 0 ≤ φ₁ * (X - a * G)) :
    0 ≤ φ₁ * X + -(a * φ₁ / (1 - a)) * (G - X) := by
  have h1 : (1 - a) ≠ 0 := by linarith
  have : φ₁ * X + -(a * φ₁ / (1 - a)) * (G - X) = φ₁ * (X - a * G) / (1 - a) := by
    field_simp
    ring
  rw [this]
  exact div_nonneg h (by linarith)

/-- $1 - 2 \varphi_2 = (N - K)/(N - \beta K)$ for the second Chernoff weight. -/
private theorem one_sub_two_mul_weight {K N β : ℝ} (hβ : 0 < β) (hN : 0 < N)
    (ha : β * (K / N) < 1) :
    1 - 2 * -(β * (K / N) * ((1 - β⁻¹) / 2) / (1 - β * (K / N))) = (N - K) / (N - β * K) := by
  have h1 : 1 - β * (K / N) ≠ 0 := by linarith
  have h2 : N - β * K ≠ 0 := by
    rw [← mul_div_assoc, div_lt_one hN] at ha
    linarith
  field_simp
  ring

/-- The exponent reached by the two Chernoff weights is at most
$(K/2)(1 - \beta + \log \beta)$ ($\log x \le x - 1$ on the second factor). -/
private theorem exponent_two_weights_le {K N β : ℝ} (hKN : K ≤ N) (hβ : 0 < β)
    (ha : β * (K / N) < 1) (hN : 0 < N) (hc : K < N ∨ β ≤ 1) :
    -(1 / 2) * (K * Real.log (1 - 2 * ((1 - β⁻¹) / 2)) + (N - K) * Real.log (1 - 2 *
      -(β * (K / N) * ((1 - β⁻¹) / 2) / (1 - β * (K / N))))) ≤
      K / 2 * (1 - β + Real.log β) := by
  have h1 : 1 - 2 * ((1 - β⁻¹) / 2) = β⁻¹ := by ring
  rw [h1, Real.log_inv, one_sub_two_mul_weight hβ hN ha]
  have hNb : 0 < N - β * K := by
    rw [← mul_div_assoc, div_lt_one hN] at ha
    linarith
  rcases hKN.lt_or_eq with hlt | heq
  · have hNK : 0 < N - K := by linarith
    have hlog := Real.log_le_sub_one_of_pos (x := (N - β * K) / (N - K)) (by positivity)
    rw [Real.log_div hNb.ne' hNK.ne'] at hlog
    rw [Real.log_div hNK.ne' hNb.ne']
    have h3 : (N - β * K) / (N - K) - 1 = K * (1 - β) / (N - K) := by
      field_simp
      ring
    rw [h3] at hlog
    have h2 : (N - K) * (Real.log (N - β * K) - Real.log (N - K)) ≤ K * (1 - β) := by
      have := mul_le_mul_of_nonneg_left hlog hNK.le
      rwa [mul_div_cancel₀ _ hNK.ne'] at this
    nlinarith
  · subst heq
    have hKN' : 0 ≤ K := by
      by_contra h
      have : β * (K / K) = β := by rw [div_self (by linarith), mul_one]
      nlinarith
    rcases hc with hc | hc
    · exact absurd hc (lt_irrefl _)
    · simp only [sub_self, zero_mul, add_zero]
      nlinarith [mul_nonneg hKN' (sub_nonneg.2 hc)]

/-- A Haar frame applied to a fixed unit vector: for an $n \times k$ Haar frame $\mathbf{Q}$
and a unit $\mathbf{x}$, $\mathbf{Q}^{\mathsf{H}}\mathbf{x}$ has the law of
$\mathbf{V}^{\mathsf{H}}\mathbf{u}$ for $\mathbf{u}$ uniform on the sphere and any $\mathbf{V}$ with
orthonormal columns (`hV` gives $\lvert k \rvert \le \lvert n \rvert$). By left invariance
(`NLAlib.HasOrthonormalCols.exists_mul_eq` sends $\mathbf{x}$ to a coordinate vector),
$\mathbf{Q} \sim \mathbf{P}\mathbf{V}$ for a square Haar frame $\mathbf{P}$
(`NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`), and a column of $\mathbf{P}^{\mathsf{H}}$
(`NLAlib.hasLaw_col_of_hasLaw_haarFrame`). -/
theorem hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame {Q : Ω → Matrix n k ℝ}
    (hQ : HasLaw Q (haarFrame n k) μ) (hV : HasOrthonormalCols V) {x : n → ℝ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) :
    HasLaw (fun ω => (Q ω)ᴴ *ᵥ x) ((uniformSphereVector n).map (Vᴴ *ᵥ ·)) μ := by
  classical
  have hcol : HasLaw (fun P : Matrix n n ℝ => Pᴴ *ᵥ x) (uniformSphereVector n)
      (haarFrame n n) := by
    refine (hasLaw_col_unit_of_hasLaw_haarFrame (hasLaw_mul_const_of_hasLaw_haarFrame
      (hasLaw_conjTranspose_of_hasLaw_haarFrame HasLaw.id) le_rfl
      (hasOrthonormalCols_replicateCol hx))).congr (ae_of_all _ fun P => ?_)
    funext i
    simp only [id, Matrix.mul_apply, Matrix.replicateCol_apply, Matrix.mulVec, dotProduct]
  have hVm : HasLaw (fun w : n → ℝ => Vᴴ *ᵥ w) ((uniformSphereVector n).map (Vᴴ *ᵥ ·))
      (uniformSphereVector n) :=
    ⟨(continuous_const.matrix_mulVec continuous_id).measurable.aemeasurable, rfl⟩
  refine HasLaw.comp_of_hasLaw_comp (f := fun M : Matrix n k ℝ => Mᴴ *ᵥ x)
    (X := fun P : Matrix n n ℝ => P * V) ?_
    (hasLaw_mul_const_of_hasLaw_haarFrame HasLaw.id le_rfl hV) hQ ?_
  · exact ((continuous_id.matrix_conjTranspose).matrix_mulVec
      continuous_const).measurable.aemeasurable
  · refine (hVm.comp hcol).congr (ae_of_all _ fun P => ?_)
    simp only [Function.comp_apply, Matrix.conjTranspose_mul, Matrix.mulVec_mulVec]

/-- The upper tail when $\beta \lvert k \rvert / \lvert n \rvert \ge 1$: on the event
$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\| = \|\mathbf{u}\|$, so the second Chernoff weight alone,
taken large, gives the bound; for $\lvert k \rvert = \lvert n \rvert$ the event is empty. -/
private theorem measureReal_upper_tail_of_one_le (hu : HasLaw u (uniformSphereVector n) μ)
    (hV : HasOrthonormalCols V) (hβ1 : 1 < β) (hN : (0 : ℝ) < Fintype.card n)
    (ha : 1 ≤ β * (Fintype.card k / Fintype.card n))
    (hS : MeasurableSet {w : n → ℝ |
      β * (Fintype.card k / Fintype.card n) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 2}) :
    μ.real {ω | u ω ∈ {w : n → ℝ |
      β * (Fintype.card k / Fintype.card n) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 2}} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β)) := by
  set K : ℝ := (Fintype.card k : ℝ) with hKdef
  set N : ℝ := (Fintype.card n : ℝ) with hNdef
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hKN : K ≤ N := Nat.cast_le.2 hV.card_le
  rcases (Nat.cast_le.1 hKN).lt_or_eq with hlt | heq
  · have hlt' : K < N := Nat.cast_lt.2 hlt
    have hL : 0 ≤ -(K / (N - K)) * (1 - β + Real.log β) := by
      have := Real.log_le_sub_one_of_pos (by linarith : 0 < β)
      have : 0 ≤ K / (N - K) := div_nonneg hK (by linarith)
      nlinarith
    set L := -(K / (N - K)) * (1 - β + Real.log β) with hLdef
    refine (measureReal_mem_le_of_two_weights hu hV hS (φ₁ := 0)
      (φ₂ := (1 - Real.exp L) / 2) (by norm_num) (fun _ => by linarith [Real.exp_pos L])
      ?_).trans (le_of_eq ?_)
    · intro g hg
      rw [Set.mem_ofPred_eq, norm_conjTranspose_mulVec_inv_norm_smul_sq] at hg
      rw [zero_mul, zero_add]
      refine mul_nonneg_of_nonpos_of_nonpos ?_ ?_
      · linarith [Real.one_le_exp hL]
      · obtain ⟨hle, h0⟩ := norm_conjTranspose_mulVec_sq_le hV g
        rcases (sq_nonneg ‖WithLp.toLp 2 g‖).eq_or_lt with hG | hG
        · rw [← hG, h0 hG.symm, sub_self]
        · rw [le_div_iff₀ hG] at hg
          nlinarith
    · rw [show 1 - 2 * ((1 - Real.exp L) / 2) = Real.exp L by ring, Real.log_exp, mul_zero,
        sub_zero, Real.log_one, mul_zero, zero_add, hLdef, ← hKdef, ← hNdef]
      have : N - K ≠ 0 := by linarith
      congr 1
      field_simp
  · rw [measureReal_mem_eq_gaussianVector hu hS]
    have hempty : {g : n → ℝ | ‖WithLp.toLp 2 g‖⁻¹ • g ∈
        {w : n → ℝ | β * (K / N) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 2}} = ∅ := by
      ext g
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      rw [norm_conjTranspose_mulVec_inv_norm_smul_sq]
      have hKN1 : K / N = 1 := by
        rw [div_eq_one_iff_eq hN.ne', hKdef, hNdef, heq]
      rw [hKN1, mul_one]
      obtain ⟨hle, _⟩ := norm_conjTranspose_mulVec_sq_le hV g
      rcases (sq_nonneg ‖WithLp.toLp 2 g‖).eq_or_lt with hG | hG
      · rw [← hG, div_zero]
        linarith
      · exact lt_of_le_of_lt (div_le_one_of_le₀ hle hG.le) hβ1
    rw [hempty, measureReal_empty]
    positivity

/-- **Projection of a uniform unit vector, upper tail**: for $\mathbf{u}$ uniform on the unit
sphere, $\mathbf{V}$ with orthonormal columns and $\beta \ge 1$,
$$\mathbb{P}\bigl[\beta \lvert k \rvert / \lvert n \rvert
\le \|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2\bigr]
\le e^{(\lvert k \rvert/2)(1 - \beta + \log \beta)} \,.$$
The exponent of Dasgupta and Gupta (2003); [Vershynin2018, Lemma 5.3.2] has the fact
with an unspecified constant $c$. The $\chi^2_{\lvert k \rvert}$ tail
`NLAlib.measureReal_norm_sq_ge_mul_card_le_of_hasLaw_gaussianVector` is the limit
$\lvert n \rvert \to \infty$. -/
theorem measureReal_norm_conjTranspose_mulVec_sq_ge_mul_div_le_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) (hβ : 1 ≤ β) :
    μ.real {ω | β * (Fintype.card k / Fintype.card n) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β)) := by
  have := hu.isProbabilityMeasure_iff.2 inferInstance
  set K : ℝ := (Fintype.card k : ℝ) with hKdef
  set N : ℝ := (Fintype.card n : ℝ) with hNdef
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hKN : K ≤ N := Nat.cast_le.2 hV.card_le
  rcases hβ.eq_or_lt with rfl | hβ1
  · simp only [sub_self, Real.log_one, add_zero, mul_zero, Real.exp_zero]
    exact measureReal_le_one
  rcases hK.eq_or_lt with hK0 | hK0
  · simp only [← hK0, zero_div, zero_mul, Real.exp_zero]
    exact measureReal_le_one
  have hN : 0 < N := hK0.trans_le hKN
  have hS : MeasurableSet {w : n → ℝ | β * (K / N) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 2} :=
    measurableSet_le measurable_const (by fun_prop)
  change μ.real {ω | u ω ∈ {w : n → ℝ | β * (K / N) ≤ ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 2}} ≤ _
  by_cases ha : β * (K / N) < 1
  · have hKN' : K < N := by
      by_contra h
      have : K / N = 1 := by rw [div_eq_one_iff_eq hN.ne']; linarith
      rw [this, mul_one] at ha
      linarith
    refine (measureReal_mem_le_of_two_weights hu hV hS (φ₁ := (1 - β⁻¹) / 2)
      (φ₂ := -(β * (K / N) * ((1 - β⁻¹) / 2) / (1 - β * (K / N)))) ?_ ?_ ?_).trans
      (Real.exp_le_exp.2 (exponent_two_weights_le hKN (by linarith) ha hN (Or.inl hKN')))
    · have : 0 < β⁻¹ := by positivity
      linarith
    · intro _
      have h := one_sub_two_mul_weight (K := K) (by linarith) hN ha
      have hNb : 0 < N - β * K := by
        rw [← mul_div_assoc, div_lt_one hN] at ha
        linarith
      have : 0 < (N - K) / (N - β * K) := div_pos (by linarith) hNb
      linarith
    · intro g hg
      rw [Set.mem_ofPred_eq, norm_conjTranspose_mulVec_inv_norm_smul_sq] at hg
      refine nonneg_two_weights ha (mul_nonneg ?_ ?_)
      · have : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hβ1.le
        linarith
      · obtain ⟨_, h0⟩ := norm_conjTranspose_mulVec_sq_le hV g
        rcases (sq_nonneg ‖WithLp.toLp 2 g‖).eq_or_lt with hG | hG
        · rw [← hG, h0 hG.symm]
          simp
        · rw [le_div_iff₀ hG] at hg
          linarith
  · exact measureReal_upper_tail_of_one_le hu hV hβ1 hN (not_lt.1 ha) hS

/-- **Projection of a uniform unit vector, lower tail**: for $\mathbf{u}$ uniform on the unit
sphere, $\mathbf{V}$ with orthonormal columns and $0 < \beta \le 1$,
$$\mathbb{P}\bigl[\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2
\le \beta \lvert k \rvert / \lvert n \rvert\bigr]
\le e^{(\lvert k \rvert/2)(1 - \beta + \log \beta)} \,.$$
The exponent of Dasgupta and Gupta (2003); [Vershynin2018, Lemma 5.3.2] has the fact
with an unspecified constant $c$. -/
theorem measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) (hβ0 : 0 < β)
    (hβ : β ≤ 1) :
    μ.real {ω | ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 ≤ β * (Fintype.card k / Fintype.card n)} ≤
      Real.exp (Fintype.card k / 2 * (1 - β + Real.log β)) := by
  have := hu.isProbabilityMeasure_iff.2 inferInstance
  set K : ℝ := (Fintype.card k : ℝ) with hKdef
  set N : ℝ := (Fintype.card n : ℝ) with hNdef
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hKN : K ≤ N := Nat.cast_le.2 hV.card_le
  rcases hβ.eq_or_lt with rfl | hβ1
  · simp only [sub_self, Real.log_one, add_zero, mul_zero, Real.exp_zero]
    exact measureReal_le_one
  rcases hK.eq_or_lt with hK0 | hK0
  · simp only [← hK0, zero_div, zero_mul, Real.exp_zero]
    exact measureReal_le_one
  have hN : 0 < N := hK0.trans_le hKN
  have ha : β * (K / N) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right hβ0.le (div_le_one_of_le₀ hKN hN.le)) hβ1
  have hS : MeasurableSet {w : n → ℝ | ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 2 ≤ β * (K / N)} :=
    measurableSet_le (by fun_prop) measurable_const
  change μ.real {ω | u ω ∈ {w : n → ℝ | ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 2 ≤ β * (K / N)}} ≤ _
  refine (measureReal_mem_le_of_two_weights hu hV hS (φ₁ := (1 - β⁻¹) / 2)
    (φ₂ := -(β * (K / N) * ((1 - β⁻¹) / 2) / (1 - β * (K / N)))) ?_ ?_ ?_).trans
    (Real.exp_le_exp.2 (exponent_two_weights_le hKN hβ0 ha hN (Or.inr hβ1.le)))
  · have : 0 < β⁻¹ := by positivity
    linarith
  · intro hlt
    have hlt' : K < N := Nat.cast_lt.2 hlt
    have h := one_sub_two_mul_weight (K := K) hβ0 hN ha
    have hNb : 0 < N - β * K := by
      rw [← mul_div_assoc, div_lt_one hN] at ha
      linarith
    have : 0 < (N - K) / (N - β * K) := div_pos (by linarith) hNb
    linarith
  · intro g hg
    rw [Set.mem_ofPred_eq, norm_conjTranspose_mulVec_inv_norm_smul_sq] at hg
    refine nonneg_two_weights ha (mul_nonneg_of_nonpos_of_nonpos ?_ ?_)
    · have : 1 ≤ β⁻¹ := (one_le_inv₀ hβ0).2 hβ1.le
      linarith
    · obtain ⟨_, h0⟩ := norm_conjTranspose_mulVec_sq_le hV g
      rcases (sq_nonneg ‖WithLp.toLp 2 g‖).eq_or_lt with hG | hG
      · rw [← hG, h0 hG.symm]
        simp
      · rw [div_le_iff₀ hG] at hg
        linarith

/-- **Projection of a uniform unit vector, relative deviation**: for $\mathbf{u}$ uniform on the
unit sphere, $\mathbf{V}$ with orthonormal columns and $\varepsilon \ge 0$,
$$\mathbb{P}\Bigl[\varepsilon \le \Bigl\lvert \frac{\lvert n \rvert}{\lvert k \rvert}
\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 - 1 \Bigr\rvert\Bigr]
\le 2 e^{-\lvert k \rvert (\varepsilon^2/4 - \varepsilon^3/6)} \,,$$
from the two tails as for $\chi^2_{\lvert k \rvert}$
(`NLAlib.measureReal_abs_norm_sq_div_card_sub_one_ge_le_of_hasLaw_gaussianVector`). At least $2$
for empty $k$ and for $\varepsilon \ge 3/2$. [Vershynin2018, Lemma 5.3.2], there with
an unspecified constant $c$; the exponent of Dasgupta and Gupta (2003). -/
theorem
measureReal_abs_div_mul_norm_conjTranspose_mulVec_sq_sub_one_ge_le_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |(Fintype.card n / Fintype.card k : ℝ) *
      ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 - 1|} ≤
      2 * Real.exp (-(Fintype.card k * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
  have := hu.isProbabilityMeasure_iff.2 inferInstance
  set K : ℝ := (Fintype.card k : ℝ) with hKdef
  set N : ℝ := (Fintype.card n : ℝ) with hNdef
  have hK : 0 ≤ K := Nat.cast_nonneg _
  have hKN : K ≤ N := Nat.cast_le.2 hV.card_le
  rcases hK.eq_or_lt with hK0 | hK0
  · rw [← hK0, zero_mul, neg_zero, Real.exp_zero]
    exact measureReal_le_one.trans (by norm_num)
  have hN : 0 < N := hK0.trans_le hKN
  set X : Ω → ℝ := fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 with hXdef
  have hsub : {ω | ε ≤ |N / K * X ω - 1|} ⊆
      {ω | (1 + ε) * (K / N) ≤ X ω} ∪ {ω | X ω ≤ (1 - ε) * (K / N)} := by
    intro ω hω
    simp only [Set.mem_union, Set.mem_ofPred_eq] at hω ⊢
    have hX : X ω = K / N * (N / K * X ω) := by field_simp
    rcases le_abs'.1 hω with h | h
    · right
      rw [hX, mul_comm (1 - ε)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    · left
      rw [hX, mul_comm (1 + ε)]
      exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hup : μ.real {ω | (1 + ε) * (K / N) ≤ X ω} ≤
      Real.exp (-(K * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
    refine (measureReal_norm_conjTranspose_mulVec_sq_ge_mul_div_le_of_hasLaw_uniformSphereVector
      hu hV (by linarith)).trans (Real.exp_le_exp.2 ?_)
    have := Real.log_one_add_le_cubic (u := ε) (by linarith)
    have : K / 2 * (1 - (1 + ε) + Real.log (1 + ε)) ≤ K / 2 * (-(ε ^ 2 / 2) + ε ^ 3 / 3) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    linarith
  have hlo : μ.real {ω | X ω ≤ (1 - ε) * (K / N)} ≤
      Real.exp (-(K * (ε ^ 2 / 4 - ε ^ 3 / 6))) := by
    rcases lt_or_ge ε 1 with hε1 | hε1
    · refine (measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector
        hu hV (by linarith) (by linarith)).trans (Real.exp_le_exp.2 ?_)
      have := Real.log_one_sub_le_quadratic hε hε1
      have : K / 2 * (1 - (1 - ε) + Real.log (1 - ε)) ≤ K / 2 * (-(ε ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have : 0 ≤ K * ε ^ 3 := by positivity
      linarith
    · set β₀ := Real.exp (-1 - ε ^ 2 / 2) with hβ₀
      have hβ₀1 : β₀ ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have hβ₀0 : 0 < β₀ := Real.exp_pos _
      refine (measureReal_mono (s₂ := {ω | X ω ≤ β₀ * (K / N)}) (fun ω hω => ?_)
        (measure_ne_top _ _)).trans
        ((measureReal_norm_conjTranspose_mulVec_sq_le_mul_div_le_of_hasLaw_uniformSphereVector
        hu hV hβ₀0 hβ₀1).trans (Real.exp_le_exp.2 ?_))
      · simp only [Set.mem_ofPred_eq] at hω ⊢
        refine hω.trans (le_trans ?_ (mul_nonneg hβ₀0.le (by positivity)))
        exact mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
      · rw [hβ₀, Real.log_exp]
        have : 0 ≤ K * Real.exp (-1 - ε ^ 2 / 2) := by positivity
        have : 0 ≤ K * ε ^ 3 := by positivity
        nlinarith
  calc _ ≤ _ := measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ _ := measureReal_union_le _ _
    _ ≤ _ := add_le_add hup hlo
    _ = _ := by ring

/-! ### Moments from invariance -/

/-- Every continuous function is integrable against the uniform law on the sphere, which lives
on the closed unit ball. -/
private theorem integrable_of_continuous {F : (n → ℝ) → ℝ} (hF : Continuous F) :
    Integrable F (uniformSphereVector n) := by
  have hset : (WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ n) 1 =
      WithLp.ofLp '' Metric.closedBall (0 : EuclideanSpace ℝ n) 1 := by
    ext v
    exact ⟨fun h => ⟨_, h, rfl⟩, by rintro ⟨x, hx, rfl⟩; simpa using hx⟩
  have hK : IsCompact ((WithLp.toLp 2) ⁻¹' Metric.closedBall (0 : EuclideanSpace ℝ n) 1) := by
    rw [hset]
    exact (isCompact_closedBall _ _).image (PiLp.continuous_ofLp 2 _)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hF.continuousOn
  refine Integrable.of_bound hF.aestronglyMeasurable C ?_
  rw [uniformSphereVector, ae_map_iff measurable_inv_norm_smul.aemeasurable
    (measurableSet_le hF.measurable.norm measurable_const)]
  refine ae_of_all _ fun g => hC _ ?_
  rw [Set.mem_preimage, mem_closedBall_zero_iff, WithLp.toLp_smul, norm_smul, norm_inv,
    norm_norm]
  rcases (norm_nonneg (WithLp.toLp 2 g)).eq_or_lt with h | h
  · rw [← h, inv_zero, zero_mul]
    exact zero_le_one
  · rw [inv_mul_cancel₀ h.ne']

/-- A uniform unit vector has norm $1$ almost surely: for $n$ nonempty and $\mathbf{u}$ with law
`uniformSphereVector n`, $\|\mathbf{u}\| = 1$ almost surely. -/
theorem ae_norm_eq_one_uniformSphereVector [Nonempty n] :
    ∀ᵐ v ∂uniformSphereVector n, ‖WithLp.toLp 2 v‖ = 1 := by
  have hm : Measurable fun x : Metric.sphere (0 : EuclideanSpace ℝ n) 1 =>
      WithLp.ofLp (x : EuclideanSpace ℝ n) :=
    ((PiLp.continuous_ofLp 2 _).comp continuous_subtype_val).measurable
  rw [uniformSphereVector_eq_map_toSphere, ae_map_iff hm.aemeasurable
    (measurableSet_eq_fun (by fun_prop) measurable_const)]
  refine ae_of_all _ fun x => ?_
  simp only [WithLp.toLp_ofLp]
  exact norm_eq_of_mem_sphere x

/-- Sphere invariance: the law of $\mathbf{V}^{\mathsf{H}}\mathbf{u}$ depends only on the
frame's column type: for $n$ nonempty and $\mathbf{u}$ uniform on the unit sphere of
$\mathbb{R}^n$ and two $\mathbf{V}_1, \mathbf{V}_2$ with orthonormal columns indexed by the same
$r$,
$\mathbf{V}_1^{\mathsf{H}}\mathbf{u}$ and $\mathbf{V}_2^{\mathsf{H}}\mathbf{u}$ have the same
law: both are the law of $\mathbf{Q}^{\mathsf{H}}\mathbf{x}$ for an $n \times r$ Haar frame
$\mathbf{Q}$ and a fixed unit $\mathbf{x}$
(`NLAlib.hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame`). For square $\mathbf{V}_2 = \mathbf{I}$
this is the orthogonal invariance of the uniform law. -/
theorem HasOrthonormalCols.uniformSphereVector_map_conjTranspose_mulVec_eq [Nonempty n] {r : Type*}
    [Finite r]
    [DecidableEq r] {V₁ V₂ : Matrix n r ℝ} (h₁ : HasOrthonormalCols V₁)
    (h₂ : HasOrthonormalCols V₂) :
    (uniformSphereVector n).map (V₁ᴴ *ᵥ ·) = (uniformSphereVector n).map (V₂ᴴ *ᵥ ·) := by
  classical
  obtain ⟨i⟩ := ‹Nonempty n›
  have := Fintype.ofFinite r
  have hx : ‖WithLp.toLp 2 (Pi.single i 1 : n → ℝ)‖ = 1 := by
    rw [PiLp.toLp_single, PiLp.norm_single, norm_one]
  rw [← (hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame (HasLaw.id (μ := haarFrame n r)) h₁
    hx).map_eq, (hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame
    (HasLaw.id (μ := haarFrame n r)) h₂ hx).map_eq]

/-- The integral form of
`NLAlib.HasOrthonormalCols.uniformSphereVector_map_conjTranspose_mulVec_eq`. -/
private theorem integral_comp_conjTranspose_mulVec_eq [Nonempty n] {r : Type*} [Finite r]
    [DecidableEq r] {V₁ V₂ : Matrix n r ℝ} (h₁ : HasOrthonormalCols V₁)
    (h₂ : HasOrthonormalCols V₂) {F : (r → ℝ) → ℝ} (hF : Continuous F) :
    ∫ v, F (V₁ᴴ *ᵥ v) ∂uniformSphereVector n = ∫ v, F (V₂ᴴ *ᵥ v) ∂uniformSphereVector n := by
  have hm (W : Matrix n r ℝ) : Measurable (Wᴴ *ᵥ · : (n → ℝ) → r → ℝ) :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [← integral_map (hm V₁).aemeasurable hF.aestronglyMeasurable,
    HasOrthonormalCols.uniformSphereVector_map_conjTranspose_mulVec_eq h₁ h₂,
    integral_map (hm V₂).aemeasurable hF.aestronglyMeasurable]

/-- $\mathbb{E}\,\mathbf{u}_a^2 \mathbf{u}_b^2$ is the same for every pair of distinct
coordinates. -/
private theorem integral_sq_mul_sq_eq [Nonempty n] {a b i₁ i₂ : n} (hab : a ≠ b)
    (h12 : i₁ ≠ i₂) :
    ∫ v, v a ^ 2 * v b ^ 2 ∂uniformSphereVector n =
      ∫ v, v i₁ ^ 2 * v i₂ ^ 2 ∂uniformSphereVector n := by
  classical
  have h := integral_comp_conjTranspose_mulVec_eq
    (hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) (injective_pair_iff_ne.2 hab))
    (hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) (injective_pair_iff_ne.2 h12))
    (F := fun w : Fin 2 → ℝ => w 0 ^ 2 * w 1 ^ 2) (by fun_prop)
  simpa only [conjTranspose_selectionMatrix_mulVec, Function.comp_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one] using h

/-- $\mathbb{E}\,\mathbf{u}_a^4$ is the same for every coordinate. -/
private theorem integral_pow_four_eq [Nonempty n] (a b : n) :
    ∫ v, v a ^ 4 ∂uniformSphereVector n = ∫ v, v b ^ 4 ∂uniformSphereVector n := by
  classical
  have hinj (c : n) : Function.Injective fun _ : Unit => c := fun _ _ _ => Subsingleton.elim _ _
  have h := integral_comp_conjTranspose_mulVec_eq
    (hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) (hinj a))
    (hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) (hinj b))
    (F := fun w : Unit → ℝ => w () ^ 4) (by fun_prop)
  simpa only [conjTranspose_selectionMatrix_mulVec, Function.comp_apply] using h

/-- **The $45^\circ$ rotation**:
$\mathbb{E}\,\mathbf{u}_{i_1}^4 = 3 \, \mathbb{E}\,\mathbf{u}_{i_1}^2 \mathbf{u}_{i_2}^2$ for
$i_1 \ne i_2$. The frame of $(\mathbf{e}_{i_1} \pm \mathbf{e}_{i_2})/\sqrt{2}$ has the law of the
coordinate frame $(\mathbf{e}_{i_1}, \mathbf{e}_{i_2})$, and
$((a + b)^4 + (a - b)^4)/4 = (a^4 + 6 a^2 b^2 + b^4)/2$. -/
private theorem integral_pow_four_eq_three_mul [Nonempty n] {i₁ i₂ : n} (h12 : i₁ ≠ i₂) :
    ∫ v, v i₁ ^ 4 ∂uniformSphereVector n =
      3 * ∫ v, v i₁ ^ 2 * v i₂ ^ 2 ∂uniformSphereVector n := by
  classical
  set E : Matrix n (Fin 2) ℝ := selectionMatrix ![i₁, i₂] with hEdef
  have hE : HasOrthonormalCols E := hasOrthonormalCols_selectionMatrix (injective_pair_iff_ne.2 h12)
  set c : ℝ := (√2)⁻¹ with hcdef
  have h2 : c ^ 2 = 1 / 2 := by
    rw [hcdef, inv_pow, Real.sq_sqrt zero_le_two, one_div]
  set H : Matrix (Fin 2) (Fin 2) ℝ := !![c, c; c, -c] with hHdef
  have hH : HasOrthonormalCols H := by
    rw [hasOrthonormalCols_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hHdef, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination 2 * h2
  have h := integral_comp_conjTranspose_mulVec_eq (hE.mul hH) hE
    (F := fun w : Fin 2 → ℝ => w 0 ^ 4 + w 1 ^ 4) (by fun_prop)
  have hl (v : n → ℝ) : ((E * H)ᴴ *ᵥ v) 0 ^ 4 + ((E * H)ᴴ *ᵥ v) 1 ^ 4 =
      (v i₁ ^ 4 + 6 * (v i₁ ^ 2 * v i₂ ^ 2) + v i₂ ^ 4) / 2 := by
    rw [Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hEdef,
      conjTranspose_selectionMatrix_mulVec]
    simp [hHdef, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    linear_combination (c ^ 2 + 1 / 2) * (2 * v i₁ ^ 4 + 12 * v i₁ ^ 2 * v i₂ ^ 2 +
      2 * v i₂ ^ 4) * h2
  have hr (v : n → ℝ) : (Eᴴ *ᵥ v) 0 ^ 4 + (Eᴴ *ᵥ v) 1 ^ 4 = v i₁ ^ 4 + v i₂ ^ 4 := by
    rw [hEdef, conjTranspose_selectionMatrix_mulVec]
    rfl
  simp only [hl, hr] at h
  have hc (F : (n → ℝ) → ℝ) (hF : Continuous F) := integrable_of_continuous hF
  rw [integral_div, integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)),
    integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)), integral_const_mul,
    integral_add (hc _ (by fun_prop)) (hc _ (by fun_prop)), integral_pow_four_eq i₂ i₁] at h
  linarith

/-- $\mathbb{E}(\sum_{j \in r} \mathbf{u}_{s(j)}^2)^2
= \lvert r \rvert (\lvert r \rvert + 2) \, \mathbb{E}\,\mathbf{u}_{i_1}^2 \mathbf{u}_{i_2}^2$ for
an injective $s$ and $i_1 \ne i_2$: the diagonal terms are
$\mathbb{E}\,\mathbf{u}_i^4 = 3 \, \mathbb{E}\,\mathbf{u}_{i_1}^2 \mathbf{u}_{i_2}^2$, the others
$\mathbb{E}\,\mathbf{u}_{i_1}^2 \mathbf{u}_{i_2}^2$. -/
private theorem integral_sum_sq_sq [Nonempty n] {i₁ i₂ : n} (h12 : i₁ ≠ i₂) {r : Type*}
    [Fintype r] {s : r → n} (hs : Function.Injective s) :
    ∫ v, (∑ j, v (s j) ^ 2) ^ 2 ∂uniformSphereVector n =
      Fintype.card r * (Fintype.card r + 2) * ∫ v, v i₁ ^ 2 * v i₂ ^ 2 ∂uniformSphereVector n := by
  classical
  set m := ∫ v, v i₁ ^ 2 * v i₂ ^ 2 ∂uniformSphereVector n
  have hterm (j l : r) : ∫ v, v (s j) ^ 2 * v (s l) ^ 2 ∂uniformSphereVector n =
      m + 2 * m * if j = l then 1 else 0 := by
    by_cases hjl : j = l
    · subst hjl
      simp only [if_true, mul_one, ← pow_add]
      rw [integral_pow_four_eq (s j) i₁, integral_pow_four_eq_three_mul h12]
      ring
    · rw [if_neg hjl, mul_zero, add_zero, integral_sq_mul_sq_eq (hs.ne hjl) h12]
  have hexp : (fun v : n → ℝ => (∑ j, v (s j) ^ 2) ^ 2) =
      fun v => ∑ j, ∑ l, v (s j) ^ 2 * v (s l) ^ 2 := by
    funext v
    rw [sq, Finset.sum_mul_sum]
  have hint (j l : r) : Integrable (fun v : n → ℝ => v (s j) ^ 2 * v (s l) ^ 2)
      (uniformSphereVector n) := integrable_of_continuous (by fun_prop)
  rw [hexp, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => hint j l]
  calc _ = ∑ j : r, ∑ l : r, (m + 2 * m * if j = l then 1 else 0) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => hint j l]
        exact Finset.sum_congr rfl fun l _ => hterm j l
    _ = _ := by
        simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ,
          if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring

omit [DecidableEq k] in
/-- The fourth power of the projected length of a uniform unit vector is integrable (it is at
most $\|\mathbf{V}\|_2^4$), for every fixed $\mathbf{V}$. -/
theorem integrable_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (V : Matrix n k ℝ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 4) μ := by
  have hF : Continuous fun w : n → ℝ => ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 4 := by fun_prop
  exact (hu.integrable_comp_iff hF.aestronglyMeasurable).2 (integrable_of_continuous hF)

/-- The fourth moment of a projected uniform unit vector: for $\mathbf{u}$ uniform on the
unit sphere of $\mathbb{R}^n$, $n$ nonempty, and $\mathbf{V}$ with orthonormal columns,
$$\mathbb{E}\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^4
= \frac{\lvert k \rvert (\lvert k \rvert + 2)}{\lvert n \rvert (\lvert n \rvert + 2)} \,,$$
from invariance alone: $\sum_i \mathbf{u}_i^2 = 1$ and a
$45^\circ$ rotation give
$\mathbb{E}\,\mathbf{u}_1^4 = 3 \, \mathbb{E}\,\mathbf{u}_1^2 \mathbf{u}_2^2$ and
$\lvert n \rvert (\lvert n \rvert + 2) \, \mathbb{E}\,\mathbf{u}_1^2 \mathbf{u}_2^2 = 1$ when
$\lvert n \rvert \ge 2$; for $\lvert n \rvert = 1$, $\mathbf{u} = \pm 1$. No radius–direction
independence. -/
theorem integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector [Nonempty n]
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) :
    ∫ ω, ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 4 ∂μ =
      Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2)) := by
  classical
  have hF : Continuous fun w : n → ℝ => ‖WithLp.toLp 2 (Vᴴ *ᵥ w)‖ ^ 4 := by fun_prop
  have h := hu.integral_comp hF.aestronglyMeasurable
  simp only [Function.comp_def] at h
  rw [h]
  obtain ⟨s⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hV.card_le
  have hE := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) s.injective
  rw [integral_comp_conjTranspose_mulVec_eq hV hE
    (F := fun w : k → ℝ => ‖WithLp.toLp 2 w‖ ^ 4) (by fun_prop)]
  have h4 (w : k → ℝ) : ‖WithLp.toLp 2 w‖ ^ 4 = (∑ j, w j ^ 2) ^ 2 := by
    rw [← EuclideanSpace.norm_toLp_sq_eq_sum_sq]
    ring
  simp only [conjTranspose_selectionMatrix_mulVec, h4, Function.comp_apply]
  have hone : ∫ v, (∑ a, v a ^ 2) ^ 2 ∂uniformSphereVector n = 1 := by
    rw [integral_congr_ae (g := fun _ => (1 : ℝ)), integral_const, probReal_univ, one_smul]
    filter_upwards [ae_norm_eq_one_uniformSphereVector] with v hv
    rw [← EuclideanSpace.norm_toLp_sq_eq_sum_sq, hv, one_pow, one_pow]
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  rcases Nat.lt_or_ge 1 (Fintype.card n) with hn | hn
  · obtain ⟨i₁, i₂, h12⟩ := Fintype.exists_pair_of_one_lt_card hn
    have h1 := integral_sum_sq_sq h12 (s := id) Function.injective_id
    simp only [id] at h1
    rw [integral_sum_sq_sq h12 s.injective]
    rw [hone] at h1
    rw [eq_div_iff (by positivity)]
    calc _ = Fintype.card k * (Fintype.card k + 2) * ((Fintype.card n * (Fintype.card n + 2)) *
          ∫ v, v i₁ ^ 2 * v i₂ ^ 2 ∂uniformSphereVector n) := by ring
      _ = _ := by rw [← h1, mul_one]
  · have hn1 : Fintype.card n = 1 := le_antisymm hn Fintype.card_pos
    rcases Nat.eq_zero_or_pos (Fintype.card k) with hk0 | hk0
    · have := Fintype.card_eq_zero_iff.1 hk0
      simp only [Finset.univ_eq_empty, Finset.sum_empty, hk0]
      simp
    · have hkn : Fintype.card k = Fintype.card n := le_antisymm hV.card_le (hn1 ▸ hk0)
      have hb : Function.Bijective s :=
        (Fintype.bijective_iff_injective_and_card s).2 ⟨s.injective, hkn⟩
      have hsum (v : n → ℝ) : ∑ j, v (s j) ^ 2 = ∑ a, v a ^ 2 :=
        (Equiv.ofBijective s hb).sum_comp fun a => v a ^ 2
      simp only [hsum, hone, hkn]
      field_simp

/-! ### The Beta law -/

omit [DecidableEq k] in
/-- The two blocks of a standard Gaussian vector indexed by $k \oplus p$ have independent sums of
squares. -/
private theorem indepFun_sum_sq_inl_sum_sq_inr_of_hasLaw_gaussianVector {p : Type*} [Fintype p]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    IndepFun (fun ω => ∑ i, h ω (Sum.inl i) ^ 2) (fun ω => ∑ j, h ω (Sum.inr j) ^ 2) μ := by
  have hpair : HasLaw (fun ω => (fun i => h ω (Sum.inl i), fun j => h ω (Sum.inr j)))
      ((gaussianVector k).prod (gaussianVector p)) μ :=
    (measurePreserving_sumPiEquivProdPi (fun _ : k ⊕ p => gaussianReal 0 1)).fun_comp_hasLaw hh
  have := hh.isProbabilityMeasure
  have hX : HasLaw (fun ω => fun i => h ω (Sum.inl i)) (gaussianVector k) μ :=
    hasLaw_comp_inl_gaussianVector.comp hh
  have hY : HasLaw (fun ω => fun j => h ω (Sum.inr j)) (gaussianVector p) μ :=
    hasLaw_comp_inr_gaussianVector.comp hh
  have hind : IndepFun (fun ω => fun i => h ω (Sum.inl i))
      (fun ω => fun j => h ω (Sum.inr j)) μ := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable, hX.map_eq,
      hY.map_eq]
    exact hpair.map_eq
  exact hind.comp (φ := fun x : k → ℝ => ∑ i, x i ^ 2) (ψ := fun y : p → ℝ => ∑ j, y j ^ 2)
    (by fun_prop) (by fun_prop)

omit [DecidableEq k] in
/-- The first block of a standard Gaussian vector indexed by $k \oplus p$, $k$ nonempty, has a
chi-square sum of squares, $\mathrm{Gamma}(\lvert k\rvert/2, 1/2)$. -/
private theorem hasLaw_sum_sq_inl_of_hasLaw_gaussianVector {p : Type*} [Fintype p] [Nonempty k]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    HasLaw (fun ω => ∑ i, h ω (Sum.inl i) ^ 2) (gammaMeasure (Fintype.card k / 2) (1 / 2)) μ :=
  hasLaw_sum_sq_of_hasLaw_pi_gaussianReal (hasLaw_comp_inl_gaussianVector.comp hh)

omit [DecidableEq k] in
/-- The second block of a standard Gaussian vector indexed by $k \oplus p$, $p$ nonempty, has a
chi-square sum of squares, $\mathrm{Gamma}(\lvert p\rvert/2, 1/2)$. -/
private theorem hasLaw_sum_sq_inr_of_hasLaw_gaussianVector {p : Type*} [Fintype p] [Nonempty p]
    {h : Ω → k ⊕ p → ℝ} (hh : HasLaw h (gaussianVector (k ⊕ p)) μ) :
    HasLaw (fun ω => ∑ j, h ω (Sum.inr j) ^ 2) (gammaMeasure (Fintype.card p / 2) (1 / 2)) μ :=
  hasLaw_sum_sq_of_hasLaw_pi_gaussianReal (hasLaw_comp_inr_gaussianVector.comp hh)

/-- **The projection of a uniform unit vector is Beta**: for $\mathbf{u}$ uniform on the unit
sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`) and $\mathbf{V}$ with $k$ orthonormal
columns, $0 < k < n$,
$$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 \sim
\mathrm{Beta}\Big(\frac{k}{2}, \frac{n-k}{2}\Big)\,.$$
No printed source.
Result: sphere-projection-beta -/
theorem hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V)
    (hk : 0 < Fintype.card k) (hkn : Fintype.card k < Fintype.card n) :
    HasLaw (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2)
      (betaMeasure (Fintype.card k / 2) (((Fintype.card n : ℝ) - Fintype.card k) / 2)) μ := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_lt hkn
  have hcard : Fintype.card k + Fintype.card (Fin (m + 1)) = Fintype.card n := by
    rw [Fintype.card_fin, hm, add_assoc]
  obtain ⟨V', hW⟩ := hV.exists_fromCols hcard
  have : Nonempty k := Fintype.card_pos_iff.mp hk
  set W := Matrix.fromCols V V'
  have hh : HasLaw (fun g => Wᴴ *ᵥ g) (gaussianVector (k ⊕ Fin (m + 1))) (gaussianVector n) :=
    hasLaw_mulVec_of_hasLaw_gaussianVector HasLaw.id (by rwa [Matrix.conjTranspose_conjTranspose])
  have hβ := hasLaw_div_add_of_hasLaw_gammaMeasure (by positivity) (by positivity)
    (by norm_num) (hasLaw_sum_sq_inl_of_hasLaw_gaussianVector hh)
    (hasLaw_sum_sq_inr_of_hasLaw_gaussianVector hh)
    (indepFun_sum_sq_inl_sum_sq_inr_of_hasLaw_gaussianVector hh)
  have hb : ((Fintype.card n : ℝ) - Fintype.card k) / 2 =
      (Fintype.card (Fin (m + 1)) : ℝ) / 2 := by
    rw [← hcard, Nat.cast_add]
    ring
  rw [hb]
  refine HasLaw.comp_of_hasLaw_comp (f := fun v => ‖WithLp.toLp 2 (Vᴴ *ᵥ v)‖ ^ 2)
    (X := fun g : n → ℝ => ‖WithLp.toLp 2 g‖⁻¹ • g) (P := gaussianVector n) ?_
    ⟨measurable_inv_norm_smul.aemeasurable, rfl⟩ hu ?_
  · fun_prop
  · refine hβ.congr (Filter.Eventually.of_forall fun g => ?_)
    obtain ⟨h1, h2⟩ := norm_sq_conjTranspose_mulVec_eq_sum_inl_and_norm_sq_eq_add hW hcard g
    beta_reduce
    rw [norm_conjTranspose_mulVec_inv_norm_smul_sq, h1, h2]

/-! ### The sharp sub-Gaussian tail -/

/-- **Projections of a uniform unit vector are sub-Gaussian**: for $\mathbf{u}$ uniform on the
unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`) and $\mathbf{V}$ with $k$
orthonormal columns, any $0 \le k \le n$,
$\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^2 - k/n$ satisfies the sub-Gaussian moment generating
function bound with variance proxy $1/(2(n+2))$. For $0 < k < n$ this is the Beta proxy
$1/(4(\alpha+\beta+1))$ at $\alpha + \beta = n/2$; for $k \in \{0, n\}$ the variable is $0$
almost surely. Compared with the Chernoff tails of this file
(`NLAlib.measureReal_norm_conjTranspose_mulVec_sq_ge_mul_div_le_of_hasLaw_uniformSphereVector`
and its lower twin), whose exponent near the mean is about $n^2\tau^2/(4k)$ at deviation $\tau$
against $(n+2)\tau^2$ here: this bound is better when $k \gtrsim n/4$ and worse for small $k$.
[MarchalArbel2017, Theorem 1] for the Beta proxy. -/
theorem hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector
    (hu : HasLaw u (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) :
    HasSubgaussianMGF
      (fun ω => ‖WithLp.toLp 2 (Vᴴ *ᵥ u ω)‖ ^ 2 - Fintype.card k / Fintype.card n)
      ‖1 / (2 * ((Fintype.card n : ℝ) + 2))‖₊ μ := by
  classical
  have : IsProbabilityMeasure μ := hu.isProbabilityMeasure
  have hk : Fintype.card k ≤ Fintype.card n := hV.card_le
  rcases Nat.eq_zero_or_pos (Fintype.card k) with h0 | hpos
  · have he : IsEmpty k := Fintype.card_eq_zero_iff.mp h0
    refine (HasSubgaussianMGF.zero.congr ?_).mono zero_le
    filter_upwards with ω
    simp [Subsingleton.elim (Vᵀ *ᵥ u ω) 0]
  rcases hk.eq_or_lt with heq | hlt
  · have hn : 0 < Fintype.card n := heq ▸ hpos
    have : Nonempty n := Fintype.card_pos_iff.mp hn
    have hVc : HasOrthonormalCols Vᴴ := hV.conjTranspose_of_card_eq heq.symm
    have hae : ∀ᵐ ω ∂μ, ‖WithLp.toLp 2 (u ω)‖ = 1 :=
      ae_of_ae_map hu.aemeasurable (by rw [hu.map_eq]; exact ae_norm_eq_one_uniformSphereVector)
    refine (HasSubgaussianMGF.zero.congr ?_).mono zero_le
    filter_upwards [hae] with ω hω
    have hn' : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
    rw [Pi.zero_apply, hVc.norm_toLp_mulVec, hω, heq]
    simp [hn']
  · have hnpos : (0 : ℝ) < Fintype.card n := by exact_mod_cast hpos.trans hlt
    have hX := hasLaw_norm_conjTranspose_mulVec_sq_of_hasLaw_uniformSphereVector hu hV hpos hlt
    have hα : (0 : ℝ) < Fintype.card k / 2 := half_pos (by exact_mod_cast hpos)
    have hβ : (0 : ℝ) < ((Fintype.card n : ℝ) - Fintype.card k) / 2 :=
      half_pos (sub_pos.mpr (by exact_mod_cast hlt))
    have key := hasSubgaussianMGF_sub_div_of_hasLaw_betaMeasure hα hβ hX
    have hab : (Fintype.card k : ℝ) / 2 + ((Fintype.card n : ℝ) - Fintype.card k) / 2 =
        Fintype.card n / 2 := by ring
    have hratio : (Fintype.card k : ℝ) / 2 /
        ((Fintype.card k : ℝ) / 2 + ((Fintype.card n : ℝ) - Fintype.card k) / 2) =
        Fintype.card k / Fintype.card n := by
      rw [hab]
      field_simp
    have hprox : ‖1 / (4 * ((Fintype.card k : ℝ) / 2 +
        ((Fintype.card n : ℝ) - Fintype.card k) / 2 + 1))‖₊ =
        ‖1 / (2 * ((Fintype.card n : ℝ) + 2))‖₊ := by
      rw [hab]
      congr 1
      field_simp
      ring
    rwa [hratio, hprox] at key

-- The declaration name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The sample mean of projected uniform unit vectors**: for $\mathbf{u}_1, \dots, \mathbf{u}_m$
independent and each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`),
$\mathbf{V}$ with $k$ orthonormal columns and $\tau \ge 0$,
$$\mathbb{P}\Bigl[\tau \le \Bigl\lvert\frac1m\sum_j\|\mathbf{V}^{\mathsf{H}}\mathbf{u}_j\|^2 -
\frac kn\Bigr\rvert\Bigr] \le 2e^{-m(n+2)\tau^2}\,.$$
Every rank $0 \le k \le n$ is allowed, and for $m = 0$ the bound is $2$.
[MarchalArbel2017, Theorem 1] for the Beta proxy, then Hoeffding's inequality.
Result: sphere-projection-tail -/
theorem
measureReal_abs_sum_norm_conjTranspose_mulVec_sq_div_card_sub_div_card_ge_le_of_hasLaw_uniformSphereVector
    {m : Type*} [Fintype m] {u : m → Ω → n → ℝ} (hind : iIndepFun u μ)
    (hu : ∀ j, HasLaw (u j) (uniformSphereVector n) μ) (hV : HasOrthonormalCols V) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ u j ω)‖ ^ 2) / Fintype.card m -
        Fintype.card k / Fintype.card n|} ≤
      2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  have := hind.isProbabilityMeasure
  rcases (Nat.cast_nonneg (α := ℝ) (Fintype.card m)).eq_or_lt with hm | hm
  · rw [← hm]
    simp only [zero_mul, neg_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans (by norm_num)
  have hg : ∀ j : m, Measurable fun x : n → ℝ =>
      ‖WithLp.toLp 2 (Vᴴ *ᵥ x)‖ ^ 2 - (Fintype.card k / Fintype.card n : ℝ) := fun _ => by
    fun_prop
  have hs := HasSubgaussianMGF.sum_of_iIndepFun (hind.comp _ hg) (s := Finset.univ)
    fun j _ => hasSubgaussianMGF_norm_conjTranspose_mulVec_sq_sub_of_hasLaw_uniformSphereVector
      (hu j) hV
  refine le_of_eq_of_le ?_ ((hs.measureReal_abs_ge_le (t := Fintype.card m * τ)
    (by positivity)).trans_eq ?_)
  · congr 1
    ext ω
    simp only [Set.mem_ofPred_eq, Function.comp_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ u j ω)‖ ^ 2) / (Fintype.card m : ℝ) -
        Fintype.card k / Fintype.card n = ((∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ u j ω)‖ ^ 2) -
        Fintype.card m * (Fintype.card k / Fintype.card n)) / Fintype.card m by field_simp,
      abs_div, abs_of_pos hm, le_div_iff₀ hm, mul_comm]
  · rw [NNReal.coe_sum]
    simp only [coe_nnnorm, Real.norm_of_nonneg (by positivity :
      (0 : ℝ) ≤ 1 / (2 * (Fintype.card n + 2))), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    congr 2
    field_simp

end NLAlib
