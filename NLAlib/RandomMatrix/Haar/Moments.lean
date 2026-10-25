/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import NLAlib.Matrix.Spectral.HermitianPart
public import NLAlib.Probability.Isotropic
public import NLAlib.RandomMatrix.Haar.Blocks
public import NLAlib.RandomMatrix.Haar.Sphere

/-!
# Moments of Haar frames

Exact second moments of an $n \times k$ Haar frame $\mathbf{Q}$
($\lvert k \rvert \le \lvert n \rvert$), from orthogonal invariance alone:
$\mathbb{E}[\mathbf{Q}\mathbf{B}\mathbf{Q}^{\mathsf{H}}]
= (\operatorname{tr} \mathbf{B} / \lvert n \rvert) \, \mathbf{I}$, in particular
$\mathbb{E}[\mathbf{Q}\mathbf{Q}^{\mathsf{H}}] = (\lvert k \rvert / \lvert n \rvert) \, \mathbf{I}$;
$\mathbb{E}[\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}]
= (\operatorname{tr} \mathbf{A} / \lvert n \rvert) \, \mathbf{I}$;
$\mathbb{E} \, \mathbf{Q}_{i,j}^2 = 1 / \lvert n \rvert$; and $\sqrt{\lvert n \rvert}$ times a
column is isotropic. The integrands are bounded (`ae_specNorm_le_one_of_hasLaw_haarFrame`), so the
integrability companions hold in every shape.

These are what a Haar sketch
$\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert} \, \mathbf{Q}^{\mathsf{H}}$ needs for
$\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$, and what trace estimation with sphere
probes or an orthonormal test matrix consumes. The fourth moment of a projected column,
$\mathbb{E}\|\mathbf{V}^{\mathsf{H}}\mathbf{u}\|^4$ for $\mathbf{u}$ uniform on the sphere, is in
`NLAlib/RandomMatrix/Haar/Sphere.lean`, also from invariance. The inverse mean of the Beta matrix
$\mathbf{W}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W}^{\mathsf{H}}$, a moment of a block of
$\mathbf{Q}$, is `NLAlib.integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame` in
`NLAlib/RandomMatrix/Haar/Blocks.lean`.

The fourth moments enter through the **variance of a Haar compression**: for real symmetric
$\mathbf{A}$ and $\lvert n \rvert \ge 2$,
$$\operatorname{Var}\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
= \frac{2\lvert k \rvert(\lvert n \rvert - \lvert k \rvert)}
{(\lvert n \rvert - 1)\lvert n \rvert(\lvert n \rvert + 2)}
\Bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 - \frac{(\operatorname{tr} \mathbf{A})^2}{\lvert n \rvert}
\Bigr)\,,$$
from invariance and the fourth moment of a projected sphere vector. Its case
$\lvert k \rvert = 1$ is the variance of the Girard–Hutchinson estimate with a probe uniform on
the sphere of radius $\sqrt{\lvert n \rvert}$, $(2\lvert n \rvert/(\lvert n \rvert + 2))
(\|\mathbf{A}\|_{\mathsf{F}}^2 - (\operatorname{tr}\mathbf{A})^2/\lvert n \rvert)$, and the
complex sphere of $\mathbb{C}^n$, the image of the real sphere of $\mathbb{R}^{n \sqcup n}$, gives
$(\lvert n \rvert/(\lvert n \rvert + 1))(\|\mathbf{A}\|_{\mathsf{F}}^2 -
\lvert\operatorname{tr}\mathbf{A}\rvert^2/\lvert n \rvert)$ for every complex $\mathbf{A}$
(Epperly's reduction to the real case). The $m$-probe estimator is
`NLAlib/Estimation/Trace/GirardHutchinson.lean`.

## Main results

* `NLAlib.integral_mul_mul_conjTranspose_of_hasLaw_haarFrame`,
  `NLAlib.integral_mul_conjTranspose_of_hasLaw_haarFrame`.
* `NLAlib.integral_conjTranspose_mul_mul_of_hasLaw_haarFrame`,
  `NLAlib.integral_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame`.
* `NLAlib.integral_apply_sq_of_hasLaw_haarFrame`.
* `NLAlib.isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame`.
* `NLAlib.variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame`, its multiplied form
  `NLAlib.mul_variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame` (every $\lvert n \rvert$)
  and the form for any real matrix,
  `NLAlib.variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame_hermitianPart`.
* `NLAlib.variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector`,
  `NLAlib.variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector_hermitianPart`: real sphere
  probes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k] {X : Ω → Matrix n k ℝ}

/-! ### $\mathbb{E}[\mathbf{Q}\mathbf{B}\mathbf{Q}^{\mathsf{H}}]$ -/

/-- $\mathbf{Q}\mathbf{B}\mathbf{Q}^{\mathsf{H}}$ is integrable for a Haar frame $\mathbf{Q}$, in
every shape. -/
theorem integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (B : Matrix k k ℝ) :
    Integrable (fun ω => X ω * B * (X ω)ᴴ) μ := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  have hm : Measurable fun Q : Matrix n k ℝ => Q * B * Qᴴ :=
    (measurable_id.matrix_mul measurable_const).matrix_mul
      (Measurable.matrix_conjTranspose continuous_star.measurable measurable_id)
  refine Integrable.of_bound (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    (specNorm B) ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hX] with ω hω
  rw [← specNorm_eq_norm]
  calc specNorm (X ω * B * (X ω)ᴴ) ≤ specNorm (X ω) * specNorm B * specNorm (X ω)ᴴ :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ 1 * specNorm B * 1 := by
        rw [specNorm_conjTranspose]
        gcongr
    _ = specNorm B := by ring

/-- **The second moment of a Haar frame**:
$$\mathbb{E}[\mathbf{Q}\mathbf{B}\mathbf{Q}^{\mathsf{H}}]
= \frac{\operatorname{tr} \mathbf{B}}{\lvert n \rvert}\,\mathbf{I}\,,$$
for an $n \times k$ Haar frame $\mathbf{Q}$, $\lvert k \rvert \le \lvert n \rvert$.
[Meckes2019, Ch. 2], there entrywise for the orthogonal group; here for frames, in matrix form.
Result: haar-frame-second-moment -/
theorem integral_mul_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (B : Matrix k k ℝ) :
    ∫ ω, X ω * B * (X ω)ᴴ ∂μ = (B.trace / Fintype.card n) • (1 : Matrix n n ℝ) := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  rw [integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant hX B
    (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX B)]
  have htr : (fun ω => (X ω * B * (X ω)ᴴ).trace) =ᵐ[μ] fun _ => B.trace := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hX hk] with ω hω
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hasOrthonormalCols_iff.1 hω, Matrix.one_mul]
  rw [integral_congr_ae htr, integral_const, probReal_univ, one_smul]

/-- $\mathbb{E}[\mathbf{Q}\mathbf{Q}^{\mathsf{H}}] = (\lvert k \rvert / \lvert n \rvert) \,
\mathbf{I}$: the range projector of an $n \times k$ Haar frame,
$\lvert k \rvert \le \lvert n \rvert$, is $\lvert k \rvert / \lvert n \rvert$ times the identity in
mean (the case $\mathbf{B} = \mathbf{I}$ of `integral_mul_mul_conjTranspose_of_hasLaw_haarFrame`,
stated because consumers rewrite with it). -/
theorem integral_mul_conjTranspose_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    ∫ ω, X ω * (X ω)ᴴ ∂μ = ((Fintype.card k : ℝ) / Fintype.card n) • (1 : Matrix n n ℝ) := by
  simpa only [Matrix.mul_one, Matrix.trace_one] using
    integral_mul_mul_conjTranspose_of_hasLaw_haarFrame hX hk 1

/-! ### $\mathbb{E}[\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}]$ -/

/-- $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is integrable for a Haar frame $\mathbf{Q}$, in
every shape. -/
theorem integrable_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (A : Matrix n n ℝ) :
    Integrable (fun ω => (X ω)ᴴ * A * X ω) μ := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  have hm : Measurable fun Q : Matrix n k ℝ => Qᴴ * A * Q :=
    ((Measurable.matrix_conjTranspose continuous_star.measurable measurable_id).matrix_mul
      measurable_const).matrix_mul measurable_id
  refine Integrable.of_bound (hm.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    (specNorm A) ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hX] with ω hω
  rw [← specNorm_eq_norm]
  calc specNorm ((X ω)ᴴ * A * X ω) ≤ specNorm (X ω)ᴴ * specNorm A * specNorm (X ω) :=
        (specNorm_mul_le _ _).trans
          (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _))
    _ ≤ 1 * specNorm A * 1 := by
        rw [specNorm_conjTranspose]
        gcongr
    _ = specNorm A := by ring

/-- **The compression of a fixed matrix by a Haar frame**:
$$\mathbb{E}[\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}]
= \frac{\operatorname{tr} \mathbf{A}}{\lvert n \rvert}\,\mathbf{I}\,,$$
for an $n \times k$ Haar frame $\mathbf{Q}$, $\lvert k \rvert \le \lvert n \rvert$.
[Meckes2019, Ch. 2], there entrywise; here in matrix form.
Result: haar-frame-second-moment -/
theorem integral_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (A : Matrix n n ℝ) :
    ∫ ω, (X ω)ᴴ * A * X ω ∂μ = (A.trace / Fintype.card n) • (1 : Matrix k k ℝ) := by
  classical
  rcases Nat.eq_zero_or_pos (Fintype.card k) with h0 | hpos
  · have := Fintype.card_eq_zero_iff.1 h0
    ext i
    exact isEmptyElim i
  have hY := hasLaw_conjTranspose_of_hasLaw_haarFrame hX
  have hint := integrable_conjTranspose_mul_mul_of_hasLaw_haarFrame hX A
  have hint' : Integrable (fun ω => A * (X ω * (X ω)ᴴ)) μ :=
    (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX 1).const_mul A |>.congr
      (ae_of_all _ fun ω => by simp only [Matrix.mul_one])
  have h := integral_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant hY A
    (by simpa only [Matrix.conjTranspose_conjTranspose] using hint)
  simp only [Matrix.conjTranspose_conjTranspose] at h
  have htr : ∫ ω, ((X ω)ᴴ * A * X ω).trace ∂μ =
      (Fintype.card k : ℝ) / Fintype.card n * A.trace := by
    have h1 : ∀ ω, ((X ω)ᴴ * A * X ω).trace = (A * (X ω * (X ω)ᴴ)).trace := fun ω => by
      rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [h1]
    rw [Matrix.integral_trace hint', Matrix.integral_const_mul A
      (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX 1 |>.congr
        (ae_of_all _ fun ω => by simp only [Matrix.mul_one])),
      integral_mul_conjTranspose_of_hasLaw_haarFrame hX hk, Matrix.mul_smul, Matrix.mul_one,
      Matrix.trace_smul, smul_eq_mul]
  rw [h, htr]
  congr 1
  have hk0 : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hpos.ne'
  field_simp

/-! ### Entries and columns -/

omit [Fintype n] in
/-- The entries of $\mathbf{Q}\mathbf{e}_j\mathbf{e}_j^{\mathsf{T}}\mathbf{Q}^{\mathsf{H}}$ are
products of entries of the $j$-th column. -/
private theorem mul_single_mul_conjTranspose_apply (Q : Matrix n k ℝ) [DecidableEq k] (i i' : n)
    (j : k) : (Q * Matrix.single j j (1 : ℝ) * Qᴴ) i i' = Q i j * Q i' j := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

/-- The second moments of two entries of a column of a Haar frame:
$\mathbb{E}[\mathbf{Q}_{i,j}\mathbf{Q}_{i',j}]$ is $1/\lvert n \rvert$ if $i = i'$ and $0$
otherwise. -/
private theorem integral_apply_mul_apply_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (i i' : n) (j : k) :
    ∫ ω, X ω i j * X ω i' j ∂μ = if i = i' then 1 / (Fintype.card n : ℝ) else 0 := by
  have h := congrFun₂ (integral_mul_mul_conjTranspose_of_hasLaw_haarFrame hX hk
    (Matrix.single j j (1 : ℝ))) i i'
  rw [Matrix.integral_apply (Matrix.integrable_iff.1
    (integrable_mul_mul_conjTranspose_of_hasLaw_haarFrame hX _))] at h
  simp only [mul_single_mul_conjTranspose_apply] at h
  rw [h, Matrix.trace_single_eq_same, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs <;> simp

/-- **The entries of a Haar frame have second moment $1 / \lvert n \rvert$**:
$\mathbb{E} \, \mathbf{Q}_{i,j}^2 = 1 / \lvert n \rvert$ for an $n \times k$ Haar frame,
$\lvert k \rvert \le \lvert n \rvert$. [Meckes2019, Ch. 2]. -/
theorem integral_apply_sq_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (i : n) (j : k) :
    ∫ ω, X ω i j ^ 2 ∂μ = 1 / Fintype.card n := by
  classical
  simpa only [sq, if_true] using integral_apply_mul_apply_of_hasLaw_haarFrame hX hk i i j

/-- A rescaled column of a Haar frame is isotropic:
$\sqrt{\lvert n \rvert} \, \mathbf{Q}\mathbf{e}_j$ has second-moment matrix the identity, for an
$n \times k$ Haar frame $\mathbf{Q}$, $\lvert k \rvert \le \lvert n \rvert$. It is what Hutchinson's
estimator with sphere probes takes (`IsIsotropic`). -/
theorem isIsotropic_sqrt_mul_col_of_hasLaw_haarFrame [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (j : k) :
    IsIsotropic (fun ω i => √(Fintype.card n : ℝ) * X ω i j) μ := by
  refine ⟨fun i => (memLp_apply_of_hasLaw_haarFrame hX i j 2).const_mul _, fun i i' => ?_⟩
  have : Nonempty n := ⟨i⟩
  have hn : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Fintype.card_ne_zero (α := n))
  have h (ω : Ω) : √(Fintype.card n : ℝ) * X ω i j * star (√(Fintype.card n : ℝ) * X ω i' j) =
      Fintype.card n * (X ω i j * X ω i' j) := by
    rw [star_trivial, mul_mul_mul_comm, Real.mul_self_sqrt (Nat.cast_nonneg _)]
  simp only [h]
  rw [integral_const_mul, integral_apply_mul_apply_of_hasLaw_haarFrame hX hk i i' j]
  split_ifs
  · field_simp
  · rw [mul_zero]

/-! ### Fourth moments: the variance of a Haar compression

The variance of $\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$. For a real
symmetric $\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$,
$\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) = \sum_i \mathbf{d}_i r_i$ with
$r_i = \sum_j \mathbf{R}_{i,j}^2$ the squared row norms of the Haar frame
$\mathbf{R} = \mathbf{U}^{\mathsf{H}}\mathbf{Q}$. Invariance gives everything: $\mathbb{E} r_i =
\lvert k \rvert / \lvert n \rvert$; $\mathbb{E} r_i^2 = \lvert k \rvert (\lvert k \rvert + 2) /
(\lvert n \rvert (\lvert n \rvert + 2))$, the fourth moment of a projected sphere vector; the
cross moments $\mathbb{E} r_i r_l$, $i \ne l$, are all equal (a pair of rows of a Haar frame has the
law of the first two rows); and $\sum_l r_l = \lvert k \rvert$ fixes their common value. -/

section TraceVariance

/-- Every continuous function of a Haar frame is in every $L^p$: the entries are bounded by
$1$ almost surely. -/
private theorem memLp_comp_of_hasLaw_haarFrame [DecidableEq k] (hX : HasLaw X (haarFrame n k) μ)
    {F : Matrix n k ℝ → ℝ} (hF : Continuous F) (p : ℝ≥0∞) :
    MemLp (fun ω => F (X ω)) p μ := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  have hK : IsCompact (Set.univ.pi (fun _ : n => Set.univ.pi fun _ : k => Set.Icc (-1 : ℝ) 1) :
      Set (Matrix n k ℝ)) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_Icc
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := F) hF.continuousOn
  refine MemLp.of_bound (hF.measurable.comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
    C ?_
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hX] with ω hω
  refine hC (X ω) (Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j => ?_)
  have h := (norm_apply_le_specNorm (X ω) i j).trans hω
  rw [Real.norm_eq_abs] at h
  exact abs_le.1 h

private theorem integrable_comp_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) {F : Matrix n k ℝ → ℝ} (hF : Continuous F) :
    Integrable (fun ω => F (X ω)) μ :=
  memLp_one_iff_integrable.1 (memLp_comp_of_hasLaw_haarFrame hX hF 1)

/-- $\mathbb{E} r_i = \lvert k \rvert / \lvert n \rvert$ for the squared norm $r_i$ of a row. -/
private theorem integral_sum_sq_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (i : n) :
    ∫ ω, ∑ j, X ω i j ^ 2 ∂μ = Fintype.card k / Fintype.card n := by
  rw [integral_finsetSum _ fun j _ =>
    integrable_comp_of_hasLaw_haarFrame hX (F := fun M : Matrix n k ℝ => M i j ^ 2)
      (by fun_prop)]
  simp only [integral_apply_sq_of_hasLaw_haarFrame hX hk i, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  ring

/-- $\mathbb{E} r_i^2 = \lvert k \rvert (\lvert k \rvert + 2) / (\lvert n \rvert (\lvert n \rvert
+ 2))$: $r_i = \|\mathbf{Q}^{\mathsf{H}}\mathbf{e}_i\|^2$ has the law of the squared length of a
projected uniform unit vector. -/
private theorem integral_sum_sq_sq_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (i : n) :
    ∫ ω, (∑ j, X ω i j ^ 2) ^ 2 ∂μ =
      Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2)) := by
  classical
  have : Nonempty n := ⟨i⟩
  obtain ⟨e⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  have hV := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) e.injective
  have hx : ‖WithLp.toLp 2 (Pi.single i 1 : n → ℝ)‖ = 1 := by
    rw [PiLp.toLp_single, PiLp.norm_single, norm_one]
  have h := hasLaw_conjTranspose_mulVec_of_hasLaw_haarFrame hX hV hx
  have hrow (M : Matrix n k ℝ) :
      (∑ j, M i j ^ 2) ^ 2 = ‖WithLp.toLp 2 (Mᴴ *ᵥ Pi.single i 1)‖ ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, EuclideanSpace.norm_toLp_sq_eq_sum_sq]
    congr 2
    funext j
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  simp only [hrow]
  have hF : Continuous fun w : k → ℝ => ‖WithLp.toLp 2 w‖ ^ 4 := by fun_prop
  have h1 := h.integral_comp hF.aestronglyMeasurable
  simp only [Function.comp_def] at h1
  have hm : Measurable fun w : n → ℝ => (selectionMatrix e : Matrix n k ℝ)ᴴ *ᵥ w :=
    (continuous_const.matrix_mulVec continuous_id).measurable
  rw [h1, integral_map hm.aemeasurable hF.aestronglyMeasurable]
  exact integral_norm_conjTranspose_mulVec_pow_four_of_hasLaw_uniformSphereVector HasLaw.id hV

/-- The cross moments $\mathbb{E} r_i r_l$, $i \ne l$, do not depend on the pair: the rows
$(i, l)$ of a Haar frame have the law of the corner of a Haar orthogonal matrix
(`NLAlib.hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols`). -/
private theorem integral_sum_sq_mul_sum_sq_eq [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) {i l i' l' : n}
    (hil : i ≠ l) (hil' : i' ≠ l') :
    ∫ ω, (∑ j, X ω i j ^ 2) * ∑ j, X ω l j ^ 2 ∂μ =
      ∫ ω, (∑ j, X ω i' j ^ 2) * ∑ j, X ω l' j ^ 2 ∂μ := by
  classical
  obtain ⟨e⟩ : Nonempty (k ↪ n) := Function.Embedding.nonempty_of_card_le hk
  have hV := hasOrthonormalCols_selectionMatrix (𝕜 := ℝ) e.injective
  set G : Matrix (Fin 2) k ℝ → ℝ := fun M => (∑ j, M 0 j ^ 2) * ∑ j, M 1 j ^ 2 with hGdef
  have hG : Continuous G := by fun_prop
  have key {a b : n} (hab : a ≠ b) : ∫ ω, (∑ j, X ω a j ^ 2) * ∑ j, X ω b j ^ 2 ∂μ =
      ∫ M, G M ∂((haarFrame (Fin 2) n).map (· * selectionMatrix e)) := by
    have hW : HasOrthonormalCols ((selectionMatrix ![a, b] : Matrix n (Fin 2) ℝ)ᴴ)ᴴ := by
      rw [Matrix.conjTranspose_conjTranspose]
      exact hasOrthonormalCols_selectionMatrix (injective_pair_iff_ne.2 hab)
    have h := (hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols hX hW hV).integral_comp
      hG.aestronglyMeasurable
    simp only [Function.comp_def, hGdef, conjTranspose_selectionMatrix_mul,
      Matrix.submatrix_apply, id, Matrix.cons_val_zero, Matrix.cons_val_one] at h
    exact h
  rw [key hil, key hil']

/-- The squared row norms of a frame sum to $\lvert k \rvert$:
$\sum_l r_l = \operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{Q})$. -/
private theorem sum_sum_sq_eq_card [DecidableEq k] {Q : Matrix n k ℝ}
    (hQ : HasOrthonormalCols Q) : ∑ l, ∑ j, Q l j ^ 2 = Fintype.card k := by
  have h := congrArg Matrix.trace (hasOrthonormalCols_iff.1 hQ)
  rw [Matrix.trace_one] at h
  rw [← h, Matrix.trace, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial, sq]

/-- The table of second moments of the squared row norms: $\mathbb{E} r_i r_l$ is
$a = \lvert k \rvert (\lvert k \rvert + 2) / (\lvert n \rvert (\lvert n \rvert + 2))$ on the
diagonal and $c = (\lvert k \rvert^2 / \lvert n \rvert - a) / (\lvert n \rvert - 1)$ off it. -/
private theorem integral_sum_sq_mul_sum_sq [DecidableEq n] [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (i l : n) :
    ∫ ω, (∑ j, X ω i j ^ 2) * ∑ j, X ω l j ^ 2 ∂μ =
      if i = l then
        (Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2)) : ℝ)
      else ((Fintype.card k : ℝ) ^ 2 / Fintype.card n -
          Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))) /
        (Fintype.card n - 1) := by
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  split_ifs with hil
  · subst hil
    rw [← integral_sum_sq_sq_of_hasLaw_haarFrame hX hk i]
    simp only [sq]
  set a : ℝ := Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))
  set b := ∫ ω, (∑ j, X ω i j ^ 2) * ∑ j, X ω l j ^ 2 ∂μ
  have hint (l' : n) : Integrable (fun ω => (∑ j, X ω i j ^ 2) * ∑ j, X ω l' j ^ 2) μ :=
    integrable_comp_of_hasLaw_haarFrame hX 
      (F := fun M : Matrix n k ℝ => (∑ j, M i j ^ 2) * ∑ j, M l' j ^ 2)
      (by fun_prop)
  -- `∑_{l'} E r_i r_{l'} = E [r_i ∑_{l'} r_{l'}] = |k| E r_i`
  have hsum : ∑ l', ∫ ω, (∑ j, X ω i j ^ 2) * ∑ j, X ω l' j ^ 2 ∂μ =
      (Fintype.card k : ℝ) ^ 2 / Fintype.card n := by
    rw [← integral_finsetSum _ fun l' _ => hint l']
    have h : (fun ω => ∑ l', (∑ j, X ω i j ^ 2) * ∑ j, X ω l' j ^ 2) =ᵐ[μ]
        fun ω => (Fintype.card k : ℝ) * ∑ j, X ω i j ^ 2 := by
      filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hX hk] with ω hω
      rw [← Finset.mul_sum, sum_sum_sq_eq_card hω, mul_comm]
    rw [integral_congr_ae h, integral_const_mul, integral_sum_sq_of_hasLaw_haarFrame hX hk i]
    ring
  have hoff (l' : n) (hl' : l' ∈ Finset.univ.erase i) :
      ∫ ω, (∑ j, X ω i j ^ 2) * ∑ j, X ω l' j ^ 2 ∂μ = b :=
    integral_sum_sq_mul_sum_sq_eq hX hk (Finset.ne_of_mem_erase hl').symm hil
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), Finset.sum_congr rfl hoff,
    Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hdiag : ∫ ω, (∑ j, X ω i j ^ 2) * ∑ j, X ω i j ^ 2 ∂μ = a := by
    simpa only [sq] using integral_sum_sq_sq_of_hasLaw_haarFrame hX hk i
  rw [hdiag] at hsum
  have h1 : 1 ≤ Fintype.card n := Fintype.card_pos_iff.2 ⟨i⟩
  have h2 : (Fintype.card n : ℝ) - 1 ≠ 0 := by
    have : 1 < Fintype.card n := Fintype.one_lt_card_iff.2 ⟨i, l, hil⟩
    have : (1 : ℝ) < Fintype.card n := by exact_mod_cast this
    linarith
  rw [Nat.cast_sub h1, Nat.cast_one] at hsum
  rw [eq_div_iff h2]
  linarith

/-- The mean and second moment of $\sum_i \mathbf{d}_i r_i$ in closed form. -/
private theorem integral_sum_mul_sum_sq_sq [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : n → ℝ) :
    ∫ ω, (∑ i, d i * ∑ j, X ω i j ^ 2) ^ 2 ∂μ =
      (Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2)) -
        ((Fintype.card k : ℝ) ^ 2 / Fintype.card n -
          Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))) /
        (Fintype.card n - 1)) * ∑ i, d i ^ 2 +
      ((Fintype.card k : ℝ) ^ 2 / Fintype.card n -
          Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))) /
        (Fintype.card n - 1) * (∑ i, d i) ^ 2 := by
  classical
  set a : ℝ := Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))
  set c : ℝ := ((Fintype.card k : ℝ) ^ 2 / Fintype.card n - a) / (Fintype.card n - 1)
  have hexp (ω : Ω) : (∑ i, d i * ∑ j, X ω i j ^ 2) ^ 2 =
      ∑ i, ∑ l, d i * d l * ((∑ j, X ω i j ^ 2) * ∑ j, X ω l j ^ 2) := by
    rw [sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  have hint (i l : n) : Integrable
      (fun ω => d i * d l * ((∑ j, X ω i j ^ 2) * ∑ j, X ω l j ^ 2)) μ :=
    integrable_comp_of_hasLaw_haarFrame hX
      (F := fun M : Matrix n k ℝ => d i * d l * ((∑ j, M i j ^ 2) * ∑ j, M l j ^ 2)) (by fun_prop)
  simp only [hexp]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun l _ => hint i l]
  calc _ = ∑ i : n, ∑ l : n, d i * d l * (c + (a - c) * if i = l then 1 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_finsetSum _ fun l _ => hint i l]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [integral_const_mul, integral_sum_sq_mul_sum_sq hX hk i l]
        split_ifs <;> ring
    _ = c * ((∑ i, d i) * ∑ l, d l) + (a - c) * ∑ i, d i ^ 2 := by
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [show (a - c) * d i ^ 2 = ∑ l, (a - c) * (d i * d l) * (if i = l then 1 else 0) by
          simp [sq], Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ = _ := by ring

/-- The compression of a diagonalised matrix: with $\mathbf{R} = \mathbf{U}^{\mathsf{H}}\mathbf{Q}$,
$\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{U}\operatorname{diag}(\mathbf{d})
\mathbf{U}^{\mathsf{H}}\mathbf{Q}) = \sum_i \mathbf{d}_i \sum_j \mathbf{R}_{i,j}^2$. -/
private theorem trace_conjTranspose_mul_mul_eq_sum [DecidableEq n] (Q : Matrix n k ℝ)
    (U : Matrix n n ℝ) (d : n → ℝ) :
    (Qᴴ * (U * Matrix.diagonal d * Uᴴ) * Q).trace = ∑ i, d i * ∑ j, (Uᴴ * Q) i j ^ 2 := by
  have h : Qᴴ * (U * Matrix.diagonal d * Uᴴ) * Q = (Uᴴ * Q)ᴴ * Matrix.diagonal d * (Uᴴ * Q) := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [h, Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
    Matrix.diagonal_apply, mul_ite, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- $\|\mathbf{A}\|_{\mathsf{F}}^2 = \sum_i \mathbf{d}_i^2$ and
$\operatorname{tr} \mathbf{A} = \sum_i \mathbf{d}_i$ for
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$, $\mathbf{U}$
orthogonal. -/
private theorem frobNorm_sq_and_trace_of_eq_mul_diagonal [DecidableEq n] {U : Matrix n n ℝ}
    (hU : HasOrthonormalCols U) (d : n → ℝ) :
    frobNorm (U * Matrix.diagonal d * Uᴴ) ^ 2 = ∑ i, d i ^ 2 ∧
      (U * Matrix.diagonal d * Uᴴ).trace = ∑ i, d i := by
  have hUU := hasOrthonormalCols_iff.1 hU
  have htr (D : Matrix n n ℝ) : (U * D * Uᴴ).trace = D.trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
  refine ⟨?_, by rw [htr, Matrix.trace_diagonal]⟩
  have h : (U * Matrix.diagonal d * Uᴴ)ᴴ * (U * Matrix.diagonal d * Uᴴ) =
      U * (Matrix.diagonal d * Matrix.diagonal d) * Uᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.diagonal_conjTranspose, star_trivial, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Uᴴ U, hUU, Matrix.one_mul]
  rw [frobNorm_sq_eq_re_trace, h, htr, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
    RCLike.re_to_real]
  simp only [sq]

/-- The mean of a Haar compression:
$\mathbb{E}\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
= (\lvert k \rvert / \lvert n \rvert) \operatorname{tr} \mathbf{A}$ for an $n \times k$ Haar frame
$\mathbf{Q}$, $\lvert k \rvert \le \lvert n \rvert$, and any square $\mathbf{A}$: the trace of
`NLAlib.integral_conjTranspose_mul_mul_of_hasLaw_haarFrame`. -/
theorem integral_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) (A : Matrix n n ℝ) :
    ∫ ω, ((X ω)ᴴ * A * X ω).trace ∂μ = Fintype.card k / Fintype.card n * A.trace := by
  rw [Matrix.integral_trace (integrable_conjTranspose_mul_mul_of_hasLaw_haarFrame hX A),
    integral_conjTranspose_mul_mul_of_hasLaw_haarFrame hX hk A, Matrix.trace_smul,
    Matrix.trace_one, smul_eq_mul]
  ring

/-- The second moment of a Haar compression of a symmetric matrix, with $a$ and $c$ the moments of
`integral_sum_sq_mul_sum_sq`. -/
private theorem integral_trace_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    ∫ ω, ((X ω)ᴴ * A * X ω).trace ^ 2 ∂μ =
      (Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2)) -
        ((Fintype.card k : ℝ) ^ 2 / Fintype.card n -
          Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))) /
        (Fintype.card n - 1)) * frobNorm A ^ 2 +
      ((Fintype.card k : ℝ) ^ 2 / Fintype.card n -
          Fintype.card k * (Fintype.card k + 2) / (Fintype.card n * (Fintype.card n + 2))) /
        (Fintype.card n - 1) * A.trace ^ 2 := by
  classical
  obtain ⟨U, d, hU, hAeq⟩ := hA.exists_hasOrthonormalCols_eq_mul_diagonal_mul_conjTranspose
  simp only [RCLike.ofReal_real_eq_id, id] at hAeq
  subst hAeq
  obtain ⟨hF, hT⟩ := frobNorm_sq_and_trace_of_eq_mul_diagonal hU d
  rw [hF, hT]
  simp only [trace_conjTranspose_mul_mul_eq_sum]
  exact integral_sum_mul_sum_sq_sq (hasLaw_const_mul_of_isLeftUnitarilyInvariant hX
    hU.conjTranspose) hk d

/-- $\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$ is square integrable for a
Haar frame. -/
private theorem memLp_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (A : Matrix n n ℝ) :
    MemLp (fun ω => ((X ω)ᴴ * A * X ω).trace) 2 μ :=
  memLp_comp_of_hasLaw_haarFrame hX (F := fun M : Matrix n k ℝ => (Mᴴ * A * M).trace)
    (by fun_prop) 2

/-- A $1 \times 1$ matrix has $\|\mathbf{A}\|_{\mathsf{F}}^2 = (\operatorname{tr}\mathbf{A})^2$. -/
private theorem frobNorm_sq_eq_trace_sq_of_card_eq_one {A : Matrix n n ℝ}
    (h : Fintype.card n = 1) : frobNorm A ^ 2 = A.trace ^ 2 := by
  obtain ⟨i, hi⟩ := Fintype.card_eq_one_iff.1 h
  have hs (f : n → ℝ) : ∑ x, f x = f i := Fintype.sum_eq_single i fun x hx => absurd (hi x) hx
  rw [frobNorm_sq_eq_sum_sq, Matrix.trace, hs, hs, hs, Matrix.diag_apply]

/-- **The variance of a Haar compression**, multiplied out: for an $n \times k$ Haar frame
$\mathbf{Q}$, $\lvert k \rvert \le \lvert n \rvert$, and real symmetric $\mathbf{A}$,
$$(\lvert n \rvert - 1)\lvert n \rvert^2(\lvert n \rvert + 2)\,
\operatorname{Var}\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
= 2\lvert k \rvert(\lvert n \rvert - \lvert k \rvert)\bigl(\lvert n \rvert
\|\mathbf{A}\|_{\mathsf{F}}^2 - (\operatorname{tr} \mathbf{A})^2\bigr)\,.$$
Every dimension, including $\lvert n \rvert = 1$ (both sides vanish); the divided form is
`NLAlib.variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame`. From invariance and the fourth
moment of a projected sphere vector. [Epperly2023, Uniform on the Real Sphere], there the case
$\lvert k \rvert = 1$. -/
theorem mul_variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    ((Fintype.card n : ℝ) - 1) * Fintype.card n ^ 2 * (Fintype.card n + 2) *
        variance (fun ω => ((X ω)ᴴ * A * X ω).trace) μ =
      2 * Fintype.card k * (Fintype.card n - Fintype.card k) *
        (Fintype.card n * frobNorm A ^ 2 - A.trace ^ 2) := by
  classical
  have := hX.isProbabilityMeasure_iff.2 inferInstance
  rw [variance_eq_sub (memLp_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame hX A)]
  simp only [Pi.pow_apply]
  rw [integral_trace_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame hX hk hA,
    integral_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame hX hk A]
  rcases Nat.lt_or_ge (Fintype.card n) 2 with hn | hn
  · interval_cases h : Fintype.card n
    · have hK0 : Fintype.card k = 0 := Nat.le_zero.1 (h ▸ hk)
      simp [hK0]
    · rw [frobNorm_sq_eq_trace_sq_of_card_eq_one h, Nat.cast_one]
      ring
  · have hN2 : (2 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
    have hN0 : (Fintype.card n : ℝ) ≠ 0 := by linarith
    have hN1 : (Fintype.card n : ℝ) - 1 ≠ 0 := by linarith
    have hN2' : (Fintype.card n : ℝ) + 2 ≠ 0 := by linarith
    field_simp
    ring

/-- **The variance of a Haar compression**: for an $n \times k$ Haar frame $\mathbf{Q}$ with
$\lvert k \rvert \le \lvert n \rvert$ and $\lvert n \rvert \ge 2$, and real symmetric
$\mathbf{A}$,
$$\operatorname{Var}\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
= \frac{2\lvert k \rvert(\lvert n \rvert - \lvert k \rvert)}
{(\lvert n \rvert - 1)\lvert n \rvert(\lvert n \rvert + 2)}
\Bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 - \frac{(\operatorname{tr} \mathbf{A})^2}{\lvert n \rvert}
\Bigr)\,.$$
It vanishes for $\lvert k \rvert = \lvert n \rvert$ (then the trace is $\operatorname{tr}
\mathbf{A}$) and for $\mathbf{A}$ a multiple of $\mathbf{I}$; with $\lvert k \rvert = 1$ it is the
sphere's variance (`NLAlib.variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector`). The
multiplied form, valid for every $\lvert n \rvert$, is
`NLAlib.mul_variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame`; for nonsymmetric
$\mathbf{A}$, `NLAlib.variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame_hermitianPart`.
[Epperly2023, Uniform on the Real Sphere], there $\lvert k \rvert = 1$; here any number of
orthonormal probes.
Result: haar-compression-trace-variance -/
theorem variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n)
    (hn : 1 < Fintype.card n) {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => ((X ω)ᴴ * A * X ω).trace) μ =
      2 * Fintype.card k * (Fintype.card n - Fintype.card k) /
          ((Fintype.card n - 1) * Fintype.card n * (Fintype.card n + 2)) *
        (frobNorm A ^ 2 - A.trace ^ 2 / Fintype.card n) := by
  have h := mul_variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame hX hk hA
  have hN : (1 : ℝ) < Fintype.card n := by exact_mod_cast hn
  have hN0 : (Fintype.card n : ℝ) ≠ 0 := by linarith
  have hN1 : (Fintype.card n : ℝ) - 1 ≠ 0 := by linarith
  have hN2 : (Fintype.card n : ℝ) + 2 ≠ 0 := by linarith
  field_simp
  linear_combination h

/-- **The variance of a Haar compression of any real matrix**: for an $n \times k$ Haar frame
$\mathbf{Q}$, $\lvert k \rvert \le \lvert n \rvert$, $\lvert n \rvert \ge 2$, and any real
$\mathbf{A}$ with symmetric part
$\mathbf{H} = \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{T}})$,
$$\operatorname{Var}\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})
= \frac{2\lvert k \rvert(\lvert n \rvert - \lvert k \rvert)}
{(\lvert n \rvert - 1)\lvert n \rvert(\lvert n \rvert + 2)}
\Bigl(\|\mathbf{H}\|_{\mathsf{F}}^2 - \frac{(\operatorname{tr} \mathbf{A})^2}{\lvert n \rvert}
\Bigr)\,:$$
the trace of a compression sees only $\mathbf{H}$
(`NLAlib.trace_conjTranspose_mul_hermitianPart_mul`), and
`NLAlib.variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame` applies to it.
[Epperly2023, Real-Valued Test Vectors], there $\lvert k \rvert = 1$. -/
theorem variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame_hermitianPart [DecidableEq k]
    (hX : HasLaw X (haarFrame n k) μ) (hk : Fintype.card k ≤ Fintype.card n)
    (hn : 1 < Fintype.card n) (A : Matrix n n ℝ) :
    variance (fun ω => ((X ω)ᴴ * A * X ω).trace) μ =
      2 * Fintype.card k * (Fintype.card n - Fintype.card k) /
          ((Fintype.card n - 1) * Fintype.card n * (Fintype.card n + 2)) *
        (frobNorm (hermitianPart A) ^ 2 - A.trace ^ 2 / Fintype.card n) := by
  classical
  have htr : (hermitianPart A).trace = A.trace := by simpa using trace_hermitianPart A
  rw [← htr, ← variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame hX hk hn
    (isHermitian_hermitianPart A)]
  simp only [trace_conjTranspose_mul_hermitianPart_mul]

/-- The quadratic form at a vector is the trace of the compression by its one-column matrix. -/
private theorem quadForm_eq_trace_replicateCol (A : Matrix n n ℝ) (u : n → ℝ) :
    quadForm A u = ((Matrix.replicateCol Unit u)ᴴ * A * Matrix.replicateCol Unit u).trace := by
  simp only [quadForm_eq_sum, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.replicateCol_apply, star_trivial, Finset.univ_unique,
    Finset.sum_singleton, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The variance of the Girard–Hutchinson estimate with a sphere probe**: for $\mathbf{u}$
uniform on the unit sphere of $\mathbb{R}^n$, so that $\boldsymbol{\omega} =
\sqrt{\lvert n \rvert}\,\mathbf{u}$ is uniform on the sphere of radius $\sqrt{\lvert n \rvert}$,
and real symmetric $\mathbf{A}$,
$$\operatorname{Var}(\boldsymbol{\omega}^{\mathsf{T}}\mathbf{A}\boldsymbol{\omega})
= \frac{2\lvert n \rvert}{\lvert n \rvert + 2}
\Bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 - \frac{(\operatorname{tr} \mathbf{A})^2}{\lvert n \rvert}
\Bigr)\,,$$
every dimension. The case $\lvert k \rvert = 1$ of the Haar compression
(`NLAlib.mul_variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame`), by
`NLAlib.hasLaw_replicateCol_of_hasLaw_uniformSphereVector`. For nonsymmetric $\mathbf{A}$,
`NLAlib.variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector_hermitianPart`.
[Epperly2023, Real-Valued Test Vectors] and [Epperly2023, Uniform on the Real Sphere]; proved
there by the radius–direction decomposition of a Gaussian, here from invariance alone.
Result: hutchinson-variance-real-sphere -/
theorem variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector {u : Ω → n → ℝ}
    (hu : HasLaw u (uniformSphereVector n) μ) {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    variance (fun ω => quadForm A (√(Fintype.card n : ℝ) • u ω)) μ =
      2 * Fintype.card n / (Fintype.card n + 2) *
        (frobNorm A ^ 2 - A.trace ^ 2 / Fintype.card n) := by
  classical
  have := hu.isProbabilityMeasure_iff.2 inferInstance
  have hQ := hasLaw_replicateCol_of_hasLaw_uniformSphereVector hu
  have hq (ω : Ω) : quadForm A (√(Fintype.card n : ℝ) • u ω) = Fintype.card n *
      ((Matrix.replicateCol Unit (u ω))ᴴ * A * Matrix.replicateCol Unit (u ω)).trace := by
    rw [quadForm_smul_right, star_trivial, Real.mul_self_sqrt (Nat.cast_nonneg _),
      quadForm_eq_trace_replicateCol]
  simp only [hq]
  rw [variance_const_mul]
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  have hk : Fintype.card Unit ≤ Fintype.card n := Fintype.card_pos
  rw [variance_eq_sub (memLp_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame hQ A)]
  simp only [Pi.pow_apply]
  rw [integral_trace_conjTranspose_mul_mul_sq_of_hasLaw_haarFrame hQ hk hA,
    integral_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame hQ hk A]
  simp only [Fintype.card_unit, Nat.cast_one]
  rcases Nat.lt_or_ge (Fintype.card n) 2 with h2 | h2
  · have h1 : Fintype.card n = 1 := le_antisymm (Nat.lt_succ_iff.1 h2) Fintype.card_pos
    rw [frobNorm_sq_eq_trace_sq_of_card_eq_one h1, h1]
    norm_num
  · have hN2 : (2 : ℝ) ≤ Fintype.card n := by exact_mod_cast h2
    have hN0 : (Fintype.card n : ℝ) ≠ 0 := by linarith
    have hN1 : (Fintype.card n : ℝ) - 1 ≠ 0 := by linarith
    have hN2' : (Fintype.card n : ℝ) + 2 ≠ 0 := by linarith
    field_simp
    ring

/-- **The variance with a sphere probe, any real matrix**: for $\boldsymbol{\omega}$ uniform on the
sphere of radius $\sqrt{\lvert n \rvert}$ and any real $\mathbf{A}$ with symmetric part
$\mathbf{H} = \tfrac{1}{2}(\mathbf{A} + \mathbf{A}^{\mathsf{T}})$,
$$\operatorname{Var}(\boldsymbol{\omega}^{\mathsf{T}}\mathbf{A}\boldsymbol{\omega})
= \frac{2\lvert n \rvert}{\lvert n \rvert + 2}
\Bigl(\|\mathbf{H}\|_{\mathsf{F}}^2 - \frac{(\operatorname{tr} \mathbf{A})^2}{\lvert n \rvert}
\Bigr)\,,$$
from `NLAlib.variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector` and
`NLAlib.quadForm_hermitianPart`. [Epperly2023, Real-Valued Test Vectors]. -/
theorem variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector_hermitianPart {u : Ω → n → ℝ}
    (hu : HasLaw u (uniformSphereVector n) μ) (A : Matrix n n ℝ) :
    variance (fun ω => quadForm A (√(Fintype.card n : ℝ) • u ω)) μ =
      2 * Fintype.card n / (Fintype.card n + 2) *
        (frobNorm (hermitianPart A) ^ 2 - A.trace ^ 2 / Fintype.card n) := by
  classical
  have htr : (hermitianPart A).trace = A.trace := by simpa using trace_hermitianPart A
  rw [← htr, ← variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector hu
    (isHermitian_hermitianPart A)]
  simp only [quadForm_hermitianPart]

end TraceVariance

end NLAlib
