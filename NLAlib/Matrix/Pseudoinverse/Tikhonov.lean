/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.RegularizedLeastSquares

/-!
# Standard Tikhonov regularization

The identity-penalty specialization of `NLAlib.tikhonovInverse` is the unique penalized
least-squares solution operator at every positive parameter. Its singular-value filter has
the uniform noise envelope $1/(2\sqrt{\beta})$, and converges to the pseudoinverse as
$\beta$ decreases to zero. Rank deficiency and empty dimensions are included.

Proof material adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Basic/Tikhonov.lean` and `TikhonovLimit.lean`, consolidated through the shared
regularized least-squares API and the native `IsSVD` interface.

## Main results

* `NLAlib.IsSVD.tikhonovInverse_one_eq`: the singular-value filter.
* `NLAlib.isMinOn_tikhonovObjective_one_iff`: the unique penalized minimizer.
* `NLAlib.specNorm_tikhonovInverse_one_le`: the uniform operator-norm envelope.
* `NLAlib.norm_sub_tikhonovInverse_mulVec_le`: deterministic noise amplification.
* `NLAlib.tendsto_tikhonovInverse_one_zero`: convergence to the pseudoinverse.
* `NLAlib.tendsto_tikhonovInverse_one_mulVec_zero`: convergence of the solution vector.
-/

@[expose] public section

open Filter Topology
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
  [DecidableEq n]

omit [Fintype n] in
/-- Adding a positive multiple of the identity makes the Gram matrix positive definite,
with no rank assumption. This is the standard Tikhonov normal matrix. -/
theorem posDef_conjTranspose_mul_self_add_smul_one [Finite n] (A : Matrix m n 𝕜)
    {β : ℝ} (hβ : 0 < β) : (Aᴴ * A + β • 1).PosDef :=
  Matrix.PosDef.posSemidef_add (Matrix.posSemidef_conjTranspose_mul_self A)
    (Matrix.PosDef.one.smul hβ)

/-- At positive parameter the identity-penalty regularized inverse is
$(\mathbf{A}^{\mathsf{H}}\mathbf{A} + \beta\mathbf{I})^{-1}\mathbf{A}^{\mathsf{H}}$.
The shared definition uses the pseudoinverse and is meaningful also at zero parameter. -/
theorem tikhonovInverse_one_eq (A : Matrix m n 𝕜) {β : ℝ} (hβ : 0 < β) :
    tikhonovInverse A (1 : Matrix n n 𝕜) β = (Aᴴ * A + β • 1)⁻¹ * Aᴴ := by
  rw [tikhonovInverse, Matrix.conjTranspose_one, Matrix.one_mul,
    pinv_of_isUnit (posDef_conjTranspose_mul_self_add_smul_one A hβ).isUnit]

/-- **Tikhonov spectral filter.** For any SVD
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\boldsymbol{\sigma})\mathbf{V}^{\mathsf{H}}$
over $\Bbbk$ and $\beta > 0$, the standard regularized inverse is
$$\mathbf{V}\operatorname{diag}\!\left(\frac{\sigma_i}{\sigma_i^2 + \beta}\right)
  \mathbf{U}^{\mathsf{H}}.$$
Zero singular values and arbitrary rectangular dimensions are included.
[FesslerNadakuditi2024, §5.6.5, equations (5.44)–(5.48)].
Result: tikhonov-spectral-filter -/
theorem IsSVD.tikhonovInverse_one_eq {r : Type*} [Fintype r] [DecidableEq r]
    {A : Matrix m n 𝕜} {U : Matrix m r 𝕜} {V : Matrix n r 𝕜} {σ : r → ℝ}
    (h : IsSVD A U σ V) {β : ℝ} (hβ : 0 < β) :
    tikhonovInverse A (1 : Matrix n n 𝕜) β =
      V * Matrix.diagonal (fun i => ((σ i / (σ i ^ 2 + β) : ℝ) : 𝕜)) * Uᴴ := by
  let S : Matrix r r 𝕜 := Matrix.diagonal (fun i => (σ i : 𝕜))
  let G : Matrix r r 𝕜 := Matrix.diagonal (fun i => ((σ i ^ 2 + β : ℝ) : 𝕜))
  let F : Matrix r r 𝕜 :=
    Matrix.diagonal (fun i => ((σ i / (σ i ^ 2 + β) : ℝ) : 𝕜))
  have hHV : (Aᴴ * A + β • 1) * V = V * G := by
    calc
      _ = Aᴴ * (A * V) + β • V := by
        simp only [Matrix.add_mul, Matrix.mul_assoc, Matrix.smul_mul, Matrix.one_mul]
      _ = V * S * S + β • V := by
        rw [h.mul_right_eq, ← Matrix.mul_assoc, h.conjTranspose.mul_right_eq]
      _ = V * (S * S + β • (1 : Matrix r r 𝕜)) := by
        simp only [Matrix.mul_add, Matrix.mul_smul, Matrix.mul_one, Matrix.mul_assoc]
      _ = _ := by
        congr 1
        ext i j
        by_cases hij : i = j
        · subst j
          simp only [S, G, Matrix.diagonal_mul_diagonal, Matrix.add_apply,
            Matrix.diagonal_apply_eq, Matrix.smul_apply, Matrix.one_apply_eq,
            RCLike.real_smul_eq_coe_mul, mul_one, RCLike.ofReal_add, pow_two,
            RCLike.ofReal_mul]
        · simp only [S, G, Matrix.diagonal_mul_diagonal, Matrix.add_apply,
            Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.one_apply_ne hij,
            smul_zero, add_zero]
  have hGF : G * F = S := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    rw [← RCLike.ofReal_mul]
    congr 1
    exact mul_div_cancel₀ _ (show σ i ^ 2 + β ≠ 0 by positivity)
  have hnormal : (Aᴴ * A + β • 1) * (V * F * Uᴴ) = Aᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hHV, Matrix.mul_assoc V G F, hGF]
    simpa only [Matrix.mul_assoc, S] using h.conjTranspose.eq.symm
  rw [NLAlib.tikhonovInverse_one_eq A hβ]
  calc
    _ = (Aᴴ * A + β • 1)⁻¹ * ((Aᴴ * A + β • 1) * (V * F * Uᴴ)) :=
      congrArg ((Aᴴ * A + β • 1)⁻¹ * ·) hnormal.symm
    _ = _ := by
      rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp
        (posDef_conjTranspose_mul_self_add_smul_one A hβ).isUnit), Matrix.one_mul]

/-- **Unique Tikhonov minimizer.** For every rectangular matrix $\mathbf{A}$ over $\Bbbk$,
data $\mathbf{b}$, and $\beta > 0$, the unique minimizer of
$\|\mathbf{b} - \mathbf{A}\mathbf{x}\|^2 + \beta\|\mathbf{x}\|^2$ is the identity-penalty
regularized inverse applied to $\mathbf{b}$. No full-rank hypothesis is required.
[FesslerNadakuditi2024, §5.6.5, equations (5.44)–(5.48)].
Result: tikhonov-spectral-filter -/
theorem isMinOn_tikhonovObjective_one_iff (A : Matrix m n 𝕜) (b : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) {x : n → 𝕜} :
    IsMinOn (tikhonovObjective A (1 : Matrix n n 𝕜) b β) Set.univ x ↔
      x = tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ b := by
  rw [isMinOn_tikhonovObjective_iff_normal_equations A (1 : Matrix n n 𝕜) b hβ.le,
    Matrix.conjTranspose_one, Matrix.one_mul, tikhonovInverse_one_eq A hβ,
    ← Matrix.mulVec_mulVec]
  have hdet := (Matrix.isUnit_iff_isUnit_det _).mp
    (posDef_conjTranspose_mul_self_add_smul_one A hβ).isUnit
  constructor
  · intro hx
    rw [← hx, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  · rintro rfl
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

/-- The scalar Tikhonov filter has a uniform envelope, used for the matrix norm bound. -/
private theorem abs_div_sq_add_le {s β : ℝ} (hs : 0 ≤ s) (hβ : 0 < β) :
    |s / (s ^ 2 + β)| ≤ 1 / (2 * Real.sqrt β) := by
  have hd : 0 < s ^ 2 + β := by positivity
  have hr : 0 < 2 * Real.sqrt β := by positivity
  rw [abs_of_nonneg (by positivity), div_le_div_iff₀ hd hr]
  nlinarith [Real.sq_sqrt hβ.le, sq_nonneg (s - Real.sqrt β)]

/-- **Tikhonov noise envelope.** For every rectangular matrix $\mathbf{A}$ over $\Bbbk$
and $\beta > 0$, the identity-penalty regularized inverse satisfies
$$\|(\mathbf{A}^{\mathsf{H}}\mathbf{A} + \beta\mathbf{I})^{-1}
  \mathbf{A}^{\mathsf{H}}\|_2 \le \frac{1}{2\sqrt{\beta}}.$$
[FesslerNadakuditi2024, §5.6.5, equations (5.44)–(5.48)]; the scalar envelope is derived
from its filter formula and attained at singular value $\sqrt{\beta}$.
This is a deterministic bound without a rank assumption.
Result: tikhonov-spectral-filter -/
theorem specNorm_tikhonovInverse_one_le (A : Matrix m n 𝕜) {β : ℝ} (hβ : 0 < β) :
    specNorm (tikhonovInverse A (1 : Matrix n n 𝕜) β) ≤ 1 / (2 * Real.sqrt β) := by
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  rw [h.tikhonovInverse_one_eq hβ, h.hasOrthonormalCols_left.specNorm_mul_conjTranspose_right,
    h.hasOrthonormalCols_right.specNorm_mul_left, specNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro i
  rw [RCLike.norm_ofReal]
  exact abs_div_sq_add_le (singularValues_nonneg A i) hβ

/-- **Noise amplification for Tikhonov solutions.** For a rectangular matrix $\mathbf{A}$
over $\Bbbk$, data $\mathbf{b}$, perturbation $\mathbf{e}$, and $\beta > 0$, the Euclidean
distance between the standard regularized solutions from clean and perturbed data is at most
$$\frac{\|\mathbf{e}\|}{2\sqrt{\beta}}.$$
[FesslerNadakuditi2024, §5.6.5, equations (5.44)–(5.48)]; a deterministic corollary of the
scalar filter envelope, with no rank or probabilistic hypothesis.
Result: tikhonov-spectral-filter -/
theorem norm_sub_tikhonovInverse_mulVec_le (A : Matrix m n 𝕜) (b e : m → 𝕜)
    {β : ℝ} (hβ : 0 < β) :
    ‖WithLp.toLp 2 (tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ b -
      tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ (b + e))‖ ≤
        ‖WithLp.toLp 2 e‖ / (2 * Real.sqrt β) := by
  rw [Matrix.mulVec_add, sub_add_cancel_left, WithLp.toLp_neg, norm_neg]
  calc
    _ ≤ specNorm (tikhonovInverse A (1 : Matrix n n 𝕜) β) * ‖WithLp.toLp 2 e‖ :=
      norm_toLp_mulVec_le _ _
    _ ≤ _ := by
      simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using
        mul_le_mul_of_nonneg_right (specNorm_tikhonovInverse_one_le A hβ)
          (norm_nonneg (WithLp.toLp 2 e))

/-- **Vanishing-parameter Tikhonov limit.** For every rectangular matrix $\mathbf{A}$ over
$\Bbbk$, the identity-penalty regularized inverse converges to $\mathbf{A}^{+}$ as
$\beta \downarrow 0$. The limit includes rank-deficient and zero matrices and empty dimensions.
[FesslerNadakuditi2024, §5.6.5, equations (5.44)–(5.48)].
Result: tikhonov-spectral-filter -/
theorem tendsto_tikhonovInverse_one_zero (A : Matrix m n 𝕜) :
    Tendsto (fun β : ℝ => tikhonovInverse A (1 : Matrix n n 𝕜) β)
      (𝓝[>] 0) (𝓝 (pinv A)) := by
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  let F := fun β : ℝ => V * Matrix.diagonal
    (fun i : Fin A.rank => ((singularValues A i / (singularValues A i ^ 2 + β) : ℝ) : 𝕜)) * Uᴴ
  have hscalar (i : Fin A.rank) : ContinuousAt
      (fun β : ℝ => ((singularValues A i / (singularValues A i ^ 2 + β) : ℝ) : 𝕜)) 0 := by
    apply RCLike.continuous_ofReal.continuousAt.comp
    apply continuousAt_const.div (continuousAt_const.add continuousAt_id)
    simpa only [Pi.add_apply, id_eq, add_zero] using
      (sq_pos_of_pos ((singularValues_pos_iff A).mpr i.isLt)).ne'
  have hdiag : ContinuousAt (fun β : ℝ => Matrix.diagonal
      (fun i : Fin A.rank => ((singularValues A i / (singularValues A i ^ 2 + β) : ℝ) : 𝕜))) 0 := by
    apply continuousAt_pi.mpr
    intro i
    apply continuousAt_pi.mpr
    intro j
    by_cases hij : i = j
    · subst j
      simpa only [Matrix.diagonal_apply_eq] using hscalar i
    · simpa only [Matrix.diagonal_apply_ne _ hij] using
        (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : 𝕜)) 0)
  have hmul : Continuous (fun M : Matrix (Fin A.rank) (Fin A.rank) 𝕜 => V * M * Uᴴ) := by
    fun_prop
  have hcont : ContinuousAt F 0 := hmul.continuousAt.comp hdiag
  have hF0 : F 0 = pinv A := by
    rw [h.pinv_eq]
    dsimp [F]
    apply congrArg (fun D => V * D * Uᴴ)
    apply congrArg Matrix.diagonal
    funext i
    rw [add_zero]
    congr 1
    rw [sq, div_mul_eq_div_div,
      div_self (ne_of_gt ((singularValues_pos_iff A).mpr i.isLt)), one_div]
  have heq : (fun β => tikhonovInverse A (1 : Matrix n n 𝕜) β) =ᶠ[𝓝[>] 0] F := by
    filter_upwards [self_mem_nhdsWithin] with β hβ
    exact h.tikhonovInverse_one_eq hβ
  rw [← hF0]
  exact (hcont.tendsto.mono_left inf_le_left).congr' heq.symm

/-- **Vanishing-parameter Tikhonov solutions.** For every rectangular matrix $\mathbf{A}$
over $\Bbbk$ and fixed data $\mathbf{b}$, the identity-penalty regularized solution converges
in Euclidean norm to $\mathbf{A}^{+}\mathbf{b}$ as $\beta \downarrow 0$. No rank or
consistency hypothesis is needed. [FesslerNadakuditi2024, §5.6.5, equations (5.44)–(5.48)].
Result: tikhonov-spectral-filter -/
theorem tendsto_tikhonovInverse_one_mulVec_zero (A : Matrix m n 𝕜) (b : m → 𝕜) :
    Tendsto (fun β : ℝ =>
      (WithLp.toLp 2 (tikhonovInverse A (1 : Matrix n n 𝕜) β *ᵥ b) : EuclideanSpace 𝕜 n))
      (𝓝[>] 0) (𝓝 (WithLp.toLp 2 (pinv A *ᵥ b))) := by
  have hc : Continuous (fun M : Matrix n m 𝕜 =>
      (WithLp.toLp 2 (M *ᵥ b) : EuclideanSpace 𝕜 n)) := by fun_prop
  exact hc.continuousAt.tendsto.comp (tendsto_tikhonovInverse_one_zero A)

end NLAlib
