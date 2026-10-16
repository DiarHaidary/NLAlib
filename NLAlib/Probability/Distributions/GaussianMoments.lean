/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.QuadraticForm.Moments

/-!
# Fourth moments of Gaussian linear images

Fourth-order Wick identities and moments of linear images of standard Gaussian vectors.

## Main results

* `NLAlib.integral_dotProduct_mul_four_of_hasLaw_gaussianVector`.
* `NLAlib.integral_norm_mulVec_pow_four_of_hasLaw_gaussianVector`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {n m : Type*} [Fintype n] [Fintype m] {g : Ω → n → ℝ}

private theorem memLp_linear (hg : HasLaw g (gaussianVector n) μ) (u : n → ℝ) :
    MemLp (fun ω => u ⬝ᵥ g ω) 4 μ :=
  ((hasLaw_dotProduct_of_hasLaw_gaussianVector hg u).memLp_comp_iff
    (f := id) aestronglyMeasurable_id).2 (memLp_id_gaussianReal' 4 (by norm_num))

private theorem memLp_pair (hg : HasLaw g (gaussianVector n) μ) (u v : n → ℝ) :
    MemLp (fun ω => (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω)) 2 μ := by
  have : ENNReal.HolderTriple 4 4 2 := ⟨by
    rw [show (4 : ℝ≥0∞) = 2 * 2 by norm_num, ENNReal.mul_inv (by simp) (by simp),
      ← two_mul, ← mul_assoc, ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]⟩
  exact (memLp_linear hg v).mul' (memLp_linear hg u)

/-- Products of four Gaussian linear forms are integrable, including degenerate forms. -/
theorem integrable_dotProduct_mul_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (u v w z : n → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) *
      (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω)) μ := by
  exact ((memLp_pair hg u v).integrable_mul (memLp_pair hg w z)).congr
    (ae_of_all _ fun ω => by dsimp only [Pi.mul_apply]; ring)

private theorem integral_linear_four (hg : HasLaw g (gaussianVector n) μ) (u : n → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) ^ 4 ∂μ = 3 * (u ⬝ᵥ u) ^ 2 := by
  rw [integral_pow_four_of_hasLaw_gaussianReal
    (hasLaw_dotProduct_of_hasLaw_gaussianVector hg u), NNReal.coe_pow, coe_nnnorm,
    EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]

private theorem integrable_linear_four (hg : HasLaw g (gaussianVector n) μ) (u : n → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) ^ 4) μ := by
  exact (integrable_dotProduct_mul_four_of_hasLaw_gaussianVector hg u u u u).congr
    (ae_of_all _ fun ω => by dsimp only [Pi.mul_apply]; ring)

private theorem integral_pair_sq (hg : HasLaw g (gaussianVector n) μ) (u v : n → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) ^ 2 * (v ⬝ᵥ g ω) ^ 2 ∂μ =
      (u ⬝ᵥ u) * (v ⬝ᵥ v) + 2 * (u ⬝ᵥ v) ^ 2 := by
  have he : ∀ ω, 12 * ((u ⬝ᵥ g ω) ^ 2 * (v ⬝ᵥ g ω) ^ 2) =
      ((u + v) ⬝ᵥ g ω) ^ 4 + ((u - v) ⬝ᵥ g ω) ^ 4 -
        2 * (u ⬝ᵥ g ω) ^ 4 - 2 * (v ⬝ᵥ g ω) ^ 4 := by
    intro ω
    rw [add_dotProduct, sub_dotProduct]
    ring
  have hi := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) (funext he)
  simp only [integral_const_mul] at hi
  have h1 := integral_sub ((integrable_linear_four hg (u + v)).add
    (integrable_linear_four hg (u - v)) |>.sub ((integrable_linear_four hg u).const_mul 2))
    ((integrable_linear_four hg v).const_mul 2)
  have h2 := integral_sub
    ((integrable_linear_four hg (u + v)).add (integrable_linear_four hg (u - v)))
    ((integrable_linear_four hg u).const_mul 2)
  have h3 := integral_add (integrable_linear_four hg (u + v)) (integrable_linear_four hg (u - v))
  simp only [Pi.sub_apply, Pi.add_apply] at h1 h2 h3
  rw [h1, h2, h3] at hi
  simp only [integral_const_mul] at hi
  rw [integral_linear_four hg (u + v), integral_linear_four hg (u - v),
    integral_linear_four hg u, integral_linear_four hg v] at hi
  simp only [add_dotProduct, dotProduct_add,
    sub_dotProduct, dotProduct_sub, dotProduct_comm v u] at hi
  linarith

private theorem integrable_pair_sq (hg : HasLaw g (gaussianVector n) μ) (u v : n → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) ^ 2 * (v ⬝ᵥ g ω) ^ 2) μ := by
  exact (integrable_dotProduct_mul_four_of_hasLaw_gaussianVector hg u u v v).congr
    (ae_of_all _ fun ω => by ring)

/-- **Fourth-order Wick formula.** Four linear forms of a standard Gaussian vector have
fourth mixed moment equal to the sum of the three covariance pairings:
$$\begin{aligned}
\mathbb{E}[\langle\mathbf{u},\mathbf{g}\rangle
\langle\mathbf{v},\mathbf{g}\rangle\langle\mathbf{w},\mathbf{g}\rangle
\langle\mathbf{z},\mathbf{g}\rangle]
&= \langle\mathbf{u},\mathbf{v}\rangle\langle\mathbf{w},\mathbf{z}\rangle \\
&\quad+\langle\mathbf{u},\mathbf{w}\rangle\langle\mathbf{v},\mathbf{z}\rangle
+\langle\mathbf{u},\mathbf{z}\rangle\langle\mathbf{v},\mathbf{w}\rangle\,.
\end{aligned}$$
[Isserlis1918, fourth-order formula]; here linear forms with possibly singular covariance.
Result: gaussian-fourth-moment -/
theorem integral_dotProduct_mul_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (u v w z : n → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) * (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω) ∂μ =
      (u ⬝ᵥ v) * (w ⬝ᵥ z) + (u ⬝ᵥ w) * (v ⬝ᵥ z) +
        (u ⬝ᵥ z) * (v ⬝ᵥ w) := by
  let F (a b : n → ℝ) : Ω → ℝ := fun ω => (a ⬝ᵥ g ω) ^ 2 * (b ⬝ᵥ g ω) ^ 2
  have hF (a b : n → ℝ) : Integrable (F a b) μ := integrable_pair_sq hg a b
  have he : (fun ω => 16 * ((u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) *
      (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω))) =
      F (u + v) (w + z) - F (u - v) (w + z) -
        F (u + v) (w - z) + F (u - v) (w - z) := by
    funext ω
    dsimp only [F, Pi.sub_apply, Pi.add_apply]
    simp only [add_dotProduct, sub_dotProduct]
    ring
  have hi := congrArg (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) he
  rw [integral_const_mul] at hi
  have h1 := integral_add
    (((hF (u + v) (w + z)).sub (hF (u - v) (w + z))).sub (hF (u + v) (w - z)))
    (hF (u - v) (w - z))
  have h2 := integral_sub ((hF (u + v) (w + z)).sub (hF (u - v) (w + z)))
    (hF (u + v) (w - z))
  have h3 := integral_sub (hF (u + v) (w + z)) (hF (u - v) (w + z))
  simp only [Pi.sub_apply, Pi.add_apply] at hi h1 h2 h3
  rw [h1, h2, h3] at hi
  dsimp only [F] at hi
  rw [integral_pair_sq hg, integral_pair_sq hg, integral_pair_sq hg, integral_pair_sq hg] at hi
  simp only [add_dotProduct, sub_dotProduct, dotProduct_add,
    dotProduct_sub] at hi
  simp only [dotProduct_comm v u, dotProduct_comm z w] at hi
  linarith

private theorem memLp_gaussian_coordinate (hg : HasLaw g (gaussianVector n) μ) (i : n) :
    MemLp (fun ω => g ω i) 4 μ :=
  ((hg.eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
    (memLp_id_gaussianReal' 4 (by norm_num))

/-- The fourth power of the Euclidean norm of a Gaussian linear image is integrable. -/
theorem integrable_norm_mulVec_pow_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix m n ℝ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4) μ := by
  have hq := memLp_quadForm (memLp_gaussian_coordinate hg) (Aᴴ * A)
  exact (hq.integrable_mul hq).congr (ae_of_all _ fun ω => by
    dsimp only [Pi.mul_apply]
    rw [quadForm_conjTranspose_mul_self]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring)

/-- **The fourth moment of a Gaussian linear image** is
$\mathbb{E}\|\mathbf{A}\mathbf{g}\|^4 =
\|\mathbf{A}\|_{\mathsf{F}}^4 + 2\|\mathbf{A}^{\mathsf{H}}\mathbf{A}\|_{\mathsf{F}}^2$.
[Isserlis1918, fourth-order formula]; the norm contraction of that identity. -/
theorem integral_norm_mulVec_pow_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix m n ℝ) :
    ∫ ω, ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4 ∂μ =
      frobNorm A ^ 4 + 2 * frobNorm (Aᴴ * A) ^ 2 := by
  classical
  have : IsProbabilityMeasure μ := hg.isProbabilityMeasure
  have hq := memLp_quadForm (memLp_gaussian_coordinate hg) (Aᴴ * A)
  have hmean := (isIsotropic_of_hasLaw_gaussianVector hg).integral_quadForm (Aᴴ * A)
  have hvar := variance_quadForm_of_hasLaw_gaussianVector hg
    (Matrix.isHermitian_conjTranspose_mul_self A)
  rw [variance_eq_sub hq] at hvar
  simp only [Pi.pow_apply] at hvar
  rw [hmean] at hvar
  have ht : (Aᴴ * A).trace = frobNorm A ^ 2 := by
    simpa only [RCLike.re_to_real] using (frobNorm_sq_eq_re_trace A).symm
  have he : (fun ω => quadForm (Aᴴ * A) (g ω) ^ 2) =
      (fun ω => ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4) := by
    funext ω
    rw [quadForm_conjTranspose_mul_self]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    ring
  rw [he, ht] at hvar
  nlinarith [hvar]

end NLAlib
