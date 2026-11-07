/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Complex.Basic
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber

/-!
# Last-row weights of an eigenvector matrix

For an invertible eigenvector matrix $\mathbf{V}$ of a diagonalizable $\mathbf{H}$, the weights
$$w_i = \frac{\lvert\mathbf{V}_{n,i}\rvert^2}{\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2}$$
form a probability vector on the eigenvalues. Sums against them are the "approximate functional
calculus" of [BanksGarzaVargasSrivastava2021, Definition 4.1]: the law of the random variable
$Z_{\mathbf{H}}$ there, written as finite weighted sums here. For normal $\mathbf{H}$ and unitary
$\mathbf{V}$ it is the spectral measure of $\mathbf{H}$ at $\mathbf{e}_n$.

## Main definitions

* `NLAlib.lastRowWeights`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The **last-row weights** of a square matrix $\mathbf{V}$:
$w_i = \lvert\mathbf{V}_{n,i}\rvert^2 / \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2$, the squared
moduli of the last row normalised to sum to $1$ (all $0$ if the last row vanishes, which an
invertible $\mathbf{V}$ excludes). With $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$, the weight $w_i$ sits on the eigenvalue $\mathbf{d}_i$: this is the distribution of
$Z_{\mathbf{H}}$ in [BanksGarzaVargasSrivastava2021, Definition 4.1], where $\mathbf{V}$ is
normalised by $\|\mathbf{V}\|_2 = \|\mathbf{V}^{-1}\|_2$, which no statement here needs. -/
noncomputable def lastRowWeights (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    ℝ :=
  ‖V (Fin.last n) i‖ ^ 2 / ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2

/-- **The last-row weights are nonnegative**. -/
theorem lastRowWeights_nonneg (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    0 ≤ lastRowWeights V i := by
  unfold lastRowWeights
  positivity

/-- **The last-row weights of an invertible matrix sum to one**: for invertible $\mathbf{V}$,
$\sum_i \lvert\mathbf{V}_{n,i}\rvert^2 / \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2 = 1$. -/
theorem sum_lastRowWeights {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hV : IsUnit V) :
    ∑ i, lastRowWeights V i = 1 := by
  have hrow : V (Fin.last n) ≠ 0 := by
    intro h
    have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
    rw [Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) (fun j => congrFun h j)] at hdet
    exact not_isUnit_zero hdet
  have hne : ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 ≠ 0 := by
    have : WithLp.toLp 2 (V (Fin.last n)) ≠ 0 := by
      intro h
      apply hrow
      simpa using congrArg WithLp.ofLp h
    have := norm_ne_zero_iff.mpr this
    positivity
  unfold lastRowWeights
  have hsum : ∑ i, ‖V (Fin.last n) i‖ ^ 2 = ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_div, hsum, div_self hne]

/-- **Approximate functional calculus, upper bound on the moment**: for invertible $\mathbf{V}$
with last-row weights $w$ and every $\mathbf{g}$,
$$\sum_i w_i\lvert\mathbf{g}_i\rvert^2 \le \bigl(\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\bigr)^2\,
\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}\|^2\,.$$
With $\mathbf{H} = \mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$ and
$\mathbf{g} = f(\mathbf{d})$: $\mathbb{E}\lvert f(Z_{\mathbf{H}})\rvert^2 \le
\kappa_V^2\|\mathbf{e}_n^{\mathsf{H}}f(\mathbf{H})\|^2$. [BanksGarzaVargasSrivastava2021,
Lemma 4.2], the right inequality. -/
theorem sum_lastRowWeights_mul_sq_le {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hV : IsUnit V)
    (g : Fin (n + 1) → ℂ) :
    ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 ≤
      pseudoConditionNumber V ^ 2 *
        ‖WithLp.toLp 2 ((V * Matrix.diagonal g * V⁻¹) (Fin.last n))‖ ^ 2 := by
  have vm : ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u : Fin (n + 1) → ℂ),
      ‖WithLp.toLp 2 (u ᵥ* A)‖ ≤ specNorm A * ‖WithLp.toLp 2 u‖ := by
    intro A u
    have h := norm_toLp_mulVec_le Aᵀ u
    rwa [specNorm_transpose, Matrix.mulVec_transpose] at h
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hinv : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  have hinv' : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hdet
  have hrow : V (Fin.last n) ≠ 0 := by
    intro h
    rw [Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) (fun j => congrFun h j)] at hdet
    exact not_isUnit_zero hdet
  have hD : ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 ≠ 0 := by
    have : WithLp.toLp 2 (V (Fin.last n)) ≠ 0 := by
      intro h; apply hrow; simpa using congrArg WithLp.ofLp h
    have := norm_ne_zero_iff.mpr this
    positivity
  set D := ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 with hDdef
  set T := ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 with hTdef
  have hT : 0 ≤ T :=
    Finset.sum_nonneg fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (sq_nonneg _)
  -- the last row of `V` is `e ᵥ* V`
  set e : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1 with he_def
  have hr : e ᵥ* V = V (Fin.last n) := by
    ext j; simp [he_def, Matrix.vecMul, dotProduct, Pi.single_apply]
  have he1 : ‖WithLp.toLp 2 e‖ = 1 := by simp [he_def]
  set y : Fin (n + 1) → ℂ := fun k => V (Fin.last n) k * g k with hy_def
  have hrowW : (V * Matrix.diagonal g * V⁻¹) (Fin.last n) = y ᵥ* V⁻¹ := by
    ext j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, hy_def,
      mul_assoc]
  have hS : ‖WithLp.toLp 2 y‖ ^ 2 = D * T := by
    rw [EuclideanSpace.norm_sq_eq, hDdef, hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold lastRowWeights
    have hn : ‖WithLp.toLp 2 (V (Fin.last n))‖ ≠ 0 := fun h => hD (by rw [hDdef, h]; ring)
    simp [hy_def, mul_pow]
    field_simp
  have hyV : (y ᵥ* V⁻¹) ᵥ* V = y := by rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  have hsq : ‖WithLp.toLp 2 y‖ ^ 2 ≤
      specNorm V ^ 2 * ‖WithLp.toLp 2 ((V * Matrix.diagonal g * V⁻¹) (Fin.last n))‖ ^ 2 := by
    rw [hrowW, ← mul_pow]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
    have := vm V (y ᵥ* V⁻¹)
    rwa [hyV] at this
  have hone : (1 : ℝ) ≤ specNorm V⁻¹ ^ 2 * D := by
    have h := vm V⁻¹ (V (Fin.last n))
    have hrV : (V (Fin.last n)) ᵥ* V⁻¹ = e := by
      rw [← hr, Matrix.vecMul_vecMul, hinv', Matrix.vecMul_one]
    rw [hrV, he1] at h
    have := pow_le_pow_left₀ zero_le_one h 2
    rw [mul_pow, one_pow] at this
    exact this
  rw [pseudoConditionNumber_of_isUnit hV, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hone hT,
    mul_le_mul_of_nonneg_left hsq (sq_nonneg (specNorm V⁻¹))]

/-- **Approximate functional calculus, lower bound on the moment**: for invertible $\mathbf{V}$
with last-row weights $w$ and every $\mathbf{g}$,
$$\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}\|^2 \le
\bigl(\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2\bigr)^2 \sum_i w_i\lvert\mathbf{g}_i\rvert^2\,.$$
[BanksGarzaVargasSrivastava2021, Lemma 4.2], the left inequality. -/
theorem norm_mul_diagonal_mul_inv_last_sq_le {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hV : IsUnit V) (g : Fin (n + 1) → ℂ) :
    ‖WithLp.toLp 2 ((V * Matrix.diagonal g * V⁻¹) (Fin.last n))‖ ^ 2 ≤
      pseudoConditionNumber V ^ 2 * ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 := by
  have vm : ∀ (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (u : Fin (n + 1) → ℂ),
      ‖WithLp.toLp 2 (u ᵥ* A)‖ ≤ specNorm A * ‖WithLp.toLp 2 u‖ := by
    intro A u
    have h := norm_toLp_mulVec_le Aᵀ u
    rwa [specNorm_transpose, Matrix.mulVec_transpose] at h
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hrow : V (Fin.last n) ≠ 0 := by
    intro h
    rw [Matrix.det_eq_zero_of_row_eq_zero (Fin.last n) (fun j => congrFun h j)] at hdet
    exact not_isUnit_zero hdet
  have hD : ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 ≠ 0 := by
    have : WithLp.toLp 2 (V (Fin.last n)) ≠ 0 := by
      intro h; apply hrow; simpa using congrArg WithLp.ofLp h
    have := norm_ne_zero_iff.mpr this
    positivity
  set D := ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2 with hDdef
  set T := ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 with hTdef
  have hT : 0 ≤ T :=
    Finset.sum_nonneg fun i _ => mul_nonneg (lastRowWeights_nonneg V i) (sq_nonneg _)
  set e : Fin (n + 1) → ℂ := Pi.single (Fin.last n) 1 with he_def
  have hr : e ᵥ* V = V (Fin.last n) := by
    ext j; simp [he_def, Matrix.vecMul, dotProduct, Pi.single_apply]
  have he1 : ‖WithLp.toLp 2 e‖ = 1 := by simp [he_def]
  have hrowle : ‖WithLp.toLp 2 (V (Fin.last n))‖ ≤ specNorm V := by
    have h := vm V e
    rwa [hr, he1, mul_one] at h
  have hDle : D ≤ specNorm V ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hrowle 2
  set y : Fin (n + 1) → ℂ := fun k => V (Fin.last n) k * g k with hy_def
  have hrowW : (V * Matrix.diagonal g * V⁻¹) (Fin.last n) = y ᵥ* V⁻¹ := by
    ext j
    simp [Matrix.mul_apply, Matrix.vecMul, dotProduct, Matrix.diagonal_apply, hy_def,
      mul_assoc]
  have hS : ‖WithLp.toLp 2 y‖ ^ 2 = D * T := by
    rw [EuclideanSpace.norm_sq_eq, hDdef, hTdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold lastRowWeights
    have hn : ‖WithLp.toLp 2 (V (Fin.last n))‖ ≠ 0 := fun h => hD (by rw [hDdef, h]; ring)
    simp [hy_def, mul_pow]
    field_simp
  have hL := vm V⁻¹ y
  rw [← hrowW] at hL
  have hL2 := pow_le_pow_left₀ (norm_nonneg _) hL 2
  rw [mul_pow, hS] at hL2
  rw [pseudoConditionNumber_of_isUnit hV, mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hDle hT)
    (sq_nonneg (specNorm V⁻¹))]

end NLAlib
