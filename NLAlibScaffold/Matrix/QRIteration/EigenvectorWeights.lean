/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.QRIteration.EigenvectorWeights

/-!
# The approximate functional calculus (scaffold)

Statements for `NLAlib/Matrix/QRIteration/EigenvectorWeights.lean` (stage SHIFTED-QR, wave W0,
design note `docs/design/Eigensolvers-ShiftedQR.md` §3.3): the last-row weights of an invertible
$\mathbf{V}$ are a probability vector, and for every $\mathbf{g}$ the last row of
$\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}$ and the weighted second moment of
$\mathbf{g}$ agree up to the factor $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$ in each direction
([BanksGarzaVargasSrivastava2021, Lemma 4.2], with $f(\mathbf{H}) =
\mathbf{V}f(\mathbf{D})\mathbf{V}^{-1}$).

## Main results

* `NLAlib.sum_lastRowWeights`, `NLAlib.lastRowWeights_nonneg`.
* `NLAlib.sum_lastRowWeights_mul_sq_le`, `NLAlib.norm_mul_diagonal_mul_inv_last_sq_le`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **The last-row weights are nonnegative**. Proof: a quotient of squares
(`div_nonneg`, `sq_nonneg`). S, about 2 lines. -/
theorem lastRowWeights_nonneg (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    0 ≤ lastRowWeights V i := by
  unfold lastRowWeights
  positivity

/-- **The last-row weights of an invertible matrix sum to one**: for invertible $\mathbf{V}$,
$\sum_i \lvert\mathbf{V}_{n,i}\rvert^2 / \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2 = 1$.
Proof: the last row is nonzero (`Matrix.IsUnit` gives an injective `Matrix.vecMul`), and
`EuclideanSpace.norm_sq_eq` with `Finset.sum_div`. S, about 10 lines. -/
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
Lemma 4.2], the right inequality.
Proof: the left side is $\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})\|^2
/ \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2$; write $\mathbf{e}_n^{\mathsf{H}}\mathbf{V}
\operatorname{diag}(\mathbf{g}) =
(\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})
\mathbf{V}^{-1})\mathbf{V}$ and bound by $\|\mathbf{V}\|_2$ (`NLAlib.norm_toLp_mulVec_le` for
$\mathbf{V}^{\mathsf{T}}$, whose norm is $\|\mathbf{V}\|_2$), and
$1 = \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\mathbf{V}^{-1}\| \le
\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|\,\|\mathbf{V}^{-1}\|_2$;
`NLAlib.pseudoConditionNumber_of_isUnit`. M, about 35 lines. -/
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
[BanksGarzaVargasSrivastava2021, Lemma 4.2], the left inequality.
Proof: $\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1}\| \le
\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\operatorname{diag}(\mathbf{g})\|\,\|\mathbf{V}^{-1}\|_2$ and
$\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\| \le \|\mathbf{V}\|_2$ (a row of $\mathbf{V}$).
M, about 30 lines. -/
theorem norm_mul_diagonal_mul_inv_last_sq_le {V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hV : IsUnit V) (g : Fin (n + 1) → ℂ) :
    ‖WithLp.toLp 2 ((V * Matrix.diagonal g * V⁻¹) (Fin.last n))‖ ^ 2 ≤
      pseudoConditionNumber V ^ 2 * ∑ i, lastRowWeights V i * ‖g i‖ ^ 2 := by
  sorry

end NLAlib
