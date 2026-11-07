/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.AlgebraMap
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.Normal

/-!
# Polynomials of a diagonalised matrix (scaffold)

Additions to `NLAlib/Matrix/Spectral/Diagonalizable.lean` (stage SHIFTED-QR, wave W0, design note
`docs/design/Eigensolvers-ShiftedQR.md` §3.3): with $\mathbf{H}\mathbf{V} = \mathbf{V}
\operatorname{diag}(\mathbf{d})$ and $\mathbf{V}$ invertible, polynomials of $\mathbf{H}$, their
inverses and powers are $\mathbf{V}\operatorname{diag}(\cdot)\mathbf{V}^{-1}$; a normal matrix is
diagonalised by a matrix of condition number $1$.

## Main results

* `NLAlib.aeval_eq_mul_diagonal_mul_inv`, `NLAlib.inv_aeval_eq_mul_diagonal_mul_inv`,
  `NLAlib.mul_diagonal_mul_inv_pow`.
* `IsStarNormal.exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_eq_one`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **A polynomial of a diagonalised matrix**: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible, then for every
polynomial $p$, $p(\mathbf{H}) = \mathbf{V}\operatorname{diag}(p(\mathbf{d}_i))\mathbf{V}^{-1}$.
Proof: $\mathbf{H} = \mathbf{V}\operatorname{diag}(\mathbf{d})\mathbf{V}^{-1}$, and
$\mathbf{X} \mapsto \mathbf{V}\mathbf{X}\mathbf{V}^{-1}$ is an algebra automorphism
(`Matrix.mul_nonsing_inv`, `Polynomial.aeval_algEquiv` for the conjugation, then
`Polynomial.induction_on` on the diagonal side, `Matrix.diagonal_mul_diagonal`).
S, about 15 lines. -/
theorem aeval_eq_mul_diagonal_mul_inv {H V : Matrix ι ι ℂ} {d : ι → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (p : Polynomial ℂ) :
    Polynomial.aeval H p = V * Matrix.diagonal (fun i => p.eval (d i)) * V⁻¹ := by
  have hdet := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hVi : V * V⁻¹ = 1 := Matrix.mul_nonsing_inv V hdet
  have hiV : V⁻¹ * V = 1 := Matrix.nonsing_inv_mul V hdet
  have key : ∀ X : Matrix ι ι ℂ, V⁻¹ * (V * X) = X := fun X => by
    rw [← mul_assoc, hiV, one_mul]
  have hH : H = V * Matrix.diagonal d * V⁻¹ := by
    calc H = H * (V * V⁻¹) := by rw [hVi, mul_one]
      _ = (H * V) * V⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [hHV]
  have hpow : ∀ e : ℕ, (V * Matrix.diagonal d * V⁻¹) ^ e
      = V * Matrix.diagonal (d ^ e) * V⁻¹ := by
    intro e
    induction e with
    | zero => rw [pow_zero, pow_zero, Pi.one_def, Matrix.diagonal_one, mul_one, hVi]
    | succ n ih =>
      rw [pow_succ, ih]
      simp only [mul_assoc]
      rw [key, ← mul_assoc (Matrix.diagonal (d ^ n)), Matrix.diagonal_mul_diagonal, pow_succ]
      rfl
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hf : (fun i => (p + q).eval (d i))
        = fun i => p.eval (d i) + q.eval (d i) := by
      funext i; simp
    rw [map_add, hp, hq, hf, ← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]
  | monomial n a =>
    have hf : (fun i => (Polynomial.monomial n a).eval (d i)) = a • (d ^ n) := by
      funext i; simp [Polynomial.eval_monomial]
    rw [Polynomial.aeval_monomial, hH, Algebra.algebraMap_eq_smul_one, Matrix.smul_mul, one_mul,
      hpow, hf, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul]

/-- **The inverse of a polynomial of a diagonalised matrix**: if $\mathbf{H}\mathbf{V} =
\mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible and $p(\mathbf{d}_i) \ne
0$ for all $i$, then $p(\mathbf{H})^{-1} = \mathbf{V}\operatorname{diag}(p(\mathbf{d}_i)^{-1})
\mathbf{V}^{-1}$.
Proof: `NLAlib.aeval_eq_mul_diagonal_mul_inv`, then `Matrix.inv_eq_left_inv` with the product of
the two diagonals (`Matrix.diagonal_mul_diagonal`, `mul_inv_cancel₀`). S, about 12 lines. -/
theorem inv_aeval_eq_mul_diagonal_mul_inv {H V : Matrix ι ι ℂ} {d : ι → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) {p : Polynomial ℂ} (hp : ∀ i, p.eval (d i) ≠ 0) :
    (Polynomial.aeval H p)⁻¹ = V * Matrix.diagonal (fun i => (p.eval (d i))⁻¹) * V⁻¹ := by
  sorry

/-- **Powers of a diagonalised matrix**: for invertible $\mathbf{V}$,
$(\mathbf{V}\operatorname{diag}(\mathbf{g})\mathbf{V}^{-1})^e =
\mathbf{V}\operatorname{diag}(\mathbf{g}^e)\mathbf{V}^{-1}$.
Proof: induction on $e$ (`pow_succ`, `Matrix.nonsing_inv_mul`, `Matrix.diagonal_mul_diagonal`).
S, about 10 lines. -/
theorem mul_diagonal_mul_inv_pow {V : Matrix ι ι ℂ} (hV : IsUnit V) (g : ι → ℂ) (e : ℕ) :
    (V * Matrix.diagonal g * V⁻¹) ^ e = V * Matrix.diagonal (g ^ e) * V⁻¹ := by
  sorry

/-- **A normal matrix has a perfectly conditioned eigenvector matrix**: a normal complex matrix
$\mathbf{H}$ has $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with
$\mathbf{V}$ unitary, so $\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2 = 1$ ($\kappa_V(\mathbf{H}) = 1$).
[HornJohnson2013, Theorem 2.5.3].
Proof: `NLAlib.isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose` gives a unitary
$\mathbf{U}$; `NLAlib.pseudoConditionNumber_of_isUnit` and the norm of a unitary matrix, which
is $1$ for nonempty $\iota$ (the empty case has norm $0$, hence the hypothesis).
S, about 15 lines. -/
theorem _root_.IsStarNormal.exists_isUnit_mul_eq_mul_diagonal_and_pseudoConditionNumber_eq_one
    [Nonempty ι] {H : Matrix ι ι ℂ} (hH : IsStarNormal H) :
    ∃ (V : Matrix ι ι ℂ) (d : ι → ℂ), IsUnit V ∧ H * V = V * Matrix.diagonal d ∧
      pseudoConditionNumber V = 1 := by
  sorry

end NLAlib
