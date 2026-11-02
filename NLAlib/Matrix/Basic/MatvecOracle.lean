/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Spectral

/-!
# Matrix-vector oracles with bounded error

`NLAlib.MatvecOracle A` is a total approximate action of a fixed matrix, with a nonnegative
relative tolerance. Its output need not be linear in the input. The error contract is
$\|\mathbf{A}\mathbf{x} - f(\mathbf{x})\| \le
\varepsilon\|\mathbf{A}\|_2\|\mathbf{x}\|$ for every vector.
This is mathematical data for an analysis, not a certificate about encoded execution.

## Main definitions

* `NLAlib.MatvecOracle`: the action and its accuracy certificate.
* `NLAlib.MatvecOracle.ofMatrix`: exact multiplication, with zero tolerance.

## Main results

* `NLAlib.MatvecOracle.mulVec_zero`: zero is mapped to zero.
* `NLAlib.MatvecOracle.mulVec_eq_of_ε_eq_zero`: zero tolerance gives exact multiplication.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A total approximate matrix-vector action for $\mathbf{A}$ over $\Bbbk$, with
$\|\mathbf{A}\mathbf{x} - f(\mathbf{x})\| \le
\varepsilon\|\mathbf{A}\|_2\|\mathbf{x}\|$ for every input. The action is not assumed linear.
The structure constructor accepts the raw action, tolerance and error certificate. -/
structure MatvecOracle {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n 𝕜) where
  /-- The returned vector for each input. -/
  mulVec : (n → 𝕜) → m → 𝕜
  /-- The relative error tolerance. -/
  ε : ℝ
  /-- The tolerance is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- The error is bounded relative to the matrix norm and the input norm. -/
  norm_sub_mulVec_le : ∀ x,
    ‖WithLp.toLp 2 (A *ᵥ x - mulVec x)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 x‖

namespace MatvecOracle

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n]
  {A : Matrix m n 𝕜}

/-- Exact multiplication by $\mathbf{A}$, with zero error tolerance. -/
noncomputable def ofMatrix (A : Matrix m n 𝕜) : MatvecOracle A where
  mulVec := A.mulVec
  ε := 0
  ε_nonneg := le_rfl
  norm_sub_mulVec_le := fun x => by
    simp only [sub_self, WithLp.toLp_zero, norm_zero, zero_mul, le_refl]

/-- The exact oracle returns the ordinary matrix-vector product. -/
@[simp] theorem mulVec_ofMatrix (A : Matrix m n 𝕜) (x : n → 𝕜) :
    (ofMatrix A).mulVec x = A *ᵥ x := rfl

/-- The exact oracle has zero tolerance. -/
@[simp] theorem ε_ofMatrix (A : Matrix m n 𝕜) : (ofMatrix A).ε = 0 := rfl

/-- Every certified oracle maps the zero vector to zero, even at nonzero tolerance. -/
@[simp] theorem mulVec_zero (O : MatvecOracle A) : O.mulVec 0 = 0 := by
  have h := O.norm_sub_mulVec_le 0
  simp only [Matrix.mulVec_zero, zero_sub, WithLp.toLp_neg, norm_neg,
    WithLp.toLp_zero, norm_zero, mul_zero] at h
  have hzero := norm_eq_zero.mp (le_antisymm h (norm_nonneg _))
  exact congrArg WithLp.ofLp hzero

/-- At zero tolerance the action agrees with multiplication by the reference matrix. -/
theorem mulVec_eq_of_ε_eq_zero (O : MatvecOracle A) (hε : O.ε = 0) (x : n → 𝕜) :
    O.mulVec x = A *ᵥ x := by
  have h := O.norm_sub_mulVec_le x
  rw [hε, zero_mul, zero_mul] at h
  have hzero := congrArg WithLp.ofLp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))
  exact (sub_eq_zero.mp hzero).symm

end MatvecOracle

end NLAlib
