/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.HadamardMatrix
public import NLAlib.Matrix.Basic.Orthonormal

/-!
# Bounded orthonormal transforms

A square matrix $\mathbf{F}$ indexed by `n` is a **bounded orthonormal transform** with constant
$\beta$ when it is unitary and its entries are uniformly small,
$\lvert n \rvert \, \lvert \mathbf{F}_{i,j} \rvert^2 \le \beta$. The normalised Walsh–Hadamard and
Fourier matrices, and every Hadamard matrix scaled by $\lvert n \rvert^{-1/2}$, have $\beta = 1$;
the discrete cosine and Hartley transforms have $\beta = 2$. For nonempty `n`, unitarity forces
$1 \le \beta$ (a row has norm $1$). These are the two features of a trigonometric transform that
the analysis of the subsampled randomized trigonometric transform uses
(`NLAlib.Sketching.Structured.Flattening`).

The hypothesis is strictly weaker than Mathlib's `Matrix.IsHadamard` on the unnormalised matrix: an
inequality on the entries admits the cosine and Hartley transforms, which are not Hadamard. The
bridge is `Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul`. Design:
`docs/design/Sketching-S6.md` §8, items 6 and 7.

This file is part of the skeleton of Sketching stage S6 (`docs/design/Sketching-S6.md` §8,
item 15).

## Main definitions

* `NLAlib.IsBoundedOrthonormal`: a unitary with uniformly small entries.

## Main results

* `Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul`: a normalised Hadamard matrix.
* `NLAlib.IsBoundedOrthonormal.transpose`, `NLAlib.IsBoundedOrthonormal.conjTranspose`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n] {F : Matrix n n 𝕜}
  {β : ℝ}

/-- $\mathbf{F}$ is a **bounded orthonormal transform** with constant $\beta$: a unitary
(`NLAlib.HasOrthonormalCols F`, $\mathbf{F}$ square) whose entries satisfy
$\lvert n \rvert \, \lvert \mathbf{F}_{i,j} \rvert^2 \le \beta$. $\beta = 1$ for the normalised
Walsh–Hadamard and Fourier matrices and every normalised Hadamard matrix, $\beta = 2$ for the
discrete cosine and Hartley transforms. For nonempty `n`, $1 \le \beta$. The bounded orthonormal
systems of Foucart and Rauhut's book on compressive sensing, with $K^2 = \beta$;
[CamanoEpperlyMeyerTropp2025, Imported Theorem 4.3] (the two features the flattening of a
randomized transform uses). -/
structure IsBoundedOrthonormal (F : Matrix n n 𝕜) (β : ℝ) : Prop where
  /-- $\mathbf{F}$ is unitary. -/
  hasOrthonormalCols : HasOrthonormalCols F
  /-- Every entry satisfies $\lvert n \rvert \, \lvert \mathbf{F}_{i,j} \rvert^2 \le \beta$. -/
  card_mul_norm_sq_le : ∀ i j, (Fintype.card n : ℝ) * ‖F i j‖ ^ 2 ≤ β

/-- **A normalised Hadamard matrix is a bounded orthonormal transform**: for a Hadamard matrix
$\mathbf{H}$ in the sense of Mathlib's `Matrix.IsHadamard`, $\lvert n \rvert^{-1/2} \mathbf{H}$ is
bounded orthonormal with $\beta = 1$. For empty `n` both fields hold vacuously. -/
theorem _root_.Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul {H : Matrix n n 𝕜}
    (hH : H.IsHadamard) : IsBoundedOrthonormal (((√(Fintype.card n : ℝ))⁻¹ : ℝ) • H) 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨Subsingleton.elim _ _, fun i => isEmptyElim i⟩
  have hc : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  have hs : (√(Fintype.card n : ℝ))⁻¹ * (√(Fintype.card n : ℝ))⁻¹ * (Fintype.card n : ℝ) = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hc.le, inv_mul_cancel₀ hc.ne']
  refine ⟨?_, fun i j => ?_⟩
  · rw [HasOrthonormalCols, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, hH.conjTranspose_mul, smul_smul,
      show ((Fintype.card n : 𝕜)) = (((Fintype.card n : ℝ) : ℝ) : 𝕜) by push_cast; rfl,
      ← RCLike.real_smul_eq_coe_smul, smul_smul, hs, one_smul]
  · rw [Matrix.smul_apply, norm_smul, CStarRing.norm_of_mem_unitary (hH.apply_mem i j), mul_one,
      Real.norm_eq_abs, abs_of_nonneg (by positivity), inv_pow, Real.sq_sqrt hc.le,
      mul_inv_cancel₀ hc.ne']

namespace IsBoundedOrthonormal

/-- The transpose of a bounded orthonormal transform is one, with the same constant. Over
$\mathbb{C}$ this carries a transform acting on the right (Halko, Martinsson and Tropp's test
matrix $\mathbf{D}\mathbf{F}\mathbf{R}$) to the left. -/
theorem transpose (hF : IsBoundedOrthonormal F β) : IsBoundedOrthonormal Fᵀ β := by
  refine ⟨?_, fun i j => hF.card_mul_norm_sq_le j i⟩
  rw [HasOrthonormalCols, Matrix.conjTranspose_transpose_eq_transpose_conjTranspose,
    ← Matrix.transpose_mul, hF.hasOrthonormalCols.mul_conjTranspose_self, Matrix.transpose_one]

/-- The conjugate transpose of a bounded orthonormal transform is one, with the same constant. -/
theorem conjTranspose (hF : IsBoundedOrthonormal F β) : IsBoundedOrthonormal Fᴴ β := by
  refine ⟨?_, fun i j => ?_⟩
  · rw [HasOrthonormalCols, Matrix.conjTranspose_conjTranspose]
    exact hF.hasOrthonormalCols.mul_conjTranspose_self
  · rw [Matrix.conjTranspose_apply, norm_star]
    exact hF.card_mul_norm_sq_le j i

end IsBoundedOrthonormal

end NLAlib
