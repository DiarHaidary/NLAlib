/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.Spectral.Weyl

/-!
# Multiplicative perturbations

Bounds for the singular values, the pseudoinverse and the pseudo-condition number of
$\mathbf{S}\mathbf{A}$ in terms of those of $\mathbf{A}$, when the Gram matrices are comparable in
the Loewner order:
$$a \mathbf{A}^{\mathsf{H}}\mathbf{A}
  \preceq (\mathbf{S}\mathbf{A})^{\mathsf{H}}(\mathbf{S}\mathbf{A})
  \preceq b \mathbf{A}^{\mathsf{H}}\mathbf{A}.$$
This two-sided bound is what a subspace embedding guarantees, and the consequences here are what
sketch-and-precondition and sketched least squares consume.

## Main results

* `NLAlib.mul_singularValues_sq_le_of_smul_le`, `NLAlib.singularValues_sq_le_mul_of_le_smul`:
  singular values under comparable Gram matrices.
* `NLAlib.rank_eq_of_smul_le_of_le_smul`: the rank is preserved.
* `NLAlib.specNorm_pinv_sq_le_of_smul_le`: the pseudoinverse.
* `NLAlib.pseudoConditionNumber_le_sqrt_div_mul_of_smul_le_of_le_smul`: the pseudo-condition number.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- **Singular values under a lower Gram bound.** If
$a \mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq \mathbf{B}^{\mathsf{H}}\mathbf{B}$ for a real $a$, then
$a \sigma_i(\mathbf{A})^2 \le \sigma_i(\mathbf{B})^2$ for every $i$. With
$\mathbf{B} = \mathbf{S}\mathbf{A}$ this is the lower half of a subspace embedding, and the lower
half of Ostrowski's theorem; the upper half for a product is
`NLAlib.singularValues_mul_le_specNorm_mul`.
[HornJohnson2013, Corollary 7.7.4 for the Gram matrices];
[HornJohnson2013, Theorem 4.5.9 (Ostrowski)], for the congruence
$\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{A}$. -/
theorem mul_singularValues_sq_le_of_smul_le {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {a : ℝ}
    (h : a • (Aᴴ * A) ≤ Bᴴ * B) (i : ℕ) :
    a * singularValues A i ^ 2 ≤ singularValues B i ^ 2 := by
  rcases le_or_gt 0 a with ha | ha
  · have hk := eigenvalue_le_eigenvalue_of_le h
      ((Matrix.isHermitian_conjTranspose_mul_self A).smul (IsSelfAdjoint.all a)) i
    rwa [eigenvalue_real_smul _ ha, ← singularValues_sq, ← singularValues_sq] at hk
  · exact (mul_nonpos_of_nonpos_of_nonneg ha.le (sq_nonneg _)).trans (sq_nonneg _)

/-- **Singular values under an upper Gram bound.** If
$\mathbf{B}^{\mathsf{H}}\mathbf{B} \preceq b \mathbf{A}^{\mathsf{H}}\mathbf{A}$ for a real $b$, then
$\sigma_i(\mathbf{B})^2 \le b \sigma_i(\mathbf{A})^2$ for every $i$. -/
theorem singularValues_sq_le_mul_of_le_smul {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {b : ℝ}
    (h : Bᴴ * B ≤ b • (Aᴴ * A)) (i : ℕ) :
    singularValues B i ^ 2 ≤ b * singularValues A i ^ 2 := by
  rcases le_or_gt 0 b with hb | hb
  · have hk := eigenvalue_le_eigenvalue_of_le h (Matrix.isHermitian_conjTranspose_mul_self B) i
    rwa [eigenvalue_real_smul _ hb, ← singularValues_sq, ← singularValues_sq] at hk
  · have hB : 0 ≤ Bᴴ * B := (Matrix.posSemidef_conjTranspose_mul_self B).nonneg
    have hA : 0 ≤ (-b) • (Aᴴ * A) :=
      ((Matrix.posSemidef_conjTranspose_mul_self A).smul (neg_nonneg.mpr hb.le)).nonneg
    rw [neg_smul, neg_nonneg] at hA
    have hB0 : Bᴴ * B = 0 := le_antisymm (h.trans hA) hB
    have hA0 : Aᴴ * A = 0 :=
      (smul_eq_zero.mp (le_antisymm hA (hB.trans h))).resolve_left hb.ne
    rw [Matrix.conjTranspose_mul_self_eq_zero.mp hB0, Matrix.conjTranspose_mul_self_eq_zero.mp hA0,
      singularValues_zero, singularValues_zero, Pi.zero_apply, zero_pow two_ne_zero, mul_zero]

/-- A lower Gram bound with a positive constant does not lose rank: if $0 < a$ and
$a \mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq \mathbf{B}^{\mathsf{H}}\mathbf{B}$, then
$\operatorname{rank} \mathbf{A} \le \operatorname{rank} \mathbf{B}$. -/
theorem rank_le_of_smul_le {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {a : ℝ} (ha : 0 < a)
    (h : a • (Aᴴ * A) ≤ Bᴴ * B) : A.rank ≤ B.rank := by
  refine Nat.le_of_not_gt fun hlt => ?_
  have hA := (singularValues_pos_iff A).mpr hlt
  have hB := (singularValues_eq_zero_iff B).mpr le_rfl
  have h' := mul_singularValues_sq_le_of_smul_le h B.rank
  rw [hB, zero_pow two_ne_zero] at h'
  exact absurd h' (not_le.mpr (mul_pos ha (pow_pos hA 2)))

/-- Comparable Gram matrices have the same rank: if $0 < a$ and
$a \mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq \mathbf{B}^{\mathsf{H}}\mathbf{B}
\preceq b \mathbf{A}^{\mathsf{H}}\mathbf{A}$, then
$\operatorname{rank} \mathbf{B} = \operatorname{rank} \mathbf{A}$. -/
theorem rank_eq_of_smul_le_of_le_smul {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {a b : ℝ}
    (ha : 0 < a) (h₁ : a • (Aᴴ * A) ≤ Bᴴ * B) (h₂ : Bᴴ * B ≤ b • (Aᴴ * A)) :
    B.rank = A.rank := by
  refine le_antisymm (Nat.le_of_not_gt fun hlt => ?_) (rank_le_of_smul_le ha h₁)
  have hB := (singularValues_pos_iff B).mpr hlt
  have hA := (singularValues_eq_zero_iff A).mpr le_rfl
  have h := singularValues_sq_le_mul_of_le_smul h₂ A.rank
  rw [hA, zero_pow two_ne_zero, mul_zero] at h
  exact absurd h (not_le.mpr (pow_pos hB 2))

/-- Under a lower Gram bound the pseudoinverse is controlled:
$\|\mathbf{B}^{+}\|_2^2 \le a^{-1} \|\mathbf{A}^{+}\|_2^2$ when
$a \mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq \mathbf{B}^{\mathsf{H}}\mathbf{B}$, $0 < a$, and the
rank of $\mathbf{B}$ is at most that of $\mathbf{A}$ (the two ranks are then equal). -/
theorem specNorm_pinv_sq_le_of_smul_le {A : Matrix m n 𝕜} {B : Matrix l n 𝕜} {a : ℝ}
    (ha : 0 < a) (h : a • (Aᴴ * A) ≤ Bᴴ * B) (hr : B.rank ≤ A.rank) :
    specNorm (pinv B) ^ 2 ≤ a⁻¹ * specNorm (pinv A) ^ 2 := by
  have hr' : B.rank = A.rank := le_antisymm hr (rank_le_of_smul_le ha h)
  rcases Nat.eq_zero_or_pos A.rank with h0 | h0
  · rw [Matrix.rank_eq_zero.mp h0, Matrix.rank_eq_zero.mp (hr'.trans h0), pinv_zero, pinv_zero,
      specNorm_zero, specNorm_zero, zero_pow two_ne_zero, mul_zero]
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = A.rank := ⟨A.rank - 1, by omega⟩
    have hA := (singularValues_pos_iff A).mpr (by omega : k < A.rank)
    have hle := mul_singularValues_sq_le_of_smul_le h k
    rw [specNorm_pinv A hk, specNorm_pinv B (hk.trans hr'.symm), inv_pow, inv_pow, ← mul_inv]
    exact inv_anti₀ (mul_pos ha (pow_pos hA 2)) hle

/-- **The pseudo-condition number under comparable Gram matrices**: if
$a \mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq \mathbf{B}^{\mathsf{H}}\mathbf{B}
\preceq b \mathbf{A}^{\mathsf{H}}\mathbf{A}$ with $0 < a$, then
$\|\mathbf{B}\|_2 \|\mathbf{B}^{+}\|_2 \le \sqrt{b / a} \, \|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$.
With $\mathbf{B} = \mathbf{S}\mathbf{A}$ this is the conditioning of a sketched matrix. -/
theorem pseudoConditionNumber_le_sqrt_div_mul_of_smul_le_of_le_smul {A : Matrix m n 𝕜}
    {B : Matrix l n 𝕜} {a b : ℝ} (ha : 0 < a) (h₁ : a • (Aᴴ * A) ≤ Bᴴ * B)
    (h₂ : Bᴴ * B ≤ b • (Aᴴ * A)) :
    pseudoConditionNumber B ≤ √(b / a) * pseudoConditionNumber A := by
  rcases Nat.eq_zero_or_pos A.rank with h0 | h0
  · rw [Matrix.rank_eq_zero.mp ((rank_eq_of_smul_le_of_le_smul ha h₁ h₂).trans h0),
      pseudoConditionNumber_zero]
    exact mul_nonneg (Real.sqrt_nonneg _) (pseudoConditionNumber_nonneg A)
  · obtain ⟨k, hk⟩ : ∃ k, k + 1 = A.rank := ⟨A.rank - 1, by omega⟩
    have hr := rank_eq_of_smul_le_of_le_smul ha h₁ h₂
    have hA := (singularValues_pos_iff A).mpr (by omega : k < A.rank)
    have hB := (singularValues_pos_iff B).mpr (by omega : k < B.rank)
    have hlo := mul_singularValues_sq_le_of_smul_le h₁ k
    have hhi := singularValues_sq_le_mul_of_le_smul h₂ 0
    rw [pseudoConditionNumber_eq_singularValues_div A hk,
      pseudoConditionNumber_eq_singularValues_div B (hk.trans hr.symm)]
    rw [← Real.sqrt_sq (div_nonneg (singularValues_nonneg A 0) hA.le),
      ← Real.sqrt_mul' _ (sq_nonneg _)]
    apply Real.le_sqrt_of_sq_le
    rw [div_pow, div_pow, div_mul_div_comm,
      div_le_div_iff₀ (pow_pos hB 2) (mul_pos ha (pow_pos hA 2))]
    exact mul_le_mul hhi hlo (mul_pos ha (pow_pos hA 2)).le ((sq_nonneg _).trans hhi)

/-! ### Deprecated aliases -/

@[deprecated pseudoConditionNumber_le_sqrt_div_mul_of_smul_le_of_le_smul (since := "2026-10-14")]
alias conditionNumber_le_sqrt_div_mul_of_smul_le_of_le_smul :=
  pseudoConditionNumber_le_sqrt_div_mul_of_smul_le_of_le_smul

end NLAlib
