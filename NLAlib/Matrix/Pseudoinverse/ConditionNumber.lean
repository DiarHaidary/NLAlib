/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.NormBounds
public import NLAlib.Matrix.Spectral.LowRank
public import Mathlib.Tactic.Positivity.Core

/-!
# The pseudo-condition number and the distance to singularity

`NLAlib.pseudoConditionNumber A` is $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$, defined for a matrix
of any shape through the Moore–Penrose pseudoinverse: the ratio of the largest singular value of
$\mathbf{A}$ to its smallest *nonzero* one, and $0$ for the zero matrix. It is real-valued.

It is not the classical condition number on singular or rank-deficient matrices, which is
$\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$, infinite as soon as
$\sigma_{\min}(\mathbf{A}) = 0$: a nonzero singular orthogonal projector, such as
$\operatorname{diag}(1, 0)$, has pseudo-condition number $1$. For a matrix of full column rank
the two agree,
$\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2 = \sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$
(`NLAlib.pseudoConditionNumber_of_injective`), and for an invertible matrix it is the classical
$\kappa(\mathbf{A}) = \|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$
(`NLAlib.pseudoConditionNumber_of_isUnit`). A theorem about the classical condition number
therefore states invertibility or full column rank as a hypothesis (`IsUnit A`,
`Function.Injective A.mulVec`), as it would anyway.

The distance from a matrix to the nearest rank-deficient one, in spectral norm, is its smallest
singular value.

The names `conditionNumber` and `conditionNumber_*` are deprecated aliases (2026-10-14).

## Main definitions

* `NLAlib.pseudoConditionNumber`: $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$, that is
  `specNorm A * specNorm (pinv A)`.

## Main results

* `NLAlib.pseudoConditionNumber_eq_singularValues_div`: the ratio of the extreme nonzero singular
  values.
* `NLAlib.pseudoConditionNumber_of_injective`: the classical
  $\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$ at full column rank.
* `NLAlib.one_le_pseudoConditionNumber`: at least one for a nonzero matrix.
* `NLAlib.pseudoConditionNumber_of_isUnit`: the classical formula
  $\|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$.
* `NLAlib.singularValues_last_le_specNorm_of_not_injective_add`,
  `NLAlib.isLeast_specNorm_not_injective_add`: the distance to rank deficiency.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The **pseudo-condition number** $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$, that is
`specNorm A * specNorm (pinv A)`, of a matrix of any shape: the ratio of its largest singular
value to its smallest nonzero singular value, computed through the pseudoinverse, and $0$ for the
zero matrix.

It is not the classical condition number $\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$ on
singular or rank-deficient matrices, where the classical one is infinite: it ignores the zero
singular values, so a nonzero singular orthogonal projector ($\operatorname{diag}(1, 0)$, or any
$\mathbf{P}$ with `IsStarProjection P`, $\mathbf{P} \ne \mathbf{0}$, $\mathbf{P} \ne \mathbf{I}$)
has pseudo-condition number $1$. For a matrix of full column rank it agrees with the classical
one, $\sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$ (`pseudoConditionNumber_of_injective`),
and for an invertible matrix it is the classical
$\kappa(\mathbf{A}) = \|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$ (`pseudoConditionNumber_of_isUnit`);
theorems about the classical condition number assume invertibility or full column rank.
[GolubVanLoan2013, §2.6.2 and §5.3.7]. Port of `NLAlib.moorePenroseConditionNumber`; the
prototype's `ℝ≥0∞`-valued `conditionNumber` of a square matrix is not reproduced. -/
noncomputable def pseudoConditionNumber (A : Matrix m n 𝕜) : ℝ :=
  specNorm A * specNorm (pinv A)

/-- `pseudoConditionNumber A` unfolds to $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$. -/
theorem pseudoConditionNumber_def (A : Matrix m n 𝕜) :
    pseudoConditionNumber A = specNorm A * specNorm (pinv A) :=
  rfl

/-- The pseudo-condition number is nonnegative.
Port of `NLAlib.moorePenroseConditionNumber_nonneg`. -/
theorem pseudoConditionNumber_nonneg (A : Matrix m n 𝕜) : 0 ≤ pseudoConditionNumber A := by
  exact mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)

/-- The pseudo-condition number of the zero matrix is zero.
Port of `NLAlib.moorePenroseConditionNumber_zero`. -/
@[simp]
theorem pseudoConditionNumber_zero : pseudoConditionNumber (0 : Matrix m n 𝕜) = 0 := by
  rw [pseudoConditionNumber, specNorm_zero, zero_mul]

/-- **The pseudo-condition number of a nonzero matrix is at least one:**
$1 \le \|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2$ for $\mathbf{A} \ne \mathbf{0}$.
Port of `NLAlib.one_le_moorePenroseConditionNumber`. -/
theorem one_le_pseudoConditionNumber {A : Matrix m n 𝕜} (hA : A ≠ 0) :
    1 ≤ pseudoConditionNumber A := by
  have hpos : 0 < specNorm A :=
    lt_of_le_of_ne (specNorm_nonneg A) (Ne.symm (mt specNorm_eq_zero_iff.mp hA))
  have hbound : 1 * specNorm A ≤ pseudoConditionNumber A * specNorm A := by
    calc 1 * specNorm A = specNorm (A * pinv A * A) := by rw [one_mul, mul_pinv_mul_self]
      _ ≤ specNorm (A * pinv A) * specNorm A := specNorm_mul_le _ _
      _ ≤ specNorm A * specNorm (pinv A) * specNorm A :=
        mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) (specNorm_nonneg _)
  exact le_of_mul_le_mul_right hbound hpos

/-- **The pseudo-condition number as a ratio of singular values**: for
$k + 1 = \operatorname{rank} \mathbf{A}$,
$\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2 = \sigma_0(\mathbf{A}) / \sigma_k(\mathbf{A})$.
Port of `NLAlib.moorePenroseConditionNumber_eq_singularValues_ratio`. -/
theorem pseudoConditionNumber_eq_singularValues_div (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = A.rank) :
    pseudoConditionNumber A = singularValues A 0 / singularValues A k := by
  rw [pseudoConditionNumber, specNorm_pinv A hk, singularValues_zero_eq_specNorm, div_eq_mul_inv]

/-- **Agreement with the classical condition number at full column rank.** If $\mathbf{A}$ has
full column rank, its pseudo-condition number is the classical
$\kappa(\mathbf{A}) = \sigma_0(\mathbf{A}) / \sigma_{\min}(\mathbf{A})$, written
$\|\mathbf{A}\|_2 / \sigma_k(\mathbf{A})$ with $k + 1 = \lvert n \rvert$.
Port of `NLAlib.moorePenroseConditionNumber_eq_specNorm_div_singularValues_last`. -/
theorem pseudoConditionNumber_of_injective {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec)
    {k : ℕ} (hk : k + 1 = Fintype.card n) :
    pseudoConditionNumber A = specNorm A / singularValues A k := by
  rw [pseudoConditionNumber, specNorm_pinv_of_injective hA hk, div_eq_mul_inv]

/-- For an invertible matrix the pseudo-condition number is the classical condition number
$\kappa(\mathbf{A}) = \|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2$.
Port of `NLAlib.moorePenroseConditionNumber_eq_mul_specNorm_inv`. -/
theorem pseudoConditionNumber_of_isUnit [DecidableEq n] {A : Matrix n n 𝕜} (hA : IsUnit A) :
    pseudoConditionNumber A = specNorm A * specNorm A⁻¹ := by
  rw [pseudoConditionNumber, pinv_of_isUnit hA]

/-- For a positive definite matrix the pseudo-condition number is the ratio of the extreme
eigenvalues: $\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2 = \lambda_0(\mathbf{A}) / \lambda_k(\mathbf{A})$
for $k + 1 = \lvert n \rvert$, eigenvalues non-increasing and indexed from $0$.
Port of `NLAlib.moorePenroseConditionNumber_eq_eigenvalues₀_ratio`, there over $\mathbb{R}$. -/
theorem _root_.Matrix.PosDef.pseudoConditionNumber_eq {A : Matrix n n 𝕜} (hA : A.PosDef) {k : ℕ}
    (hk : k + 1 = Fintype.card n) : pseudoConditionNumber A = eigenvalue A 0 / eigenvalue A k := by
  classical
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hA.isUnit
  rw [pseudoConditionNumber_of_injective hinj hk, ← singularValues_zero_eq_specNorm,
    hA.posSemidef.singularValues_eq_eigenvalue]

/-- The pseudo-condition number is invariant under the conjugate transpose:
$\mathbf{A}^{\mathsf{H}}$ and $\mathbf{A}$ have the same pseudo-condition number.
Port of `NLAlib.moorePenroseConditionNumber_conjTranspose`. -/
@[simp]
theorem pseudoConditionNumber_conjTranspose (A : Matrix m n 𝕜) :
    pseudoConditionNumber Aᴴ = pseudoConditionNumber A := by
  rw [pseudoConditionNumber, pinv_conjTranspose, specNorm_conjTranspose, specNorm_conjTranspose,
    pseudoConditionNumber]

/-- The pseudo-condition number of the pseudoinverse $\mathbf{A}^{+}$ is that of $\mathbf{A}$. -/
@[simp]
theorem pseudoConditionNumber_pinv (A : Matrix m n 𝕜) :
    pseudoConditionNumber (pinv A) = pseudoConditionNumber A := by
  rw [pseudoConditionNumber, pinv_pinv, mul_comm, pseudoConditionNumber]

/-- The pseudo-condition number is invariant under nonzero scaling: $c\mathbf{A}$ and
$\mathbf{A}$ have the same pseudo-condition number for $c \ne 0$.
Port of `NLAlib.moorePenroseConditionNumber_smul`. -/
theorem pseudoConditionNumber_smul {c : 𝕜} (hc : c ≠ 0) (A : Matrix m n 𝕜) :
    pseudoConditionNumber (c • A) = pseudoConditionNumber A := by
  have hc' : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  rw [pseudoConditionNumber, pinv_smul, specNorm_smul, specNorm_smul, norm_inv,
    pseudoConditionNumber]
  field_simp

/-- The pseudo-condition number of the Gram matrix $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ is the
square of the pseudo-condition number of $\mathbf{A}$.
Port of `NLAlib.moorePenroseConditionNumber_conjTranspose_mul_self`. -/
theorem pseudoConditionNumber_conjTranspose_mul_self (A : Matrix m n 𝕜) :
    pseudoConditionNumber (Aᴴ * A) = pseudoConditionNumber A ^ 2 := by
  rw [pseudoConditionNumber, specNorm_conjTranspose_mul_self, ← specNorm_pinv_sq,
    pseudoConditionNumber, mul_pow]

/-- Left multiplication by a matrix with orthonormal columns preserves the pseudo-condition number.
Port of `NLAlib.moorePenroseConditionNumber_mul_left_of_hasOrthonormalCols`. -/
theorem HasOrthonormalCols.pseudoConditionNumber_mul_left [DecidableEq m] {Q : Matrix l m 𝕜}
    (hQ : HasOrthonormalCols Q) (A : Matrix m n 𝕜) :
    pseudoConditionNumber (Q * A) = pseudoConditionNumber A := by
  rw [pseudoConditionNumber, hQ.pinv_mul_left, hQ.specNorm_mul_left,
    hQ.specNorm_mul_conjTranspose_right, pseudoConditionNumber]

/-- A matrix with orthonormal columns, and at least one column, has pseudo-condition number one. -/
theorem HasOrthonormalCols.pseudoConditionNumber_eq_one [DecidableEq n] [Nonempty n]
    {Q : Matrix m n 𝕜} (hQ : HasOrthonormalCols Q) : pseudoConditionNumber Q = 1 := by
  rw [pseudoConditionNumber, hQ.pinv_eq, specNorm_conjTranspose, hQ.specNorm_eq_one, mul_one]

/-- **Two-sided Gram bounds control the pseudo-condition number.** If
$a\mathbf{I} \preceq \mathbf{A}^{\mathsf{H}}\mathbf{A} \preceq b\mathbf{I}$ with $0 < a$ and
$0 \le b$, then $(\|\mathbf{A}\|_2 \|\mathbf{A}^{+}\|_2)^2 \le b / a$. With
$\mathbf{A} = \mathbf{S}\mathbf{U}$ this is the conditioning of a sketched orthonormal basis. -/
theorem pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one [DecidableEq n]
    {A : Matrix m n 𝕜} {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (h₁ : a • (1 : Matrix n n 𝕜) ≤ Aᴴ * A) (h₂ : Aᴴ * A ≤ b • (1 : Matrix n n 𝕜)) :
    pseudoConditionNumber A ^ 2 ≤ b / a := by
  rw [pseudoConditionNumber, mul_pow, div_eq_mul_inv]
  exact mul_le_mul ((specNorm_sq_le_iff_conjTranspose_mul_self_le hb).mpr h₂)
    (specNorm_pinv_sq_le_inv_of_smul_one_le ha h₁) (sq_nonneg _) hb

/-! ### Distance to rank deficiency -/

/-- **The smallest singular value is a lower bound for rank-deficient perturbations.** If
$\mathbf{A} + \mathbf{E}$ does not have full column rank, then
$\sigma_k(\mathbf{A}) \le \|\mathbf{E}\|_2$ for $k + 1 = \lvert n \rvert$: $\sigma_k(\mathbf{A})$ is
$\sigma_{\min}(\mathbf{A})$, the last of the $\lvert n \rvert$ singular values.
[GolubVanLoan2013, Theorem 2.5.3 and §2.6.2].
Port of `NLAlib.inv_specNorm_inv_le_specNorm_of_not_isUnit_add`, there for square real
matrices. -/
theorem singularValues_last_le_specNorm_of_not_injective_add (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) {E : Matrix m n 𝕜}
    (hE : ¬ Function.Injective (A + E).mulVec) : singularValues A k ≤ specNorm E := by
  have h0 : singularValues (A + E) k = 0 :=
    le_antisymm (not_lt.mp ((singularValues_last_pos_iff_injective (A + E) hk).not.mpr hE))
      (singularValues_nonneg _ _)
  have h := abs_singularValues_sub_le_specNorm A (A + E) k
  rw [h0, sub_zero, sub_add_cancel_left, specNorm_neg] at h
  exact (le_abs_self _).trans h

/-- **The distance to rank deficiency is the smallest singular value.** Among perturbations
$\mathbf{E}$ for which $\mathbf{A} + \mathbf{E}$ loses full column rank, the smallest spectral norm
is $\sigma_k(\mathbf{A})$ with $k + 1 = \lvert n \rvert$, that is $\sigma_{\min}(\mathbf{A})$; it is
attained.
[GolubVanLoan2013, §2.6.2].
Port of `NLAlib.isLeast_specNorm_singular_perturbations`, there for square real matrices.
Result: distance-to-singularity -/
theorem isLeast_specNorm_not_injective_add (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    IsLeast (specNorm '' {E : Matrix m n 𝕜 | ¬ Function.Injective (A + E).mulVec})
      (singularValues A k) := by
  refine ⟨⟨truncatedSVD A k - A, ?_, ?_⟩, ?_⟩
  · rw [Set.mem_ofPred_eq, add_sub_cancel, mulVec_injective_iff_rank_eq]
    have := rank_truncatedSVD_le A k
    omega
  · rw [specNorm_sub_comm, specNorm_sub_truncatedSVD]
  · rintro _ ⟨E, hE, rfl⟩
    exact singularValues_last_le_specNorm_of_not_injective_add A hk hE

/-- **The distance from an invertible matrix to the singular matrices** is
$1 / \|\mathbf{A}^{-1}\|_2$: it is the least $\|\mathbf{E}\|_2$ over $\mathbf{E}$ with
$\mathbf{A} + \mathbf{E}$ singular, on a nonempty index type.
[GolubVanLoan2013, §2.6.2].
Port of `NLAlib.isLeast_specNorm_singular_perturbations`.
Result: distance-to-singularity -/
theorem isLeast_specNorm_not_isUnit_add [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : IsUnit A) :
    IsLeast (specNorm '' {E : Matrix n n 𝕜 | ¬ IsUnit (A + E)}) (specNorm A⁻¹)⁻¹ := by
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n :=
    ⟨Fintype.card n - 1, Nat.sub_add_cancel Fintype.card_pos⟩
  have hinj : Function.Injective A.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hA
  have hset : {E : Matrix n n 𝕜 | ¬ IsUnit (A + E)} =
      {E | ¬ Function.Injective (A + E).mulVec} := by
    ext E
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Matrix.mulVec_injective_iff_isUnit]
  rw [hset, ← pinv_of_isUnit hA, specNorm_pinv_of_injective hinj hk, inv_inv]
  exact isLeast_specNorm_not_injective_add A hk

/-- The relative distance from an invertible matrix to the singular matrices is the inverse of
the pseudo-condition number, which for an invertible matrix is the classical condition number:
the least $\|\mathbf{E}\|_2 / \|\mathbf{A}\|_2$ over $\mathbf{E}$ with $\mathbf{A} + \mathbf{E}$
singular is $\kappa(\mathbf{A})^{-1} = (\|\mathbf{A}\|_2 \|\mathbf{A}^{-1}\|_2)^{-1}$. Port of
`NLAlib.isLeast_relative_singular_perturbations`. -/
theorem isLeast_specNorm_div_not_isUnit_add [DecidableEq n] [Nonempty n] {A : Matrix n n 𝕜}
    (hA : IsUnit A) :
    IsLeast ((fun E : Matrix n n 𝕜 => specNorm E / specNorm A) '' {E | ¬ IsUnit (A + E)})
      (pseudoConditionNumber A)⁻¹ := by
  have heq : (pseudoConditionNumber A)⁻¹ = (specNorm A⁻¹)⁻¹ / specNorm A := by
    rw [pseudoConditionNumber_of_isUnit hA, mul_inv, div_eq_mul_inv, mul_comm]
  obtain ⟨⟨E, hE, hEn⟩, hmin⟩ := isLeast_specNorm_not_isUnit_add hA
  rw [heq]
  refine ⟨⟨E, hE, ?_⟩, ?_⟩
  · rw [← hEn]
  · rintro _ ⟨F, hF, rfl⟩
    exact div_le_div_of_nonneg_right (hmin ⟨F, hF, rfl⟩) (specNorm_nonneg A)

/-! ### Deprecated aliases -/

@[deprecated pseudoConditionNumber (since := "2026-10-14")]
noncomputable alias conditionNumber :=
  pseudoConditionNumber

@[deprecated pseudoConditionNumber_def (since := "2026-10-14")]
alias conditionNumber_def :=
  pseudoConditionNumber_def

@[deprecated pseudoConditionNumber_nonneg (since := "2026-10-14")]
alias conditionNumber_nonneg :=
  pseudoConditionNumber_nonneg

@[deprecated pseudoConditionNumber_zero (since := "2026-10-14")]
alias conditionNumber_zero :=
  pseudoConditionNumber_zero

@[deprecated one_le_pseudoConditionNumber (since := "2026-10-14")]
alias one_le_conditionNumber :=
  one_le_pseudoConditionNumber

@[deprecated pseudoConditionNumber_eq_singularValues_div (since := "2026-10-14")]
alias conditionNumber_eq_singularValues_div :=
  pseudoConditionNumber_eq_singularValues_div

@[deprecated pseudoConditionNumber_of_injective (since := "2026-10-14")]
alias conditionNumber_of_injective :=
  pseudoConditionNumber_of_injective

@[deprecated pseudoConditionNumber_of_isUnit (since := "2026-10-14")]
alias conditionNumber_of_isUnit :=
  pseudoConditionNumber_of_isUnit

@[deprecated _root_.Matrix.PosDef.pseudoConditionNumber_eq (since := "2026-10-14")]
alias _root_.Matrix.PosDef.conditionNumber_eq :=
  _root_.Matrix.PosDef.pseudoConditionNumber_eq

@[deprecated pseudoConditionNumber_conjTranspose (since := "2026-10-14")]
alias conditionNumber_conjTranspose :=
  pseudoConditionNumber_conjTranspose

@[deprecated pseudoConditionNumber_pinv (since := "2026-10-14")]
alias conditionNumber_pinv :=
  pseudoConditionNumber_pinv

@[deprecated pseudoConditionNumber_smul (since := "2026-10-14")]
alias conditionNumber_smul :=
  pseudoConditionNumber_smul

@[deprecated pseudoConditionNumber_conjTranspose_mul_self (since := "2026-10-14")]
alias conditionNumber_conjTranspose_mul_self :=
  pseudoConditionNumber_conjTranspose_mul_self

@[deprecated HasOrthonormalCols.pseudoConditionNumber_mul_left (since := "2026-10-14")]
alias HasOrthonormalCols.conditionNumber_mul_left :=
  HasOrthonormalCols.pseudoConditionNumber_mul_left

@[deprecated HasOrthonormalCols.pseudoConditionNumber_eq_one (since := "2026-10-14")]
alias HasOrthonormalCols.conditionNumber_eq_one :=
  HasOrthonormalCols.pseudoConditionNumber_eq_one

@[deprecated pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one (since := "2026-10-14")]
alias conditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one :=
  pseudoConditionNumber_sq_le_div_of_smul_one_le_of_le_smul_one

end NLAlib

namespace Mathlib.Meta.Positivity

open Lean Meta Qq

/-- Extension for the `positivity` tactic: `NLAlib.pseudoConditionNumber A` is nonnegative. -/
@[positivity NLAlib.pseudoConditionNumber _]
meta def evalPseudoConditionNumber : PositivityExt where eval {_ _} _ pα? e :=
  match pα? with
  | none => pure .none
  | some _ => do
    let pf ← mkAppM ``NLAlib.pseudoConditionNumber_nonneg #[e.appArg!]
    pure (.nonnegative pf)

end Mathlib.Meta.Positivity
