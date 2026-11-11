/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.SingularValueFilters
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Polynomial.Approximation.NewtonSchulz
public import NLAlib.Matrix.Basic.Gram

/-!
# Inverse-free rectangular polar iteration

The library scalar cubic acts on the singular directions. The defect estimates start
after its first update, including when the initial defect exceeds one. The argument
adapts the original NLAlib atlas at commit 77514ce.

## Main results

* `NLAlib.columnGramDefect_polarSchulzStep`: the exact defect polynomial.
* `NLAlib.specNorm_columnGramDefect_polarSchulzIterate_succ_le`: quadratic defect contraction.
* `NLAlib.tendsto_polarSchulzIterate`: convergence to the polar factor.
-/

@[expose] public section

open Matrix Polynomial Filter
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
namespace NLAlib

/-- The exact scalar identity proving that each admissible step is at most one. -/
private theorem one_sub_polarSchulz_step (s : ℝ) :
    1 - s * (3 - s ^ 2) / 2 = (s - 1) ^ 2 * (s + 2) / 2 := by ring

/-- One admissible step enters the positive unit interval. -/
private theorem polarSchulz_step_mem {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) :
    0 < s * (3 - s ^ 2) / 2 ∧ s * (3 - s ^ 2) / 2 ≤ 1 := by
  constructor
  · positivity
  · have h := one_sub_polarSchulz_step s
    have hn : 0 ≤ (s - 1) ^ 2 * (s + 2) / 2 := by positivity
    linarith

/-- Every iterate after the first lies in `(0,1]`, with no restriction that
the initial defect have norm below one. -/
private theorem polarSchulzScalar_mem {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) (k : ℕ) :
    0 < (newtonSchulz^[k + 1]) s ∧ (newtonSchulz^[k + 1]) s ≤ 1 := by
  induction k with
  | zero => exact polarSchulz_step_mem hs hs3
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    apply polarSchulz_step_mem ih.1
    nlinarith [sq_nonneg ((newtonSchulz^[k + 1]) s - 1)]

/-- Exact scalar orthogonality-defect recurrence. -/
private theorem one_sub_sq_polarSchulz_step (s : ℝ) :
    1 - (s * (3 - s ^ 2) / 2) ^ 2 = (1 - s ^ 2) ^ 2 * (3 + (1 - s ^ 2)) / 4 := by
  rw [← newtonSchulz, one_sub_newtonSchulz_sq]
  ring

/-- Positive unit-interval iterates have defects in `[0,1)`. -/
private theorem polarSchulzScalar_defect_mem {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) (k : ℕ) :
    0 ≤ 1 - (newtonSchulz^[k + 1]) s ^ 2 ∧
      1 - (newtonSchulz^[k + 1]) s ^ 2 < 1 := by
  obtain ⟨hp, hle⟩ := polarSchulzScalar_mem hs hs3 k
  constructor <;> nlinarith [sq_pos_of_pos hp]

/-- After the first iteration, each scalar defect is bounded by the square
of its predecessor. Higham–Schreiber (1990), §3. -/
private theorem polarSchulzScalar_defect_step_le {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3)
    (k : ℕ) :
    1 - (newtonSchulz^[k + 2]) s ^ 2 ≤
      (1 - (newtonSchulz^[k + 1]) s ^ 2) ^ 2 := by
  rw [show k + 2 = (k + 1) + 1 by omega, Function.iterate_succ_apply', newtonSchulz,
    one_sub_sq_polarSchulz_step]
  have he := polarSchulzScalar_defect_mem hs hs3 k
  have hm := mul_le_mul_of_nonneg_left (by linarith :
    3 + (1 - (newtonSchulz^[k + 1]) s ^ 2) ≤ 4)
      (sq_nonneg (1 - (newtonSchulz^[k + 1]) s ^ 2))
  linarith

/-- Double-exponential scalar defect bound, starting with the first defect. -/
private theorem polarSchulzScalar_defect_le {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3)
    (k : ℕ) :
    1 - (newtonSchulz^[k + 1]) s ^ 2 ≤
      (1 - (newtonSchulz^[1]) s ^ 2) ^ (2 ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    calc
      _ ≤ (1 - (newtonSchulz^[k + 1]) s ^ 2) ^ 2 :=
        polarSchulzScalar_defect_step_le hs hs3 k
      _ ≤ ((1 - (newtonSchulz^[1]) s ^ 2) ^ (2 ^ k)) ^ 2 :=
        pow_le_pow_left₀ (polarSchulzScalar_defect_mem hs hs3 k).1 ih 2
      _ = _ := by rw [← pow_mul, Nat.pow_succ]

/-- The scalar distance to one is bounded by the orthogonality defect. -/
private theorem abs_polarSchulzScalar_sub_one_le_defect {s : ℝ}
    (hs : 0 < s) (hs3 : s ^ 2 < 3) (k : ℕ) :
    |(newtonSchulz^[k + 1]) s - 1| ≤ 1 - (newtonSchulz^[k + 1]) s ^ 2 := by
  obtain ⟨hp, hle⟩ := polarSchulzScalar_mem hs hs3 k
  rw [abs_of_nonpos (by linarith)]
  nlinarith [mul_nonneg hp.le (sub_nonneg.mpr hle)]

/-- The actual inverse-free scalar recurrence converges to one. -/
private theorem tendsto_polarSchulzScalar {s : ℝ} (hs : 0 < s) (hs3 : s ^ 2 < 3) :
    Tendsto (fun k => (newtonSchulz^[k]) s) atTop (𝓝 1) := by
  obtain ⟨he0, he1⟩ := polarSchulzScalar_defect_mem hs hs3 0
  have hp := (tendsto_pow_atTop_nhds_zero_of_lt_one he0 he1).comp
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℕ) < 2))
  have ht : Tendsto (fun k => (newtonSchulz^[k + 1]) s - 1) atTop (𝓝 0) :=
    squeeze_zero_norm (fun k => (abs_polarSchulzScalar_sub_one_le_defect hs hs3 k).trans
      (polarSchulzScalar_defect_le hs hs3 k)) hp
  have hh : Tendsto (fun k => (newtonSchulz^[k + 1]) s) atTop (𝓝 1) := by
    simpa only [sub_add_cancel, zero_add] using ht.add_const 1
  exact (tendsto_add_atTop_iff_nat 1).mp hh

variable {𝕜 m n r : Type*} [RCLike 𝕜] [Fintype m] [Fintype n] [Fintype r]
variable [DecidableEq n] [DecidableEq r]

/-- One cubic step for the rectangular polar factor, evaluated using its column Gram matrix.
[Higham2008, §8.3]. -/
noncomputable def polarSchulzStep (A : Matrix m n 𝕜) : Matrix m n 𝕜 :=
  (1 / 2 : ℝ) • (A * ((3 : ℝ) • 1 - Aᴴ * A))

/-- The inverse-free polar Newton–Schulz iteration.
[Higham2008, §8.3].
Algorithm: polar-newton-schulz -/
noncomputable def polarSchulzIterate (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  polarSchulzStep^[k] A

/-- The deviation of a column Gram matrix from the identity, with the sign for which
the defect is positive semidefinite after the first admissible polar step. -/
noncomputable def columnGramDefect (A : Matrix m n 𝕜) : Matrix n n 𝕜 := 1 - Aᴴ * A

/-- **Cubic polar-step defect.** For every real or complex rectangular matrix, the Gram defect
$\mathbf{E}=\mathbf{I}-\mathbf{X}^{\mathsf{H}}\mathbf{X}$ after one cubic step obeys
$$\mathbf{E}_+=\frac14
\mathbf{E}^2(3\mathbf{I}+\mathbf{E}).$$ [Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem columnGramDefect_polarSchulzStep (X : Matrix m n 𝕜) :
    columnGramDefect (polarSchulzStep X) =
      (1 / 4 : ℝ) • (columnGramDefect X ^ 2 * ((3 : ℝ) • 1 + columnGramDefect X)) := by
  let S := Xᴴ * X
  let L := (3 : ℝ) • (1 : Matrix n n 𝕜) - S
  have hS : Sᴴ = S := by simp [S]
  have hL : Lᴴ = L := by simp [L, hS]
  have hG : (polarSchulzStep X)ᴴ * polarSchulzStep X = (1 / 4 : ℝ) • (L * S * L) := by
    change ((1 / 2 : ℝ) • (X * L))ᴴ * ((1 / 2 : ℝ) • (X * L)) = _
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hL,
      star_trivial, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    norm_num only [show (1 / 2 : ℝ) * (1 / 2) = 1 / 4 by norm_num]
    simp only [S, Matrix.mul_assoc]
  rw [columnGramDefect, hG]
  calc
    _ = (1 / 4 : ℝ) • ((4 : ℝ) • (1 : Matrix n n 𝕜) - L * S * L) := by module
    _ = _ := by
      congr 1
      dsimp only [L, S, columnGramDefect]
      noncomm_ring
      module

private theorem polarSchulzStep_eq_aeval (A : Matrix m n 𝕜) :
    polarSchulzStep A = A * aeval (Aᴴ * A) (C (2⁻¹ : ℝ) * (C 3 - X) : ℝ[X]) := by
  simp only [map_mul, map_sub, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
    Matrix.smul_mul, Matrix.one_mul, Matrix.mul_smul, polarSchulzStep, one_div]

/-- **Singular directions of the inverse-free polar iteration.** The kth matrix iterate
acts by the kth iterate of the real cubic on each supplied singular coordinate.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem IsSVD.polarSchulzIterate_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (k : ℕ) :
    polarSchulzIterate A k =
      U * diagonal (fun i => (((newtonSchulz^[k]) (σ i) : ℝ) : 𝕜)) * Vᴴ := by
  induction k with
  | zero => exact h.eq
  | succ k ih =>
    change polarSchulzStep^[k + 1] A = _
    rw [Function.iterate_succ_apply']
    change polarSchulzStep (polarSchulzIterate A k) = _
    rw [polarSchulzStep_eq_aeval, ih,
      h.hasOrthonormalCols_left.mul_aeval_conjTranspose_mul_self h.hasOrthonormalCols_right]
    simp only [eval_mul, eval_sub, eval_C, eval_X, Function.iterate_succ_apply', newtonSchulz,
      div_eq_mul_inv]
    congr 2
    funext i
    congr 1
    ring_nf

omit [DecidableEq n] in
private theorem IsSVD.sq_lt_three {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hA : specNorm A < √3) (i : r) :
    σ i ^ 2 < 3 := by
  have hs : σ i < √3 := (le_abs_self _).trans_lt <|
    (norm_le_pi_norm σ i).trans_lt (h.specNorm_eq ▸ hA)
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), h.nonneg i]

private theorem isSVD_polarSchulzIterate {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hp : ∀ i, 0 < σ i)
    (hA : specNorm A < √3) (k : ℕ) :
    IsSVD (polarSchulzIterate A k) U (fun i => (newtonSchulz^[k]) (σ i)) V := by
  refine ⟨h.hasOrthonormalCols_left, h.hasOrthonormalCols_right, ?_, h.polarSchulzIterate_eq k⟩
  intro i
  cases k with
  | zero => exact (hp i).le
  | succ k => exact (polarSchulzScalar_mem (hp i) (h.sq_lt_three hA i) k).1.le

private theorem IsSVD.columnGramDefect_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hp : ∀ i, 0 < σ i)
    (hc : Fintype.card n = Fintype.card r) (hA : specNorm A < √3) (k : ℕ) :
    columnGramDefect (polarSchulzIterate A k) =
      V * diagonal (fun i => ((1 - ((newtonSchulz^[k]) (σ i)) ^ 2 : ℝ) : 𝕜)) * Vᴴ := by
  have hI : (1 : Matrix n n 𝕜) = V * diagonal (fun _ : r => (1 : 𝕜)) * Vᴴ := by
    simpa only [Matrix.diagonal_one, Matrix.mul_one] using
      (h.hasOrthonormalCols_right.mul_conjTranspose_self_of_card_eq hc).symm
  rw [columnGramDefect, hI, (isSVD_polarSchulzIterate h hp hA k).conjTranspose_mul_self_eq,
    ← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.diagonal_sub]
  simp only [RCLike.ofReal_sub, RCLike.ofReal_one]

private theorem IsSVD.specNorm_columnGramDefect_eq {A : Matrix m n 𝕜} {U : Matrix m r 𝕜}
    {V : Matrix n r 𝕜} {σ : r → ℝ} (h : IsSVD A U σ V) (hp : ∀ i, 0 < σ i)
    (hc : Fintype.card n = Fintype.card r) (hA : specNorm A < √3) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A k)) =
      ‖fun i => 1 - ((newtonSchulz^[k]) (σ i)) ^ 2‖ := by
  rw [h.columnGramDefect_eq hp hc hA,
    h.hasOrthonormalCols_right.specNorm_mul_diagonal_mul_conjTranspose h.hasOrthonormalCols_right]

omit [DecidableEq n] in
private theorem exists_compactSVD_of_injective (A : Matrix m n 𝕜)
    (hr : Function.Injective A.mulVec) :
    ∃ (U : Matrix m (Fin A.rank) 𝕜) (V : Matrix n (Fin A.rank) 𝕜),
      IsSVD A U (fun i : Fin A.rank => singularValues A i) V ∧
      (∀ i : Fin A.rank, 0 < singularValues A i) ∧ Fintype.card n = Fintype.card (Fin A.rank) := by
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  refine ⟨U, V, h, fun i => (singularValues_pos_iff A).mpr i.isLt, ?_⟩
  rw [Fintype.card_fin, ← mulVec_injective_iff_rank_eq.mp hr]

/-- **Positivity after the first inverse-free polar step.** If the input has full column rank
and spectral norm below $\sqrt{3}$, each subsequent Gram defect is positive semidefinite.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem posSemidef_columnGramDefect_polarSchulzIterate (A : Matrix m n 𝕜)
    (hA : specNorm A < √3) (hr : Function.Injective A.mulVec) (k : ℕ) :
    (columnGramDefect (polarSchulzIterate A (k + 1))).PosSemidef := by
  classical
  obtain ⟨U, V, h, hp, hc⟩ := exists_compactSVD_of_injective A hr
  rw [h.columnGramDefect_eq hp hc hA]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.posSemidef_diagonal_iff.mpr
  intro i
  exact_mod_cast (polarSchulzScalar_defect_mem (hp i) (h.sq_lt_three hA i) k).1

/-- **Strict upper bound on the polar Gram defect.** For a full-column-rank input of
spectral norm below $\sqrt{3}$, every subsequent Gram defect is strictly below the identity.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem posDef_one_sub_columnGramDefect_polarSchulzIterate (A : Matrix m n 𝕜)
    (hA : specNorm A < √3) (hr : Function.Injective A.mulVec) (k : ℕ) :
    (1 - columnGramDefect (polarSchulzIterate A (k + 1))).PosDef := by
  classical
  obtain ⟨U, V, h, hp, hc⟩ := exists_compactSVD_of_injective A hr
  simp only [columnGramDefect, sub_sub_cancel]
  apply (Matrix.posSemidef_conjTranspose_mul_self _).posDef_iff_isUnit.mpr
  rw [isUnit_conjTranspose_mul_self_iff_rank, (isSVD_polarSchulzIterate h hp hA _).rank_eq,
    hc]
  have hne (i : Fin A.rank) : (newtonSchulz^[k + 1]) (singularValues A i) ≠ 0 :=
    (polarSchulzScalar_mem (hp i) (h.sq_lt_three hA i) k).1.ne'
  change (Finset.univ.filter (fun i : Fin A.rank =>
    (newtonSchulz^[k + 1]) (singularValues A i) ≠ 0)).card = Fintype.card (Fin A.rank)
  rw [Finset.filter_eq_self.mpr (fun i _ => hne i), Finset.card_univ]

/-- **Polar Gram defect below one.** A full-column-rank input of spectral norm below
$\sqrt{3}$ has a strict Gram defect contraction after one or more steps.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_columnGramDefect_polarSchulzIterate_lt_one (A : Matrix m n 𝕜)
    (hA : specNorm A < √3) (hr : Function.Injective A.mulVec) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) < 1 := by
  classical
  obtain ⟨U, V, h, hp, hc⟩ := exists_compactSVD_of_injective A hr
  simp only [h.specNorm_columnGramDefect_eq hp hc hA]
  apply (pi_norm_lt_iff (by norm_num : (0 : ℝ) < 1)).mpr
  intro i
  have he := polarSchulzScalar_defect_mem (hp i) (h.sq_lt_three hA i) k
  simpa only [Real.norm_eq_abs, abs_of_nonneg he.1] using he.2

/-- **Quadratic Gram defect contraction.** For a full-column-rank input of spectral norm
below $\sqrt{3}$, each subsequent defect norm is at most the square of the preceding one.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_columnGramDefect_polarSchulzIterate_succ_le (A : Matrix m n 𝕜)
    (hA : specNorm A < √3) (hr : Function.Injective A.mulVec) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A (k + 2))) ≤
      specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) ^ 2 := by
  classical
  obtain ⟨U, V, h, hp, hc⟩ := exists_compactSVD_of_injective A hr
  simp only [h.specNorm_columnGramDefect_eq hp hc hA]
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg _)).mpr
  intro i
  have hx := h.sq_lt_three hA i
  have he := polarSchulzScalar_defect_mem (hp i) hx (k + 1)
  rw [Real.norm_eq_abs, abs_of_nonneg he.1]
  exact (polarSchulzScalar_defect_step_le (hp i) hx k).trans <|
    pow_le_pow_left₀ (polarSchulzScalar_defect_mem (hp i) hx k).1
      ((le_abs_self _).trans (norm_le_pi_norm
        (fun j : Fin A.rank => 1 - ((newtonSchulz^[k + 1]) (singularValues A j)) ^ 2) i)) 2

/-- **Polar error controlled by the Gram defect.** At full column rank and initial spectral
norm below $\sqrt{3}$, the defect bounds the polar error from the first step.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_polarFactor_sub_polarSchulzIterate_le (A : Matrix m n 𝕜)
    (hA : specNorm A < √3) (hr : Function.Injective A.mulVec) (k : ℕ) :
    specNorm (polarFactor A - polarSchulzIterate A (k + 1)) ≤
      specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) := by
  classical
  obtain ⟨U, V, h, hp, hc⟩ := exists_compactSVD_of_injective A hr
  simp only [h.specNorm_columnGramDefect_eq hp hc hA]
  rw [h.polarFactor_eq, h.polarSchulzIterate_eq]
  simp only [if_neg (hp _).ne']
  have he := h.hasOrthonormalCols_left.specNorm_sub_mul_diagonal_mul_conjTranspose
    h.hasOrthonormalCols_right (fun _ => (1 : ℝ))
    (fun i : Fin A.rank => (newtonSchulz^[k + 1]) (singularValues A i))
  simp only [RCLike.ofReal_one] at he
  rw [he]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro i
  rw [Pi.sub_apply, Real.norm_eq_abs, abs_sub_comm]
  exact (abs_polarSchulzScalar_sub_one_le_defect (hp i) (h.sq_lt_three hA i) k).trans
    ((le_abs_self _).trans (norm_le_pi_norm
      (fun j : Fin A.rank => 1 - ((newtonSchulz^[k + 1]) (singularValues A j)) ^ 2) i))

/-- **Polar Gram defect rate.** At full column rank and initial spectral norm below $\sqrt{3}$,
the defect after $k+1$ steps is at most the first defect norm raised to $2^k$.
[Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem specNorm_columnGramDefect_polarSchulzIterate_le_pow (A : Matrix m n 𝕜)
    (hA : specNorm A < √3) (hr : Function.Injective A.mulVec) (k : ℕ) :
    specNorm (columnGramDefect (polarSchulzIterate A (k + 1))) ≤
      specNorm (columnGramDefect (polarSchulzIterate A 1)) ^ (2 ^ k) := by
  classical
  obtain ⟨U, V, h, hp, hc⟩ := exists_compactSVD_of_injective A hr
  simp only [h.specNorm_columnGramDefect_eq hp hc hA]
  apply (pi_norm_le_iff_of_nonneg (pow_nonneg (norm_nonneg _) _)).mpr
  intro i
  have hx := h.sq_lt_three hA i
  have he := polarSchulzScalar_defect_mem (hp i) hx k
  rw [Real.norm_eq_abs, abs_of_nonneg he.1]
  exact (polarSchulzScalar_defect_le (hp i) hx k).trans
    (pow_le_pow_left₀ (polarSchulzScalar_defect_mem (hp i) hx 0).1
      ((le_abs_self _).trans (norm_le_pi_norm
        (fun j : Fin A.rank => 1 - (newtonSchulz (singularValues A j)) ^ 2) i)) _)

/-- **Convergence of the inverse-free polar iteration.** For every real or complex rectangular
matrix of spectral norm below the square root of three, the cubic iterates converge to its
canonical polar factor, including rank-deficient inputs. [Higham2008, §8.3].
Result: polar-newton-schulz-iteration -/
theorem tendsto_polarSchulzIterate (A : Matrix m n 𝕜) (hA : specNorm A < √3) :
    Tendsto (polarSchulzIterate A) atTop (𝓝 (polarFactor A)) := by
  classical
  obtain ⟨U, V, h⟩ := exists_isSVD A le_rfl A.rank_le_card_height A.rank_le_card_width
  have hp (i : Fin A.rank) : 0 < singularValues A i := (singularValues_pos_iff A).mpr i.isLt
  let F (f : Fin A.rank → ℝ) := U * diagonal (fun i => (f i : 𝕜)) * Vᴴ
  have hc : Continuous F := by dsimp [F]; fun_prop
  have hs : Tendsto (fun k (i : Fin A.rank) => (newtonSchulz^[k]) (singularValues A i))
      atTop (𝓝 (fun _ : Fin A.rank => (1 : ℝ))) :=
    tendsto_pi_nhds.mpr fun i => tendsto_polarSchulzScalar (hp i) (h.sq_lt_three hA i)
  convert! hc.continuousAt.tendsto.comp hs using 1
  · exact funext fun k => h.polarSchulzIterate_eq k
  · apply congrArg nhds
    simpa only [F, RCLike.ofReal_one, if_neg (hp _).ne'] using h.polarFactor_eq

end NLAlib
