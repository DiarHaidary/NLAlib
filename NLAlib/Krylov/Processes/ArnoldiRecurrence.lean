/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.Lanczos
public import NLAlib.Matrix.Factorizations.GramSchmidt

/-!
# The Arnoldi process

The Arnoldi process in modified Gram–Schmidt form, as a total recursion on the sequence of
computed vectors: step $j$ forms $\mathbf{A}\mathbf{q}_j$, orthogonalises it against
$\mathbf{q}_0, \dots, \mathbf{q}_j$ one at a time (`NLAlib.mgsSweep`), records the coefficients
$h_{ij}$ and $h_{j+1,j} = \|\mathbf{w}_j\|$, and sets $\mathbf{q}_{j+1} = \mathbf{w}_j/h_{j+1,j}$.
Breakdown is a value: with $0^{-1} = 0$ the vector after $h_{j+1,j} = 0$ is zero, and so is every
later vector and coefficient.

The realisation theorems say that for every $\mathbf{A}$ the process computes the canonical basis
`arnoldiMatrix A b q` and the rectangular Hessenberg matrix
$\mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q$, for every $q$ and with no breakdown
hypothesis, because past the grade both sides are zero. Breakdown happens exactly at the grade.

## Main definitions

* `NLAlib.arnoldiStep`, `NLAlib.arnoldiState`: the recursion.
* `NLAlib.mgsArnoldiMatrix`, `NLAlib.mgsArnoldiHessenberg`: what the implementation outputs.

## Main results

* `NLAlib.mgsArnoldiMatrix_eq_arnoldiMatrix`: the process computes the canonical basis.
* `NLAlib.mgsArnoldiHessenberg_eq`: it computes $\underline{\mathbf{H}}_q$.
* `NLAlib.isUpperHessenberg_mgsArnoldiHessenberg`: the computed matrix is Hessenberg.
* `NLAlib.mul_mgsArnoldiMatrix`: the computed Arnoldi relation.
* `NLAlib.mgsArnoldiHessenberg_apply_succ_eq_zero_iff`: breakdown exactly at the grade.
* `NLAlib.mgsArnoldiHessenberg_apply_eq_zero_of_le`: past the grade the computed matrix is zero.
* `NLAlib.injective_mulVec_mgsArnoldiHessenberg_iff`: for invertible $\mathbf{A}$, full column
  rank exactly up to the grade.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **One Arnoldi step** in modified Gram–Schmidt form: from the vectors
$\mathbf{q}_0, \dots, \mathbf{q}_j$ (entries $0$ to $j$ of `V`), form
$\mathbf{w} = \mathsf{mgsSweep}(\mathbf{q}, \mathbf{A}\mathbf{q}_j, j + 1)$ and set entry $j + 1$
to $\mathbf{w}/\|\mathbf{w}\|$ ($\mathbf{0}$ when $\mathbf{w} = \mathbf{0}$).
[Saad2003, Algorithm 6.2]. -/
noncomputable def arnoldiStep (A : Matrix n n 𝕜) (j : ℕ) (V : ℕ → n → 𝕜) : ℕ → n → 𝕜 :=
  Function.update V (j + 1)
    ((‖WithLp.toLp 2 (mgsSweep V (A *ᵥ V j) (j + 1))‖⁻¹ : 𝕜) • mgsSweep V (A *ᵥ V j) (j + 1))

/-- The **Arnoldi process**: after step $j$, entries $0$ to $j$ are $\mathbf{q}_0, \dots,
\mathbf{q}_j$, from $\mathbf{q}_0 = \mathbf{b}/\|\mathbf{b}\|$; later entries are $\mathbf{0}$.
[Saad2003, Algorithm 6.2]. -/
noncomputable def arnoldiState (A : Matrix n n 𝕜) (b : n → 𝕜) : ℕ → ℕ → n → 𝕜
  | 0 => Pi.single 0 ((‖WithLp.toLp 2 b‖⁻¹ : 𝕜) • b)
  | j + 1 => arnoldiStep A j (arnoldiState A b j)

/-- The basis computed by the Arnoldi process: column $j$ is $\mathbf{q}_j$. -/
noncomputable def mgsArnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun i j => arnoldiState A b j j i

/-- The $(q + 1) \times q$ Hessenberg matrix computed by the Arnoldi process: the modified
Gram–Schmidt coefficients $h_{ij} = \mathbf{q}_i^{\mathsf{H}}\mathbf{u}_i$ for $i \le j$, where
$\mathbf{u}_i$ is $\mathbf{A}\mathbf{q}_j$ reduced against $\mathbf{q}_0, \dots, \mathbf{q}_{i-1}$,
the norm $h_{j+1,j} = \|\mathbf{w}_j\|$, and zero below. -/
noncomputable def mgsArnoldiHessenberg (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin q) 𝕜 :=
  Matrix.of fun i j =>
    if (i : ℕ) ≤ j then
      star (arnoldiState A b j i) ⬝ᵥ
        mgsSweep (arnoldiState A b j) (A *ᵥ arnoldiState A b j j) i
    else if (i : ℕ) = j + 1 then
      (‖WithLp.toLp 2 (mgsSweep (arnoldiState A b j) (A *ᵥ arnoldiState A b j j) (j + 1))‖ : 𝕜)
    else 0

omit [DecidableEq n] in
/-- Computed vectors do not change at later steps. -/
theorem arnoldiState_apply_of_le (A : Matrix n n 𝕜) (b : n → 𝕜) {i j : ℕ} (h : i ≤ j) :
    arnoldiState A b j i = arnoldiState A b i i := by
  induction j, h using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    rw [← ih]
    change Function.update (arnoldiState A b j) (j + 1) _ i = _
    exact Function.update_of_ne (by omega) _ _

/-! ### The computed vectors are the canonical columns -/

section Canonical

variable (A : Matrix n n 𝕜) (b : n → 𝕜)

/-- A sweep against vectors equal to the canonical columns is the classical sweep. -/
private theorem mgsSweep_eq_of_forall {V : ℕ → n → 𝕜} {j : ℕ}
    (hV : ∀ i ≤ j, V i = (arnoldiMatrix A b (i + 1)).col (Fin.last i)) {k : ℕ} (hk : k ≤ j + 1)
    (w : n → 𝕜) :
    mgsSweep V w k = w - ∑ i ∈ Finset.range k,
      (star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ w) •
        (arnoldiMatrix A b (i + 1)).col (Fin.last i) := by
  rw [mgsSweep_eq_sub_sum (fun i hi l hl => by
    rw [hV i (by omega), hV l (by omega)]
    exact star_arnoldiMatrix_col_last_dotProduct_of_ne A b (by omega))]
  refine congrArg (w - ·) (Finset.sum_congr rfl fun i hi => ?_)
  rw [hV i (by have := Finset.mem_range.mp hi; omega)]

/-- The classical sweep against the first $j + 1$ canonical columns is the projector onto
$\mathcal{K}_{j+1}$. -/
private theorem sum_range_smul_arnoldiMatrix_col_last (j : ℕ) (w : n → 𝕜) :
    ∑ i ∈ Finset.range (j + 1), (star ((arnoldiMatrix A b (i + 1)).col (Fin.last i)) ⬝ᵥ w) •
        (arnoldiMatrix A b (i + 1)).col (Fin.last i) =
      rangeProjector (krylovMatrix A b (j + 1)) *ᵥ w := by
  rw [← gramSchmidtQ_mul_conjTranspose, ← arnoldiMatrix, ← Matrix.mulVec_mulVec,
    Matrix.mulVec_eq_sum, Finset.sum_range]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [op_smul_eq_smul, ← arnoldiMatrix_col_eq_col_last A b i]
  rfl

/-- One step of the process on vectors equal to the canonical columns. -/
private theorem mgsSweep_succ_eq_of_forall {V : ℕ → n → 𝕜} {j : ℕ}
    (hV : ∀ i ≤ j, V i = (arnoldiMatrix A b (i + 1)).col (Fin.last i)) :
    mgsSweep V (A *ᵥ V j) (j + 1) = (1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) := by
  rw [mgsSweep_eq_of_forall A b hV le_rfl, sum_range_smul_arnoldiMatrix_col_last, hV j le_rfl,
    Matrix.sub_mulVec, Matrix.one_mulVec]

/-- The computed vectors are the canonical columns. -/
private theorem arnoldiState_apply_eq (j : ℕ) :
    ∀ i ≤ j, arnoldiState A b j i = (arnoldiMatrix A b (i + 1)).col (Fin.last i) := by
  induction j with
  | zero =>
    intro i hi
    obtain rfl : i = 0 := by omega
    have hcol : (krylovMatrix A b (0 + 1)).col ⊥ = b := by
      ext i
      simp [show (⊥ : Fin 1) = 0 from rfl]
    rw [arnoldiMatrix, show Fin.last 0 = ⊥ from rfl, gramSchmidtQ_col_bot, hcol]
    exact Pi.single_eq_same _ _
  | succ j ih =>
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hi) with hi | rfl
    · rw [← ih i (Nat.lt_succ_iff.mp hi)]
      change Function.update (arnoldiState A b j) (j + 1) _ i = _
      exact Function.update_of_ne (by omega) _ _
    · change Function.update (arnoldiState A b j) (j + 1) _ (j + 1) = _
      rw [Function.update_self, mgsSweep_succ_eq_of_forall A b ih]
      exact (arnoldiMatrix_col_succ A b j).symm

/-- The last Arnoldi vector reduction: $\mathbf{w}_j = (\mathbf{I} -
\mathbf{P}_{\mathcal{K}_{j+1}})\mathbf{A}\mathbf{q}_j$. -/
private theorem mgsSweep_arnoldiState (j : ℕ) :
    mgsSweep (arnoldiState A b j) (A *ᵥ arnoldiState A b j j) (j + 1) =
      (1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) :=
  mgsSweep_succ_eq_of_forall A b (arnoldiState_apply_eq A b j)

/-- The subdiagonal of the canonical compression is the norm of the reduced vector:
$\mathbf{q}_{j+1}^{\mathsf{H}}\mathbf{A}\mathbf{q}_j = \|\mathbf{w}_j\|$. -/
private theorem star_arnoldiMatrix_col_succ_dotProduct_mulVec (j : ℕ) :
    star ((arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1))) ⬝ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) =
      (‖WithLp.toLp 2 ((1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)))‖ : 𝕜) := by
  have hPv : rangeProjector (krylovMatrix A b (j + 1)) *ᵥ
      (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) ∈ krylovSpace A b (j + 1) := by
    rw [krylovSpace, ← range_mulVecLin_rangeProjector]
    exact ⟨_, rfl⟩
  have hv : A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j) =
      rangeProjector (krylovMatrix A b (j + 1)) *ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) +
      (1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, add_sub_cancel]
  have hq := arnoldiMatrix_col_succ A b j
  calc star ((arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1))) ⬝ᵥ
        (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)) =
      star ((arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1))) ⬝ᵥ
        ((1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
          (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j))) := by
        conv_lhs => rw [hv]
        rw [dotProduct_add, star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem A b le_rfl hPv,
          zero_add]
    _ = _ := by
        rw [show (arnoldiMatrix A b (j + 1 + 1)).col (Fin.last (j + 1)) = _ from hq, star_smul,
          smul_dotProduct, EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, smul_eq_mul,
          RCLike.star_def, map_inv₀, RCLike.conj_ofReal]
        rcases eq_or_ne ‖WithLp.toLp 2 ((1 - rangeProjector (krylovMatrix A b (j + 1))) *ᵥ
          (A *ᵥ (arnoldiMatrix A b (j + 1)).col (Fin.last j)))‖ 0 with h | h
        · rw [h]
          simp
        · push_cast
          field_simp

end Canonical

/-- **The Arnoldi process computes the canonical basis**, for every $\mathbf{A}$ and every $q$,
with no breakdown hypothesis: past the grade both are zero. [Saad2003, Proposition 6.4].
Result: arnoldi-recurrence -/
theorem mgsArnoldiMatrix_eq_arnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    mgsArnoldiMatrix A b q = arnoldiMatrix A b q := by
  ext i j
  change arnoldiState A b j j i = _
  rw [arnoldiState_apply_eq A b j j le_rfl]
  exact congrFun (arnoldiMatrix_col_eq_col_last A b j).symm i

/-- **The Arnoldi process computes the Hessenberg matrix**: for every $\mathbf{A}$ and $q$,
the computed matrix is $\underline{\mathbf{H}}_q =
\mathbf{Q}_{q+1}^{\mathsf{H}}\mathbf{A}\mathbf{Q}_q$ for the canonical bases. [Saad2003, §6.3]. -/
theorem mgsArnoldiHessenberg_eq (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    mgsArnoldiHessenberg A b q = (arnoldiMatrix A b (q + 1))ᴴ * A * arnoldiMatrix A b q := by
  ext i j
  rw [Matrix.mul_assoc, conjTranspose_mul_apply, arnoldiMatrix_col_eq_col_last A b i,
    show (A * arnoldiMatrix A b q).col j = A *ᵥ (arnoldiMatrix A b q).col j from rfl,
    arnoldiMatrix_col_eq_col_last A b j]
  simp only [mgsArnoldiHessenberg, Matrix.of_apply]
  split_ifs with h1 h2
  · rw [mgsSweep_eq_of_forall A b (arnoldiState_apply_eq A b j) (show (i : ℕ) ≤ j + 1 by omega),
      arnoldiState_apply_eq A b j i h1,
      arnoldiState_apply_eq A b j j le_rfl, dotProduct_sub, dotProduct_sum, sub_eq_self]
    refine Finset.sum_eq_zero fun l hl => ?_
    rw [dotProduct_smul, star_arnoldiMatrix_col_last_dotProduct_of_ne A b
      (by have := Finset.mem_range.mp hl; omega), smul_zero]
  · rw [mgsSweep_arnoldiState]
    obtain ⟨i, hi⟩ := i
    simp only at h2 ⊢
    subst h2
    exact (star_arnoldiMatrix_col_succ_dotProduct_mulVec A b j).symm
  · exact (star_arnoldiMatrix_col_last_dotProduct_mulVec_of_lt A b (by omega)).symm

omit [DecidableEq n] in
/-- The computed Hessenberg matrix is upper Hessenberg, for every $\mathbf{A}$; with
`mgsArnoldiHessenberg_eq` this is `IsGradedKrylovBasis.isUpperHessenberg` in rectangular form. -/
theorem isUpperHessenberg_mgsArnoldiHessenberg (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    IsUpperHessenberg (mgsArnoldiHessenberg A b q) := by
  intro i j hij
  simp only [mgsArnoldiHessenberg, Matrix.of_apply]
  rw [if_neg (by omega), if_neg (by omega)]

omit [DecidableEq n] in
/-- **The computed Arnoldi relation**
$\mathbf{A}\mathbf{Q}_q = \mathbf{Q}_{q+1}\underline{\mathbf{H}}_q$, for every $\mathbf{A}$ and
$q$, with the matrices the process computes. [Saad2003, Proposition 6.5]. -/
theorem mul_mgsArnoldiMatrix (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    A * mgsArnoldiMatrix A b q = mgsArnoldiMatrix A b (q + 1) * mgsArnoldiHessenberg A b q := by
  classical
  rw [mgsArnoldiMatrix_eq_arnoldiMatrix, mgsArnoldiMatrix_eq_arnoldiMatrix,
    mgsArnoldiHessenberg_eq]
  exact mul_arnoldiMatrix A b q

/-- **Arnoldi breaks down exactly at the grade**: $h_{j+1,j} = 0$ iff $\nu \le j + 1$, for every
$\mathbf{A}$. [Saad2003, Proposition 6.6]. -/
theorem mgsArnoldiHessenberg_apply_succ_eq_zero_iff (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ}
    (j : Fin q) : mgsArnoldiHessenberg A b q j.succ j = 0 ↔ krylovGrade A b ≤ j + 1 := by
  simp only [mgsArnoldiHessenberg, Matrix.of_apply, Fin.val_succ, Nat.not_succ_le_self,
    ↓reduceIte]
  rw [mgsSweep_arnoldiState A b j, RCLike.ofReal_eq_zero,
    norm_eq_zero, WithLp.toLp_eq_zero, ← arnoldiMatrix_col_last_eq_zero_iff,
    show (arnoldiMatrix A b ((j : ℕ) + 1 + 1)).col (Fin.last ((j : ℕ) + 1)) = _ from
      arnoldiMatrix_col_succ A b j, smul_eq_zero, inv_eq_zero, RCLike.ofReal_eq_zero, norm_eq_zero,
    WithLp.toLp_eq_zero, or_self]

/-- **The computed Hessenberg matrix past the grade**: for every $\mathbf{A}$, the entry
$h_{a,c}$ of $\underline{\mathbf{H}}_q$ vanishes when $\nu \le a$ or $\nu \le c$, $\nu$ the
grade: its rows and columns from $\nu$ on are zero. -/
theorem mgsArnoldiHessenberg_apply_eq_zero_of_le (A : Matrix n n 𝕜) (b : n → 𝕜) {q : ℕ}
    {a : Fin (q + 1)} {c : Fin q} (h : krylovGrade A b ≤ a ∨ krylovGrade A b ≤ c) :
    mgsArnoldiHessenberg A b q a c = 0 := by
  rw [mgsArnoldiHessenberg_eq, Matrix.mul_assoc, conjTranspose_mul_apply,
    show (A * arnoldiMatrix A b q).col c = A *ᵥ (arnoldiMatrix A b q).col c from rfl,
    arnoldiMatrix_col_eq_col_last A b a, arnoldiMatrix_col_eq_col_last A b c]
  rcases h with h | h
  · rw [arnoldiMatrix_col_last_eq_zero_iff.mpr h, star_zero, zero_dotProduct]
  · rw [arnoldiMatrix_col_last_eq_zero_iff.mpr h, Matrix.mulVec_zero, dotProduct_zero]

/-- **Full column rank of the computed Hessenberg matrix**: for invertible $\mathbf{A}$,
$\underline{\mathbf{H}}_q$ has full column rank iff $q \le \nu$, the grade of $\mathbf{b}$. -/
theorem injective_mulVec_mgsArnoldiHessenberg_iff {A : Matrix n n 𝕜} (hA : IsUnit A)
    (b : n → 𝕜) (q : ℕ) :
    Function.Injective (mgsArnoldiHessenberg A b q).mulVec ↔ q ≤ krylovGrade A b := by
  constructor
  · intro h
    by_contra hq
    push Not at hq
    have h0 : mgsArnoldiHessenberg A b q *ᵥ Pi.single ⟨krylovGrade A b, hq⟩ 1 =
        mgsArnoldiHessenberg A b q *ᵥ 0 := by
      ext a
      rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.mulVec_zero, Pi.zero_apply]
      exact mgsArnoldiHessenberg_apply_eq_zero_of_le A b (Or.inr le_rfl)
    exact one_ne_zero (Pi.single_eq_zero_iff.mp (h h0))
  · intro hq x y hxy
    have hQ : HasOrthonormalCols (mgsArnoldiMatrix A b q) := by
      rw [mgsArnoldiMatrix_eq_arnoldiMatrix]
      exact hasOrthonormalCols_arnoldiMatrix_iff.mpr hq
    refine hQ.mulVec_injective (Matrix.mulVec_injective_iff_isUnit.mpr hA ?_)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, mul_mgsArnoldiMatrix, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, hxy]

end NLAlib
