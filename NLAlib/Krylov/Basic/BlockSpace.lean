/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import NLAlib.ForMathlib.Data.Matrix.Mul
public import NLAlib.Krylov.Basic.Space
public import NLAlib.Matrix.Functions.Polynomial

/-!
# Block Krylov matrices and block Krylov spaces

The block Krylov matrix $\mathbf{K}_q(\mathbf{A}, \mathbf{B}) =
[\mathbf{B}, \mathbf{A}\mathbf{B}, \dots, \mathbf{A}^{q-1}\mathbf{B}]$ of a square $\mathbf{A}$ and
a starting block $\mathbf{B} \in \Bbbk^{n \times p}$, with columns indexed by `Fin q × p`
(block $j$, column $c$ of $\mathbf{A}^j\mathbf{B}$), and its column space, the block Krylov space
$\mathcal{K}_q(\mathbf{A}, \mathbf{B})$. Its vectors are the sums
$\sum_c f_c(\mathbf{A})\mathbf{b}_c$ over the columns $\mathbf{b}_c$ of $\mathbf{B}$, one polynomial
of degree less than $q$ per column; in particular the range of $f(\mathbf{A})\mathbf{B}$ lies in it
for every polynomial of degree less than $q$, which is the only Krylov fact the analysis of
randomized block Krylov iteration uses.

The vector Krylov API (`NLAlib.krylovMatrix`, `NLAlib.krylovSpace`) is separate (design note
`docs/design/Krylov-Block.md`, BD1 (b)); the bridges say that the one-column block objects are the
vector ones and that a block Krylov space is the supremum of the vector Krylov spaces of its
columns.

The index $q$ counts blocks: $\mathcal{K}_0 = \{\mathbf{0}\}$, $\mathcal{K}_1$ is the range of
$\mathbf{B}$.

## Main definitions

* `NLAlib.blockKrylovMatrix`: the block Krylov matrix, columns indexed by `Fin q × p`.
* `NLAlib.blockKrylovSpace`: its column space.

## Main results

* `NLAlib.blockKrylovMatrix_replicateCol`, `NLAlib.blockKrylovSpace_replicateCol`: one column is the
  vector case.
* `NLAlib.blockKrylovSpace_eq_iSup_krylovSpace`: the supremum of the column Krylov spaces.
* `NLAlib.blockKrylovSpace_mono`, `NLAlib.blockKrylovSpace_succ`,
  `NLAlib.mulVec_mem_blockKrylovSpace_succ`: nesting, one block per step,
  $\mathbf{A}\mathcal{K}_q \subseteq \mathcal{K}_{q+1}$.
* `NLAlib.blockKrylovSpace_add_smul_one`: shift invariance.
* `NLAlib.blockKrylovMatrix_mul_mul`, `NLAlib.blockKrylovSpace_mul_mul`: the change of variables
  $\mathcal{K}_q(\mathbf{C}\mathbf{D}, \mathbf{C}\mathbf{B}) =
  \mathbf{C}\,\mathcal{K}_q(\mathbf{D}\mathbf{C}, \mathbf{B})$ for rectangular $\mathbf{C}$,
  $\mathbf{D}$.
* `NLAlib.mem_blockKrylovSpace_iff`, `NLAlib.exists_aeval_mul_eq_blockKrylovMatrix_mul`,
  `NLAlib.range_aeval_mul_le_blockKrylovSpace`: the polynomial description.
-/

@[expose] public section

open scoped Matrix
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq n]

-- Stage B0

omit [Fintype p] in
/-- The **block Krylov matrix** $\mathbf{K}_q(\mathbf{A}, \mathbf{B}) =
[\mathbf{B}, \mathbf{A}\mathbf{B}, \dots, \mathbf{A}^{q-1}\mathbf{B}]$: the column indexed by
$(j, c)$ is column $c$ of $\mathbf{A}^j\mathbf{B}$, for $j < q$. For $q = 0$ it has no columns.
[Saad2003, §6.12]; [TroppWebber2023, §5.3]. -/
def blockKrylovMatrix (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) : Matrix n (Fin q × p) 𝕜 :=
  Matrix.of fun i jc => (A ^ (jc.1 : ℕ) * B) i jc.2

omit [Fintype p] in
/-- The column $(j, c)$ of the block Krylov matrix is column $c$ of $\mathbf{A}^j\mathbf{B}$. -/
@[simp]
theorem blockKrylovMatrix_apply (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ} (i : n) (j : Fin q)
    (c : p) : blockKrylovMatrix A B q i (j, c) = (A ^ (j : ℕ) * B) i c :=
  rfl

/-- The **block Krylov space** $\mathcal{K}_q(\mathbf{A}, \mathbf{B}) =
\operatorname{range}[\mathbf{B}, \mathbf{A}\mathbf{B}, \dots, \mathbf{A}^{q-1}\mathbf{B}]$, the
column space of `blockKrylovMatrix A B q`; $\mathcal{K}_0 = \{\mathbf{0}\}$.
[Saad2003, §6.12]; [TroppWebber2023, §5.3]. -/
def blockKrylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) : Submodule 𝕜 (n → 𝕜) :=
  LinearMap.range (blockKrylovMatrix A B q).mulVecLin

/-- The block Krylov space is the span of the vectors $\mathbf{A}^j\mathbf{b}_c$, $j < q$. -/
private theorem blockKrylovSpace_eq_span (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace A B q =
      Submodule.span 𝕜 (Set.range fun jc : Fin q × p => A ^ (jc.1 : ℕ) *ᵥ B.col jc.2) := by
  rw [blockKrylovSpace, Matrix.range_mulVecLin]
  rfl

/-- The vector $\mathbf{A}^j\mathbf{b}_c$ lies in $\mathcal{K}_q(\mathbf{A}, \mathbf{B})$ for
$j < q$. -/
private theorem pow_mulVec_col_mem_blockKrylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜)
    {q j : ℕ} (hj : j < q) (c : p) : A ^ j *ᵥ B.col c ∈ blockKrylovSpace A B q := by
  rw [blockKrylovSpace_eq_span]
  exact Submodule.subset_span ⟨(⟨j, hj⟩, c), rfl⟩

/-! ### Bridges to the vector Krylov API -/

/-- **One column is the vector case**: the block Krylov matrix of the one-column block
$\mathbf{b}$ is the vector Krylov matrix, with its columns reindexed by `Fin q × Unit`. -/
theorem blockKrylovMatrix_replicateCol (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    blockKrylovMatrix A (Matrix.replicateCol Unit b) q =
      (krylovMatrix A b q).submatrix id Prod.fst := by
  rfl

/-- The block Krylov space of a one-column block is the vector Krylov space:
$\mathcal{K}_q(\mathbf{A}, [\mathbf{b}]) = \mathcal{K}_q(\mathbf{A}, \mathbf{b})$. -/
theorem blockKrylovSpace_replicateCol (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    blockKrylovSpace A (Matrix.replicateCol Unit b) q = krylovSpace A b q := by
  rw [blockKrylovSpace_eq_span, krylovSpace_eq_span]
  exact congrArg _ (Prod.fst_surjective.range_comp fun j : Fin q => A ^ (j : ℕ) *ᵥ b)

/-- **A block Krylov space is the sum of the Krylov spaces of its columns**:
$\mathcal{K}_q(\mathbf{A}, \mathbf{B}) = \sum_c \mathcal{K}_q(\mathbf{A}, \mathbf{b}_c)$, with
$\mathbf{b}_c$ the columns of $\mathbf{B}$. Every vector Krylov bound transfers to block methods
through it. -/
theorem blockKrylovSpace_eq_iSup_krylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace A B q = ⨆ c, krylovSpace A (B.col c) q := by
  refine le_antisymm ?_ (iSup_le fun c => ?_)
  · rw [blockKrylovSpace_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, c⟩, rfl⟩
    exact le_iSup (fun c => krylovSpace A (B.col c) q) c (pow_mulVec_mem_krylovSpace A _ j.isLt)
  · rw [krylovSpace_eq_span]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨j, rfl⟩
    exact pow_mulVec_col_mem_blockKrylovSpace A B j.isLt c

/-- The Krylov space of each column lies in the block Krylov space:
$\mathcal{K}_q(\mathbf{A}, \mathbf{b}_c) \subseteq \mathcal{K}_q(\mathbf{A}, \mathbf{B})$. -/
theorem krylovSpace_col_le_blockKrylovSpace (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ)
    (c : p) : krylovSpace A (B.col c) q ≤ blockKrylovSpace A B q := by
  rw [blockKrylovSpace_eq_iSup_krylovSpace]
  exact le_iSup (fun c => krylovSpace A (B.col c) q) c

/-! ### Structure -/

omit [Fintype p] in
/-- The first $q$ blocks of a longer block Krylov matrix form the shorter one. -/
theorem blockKrylovMatrix_submatrix_castLE (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q q' : ℕ}
    (h : q ≤ q') :
    (blockKrylovMatrix A B q').submatrix id (Prod.map (Fin.castLE h) id) =
      blockKrylovMatrix A B q := by
  rfl

/-- The block Krylov spaces increase with $q$. -/
theorem blockKrylovSpace_mono (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) :
    Monotone (blockKrylovSpace A B) := by
  intro q q' h
  rw [blockKrylovSpace_eq_span A B q]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨j, c⟩, rfl⟩
  exact pow_mulVec_col_mem_blockKrylovSpace A B (j.isLt.trans_le h) c

/-- The empty block Krylov space. -/
@[simp]
theorem blockKrylovSpace_zero (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) :
    blockKrylovSpace A B 0 = ⊥ := by
  rw [blockKrylovSpace_eq_span, Set.range_eq_empty, Submodule.span_empty]

/-- One block: $\mathcal{K}_1(\mathbf{A}, \mathbf{B}) = \operatorname{range}\mathbf{B}$. -/
theorem blockKrylovSpace_one (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) :
    blockKrylovSpace A B 1 = LinearMap.range B.mulVecLin := by
  rw [blockKrylovSpace_eq_span, Matrix.range_mulVecLin]
  have h : (fun jc : Fin 1 × p => A ^ (jc.1 : ℕ) *ᵥ B.col jc.2) = B.col ∘ Prod.snd := by
    funext ⟨j, c⟩
    rw [Fin.fin_one_eq_zero j, Fin.val_zero, pow_zero, Matrix.one_mulVec]
    rfl
  rw [h, Prod.snd_surjective.range_comp]

/-- One step adds one block: $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{B}) =
\mathcal{K}_q(\mathbf{A}, \mathbf{B}) + \operatorname{range}(\mathbf{A}^q\mathbf{B})$. -/
theorem blockKrylovSpace_succ (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace A B (q + 1) =
      blockKrylovSpace A B q ⊔ LinearMap.range (A ^ q * B).mulVecLin := by
  rw [blockKrylovSpace_eq_span, blockKrylovSpace_eq_span, Matrix.range_mulVecLin,
    ← Submodule.span_union]
  congr 1
  ext x
  simp only [Set.mem_range, Set.mem_union, Prod.exists]
  constructor
  · rintro ⟨i, c, rfl⟩
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact Or.inl ⟨j, c, rfl⟩
    · exact Or.inr ⟨c, rfl⟩
  · rintro (⟨i, c, rfl⟩ | ⟨c, rfl⟩)
    · exact ⟨i.castSucc, c, rfl⟩
    · exact ⟨Fin.last q, c, rfl⟩

/-- $\mathbf{A}\mathcal{K}_q(\mathbf{A}, \mathbf{B}) \subseteq \mathcal{K}_{q+1}(\mathbf{A},
\mathbf{B})$, the invariance a block Arnoldi relation rests on. -/
theorem mulVec_mem_blockKrylovSpace_succ {A : Matrix n n 𝕜} {B : Matrix n p 𝕜} {q : ℕ}
    {x : n → 𝕜} (hx : x ∈ blockKrylovSpace A B q) : A *ᵥ x ∈ blockKrylovSpace A B (q + 1) := by
  have hle : blockKrylovSpace A B q ≤ (blockKrylovSpace A B (q + 1)).comap A.mulVecLin := by
    rw [blockKrylovSpace_eq_span A B q]
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨j, c⟩, rfl⟩
    change A *ᵥ (A ^ (j : ℕ) *ᵥ B.col c) ∈ blockKrylovSpace A B (q + 1)
    rw [Matrix.mulVec_mulVec, ← pow_succ']
    exact pow_mulVec_col_mem_blockKrylovSpace A B (Nat.succ_lt_succ j.isLt) c
  exact hle hx

/-- **Shift invariance**: $\mathcal{K}_q(\mathbf{A} + s\mathbf{I}, \mathbf{B}) =
\mathcal{K}_q(\mathbf{A}, \mathbf{B})$ for every real shift $s$. -/
theorem blockKrylovSpace_add_smul_one (A : Matrix n n 𝕜) (s : ℝ) (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace (A + s • (1 : Matrix n n 𝕜)) B q = blockKrylovSpace A B q := by
  simp_rw [blockKrylovSpace_eq_iSup_krylovSpace, krylovSpace_add_smul_one]

omit [Fintype p] in
/-- **Block Krylov matrices under a change of variables**, for rectangular
$\mathbf{C} \in \Bbbk^{m \times n}$ and $\mathbf{D} \in \Bbbk^{n \times m}$:
$$\mathbf{K}_q(\mathbf{C}\mathbf{D}, \mathbf{C}\mathbf{B}) =
\mathbf{C}\,\mathbf{K}_q(\mathbf{D}\mathbf{C}, \mathbf{B})\,,$$
since $(\mathbf{C}\mathbf{D})^j\mathbf{C} = \mathbf{C}(\mathbf{D}\mathbf{C})^j$. At
$\mathbf{C} = \mathbf{A}$, $\mathbf{D} = \mathbf{A}^{\mathsf{H}}$ it is
$\mathbf{K}_q(\mathbf{A}\mathbf{A}^{\mathsf{H}}, \mathbf{A}\mathbf{\Omega}) =
\mathbf{A}\,\mathbf{K}_q(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{\Omega})$.
[TroppWebber2023, §5.3]. -/
theorem blockKrylovMatrix_mul_mul [DecidableEq m] (C : Matrix m n 𝕜) (D : Matrix n m 𝕜)
    (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovMatrix (C * D) (C * B) q = C * blockKrylovMatrix (D * C) B q := by
  ext i ⟨j, c⟩
  rw [blockKrylovMatrix_apply, ← Matrix.mul_assoc, Matrix.mul_pow_mul, Matrix.mul_assoc]
  rfl

/-- **Block Krylov spaces under a change of variables**:
$\mathcal{K}_q(\mathbf{C}\mathbf{D}, \mathbf{C}\mathbf{B}) =
\mathbf{C}\,\mathcal{K}_q(\mathbf{D}\mathbf{C}, \mathbf{B})$.
[TroppWebber2023, §5.3]. -/
theorem blockKrylovSpace_mul_mul [DecidableEq m] (C : Matrix m n 𝕜) (D : Matrix n m 𝕜)
    (B : Matrix n p 𝕜) (q : ℕ) :
    blockKrylovSpace (C * D) (C * B) q = (blockKrylovSpace (D * C) B q).map C.mulVecLin := by
  rw [blockKrylovSpace, blockKrylovSpace, blockKrylovMatrix_mul_mul, Matrix.mulVecLin_mul,
    LinearMap.range_comp]

/-- The block Krylov matrix has rank at most the number of its columns,
$\operatorname{rank}\mathbf{K}_q(\mathbf{A}, \mathbf{B}) \le q\,\lvert p \rvert$. -/
theorem rank_blockKrylovMatrix_le (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) (q : ℕ) :
    (blockKrylovMatrix A B q).rank ≤ q * Fintype.card p := by
  simpa using (blockKrylovMatrix A B q).rank_le_card_width

/-! ### Polynomials -/

/-- **The polynomial description of the block Krylov space**: $\mathbf{x} \in
\mathcal{K}_q(\mathbf{A}, \mathbf{B})$ exactly when
$\mathbf{x} = \sum_c f_c(\mathbf{A})\mathbf{b}_c$ for polynomials $f_c \in \Bbbk[X]$ of degree
less than $q$, one per column $\mathbf{b}_c$ of $\mathbf{B}$. [Saad2003, §6.12].
Port of `NLAlib.mem_blockKrylovSpace_iff` (prototype, `Krylov/Spaces/Block.lean`). -/
theorem mem_blockKrylovSpace_iff {A : Matrix n n 𝕜} {B : Matrix n p 𝕜} {q : ℕ} {x : n → 𝕜} :
    x ∈ blockKrylovSpace A B q ↔
      ∃ f : p → 𝕜[X], (∀ c, (f c).degree < q) ∧ ∑ c, aeval A (f c) *ᵥ B.col c = x := by
  constructor
  · intro hx
    have hx' : x ∈ ⨆ c ∈ Finset.univ, krylovSpace A (B.col c) q := by
      simpa [blockKrylovSpace_eq_iSup_krylovSpace] using hx
    obtain ⟨μ, rfl⟩ := (Submodule.mem_iSup_finset_iff_exists_sum _ x).1 hx'
    choose f hf using fun c => mem_krylovSpace_iff.1 (μ c).2
    exact ⟨f, fun c => (hf c).1, Finset.sum_congr rfl fun c _ => (hf c).2⟩
  · rintro ⟨f, hf, rfl⟩
    exact Submodule.sum_mem _ fun c _ => krylovSpace_col_le_blockKrylovSpace A B q c
      (mem_krylovSpace_iff.2 ⟨f c, hf c, rfl⟩)

/-- A polynomial filter of degree less than $q$, with coefficients in any subfield, applied to the
block is a block Krylov combination: $f(\mathbf{A})\mathbf{B} = \mathbf{K}_q(\mathbf{A},
\mathbf{B})\,\mathbf{C}$ for some coefficient matrix $\mathbf{C}$. -/
theorem exists_aeval_mul_eq_blockKrylovMatrix_mul {R : Type*} [CommSemiring R] [Algebra R 𝕜]
    (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ} {f : R[X]} (hf : f.degree < q) :
    ∃ C : Matrix (Fin q × p) p 𝕜, aeval A f * B = blockKrylovMatrix A B q * C := by
  choose v hv using fun c => krylovSpace_col_le_blockKrylovSpace A B q c
    (aeval_mulVec_mem_krylovSpace A (B.col c) hf)
  refine ⟨Matrix.of fun jc c => v c jc, ?_⟩
  ext i c
  exact (congrFun (hv c) i).symm

/-- **The range of a polynomial filter lies in the block Krylov space**: for $\deg f < q$,
$\operatorname{range}(f(\mathbf{A})\mathbf{B}) \subseteq \mathcal{K}_q(\mathbf{A}, \mathbf{B})$.
[TroppWebber2023, §9.3 (proof)].
Port of `NLAlib.range_aeval_mul_le_blockKrylovSpace` (prototype). -/
theorem range_aeval_mul_le_blockKrylovSpace {R : Type*} [CommSemiring R] [Algebra R 𝕜]
    (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ} {f : R[X]} (hf : f.degree < q) :
    LinearMap.range (aeval A f * B).mulVecLin ≤ blockKrylovSpace A B q := by
  obtain ⟨C, hC⟩ := exists_aeval_mul_eq_blockKrylovMatrix_mul A B hf
  rw [hC, Matrix.mulVecLin_mul, LinearMap.range_comp]
  exact LinearMap.map_le_range

/-- The range of a filtered sketch lies in that of the block Krylov sketch: for $\deg f < q$ and
any left factor $\mathbf{C}$,
$\operatorname{range}(\mathbf{C}f(\mathbf{A})\mathbf{B}) \subseteq
\operatorname{range}(\mathbf{C}\mathbf{K}_q(\mathbf{A}, \mathbf{B}))$. -/
theorem range_mul_aeval_mul_le_range_mul_blockKrylovMatrix {R : Type*} [CommSemiring R]
    [Algebra R 𝕜] {l : Type*} (C : Matrix l n 𝕜) (A : Matrix n n 𝕜) (B : Matrix n p 𝕜) {q : ℕ}
    {f : R[X]} (hf : f.degree < q) :
    LinearMap.range (C * aeval A f * B).mulVecLin ≤
      LinearMap.range (C * blockKrylovMatrix A B q).mulVecLin := by
  obtain ⟨D, hD⟩ := exists_aeval_mul_eq_blockKrylovMatrix_mul A B hf
  exact range_le_iff_exists_mul.mpr ⟨D, by rw [Matrix.mul_assoc, hD, Matrix.mul_assoc]⟩

end NLAlib
