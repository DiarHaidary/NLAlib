/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec
public import NLAlib.Matrix.Computation.Primitives
public import NLAlib.Matrix.Factorizations.QR
public import Mathlib.Logic.Equiv.Fin.Basic
public import NLAlib.Computation.Contract

/-!
# Contracts for black-box matrix multiplication and QR kernels

A program calls a black-box kernel (`NLAlib.Computation.Stmt.kcall`) on contiguous blocks of
words, and a result about it quantifies over every interpretation whose kernels meet a contract
([Shah2024, Definition 1.1], [Shah2024, Definition 1.2]; design note
`docs/design/Computation-DynamicPrograms.md`, §4.3). This file states those contracts in two
parts.

* **What the kernel computes**, functionally: `NLAlib.Computation.IsMatMulKernel I o L mm` says
  that kernel `o` of `I` reads its two operand blocks as matrices of stored entries, applies a
  routine `mm` on matrices, and writes the product block; `NLAlib.Computation.IsQRKernel` the
  same for a QR routine. A matrix with $l$ rows and $m$ columns of entries in `E` is stored
  packed and column-major, $w$ words per entry (`NLAlib.Computation.EntryLayout`): one word for a
  real entry (`NLAlib.Computation.realLayout`), two interleaved words for a complex entry stored
  as a pair (`NLAlib.Computation.pairLayout`). The operands are contiguous blocks, with no
  leading dimension.
* **How accurate the routine is**, normwise through a decoding of stored entries:
  `NLAlib.IsMatMulErr` and `NLAlib.IsQRErr`, the contracts of the floating-point machine
  `NLAlib.FloatMachine` (`NLAlib/Matrix/Computation/Primitives.lean`), on the routine types
  `NLAlib.MatMulMap` and `NLAlib.QRMap` defined there.

The exact routines `NLAlib.Computation.exactMM` (the product) and `NLAlib.Computation.exactQR` (a
QR factorization chosen from `NLAlib.exists_hasOrthonormalCols_mul_isUpperTrapezoidal`) are the
witnesses that the contracts are satisfiable.

## Main definitions

* `NLAlib.Computation.EntryLayout`, `NLAlib.Computation.realLayout`,
  `NLAlib.Computation.pairLayout`, `NLAlib.Computation.EntryLayout.toMatrix`,
  `NLAlib.Computation.EntryLayout.toArray`, `NLAlib.Computation.EntryLayout.Holds`: packed
  column-major storage of a matrix.
* `NLAlib.Computation.mmShape`, `NLAlib.Computation.qrShape`, `NLAlib.Computation.liftMM`,
  `NLAlib.Computation.liftQR`: a routine as a kernel on blocks.
* `NLAlib.Computation.IsMatMulKernel`, `NLAlib.Computation.IsQRKernel`: the kernel contracts.
* `NLAlib.Computation.exactMM`, `NLAlib.Computation.exactQR`: the exact routines.

## Main results

* `NLAlib.Computation.EntryLayout.size_toArray`, `NLAlib.Computation.EntryLayout.toMatrix_toArray`:
  packed storage.
* `NLAlib.Computation.realLayout.get_put`, `NLAlib.Computation.pairLayout.get_put`: the two
  layouts read back.
* `NLAlib.Computation.isMatMulErr_exactMM`, `NLAlib.Computation.isQRErr_exactQR`: the exact
  witnesses.
* `NLAlib.Computation.isMatMulKernel_withKernel`, `NLAlib.Computation.isQRKernel_withKernel`:
  lifted routines meet the kernel contracts.
* `NLAlib.Computation.IsMatMulKernel.kcallStore_eq`, `NLAlib.Computation.IsQRKernel.kcallStore_eq`:
  a kernel call writes the routine's output.
* `NLAlib.Computation.EntryLayout.holds_iff_readBlock_eq_some`,
  `NLAlib.Computation.pairLayout.holds_iff`: holding a matrix is reading its packed storage.
* `NLAlib.Computation.EntryLayout.holds_of_writeBlock_eq_some`,
  `NLAlib.Computation.EntryLayout.holds_inputState`,
  `NLAlib.Computation.EntryLayout.Holds.of_forall_read_eq`: how a block comes to hold a matrix.
* `NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some`,
  `NLAlib.Computation.IsQRKernel.holds_of_kcallStore_eq_some`: kernel calls on held matrices.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

/-! ### Exact routines -/

variable {𝕜 : Type} [RCLike 𝕜]

/-- The **exact product**, the witness that `NLAlib.IsMatMulErr` is satisfiable. -/
def exactMM : MatMulMap 𝕜 := fun A B => A * B

/-- An **exact QR factorization**: $\mathbf{A} = \mathbf{Q}\mathbf{R}$ with $\mathbf{Q}$ unitary
and $\mathbf{R}$ upper trapezoidal, chosen from
`NLAlib.exists_hasOrthonormalCols_mul_isUpperTrapezoidal`; the witness that
`NLAlib.IsQRErr` is satisfiable. -/
noncomputable def exactQR : QRMap 𝕜 := fun A =>
  ((exists_hasOrthonormalCols_mul_isUpperTrapezoidal A).choose,
    (exists_hasOrthonormalCols_mul_isUpperTrapezoidal A).choose_spec.choose)

/-! ### Packed storage of a matrix in a block -/

/-- **The storage of one matrix entry** of type `E` in `width` consecutive words of type `K`:
`get` reads the entry from its words and `put` writes them. -/
structure EntryLayout (K E : Type) where
  /-- The number of words of one entry. -/
  width : ℕ
  /-- The entry stored in its words. -/
  get : (Fin width → K) → E
  /-- The words of an entry. -/
  put : E → Fin width → K

variable {K E : Type}

/-- A real entry in one word. -/
def realLayout : EntryLayout K K := ⟨1, fun f => f 0, fun x _ => x⟩

/-- A complex entry as a pair of words, real part first (interleaved storage). -/
def pairLayout : EntryLayout K (K × K) := ⟨2, fun f => (f 0, f 1), fun z => ![z.1, z.2]⟩

/-- The $l \times m$ matrix stored packed and column-major in the block `X`: entry $(i, j)$ in
the `L.width` words from word `L.width * (i + l * j)`; words past the end of the block read as
`default`. -/
def EntryLayout.toMatrix [Inhabited K] (L : EntryLayout K E) (l m : ℕ) (X : Array K) :
    Matrix (Fin l) (Fin m) E :=
  Matrix.of fun i j => L.get fun t => X.getD (L.width * (i + l * j) + t) default

/-- The block of `m * l * L.width` words storing the $l \times m$ matrix `Y` packed and
column-major: word `t + L.width * (i + l * j)` is word `t` of entry $(i, j)$. -/
def EntryLayout.toArray (L : EntryLayout K E) {l m : ℕ} (Y : Matrix (Fin l) (Fin m) E) :
    Array K :=
  Array.ofFn fun k : Fin (m * l * L.width) =>
    let et := finProdFinEquiv.symm k
    let ji := finProdFinEquiv.symm et.1
    L.put (Y ji.2 ji.1) et.2

variable {P : Type} [DecidableEq P] in
/-- Buffer `b` of the store `s` **holds the $l \times m$ matrix `Y`** at tag `p`, packed and
column-major in the layout `L` from offset `off`: word `t` of entry $(i, j)$ is at
`off + (L.width * (i + l * j) + t)` and holds word `t` of `L.put (Y i j)`. For the interleaved
layout `NLAlib.Computation.pairLayout`, the real part of entry $(i, j)$ is at $2(i + lj)$ from the
offset and the imaginary part at the next word. -/
def EntryLayout.Holds (L : EntryLayout K E) {l m : ℕ} (s : Store P K) (p : P) (b off : ℕ)
    (Y : Matrix (Fin l) (Fin m) E) : Prop :=
  ∀ (i : Fin l) (j : Fin m) (t : Fin L.width),
    s.read p b (off + (L.width * (i + l * j) + t)) = some (L.put (Y i j) t)

/-! ### Routines as kernels on blocks -/

/-- The block shape of a matrix-multiplication kernel at the dimensions `[l, m, n]`: inputs an
$l \times m$ and an $m \times n$ block, output an $l \times n$ block, `L.width` words per entry;
no blocks at other dimension lists. -/
def mmShape (L : EntryLayout K E) : List ℕ → List ℕ × List ℕ
  | [l, m, n] => ([m * l * L.width, n * m * L.width], [n * l * L.width])
  | _ => ([], [])

/-- The block shape of a QR kernel at the dimensions `[m, n]`: input an $m \times n$ block,
outputs the $m \times m$ and $m \times n$ factors; no blocks at other dimension lists. -/
def qrShape (L : EntryLayout K E) : List ℕ → List ℕ × List ℕ
  | [m, n] => ([n * m * L.width], [m * m * L.width, n * m * L.width])
  | _ => ([], [])

/-- **A matrix-multiplication routine as a kernel**: at the dimensions `[l, m, n]`, the two input
blocks read as matrices in the layout `L`, their product by `mm` written as one block; `none` at
other dimension lists or numbers of blocks. -/
def liftMM [Inhabited K] (L : EntryLayout K E) (mm : MatMulMap E) :
    List ℕ → List (Array K) → Option (List (Array K))
  | [l, m, n], [A, B] => some [L.toArray (mm (L.toMatrix l m A) (L.toMatrix m n B))]
  | _, _ => none

/-- **A QR routine as a kernel**: at the dimensions `[m, n]`, the input block read as a matrix in
the layout `L`, its two factors by `qr` written as two blocks; `none` at other dimension lists or
numbers of blocks. -/
def liftQR [Inhabited K] (L : EntryLayout K E) (qr : QRMap E) :
    List ℕ → List (Array K) → Option (List (Array K))
  | [m, n], [A] => some [L.toArray (qr (L.toMatrix m n A)).1, L.toArray (qr (L.toMatrix m n A)).2]
  | _, _ => none

variable {P ι C : Type}

/-- **Kernel `o` of `I` is the routine `mm`**, functionally on stored entries in the layout `L`:
its kernel is `NLAlib.Computation.liftMM L mm` and its shape `NLAlib.Computation.mmShape L`. A
contract on `mm` (such as `NLAlib.IsMatMulErr`) then bounds the kernel's error. -/
def IsMatMulKernel [Inhabited K] (I : Interp P ι K C) (o : ι) (L : EntryLayout K E)
    (mm : MatMulMap E) : Prop :=
  I.kernel o = liftMM L mm ∧ I.kshape o = mmShape L

/-- **Kernel `o` of `I` is the routine `qr`**, functionally on stored entries in the layout `L`:
its kernel is `NLAlib.Computation.liftQR L qr` and its shape `NLAlib.Computation.qrShape L`. A
contract on `qr` (such as `NLAlib.IsQRErr`) then bounds the kernel's error. -/
def IsQRKernel [Inhabited K] (I : Interp P ι K C) (o : ι) (L : EntryLayout K E)
    (qr : QRMap E) : Prop :=
  I.kernel o = liftQR L qr ∧ I.kshape o = qrShape L

/-! ### Storage, witnesses and kernel calls -/

section Results

variable {K E : Type}

/-- The length of a stored matrix: the packed storage of an $l \times m$ matrix in the layout
`L` has `m * l * L.width` words. No printed source. -/
theorem EntryLayout.size_toArray (L : EntryLayout K E) {l m : ℕ}
    (Y : Matrix (Fin l) (Fin m) E) : (L.toArray Y).size = m * l * L.width := by
  simp [EntryLayout.toArray]

/-- Packed storage reads back: for a layout whose `get` inverts its `put`, reading the packed
storage of an $l \times m$ matrix as an $l \times m$ matrix gives the matrix back. No printed
source. -/
theorem EntryLayout.toMatrix_toArray [Inhabited K] (L : EntryLayout K E)
    (hL : ∀ e, L.get (L.put e) = e) {l m : ℕ} (Y : Matrix (Fin l) (Fin m) E) :
    L.toMatrix l m (L.toArray Y) = Y := by
  ext i j
  simp only [EntryLayout.toMatrix, Matrix.of_apply]
  convert hL (Y i j)
  rename_i t
  have hi : i + l * j + 1 ≤ m * l := by nlinarith [i.isLt, j.isLt]
  have hlt : L.width * (i + l * j) + t < m * l * L.width := by
    nlinarith [Nat.mul_le_mul_left L.width hi, t.isLt]
  have e1 : (finProdFinEquiv.symm ⟨L.width * (i + l * j) + t, hlt⟩ : Fin (m * l) × Fin L.width)
      = (⟨i + l * j, by omega⟩, t) := by
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    simp [finProdFinEquiv]
    ring
  have e2 : (finProdFinEquiv.symm (⟨i + l * j, by omega⟩ : Fin (m * l))
      : Fin m × Fin l) = (j, i) := by
    rw [Equiv.symm_apply_eq]
    apply Fin.ext
    simp [finProdFinEquiv]
  simp only [EntryLayout.toArray, Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, hlt, dif_pos,
    e1, e2, Option.getD_some]

/-- The real layout reads back: one word holds a real entry. No printed source. -/
theorem realLayout.get_put (e : K) :
    (realLayout (K := K)).get ((realLayout (K := K)).put e) = e := by
  rfl

/-- The interleaved layout reads back: two words hold a complex entry as a pair. No printed
source. -/
theorem pairLayout.get_put (e : K × K) :
    (pairLayout (K := K)).get ((pairLayout (K := K)).put e) = e := by
  rfl

variable {𝕜 : Type} [RCLike 𝕜]

/-- The exact product meets the product contract: for every unit roundoff $u \ge 0$, floor
$\tau$, range $\Omega$ and constants $\mu \ge 0$, the exact product
`NLAlib.Computation.exactMM` meets `NLAlib.IsMatMulErr` with the identity decoding.
No printed source. -/
theorem isMatMulErr_exactMM {u : ℝ} (hu : 0 ≤ u) (τ Ω : ℝ) {μ : ℕ → ℝ} (hμ : ∀ d, 0 ≤ μ d) :
    IsMatMulErr (fun x : 𝕜 => x) u τ Ω μ exactMM := by
  refine ⟨fun A B _ => ?_, fun A B hB => ?_⟩
  · simp only [exactMM, Matrix.map_id', sub_self, specNorm_zero]
    exact mul_nonneg (mul_nonneg (hμ _) hu)
      (le_max_of_le_left (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _)))
  · simp only [exactMM, Matrix.map_id'] at hB ⊢
    rw [hB]
    exact Matrix.isHermitian_mul_conjTranspose_self _

/-- The exact QR factorization meets the QR contract: for every unit roundoff $u \ge 0$,
floor $\tau$, range $\Omega$ and constants $\mu \ge 0$, the exact factorization
`NLAlib.Computation.exactQR` meets `NLAlib.IsQRErr` with the identity decoding.
No printed source. -/
theorem isQRErr_exactQR {u : ℝ} (hu : 0 ≤ u) (τ Ω : ℝ) {μ : ℕ → ℝ} (hμ : ∀ d, 0 ≤ μ d) :
    IsQRErr (fun x : 𝕜 => x) u τ Ω μ exactQR := by
  intro m n A _
  obtain ⟨hQ, hR, hA⟩ :=
    (exists_hasOrthonormalCols_mul_isUpperTrapezoidal A).choose_spec.choose_spec
  simp only [exactQR, Matrix.map_id']
  refine ⟨hR, (exists_hasOrthonormalCols_mul_isUpperTrapezoidal A).choose, hQ, ?_, ?_⟩
  · rw [sub_self, specNorm_zero]
    exact mul_nonneg (hμ _) hu
  · rw [sub_eq_zero.mpr hA, specNorm_zero]
    exact mul_nonneg (mul_nonneg (hμ _) hu) (le_max_of_le_left (specNorm_nonneg _))

variable {P ι C : Type}

/-- A lifted product routine meets the kernel contract: the interpretation `I` with kernel
`o` replaced by the routine `mm` lifted to blocks in the layout `L`, of the product shape, meets
`NLAlib.Computation.IsMatMulKernel` at `o`. No printed source. -/
theorem isMatMulKernel_withKernel [DecidableEq ι] [Inhabited K] (I : Interp P ι K C) (o : ι)
    (L : EntryLayout K E) (mm : MatMulMap E) :
    IsMatMulKernel (I.withKernel o (liftMM L mm) (mmShape L)) o L mm := by
  exact ⟨Function.update_self .., Function.update_self ..⟩

/-- A lifted QR routine meets the kernel contract: the interpretation `I` with kernel `o`
replaced by the routine `qr` lifted to blocks in the layout `L`, of the QR shape, meets
`NLAlib.Computation.IsQRKernel` at `o`. No printed source. -/
theorem isQRKernel_withKernel [DecidableEq ι] [Inhabited K] (I : Interp P ι K C) (o : ι)
    (L : EntryLayout K E) (qr : QRMap E) :
    IsQRKernel (I.withKernel o (liftQR L qr) (qrShape L)) o L qr := by
  exact ⟨Function.update_self .., Function.update_self ..⟩

variable [DecidableEq P]

/-- A product kernel call writes the product: if kernel `o` of `I` is the routine `mm` in the
layout `L` (`NLAlib.Computation.IsMatMulKernel`), a call at the dimensions $[l, m, n]$ with input
operands $a$, $b$ and output operand $c$, at tag `p`, whose input blocks read as $X$ and $Y$ and
whose output block is disjoint from both input blocks, is the block write at $c$ of the packed
storage of `mm` applied to $X$ and $Y$ read as $l \times m$ and $m \times n$ matrices. No printed
source. -/
theorem IsMatMulKernel.kcallStore_eq [Inhabited K] {I : Interp P ι K C} {o : ι}
    {L : EntryLayout K E} {mm : MatMulMap E} (h : IsMatMulKernel I o L mm) (p : P) {l m n : ℕ}
    {a b c : ℕ × ℕ} {s : Store P K} {X Y : Array K}
    (hX : s.readBlock p a.1 a.2 (m * l * L.width) = some X)
    (hY : s.readBlock p b.1 b.2 (n * m * L.width) = some Y)
    (hca : blockDisjoint (c.1, c.2, n * l * L.width) (a.1, a.2, m * l * L.width) = true)
    (hcb : blockDisjoint (c.1, c.2, n * l * L.width) (b.1, b.2, n * m * L.width) = true) :
    I.kcallStore o p [l, m, n] [a, b] [c] s =
      s.writeBlock p c.1 c.2 (L.toArray (mm (L.toMatrix l m X) (L.toMatrix m n Y))) := by
  obtain ⟨hk, hs⟩ := h
  unfold Interp.kcallStore
  simp only [hs, mmShape, kcallBlocks, List.zipWith]
  rw [if_pos ⟨rfl, rfl, List.pairwise_singleton _ _, by
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    subst hx
    rcases hy with rfl | rfl
    · exact hca
    · exact hcb⟩]
  simp only [Store.readBlocks, List.mapM_cons, List.mapM_nil, hX, hY, hk, liftMM, bind,
    Option.bind, pure]
  simp only [Store.writeBlocks, EntryLayout.size_toArray, if_true, Option.bind_fun_some]

/-- A QR kernel call writes the factors: if kernel `o` of `I` is the routine `qr` in the layout
`L` (`NLAlib.Computation.IsQRKernel`), a call at the dimensions $[m, n]$ with input operand $a$
and output operands $q$, $r$, at tag `p`, whose input block reads as $X$, whose two output blocks
are disjoint and each disjoint from the input block, writes the packed storage of the two factors
of `qr` applied to $X$ read as an $m \times n$ matrix, first at $q$ and then at $r$. No printed
source. -/
theorem IsQRKernel.kcallStore_eq [Inhabited K] {I : Interp P ι K C} {o : ι}
    {L : EntryLayout K E} {qr : QRMap E} (h : IsQRKernel I o L qr) (p : P) {m n : ℕ}
    {a q r : ℕ × ℕ} {s : Store P K} {X : Array K}
    (hX : s.readBlock p a.1 a.2 (n * m * L.width) = some X)
    (hqr : blockDisjoint (q.1, q.2, m * m * L.width) (r.1, r.2, n * m * L.width) = true)
    (hqa : blockDisjoint (q.1, q.2, m * m * L.width) (a.1, a.2, n * m * L.width) = true)
    (hra : blockDisjoint (r.1, r.2, n * m * L.width) (a.1, a.2, n * m * L.width) = true) :
    I.kcallStore o p [m, n] [a] [q, r] s =
      (s.writeBlock p q.1 q.2 (L.toArray (qr (L.toMatrix m n X)).1)).bind fun s' =>
        s'.writeBlock p r.1 r.2 (L.toArray (qr (L.toMatrix m n X)).2) := by
  obtain ⟨hk, hs⟩ := h
  unfold Interp.kcallStore
  simp only [hs, qrShape, kcallBlocks, List.zipWith]
  rw [if_pos ⟨rfl, rfl, List.pairwise_pair.mpr hqr, by
    intro x hx y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    subst hy
    rcases hx with rfl | rfl
    · exact hqa
    · exact hra⟩]
  simp only [Store.readBlocks, List.mapM_cons, List.mapM_nil, hX, hk, liftQR, bind, Option.bind,
    pure]
  simp only [Store.writeBlocks, EntryLayout.size_toArray, if_true, Option.bind_fun_some]
  rfl

end Results

end NLAlib.Computation

namespace NLAlib.Computation

variable {P K E : Type} [DecidableEq P]

/-- Holding a matrix is reading its packed storage: for a layout whose `get` inverts its
`put`, buffer `b` holds the $l \times m$ matrix $\mathbf{Y}$ from offset `off` exactly when the
block of `m * l * L.width` words there reads as the packed storage of $\mathbf{Y}$. No printed
source. -/
theorem EntryLayout.holds_iff_readBlock_eq_some (L : EntryLayout K E) {l m : ℕ} (s : Store P K)
    (p : P) (b off : ℕ) (Y : Matrix (Fin l) (Fin m) E) :
    L.Holds s p b off Y ↔ s.readBlock p b off (m * l * L.width) = some (L.toArray Y) := by
  have hlt : ∀ (i : Fin l) (j : Fin m) (t : Fin L.width),
      L.width * (i + l * j) + t < m * l * L.width := by
    intro i j t
    have hi : i + l * j + 1 ≤ m * l := by nlinarith [i.isLt, j.isLt]
    nlinarith [Nat.mul_le_mul_left L.width hi, t.isLt]
  have hget : ∀ (i : Fin l) (j : Fin m) (t : Fin L.width),
      (L.toArray Y)[L.width * (i + l * j) + t]? = some (L.put (Y i j) t) := by
    intro i j t
    have hi : i + l * j + 1 ≤ m * l := by nlinarith [i.isLt, j.isLt]
    have hl := hlt i j t
    have e1 : (finProdFinEquiv.symm ⟨L.width * (i + l * j) + t, hl⟩ : Fin (m * l) × Fin L.width)
        = (⟨i + l * j, by omega⟩, t) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [finProdFinEquiv]
      ring
    have e2 : (finProdFinEquiv.symm (⟨i + l * j, by omega⟩ : Fin (m * l))
        : Fin m × Fin l) = (j, i) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [finProdFinEquiv]
    simp only [EntryLayout.toArray, Array.getElem?_ofFn, hl, dif_pos, e1, e2]
  have hdec : ∀ k (hk : k < m * l * L.width), ∃ (i : Fin l) (j : Fin m) (t : Fin L.width),
      k = L.width * (i + l * j) + t := by
    intro k hk
    have hw : 0 < L.width := by
      rcases Nat.eq_zero_or_pos L.width with h0 | h0
      · simp [h0] at hk
      · exact h0
    have hl : 0 < l := by
      rcases Nat.eq_zero_or_pos l with h0 | h0
      · simp [h0] at hk
      · exact h0
    refine ⟨⟨k / L.width % l, Nat.mod_lt _ hl⟩, ⟨k / L.width / l, ?_⟩,
      ⟨k % L.width, Nat.mod_lt _ hw⟩, ?_⟩
    · apply Nat.div_lt_of_lt_mul
      apply Nat.div_lt_of_lt_mul
      linarith [hk, show L.width * (l * m) = m * l * L.width by ring]
    · change k = L.width * (k / L.width % l + l * (k / L.width / l)) + k % L.width
      rw [Nat.mod_add_div]
      exact (Nat.div_add_mod k L.width).symm
  unfold EntryLayout.Holds
  constructor
  · intro h
    by_cases hz : m * l * L.width = 0
    · have hY : L.toArray Y = #[] :=
        Array.eq_empty_of_size_eq_zero (by rw [EntryLayout.size_toArray, hz])
      rw [hY, hz]
      simp [Store.readBlock]
    · have hl : 0 < l := by
        rcases Nat.eq_zero_or_pos l with h0 | h0
        · simp [h0] at hz
        · exact h0
      have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · simp [h0] at hz
        · exact h0
      have hw : 0 < L.width := by
        rcases Nat.eq_zero_or_pos L.width with h0 | h0
        · simp [h0] at hz
        · exact h0
      have hr : ∀ k, k < m * l * L.width → s.read p b (off + k)
          = some (((L.toArray Y)[k]?).getD (L.put (Y ⟨0, hl⟩ ⟨0, hm⟩) ⟨0, hw⟩)) := by
        intro k hk
        obtain ⟨i, j, t, rfl⟩ := hdec k hk
        rw [h i j t, hget i j t]
        rfl
      rw [Store.readBlock_eq_some_map_range _ hr]
      congr 1
      apply Array.ext
      · simp [EntryLayout.size_toArray]
      · intro k h1 h2
        simp [Array.getElem?_eq_getElem h2]
  · intro h i j t
    rw [Store.read_of_readBlock_eq_some_of_lt h (hlt i j t), hget i j t]

/-- The interleaved layout holds a complex matrix in buffer `b` from offset `off` exactly
when the real part of entry $(i, j)$ reads at word $2(i + lj)$ and the imaginary part at the
next word. No printed source. -/
theorem pairLayout.holds_iff {l m : ℕ} (s : Store P K) (p : P) (b off : ℕ)
    (Y : Matrix (Fin l) (Fin m) (K × K)) :
    pairLayout.Holds s p b off Y ↔ ∀ (i : Fin l) (j : Fin m),
      s.read p b (off + 2 * (i + l * j)) = some (Y i j).1 ∧
        s.read p b (off + 2 * (i + l * j) + 1) = some (Y i j).2 := by
  unfold EntryLayout.Holds pairLayout
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_assoc, add_zero,
    Fin.val_zero, Fin.val_one]

/-- A block write of the packed storage holds the matrix: if writing the packed storage of
$\mathbf{Y}$ into buffer `b` from offset `off` succeeds, the result holds $\mathbf{Y}$ there. No
printed source. -/
theorem EntryLayout.holds_of_writeBlock_eq_some (L : EntryLayout K E) {l m : ℕ} {s s' : Store P K}
    {p : P} {b off : ℕ} {Y : Matrix (Fin l) (Fin m) E}
    (h : s.writeBlock p b off (L.toArray Y) = some s') : L.Holds s' p b off Y := by
  have hlt : ∀ (i : Fin l) (j : Fin m) (t : Fin L.width),
      L.width * (i + l * j) + t < m * l * L.width := by
    intro i j t
    have hi : i + l * j + 1 ≤ m * l := by nlinarith [i.isLt, j.isLt]
    nlinarith [Nat.mul_le_mul_left L.width hi, t.isLt]
  have hget : ∀ (i : Fin l) (j : Fin m) (t : Fin L.width),
      (L.toArray Y)[L.width * (i + l * j) + t]? = some (L.put (Y i j) t) := by
    intro i j t
    have hi : i + l * j + 1 ≤ m * l := by nlinarith [i.isLt, j.isLt]
    have hl := hlt i j t
    have e1 : (finProdFinEquiv.symm ⟨L.width * (i + l * j) + t, hl⟩ : Fin (m * l) × Fin L.width)
        = (⟨i + l * j, by omega⟩, t) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [finProdFinEquiv]
      ring
    have e2 : (finProdFinEquiv.symm (⟨i + l * j, by omega⟩ : Fin (m * l))
        : Fin m × Fin l) = (j, i) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [finProdFinEquiv]
    simp only [EntryLayout.toArray, Array.getElem?_ofFn, hl, dif_pos, e1, e2]
  unfold EntryLayout.Holds
  intro i j t
  have hj : L.width * (i + l * j) + t < (L.toArray Y).size := by
    rw [EntryLayout.size_toArray]
    exact hlt i j t
  rw [Store.read_of_writeBlock_eq_some_of_lt h hj, hget i j t]

/-- A declared input holds its matrix: in the initial state whose declared buffer $k$ is the
packed storage of $\mathbf{Y}$ (every word present), buffer $k$ holds $\mathbf{Y}$ from offset
$0$. No printed source. -/
theorem EntryLayout.holds_inputState {C : Type} [Zero C] (L : EntryLayout K E) {l m : ℕ}
    (p : P) {bufs : List (Array (Option K))} {k : ℕ} {Y : Matrix (Fin l) (Fin m) E}
    (hk : bufs[k]? = some ((L.toArray Y).map some)) :
    L.Holds (inputState (C := C) p bufs).store p k 0 Y := by
  have hget : ∀ (i : Fin l) (j : Fin m) (t : Fin L.width),
      (L.toArray Y)[L.width * (i + l * j) + t]? = some (L.put (Y i j) t) := by
    intro i j t
    have hi : i + l * j + 1 ≤ m * l := by nlinarith [i.isLt, j.isLt]
    have hlt : L.width * (i + l * j) + t < m * l * L.width := by
      nlinarith [Nat.mul_le_mul_left L.width hi, t.isLt]
    have e1 : (finProdFinEquiv.symm ⟨L.width * (i + l * j) + t, hlt⟩ : Fin (m * l) × Fin L.width)
        = (⟨i + l * j, by omega⟩, t) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [finProdFinEquiv]
      ring
    have e2 : (finProdFinEquiv.symm (⟨i + l * j, by omega⟩ : Fin (m * l))
        : Fin m × Fin l) = (j, i) := by
      rw [Equiv.symm_apply_eq]
      apply Fin.ext
      simp [finProdFinEquiv]
    simp only [EntryLayout.toArray, Array.getElem?_ofFn, hlt, dif_pos, e1, e2]
  unfold EntryLayout.Holds
  intro i j t
  have hk' : (inputState (C := C) p bufs).store[k]? = some (p, (L.toArray Y).map some) := by
    simp [inputState, hk]
  simp only [Store.read, hk', zero_add, Array.getElem?_map, hget i j t]
  rfl

/-- Holding is local: if the store `s'` reads like `s` on the block of buffer `b` from `off`
of `m * l * L.width` words, and `s` holds $\mathbf{Y}$ there, so does `s'`. No printed source. -/
theorem EntryLayout.Holds.of_forall_read_eq {L : EntryLayout K E} {l m : ℕ} {s s' : Store P K}
    {p : P} {b off : ℕ} {Y : Matrix (Fin l) (Fin m) E} (hY : L.Holds s p b off Y)
    (h : ∀ i, off ≤ i → i < off + m * l * L.width → s'.read p b i = s.read p b i) :
    L.Holds s' p b off Y := by
  unfold EntryLayout.Holds at hY ⊢
  intro i j t
  have hlt : L.width * (i + l * j) + t < m * l * L.width := by
    have hi : i + l * j + 1 ≤ m * l := by nlinarith [i.isLt, j.isLt]
    nlinarith [Nat.mul_le_mul_left L.width hi, t.isLt]
  rw [h (off + (L.width * (i + l * j) + t)) (Nat.le_add_right _ _)
    (Nat.add_lt_add_left hlt off)]
  exact hY i j t

variable {ι C : Type}

/-- A product kernel call on held matrices holds the product: if kernel `o` of `I` is the
routine `mm` in a layout `L` whose `get` inverts its `put`, the operands $a$, $b$ hold the
$l \times m$ and $m \times n$ matrices $\mathbf{A}$, $\mathbf{B}$, and the output block at $c$ is
disjoint from both input blocks, then a successful call at the dimensions $[l, m, n]$ ends in a
store that holds $\mathrm{mm}(\mathbf{A}, \mathbf{B})$ at $c$ and reads as before outside the
output block. No printed source. -/
theorem IsMatMulKernel.holds_of_kcallStore_eq_some [Inhabited K] {I : Interp P ι K C} {o : ι}
    {L : EntryLayout K E} {mm : MatMulMap E} (h : IsMatMulKernel I o L mm)
    (hL : ∀ e, L.get (L.put e) = e) (p : P) {l m n : ℕ} {a b c : ℕ × ℕ} {s s' : Store P K}
    {A : Matrix (Fin l) (Fin m) E} {B : Matrix (Fin m) (Fin n) E}
    (hA : L.Holds s p a.1 a.2 A) (hB : L.Holds s p b.1 b.2 B)
    (hca : blockDisjoint (c.1, c.2, n * l * L.width) (a.1, a.2, m * l * L.width) = true)
    (hcb : blockDisjoint (c.1, c.2, n * l * L.width) (b.1, b.2, n * m * L.width) = true)
    (hs : I.kcallStore o p [l, m, n] [a, b] [c] s = some s') :
    L.Holds s' p c.1 c.2 (mm A B) ∧ ∀ q b' i,
      blockDisjoint (b', i, 1) (c.1, c.2, n * l * L.width) = true →
        s'.read q b' i = s.read q b' i := by
  have hd : ∀ (x y : ℕ × ℕ × ℕ), blockDisjoint x y = true →
      x.1 ≠ y.1 ∨ x.2.1 + x.2.2 ≤ y.2.1 ∨ y.2.1 + y.2.2 ≤ x.2.1 := by
    intro x y hxy
    simpa [blockDisjoint, or_assoc] using hxy
  have hX := (EntryLayout.holds_iff_readBlock_eq_some L s p a.1 a.2 A).mp hA
  have hY := (EntryLayout.holds_iff_readBlock_eq_some L s p b.1 b.2 B).mp hB
  rw [h.kcallStore_eq p hX hY hca hcb, EntryLayout.toMatrix_toArray L hL,
    EntryLayout.toMatrix_toArray L hL] at hs
  have hsz := EntryLayout.size_toArray L (mm A B)
  refine ⟨EntryLayout.holds_of_writeBlock_eq_some L hs, fun q' b' i hd' => ?_⟩
  have hne : b' ≠ c.1 ∨ i < c.2 ∨ c.2 + (L.toArray (mm A B)).size ≤ i := by
    rw [hsz]
    rcases hd _ _ hd' with h1 | h1 | h1
    · exact Or.inl h1
    · dsimp only at h1
      exact Or.inr (Or.inl (by omega))
    · dsimp only at h1
      exact Or.inr (Or.inr (by omega))
  exact Store.read_of_writeBlock_eq_some_of_ne hs hne

/-- A QR kernel call on a held matrix holds the factors: if kernel `o` of `I` is the routine
`qr` in a layout `L` whose `get` inverts its `put`, the operand $a$ holds the $m \times n$ matrix
$\mathbf{A}$, and the output blocks at $q$ and $r$ are disjoint from each other and from the
input block, then a successful call at the dimensions $[m, n]$ ends in a store that holds the two
factors of $\mathrm{qr}(\mathbf{A})$ at $q$ and $r$ and reads as before outside the output
blocks. No printed source. -/
theorem IsQRKernel.holds_of_kcallStore_eq_some [Inhabited K] {I : Interp P ι K C} {o : ι}
    {L : EntryLayout K E} {qr : QRMap E} (h : IsQRKernel I o L qr)
    (hL : ∀ e, L.get (L.put e) = e) (p : P) {m n : ℕ} {a q r : ℕ × ℕ} {s s' : Store P K}
    {A : Matrix (Fin m) (Fin n) E} (hA : L.Holds s p a.1 a.2 A)
    (hqr : blockDisjoint (q.1, q.2, m * m * L.width) (r.1, r.2, n * m * L.width) = true)
    (hqa : blockDisjoint (q.1, q.2, m * m * L.width) (a.1, a.2, n * m * L.width) = true)
    (hra : blockDisjoint (r.1, r.2, n * m * L.width) (a.1, a.2, n * m * L.width) = true)
    (hs : I.kcallStore o p [m, n] [a] [q, r] s = some s') :
    L.Holds s' p q.1 q.2 (qr A).1 ∧ L.Holds s' p r.1 r.2 (qr A).2 ∧ ∀ q' b' i,
      blockDisjoint (b', i, 1) (q.1, q.2, m * m * L.width) = true →
      blockDisjoint (b', i, 1) (r.1, r.2, n * m * L.width) = true →
        s'.read q' b' i = s.read q' b' i := by
  have hd : ∀ (x y : ℕ × ℕ × ℕ), blockDisjoint x y = true →
      x.1 ≠ y.1 ∨ x.2.1 + x.2.2 ≤ y.2.1 ∨ y.2.1 + y.2.2 ≤ x.2.1 := by
    intro x y hxy
    simpa [blockDisjoint, or_assoc] using hxy
  have hX := (EntryLayout.holds_iff_readBlock_eq_some L s p a.1 a.2 A).mp hA
  rw [h.kcallStore_eq p hX hqr hqa hra, EntryLayout.toMatrix_toArray L hL] at hs
  obtain ⟨s₁, h1, h2⟩ := Option.bind_eq_some_iff.mp hs
  have hsq := EntryLayout.size_toArray L (qr A).1
  have hsr := EntryLayout.size_toArray L (qr A).2
  have hne : ∀ (b' i : ℕ) (c : ℕ × ℕ) (N : ℕ), blockDisjoint (b', i, 1) (c.1, c.2, N) = true →
      b' ≠ c.1 ∨ i < c.2 ∨ c.2 + N ≤ i := by
    intro b' i c N hbd
    rcases hd _ _ hbd with h3 | h3 | h3
    · exact Or.inl h3
    · dsimp only at h3
      exact Or.inr (Or.inl (by omega))
    · dsimp only at h3
      exact Or.inr (Or.inr (by omega))
  -- the write at `r` leaves reads outside its block unchanged
  have hr_frame : ∀ (q' : P) (b' i : ℕ), (b' ≠ r.1 ∨ i < r.2 ∨ r.2 + n * m * L.width ≤ i) →
      s'.read q' b' i = s₁.read q' b' i := by
    intro q' b' i hne'
    apply Store.read_of_writeBlock_eq_some_of_ne h2
    rw [hsr]
    exact hne'
  -- the write at `q` leaves reads outside its block unchanged
  have hq_frame : ∀ (q' : P) (b' i : ℕ), (b' ≠ q.1 ∨ i < q.2 ∨ q.2 + m * m * L.width ≤ i) →
      s₁.read q' b' i = s.read q' b' i := by
    intro q' b' i hne'
    apply Store.read_of_writeBlock_eq_some_of_ne h1
    rw [hsq]
    exact hne'
  have hfq : L.Holds s₁ p q.1 q.2 (qr A).1 := EntryLayout.holds_of_writeBlock_eq_some L h1
  have hfr : L.Holds s' p r.1 r.2 (qr A).2 := EntryLayout.holds_of_writeBlock_eq_some L h2
  refine ⟨EntryLayout.Holds.of_forall_read_eq hfq (fun i hi1 hi2 => hr_frame p q.1 i ?_), hfr,
    fun q' b' i hdq hdr => ?_⟩
  · rcases hd _ _ hqr with h3 | h3 | h3
    · exact Or.inl h3
    · dsimp only at h3
      exact Or.inr (Or.inl (by omega))
    · dsimp only at h3
      exact Or.inr (Or.inr (by omega))
  · rw [hr_frame q' b' i (hne _ _ r _ hdr), hq_frame q' b' i (hne _ _ q _ hdq)]

end NLAlib.Computation
