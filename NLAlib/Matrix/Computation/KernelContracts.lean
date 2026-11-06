/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec
public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Factorizations.Triangular
public import NLAlib.Matrix.Norms.Spectral
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Logic.Equiv.Fin.Basic

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
  `NLAlib.Computation.IsMatMulErr` and `NLAlib.Computation.IsQRErr`, the shape of the
  floating-point machine contracts of the shallow eigensolver analysis.

The exact routines `NLAlib.Computation.exactMM` (the product) and `NLAlib.Computation.exactQR` (a
QR factorization chosen from `NLAlib.exists_hasOrthonormalCols_mul_isUpperTrapezoidal`) are the
witnesses that the contracts are satisfiable.

## Main definitions

* `NLAlib.Computation.MatMulMap`, `NLAlib.Computation.QRMap`: routines on matrices.
* `NLAlib.Computation.IsMatMulErr`, `NLAlib.Computation.IsQRErr`: their normwise contracts.
* `NLAlib.Computation.EntryLayout`, `NLAlib.Computation.realLayout`,
  `NLAlib.Computation.pairLayout`, `NLAlib.Computation.EntryLayout.toMatrix`,
  `NLAlib.Computation.EntryLayout.toArray`: packed column-major storage of a matrix.
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
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

/-! ### Routines on matrices and their normwise contracts -/

/-- A **matrix-multiplication routine** on matrices with entries in `E`, indexed by `Fin`, of
compatible shapes. -/
abbrev MatMulMap (E : Type) : Type :=
  ∀ {l m n : ℕ}, Matrix (Fin l) (Fin m) E → Matrix (Fin m) (Fin n) E → Matrix (Fin l) (Fin n) E

/-- A **QR routine** on matrices with entries in `E`: an $m \times n$ matrix to a square
$m \times m$ factor and an $m \times n$ factor. -/
abbrev QRMap (E : Type) : Type :=
  ∀ {m n : ℕ}, Matrix (Fin m) (Fin n) E → Matrix (Fin m) (Fin m) E × Matrix (Fin m) (Fin n) E

variable {E : Type} {𝕜 : Type} [RCLike 𝕜]

/-- `IsMatMulErr dec u τ Ω μ mm`: **the routine `mm` multiplies with normwise error
$\mu(d)\,u$**, read through the decoding `dec` of stored entries: for stored $\mathbf{A}$,
$\mathbf{B}$ with decodings $\bar{\mathbf{A}}$, $\bar{\mathbf{B}}$,
$\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2 \le \Omega$ and $d$ the largest dimension,
$$\|\bar{\mathbf{A}}\bar{\mathbf{B}} - \overline{\mathrm{mm}(\mathbf{A}, \mathbf{B})}\|_2 \le
\mu(d)\,u\max(\|\bar{\mathbf{A}}\|_2\|\bar{\mathbf{B}}\|_2, \tau) \,,$$
and when $\bar{\mathbf{B}} = \bar{\mathbf{A}}^{\mathsf{H}}$ the decoded product is exactly
Hermitian. [Shah2024, Definition 1.1], with the identity decoding, $\tau = 0$ and no range
there. -/
structure IsMatMulErr (dec : E → 𝕜) (u τ Ω : ℝ) (μ : ℕ → ℝ) (mm : MatMulMap E) : Prop where
  /-- The normwise error bound in range. -/
  specNorm_mul_sub_le : ∀ {l m n : ℕ} (A : Matrix (Fin l) (Fin m) E)
    (B : Matrix (Fin m) (Fin n) E), specNorm (A.map dec) * specNorm (B.map dec) ≤ Ω →
      specNorm (A.map dec * B.map dec - (mm A B).map dec) ≤
        μ (max l (max m n)) * u * max (specNorm (A.map dec) * specNorm (B.map dec)) τ
  /-- A product with its own conjugate transpose is computed exactly Hermitian. -/
  isHermitian_of_map_eq_conjTranspose : ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) E)
    (B : Matrix (Fin n) (Fin m) E), B.map dec = (A.map dec)ᴴ → ((mm A B).map dec).IsHermitian

/-- `IsQRErr dec u τ Ω μ qr`: **the routine `qr` computes a backward-stable QR factorization**,
read through the decoding `dec`: for stored $\mathbf{A}$ with decoding $\bar{\mathbf{A}}$,
$\|\bar{\mathbf{A}}\|_2 \le \Omega$, $(\mathbf{Q}, \mathbf{R}) = \mathrm{qr}(\mathbf{A})$ and
$d = \max(m, n)$, the decoded $\bar{\mathbf{R}}$ is upper trapezoidal and there is a unitary
$\mathbf{Q}'$ with
$$\|\mathbf{Q}' - \bar{\mathbf{Q}}\|_2 \le \mu(d)\,u \,, \qquad
\|\bar{\mathbf{A}} - \mathbf{Q}'\bar{\mathbf{R}}\|_2 \le \mu(d)\,u\max(\|\bar{\mathbf{A}}\|_2,
\tau) \,.$$
[Shah2024, Definition 1.2], with the identity decoding, $\tau = 0$ and no range there. -/
def IsQRErr (dec : E → 𝕜) (u τ Ω : ℝ) (μ : ℕ → ℝ) (qr : QRMap E) : Prop :=
  ∀ {m n : ℕ} (A : Matrix (Fin m) (Fin n) E), specNorm (A.map dec) ≤ Ω →
    IsUpperTrapezoidal ((qr A).2.map dec) ∧
      ∃ Q' : Matrix (Fin m) (Fin m) 𝕜, HasOrthonormalCols Q' ∧
        specNorm (Q' - (qr A).1.map dec) ≤ μ (max m n) * u ∧
        specNorm (A.map dec - Q' * (qr A).2.map dec) ≤
          μ (max m n) * u * max (specNorm (A.map dec)) τ

/-- The **exact product**, the witness that `NLAlib.Computation.IsMatMulErr` is satisfiable. -/
def exactMM : MatMulMap 𝕜 := fun A B => A * B

/-- An **exact QR factorization**: $\mathbf{A} = \mathbf{Q}\mathbf{R}$ with $\mathbf{Q}$ unitary
and $\mathbf{R}$ upper trapezoidal, chosen from
`NLAlib.exists_hasOrthonormalCols_mul_isUpperTrapezoidal`; the witness that
`NLAlib.Computation.IsQRErr` is satisfiable. -/
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

variable {K : Type}

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
contract on `mm` (such as `NLAlib.Computation.IsMatMulErr`) then bounds the kernel's error. -/
def IsMatMulKernel [Inhabited K] (I : Interp P ι K C) (o : ι) (L : EntryLayout K E)
    (mm : MatMulMap E) : Prop :=
  I.kernel o = liftMM L mm ∧ I.kshape o = mmShape L

/-- **Kernel `o` of `I` is the routine `qr`**, functionally on stored entries in the layout `L`:
its kernel is `NLAlib.Computation.liftQR L qr` and its shape `NLAlib.Computation.qrShape L`. A
contract on `qr` (such as `NLAlib.Computation.IsQRErr`) then bounds the kernel's error. -/
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
`NLAlib.Computation.exactMM` meets `NLAlib.Computation.IsMatMulErr` with the identity decoding.
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
`NLAlib.Computation.exactQR` meets `NLAlib.Computation.IsQRErr` with the identity decoding.
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
