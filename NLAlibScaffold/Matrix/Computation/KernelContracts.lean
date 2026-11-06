/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Contract
public import NLAlib.Matrix.Computation.KernelContracts

/-!
# Stored matrices in blocks, and kernel calls on them (scaffold)

Statements for `NLAlib/Matrix/Computation/KernelContracts.lean` (stage COMPDYN S1c, design note
`docs/design/Computation-SignDeflatePrograms.md`, §2): the complex-pair patterns. A block holds a
matrix (`NLAlib.Computation.EntryLayout.Holds`) exactly when it reads as its packed storage; for
the interleaved layout that is one read per part; a block write of the packed storage makes the
block hold the matrix; a declared input buffer holds its matrix; and a call of a kernel meeting
`NLAlib.Computation.IsMatMulKernel` or `NLAlib.Computation.IsQRKernel` on blocks that hold
matrices writes blocks that hold the routine's output.

## Main results

* `NLAlib.Computation.EntryLayout.holds_iff_readBlock_eq_some`,
  `NLAlib.Computation.pairLayout.holds_iff`: what holding a matrix means.
* `NLAlib.Computation.EntryLayout.holds_of_writeBlock_eq_some`,
  `NLAlib.Computation.EntryLayout.holds_inputState`,
  `NLAlib.Computation.EntryLayout.Holds.of_forall_read_eq`: how a block comes to hold a matrix.
* `NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some`,
  `NLAlib.Computation.IsQRKernel.holds_of_kcallStore_eq_some`: kernel calls on held matrices.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P K E : Type} [DecidableEq P]

/-- **Holding a matrix is reading its packed storage**: for a layout whose `get` inverts its
`put`, buffer `b` holds the $l \times m$ matrix $\mathbf{Y}$ from offset `off` exactly when the
block of `m * l * L.width` words there reads as the packed storage of $\mathbf{Y}$. No printed
source.
Proof: unfold `NLAlib.Computation.EntryLayout.Holds` and `NLAlib.Computation.Store.readBlock`;
`Array.mapM` of `(List.range len).toArray` is `some` exactly when every read is
(`NLAlib.Computation.Store.readBlock_eq_some_map_range` gives one direction); the word
$w(i + lj) + t$ of the packed storage is word `t` of entry $(i, j)$ (the index computation of
`NLAlib.Computation.EntryLayout.toMatrix_toArray`, `finProdFinEquiv`), and every word below
$mlw$ is of this form (`finProdFinEquiv.symm`). M, about 40 lines. -/
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

/-- **The interleaved layout holds a complex matrix** in buffer `b` from offset `off` exactly
when the real part of entry $(i, j)$ reads at word $2(i + lj)$ and the imaginary part at the
next word. No printed source.
Proof: unfold `NLAlib.Computation.EntryLayout.Holds`, `NLAlib.Computation.pairLayout`;
`Fin.forall_fin_two`; `Matrix.cons_val_zero`, `Matrix.cons_val_one`; `add_assoc`. S, 6 lines. -/
theorem pairLayout.holds_iff {l m : ℕ} (s : Store P K) (p : P) (b off : ℕ)
    (Y : Matrix (Fin l) (Fin m) (K × K)) :
    pairLayout.Holds s p b off Y ↔ ∀ (i : Fin l) (j : Fin m),
      s.read p b (off + 2 * (i + l * j)) = some (Y i j).1 ∧
        s.read p b (off + 2 * (i + l * j) + 1) = some (Y i j).2 := by
  unfold EntryLayout.Holds pairLayout
  simp only [Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_assoc, add_zero,
    Fin.val_zero, Fin.val_one]

/-- **A block write of the packed storage holds the matrix**: if writing the packed storage of
$\mathbf{Y}$ into buffer `b` from offset `off` succeeds, the result holds $\mathbf{Y}$ there. No
printed source.
Proof: `NLAlib.Computation.Store.read_of_writeBlock_eq_some_of_lt` at word $w(i + lj) + t$,
which is below the length of the packed storage
(`NLAlib.Computation.EntryLayout.size_toArray`), and the index
computation of `NLAlib.Computation.EntryLayout.toMatrix_toArray` (`Array.getElem?_ofFn`,
`finProdFinEquiv`). M, about 20 lines. -/
theorem EntryLayout.holds_of_writeBlock_eq_some (L : EntryLayout K E) {l m : ℕ} {s s' : Store P K}
    {p : P} {b off : ℕ} {Y : Matrix (Fin l) (Fin m) E}
    (h : s.writeBlock p b off (L.toArray Y) = some s') : L.Holds s' p b off Y := by
  sorry

/-- **A declared input holds its matrix**: in the initial state whose declared buffer $k$ is the
packed storage of $\mathbf{Y}$ (every word present), buffer $k$ holds $\mathbf{Y}$ from offset
$0$. No printed source.
Proof: unfold `NLAlib.Computation.inputState`, `NLAlib.Computation.Store.read`;
`List.getElem?_toArray`, `List.getElem?_map`, `hk`, `if_pos rfl`; `Array.getElem?_map`, the entry
of `Array.ofFn` (as in `NLAlib.Computation.EntryLayout.toMatrix_toArray`), `Option.join`. S, about
10 lines. -/
theorem EntryLayout.holds_inputState {C : Type} [Zero C] (L : EntryLayout K E) {l m : ℕ}
    (p : P) {bufs : List (Array (Option K))} {k : ℕ} {Y : Matrix (Fin l) (Fin m) E}
    (hk : bufs[k]? = some ((L.toArray Y).map some)) :
    L.Holds (inputState (C := C) p bufs).store p k 0 Y := by
  sorry

/-- **Holding is local**: if the store `s'` reads like `s` on the block of buffer `b` from `off`
of `m * l * L.width` words, and `s` holds $\mathbf{Y}$ there, so does `s'`. No printed source.
Proof: `intro i j t`; `rw [h]`, then `hY i j t`; the word index is below the end of the block
(`nlinarith` on `i < l`, `j < m`, $t$ below the width). S, 5 lines. -/
theorem EntryLayout.Holds.of_forall_read_eq {L : EntryLayout K E} {l m : ℕ} {s s' : Store P K}
    {p : P} {b off : ℕ} {Y : Matrix (Fin l) (Fin m) E} (hY : L.Holds s p b off Y)
    (h : ∀ i, off ≤ i → i < off + m * l * L.width → s'.read p b i = s.read p b i) :
    L.Holds s' p b off Y := by
  sorry

variable {ι C : Type}

/-- **A product kernel call on held matrices holds the product**: if kernel `o` of `I` is the
routine `mm` in a layout `L` whose `get` inverts its `put`, the operands $a$, $b$ hold the
$l \times m$ and $m \times n$ matrices $\mathbf{A}$, $\mathbf{B}$, and the output block at $c$ is
disjoint from both input blocks, then a successful call at the dimensions $[l, m, n]$ ends in a
store that holds $\mathrm{mm}(\mathbf{A}, \mathbf{B})$ at $c$ and reads as before outside the
output block. No printed source.
Proof: `NLAlib.Computation.EntryLayout.holds_iff_readBlock_eq_some` gives the input reads;
`NLAlib.Computation.IsMatMulKernel.kcallStore_eq` rewrites the call as one block write of
the packed storage of `mm` on the read-back matrices, and
`NLAlib.Computation.EntryLayout.toMatrix_toArray` with `hL` turns the read-back matrices into
$\mathbf{A}$, $\mathbf{B}$; then `NLAlib.Computation.EntryLayout.holds_of_writeBlock_eq_some`
and `NLAlib.Computation.Store.read_of_writeBlock_eq_some_of_ne` for the frame. M, about 25
lines. -/
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
  sorry

/-- **A QR kernel call on a held matrix holds the factors**: if kernel `o` of `I` is the routine
`qr` in a layout `L` whose `get` inverts its `put`, the operand $a$ holds the $m \times n$ matrix
$\mathbf{A}$, and the output blocks at $q$ and $r$ are disjoint from each other and from the
input block, then a successful call at the dimensions $[m, n]$ ends in a store that holds the two
factors of $\mathrm{qr}(\mathbf{A})$ at $q$ and $r$ and reads as before outside the output
blocks. No printed source.
Proof: as `NLAlib.Computation.IsMatMulKernel.holds_of_kcallStore_eq_some`, with
`NLAlib.Computation.IsQRKernel.kcallStore_eq` (two block writes, the second disjoint from the
first by `hqr`, so the first block still holds its factor:
`NLAlib.Computation.EntryLayout.Holds.of_forall_read_eq` and
`NLAlib.Computation.Store.read_of_writeBlock_eq_some_of_ne`). M, about 30 lines. -/
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
  sorry

end NLAlib.Computation
