/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.KernelContracts

/-!
# Kernel contracts: storage, witnesses and calls (scaffold)

Statements for `NLAlib/Matrix/Computation/KernelContracts.lean` (stage COMPDYN S1a, design note
`docs/design/Computation-DynamicPrograms.md`, §4.3 and "S1 implementation status"): packed storage
has the right length and reads back; the exact product and the exact QR factorization meet the
normwise contracts at $u = 0$ error (so the contracts are satisfiable); an interpretation with a
lifted routine meets the kernel contract; and a call of a matrix-multiplication or QR kernel that
meets its contract writes the routine's output.

## Main results

* `NLAlib.Computation.EntryLayout.size_toArray`, `NLAlib.Computation.EntryLayout.toMatrix_toArray`:
  packed storage.
* `NLAlib.Computation.realLayout_get_put`, `NLAlib.Computation.pairLayout_get_put`: the two
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

variable {K E : Type}

/-- **The length of a stored matrix**: the packed storage of an $l \times m$ matrix in the layout
`L` has `m * l * L.width` words. No printed source.
Proof: `simp [EntryLayout.toArray]` (`Array.size_ofFn`). S, 1 line. -/
theorem EntryLayout.size_toArray (L : EntryLayout K E) {l m : ℕ}
    (Y : Matrix (Fin l) (Fin m) E) : (L.toArray Y).size = m * l * L.width := by
  simp [EntryLayout.toArray]

/-- **Packed storage reads back**: for a layout whose `get` inverts its `put`, reading the packed
storage of an $l \times m$ matrix as an $l \times m$ matrix gives the matrix back. No printed
source.
Proof: `ext i j`; `simp only [EntryLayout.toMatrix, Matrix.of_apply]`; `convert hL (Y i j)`;
`funext t`; the word index $w(i + lj) + t$ ($w$ the width) is below $mlw$
(`Nat.lt_of_lt_of_le`, `nlinarith` on `i < l`, `j < m`, $t < w$), so `Array.getD` is the
entry of `Array.ofFn` there (`Array.getD_eq_getD_getElem?`, `Array.getElem?_ofFn`); then
`Equiv.symm_apply_apply` on the index `finProdFinEquiv (finProdFinEquiv (j, i), t)` (or
`finProdFinEquiv_symm_apply` with `Nat.add_mul_div_left`, `Nat.add_mul_mod_self_left`,
`Nat.div_eq_of_lt`, `Nat.mod_eq_of_lt`) recovers $(j, i)$ and $t$. M, about 25 lines. -/
theorem EntryLayout.toMatrix_toArray [Inhabited K] (L : EntryLayout K E)
    (hL : ∀ e, L.get (L.put e) = e) {l m : ℕ} (Y : Matrix (Fin l) (Fin m) E) :
    L.toMatrix l m (L.toArray Y) = Y := by
  ext i j
  simp only [EntryLayout.toMatrix, Matrix.of_apply]
  convert hL (Y i j)
  rename_i t
  have hi : i + l * j + 1 ≤ m * l := by
    have := i.isLt
    have := j.isLt
    nlinarith
  have hlt : L.width * (i + l * j) + t < m * l * L.width := by
    have h3 : L.width * (i + l * j + 1) ≤ L.width * (m * l) := Nat.mul_le_mul_left _ hi
    have := t.isLt
    nlinarith
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

/-- **The real layout reads back**: one word holds a real entry. No printed source.
Proof: `rfl`. S, 1 line. -/
theorem realLayout_get_put (e : K) :
    (realLayout (K := K)).get ((realLayout (K := K)).put e) = e := by
  rfl

/-- **The interleaved layout reads back**: two words hold a complex entry as a pair. No printed
source.
Proof: `rfl` (or `Prod.ext rfl rfl` after `simp [pairLayout]`). S, 1 line. -/
theorem pairLayout_get_put (e : K × K) :
    (pairLayout (K := K)).get ((pairLayout (K := K)).put e) = e := by
  rfl

variable {𝕜 : Type} [RCLike 𝕜]

/-- **The exact product meets the product contract**: for every unit roundoff $u \ge 0$, floor
$\tau$, range $\Omega$ and constants $\mu \ge 0$, the exact product
`NLAlib.Computation.exactMM` meets `NLAlib.Computation.IsMatMulErr` with the identity decoding.
No printed source.
Proof: `Matrix.map_id'`-style `simp only [Matrix.map, exactMM]` (the identity map is the
identity); the error is `specNorm 0 = 0` (`sub_self`, `NLAlib.specNorm_zero`) against
`mul_nonneg (mul_nonneg (hμ _) hu) (le_max_of_le_left (mul_nonneg (specNorm_nonneg _)
(specNorm_nonneg _)))`; the Hermitian clause is `Matrix.isHermitian_mul_conjTranspose_self`
after rewriting `B` by the hypothesis. S, about 10 lines. -/
theorem isMatMulErr_exactMM {u : ℝ} (hu : 0 ≤ u) (τ Ω : ℝ) {μ : ℕ → ℝ} (hμ : ∀ d, 0 ≤ μ d) :
    IsMatMulErr (fun x : 𝕜 => x) u τ Ω μ exactMM := by
  sorry

/-- **The exact QR factorization meets the QR contract**: for every unit roundoff $u \ge 0$,
floor $\tau$, range $\Omega$ and constants $\mu \ge 0$, the exact factorization
`NLAlib.Computation.exactQR` meets `NLAlib.Computation.IsQRErr` with the identity decoding.
No printed source.
Proof: let `h := (exists_hasOrthonormalCols_mul_isUpperTrapezoidal A).choose_spec.choose_spec`;
the identity map is the identity (`Matrix.map_id'`); `R` is upper trapezoidal by `h.2.1`; take
`Q' := Q` (`h.1`), so both errors are `specNorm 0 = 0` (`sub_self`, and `h.2.2 ▸ sub_self _`)
against nonnegative right sides (`mul_nonneg`, `le_max_of_le_left`, `specNorm_nonneg`). S, about
10 lines. -/
theorem isQRErr_exactQR {u : ℝ} (hu : 0 ≤ u) (τ Ω : ℝ) {μ : ℕ → ℝ} (hμ : ∀ d, 0 ≤ μ d) :
    IsQRErr (fun x : 𝕜 => x) u τ Ω μ exactQR := by
  sorry

variable {P ι C : Type}

/-- **A lifted product routine meets the kernel contract**: the interpretation `I` with kernel
`o` replaced by the routine `mm` lifted to blocks in the layout `L`, of the product shape, meets
`NLAlib.Computation.IsMatMulKernel` at `o`. No printed source.
Proof: `⟨Function.update_self .., Function.update_self ..⟩` after unfolding
`Interp.withKernel`. S, 2 lines. -/
theorem isMatMulKernel_withKernel [DecidableEq ι] [Inhabited K] (I : Interp P ι K C) (o : ι)
    (L : EntryLayout K E) (mm : MatMulMap E) :
    IsMatMulKernel (I.withKernel o (liftMM L mm) (mmShape L)) o L mm := by
  sorry

/-- **A lifted QR routine meets the kernel contract**: the interpretation `I` with kernel `o`
replaced by the routine `qr` lifted to blocks in the layout `L`, of the QR shape, meets
`NLAlib.Computation.IsQRKernel` at `o`. No printed source.
Proof: `⟨Function.update_self .., Function.update_self ..⟩` after unfolding
`Interp.withKernel`. S, 2 lines. -/
theorem isQRKernel_withKernel [DecidableEq ι] [Inhabited K] (I : Interp P ι K C) (o : ι)
    (L : EntryLayout K E) (qr : QRMap E) :
    IsQRKernel (I.withKernel o (liftQR L qr) (qrShape L)) o L qr := by
  sorry

variable [DecidableEq P]

/-- **A product kernel call writes the product**: if kernel `o` of `I` is the routine `mm` in the
layout `L` (`NLAlib.Computation.IsMatMulKernel`), a call at the dimensions $[l, m, n]$ with input
operands $a$, $b$ and output operand $c$, at tag `p`, whose input blocks read as $X$ and $Y$ and
whose output block is disjoint from both input blocks, is the block write at $c$ of the packed
storage of `mm` applied to $X$ and $Y$ read as $l \times m$ and $m \times n$ matrices. No printed
source.
Proof: `obtain ⟨hk, hs⟩ := h`; `unfold Interp.kcallStore`; `simp only [hs, mmShape, kcallBlocks,
List.zipWith]`; `rw [if_pos]` (lengths `rfl`, `List.pairwise_singleton`, the two disjointness
hypotheses for `∀ x ∈ [_], ∀ y ∈ [_, _]`: `List.forall_mem_singleton`, `List.forall_mem_cons`);
`simp only [Store.readBlocks, List.mapM_cons, List.mapM_nil, hX, hY, Option.bind_some, hk,
liftMM]`; `Store.writeBlocks` of one block, `if_pos (EntryLayout.size_toArray _ _)`, and the
trailing `Store.writeBlocks … [] []` is `some`, so the bind is the block write (`cases` on the
block write, then `Option.bind_some` and `Option.some_bind`). M, about 20 lines. -/
theorem IsMatMulKernel.kcallStore_eq [Inhabited K] {I : Interp P ι K C} {o : ι}
    {L : EntryLayout K E} {mm : MatMulMap E} (h : IsMatMulKernel I o L mm) (p : P) {l m n : ℕ}
    {a b c : ℕ × ℕ} {s : Store P K} {X Y : Array K}
    (hX : s.readBlock p a.1 a.2 (m * l * L.width) = some X)
    (hY : s.readBlock p b.1 b.2 (n * m * L.width) = some Y)
    (hca : blockDisjoint (c.1, c.2, n * l * L.width) (a.1, a.2, m * l * L.width) = true)
    (hcb : blockDisjoint (c.1, c.2, n * l * L.width) (b.1, b.2, n * m * L.width) = true) :
    I.kcallStore o p [l, m, n] [a, b] [c] s =
      s.writeBlock p c.1 c.2 (L.toArray (mm (L.toMatrix l m X) (L.toMatrix m n Y))) := by
  sorry

/-- **A QR kernel call writes the factors**: if kernel `o` of `I` is the routine `qr` in the layout
`L` (`NLAlib.Computation.IsQRKernel`), a call at the dimensions $[m, n]$ with input operand $a$
and output operands $q$, $r$, at tag `p`, whose input block reads as $X$, whose two output blocks
are disjoint and each disjoint from the input block, writes the packed storage of the two factors
of `qr` applied to $X$ read as an $m \times n$ matrix, first at $q$ and then at $r$. No printed
source.
Proof: as `NLAlib.Computation.IsMatMulKernel.kcallStore_eq`, with `qrShape` and `liftQR`; the
`if` needs `List.pairwise_pair` (the hypothesis `hqr`); `Store.writeBlocks` of two blocks unfolds
twice, the sizes by `NLAlib.Computation.EntryLayout.size_toArray`, and the trailing
`Store.writeBlocks … [] []` is `some` (`cases` on the second block write, then `Option.bind_some`
and `Option.some_bind`). M, about 25 lines. -/
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
  sorry

end NLAlib.Computation
