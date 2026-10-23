/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exact

/-!
# BLAS kernels as programs

The BLAS kernels used by the library's programs, as derived programs inside `named` nodes (so
that the NumPy emitter may print them as calls into its prelude). Vectors are a buffer, an offset
and a length, with stride one; matrices are column-major from an offset. Offsets and lengths are
index expressions.

Each kernel has one specification under exact arithmetic, in six parts: the value (the final
store is the store with the result written, which also gives the frame), the tape positions
(unchanged), the memory in cells (current memory unchanged, the peak raised by the scratch at
most), the memory in bits (likewise), and the counts (exact). Kernels that are not elementwise
carry disjointness hypotheses; in-place kernels allow exact aliasing and forbid partial overlap.
Design: `docs/design/Computation.md` (D13, D17, §4).

## Main definitions

* Level 1: `NLAlib.Computation.dot`, `NLAlib.Computation.axpy`, `NLAlib.Computation.scal`,
  `NLAlib.Computation.rscl`, `NLAlib.Computation.copyv`, `NLAlib.Computation.nrm2`.
* Levels 2 and 3: `NLAlib.Computation.gemv`, `NLAlib.Computation.ger`,
  `NLAlib.Computation.gemm`.

## Main results

* `NLAlib.Computation.exec_dot`, `NLAlib.Computation.exec_axpy`, `NLAlib.Computation.exec_scal`,
  `NLAlib.Computation.exec_rscl`, `NLAlib.Computation.exec_copyv`, `NLAlib.Computation.exec_nrm2`,
  `NLAlib.Computation.exec_gemv`, `NLAlib.Computation.exec_ger`, `NLAlib.Computation.exec_gemm`:
  the specifications.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

open Builder

section Kernels

variable {P ι VB VI : Type}

/-- `dot`: $\mathit{dst} \leftarrow \mathbf{x}^{\mathsf{H}}\mathbf{y}$, accumulated in order.
One scratch cell. -/
def dot (p : P) (dst : Cell VB VI) (x : VB) (xo : IExp VI) (y : VB) (yo : IExp VI)
    (n : IExp VI) : Builder P ι VB VI Unit :=
  named "dot" [.cell dst, .buf x, .idx xo, .buf y, .idx yo, .idx n] do
    ins (.lit p dst 0)
    let t ← alloc p 1
    forRange n fun i => do
      ins (.un p .conj ⟨t, 0⟩ ⟨x, xo + .var i⟩)
      ins (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨y, yo + .var i⟩)
      ins (.bin p .add dst dst ⟨t, 0⟩)

/-- `axpy`: $\mathbf{y} \leftarrow a\mathbf{x} + \mathbf{y}$, in place. One scratch cell. -/
def axpy (p : P) (a : Cell VB VI) (x : VB) (xo : IExp VI) (y : VB) (yo : IExp VI)
    (n : IExp VI) : Builder P ι VB VI Unit :=
  named "axpy" [.cell a, .buf x, .idx xo, .buf y, .idx yo, .idx n] do
    let t ← alloc p 1
    forRange n fun i => do
      ins (.bin p .mul ⟨t, 0⟩ a ⟨x, xo + .var i⟩)
      ins (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)

/-- `scal`: $\mathbf{x} \leftarrow a\mathbf{x}$, in place. -/
def scal (p : P) (a : Cell VB VI) (x : VB) (xo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "scal" [.cell a, .buf x, .idx xo, .idx n] do
    forRange n fun i => ins (.bin p .mul ⟨x, xo + .var i⟩ a ⟨x, xo + .var i⟩)

/-- `rscl`: $\mathbf{x} \leftarrow \mathbf{x}/a$, in place (LAPACK's `rscl`). -/
def rscl (p : P) (a : Cell VB VI) (x : VB) (xo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "rscl" [.cell a, .buf x, .idx xo, .idx n] do
    forRange n fun i => ins (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ a)

/-- `copy`: $\mathbf{y} \leftarrow \mathbf{x}$. -/
def copyv (p : P) (x : VB) (xo : IExp VI) (y : VB) (yo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "copy" [.buf x, .idx xo, .buf y, .idx yo, .idx n] do
    forRange n fun i => ins (.copy p ⟨y, yo + .var i⟩ ⟨x, xo + .var i⟩)

/-- `nrm2`: $\mathit{dst} \leftarrow \|\mathbf{x}\|$, as the square root of `dot`. -/
def nrm2 (p : P) (dst : Cell VB VI) (x : VB) (xo : IExp VI) (n : IExp VI) :
    Builder P ι VB VI Unit :=
  named "nrm2" [.cell dst, .buf x, .idx xo, .idx n] do
    dot p dst x xo x xo n
    ins (.un p .sqrt dst dst)

/-- `gemv`: $\mathbf{y} \leftarrow \mathbf{A}\mathbf{x}$ for a stored $m \times n$ matrix
$\mathbf{A}$, column by column. One scratch cell. -/
def gemv (p : P) (m n : IExp VI) (A : VB) (ao : IExp VI) (x : VB) (xo : IExp VI) (y : VB)
    (yo : IExp VI) : Builder P ι VB VI Unit :=
  named "gemv" [.idx m, .idx n, .buf A, .idx ao, .buf x, .idx xo, .buf y, .idx yo] do
    forRange m fun i => ins (.lit p ⟨y, yo + .var i⟩ 0)
    let t ← alloc p 1
    forRange n fun j => forRange m fun i => do
      ins (.bin p .mul ⟨t, 0⟩ ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)
      ins (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)

/-- `ger`: $\mathbf{A} \leftarrow \mathbf{A} + a\mathbf{x}\mathbf{y}^{\mathsf{H}}$ for a stored
$m \times n$ matrix $\mathbf{A}$, in place, column by column. Two scratch cells. -/
def ger (p : P) (m n : IExp VI) (a : Cell VB VI) (x : VB) (xo : IExp VI) (y : VB)
    (yo : IExp VI) (A : VB) (ao : IExp VI) : Builder P ι VB VI Unit :=
  named "ger" [.idx m, .idx n, .cell a, .buf x, .idx xo, .buf y, .idx yo, .buf A, .idx ao] do
    let t ← alloc p 2
    forRange n fun j => do
      ins (.un p .conj ⟨t, 0⟩ ⟨y, yo + .var j⟩)
      ins (.bin p .mul ⟨t, 0⟩ a ⟨t, 0⟩)
      forRange m fun i => do
        ins (.bin p .mul ⟨t, 1⟩ ⟨x, xo + .var i⟩ ⟨t, 0⟩)
        ins (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩ ⟨t, 1⟩)

/-- `gemm`: $\mathbf{C} \leftarrow \mathbf{A}\mathbf{B}$, $\mathbf{A}$ of size $m \times n$ and
$\mathbf{B}$ of size $n \times l$, one `gemv` per column. -/
def gemm (p : P) (m n l : IExp VI) (A : VB) (ao : IExp VI) (B : VB) (bo : IExp VI) (C : VB)
    (co : IExp VI) : Builder P ι VB VI Unit :=
  named "gemm" [.idx m, .idx n, .idx l, .buf A, .idx ao, .buf B, .idx bo, .buf C, .idx co] do
    forRange l fun c => gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)

end Kernels

/-! ### Specifications under exact arithmetic -/

section Specs

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]
  (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
  (hc : ∀ k, I.charge k = Finsupp.single k 1) (p : P) (st : St P 𝕜 (OpCount P ι))

include hI hc

/-- **`dot` computes $\mathbf{x}^{\mathsf{H}}\mathbf{y}$** for every index expression of the
offsets and the length: if the cells of $\mathbf{x}$ and $\mathbf{y}$ hold $x_i$, $y_i$ for
$i < n$ and $\mathit{dst}$ is in neither, the run writes $\sum_{i<n} \bar{x}_i y_i$ into
$\mathit{dst}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell at tag $p$, and counts $n$ conjugations, multiplications and additions and one literal.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_dot (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ)
    (xs ys : ℕ → 𝕜) (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i))
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → ∀ i < n.eval, dst.idx.eval ≠ yo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.write p dst.buf dst.idx.eval
      (∑ i ∈ Finset.range n.eval, star (xs i) * ys i) = some s₁) :
    ∃ st', exec I (dot p dst x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (n.eval • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1) +
        Finsupp.single (.lit p) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  sorry

/-- **`axpy` computes $\mathbf{y} \leftarrow a\mathbf{x} + \mathbf{y}$ in place**: if $a$, the
$x_i$ and the $y_i$ ($i < n$) are stored, $a$ is not in $\mathbf{y}$, and $\mathbf{x}$ and
$\mathbf{y}$ are the same vector or do not overlap, the run writes $a x_i + y_i$ into the cells
of $\mathbf{y}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell, and counts $n$ multiplications and additions. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_axpy (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (av : 𝕜)
    (xs ys : ℕ → 𝕜) (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read p y (yo.eval + i) = some (ys i))
    (hay : a.buf = y → ∀ i < n.eval, a.idx.eval ≠ yo.eval + i)
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j)
    (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p y yo.eval
      ((List.range n.eval).toArray.map fun i => av * xs i + ys i) = some s₁) :
    ∃ st', exec I (axpy p a x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • (Finsupp.single (.bin p .mul) 1 +
        Finsupp.single (.bin p .add) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  sorry

/-- **`scal` computes $\mathbf{x} \leftarrow a\mathbf{x}$ in place**: if $a$ and the $x_i$
($i < n$) are stored and $a$ is not in $\mathbf{x}$, the run writes $a x_i$ into the cells of
$\mathbf{x}$ and nothing else, keeps the tape and the memory, and counts $n$ multiplications.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_scal (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (av : 𝕜) (xs : ℕ → 𝕜)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hax : a.buf = x → ∀ i < n.eval, a.idx.eval ≠ xo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p x xo.eval
      ((List.range n.eval).toArray.map fun i => av * xs i) = some s₁) :
    ∃ st', exec I (scal p a x xo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • Finsupp.single (.bin p .mul) 1 ∧
      st'.peak = st.peak ∧ st'.peakW = st.peakW := by
  sorry

/-- **`rscl` computes $\mathbf{x} \leftarrow \mathbf{x}/a$ in place**: if $a \ne 0$ and the
$x_i$ ($i < n$) are stored and $a$ is not in $\mathbf{x}$, the run writes $x_i/a$ into the cells
of $\mathbf{x}$ and nothing else, keeps the tape and the memory, and counts $n$ divisions.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_rscl (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (av : 𝕜) (xs : ℕ → 𝕜) (hav : av ≠ 0)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hax : a.buf = x → ∀ i < n.eval, a.idx.eval ≠ xo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p x xo.eval
      ((List.range n.eval).toArray.map fun i => xs i / av) = some s₁) :
    ∃ st', exec I (rscl p a x xo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • Finsupp.single (.bin p .div) 1 ∧
      st'.peak = st.peak ∧ st'.peakW = st.peakW := by
  sorry

/-- **`copy` copies $\mathbf{x}$ into $\mathbf{y}$**: if the $x_i$ ($i < n$) are stored and the
two vectors are the same or do not overlap, the run writes $x_i$ into the cells of $\mathbf{y}$
and nothing else, keeps the tape and the memory, and counts $n$ copies. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_copyv (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) (xs : ℕ → 𝕜)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hxy : x = y → ∀ i < n.eval, ∀ j < n.eval, xo.eval + i = yo.eval + j → i = j)
    (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p y yo.eval ((List.range n.eval).toArray.map xs) = some s₁) :
    ∃ st', exec I (copyv p x xo y yo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + n.eval • Finsupp.single (.copy p) 1 ∧
      st'.peak = st.peak ∧ st'.peakW = st.peakW := by
  sorry

/-- **`nrm2` computes $\|\mathbf{x}\|$**: if the $x_i$ ($i < n$) are stored and $\mathit{dst}$ is
not in $\mathbf{x}$, the run writes $\bigl(\sum_{i<n} \bar{x}_i x_i\bigr)^{1/2}$ into
$\mathit{dst}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell, and counts $n$ conjugations, multiplications and additions, one literal and one square
root. The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_nrm2 (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (xs : ℕ → 𝕜)
    (hx : ∀ i < n.eval, st.store.read p x (xo.eval + i) = some (xs i))
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval + i) (s₁ : Store P 𝕜)
    (h₁ : st.store.write p dst.buf dst.idx.eval
      ((√(RCLike.re (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)) : ℝ) : 𝕜) = some s₁) :
    ∃ st', exec I (nrm2 p dst x xo n).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (n.eval • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1) +
        Finsupp.single (.lit p) 1 + Finsupp.single (.un p .sqrt) 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  sorry

/-- **`gemv` computes $\mathbf{A}\mathbf{x}$**: if buffer $A$ holds the $m \times n$ matrix
$\mathbf{A}$ from $\mathit{ao}$, the cells of $\mathbf{x}$ hold $\mathbf{x}$, and the cells of
$\mathbf{y}$ overlap neither, the run writes $\mathbf{A}\mathbf{x}$ into the cells of
$\mathbf{y}$ and nothing else, keeps the tape and the current memory, raises the peak by one
cell, and counts $m$ literals and $mn$ multiplications and additions. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_gemv (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo : IExp ℕ) (M : Matrix (Fin m.eval) (Fin n.eval) 𝕜) (xv : Fin n.eval → 𝕜)
    (hA : Holds st.store p A ao.eval M)
    (hx : ∀ j : Fin n.eval, st.store.read p x (xo.eval + j) = some (xv j))
    (hyA : y = A → yo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (hyx : y = x → yo.eval + m.eval ≤ xo.eval ∨ xo.eval + n.eval ≤ yo.eval) (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p y yo.eval (Array.ofFn (M *ᵥ xv)) = some s₁) :
    ∃ st', exec I (gemv p m n A ao x xo y yo).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (m.eval • Finsupp.single (.lit p) 1 + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW = max st.peakW (st.curW + I.width p) := by
  sorry

/-- **`ger` computes $\mathbf{A} + a\mathbf{x}\mathbf{y}^{\mathsf{H}}$ in place**: if buffer $A$
holds the $m \times n$ matrix $\mathbf{A}$ from $\mathit{ao}$, the cells of $a$, $\mathbf{x}$
and $\mathbf{y}$ hold $a$, $\mathbf{x}$, $\mathbf{y}$ and lie outside the block of $\mathbf{A}$,
the run writes $\mathbf{A} + a\mathbf{x}\mathbf{y}^{\mathsf{H}}$ into the block and nothing else,
keeps the tape and the current memory, raises the peak by two cells, and counts $n$
conjugations, $n + mn$ multiplications and $mn$ additions. The operation is in
[GolubVanLoan2013, §1.1]. -/
theorem exec_ger (m n : IExp ℕ) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo : IExp ℕ)
    (A : ℕ) (ao : IExp ℕ) (av : 𝕜) (xv : Fin m.eval → 𝕜) (yv : Fin n.eval → 𝕜)
    (M : Matrix (Fin m.eval) (Fin n.eval) 𝕜) (hA : Holds st.store p A ao.eval M)
    (ha : st.store.read p a.buf a.idx.eval = some av)
    (hx : ∀ i : Fin m.eval, st.store.read p x (xo.eval + i) = some (xv i))
    (hy : ∀ j : Fin n.eval, st.store.read p y (yo.eval + j) = some (yv j))
    (haA : a.buf = A → a.idx.eval < ao.eval ∨ ao.eval + m.eval * n.eval ≤ a.idx.eval)
    (hxA : x = A → xo.eval + m.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ xo.eval)
    (hyA : y = A → yo.eval + n.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ yo.eval)
    (s₁ : Store P 𝕜)
    (h₁ : st.store.writeBlock p A ao.eval (flatten (M + av • Matrix.vecMulVec xv (star yv))) =
      some s₁) :
    ∃ st', exec I (ger p m n a x xo y yo A ao).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + (n.eval • (Finsupp.single (.un p .conj) 1 +
        Finsupp.single (.bin p .mul) 1) + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 2)) ∧
      st'.peakW = max st.peakW (st.curW + 2 * I.width p) := by
  sorry

/-- **`gemm` computes $\mathbf{A}\mathbf{B}$**: if buffers $A$ and $B$ hold the $m \times n$ and
$n \times l$ matrices $\mathbf{A}$, $\mathbf{B}$ from $\mathit{ao}$, $\mathit{bo}$, and the block
of $\mathbf{C}$ overlaps neither, the run writes $\mathbf{A}\mathbf{B}$ into the block of
$\mathbf{C}$ and nothing else, keeps the tape and the current memory, raises the peak by at
most one cell, and counts $lm$ literals and $lnm$ multiplications and additions.
The operation is in [GolubVanLoan2013, §1.1]. -/
theorem exec_gemm (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ) (bo : IExp ℕ) (C : ℕ)
    (co : IExp ℕ) (MA : Matrix (Fin m.eval) (Fin n.eval) 𝕜)
    (MB : Matrix (Fin n.eval) (Fin l.eval) 𝕜) (hA : Holds st.store p A ao.eval MA)
    (hB : Holds st.store p B bo.eval MB)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (s₁ : Store P 𝕜) (h₁ : st.store.writeBlock p C co.eval (flatten (MA * MB)) = some s₁) :
    ∃ st', exec I (gemm p m n l A ao B bo C co).run st = some st' ∧ st'.store = s₁ ∧
      st'.pos = st.pos ∧ st'.cur = st.cur ∧ st'.curW = st.curW ∧
      st'.cnt = st.cnt + l.eval • (m.eval • Finsupp.single (.lit p) 1 + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      st'.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.peakW ≤ max st.peakW (st.curW + I.width p) := by
  sorry

end Specs

end NLAlib.Computation
