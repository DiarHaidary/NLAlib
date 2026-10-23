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

open scoped Matrix ComplexOrder

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

/-! ### Run lemmas for the level-1 kernels -/

section Runs

variable {P ι : Type}

private theorem dot_run (p : P) (dst : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    (dot (ι := ι) p dst x xo y yo n).run = .seq (.named "dot"
      [.cell dst, .buf x, .idx xo, .buf y, .idx yo, .idx n]
      (.seq (.instr (.lit p dst 0)) (.alloc p 1 fun t => .seq (.loop n fun i =>
        .seq (.instr (.un p .conj ⟨t, 0⟩ ⟨x, xo + .var i⟩))
          (.seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨y, yo + .var i⟩))
            (.seq (.instr (.bin p .add dst dst ⟨t, 0⟩)) .skip))) .skip))) .skip := rfl

private theorem axpy_run (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    (axpy (ι := ι) p a x xo y yo n).run = .seq (.named "axpy"
      [.cell a, .buf x, .idx xo, .buf y, .idx yo, .idx n]
      (.alloc p 1 fun t => .seq (.loop n fun i =>
        .seq (.instr (.bin p .mul ⟨t, 0⟩ a ⟨x, xo + .var i⟩))
          (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)) .skip))
        .skip)) .skip := rfl

private theorem scal_run (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    (scal (ι := ι) p a x xo n).run = .seq (.named "scal" [.cell a, .buf x, .idx xo, .idx n]
      (.seq (.loop n fun i =>
        .seq (.instr (.bin p .mul ⟨x, xo + .var i⟩ a ⟨x, xo + .var i⟩)) .skip) .skip)) .skip :=
  rfl

private theorem rscl_run (p : P) (a : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    (rscl (ι := ι) p a x xo n).run = .seq (.named "rscl" [.cell a, .buf x, .idx xo, .idx n]
      (.seq (.loop n fun i =>
        .seq (.instr (.bin p .div ⟨x, xo + .var i⟩ ⟨x, xo + .var i⟩ a)) .skip) .skip)) .skip :=
  rfl

private theorem copyv_run (p : P) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ) :
    (copyv (ι := ι) p x xo y yo n).run = .seq (.named "copy"
      [.buf x, .idx xo, .buf y, .idx yo, .idx n]
      (.seq (.loop n fun i =>
        .seq (.instr (.copy p ⟨y, yo + .var i⟩ ⟨x, xo + .var i⟩)) .skip) .skip)) .skip := rfl

private theorem nrm2_run (p : P) (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) :
    (nrm2 (ι := ι) p dst x xo n).run = .seq (.named "nrm2" [.cell dst, .buf x, .idx xo, .idx n]
      (dot p dst x xo x xo n >>= fun _ => ins (.un p .sqrt dst dst)).run) .skip := rfl

private theorem gemv_run (p : P) (m n : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (x : ℕ) (xo : IExp ℕ)
    (y : ℕ) (yo : IExp ℕ) :
    (gemv (ι := ι) p m n A ao x xo y yo).run = .seq (.named "gemv"
      [.idx m, .idx n, .buf A, .idx ao, .buf x, .idx xo, .buf y, .idx yo]
      (.seq (.loop m fun i => .seq (.instr (.lit p ⟨y, yo + .var i⟩ 0)) .skip)
        (.alloc p 1 fun t => .seq (.loop n fun j => .seq (.loop m fun i =>
          .seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩))
            (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)) .skip))
          .skip) .skip))) .skip := rfl

private theorem ger_run (p : P) (m n : IExp ℕ) (a : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ)
    (yo : IExp ℕ) (A : ℕ) (ao : IExp ℕ) :
    (ger (ι := ι) p m n a x xo y yo A ao).run = .seq (.named "ger"
      [.idx m, .idx n, .cell a, .buf x, .idx xo, .buf y, .idx yo, .buf A, .idx ao]
      (.alloc p 2 fun t => .seq (.loop n fun j =>
        .seq (.instr (.un p .conj ⟨t, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨t, 0⟩ a ⟨t, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨t, 1⟩ ⟨x, xo + .var i⟩ ⟨t, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨t, 1⟩)) .skip)) .skip))) .skip)) .skip := rfl

private theorem gemm_run (p : P) (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ) (bo : IExp ℕ)
    (C : ℕ) (co : IExp ℕ) :
    (gemm (ι := ι) p m n l A ao B bo C co).run = .seq (.named "gemm"
      [.idx m, .idx n, .idx l, .buf A, .idx ao, .buf B, .idx bo, .buf C, .idx co]
      (.seq (.loop l fun c => (gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)).run)
        .skip)) .skip := rfl

private theorem exists_map_eq_some {α β : Type} {o : Option α} {f : α → β} {Q : α → Prop}
    {R : β → Prop} (h : ∃ a, o = some a ∧ Q a) (hQ : ∀ a, Q a → R (f a)) :
    ∃ b, o.map f = some b ∧ R b := by
  obtain ⟨a, rfl, ha⟩ := h
  exact ⟨f a, rfl, hQ a ha⟩

private theorem foldlM_range_succ {α : Type} (g : α → ℕ → Option α) (a : α) (i : ℕ) :
    (List.range (i + 1)).foldlM g a = ((List.range i).foldlM g a).bind fun b => g b i := by
  rw [List.range_succ, List.foldlM_append]
  rcases (List.range i).foldlM g a with _ | b
  · rfl
  · change (g b i).bind (fun b => some b) = g b i
    rcases g b i <;> rfl

private theorem exists_foldlM_range_eq_some_of_le {α : Type} {g : α → ℕ → Option α} {a b : α}
    {n i : ℕ} (h : (List.range n).foldlM g a = some b) (hi : i ≤ n) :
    ∃ c, (List.range i).foldlM g a = some c := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [List.range_add, List.foldlM_append] at h
  obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h
  exact ⟨c, hc⟩

private theorem read_push_size_set {K : Type} [DecidableEq P] {s : Store P K} {p : P}
    {arr : Array (Option K)} {v : K} (h : 0 < arr.size) :
    Store.read (s.push (p, arr.set! 0 (some v))) p s.size 0 = some v := by
  simp [Store.read_push_size, h]

end Runs

section Steps

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- One step of `dot`, from a store `s` with `v` written into `dst`. -/
private theorem exec_dot_step (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem) (p : P)
    {s : Store P 𝕜} {dst : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo : IExp ℕ} {t i : ℕ}
    {xi yi v : 𝕜} {si si' : Store P 𝕜} {st' : St P 𝕜 (OpCount P ι)} {arr : Array (Option 𝕜)}
    (hx : s.read p x (xo.eval + i) = some xi) (hy : s.read p y (yo.eval + i) = some yi)
    (hdx : dst.buf = x → dst.idx.eval ≠ xo.eval + i)
    (hdy : dst.buf = y → dst.idx.eval ≠ yo.eval + i) (ht : s.size = t)
    (hsi : s.write p dst.buf dst.idx.eval v = some si)
    (hsi' : s.write p dst.buf dst.idx.eval (v + star xi * yi) = some si')
    (harr : arr.size = 1) (hst : st'.store = si.push (p, arr)) :
    ∃ arr' : Array (Option 𝕜), arr'.size = 1 ∧
      exec I (.seq (.instr (.un p .conj ⟨t, 0⟩ ⟨x, xo + .var i⟩))
        (.seq (.instr (.bin p .mul ⟨t, 0⟩ ⟨t, 0⟩ ⟨y, yo + .var i⟩))
          (.seq (.instr (.bin p .add dst dst ⟨t, 0⟩)) .skip))) st' =
      some { st' with
        store := si'.push (p, arr')
        cnt := st'.cnt + I.charge (.un p .conj) + I.charge (.bin p .mul) +
          I.charge (.bin p .add) } := by
  have hsz : si.size = t := by rw [← ht, Store.size_of_write_eq_some hsi]
  have hlt : ∀ {b j : ℕ} {w : 𝕜}, s.read p b j = some w → b < si.size := fun h => by
    rw [Store.size_of_write_eq_some hsi]; exact Store.lt_size_of_read_eq_some h
  have hdlt : dst.buf < si.size := by
    rw [Store.size_of_write_eq_some hsi]; exact Store.lt_size_of_write_eq_some hsi
  have r1 : ∀ arr' : Array (Option 𝕜), Store.read (si.push (p, arr')) p x (xo.eval + i) =
      some xi := by
    intro arr'
    rw [Store.read_push_of_lt (hlt hx), Store.read_of_write_eq_some_of_ne hsi, hx]
    by_cases h : x = dst.buf
    · exact Or.inr fun he => hdx h.symm he.symm
    · exact Or.inl h
  have r3 : ∀ arr' : Array (Option 𝕜), Store.read (si.push (p, arr')) p y (yo.eval + i) =
      some yi := by
    intro arr'
    rw [Store.read_push_of_lt (hlt hy), Store.read_of_write_eq_some_of_ne hsi, hy]
    by_cases h : y = dst.buf
    · exact Or.inr fun he => hdy h.symm he.symm
    · exact Or.inl h
  set a₁ := arr.set! 0 (some (star xi))
  set a₂ := a₁.set! 0 (some (star xi * yi))
  have h₁ : 0 < a₁.size := by simp [a₁, harr]
  have w3 : Store.write (si.push (p, a₂)) p dst.buf dst.idx.eval (v + star xi * yi) =
      some (si'.push (p, a₂)) := by
    rw [Store.write_push_of_lt hdlt, Store.write_of_write_eq_some hsi, hsi', Option.map_some]
  refine ⟨a₂, by simp [a₂, a₁, harr], (exec_seq_instr_un I (s := si.push (p, a₁))
      (by rw [hst]; exact r1 arr) (by rw [hI]; rfl)
      (by dsimp only [IExp.eval_zero]; rw [hst, ← hsz, Store.write_push_size (by omega)])).trans
    ((exec_seq_instr_bin I (s := si.push (p, a₂))
      (by dsimp only [IExp.eval_zero]; rw [← hsz]; exact read_push_size_set (by omega)) (r3 _)
      (by rw [hI]; rfl)
      (by dsimp only [IExp.eval_zero]; rw [← hsz, Store.write_push_size h₁])).trans
    ((exec_seq_instr_bin I
      (by rw [Store.read_push_of_lt hdlt]; exact Store.read_of_write_eq_some hsi)
      (by dsimp only [IExp.eval_zero]; rw [← hsz]; exact read_push_size_set h₁)
      (by rw [hI]; rfl) w3).trans (exec_skip I _)))⟩

private theorem exec_axpy_step (I : Interp P ι 𝕜 (OpCount P ι)) (hI : I.sem = exactSem)
    (p : P) {si si' : Store P 𝕜} {a : Cell ℕ ℕ} {x : ℕ} {xo : IExp ℕ} {y : ℕ} {yo : IExp ℕ}
    {t i : ℕ} {av xi yi : 𝕜} {st' : St P 𝕜 (OpCount P ι)} {arr : Array (Option 𝕜)}
    (ha : si.read p a.buf a.idx.eval = some av) (hx : si.read p x (xo.eval + i) = some xi)
    (hy : si.read p y (yo.eval + i) = some yi) (ht : si.size = t)
    (hsi' : si.write p y (yo.eval + i) (av * xi + yi) = some si') (harr : arr.size = 1)
    (hst : st'.store = si.push (p, arr)) :
    ∃ arr' : Array (Option 𝕜), arr'.size = 1 ∧
      exec I (.seq (.instr (.bin p .mul ⟨t, 0⟩ a ⟨x, xo + .var i⟩))
        (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨t, 0⟩)) .skip)) st' =
      some { st' with
        store := si'.push (p, arr')
        cnt := st'.cnt + I.charge (.bin p .mul) + I.charge (.bin p .add) } := by
  set a₁ := arr.set! 0 (some (av * xi))
  have h₁ : 0 < a₁.size := by simp [a₁, harr]
  have hylt : y < si.size := Store.lt_size_of_read_eq_some hy
  refine ⟨a₁, by simp [a₁, harr], (exec_seq_instr_bin I (s := si.push (p, a₁))
      (by rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some ha)]; exact ha)
      (by rw [hst, Store.read_push_of_lt (Store.lt_size_of_read_eq_some hx)]; exact hx)
      (by rw [hI]; rfl)
      (by dsimp only [IExp.eval_zero]; rw [hst, ← ht, Store.write_push_size (by omega)])).trans
    ((exec_seq_instr_bin I
      (by rw [Store.read_push_of_lt hylt]; exact hy)
      (by dsimp only [IExp.eval_zero]; rw [← ht]; exact read_push_size_set (by omega))
      (by rw [hI]; exact congrArg some (add_comm _ _))
      (by rw [Store.write_push_of_lt hylt]; dsimp only [IExp.eval_add, IExp.eval_var];
          rw [hsi', Option.map_some])).trans (exec_skip I _))⟩

end Steps

section Level2Helpers

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-! ### Frame invariant for the level-2 and level-3 kernels

Private copies of the store lemmas and the frame invariant of `Dense.lean`, to be shared in the
closing step. -/

namespace Level2

section StoreLemmas

variable {K : Type}

omit [DecidableEq P] in
private theorem shape_getElem? {s : Store P K} {b : ℕ} :
    s.shape[b]? = s[b]?.map fun x => (x.1, x.2.size) := by
  simp [Store.shape]

private theorem read_of_write_of_ne_tag {s s' : Store P K} {p q : P} {b i b' i' : ℕ} {v : K}
    (h : s.write p b i v = some s') (hq : q ≠ p) : s'.read q b' i' = s.read q b' i' := by
  by_cases hc : b' = b ∧ i' = i
  · obtain ⟨rfl, rfl⟩ := hc
    unfold Store.write at h
    rcases hb : s[b']? with _ | ⟨r, arr⟩ <;> rw [hb] at h
    · exact absurd h (by simp)
    · dsimp only at h
      split_ifs at h with hr
      obtain ⟨rfl, hi⟩ := hr
      cases h
      obtain ⟨hb', heq⟩ := Array.getElem?_eq_some_iff.mp hb
      simp [Store.read, Array.set!, hb', heq, Ne.symm hq]
  · exact Store.read_of_write_eq_some_of_ne h (by tauto)

private theorem exists_write_of_shape {s : Store P K} {p : P} {b i n : ℕ} (v : K)
    (hs : s.shape[b]? = some (p, n)) (hi : i < n) : ∃ s', s.write p b i v = some s' := by
  rw [shape_getElem?] at hs
  unfold Store.write
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at hs
  · simp at hs
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    exact ⟨_, if_pos ⟨rfl, hi⟩⟩

private theorem shape_of_read_eq_some {s : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.read p b i = some v) : ∃ n, s.shape[b]? = some (p, n) ∧ i < n := by
  unfold Store.read at h
  rw [shape_getElem?]
  rcases hb : s[b]? with _ | ⟨q, arr⟩ <;> rw [hb] at h
  · simp at h
  · dsimp only at h
    split_ifs at h with hq
    subst hq
    refine ⟨arr.size, rfl, ?_⟩
    rcases hi : arr[i]? with _ | x
    · simp [hi] at h
    · exact (Array.getElem?_eq_some_iff.mp hi).1

private theorem read_eq_none_of_shape {s : Store P K} {p q : P} {b i n : ℕ}
    (hs : s.shape[b]? = some (p, n)) (hq : q ≠ p) : s.read q b i = none := by
  rw [shape_getElem?] at hs
  unfold Store.read
  rcases hb : s[b]? with _ | ⟨r, arr⟩
  · rfl
  · rw [hb] at hs
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hs
    obtain ⟨rfl, -⟩ := hs
    simp [Ne.symm hq]

private theorem Store.ext_of_shape {s s' : Store P K} (hs : s.shape = s'.shape)
    (hr : ∀ q b i, s.read q b i = s'.read q b i) : s = s' := by
  have hsize : s.size = s'.size := by simpa [Store.shape] using congrArg Array.size hs
  refine Array.ext hsize fun b h₁ h₂ => ?_
  have hb := congrArg (·[b]?) hs
  simp only [shape_getElem?, Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem h₂,
    Option.map_some, Option.some.injEq, Prod.mk.injEq] at hb
  obtain ⟨hq, hn⟩ := hb
  refine Prod.ext hq (Array.ext hn fun i hi₁ hi₂ => ?_)
  have := hr s[b].1 b i
  simp only [Store.read, Array.getElem?_eq_getElem h₁, Array.getElem?_eq_getElem h₂, ← hq,
    if_true, Array.getElem?_eq_getElem hi₁, Array.getElem?_eq_getElem hi₂, Option.join_some]
    at this
  exact this

private theorem shape_of_foldlM_write {s s' : Store P K} {p : P} {b off : ℕ} {xs : Array K}
    (l : List ℕ) (h : l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s') :
    s'.shape = s.shape := by
  induction l generalizing s with
  | nil =>
    simp only [List.foldlM_nil, pure, Option.some.injEq] at h
    rw [h]
  | cons i l ih =>
    rw [List.foldlM_cons] at h
    change (Option.bind _ fun s => List.foldlM _ s l) = some s' at h
    obtain ⟨s₂, h₂, h₃⟩ := Option.bind_eq_some_iff.mp h
    change Option.bind xs[i]? (fun v => s.write p b (off + i) v) = some s₂ at h₂
    obtain ⟨v, -, hw⟩ := Option.bind_eq_some_iff.mp h₂
    rw [ih h₃, Store.shape_of_write_eq_some hw]

private theorem shape_of_writeBlock {s s' : Store P K} {p : P} {b off : ℕ} {xs : Array K}
    (h : s.writeBlock p b off xs = some s') : s'.shape = s.shape :=
  shape_of_foldlM_write _ h

private theorem read_eq_none_of_size_le {s : Store P K} {q : P} {b i : ℕ} (hb : s.size ≤ b) :
    s.read q b i = none := by
  simp [Store.read, Array.getElem?_eq_none hb]

private theorem read_pop_of_lt {s : Store P K} {q : P} {b i : ℕ} (hb : b < s.size - 1) :
    Store.read (Array.pop s) q b i = s.read q b i := by
  have hb' : b < s.size := by omega
  simp [Store.read, hb, Array.getElem?_eq_getElem hb']

omit [DecidableEq P] in
private theorem shape_pop (s : Store P K) : Store.shape (Array.pop s) = s.shape.pop := by
  simp [Store.shape]

omit [DecidableEq P] in
private theorem size_shape (s : Store P K) : s.shape.size = s.size := by
  simp [Store.shape]

omit [DecidableEq P] in
private theorem shape_push_size (s : Store P K) (p : P) (n : ℕ) :
    (Store.shape (s.push (p, Array.replicate n none)))[s.size]? = some (p, n) := by
  simp only [Store.shape, Array.map_push, Array.getElem?_push, Array.size_map, if_true]
  simp

private theorem blockFacts {s s₁ : Store P K} {p : P} {dst dOff L : ℕ} {Y : Array K}
    (hs₁ : s.writeBlock p dst dOff Y = some s₁) (hYs : Y.size = L) :
    (0 < L → dst < s.size) ∧ ∀ m < L, ∃ n, s.shape[dst]? = some (p, n) ∧ dOff + m < n := by
  have hdst₀ : ∀ m < L, ∃ n, s.shape[dst]? = some (p, n) ∧ dOff + m < n := by
    intro m hm
    obtain ⟨n, hn, hlt⟩ := shape_of_read_eq_some
      ((Store.read_of_writeBlock_eq_some_of_lt (j := m) hs₁ (by omega)).trans
        (Array.getElem?_eq_getElem (by omega)))
    exact ⟨n, shape_of_writeBlock hs₁ ▸ hn, hlt⟩
  refine ⟨fun h => ?_, hdst₀⟩
  obtain ⟨n, hn, -⟩ := hdst₀ 0 h
  simpa [size_shape] using (Array.getElem?_eq_some_iff.mp hn).1

omit [DecidableEq P] in
private theorem shape_push_of_lt {s : Store P K} {b : ℕ} (x : P × Array (Option K))
    (hb : b < s.size) : (Store.shape (s.push x))[b]? = s.shape[b]? := by
  simp [Store.shape, Array.getElem?_push, Nat.ne_of_lt hb]

private theorem lt_size_of_read {s : Store P K} {p : P} {b i : ℕ} {v : K}
    (h : s.read p b i = some v) : b < s.size := by
  obtain ⟨n, hn, -⟩ := shape_of_read_eq_some h
  simpa [size_shape] using (Array.getElem?_eq_some_iff.mp hn).1

private theorem exists_writeBlock_of_shape {s : Store P K} {p : P} {b off : ℕ} {xs : Array K}
    (h : ∀ i < xs.size, ∃ n, s.shape[b]? = some (p, n) ∧ off + i < n) :
    ∃ s', s.writeBlock p b off xs = some s' := by
  suffices key : ∀ (l : List ℕ), (∀ i ∈ l, i < xs.size) → ∀ s : Store P K,
      (∀ i < xs.size, ∃ n, s.shape[b]? = some (p, n) ∧ off + i < n) →
        ∃ s', l.foldlM (fun s i => do s.write p b (off + i) (← xs[i]?)) s = some s' from
    key _ (fun i hi => List.mem_range.mp hi) s h
  intro l
  induction l with
  | nil => exact fun _ s _ => ⟨s, rfl⟩
  | cons i l ih =>
    intro hl s hs
    have hi := hl i List.mem_cons_self
    obtain ⟨n, hn, hlt⟩ := hs i hi
    obtain ⟨s₁, h₁⟩ := exists_write_of_shape (i := off + i) xs[i] hn hlt
    obtain ⟨s₂, h₂⟩ := ih (fun j hj => hl j (List.mem_cons_of_mem _ hj)) s₁
      (by rw [Store.shape_of_write_eq_some h₁]; exact hs)
    refine ⟨s₂, ?_⟩
    rw [List.foldlM_cons]
    change (Option.bind (Option.bind xs[i]? fun v => s.write p b (off + i) v) fun s =>
      List.foldlM _ s l) = some s₂
    rw [Array.getElem?_eq_getElem hi, Option.bind_some, h₁, Option.bind_some, h₂]

end StoreLemmas

/-! ### Folds, the frame invariant and the steps of the run -/

section Run

omit [RCLike 𝕜]

private def DInv (s₀ : Store P 𝕜) (p : P) (T dst dOff L : ℕ) (s : Store P 𝕜)
    (g : ℕ → Option 𝕜) : Prop :=
  s.shape = s₀.shape ∧
    (∀ q b i, b ≠ T → ¬(q = p ∧ b = dst ∧ dOff ≤ i ∧ i < dOff + L) →
      s.read q b i = s₀.read q b i) ∧
    ∀ m < L, s.read p dst (dOff + m) = g m

variable {s₀ s s' : Store P 𝕜} {p : P} {T dst dOff L : ℕ} {g : ℕ → Option 𝕜}

private theorem DInv.write_dst (h : DInv s₀ p T dst dOff L s g) {m : ℕ} {v : 𝕜} (hm : m < L)
    (hw : s.write p dst (dOff + m) v = some s') :
    DInv s₀ p T dst dOff L s' (Function.update g m (some v)) := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  refine ⟨(Store.shape_of_write_eq_some hw).trans hsh, fun q b i hbT hout => ?_, fun m' hm' => ?_⟩
  · rw [← hfr q b i hbT hout]
    by_cases hq : q = p
    · subst hq
      refine Store.read_of_write_eq_some_of_ne hw ?_
      by_cases hb : b = dst
      · subst hb
        exact Or.inr fun he => hout ⟨rfl, rfl, by omega, by omega⟩
      · exact Or.inl hb
    · exact read_of_write_of_ne_tag hw hq
  · by_cases hmm : m' = m
    · subst hmm
      rw [Function.update_self]
      exact Store.read_of_write_eq_some hw
    · rw [Function.update_of_ne hmm, ← hblk m' hm']
      exact Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega))

private theorem DInv.write_scratch (h : DInv s₀ p T dst dOff L s g) {k : ℕ} {v : 𝕜}
    (hdT : 0 < L → dst ≠ T) (hw : s.write p T k v = some s') : DInv s₀ p T dst dOff L s' g := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  refine ⟨(Store.shape_of_write_eq_some hw).trans hsh, fun q b i hbT hout => ?_, fun m hm => ?_⟩
  · by_cases hq : q = p
    · subst hq
      rw [Store.read_of_write_eq_some_of_ne hw (Or.inl hbT), hfr _ b i hbT hout]
    · rw [read_of_write_of_ne_tag hw hq, hfr q b i hbT hout]
  · rw [Store.read_of_write_eq_some_of_ne hw (Or.inl (hdT (by omega))), hblk m hm]

private theorem DInv.exists_write (h : DInv s₀ p T dst dOff L s g) {b i n : ℕ} (v : 𝕜)
    (hs : s₀.shape[b]? = some (p, n)) (hi : i < n) : ∃ s', s.write p b i v = some s' :=
  exists_write_of_shape v (h.1 ▸ hs) hi

private theorem DInv.read_out (h : DInv s₀ p T dst dOff L s g) {q : P} {b i : ℕ} (hbT : b ≠ T)
    (hout : ¬(q = p ∧ b = dst ∧ dOff ≤ i ∧ i < dOff + L)) : s.read q b i = s₀.read q b i :=
  h.2.1 q b i hbT hout

private theorem pop_eq_of_DInv {st₀ s₁ sF : Store P 𝕜} {arr : Array (Option 𝕜)} {Y : Array 𝕜}
    (hs₁ : st₀.writeBlock p dst dOff Y = some s₁) (hYs : Y.size = L)
    (hI : DInv (st₀.push (p, arr)) p st₀.size dst dOff L sF g) (hg : ∀ m < L, g m = Y[m]?) :
    Array.pop sF = s₁ := by
  obtain ⟨hsh, hfr, hblk⟩ := hI
  have hsh₁ := shape_of_writeBlock hs₁
  have hsize : sF.size = st₀.size + 1 := by
    simpa [size_shape] using congrArg Array.size hsh
  have hsize₁ : s₁.size = st₀.size := by simpa [size_shape] using congrArg Array.size hsh₁
  have hread₁ : ∀ m < L, s₁.read p dst (dOff + m) = Y[m]? := fun m hm =>
    Store.read_of_writeBlock_eq_some_of_lt hs₁ (by omega)
  refine Store.ext_of_shape ?_ fun q b i => ?_
  · rw [shape_pop, hsh, hsh₁]
    simp [Store.shape]
  by_cases hb : b < st₀.size
  swap
  · rw [read_eq_none_of_size_le (by simp; omega), read_eq_none_of_size_le (by omega)]
  rw [read_pop_of_lt (by omega)]
  by_cases hin : b = dst ∧ dOff ≤ i ∧ i < dOff + L
  · obtain ⟨rfl, h₁, h₂⟩ := hin
    have hi : i = dOff + (i - dOff) := by omega
    obtain ⟨v, hv⟩ : ∃ v, Y[i - dOff]? = some v :=
      ⟨_, Array.getElem?_eq_getElem (by omega)⟩
    obtain ⟨n, hn, -⟩ := shape_of_read_eq_some ((hread₁ _ (by omega)).trans hv)
    by_cases hq : q = p
    · subst hq
      rw [hi, hblk _ (by omega), hg _ (by omega), hread₁ _ (by omega)]
    · rw [read_eq_none_of_shape hn hq, hfr q b i (by omega) (by tauto),
        Store.read_push_of_lt hb, read_eq_none_of_shape (hsh₁ ▸ hn) hq]
  · rw [hfr q b i (by omega) (by tauto), Store.read_push_of_lt hb,
      Store.read_of_writeBlock_eq_some_of_ne hs₁ (by omega)]

private theorem DInv.push (h : DInv s₀ p s₀.size dst dOff L s g) (x : P × Array (Option 𝕜))
    (hdT : 0 < L → dst < s₀.size) :
    DInv (s₀.push x) p s₀.size dst dOff L (s.push x) g := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  have hsz : s.size = s₀.size := by simpa [size_shape] using congrArg Array.size hsh
  have hsh' := hsh
  simp only [Store.shape] at hsh'
  refine ⟨by simp [Store.shape, hsh'], fun q b i hbT hout => ?_, fun m hm => ?_⟩
  · by_cases hb : b < s₀.size
    · rw [Store.read_push_of_lt (by omega), Store.read_push_of_lt hb, hfr q b i hbT hout]
    · rw [read_eq_none_of_size_le (by simp; omega), read_eq_none_of_size_le (by simp; omega)]
  · rw [Store.read_push_of_lt (by have := hdT (by omega); omega), hblk m hm]

private theorem DInv.writeBlock (h : DInv s₀ p T dst dOff L s g) {off : ℕ} {xs : Array 𝕜}
    (hw : s.writeBlock p dst (dOff + off) xs = some s') (hL : off + xs.size ≤ L) :
    DInv s₀ p T dst dOff L s'
      (fun k => if off ≤ k ∧ k < off + xs.size then xs[k - off]? else g k) := by
  obtain ⟨hsh, hfr, hblk⟩ := h
  have hsh' := shape_of_writeBlock hw
  refine ⟨hsh'.trans hsh, fun q b i hbT hout => ?_, fun k hk => ?_⟩
  · by_cases hin : b = dst ∧ dOff + off ≤ i ∧ i < dOff + off + xs.size
    · obtain ⟨rfl, h₁, h₂⟩ := hin
      have hq : q ≠ p := fun hq => hout ⟨hq, rfl, by omega, by omega⟩
      obtain ⟨v, hv⟩ : ∃ v, xs[i - (dOff + off)]? = some v :=
        ⟨_, Array.getElem?_eq_getElem (by omega)⟩
      obtain ⟨n, hn, -⟩ := shape_of_read_eq_some
        ((Store.read_of_writeBlock_eq_some_of_lt (j := i - (dOff + off)) hw (by omega)).trans hv)
      rw [← hfr q b i hbT hout, read_eq_none_of_shape hn hq,
        read_eq_none_of_shape (hsh' ▸ hn) hq]
    · rw [Store.read_of_writeBlock_eq_some_of_ne hw (by omega), hfr q b i hbT hout]
  · beta_reduce
    by_cases hin : off ≤ k ∧ k < off + xs.size
    · rw [if_pos hin, show dOff + k = dOff + off + (k - off) by omega]
      exact Store.read_of_writeBlock_eq_some_of_lt hw (by omega)
    · rw [if_neg hin, Store.read_of_writeBlock_eq_some_of_ne hw (by omega), hblk k hk]

end Run


section GemvSteps

variable {I : Interp P ι 𝕜 (OpCount P ι)} {s₀ : Store P 𝕜} {p : P} {T A x y L : ℕ}
  {m n ao xo yo : IExp ℕ}

private theorem exec_gemvStep (hsem : I.sem = exactSem) (hc : ∀ k, I.charge k = .single k 1)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {i j : ℕ} {a xj w : 𝕜}
    (h : DInv s₀ p T y yo.eval L σ.store g) (hT : s₀.shape[T]? = some (p, 1)) (hyT : y ≠ T)
    (hi : i < L) (hy : ∃ k, s₀.shape[y]? = some (p, k) ∧ yo.eval + i < k)
    (hA : σ.store.read p A (ao.eval + i + m.eval * j) = some a)
    (hx : σ.store.read p x (xo.eval + j) = some xj) (hw : g i = some w) :
    ∃ s', exec I (.seq (.instr (.bin p .mul ⟨T, 0⟩ ⟨A, ao + .var i + m * .var j⟩
        ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩
          ⟨T, 0⟩)) .skip)) σ = some { σ with store := s', cnt := σ.cnt +
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      DInv s₀ p T y yo.eval L s' (Function.update g i (some (w + a * xj))) := by
  obtain ⟨s₁, h₁⟩ := h.exists_write (a * xj) hT one_pos
  have h₁' := h.write_scratch (fun _ => hyT) h₁
  obtain ⟨k, hysh, hylt⟩ := hy
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write (w + a * xj) hysh hylt
  refine ⟨s₂, ?_, h₁'.write_dst hi h₂⟩
  have rw₁ : s₁.read p y (yo.eval + i) = some w := by rw [h₁'.2.2 _ hi, hw]
  simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
    IExp.eval_zero, hA, hx, hsem, hc, h₁, Option.bind_some, Option.map_some,
    Store.read_of_write_eq_some h₁, rw₁, exactSem, h₂]
  simp only [add_assoc]

private structure GemvCtx (I : Interp P ι 𝕜 (OpCount P ι)) (s₀ : Store P 𝕜) (p : P)
    (T A x y : ℕ) (m n ao xo yo : ℕ) (a : ℕ → ℕ → 𝕜) (xv : ℕ → 𝕜) : Prop where
  sem : I.sem = exactSem
  charge : ∀ k, I.charge k = .single k 1
  scratch : s₀.shape[T]? = some (p, 1)
  y_ne : 0 < m → y ≠ T
  y_shape : ∀ i < m, ∃ k, s₀.shape[y]? = some (p, k) ∧ yo + i < k
  A_read : ∀ i < m, ∀ j < n, s₀.read p A (ao + i + m * j) = some (a i j)
  A_out : ∀ i < m, ∀ j < n, A ≠ T ∧ ¬(p = p ∧ A = y ∧ yo ≤ ao + i + m * j ∧
    ao + i + m * j < yo + m)
  x_read : ∀ j < n, s₀.read p x (xo + j) = some (xv j)
  x_out : ∀ j < n, x ≠ T ∧ ¬(p = p ∧ x = y ∧ yo ≤ xo + j ∧ xo + j < yo + m)

variable {a : ℕ → ℕ → 𝕜} {xv : ℕ → 𝕜}

private theorem exec_gemvRow
    (hC : GemvCtx I s₀ p T A x y m.eval n.eval ao.eval xo.eval yo.eval a xv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {j : ℕ} (hj : j < n.eval)
    (h : DInv s₀ p T y yo.eval m.eval σ.store g)
    (hg : ∀ i < m.eval, g i = some (∑ j' ∈ Finset.range j, a i j' * xv j')) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 0⟩
        ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add
          ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨T, 0⟩)) .skip)) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + m.eval •
          (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
        DInv s₀ p T y yo.eval m.eval s' g' ∧
        ∀ i < m.eval, g' i = some (∑ j' ∈ Finset.range (j + 1), a i j' * xv j') := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + i' • (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      DInv s₀ p T y yo.eval m.eval s' g' ∧
      ∀ i < m.eval, g' i = some (∑ j' ∈ Finset.range (if i < i' then j + 1 else j),
        a i j' * xv j')) ⟨σ.store, g, by simp, h, by simpa using hg⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow⟩ =>
      ⟨hrun, s', g', hσ, hI, fun i hi => by simpa [hi] using hrow i hi⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : DInv s₀ p T y yo.eval m.eval σ'.store g' := hσ ▸ hI
  obtain ⟨hAT, hAout⟩ := hC.A_out i' hi' j hj
  obtain ⟨hxT, hxout⟩ := hC.x_out j hj
  obtain ⟨s'', hrun, hI'⟩ := exec_gemvStep hC.sem hC.charge hI hC.scratch
    (hC.y_ne (by omega)) hi' (hC.y_shape i' hi')
    ((hI.read_out hAT hAout).trans (hC.A_read i' hi' j hj))
    ((hI.read_out hxT hxout).trans (hC.x_read j hj)) (by simpa using hrow i' hi')
  refine ⟨_, hrun, s'', _, ?_, hI', fun i hi => ?_⟩
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hii : i = i'
    · subst hii
      simp [Finset.sum_range_succ]
    · rw [Function.update_of_ne hii, hrow i hi]
      have : (i < i' + 1) = (i < i') := by
        apply propext
        omega
      simp only [this]

private theorem exec_gemvCols
    (hC : GemvCtx I s₀ p T A x y m.eval n.eval ao.eval xo.eval yo.eval a xv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (h : DInv s₀ p T y yo.eval m.eval σ.store g) (hg : ∀ i < m.eval, g i = some 0) :
    ∃ σ', exec I (.loop n fun j => .seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 0⟩
        ⟨A, ao + .var i + m * .var j⟩ ⟨x, xo + .var j⟩)) (.seq (.instr (.bin p .add
          ⟨y, yo + .var i⟩ ⟨y, yo + .var i⟩ ⟨T, 0⟩)) .skip)) .skip) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + n.eval • (m.eval •
          (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
        DInv s₀ p T y yo.eval m.eval s' g' ∧
        ∀ i < m.eval, g' i = some (∑ j ∈ Finset.range n.eval, a i j * xv j) := by
  refine exists_exec_loop_eq_some_of_forall I (fun j' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + j' • (m.eval • (.single (.bin p .mul) 1 +
        .single (.bin p .add) 1)) } ∧ DInv s₀ p T y yo.eval m.eval s' g' ∧
      ∀ i < m.eval, g' i = some (∑ j ∈ Finset.range j', a i j * xv j))
    ⟨σ.store, g, by simp, h, by simpa using hg⟩ ?_
  rintro j hj σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : DInv s₀ p T y yo.eval m.eval σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hrow'⟩ := exec_gemvRow hC hj hI hrow
  refine ⟨_, by rw [exec_seq_skip, hrun], s'', g'', ?_, hI', hrow'⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]

private theorem exec_gemvZero (hsem : I.sem = exactSem) (hc : ∀ k, I.charge k = .single k 1)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (hy : ∀ i < m.eval, ∃ k, s₀.shape[y]? = some (p, k) ∧ yo.eval + i < k)
    (h : DInv s₀ p T y yo.eval m.eval σ.store g) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.lit p ⟨y, yo + .var i⟩ 0)) .skip) σ =
        some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + m.eval • .single (.lit p) 1 } ∧
        DInv s₀ p T y yo.eval m.eval s' g' ∧ ∀ i < m.eval, g' i = some 0 := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + i' • .single (.lit p) 1 } ∧
      DInv s₀ p T y yo.eval m.eval s' g' ∧ ∀ i < i', g' i = some 0)
    ⟨σ.store, g, by simp, h, by simp⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow⟩ => ⟨hrun, s', g', hσ, hI, hrow⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : DInv s₀ p T y yo.eval m.eval σ'.store g' := hσ ▸ hI
  obtain ⟨k, hysh, hylt⟩ := hy i' hi'
  obtain ⟨s'', hw⟩ := hI.exists_write 0 hysh hylt
  refine ⟨{ σ' with store := s'', cnt := σ'.cnt + .single (.lit p) 1 }, ?_, s'', _, ?_,
    hI.write_dst hi' hw, fun i hi => ?_⟩
  · simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_var, hsem, hc, exactSem,
      Rat.cast_zero, Option.bind_some, hw, Option.map_some]
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases hii : i = i'
    · subst hii
      simp
    · rw [Function.update_of_ne hii]
      exact hrow i (by omega)

end GemvSteps

section GerSteps

variable {I : Interp P ι 𝕜 (OpCount P ι)} {s₀ : Store P 𝕜} {p : P} {T A x y : ℕ}
  {m n ao xo yo : IExp ℕ}

private structure GerCtx (I : Interp P ι 𝕜 (OpCount P ι)) (s₀ : Store P 𝕜) (p : P)
    (T A x y : ℕ) (a : Cell ℕ ℕ) (m n ao xo yo : ℕ) (av : 𝕜) (xv yv : ℕ → 𝕜) : Prop where
  sem : I.sem = exactSem
  charge : ∀ k, I.charge k = .single k 1
  scratch : s₀.shape[T]? = some (p, 2)
  A_ne : 0 < m * n → A ≠ T
  A_shape : ∀ k < m * n, ∃ l, s₀.shape[A]? = some (p, l) ∧ ao + k < l
  a_read : s₀.read p a.buf a.idx.eval = some av
  a_out : a.buf ≠ T ∧ ¬(p = p ∧ a.buf = A ∧ ao ≤ a.idx.eval ∧ a.idx.eval < ao + m * n)
  x_read : ∀ i < m, s₀.read p x (xo + i) = some (xv i)
  x_out : ∀ i < m, x ≠ T ∧ ¬(p = p ∧ x = A ∧ ao ≤ xo + i ∧ xo + i < ao + m * n)
  y_read : ∀ j < n, s₀.read p y (yo + j) = some (yv j)
  y_out : ∀ j < n, y ≠ T ∧ ¬(p = p ∧ y = A ∧ ao ≤ yo + j ∧ yo + j < ao + m * n)

variable {a : Cell ℕ ℕ} {av : 𝕜} {xv yv : ℕ → 𝕜} {M : ℕ → ℕ → 𝕜}

private theorem exec_gerStep
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {i j : ℕ} {c₀ w : 𝕜} (hi : i < m.eval)
    (hj : j < n.eval) (h : DInv s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (ht : σ.store.read p T 0 = some c₀) (hw : g (i + m.eval * j) = some w) :
    ∃ s', exec I (.seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
        (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩
          ⟨T, 1⟩)) .skip)) σ = some { σ with store := s', cnt := σ.cnt +
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      DInv s₀ p T A ao.eval (m.eval * n.eval) s'
        (Function.update g (i + m.eval * j) (some (w + xv i * c₀))) ∧
      s'.read p T 0 = some c₀ := by
  have hk : i + m.eval * j < m.eval * n.eval := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
  have hAT := hC.A_ne (by omega)
  obtain ⟨s₁, h₁⟩ := h.exists_write (xv i * c₀) hC.scratch (by omega : 1 < 2)
  have h₁' := h.write_scratch (fun _ => hAT) h₁
  obtain ⟨l, hAsh, hAlt⟩ := hC.A_shape _ hk
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write (w + xv i * c₀) hAsh hAlt
  refine ⟨s₂, ?_, h₁'.write_dst hk h₂, ?_⟩
  · have rx : σ.store.read p x (xo.eval + i) = some (xv i) :=
      (h.read_out (hC.x_out i hi).1 (hC.x_out i hi).2).trans (hC.x_read i hi)
    have rA : s₁.read p A (ao.eval + i + m.eval * j) = some w := by
      rw [Nat.add_assoc, h₁'.2.2 _ hk, hw]
    rw [← Nat.add_assoc] at h₂
    simp only [exec, Instr.run, Instr.kind, IExp.eval_add, IExp.eval_mul, IExp.eval_var,
      IExp.eval_zero, IExp.eval_one, rx, ht, hC.sem, hC.charge, h₁, Option.bind_some,
      Option.map_some, Store.read_of_write_eq_some h₁, rA, exactSem, h₂]
    simp only [add_assoc]
  · rw [Store.read_of_write_eq_some_of_ne h₂ (Or.inl (Ne.symm hAT)),
      Store.read_of_write_eq_some_of_ne h₁ (Or.inr (by omega)), ht]

private def gerVal (M : ℕ → ℕ → 𝕜) (av : 𝕜) (xv yv : ℕ → 𝕜) (i j : ℕ) (b : Prop)
    [Decidable b] : Option 𝕜 :=
  some (if b then M i j + xv i * (av * star (yv j)) else M i j)

private theorem exec_gerRow
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {j : ℕ} (hj : j < n.eval)
    (h : DInv s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (ht : σ.store.read p T 0 = some (av * star (yv j)))
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = gerVal M av xv yv i j' (j' < j)) :
    ∃ σ', exec I (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
        (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩ ⟨A, ao + .var i + m * .var j⟩
          ⟨T, 1⟩)) .skip)) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + m.eval •
          (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
        DInv s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          gerVal M av xv yv i j' (j' < j + 1) := by
  refine (exists_exec_loop_eq_some_of_forall I (fun i' σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + i' • (.single (.bin p .mul) 1 + .single (.bin p .add) 1) } ∧
      DInv s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
      s'.read p T 0 = some (av * star (yv j)) ∧ ∀ i < m.eval, ∀ j' < n.eval,
        g' (i + m.eval * j') = gerVal M av xv yv i j' (j' < j ∨ (j' = j ∧ i < i')))
    ⟨σ.store, g, by simp, h, ht, by simpa using hg⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, _, hrow⟩ => ⟨hrun, s', g', hσ, hI, fun i hi j' hj' => by
      rw [hrow i hi j' hj']
      unfold gerVal
      split_ifs <;> first | rfl | (exfalso; omega)⟩
  rintro i' hi' σ' ⟨s, g', hσ, hI, ht', hrow⟩
  replace hI : DInv s₀ p T A ao.eval (m.eval * n.eval) σ'.store g' := hσ ▸ hI
  replace ht' : σ'.store.read p T 0 = some (av * star (yv j)) := hσ ▸ ht'
  have hw := hrow i' hi' j hj
  simp only [gerVal, lt_irrefl, false_or, and_false, if_false] at hw
  obtain ⟨s'', hrun, hI', ht''⟩ := exec_gerStep hC hi' hj hI ht' hw
  refine ⟨_, hrun, s'', _, ?_, hI', ht'', fun i hi j' hj' => ?_⟩
  · subst hσ
    simp only [succ_nsmul, add_assoc]
  · by_cases he : i = i' ∧ j' = j
    · obtain ⟨rfl, rfl⟩ := he
      simp [gerVal]
    · rw [Function.update_of_ne (fun h' => he
        ((Nat.add_mul_eq_add_mul_iff_of_lt hi hi').mp h')), hrow i hi j' hj']
      unfold gerVal
      split_ifs <;> first | rfl | (exfalso; omega)

private theorem exec_gerCol
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜} {j : ℕ} (hj : j < n.eval)
    (h : DInv s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = gerVal M av xv yv i j' (j' < j)) :
    ∃ σ', exec I (.seq (.instr (.un p .conj ⟨T, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨T, 0⟩ a ⟨T, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨T, 1⟩)) .skip)) .skip))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + (.single (.un p .conj) 1 +
          .single (.bin p .mul) 1 + m.eval •
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
        DInv s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          gerVal M av xv yv i j' (j' < j + 1) := by
  obtain ⟨hyT, hyout⟩ := hC.y_out j hj
  have ry : σ.store.read p y (yo.eval + j) = some (yv j) :=
    (h.read_out hyT hyout).trans (hC.y_read j hj)
  obtain ⟨s₁, h₁⟩ := h.exists_write (star (yv j)) hC.scratch (by omega : 0 < 2)
  have h₁' := h.write_scratch hC.A_ne h₁
  have ra : s₁.read p a.buf a.idx.eval = some av :=
    (h₁'.read_out hC.a_out.1 hC.a_out.2).trans hC.a_read
  obtain ⟨s₂, h₂⟩ := h₁'.exists_write (av * star (yv j)) hC.scratch (by omega : 0 < 2)
  have h₂' := h₁'.write_scratch hC.A_ne h₂
  obtain ⟨σ'', hrun, s'', g'', hσ'', hI'', hrow''⟩ := exec_gerRow (M := M) hC hj (σ := { σ with
      store := s₂, cnt := σ.cnt + .single (.un p .conj) 1 + .single (.bin p .mul) 1 }) h₂'
    (Store.read_of_write_eq_some h₂) hg
  refine ⟨σ'', ?_, s'', g'', ?_, hI'', hrow''⟩
  · rw [exec_seq_instr_un I (s := s₁) ry (by rw [hC.sem]; rfl) h₁,
      exec_seq_instr_bin I (s := s₂) ra (Store.read_of_write_eq_some h₁) (by rw [hC.sem]; rfl)
        h₂, exec_seq_skip]
    simp only [hC.charge]
    exact hrun
  · rw [hσ'']
    simp only [add_assoc]

private theorem exec_gerCols
    (hC : GerCtx I s₀ p T A x y a m.eval n.eval ao.eval xo.eval yo.eval av xv yv)
    {σ : St P 𝕜 (OpCount P ι)} {g : ℕ → Option 𝕜}
    (h : DInv s₀ p T A ao.eval (m.eval * n.eval) σ.store g)
    (hg : ∀ i < m.eval, ∀ j' < n.eval, g (i + m.eval * j') = some (M i j')) :
    ∃ σ', exec I (.loop n fun j => .seq (.instr (.un p .conj ⟨T, 0⟩ ⟨y, yo + .var j⟩))
        (.seq (.instr (.bin p .mul ⟨T, 0⟩ a ⟨T, 0⟩))
        (.seq (.loop m fun i => .seq (.instr (.bin p .mul ⟨T, 1⟩ ⟨x, xo + .var i⟩ ⟨T, 0⟩))
          (.seq (.instr (.bin p .add ⟨A, ao + .var i + m * .var j⟩
            ⟨A, ao + .var i + m * .var j⟩ ⟨T, 1⟩)) .skip)) .skip))) σ = some σ' ∧
      ∃ s' g', σ' = { σ with store := s', cnt := σ.cnt + n.eval •
          (.single (.un p .conj) 1 + .single (.bin p .mul) 1 + m.eval •
            (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
        DInv s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
        ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') =
          some (M i j' + xv i * (av * star (yv j'))) := by
  refine (exists_exec_loop_eq_some_of_forall I (fun j σ' => ∃ s' g', σ' = { σ with
      store := s', cnt := σ.cnt + j • (.single (.un p .conj) 1 + .single (.bin p .mul) 1 +
        m.eval • (.single (.bin p .mul) 1 + .single (.bin p .add) 1)) } ∧
      DInv s₀ p T A ao.eval (m.eval * n.eval) s' g' ∧
      ∀ i < m.eval, ∀ j' < n.eval, g' (i + m.eval * j') = gerVal M av xv yv i j' (j' < j))
    ⟨σ.store, g, by simp, h, fun i hi j' hj' => by simp [gerVal, hg i hi j' hj']⟩ ?_).imp
    fun σ' ⟨hrun, s', g', hσ, hI, hrow⟩ => ⟨hrun, s', g', hσ, hI, fun i hi j' hj' => by
      simpa [gerVal, hj'] using hrow i hi j' hj'⟩
  rintro j hj σ' ⟨s, g', hσ, hI, hrow⟩
  replace hI : DInv s₀ p T A ao.eval (m.eval * n.eval) σ'.store g' := hσ ▸ hI
  obtain ⟨σ'', hrun, s'', g'', rfl, hI', hrow'⟩ := exec_gerCol hC hj hI hrow
  refine ⟨_, hrun, s'', g'', ?_, hI', hrow'⟩
  subst hσ
  simp only [succ_nsmul, add_assoc]

end GerSteps

end Level2

end Level2Helpers

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
  set S : ℕ → 𝕜 := fun i => ∑ j ∈ Finset.range i, star (xs j) * ys j with hS
  have hw := Store.exists_write_eq_some_of_write_eq_some h₁
  obtain ⟨s0, hs0⟩ := hw ((0 : ℚ) : 𝕜)
  have hv0 : I.sem.lit p (0 : ℚ) = some ((0 : ℚ) : 𝕜) := by rw [hI]; rfl
  rw [dot_run, exec_seq_skip, exec_named, exec_seq_instr_lit I hv0 hs0, exec_alloc,
    exec_seq_skip]
  refine exists_map_eq_some (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜, ∃ arr : Array (Option 𝕜),
      st.store.write p dst.buf dst.idx.eval (S i) = some si ∧ arr.size = 1 ∧
      st'.store = si.push (p, arr) ∧ st'.cnt = st.cnt + I.charge (.lit p) +
        i • (I.charge (.un p .conj) + I.charge (.bin p .mul) + I.charge (.bin p .add)) ∧
      st'.pos = st.pos ∧ st'.cur = Function.update st.cur p (st.cur p + 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.curW = st.curW + 1 * I.width p ∧ st'.peakW = max st.peakW (st.curW + 1 * I.width p))
    ?_ ?_) ?_
  · exact ⟨s0, Array.replicate 1 none, by simpa [S] using hs0, by simp, rfl, by simp, rfl,
      by simp, by simp, by simp, by simp⟩
  · intro i hi st' ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    obtain ⟨si', hsi'⟩ := hw (S (i + 1))
    have hsi'' := hsi'
    rw [show S (i + 1) = S i + star (xs i) * ys i from Finset.sum_range_succ _ _] at hsi''
    obtain ⟨arr', harr', hrun⟩ := exec_dot_step I hI p (hx i hi) (hy i hi)
      (fun h => hdx h i hi) (fun h => hdy h i hi) (Store.size_of_write_eq_some hs0).symm hsi
      hsi'' harr hst
    refine ⟨_, hrun, si', arr', hsi', harr', rfl, ?_, hpos, hcur, hpeak, hcurW, hpeakW⟩
    simp only [hcnt, succ_nsmul, add_assoc]
  · intro stL ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨by simp [hst, hsi₁], hpos, by simp [hcur], by simp [hcurW], ?_, hpeak,
      by simp [hpeakW]⟩
    simp only [hcnt, hc]
    abel

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
  rw [Store.writeBlock_map_range] at h₁
  rw [axpy_run, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  refine exists_map_eq_some (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜, ∃ arr : Array (Option 𝕜),
      (List.range i).foldlM (fun s j => s.write p y (yo.eval + j) (av * xs j + ys j)) st.store =
        some si ∧ arr.size = 1 ∧
      st'.store = si.push (p, arr) ∧
      st'.cnt = st.cnt + i • (I.charge (.bin p .mul) + I.charge (.bin p .add)) ∧
      st'.pos = st.pos ∧ st'.cur = Function.update st.cur p (st.cur p + 1) ∧
      st'.peak = Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      st'.curW = st.curW + 1 * I.width p ∧ st'.peakW = max st.peakW (st.curW + 1 * I.width p))
    ?_ ?_) ?_
  · exact ⟨st.store, Array.replicate 1 none, rfl, by simp, rfl, by simp, rfl, by simp, by simp,
      by simp, by simp⟩
  · intro i hi st' ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [foldlM_range_succ, hsi, Option.bind_some] at hstep
    have hrd : ∀ {b j : ℕ}, (∀ k < i, b ≠ y ∨ j ≠ yo.eval + k) →
        si.read p b j = st.store.read p b j := fun h =>
      Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk =>
        h k (List.mem_range.mp hk)
    have ha' : si.read p a.buf a.idx.eval = some av := by
      rw [hrd fun k hk => ?_, ha]
      by_cases h : a.buf = y
      · exact Or.inr (hay h k (hk.trans hi))
      · exact Or.inl h
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [hrd fun k hk => ?_, hx i hi]
      by_cases h : x = y
      · exact Or.inr fun he => absurd (hxy h i hi k (hk.trans hi) he) (by omega)
      · exact Or.inl h
    have hy' : si.read p y (yo.eval + i) = some (ys i) := by
      rw [hrd fun k hk => Or.inr (by omega), hy i hi]
    obtain ⟨arr', harr', hrun⟩ := exec_axpy_step I hI p ha' hx' hy'
      (Store.size_of_foldlM_write_eq_some _ _ _ hsi) hstep harr hst
    refine ⟨_, hrun, si', arr', hsi', harr', rfl, ?_, hpos, hcur, hpeak, hcurW, hpeakW⟩
    simp only [hcnt, succ_nsmul, add_assoc]
  · intro stL ⟨si, arr, hsi, harr, hst, hcnt, hpos, hcur, hpeak, hcurW, hpeakW⟩
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨by simp [hst, hsi₁], hpos, by simp [hcur], by simp [hcurW], ?_, hpeak,
      by simp [hpeakW]⟩
    simp only [hcnt, hc]

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
  rw [Store.writeBlock_map_range] at h₁
  rw [scal_run, exec_seq_skip, exec_named, exec_seq_skip]
  refine Exists.imp (fun stL h => ⟨h.1, ?_⟩) (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜,
      (List.range i).foldlM (fun s j => s.write p x (xo.eval + j) (av * xs j)) st.store =
        some si ∧ st' = { st with store := si, cnt := st.cnt + i • I.charge (.bin p .mul) })
    ⟨st.store, rfl, by simp⟩ ?_)
  · obtain ⟨-, si, hsi, rfl⟩ := h
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨hsi₁, rfl, rfl, rfl, by simp [hc], rfl, rfl⟩
  · rintro i hi _ ⟨si, hsi, rfl⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [foldlM_range_succ, hsi, Option.bind_some] at hstep
    have hrd : ∀ {b j : ℕ}, (∀ k < i, b ≠ x ∨ j ≠ xo.eval + k) →
        si.read p b j = st.store.read p b j := fun h =>
      Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk =>
        h k (List.mem_range.mp hk)
    have ha' : si.read p a.buf a.idx.eval = some av := by
      rw [hrd fun k hk => ?_, ha]
      by_cases h : a.buf = x
      · exact Or.inr (hax h k (hk.trans hi))
      · exact Or.inl h
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [hrd fun k hk => Or.inr (by omega), hx i hi]
    refine ⟨_, (exec_seq_instr_bin I ha' hx' (by rw [hI]; rfl) hstep).trans (exec_skip I _),
      si', hsi', ?_⟩
    rw [succ_nsmul, ← add_assoc]

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
  rw [Store.writeBlock_map_range] at h₁
  rw [rscl_run, exec_seq_skip, exec_named, exec_seq_skip]
  refine Exists.imp (fun stL h => ⟨h.1, ?_⟩) (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜,
      (List.range i).foldlM (fun s j => s.write p x (xo.eval + j) (xs j / av)) st.store =
        some si ∧ st' = { st with store := si, cnt := st.cnt + i • I.charge (.bin p .div) })
    ⟨st.store, rfl, by simp⟩ ?_)
  · obtain ⟨-, si, hsi, rfl⟩ := h
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨hsi₁, rfl, rfl, rfl, by simp [hc], rfl, rfl⟩
  · rintro i hi _ ⟨si, hsi, rfl⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [foldlM_range_succ, hsi, Option.bind_some] at hstep
    have hrd : ∀ {b j : ℕ}, (∀ k < i, b ≠ x ∨ j ≠ xo.eval + k) →
        si.read p b j = st.store.read p b j := fun h =>
      Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk =>
        h k (List.mem_range.mp hk)
    have ha' : si.read p a.buf a.idx.eval = some av := by
      rw [hrd fun k hk => ?_, ha]
      by_cases h : a.buf = x
      · exact Or.inr (hax h k (hk.trans hi))
      · exact Or.inl h
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [hrd fun k hk => Or.inr (by omega), hx i hi]
    refine ⟨_, (exec_seq_instr_bin I hx' ha' (by rw [hI]; simp [exactSem, hav]) hstep).trans
      (exec_skip I _), si', hsi', ?_⟩
    rw [succ_nsmul, ← add_assoc]

omit [RCLike 𝕜] hI in
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
  rw [Store.writeBlock_map_range] at h₁
  rw [copyv_run, exec_seq_skip, exec_named, exec_seq_skip]
  refine Exists.imp (fun stL h => ⟨h.1, ?_⟩) (exists_exec_loop_eq_some_of_forall I (fun i st' =>
    ∃ si : Store P 𝕜,
      (List.range i).foldlM (fun s j => s.write p y (yo.eval + j) (xs j)) st.store =
        some si ∧ st' = { st with store := si, cnt := st.cnt + i • I.charge (.copy p) })
    ⟨st.store, rfl, by simp⟩ ?_)
  · obtain ⟨-, si, hsi, rfl⟩ := h
    have hsi₁ : si = s₁ := Option.some.inj (hsi.symm.trans h₁)
    refine ⟨hsi₁, rfl, rfl, rfl, by simp [hc], rfl, rfl⟩
  · rintro i hi _ ⟨si, hsi, rfl⟩
    obtain ⟨si', hsi'⟩ := exists_foldlM_range_eq_some_of_le h₁ hi
    have hstep := hsi'
    rw [foldlM_range_succ, hsi, Option.bind_some] at hstep
    have hx' : si.read p x (xo.eval + i) = some (xs i) := by
      rw [Store.read_of_foldlM_write_eq_some_of_forall_ne _ _ _ hsi fun k hk => ?_, hx i hi]
      by_cases h : x = y
      · exact Or.inr fun he =>
          absurd (hxy h i hi k ((List.mem_range.mp hk).trans hi) he)
            (by have := List.mem_range.mp hk; omega)
      · exact Or.inl h
    refine ⟨_, (exec_seq_instr_copy I hx' hstep).trans (exec_skip I _), si', hsi', ?_⟩
    rw [succ_nsmul, ← add_assoc]

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
  obtain ⟨s₀, hs₀⟩ := Store.exists_write_eq_some_of_write_eq_some h₁
    (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)
  obtain ⟨st₁, h1, hs1, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_dot I hI hc p st dst x xo x xo n xs xs hx hx hdx hdx s₀ hs₀
  have hnn : (0 : 𝕜) ≤ ∑ i ∈ Finset.range n.eval, star (xs i) * xs i :=
    Finset.sum_nonneg fun i _ => star_mul_self_nonneg (xs i)
  have hv : I.sem.un p .sqrt (∑ i ∈ Finset.range n.eval, star (xs i) * xs i) =
      some ((√(RCLike.re (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)) : ℝ) : 𝕜) := by
    rw [hI]; exact if_pos hnn
  rw [nrm2_run, exec_seq_skip, exec_named, exec_run_bind I (b := dot p dst x xo x xo n)
    (fun _ => rfl), h1, Option.bind_some]
  refine ⟨_, (exec_seq_instr_un I (by rw [hs1]; exact Store.read_of_write_eq_some hs₀) hv
    (by rw [hs1, Store.write_of_write_eq_some hs₀]; exact h₁)).trans (exec_skip I _), rfl, hpos,
    hcur, hcurW, ?_, hpeak, hpeakW⟩
  simp only [hcnt, hc, add_assoc]

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
  obtain ⟨hylt, hyshape⟩ := Level2.blockFacts (L := m.eval) h₁ (by simp)
  rw [gemv_run, exec_seq_skip, exec_named, exec_seq]
  obtain ⟨σ₁, h0, s₁', g₁, rfl, hI₁, hz⟩ := Level2.exec_gemvZero (I := I) (s₀ := st.store)
    (T := st.store.size) (σ := st) hI hc hyshape ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩
  have hsz : s₁'.size = st.store.size := by
    simpa [Level2.size_shape] using congrArg Array.size hI₁.1
  rw [h0, Option.bind_some, exec_alloc, exec_seq_skip]
  dsimp only
  rw [hsz]
  have hC : Level2.GemvCtx I (st.store.push (p, Array.replicate (1 : IExp ℕ).eval none)) p
      st.store.size A x y m.eval n.eval ao.eval xo.eval yo.eval
      (fun i j => if h : i < m.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0)
      (fun j => if h : j < n.eval then xv ⟨j, h⟩ else 0) :=
    { sem := hI
      charge := hc
      scratch := Level2.shape_push_size _ _ _
      y_ne := fun h => Nat.ne_of_lt (hylt h)
      y_shape := fun i hi => by
        rw [Level2.shape_push_of_lt _ (hylt (by omega))]
        exact hyshape i hi
      A_read := fun i hi j hj => by
        have := hA ⟨i, hi⟩ ⟨j, hj⟩
        rw [Store.read_push_of_lt (Level2.lt_size_of_read this), this]
        simp [hi, hj]
      A_out := fun i hi j hj => by
        have hlt : i + m.eval * j < m.eval * n.eval := Nat.add_mul_lt_mul_of_lt_of_lt hi hj
        refine ⟨Nat.ne_of_lt (Level2.lt_size_of_read (hA ⟨i, hi⟩ ⟨j, hj⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyA rfl with h | h <;> omega
      x_read := fun j hj => by
        have := hx ⟨j, hj⟩
        rw [Store.read_push_of_lt (Level2.lt_size_of_read this), this]
        simp [hj]
      x_out := fun j hj => by
        refine ⟨Nat.ne_of_lt (Level2.lt_size_of_read (hx ⟨j, hj⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyx rfl with h | h <;> omega }
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := Level2.exec_gemvCols hC
    (σ := { st with
      store := s₁'.push (p, Array.replicate (1 : IExp ℕ).eval none)
      cnt := st.cnt + m.eval • .single (.lit p) 1
      cur := Function.update st.cur p (st.cur p + (1 : IExp ℕ).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (1 : IExp ℕ).eval))
      curW := st.curW + (1 : IExp ℕ).eval * I.width p
      peakW := max st.peakW (st.curW + (1 : IExp ℕ).eval * I.width p) })
    (Level2.DInv.push hI₁ _ hylt) hz
  rw [hF, Option.map_some]
  refine ⟨_, rfl, Level2.pop_eq_of_DInv h₁ (by simp) hIF fun i hi => ?_, rfl, ?_, ?_, ?_, ?_,
    ?_⟩
  · rw [hgF i hi, Array.getElem?_ofFn]
    simp only [hi, dif_pos, Option.some.injEq, Matrix.mulVec, dotProduct]
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => by simp [j.2]
  · funext q
    by_cases hq : q = p <;> simp [hq]
  · simp
  · simp only [mul_smul, add_assoc]
  · simp
  · simp

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
  obtain ⟨hAlt, hAshape⟩ := Level2.blockFacts (L := m.eval * n.eval) h₁ (by simp [size_flatten])
  rw [ger_run, exec_seq_skip, exec_named, exec_alloc, exec_seq_skip]
  set s₀ : Store P 𝕜 := st.store.push (p, Array.replicate (2 : IExp ℕ).eval none) with hs₀
  have hC : Level2.GerCtx I s₀ p st.store.size A x y a m.eval n.eval ao.eval xo.eval yo.eval av
      (fun i => if h : i < m.eval then xv ⟨i, h⟩ else 0)
      (fun j => if h : j < n.eval then yv ⟨j, h⟩ else 0) :=
    { sem := hI
      charge := hc
      scratch := Level2.shape_push_size _ _ _
      A_ne := fun h => Nat.ne_of_lt (hAlt h)
      A_shape := fun k hk => by
        rw [hs₀, Level2.shape_push_of_lt _ (hAlt (by omega))]
        exact hAshape k hk
      a_read := by rw [hs₀, Store.read_push_of_lt (Level2.lt_size_of_read ha), ha]
      a_out := by
        refine ⟨Nat.ne_of_lt (Level2.lt_size_of_read ha), ?_⟩
        rintro ⟨-, h, h₁, h₂⟩
        rcases haA h with h | h <;> omega
      x_read := fun i hi => by
        rw [hs₀, Store.read_push_of_lt (Level2.lt_size_of_read (hx ⟨i, hi⟩)), hx ⟨i, hi⟩]
        simp [hi]
      x_out := fun i hi => by
        refine ⟨Nat.ne_of_lt (Level2.lt_size_of_read (hx ⟨i, hi⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hxA rfl with h | h <;> omega
      y_read := fun j hj => by
        rw [hs₀, Store.read_push_of_lt (Level2.lt_size_of_read (hy ⟨j, hj⟩)), hy ⟨j, hj⟩]
        simp [hj]
      y_out := fun j hj => by
        refine ⟨Nat.ne_of_lt (Level2.lt_size_of_read (hy ⟨j, hj⟩)), ?_⟩
        rintro ⟨-, rfl, h₁, h₂⟩
        rcases hyA rfl with h | h <;> omega }
  obtain ⟨σF, hF, sF, gF, rfl, hIF, hgF⟩ := Level2.exec_gerCols
    (M := fun i j => if h : i < m.eval ∧ j < n.eval then M ⟨i, h.1⟩ ⟨j, h.2⟩ else 0) hC
    (σ := { st with
      store := s₀
      cur := Function.update st.cur p (st.cur p + (2 : IExp ℕ).eval)
      peak := Function.update st.peak p (max (st.peak p) (st.cur p + (2 : IExp ℕ).eval))
      curW := st.curW + (2 : IExp ℕ).eval * I.width p
      peakW := max st.peakW (st.curW + (2 : IExp ℕ).eval * I.width p) })
    ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩ fun i hi j hj => by
      have := hA ⟨i, hi⟩ ⟨j, hj⟩
      rw [← Nat.add_assoc, hs₀, Store.read_push_of_lt (Level2.lt_size_of_read this), this]
      simp [hi, hj]
  rw [hF, Option.map_some]
  refine ⟨_, rfl, Level2.pop_eq_of_DInv h₁ (by simp [size_flatten]) hIF fun k hk => ?_, rfl, ?_,
    ?_, ?_, ?_, ?_⟩
  · have hm : 0 < m.eval := Nat.pos_of_ne_zero fun h => by simp [h] at hk
    have hi : k % m.eval < m.eval := Nat.mod_lt _ hm
    have hj : k / m.eval < n.eval := Nat.div_lt_of_lt_mul hk
    rw [← Nat.mod_add_div k m.eval, hgF _ hi _ hj, getElem?_flatten _ ⟨_, hi⟩ ⟨_, hj⟩]
    simp [hi, hj, Matrix.vecMulVec_apply, mul_left_comm]
  · funext q
    by_cases hq : q = p <;> simp [hq]
  · simp
  · simp only [smul_add, mul_smul, add_assoc]
  · simp
  · simp

/-- One column of `gemm`: the `gemv` of column $c$, from a store with the frame invariant of the
block of $\mathbf{C}$. -/
private theorem exec_gemm_step (m n l : IExp ℕ) (A : ℕ) (ao : IExp ℕ) (B : ℕ) (bo : IExp ℕ)
    (C : ℕ) (co : IExp ℕ) (MA : Matrix (Fin m.eval) (Fin n.eval) 𝕜)
    (MB : Matrix (Fin n.eval) (Fin l.eval) 𝕜) (hA : Holds st.store p A ao.eval MA)
    (hB : Holds st.store p B bo.eval MB)
    (hCA : C = A → co.eval + m.eval * l.eval ≤ ao.eval ∨ ao.eval + m.eval * n.eval ≤ co.eval)
    (hCB : C = B → co.eval + m.eval * l.eval ≤ bo.eval ∨ bo.eval + n.eval * l.eval ≤ co.eval)
    (hCsh : ∀ k < m.eval * l.eval, ∃ N, st.store.shape[C]? = some (p, N) ∧ co.eval + k < N)
    {c : ℕ} (hcl : c < l.eval) (σ : St P 𝕜 (OpCount P ι)) (g : ℕ → Option 𝕜)
    (hD : Level2.DInv st.store p st.store.size C co.eval (m.eval * l.eval) σ.store g)
    (hg : ∀ k < m.eval * c, g k = (flatten (MA * MB))[k]?) :
    ∃ σ', exec I (gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)).run σ = some σ' ∧
      σ'.pos = σ.pos ∧ σ'.cur = σ.cur ∧ σ'.curW = σ.curW ∧
      σ'.cnt = σ.cnt + (m.eval • Finsupp.single (.lit p) 1 + (n.eval * m.eval) •
        (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      σ'.peak = Function.update σ.peak p (max (σ.peak p) (σ.cur p + 1)) ∧
      σ'.peakW = max σ.peakW (σ.curW + I.width p) ∧
      ∃ g', Level2.DInv st.store p st.store.size C co.eval (m.eval * l.eval) σ'.store g' ∧
        ∀ k < m.eval * (c + 1), g' k = (flatten (MA * MB))[k]? := by
  have hmc : m.eval * c + m.eval ≤ m.eval * l.eval := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcl
  have hnc : n.eval * c + n.eval ≤ n.eval * l.eval := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hcl
  have hA' : Holds σ.store p A ao.eval MA := fun i j => by
    have hk := Nat.add_mul_lt_mul_of_lt_of_lt i.2 j.2
    refine (hD.read_out (Nat.ne_of_lt (Level2.lt_size_of_read (hA i j))) ?_).trans (hA i j)
    rintro ⟨-, h, h₁, h₂⟩
    rcases hCA h.symm with h | h <;> omega
  have hx : ∀ j : Fin n.eval, σ.store.read p B ((bo + n * .var c).eval + j) =
      some (MB j ⟨c, hcl⟩) := fun j => by
    have hk := Nat.add_mul_lt_mul_of_lt_of_lt j.2 hcl
    simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]
    rw [show bo.eval + n.eval * c + j = bo.eval + j + n.eval * c by omega]
    refine (hD.read_out (Nat.ne_of_lt (Level2.lt_size_of_read (hB j ⟨c, hcl⟩))) ?_).trans
      (hB j ⟨c, hcl⟩)
    rintro ⟨-, h, h₁, h₂⟩
    rcases hCB h.symm with h | h <;> omega
  obtain ⟨s₁, hs₁⟩ := Level2.exists_writeBlock_of_shape (s := σ.store) (p := p) (b := C)
    (off := (co + m * .var c).eval) (xs := Array.ofFn (MA *ᵥ fun j => MB j ⟨c, hcl⟩))
    fun i hi => by
      obtain ⟨N, hN, hlt⟩ := hCsh (m.eval * c + i) (by simp at hi; omega)
      exact ⟨N, hD.1 ▸ hN, by simp; omega⟩
  obtain ⟨σ', hrun, hst, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ := exec_gemv I hI hc p σ m n A ao
    B (bo + n * .var c) C (co + m * .var c) MA (fun j => MB j ⟨c, hcl⟩) hA' hx
    (fun h => by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]; omega)
    (fun h => by simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var]; omega)
    s₁ hs₁
  simp only [IExp.eval_add, IExp.eval_mul, IExp.eval_var] at hs₁
  refine ⟨σ', hrun, hpos, hcur, hcurW, hcnt, hpeak, hpeakW, _,
    hst ▸ hD.writeBlock hs₁ (by simp; omega), fun k hk => ?_⟩
  by_cases hkc : k < m.eval * c
  · rw [if_neg (by omega), hg k hkc]
  · have hi : k - m.eval * c < m.eval := by rw [Nat.mul_succ] at hk; omega
    rw [if_pos (by simp; omega), show k = (k - m.eval * c) + m.eval * c by omega,
      Nat.add_sub_cancel, getElem?_flatten _ ⟨_, hi⟩ ⟨c, hcl⟩, Array.getElem?_ofFn]
    simp [hi, Matrix.mulVec, dotProduct, Matrix.mul_apply]

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
  obtain ⟨hClt, hCsh⟩ := Level2.blockFacts (L := m.eval * l.eval) h₁ (by simp [size_flatten])
  rw [gemm_run, exec_seq_skip, exec_named, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall I (n := l)
    (body := fun c => (gemv p m n A ao B (bo + n * .var c) C (co + m * .var c)).run)
    (fun c σ => σ.pos = st.pos ∧ σ.cur = st.cur ∧
      σ.curW = st.curW ∧ σ.cnt = st.cnt + c • (m.eval • Finsupp.single (.lit p) 1 +
        (n.eval * m.eval) • (Finsupp.single (.bin p .mul) 1 + Finsupp.single (.bin p .add) 1)) ∧
      σ.peak ≤ Function.update st.peak p (max (st.peak p) (st.cur p + 1)) ∧
      σ.peakW ≤ max st.peakW (st.curW + I.width p) ∧
      ∃ g, Level2.DInv st.store p st.store.size C co.eval (m.eval * l.eval) σ.store g ∧
        ∀ k < m.eval * c, g k = (flatten (MA * MB))[k]?)
    ⟨rfl, rfl, rfl, by simp, fun q => ?_, le_max_left _ _, _,
      ⟨rfl, fun _ _ _ _ _ => rfl, fun _ _ => rfl⟩, by simp⟩ ?_).imp ?_
  · by_cases hq : q = p
    · subst hq
      simp
    · simp [hq]
  · rintro c hcl σ ⟨hpos, hcur, hcurW, hcnt, hpeak, hpeakW, g, hD, hg⟩
    obtain ⟨σ', hrun, hpos', hcur', hcurW', hcnt', hpeak', hpeakW', g', hD', hg'⟩ :=
      exec_gemm_step I hI hc p st m n l A ao B bo C co MA MB hA hB hCA hCB hCsh hcl σ g hD hg
    refine ⟨σ', hrun, hpos'.trans hpos, hcur'.trans hcur, hcurW'.trans hcurW, ?_, fun q => ?_,
      ?_, g', hD', hg'⟩
    · rw [hcnt', hcnt, succ_nsmul, add_assoc]
    · rw [hpeak', hcur]
      by_cases hq : q = p
      · rw [hq, Function.update_self, Function.update_self]
        exact max_le ((hpeak p).trans_eq (Function.update_self _ _ _)) (le_max_right _ _)
      · rw [Function.update_of_ne hq, Function.update_of_ne hq]
        exact (hpeak q).trans_eq (Function.update_of_ne hq _ _)
    · rw [hpeakW', hcurW]
      exact max_le hpeakW (le_max_right _ _)
  · rintro σ ⟨hrun, hpos, hcur, hcurW, hcnt, hpeak, hpeakW, g, hD, hg⟩
    refine ⟨hrun, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
    have := Level2.pop_eq_of_DInv h₁ (by simp [size_flatten])
      (Level2.DInv.push hD (p, Array.replicate 1 none) hClt) hg
    simpa using this

end Specs

end NLAlib.Computation
