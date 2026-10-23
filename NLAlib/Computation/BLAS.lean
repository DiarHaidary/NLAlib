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
