/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Normalization
public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# Execution lemmas for the proposed concrete Lanczos program

Exact execution, zero branches, storage frames and budgets for the operations appearing in
`proposals/krylov/Lanczos.lean`. These supporting proposals introduce no new algorithm program
and assume no desired arithmetic error bounds. The full proposed target is kept distinct from
its progressively proved execution lemmas.

## Main results

* `NLAlib.LanczosImplementation.exec_forRange_zero`: literal-zero branch with a storage frame.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.LanczosImplementation

open Computation Computation.Builder

variable {P ι C : Type} [DecidableEq P] [AddMonoid C]

/-- The exact stored state after initialization and the first `j` concrete Lanczos steps.
The nine buffers are the six declared buffers followed by loaded matrix, work vector and
two scalar scratch cells. Only the negative scratch cell and work vector are unconstrained.
This is an induction invariant proved from execution, not an extra target premise. -/
structure State (tag : P) (N q j : ℕ) (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (st : St P ℝ (OpCount P ι)) : Prop where
  /-- Exact shape of the declared and scoped workspace buffers. -/
  shape : st.store.shape = #[(tag, N), (tag, N * (q + 1)), (tag, q), (tag, q + 1),
    (tag, 1), (tag, N), (tag, N * N), (tag, N), (tag, 2)]
  /-- The declared input is retained. -/
  input : ∀ i : Fin N, st.store.read tag 0 i = some (b i)
  /-- The ROM matrix has been loaded column-major. -/
  matrix : Holds st.store tag 6 0 A
  /-- Every computed basis column agrees with its exact recurrence state. -/
  basis : ∀ c ≤ j, ∀ i : Fin N,
    st.store.read tag 1 (N * c + i) = some ((lanczosState A b c).cur i)
  /-- Every completed diagonal coefficient agrees with the recurrence. -/
  alpha : ∀ c < j,
    st.store.read tag 2 c = some (lanczosAlpha A (lanczosState A b c))
  /-- The initial and all completed off-diagonal coefficients agree with the recurrence. -/
  beta : ∀ c ≤ j, st.store.read tag 3 c = some ((lanczosState A b c).beta)
  /-- The actual input norm has its exact arithmetic value. -/
  inputNorm : st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖
  /-- The previous-vector buffer holds the previous exact state vector. -/
  prev : ∀ i : Fin N, st.store.read tag 5 i = some ((lanczosState A b j).prev i)
  /-- The persistent comparison scalar remains exact zero. -/
  zero : st.store.read tag 8 0 = some 0

/-- Componentwise upper counts of one concrete Paige step, including both alternatives of
the guarded next-column normalization. ROM loading and initialization are counted separately. -/
noncomputable def stepCount {P ι : Type} (tag : P) (N : ℕ) : OpCount P ι :=
  Finsupp.single (.bin tag .mul) (N ^ 2 + 4 * N) +
  Finsupp.single (.bin tag .add) (N ^ 2 + 4 * N) +
  Finsupp.single (.un tag .conj) (2 * N) +
  Finsupp.single (.bin tag .div) N + Finsupp.single (.un tag .sqrt) 1 +
  Finsupp.single (.un tag .neg) 2 + Finsupp.single (.lit tag) (2 * N + 2) +
  Finsupp.single (.cmp tag) 1 + Finsupp.single (.copy tag) (2 * N)

/-- The actual literal-zero loop succeeds where its output window is writable. It writes
zero to that window, preserves all other cells and every usage field except the literal
count, and keeps the shape. The window may be uninitialized or have length zero. -/
theorem exec_forRange_zero (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (st : St P ℝ C) (n : IExp ℕ) (buf : ℕ) (off : IExp ℕ)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[buf]? = some (tag, len) ∧ off.eval + i < len) :
    ∃ s', exec I (forRange n fun i => ins (.lit tag ⟨buf, off + .var i⟩ 0)).run st =
      some { st with store := s', cnt := st.cnt + n.eval • I.charge (.lit tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < n.eval, s'.read tag buf (off.eval + i) = some 0) ∧
      ∀ q b j, (q ≠ tag ∨ b ≠ buf ∨ j < off.eval ∨ off.eval + n.eval ≤ j) →
        s'.read q b j = st.store.read q b j := by
  let R (k : ℕ) (out : St P ℝ C) : Prop :=
    ∃ s', out = { st with store := s', cnt := st.cnt + k • I.charge (.lit tag) } ∧
      s'.shape = st.store.shape ∧
      (∀ i < k, s'.read tag buf (off.eval + i) = some 0) ∧
      ∀ q b j, (q ≠ tag ∨ b ≠ buf ∨ j < off.eval ∨ off.eval + n.eval ≤ j) →
        s'.read q b j = st.store.read q b j
  have h0 : R 0 st := ⟨st.store, by simp only [zero_nsmul, add_zero], rfl,
    fun i hi => by omega, fun _ _ _ _ => rfl⟩
  have hstep : ∀ i < n.eval, ∀ out, R i out → ∃ out',
      exec I (.seq (.instr (.lit tag ⟨buf, off + .var i⟩ 0)) .skip) out = some out' ∧
        R (i + 1) out' := by
    rintro i hi out ⟨s, rfl, hsh, hread, hframe⟩
    obtain ⟨len, hlen, hlt⟩ := hshape i hi
    have hlen' : s.shape[buf]? = some (tag, len) := by rw [hsh]; exact hlen
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_getElem?_shape (0 : ℝ) hlen' hlt
    refine ⟨{ st with store := s', cnt := st.cnt + (i + 1) • I.charge (.lit tag) },
      ?_, s', rfl, (Store.shape_of_write_eq_some hs').trans hsh, ?_, ?_⟩
    · have hwrite : s.write tag buf (off + IExp.var i).eval 0 = some s' := by
        simpa only [IExp.eval_add, IExp.eval_var] using hs'
      have hrun := (exec_seq_instr_lit I (p := tag) (q := 0) (t := .skip)
        (dst := ⟨buf, off + IExp.var i⟩)
        (st := { st with store := s, cnt := st.cnt + i • I.charge (.lit tag) })
        (by rw [hI]; simp only [exactSem, Rat.cast_zero]) hwrite).trans (exec_skip I _)
      simpa only [succ_nsmul, add_assoc] using hrun
    · intro j hj
      rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hji
      · exact Store.read_of_write_eq_some hs'
      · rw [Store.read_of_write_eq_some_of_ne hs' (Or.inr (by omega))]
        exact hread j hji
    · intro q b j hout
      have hne : q ≠ tag ∨ b ≠ buf ∨ j ≠ off.eval + i := by
        rcases hout with hq | hb | hj | hj
        · exact Or.inl hq
        · exact Or.inr (Or.inl hb)
        · exact Or.inr (Or.inr (by omega))
        · exact Or.inr (Or.inr (by omega))
      rcases hne with hq | hcell
      · rw [Store.read_of_write_eq_some_of_ne_tag hs' hq]
        exact hframe q b j hout
      · rw [Store.read_of_write_eq_some_of_ne hs' hcell]
        exact hframe q b j hout
  obtain ⟨out, hrun, s', hout, hsh, hread, hframe⟩ :=
    exists_exec_loop_eq_some_of_forall I (n := n) R h0 hstep
  refine ⟨s', ?_, hsh, hread, hframe⟩
  change exec I (.seq (.loop n _) .skip) st = _
  rw [exec_seq_skip]
  exact hout ▸ hrun

/-- The existing copy kernel preserves the entire store outside its destination window,
including earlier columns of the same basis buffer. Writable capacity suffices; destination
entries need not have been initialized. Its operation count and memory footprint are exact. -/
theorem exec_copyv_frame {K : Type} (I : Interp P ι K (OpCount P ι))
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P K (OpCount P ι)) (n : IExp ℕ) (src dst : ℕ) (soff doff : IExp ℕ)
    (xs : ℕ → K) (hx : ∀ i < n.eval, st.store.read tag src (soff.eval + i) = some (xs i))
    (hdisjoint : src ≠ dst)
    (hshape : ∀ i < n.eval, ∃ len,
      st.store.shape[dst]? = some (tag, len) ∧ doff.eval + i < len) :
    ∃ out, exec I (copyv tag src soff dst doff n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read tag dst (doff.eval + i) = some (xs i)) ∧
      (∀ q b i, (b ≠ dst ∨ i < doff.eval ∨ doff.eval + n.eval ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + n.eval • Finsupp.single (.copy tag) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (xs := (List.range n.eval).toArray.map xs) (fun i hi => hshape i (by simpa using hi))
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_copyv I hc tag st src soff dst doff n xs hx (fun h => (hdisjoint h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_,
    hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_writeBlock_eq_some hs'
  · intro i hi
    rw [hout]
    simpa only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hi,
      Option.map_some] using Store.read_of_writeBlock_eq_some_of_lt (j := i) hs'
        (by simpa only [Array.size_map, List.size_toArray, List.length_range] using hi)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    simpa only [Array.size_map, List.size_toArray, List.length_range] using hi

/-- The actual stored dense matrix kernel has an exact vector output, a full destination
frame, and its published operation and peak-memory bounds. This uses no oracle accuracy
assumption and permits an uninitialized destination. -/
theorem exec_gemv_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (A x y : ℕ) (xo : IExp ℕ)
    (M : Matrix (Fin N) (Fin N) ℝ) (v : Fin N → ℝ)
    (hA : Holds st.store tag A 0 M)
    (hx : ∀ i : Fin N, st.store.read tag x (xo.eval + i) = some (v i))
    (hyA : y ≠ A) (hyx : y ≠ x)
    (hshape : ∀ i < N, ∃ len, st.store.shape[y]? = some (tag, len) ∧ i < len) :
    ∃ out, exec I (gemv tag (.const N) (.const N) A 0 x xo y 0).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag y i = some ((M *ᵥ v) i)) ∧
      (∀ q b i, (b ≠ y ∨ N ≤ i) → out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N • Finsupp.single (.lit tag) 1 + (N * N) •
        (Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1)) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape
    (b := y) (off := 0) (xs := Array.ofFn (M *ᵥ v)) (fun i hi => by
      obtain ⟨len, hl, hi⟩ := hshape i (by simpa using hi)
      exact ⟨len, hl, by simpa only [zero_add] using hi⟩)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_gemv I hI hc tag st (.const N) (.const N) A 0 x xo y 0 M v hA hx
      (fun h => (hyA h).elim) (fun h => (hyx h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_writeBlock_eq_some hs'
  · intro i
    rw [hout]
    simpa only [IExp.eval_zero, zero_add, Array.getElem?_ofFn, dif_pos i.2] using
      Store.read_of_writeBlock_eq_some_of_lt (j := (i : ℕ)) hs' (by simp)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    rcases hi with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (by simpa only [Array.size_ofFn, IExp.eval_zero, zero_add] using h))

/-- Exact componentwise division by a nonzero stored scalar, retaining the entire store
outside the divided window and the exact operation count and memory footprint. -/
theorem exec_rscl_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (n : IExp ℕ) (a : Cell ℕ ℕ) (x : ℕ) (off : IExp ℕ)
    (av : ℝ) (xs : ℕ → ℝ) (hav : av ≠ 0)
    (ha : st.store.read tag a.buf a.idx.eval = some av)
    (hx : ∀ i < n.eval, st.store.read tag x (off.eval + i) = some (xs i))
    (hax : a.buf ≠ x) :
    ∃ out, exec I (rscl tag a x off n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read tag x (off.eval + i) = some (xs i / av)) ∧
      (∀ q b i, (b ≠ x ∨ i < off.eval ∨ off.eval + n.eval ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + n.eval • Finsupp.single (.bin tag .div) 1 ∧
      out.peak = st.peak ∧ out.peakW = st.peakW := by
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some
    (xs := (List.range n.eval).toArray.map fun i => xs i / av)
    (fun i hi => ⟨xs i, hx i (by simpa using hi)⟩)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_rscl I hI hc tag st a x off n av xs hav ha hx (fun h => (hax h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]; exact Store.shape_of_writeBlock_eq_some hs'
  · intro i hi
    rw [hout]
    simpa only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hi,
      Option.map_some] using Store.read_of_writeBlock_eq_some_of_lt (j := i) hs'
        (by simpa only [Array.size_map, List.size_toArray, List.length_range] using hi)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    simpa only [Array.size_map, List.size_toArray, List.length_range] using hi

/-- The actual exact norm kernel overwrites its scalar destination with the Euclidean norm,
preserves every other cell, and has the existing dot-then-square-root count and scratch peak. -/
theorem exec_nrm2_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (dst : Cell ℕ ℕ) (src : ℕ) (off n : IExp ℕ)
    (xs : ℕ → ℝ) (hx : ∀ i < n.eval, st.store.read tag src (off.eval + i) = some (xs i))
    (hds : dst.buf ≠ src)
    (hd : ∃ w s, st.store.write tag dst.buf dst.idx.eval w = some s) :
    ∃ out, exec I (nrm2 tag dst src off n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag dst.buf dst.idx.eval =
        some ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ∧
      (∀ q b i, (b ≠ dst.buf ∨ i ≠ dst.idx.eval) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (n.eval • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1 + Finsupp.single (.un tag .sqrt) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let r := ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖
  have hsq : r ^ 2 = ∑ i ∈ Finset.range n.eval, xs i * xs i := by
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, dotProduct]
    exact Fin.sum_univ_eq_sum_range (fun i => xs i * xs i) n.eval
  have hval : ((√(RCLike.re (∑ i ∈ Finset.range n.eval, star (xs i) * xs i)) : ℝ) : ℝ) =
      r := by
    simp only [star_trivial, RCLike.re_to_real]
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  obtain ⟨old, s, hs⟩ := hd
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_write_eq_some hs r
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_nrm2 I hI hc tag st dst src off n xs hx (fun h => (hds h).elim) s'
      (by rw [hval]; exact hs')
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]; exact Store.shape_of_write_eq_some hs'
  · rw [hout]; exact Store.read_of_write_eq_some hs'
  · intro q b i hi
    rw [hout]
    exact Store.read_of_write_eq_some_of_ne hs' hi

/-- The actual negation and `axpy` operations subtract a stored coefficient times a source
vector. All cells outside the updated vector and negative-coefficient scratch are retained. -/
theorem exec_neg_axpy
    (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P) (st : St P ℝ C)
    (buf : Fin 4 → ℕ) (hbuf : Function.Injective buf) (n xo yo ai ti : IExp ℕ)
    (av : ℝ) (xs ys : ℕ → ℝ)
    (ha : st.store.read tag (buf 2) ai.eval = some av)
    (hx : ∀ i < n.eval, st.store.read tag (buf 0) (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read tag (buf 1) (yo.eval + i) = some (ys i))
    (ht : ∃ w s, st.store.write tag (buf 3) ti.eval w = some s) :
    ∃ out, exec I (do
        ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)
        axpy tag ⟨buf 3, ti⟩ (buf 0) xo (buf 1) yo n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i < n.eval, out.store.read tag (buf 1) (yo.eval + i) = some (ys i - av * xs i)) ∧
      ∀ q b i, (b ≠ buf 1 ∨ i < yo.eval ∨ yo.eval + n.eval ≤ i) →
        (b = buf 3 → i ≠ ti.eval) → out.store.read q b i = st.store.read q b i := by
  have hne : ∀ i j : Fin 4, i ≠ j → buf i ≠ buf j := fun _ _ hij he => hij (hbuf he)
  have hsem : IsRelErrSem (fun _ : P => 0) (fun (_ : P) (x : ℝ) => x)
      (fun _ _ => True) I.sem := by rw [hI]; exact isRelErrSem_exactSem
  obtain ⟨old, s, hs⟩ := ht
  obtain ⟨s₁, hs₁⟩ := Store.exists_write_eq_some_of_write_eq_some hs (-av)
  let st₁ := { st with store := s₁, cnt := st.cnt + I.charge (.un tag .neg) }
  have hneg : exec I (ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)).run st = some st₁ :=
    (exec_seq_instr_un I ha (by rw [hI]; rfl) hs₁).trans (exec_skip I _)
  have hx₁ : ∀ i < n.eval, s₁.read tag (buf 0) (xo.eval + i) = some (xs i) := by
    intro i hi
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl (hne 0 3 (by decide))), hx i hi]
  have hy₁ : ∀ i < n.eval, s₁.read tag (buf 1) (yo.eval + i) = some (ys i) := by
    intro i hi
    rw [Store.read_of_write_eq_some_of_ne hs₁ (Or.inl (hne 1 3 (by decide))), hy i hi]
  obtain ⟨out, W, hax, hWstore, hW⟩ := hsem.exec_axpy I tag st₁ ⟨buf 3, ti⟩
    (buf 0) xo (buf 1) yo n (-av) xs ys (by simp) ⟨_, Store.read_of_write_eq_some hs₁, rfl⟩
    (fun i hi => ⟨_, hx₁ i hi, rfl⟩) (fun i hi => ⟨_, hy₁ i hi, rfl⟩)
    (fun h => (hne 3 1 (by decide) h).elim) (fun h => (hne 0 1 (by decide) h).elim)
  have hval : ∀ i < n.eval, W i = ys i - av * xs i := by
    intro i hi
    obtain ⟨θ, δ, hθ, hδ, hval⟩ := hW i hi
    have hθ0 : θ = 0 := abs_eq_zero.mp (le_antisymm (by simpa [roundingFactor] using hθ)
      (abs_nonneg _))
    have hδ0 : δ = 0 := abs_eq_zero.mp (le_antisymm hδ (abs_nonneg _))
    simpa only [hθ0, hδ0, add_zero, zero_add, mul_one, neg_mul, sub_eq_add_neg, add_comm]
      using hval
  refine ⟨out, ?_, (Store.shape_of_writeBlock_eq_some hWstore).trans
    (Store.shape_of_write_eq_some hs₁), ?_, ?_⟩
  · rw [exec_run_bind I (b := ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)) (fun _ => rfl),
      hneg, Option.bind_some]
    exact hax
  · intro i hi
    simpa only [Array.getElem?_map, List.getElem?_toArray, List.getElem?_range hi,
      Option.map_some, hval i hi] using Store.read_of_writeBlock_eq_some_of_lt
        (j := i) hWstore (by simpa using hi)
  · intro q b i hi hti
    have hnt : b ≠ buf 3 ∨ i ≠ ti.eval := by
      by_cases h : b = buf 3
      · exact Or.inr (hti h)
      · exact Or.inl h
    rw [Store.read_of_writeBlock_eq_some_of_ne hWstore (by simpa using hi),
      Store.read_of_write_eq_some_of_ne hs₁ hnt]

/-- The actual dot, negation and `axpy` part of a Paige step computes
$\mathbf{y}-(\mathbf{x}^{\mathsf{T}}\mathbf{y})\mathbf{x}$ in exact arithmetic. Its coefficient
and vector outputs come from executed kernels. The frame retains all other buffers, earlier
coefficient cells and the other scalar scratch cell. This lemma imposes no symmetry or
orthogonality hypothesis. -/
theorem exec_dot_neg_axpy
    (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P) (st : St P ℝ C)
    (buf : Fin 4 → ℕ) (hbuf : Function.Injective buf) (n xo yo ai ti : IExp ℕ)
    (xs ys : ℕ → ℝ)
    (hx : ∀ i < n.eval, st.store.read tag (buf 0) (xo.eval + i) = some (xs i))
    (hy : ∀ i < n.eval, st.store.read tag (buf 1) (yo.eval + i) = some (ys i))
    (ha : ∃ w s, st.store.write tag (buf 2) ai.eval w = some s)
    (ht : ∃ w s, st.store.write tag (buf 3) ti.eval w = some s) :
    ∃ out,
      exec I (do
        dot tag ⟨buf 2, ai⟩ (buf 0) xo (buf 1) yo n
        ins (.un tag .neg ⟨buf 3, ti⟩ ⟨buf 2, ai⟩)
        axpy tag ⟨buf 3, ti⟩ (buf 0) xo (buf 1) yo n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag (buf 2) ai.eval = some (∑ i ∈ Finset.range n.eval, xs i * ys i) ∧
      (∀ i < n.eval, out.store.read tag (buf 1) (yo.eval + i) =
        some (ys i - (∑ j ∈ Finset.range n.eval, xs j * ys j) * xs i)) ∧
      ∀ q b i, (b ≠ buf 1 ∨ i < yo.eval ∨ yo.eval + n.eval ≤ i) →
        (b = buf 2 → i ≠ ai.eval) → (b = buf 3 → i ≠ ti.eval) →
        out.store.read q b i = st.store.read q b i := by
  have hne : ∀ i j : Fin 4, i ≠ j → buf i ≠ buf j := fun _ _ hij he => hij (hbuf he)
  have hsem : IsRelErrSem (fun _ : P => 0) (fun (_ : P) (x : ℝ) => x)
      (fun _ _ => True) I.sem := by rw [hI]; exact isRelErrSem_exactSem
  have hz : AddsZeroExactly (fun (_ : P) (x : ℝ) => x) I.sem := by
    rw [hI]; exact addsZeroExactly_exactSem
  obtain ⟨st₁, w, hdot, hw, he⟩ := hsem.exec_dot_abs_sum_mul_sub_le I tag st hz
    ⟨buf 2, ai⟩ (buf 0) xo (buf 1) yo n xs ys (by simp) (fun i hi => ⟨_, hx i hi, rfl⟩)
    (fun i hi => ⟨_, hy i hi, rfl⟩) (fun h => (hne 2 0 (by decide) h).elim)
    (fun h => (hne 2 1 (by decide) h).elim) ha
  let c := ∑ i ∈ Finset.range n.eval, xs i * ys i
  have hwc : w = c := by
    simp only [roundingFactor, mul_zero, zero_div, zero_mul] at he
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm he (abs_nonneg _)))).symm
  have hx₁ : ∀ i < n.eval, st₁.store.read tag (buf 0) (xo.eval + i) = some (xs i) := by
    intro i hi
    rw [Store.read_of_write_eq_some_of_ne hw (Or.inl (hne 0 2 (by decide))), hx i hi]
  have hy₁ : ∀ i < n.eval, st₁.store.read tag (buf 1) (yo.eval + i) = some (ys i) := by
    intro i hi
    rw [Store.read_of_write_eq_some_of_ne hw (Or.inl (hne 1 2 (by decide))), hy i hi]
  have ht₁ : ∃ w s, st₁.store.write tag (buf 3) ti.eval w = some s := by
    obtain ⟨old, s, hs⟩ := ht
    obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_shape_eq
      (Store.shape_of_write_eq_some hw) hs old
    exact ⟨old, s', hs'⟩
  obtain ⟨out, hrun, hsh, hread, hframe⟩ := exec_neg_axpy I hI tag st₁ buf hbuf
    n xo yo ai ti c xs ys (by rw [Store.read_of_write_eq_some hw, hwc]) hx₁ hy₁ ht₁
  refine ⟨out, ?_, hsh.trans (Store.shape_of_write_eq_some hw), ?_, hread, ?_⟩
  · rw [exec_run_bind I (b := dot tag ⟨buf 2, ai⟩ (buf 0) xo (buf 1) yo n) (fun _ => rfl),
      hdot, Option.bind_some]
    exact hrun
  · rw [hframe tag (buf 2) ai.eval (Or.inl (hne 2 1 (by decide)))
      (fun h => (hne 2 3 (by decide) h).elim), Store.read_of_write_eq_some hw, hwc]
  · intro q b i hi hai hti
    rw [hframe q b i hi hti]
    apply Store.read_of_write_eq_some_of_ne hw
    by_cases h : b = buf 2
    · exact Or.inr (hai h)
    · exact Or.inl h

end NLAlib.LanczosImplementation
