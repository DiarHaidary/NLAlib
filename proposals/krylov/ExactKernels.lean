/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS

/-!
# Exact kernel frames for concrete Krylov execution proofs

Finite-vector wrappers of the existing exact `dot` and `axpy` executions, retaining
all storage, tape, operation-count and memory guarantees. Offsets permit both CG vectors
and Lanczos columns. These are supporting local executions, not whole solver targets.

## Main results

* `NLAlib.KrylovImplementation.exec_dot_frame`: exact scalar pairing and its full cell frame.
* `NLAlib.KrylovImplementation.exec_axpy_frame`: exact vector update and its window frame.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.KrylovImplementation

open Computation

variable {P ι : Type} [DecidableEq P]

/-- The actual exact dot kernel returns the finite-vector dot product, with one scalar-cell
write, exact standard operation counts, unchanged tape and current memory, and its one-cell
scratch peak. The destination is writable and lies outside both input buffers. -/
theorem exec_dot_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (dst : Cell ℕ ℕ) (x y : ℕ)
    (xo yo : IExp ℕ) (xs ys : Fin N → ℝ)
    (hx : ∀ i : Fin N, st.store.read tag x (xo.eval + i) = some (xs i))
    (hy : ∀ i : Fin N, st.store.read tag y (yo.eval + i) = some (ys i))
    (hdx : dst.buf ≠ x) (hdy : dst.buf ≠ y)
    (hd : ∃ w s, st.store.write tag dst.buf dst.idx.eval w = some s) :
    ∃ out, exec I (dot tag dst x xo y yo (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      out.store.read tag dst.buf dst.idx.eval = some (xs ⬝ᵥ ys) ∧
      (∀ q b i, (b ≠ dst.buf ∨ i ≠ dst.idx.eval) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + (N • (Finsupp.single (.un tag .conj) 1 +
        Finsupp.single (.bin tag .mul) 1 + Finsupp.single (.bin tag .add) 1) +
        Finsupp.single (.lit tag) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let xs' : ℕ → ℝ := fun i => if hi : i < N then xs ⟨i, hi⟩ else 0
  let ys' : ℕ → ℝ := fun i => if hi : i < N then ys ⟨i, hi⟩ else 0
  have hval : (∑ i ∈ Finset.range N, star (xs' i) * ys' i) = xs ⬝ᵥ ys := by
    rw [← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun i _ => by simp [xs', ys', i.isLt]
  obtain ⟨old, s, hs⟩ := hd
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_write_eq_some hs (xs ⬝ᵥ ys)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_dot I hI hc tag st dst x xo y yo (.const N) xs' ys'
      (fun i hi => by
        change i < N at hi
        simpa only [xs', dif_pos hi] using hx ⟨i, hi⟩)
      (fun i hi => by
        change i < N at hi
        simpa only [ys', dif_pos hi] using hy ⟨i, hi⟩)
      (fun h => (hdx h).elim) (fun h => (hdy h).elim) s' (by simpa only [IExp.eval_const, hval] using hs')
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_write_eq_some hs'
  · rw [hout]
    exact Store.read_of_write_eq_some hs'
  · intro q b i hi
    rw [hout]
    exact Store.read_of_write_eq_some_of_ne hs' hi

/-- The actual exact axpy kernel updates a finite output vector, retains every cell outside
its output window, and has exact standard counts and one-cell scratch peak. The source and
output buffers are disjoint, and the coefficient lies outside the output buffer. -/
theorem exec_axpy_frame (I : Interp P ι ℝ (OpCount P ι)) (hI : I.sem = exactSem)
    (hc : ∀ k, I.charge k = Finsupp.single k 1) (tag : P)
    (st : St P ℝ (OpCount P ι)) (N : ℕ) (a : Cell ℕ ℕ) (x y : ℕ)
    (xo yo : IExp ℕ) (av : ℝ) (xs ys : Fin N → ℝ)
    (ha : st.store.read tag a.buf a.idx.eval = some av)
    (hx : ∀ i : Fin N, st.store.read tag x (xo.eval + i) = some (xs i))
    (hy : ∀ i : Fin N, st.store.read tag y (yo.eval + i) = some (ys i))
    (hxy : x ≠ y) (hay : a.buf ≠ y) :
    ∃ out, exec I (axpy tag a x xo y yo (.const N)).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin N, out.store.read tag y (yo.eval + i) = some (ys i + av * xs i)) ∧
      (∀ q b i, (b ≠ y ∨ i < yo.eval ∨ yo.eval + N ≤ i) →
        out.store.read q b i = st.store.read q b i) ∧
      out.pos = st.pos ∧ out.cur = st.cur ∧ out.curW = st.curW ∧
      out.cnt = st.cnt + N • (Finsupp.single (.bin tag .mul) 1 +
        Finsupp.single (.bin tag .add) 1) ∧
      out.peak = Function.update st.peak tag (max (st.peak tag) (st.cur tag + 1)) ∧
      out.peakW = max st.peakW (st.curW + I.width tag) := by
  let xs' : ℕ → ℝ := fun i => if hi : i < N then xs ⟨i, hi⟩ else 0
  let ys' : ℕ → ℝ := fun i => if hi : i < N then ys ⟨i, hi⟩ else 0
  obtain ⟨s', hs'⟩ := Store.exists_writeBlock_eq_some (p := tag) (b := y) (off := yo.eval)
    (xs := (List.range N).toArray.map fun i => av * xs' i + ys' i) (fun i hi => by
      have hi' : i < N := by simpa only [Array.size_map, List.size_toArray,
        List.length_range] using hi
      exact ⟨ys ⟨i, hi'⟩, hy ⟨i, hi'⟩⟩)
  obtain ⟨out, hrun, hout, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩ :=
    exec_axpy I hI hc tag st a x xo y yo (.const N) av xs' ys' ha
      (fun i hi => by
        change i < N at hi
        simpa only [xs', dif_pos hi] using hx ⟨i, hi⟩)
      (fun i hi => by
        change i < N at hi
        simpa only [ys', dif_pos hi] using hy ⟨i, hi⟩)
      (fun h => (hay h).elim) (fun h => (hxy h).elim) s' hs'
  refine ⟨out, hrun, ?_, ?_, ?_, hpos, hcur, hcurW, hcnt, hpeak, hpeakW⟩
  · rw [hout]
    exact Store.shape_of_writeBlock_eq_some hs'
  · intro i
    rw [hout]
    simpa [xs', ys', i.isLt, add_comm] using Store.read_of_writeBlock_eq_some_of_lt
      (j := (i : ℕ)) hs' (by simpa only [Array.size_map, List.size_toArray,
        List.length_range] using i.isLt)
  · intro q b i hi
    rw [hout]
    apply Store.read_of_writeBlock_eq_some_of_ne hs'
    simpa only [Array.size_map, List.size_toArray, List.length_range] using hi

end NLAlib.KrylovImplementation
