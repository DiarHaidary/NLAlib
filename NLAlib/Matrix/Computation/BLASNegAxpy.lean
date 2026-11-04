/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.BLAS
public import NLAlib.Computation.ScalarFrames

/-!
# Actual negation followed by rounded axpy

Vector subtraction in the concrete Krylov programs negates a stored scalar into scratch
before running axpy. This adapter retains both executed instructions and the complete raw
storage frame. It uses the existing scalar relative-error contract and axpy theorem.

## Main results

* `NLAlib.Computation.IsRelErrSem.exec_neg_axpy_norm_sub_le`: executed subtraction error.
-/

@[expose] public section

namespace NLAlib.Computation

open Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    {u : P → ℝ} {dec : P → K → ℝ}

/-- Execute a stored scalar negation into disjoint scratch, then the actual rounded axpy.
The Euclidean subtraction bound is inherited from [Higham2002, (3.5)] with both rounding
operations retained. Output words, shape and all reads outside the two written windows
are conclusions; neither successful execution nor desired numerical errors are premises. -/
theorem IsRelErrSem.exec_neg_axpy_norm_sub_le (I : Interp P ι K C) (p : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (st : St P K C)
    (a tmp : Cell ℕ ℕ) (x : ℕ) (xo : IExp ℕ) (y : ℕ) (yo n : IExp ℕ)
    (av : ℝ) (xs ys : ℕ → ℝ) (hu : 2 * u p < 1)
    (ha : ∃ w, st.store.read p a.buf a.idx.eval = some w ∧ dec p w = av)
    (hx : ∀ i < n.eval, ∃ w, st.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i)
    (hy : ∀ i < n.eval, ∃ w, st.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i)
    (ht : ∃ len, st.store.shape[tmp.buf]? = some (p, len) ∧ tmp.idx.eval < len)
    (htx : tmp.buf ≠ x) (hty : tmp.buf ≠ y) (hxy : x ≠ y) :
    ∃ (out : St P K C) (W : ℕ → K),
      exec I (do ins (.un p .neg tmp a); axpy p tmp x xo y yo n).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin n.eval, out.store.read p y (yo.eval + i) = some (W i)) ∧
      (∀ q buf idx, (buf ≠ y ∨ idx < yo.eval ∨ yo.eval + n.eval ≤ idx) →
        (buf = tmp.buf → idx ≠ tmp.idx.eval) →
        out.store.read q buf idx = st.store.read q buf idx) ∧
      ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i - av * xs i - dec p (W i))‖ ≤
        roundingFactor 2 (u p) * (‖WithLp.toLp 2 (fun i : Fin n.eval => ys i)‖ +
          |av| * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖) := by
  obtain ⟨wa, hra, hda⟩ := ha
  obtain ⟨wt, hneg, hdt⟩ := h.neg p wa
  obtain ⟨store, hw, hr, hshape, hread, hframe⟩ :=
    exec_scalar_un I p st .neg tmp a wa wt hra hneg ht
  let mid := { st with store := store, cnt := st.cnt + I.charge (.un p .neg) }
  have htm : ∃ w, mid.store.read p tmp.buf tmp.idx.eval = some w ∧ dec p w = -av :=
    ⟨wt, hread, hdt.trans (congrArg Neg.neg hda)⟩
  have hxm (i : ℕ) (hi : i < n.eval) : ∃ w,
      mid.store.read p x (xo.eval + i) = some w ∧ dec p w = xs i := by
    change ∃ w, store.read p x (xo.eval + i) = some w ∧ dec p w = xs i
    rw [hframe p x _ (Or.inr (Or.inl (Ne.symm htx)))]
    exact hx i hi
  have hym (i : ℕ) (hi : i < n.eval) : ∃ w,
      mid.store.read p y (yo.eval + i) = some w ∧ dec p w = ys i := by
    change ∃ w, store.read p y (yo.eval + i) = some w ∧ dec p w = ys i
    rw [hframe p y _ (Or.inr (Or.inl (Ne.symm hty)))]
    exact hy i hi
  obtain ⟨out, W, hax, hblock, herr⟩ := h.exec_axpy_norm_sub_le I p mid tmp x xo y yo n
    (-av) xs ys hu htm hxm hym (fun he => (hty he).elim) (fun he => (hxy he).elim)
  refine ⟨out, W, ?_, (Store.shape_of_writeBlock_eq_some hblock).trans hshape,
    ?_, ?_, ?_⟩
  · rw [exec_run_bind I (b := ins (.un p .neg tmp a)) (fun _ => rfl), hr, Option.bind_some]
    exact hax
  · intro i
    have hrW := Store.read_of_writeBlock_eq_some_of_lt hblock
      (j := (i : ℕ)) (by simp)
    simpa using hrW
  · intro q buf idx hby htcell
    have hout : out.store.read q buf idx = mid.store.read q buf idx :=
      Store.read_of_writeBlock_eq_some_of_ne hblock (by simpa using hby)
    refine hout.trans (hframe q buf idx (Or.inr ?_))
    by_cases hb : buf = tmp.buf
    · exact Or.inr (htcell hb)
    · exact Or.inl hb
  · simpa only [neg_mul, sub_eq_add_neg, abs_neg] using herr

end NLAlib.Computation
