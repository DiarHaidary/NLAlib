/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramRoundedState
public import NLAlib.Krylov.Processes.LanczosProgramRounding
public import NLAlib.Matrix.Computation.BLASNegAxpy
public import NLAlib.Computation.BLAS.NormalizationFrames

/-!
# Actual rounded kernels of a stored Lanczos step

Each bound here follows an actual kernel execution in the canonical nine-buffer workspace.
The decoded prefix records words already computed; local numerical defects are conclusions
of the scalar arithmetic contract, not assumptions on the stored trajectory.

## Main results

* `NLAlib.LanczosImplementation.exec_rounded_matvec`: executed dense matvec and its defect.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation Builder
open scoped Matrix

variable {P ι K : Type} [DecidableEq P]
    {u : P → ℝ} {dec : P → K → ℝ}

/-- The actual dense matrix-vector kernel initializes the work buffer and preserves the
completed decoded prefix. Its spectral norm error follows from the input-only implementation
precision window and the ordered rounded kernel bound [Higham2002, (3.12)]. Empty dimension
and a zero current vector are included. -/
theorem exec_rounded_matvec (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (uv : Fin N → ℝ),
      exec I (gemv tag (IExp.const N) (IExp.const N) 6 0 1
        (IExp.const N * IExp.var j) 7 0).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 7 i = some w ∧ dec tag w = uv i) ∧
      ‖WithLp.toLp 2 (A *ᵥ v (j + 1) - uv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) * specNorm A *
          ‖WithLp.toLp 2 (v (j + 1))‖ := by
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N (h.nonneg trivial) hsmall
  have hn : (N : ℝ) * u tag < 1 := by
    have hu := h.nonneg (p := tag) trivial
    have hsucc := hwin.1
    push_cast at hsucc
    nlinarith
  have hx (i : Fin N) : ∃ w,
      st.store.read tag 1 ((IExp.const N * IExp.var j).eval + i) = some w ∧
        dec tag w = v (j + 1) i := by
    simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using hs.basis j le_rfl i
  have hy (i : ℕ) (hi : i < N) :
      ∃ w store, st.store.write tag 7 i w = some store := by
    obtain ⟨w, _, _⟩ := hs.input ⟨i, hi⟩
    exact ⟨w, Store.exists_write_eq_some_of_getElem?_shape w
      (by rw [hs.shape]; rfl) hi⟩
  obtain ⟨out, W, hr, hw, herr⟩ := h.exec_gemv_norm_sub_le_specNorm_mul I tag st hz
    (IExp.const N) (IExp.const N) 6 0 1 (IExp.const N * IExp.var j) 7 0 A (v (j + 1))
    hn hs.matrix hx (by omega) (by omega) (by simpa using hy)
  have hctx : StoreContext tag dec N q j A b v α β s out.store :=
    hs.of_frame (Store.shape_of_writeBlock_eq_some hw) (by
      intro p k i hk _ _ _
      exact Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hk))
  refine ⟨out, (fun i => dec tag (W i)), hr, hctx, ?_, ?_⟩
  · intro i
    refine ⟨W i, ?_, rfl⟩
    have hread := Store.read_of_writeBlock_eq_some_of_lt hw
      (j := (i : ℕ)) (by simp)
    simpa using hread
  · refine herr.trans ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (roundingFactor_mul_sqrt_le_lanczosImplementationRoundoffBound N
          (h.nonneg trivial) hsmall) (specNorm_nonneg A)) (norm_nonneg _)

/-- The actual previous-vector subtraction executes the scalar negation before axpy.
The returned work vector and its complete prefix invariant are derived from actual reads;
the previous coefficient may be zero or negative. -/
theorem exec_rounded_previous_update (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store)
    (uv : Fin N → ℝ)
    (huv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = uv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (wv : Fin N → ℝ),
      exec I (do
        ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 7 i = some w ∧ dec tag w = wv i) ∧
      ‖WithLp.toLp 2 (uv - β j • v j - wv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 uv‖ + |β j| * ‖WithLp.toLp 2 (v j)‖) := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then v j ⟨i, hi⟩ else 0
  let ys : ℕ → ℝ := fun i => if hi : i < N then uv ⟨i, hi⟩ else 0
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N (h.nonneg trivial) hsmall
  obtain ⟨out, W, hr, hshape, hread, hframe, herr⟩ := h.exec_neg_axpy_norm_sub_le I tag st
    ⟨3, IExp.var j⟩ ⟨8, 1⟩ 5 0 7 0 (IExp.const N) (β j) xs ys hwin.2.1
    (hs.beta j le_rfl)
    (by intro i hi; change i < N at hi; simpa [xs, hi] using hs.prev ⟨i, hi⟩)
    (by intro i hi; change i < N at hi; simpa [ys, hi] using huv ⟨i, hi⟩)
    ⟨2, by rw [hs.shape]; rfl, by simp⟩ (by simp) (by simp) (by omega)
  refine ⟨out, (fun i => dec tag (W i)), hr, hs.of_frame hshape ?_, ?_, ?_⟩
  · intro p k i hk _ _ ht
    exact hframe p k i (Or.inl hk) ht
  · intro i
    exact ⟨W i, by simpa using hread i, rfl⟩
  · have he := herr.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.1
      (by positivity))
    have hxs : (fun i : Fin N => xs i) = v j := by funext i; simp [xs]
    have hys : (fun i : Fin N => ys i) = uv := by funext i; simp [ys]
    have heq : (fun i : Fin N => ys i - β j * xs i - dec tag (W i)) =
        uv - β j • v j - (fun i : Fin N => dec tag (W i)) := by
      ext i
      simp [xs, ys]
    change ‖WithLp.toLp 2 (fun i : Fin N => ys i - β j * xs i - dec tag (W i))‖ ≤
      _ * (‖WithLp.toLp 2 (fun i : Fin N => ys i)‖ +
        |β j| * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖) at he
    rw [heq, hxs, hys] at he
    exact he

/-- The actual dot stores the current diagonal coefficient with its ordered-product error.
The writable diagonal slot follows from the requested step index. No sign or unit-norm
property of either input is required. -/
theorem exec_rounded_dot (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store)
    (hj : j < q) (wv : Fin N → ℝ)
    (hwv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = wv i)
    (hn : (N : ℝ) * u tag < 1) :
    ∃ (out : St P K (OpCount P ι)) (an : ℝ),
      exec I (dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j)
        7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store ∧
      (∃ w, out.store.read tag 2 j = some w ∧ dec tag w = an) ∧
      |v (j + 1) ⬝ᵥ wv - an| ≤
        roundingFactor N (u tag) * ‖WithLp.toLp 2 (v (j + 1))‖ * ‖WithLp.toLp 2 wv‖ ∧
      (∀ p k i, k ≠ 2 ∨ i ≠ j → out.store.read p k i = st.store.read p k i) := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then v (j + 1) ⟨i, hi⟩ else 0
  let ys : ℕ → ℝ := fun i => if hi : i < N then wv ⟨i, hi⟩ else 0
  have hdst : ∃ w store, st.store.write tag 2 j w = some store := by
    obtain ⟨w, _, _⟩ := hs.zero
    exact ⟨w, Store.exists_write_eq_some_of_getElem?_shape w
      (by rw [hs.shape]; rfl) hj⟩
  obtain ⟨out, w, hr, hw, herr⟩ := h.exec_dot_abs_dotProduct_sub_le I tag st hz
    ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N) xs ys hn
    (by intro i hi; change i < N at hi; simpa [xs, hi] using hs.basis j le_rfl ⟨i, hi⟩)
    (by intro i hi; change i < N at hi; simpa [ys, hi] using hwv ⟨i, hi⟩)
    (by simp) (by simp) hdst
  refine ⟨out, dec tag w, hr, hs.of_frame (Store.shape_of_write_eq_some hw) ?_,
    ⟨w, Store.read_of_write_eq_some hw, rfl⟩, ?_, ?_⟩
  · intro p k i _ ha _ _
    apply Store.read_of_write_eq_some_of_ne hw
    by_cases he : k = 2
    · exact Or.inr (ha he)
    · exact Or.inl he
  · have hxs : (fun i : Fin N => xs i) = v (j + 1) := by funext i; simp [xs]
    have hys : (fun i : Fin N => ys i) = wv := by funext i; simp [ys]
    change |(fun i : Fin N => xs i) ⬝ᵥ (fun i : Fin N => ys i) - dec tag w| ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ *
        ‖WithLp.toLp 2 (fun i : Fin N => ys i)‖ at herr
    rw [hxs, hys] at herr
    exact herr
  · intro p k i hi
    exact Store.read_of_write_eq_some_of_ne hw hi

/-- Subtract the actual newly computed diagonal coefficient times the current column.
The stored coefficient survives the executed negation and axpy, and the full raw frame
retains its provenance for the later normalization and prefix commit. -/
theorem exec_rounded_projection_update (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store)
    (an : ℝ) (han : ∃ w, st.store.read tag 2 j = some w ∧ dec tag w = an)
    (wv : Fin N → ℝ)
    (hwv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = wv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (zv : Fin N → ℝ),
      exec I (do
        ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 7 i = some w ∧ dec tag w = zv i) ∧
      ‖WithLp.toLp 2 (wv - an • v (j + 1) - zv)‖ ≤
        lanczosImplementationRoundoffBound N (u tag) *
          (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 (v (j + 1))‖) ∧
      (∀ p k i, k ≠ 7 → (k = 8 → i ≠ 1) →
        out.store.read p k i = st.store.read p k i) := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then v (j + 1) ⟨i, hi⟩ else 0
  let ys : ℕ → ℝ := fun i => if hi : i < N then wv ⟨i, hi⟩ else 0
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N (h.nonneg trivial) hsmall
  obtain ⟨out, W, hr, hshape, hread, hframe, herr⟩ := h.exec_neg_axpy_norm_sub_le I tag st
    ⟨2, IExp.var j⟩ ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N) an xs ys hwin.2.1
    han
    (by intro i hi; change i < N at hi; simpa [xs, hi] using hs.basis j le_rfl ⟨i, hi⟩)
    (by intro i hi; change i < N at hi; simpa [ys, hi] using hwv ⟨i, hi⟩)
    ⟨2, by rw [hs.shape]; rfl, by simp⟩ (by simp) (by simp) (by omega)
  refine ⟨out, (fun i => dec tag (W i)), hr, hs.of_frame hshape ?_, ?_, ?_, ?_⟩
  · intro p k i hk _ _ ht
    exact hframe p k i (Or.inl hk) ht
  · intro i
    exact ⟨W i, by simpa using hread i, rfl⟩
  · have he := herr.trans (mul_le_mul_of_nonneg_right hwin.2.2.2.1 (by positivity))
    have hxs : (fun i : Fin N => xs i) = v (j + 1) := by funext i; simp [xs]
    have hys : (fun i : Fin N => ys i) = wv := by funext i; simp [ys]
    have heq : (fun i : Fin N => ys i - an * xs i - dec tag (W i)) =
        wv - an • v (j + 1) - (fun i : Fin N => dec tag (W i)) := by
      ext i
      simp [xs, ys]
    change ‖WithLp.toLp 2 (fun i : Fin N => ys i - an * xs i - dec tag (W i))‖ ≤
      _ * (‖WithLp.toLp 2 (fun i : Fin N => ys i)‖ +
        |an| * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖) at he
    rw [heq, hxs, hys] at he
    exact he
  · intro p k i hk ht
    exact hframe p k i (Or.inl hk) ht

/-- The actual norm of the newly projected work vector supplies a nonnegative next
off-diagonal coefficient and an exact decoded zero test. Its full raw frame preserves
the diagonal and work words for the following previous-vector copy and guarded division. -/
theorem exec_rounded_next_norm (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (tag : P) {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store)
    (hj : j < q) (zv : Fin N → ℝ)
    (hzv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = zv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (bn : ℝ),
      exec I (nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store ∧
      (∃ w, out.store.read tag 3 (j + 1) = some w ∧ dec tag w = bn) ∧
      0 ≤ bn ∧ (bn = 0 ↔ zv = 0) ∧
      |‖WithLp.toLp 2 zv‖ - bn| ≤
        roundingFactor (N + 1) (u tag) * ‖WithLp.toLp 2 zv‖ ∧
      (∀ p k i, k ≠ 3 ∨ i ≠ j + 1 → out.store.read p k i = st.store.read p k i) := by
  let xs : ℕ → ℝ := fun i => if hi : i < N then zv ⟨i, hi⟩ else 0
  have hxs : (fun i : Fin N => xs i) = zv := by funext i; simp [xs]
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N (h.nonneg trivial) hsmall
  have hdst : ∃ w store, st.store.write tag 3 (j + 1) w = some store := by
    obtain ⟨w, _, _⟩ := hs.zero
    exact ⟨w, Store.exists_write_eq_some_of_getElem?_shape w
      (by rw [hs.shape]; rfl) (by omega)⟩
  obtain ⟨out, w, hr, hw, hpos, herr, hzero⟩ := h.exec_nrm2_abs_norm_sub_le_zero_iff I tag hz st
    ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N) xs hwin.1 hwin.2.2.1
    (by intro i hi; change i < N at hi; simpa [xs, hi] using hzv ⟨i, hi⟩)
    (by simp) hdst
  refine ⟨out, dec tag w, hr, hs.of_frame (Store.shape_of_write_eq_some hw) ?_,
    ⟨w, Store.read_of_write_eq_some hw, rfl⟩, hpos, ?_, ?_, ?_⟩
  · intro p k i _ _ hb _
    apply Store.read_of_write_eq_some_of_ne hw
    by_cases he : k = 3
    · exact Or.inr (hb he)
    · exact Or.inl he
  · change dec tag w = 0 ↔ (fun i : Fin N => xs i) = 0 at hzero
    rwa [hxs] at hzero
  · change |‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ - dec tag w| ≤
      _ * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at herr
    rwa [hxs] at herr
  · intro p k i hi
    exact Store.read_of_write_eq_some_of_ne hw hi

end NLAlib.LanczosImplementation
