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
public import NLAlib.Matrix.Computation.MatvecRoutine

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
    {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
    {mv : ℕ → Builder P ι ℕ ℕ Unit}

/-- Primitive scalar rounding certifies the dense backend at the existing Lanczos
implementation budget, for every basis-column offset and including empty dimension. -/
theorem isMatvecRoutine_dense (I : Interp P ι K (OpCount P ι)) (tag : P)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (N : ℕ) (A : Matrix (Fin N) (Fin N) ℝ)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) (j : ℕ) :
    IsMatvecRoutine I dec tag A
      (lanczosImplementationRoundoffBound N (u tag) * specNorm A)
      (fun store => HoldsDecoded store dec tag 6 0 A)
      1 7 (IExp.const N * IExp.var j) 0
      (gemv tag (.const N) (.const N) 6 0 1 (IExp.const N * IExp.var j) 7 0) := by
  have hu := h.nonneg (p := tag) trivial
  have hwin := lanczosImplementationRoundoffBound_kernel_bounds N hu hsmall
  have hn : (N : ℝ) * u tag < 1 := by
    have hs := hwin.1
    push_cast at hs
    nlinarith
  exact (h.isMatvecRoutine_gemv I tag hz N A 6 1 7 0 (IExp.const N * IExp.var j) 0
    hn (by omega) (by omega)).mono (mul_le_mul_of_nonneg_right
      (roundingFactor_mul_sqrt_le_lanczosImplementationRoundoffBound N hu hsmall)
      (specNorm_nonneg A))

/-- A certified backend executes the current Lanczos product, preserving the completed
prefix through its actual block-write frame. Scalar rounding is a separate hypothesis of
the subsequent Paige phases. -/
theorem exec_rounded_matvec (I : Interp P ι K (OpCount P ι)) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι))
    (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    {c : ℝ} (hmv : IsMatvecRoutine I dec tag A c
      (fun store => if storedMatrix then HoldsDecoded store dec tag 6 0 A else True)
      1 7 (IExp.const N * IExp.var j) 0 (mv j)) :
    ∃ (out : St P K (OpCount P ι)) (uv : Fin N → ℝ),
      exec I (mv j).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store storedMatrix ∧
      (∀ i : Fin N, ∃ w, out.store.read tag 7 i = some w ∧ dec tag w = uv i) ∧
      ‖WithLp.toLp 2 (A *ᵥ v (j + 1) - uv)‖ ≤ c * ‖WithLp.toLp 2 (v (j + 1))‖ := by
  obtain ⟨out, W, hr, hw, he⟩ := hmv.run st (v (j + 1)) hs.matrix
    (by simpa only [IExp.eval_mul, IExp.eval_const, IExp.eval_var] using hs.basis j le_rfl)
    (fun i hi => ⟨N, by simp [hs.shape, workspaceShape], by simpa using hi⟩)
  refine ⟨out, fun i => dec tag (W i), hr, ?_, ?_, he⟩
  · exact hs.of_frame (Store.shape_of_writeBlock_eq_some hw) (by
      intro p k i hk _ _ _
      exact Store.read_of_writeBlock_eq_some_of_ne hw (Or.inl hk))
  · intro i
    refine ⟨W i, ?_, rfl⟩
    simpa using Store.read_of_writeBlock_eq_some_of_lt hw
      (j := (i : ℕ)) (by simp)

/-- The actual previous-vector subtraction executes the scalar negation before axpy.
The returned work vector and its complete prefix invariant are derived from actual reads;
the previous coefficient may be zero or negative. -/
theorem exec_rounded_previous_update (I : Interp P ι K (OpCount P ι))
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (tag : P)
    {N q j : ℕ} {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ}
    {v : ℕ → Fin N → ℝ} {α β : ℕ → ℝ} {s : ℝ}
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    (uv : Fin N → ℝ)
    (huv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = uv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (wv : Fin N → ℝ),
      exec I (do
        ins (.un tag .neg ⟨8, 1⟩ ⟨3, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 5 0 7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store storedMatrix ∧
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
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    (hj : j < q) (wv : Fin N → ℝ)
    (hwv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = wv i)
    (hn : (N : ℝ) * u tag < 1) :
    ∃ (out : St P K (OpCount P ι)) (an : ℝ),
      exec I (dot tag ⟨2, IExp.var j⟩ 1 (IExp.const N * IExp.var j)
        7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store storedMatrix ∧
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
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    (an : ℝ) (han : ∃ w, st.store.read tag 2 j = some w ∧ dec tag w = an)
    (wv : Fin N → ℝ)
    (hwv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = wv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (zv : Fin N → ℝ),
      exec I (do
        ins (.un tag .neg ⟨8, 1⟩ ⟨2, IExp.var j⟩)
        axpy tag ⟨8, 1⟩ 1 (IExp.const N * IExp.var j) 7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store storedMatrix ∧
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
    (st : St P K (OpCount P ι)) (hs : StoreContext tag dec N q j A b v α β s st.store storedMatrix)
    (hj : j < q) (zv : Fin N → ℝ)
    (hzv : ∀ i : Fin N, ∃ w, st.store.read tag 7 i = some w ∧ dec tag w = zv i)
    (hsmall : lanczosImplementationRoundoffBound N (u tag) ≤ 1 / 100) :
    ∃ (out : St P K (OpCount P ι)) (bn : ℝ),
      exec I (nrm2 tag ⟨3, IExp.var j + 1⟩ 7 0 (IExp.const N)).run st = some out ∧
      StoreContext tag dec N q j A b v α β s out.store storedMatrix ∧
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
