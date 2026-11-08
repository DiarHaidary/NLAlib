/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Processes.LanczosProgramState

/-!
# Decoded storage of the rounded Lanczos program

The concrete nine-buffer layout stores actual words. Its decoded prefix is recorded without
assuming recurrence identities, local error bounds, successful future execution or nonzero
off-diagonal coefficients. Kernel execution establishes those additional facts separately.

## Main definitions

* `NLAlib.LanczosImplementation.StoreContext`: decoded initialized cells and prefixes.

## Main results

* `NLAlib.LanczosImplementation.StoreContext.of_frame`: preservation through local work writes.
* `NLAlib.LanczosImplementation.StoreContext.succ_of_commit`: installation of a computed column.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open Computation

variable {P K : Type} [DecidableEq P] {storedMatrix : Bool}

/-- Actual decoded words after initialization and `j` rounded Lanczos steps. The basis
column `c` stores `v (c+1)`, while the previous-vector buffer stores `v j`. The scalar and
vector prefixes have no assumed arithmetic relation. The stored-matrix flag defaults to
true; the oracle variant leaves the matrix slot empty and imposes no matrix-storage condition. -/
structure StoreContext (tag : P) (dec : P → K → ℝ) (N q j : ℕ)
    (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ) (v : ℕ → Fin N → ℝ)
    (α β : ℕ → ℝ) (s : ℝ) (store : Store P K) (storedMatrix : Bool := true) : Prop where
  /-- The canonical nine-buffer shape, with an empty matrix slot for the oracle variant. -/
  shape : store.shape = workspaceShape tag N q storedMatrix
  /-- The declared input words are retained. -/
  input : ∀ i : Fin N, ∃ w, store.read tag 0 i = some w ∧ dec tag w = b i
  /-- Stored execution has loaded the matrix column-major; the oracle variant needs no entries. -/
  matrix : if storedMatrix then HoldsDecoded store dec tag 6 0 A else True
  /-- Completed basis columns, including the initialized first column. -/
  basis : ∀ c ≤ j, ∀ i : Fin N,
    ∃ w, store.read tag 1 (N * c + i) = some w ∧ dec tag w = v (c + 1) i
  /-- Completed diagonal coefficients. -/
  alpha : ∀ c < j, ∃ w, store.read tag 2 c = some w ∧ dec tag w = α (c + 1)
  /-- Initial and completed off-diagonal coefficients. -/
  beta : ∀ c ≤ j, ∃ w, store.read tag 3 c = some w ∧ dec tag w = β c
  /-- The retained computed input norm. -/
  inputNorm : ∃ w, store.read tag 4 0 = some w ∧ dec tag w = s
  /-- The previous vector used by the next Paige step. -/
  prev : ∀ i : Fin N, ∃ w, store.read tag 5 i = some w ∧ dec tag w = v j i
  /-- The persistent comparison word decodes to zero. -/
  zero : ∃ w, store.read tag 8 0 = some w ∧ dec tag w = 0

variable {tag : P} {dec : P → K → ℝ} {N q j : ℕ}
    {A : Matrix (Fin N) (Fin N) ℝ} {b : Fin N → ℝ} {v : ℕ → Fin N → ℝ}
    {α β : ℕ → ℝ} {s : ℝ} {old next : Store P K}

/-- Local work-vector, current diagonal, next off-diagonal and negation-scratch writes
preserve every already completed decoded prefix. The premise concerns actual raw reads. -/
theorem StoreContext.of_frame (h : StoreContext tag dec N q j A b v α β s old storedMatrix)
    (hshape : next.shape = old.shape)
    (hf : ∀ p k i, k ≠ 7 → (k = 2 → i ≠ j) → (k = 3 → i ≠ j + 1) →
      (k = 8 → i ≠ 1) → next.read p k i = old.read p k i) :
    StoreContext tag dec N q j A b v α β s next storedMatrix := by
  refine ⟨hshape.trans h.shape, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hf tag 0 i (by omega) (by omega) (by omega) (by omega)]
    exact h.input i
  · cases storedMatrix with
    | false => trivial
    | true =>
      intro i k
      rw [hf tag 6 _ (by omega) (by omega) (by omega) (by omega)]
      exact h.matrix i k
  · intro c hc i
    rw [hf tag 1 _ (by omega) (by omega) (by omega) (by omega)]
    exact h.basis c hc i
  · intro c hc
    rw [hf tag 2 c (by omega) (by omega) (by omega) (by omega)]
    exact h.alpha c hc
  · intro c hc
    rw [hf tag 3 c (by omega) (by omega) (by omega) (by omega)]
    exact h.beta c hc
  · rw [hf tag 4 0 (by omega) (by omega) (by omega) (by omega)]
    exact h.inputNorm
  · intro i
    rw [hf tag 5 i (by omega) (by omega) (by omega) (by omega)]
    exact h.prev i
  · rw [hf tag 8 0 (by omega) (by omega) (by omega) (by omega)]
    exact h.zero

/-- Commit the actual next basis column, previous vector and two coefficients. Old
prefixes are retained through a raw frame outside the new column and previous-vector
buffer. No numerical property of the supplied decoded outputs is assumed. -/
theorem StoreContext.succ_of_commit (h : StoreContext tag dec N q j A b v α β s old storedMatrix)
    (vn : Fin N → ℝ) (an bn : ℝ) (hshape : next.shape = old.shape)
    (hf : ∀ p k i, k ≠ 5 → (k = 1 → i < N * (j + 1) ∨ N * (j + 2) ≤ i) →
      next.read p k i = old.read p k i)
    (hvn : ∀ i : Fin N, ∃ w,
      next.read tag 1 (N * (j + 1) + i) = some w ∧ dec tag w = vn i)
    (han : ∃ w, next.read tag 2 j = some w ∧ dec tag w = an)
    (hbn : ∃ w, next.read tag 3 (j + 1) = some w ∧ dec tag w = bn)
    (hp : ∀ i : Fin N, ∃ w, next.read tag 5 i = some w ∧ dec tag w = v (j + 1) i) :
    StoreContext tag dec N q (j + 1) A b (Function.update v (j + 2) vn)
      (Function.update α (j + 1) an) (Function.update β (j + 1) bn) s next storedMatrix := by
  refine ⟨hshape.trans h.shape, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hf tag 0 i (by omega) (by omega)]
    exact h.input i
  · cases storedMatrix with
    | false => trivial
    | true =>
      intro i k
      rw [hf tag 6 _ (by omega) (by omega)]
      exact h.matrix i k
  · intro c hc i
    by_cases he : c = j + 1
    · subst c
      simpa using hvn i
    · have hcj : c ≤ j := by omega
      have hi : N * c + i < N * (j + 1) := by
        calc
          N * c + i < N * c + N := Nat.add_lt_add_left i.isLt _
          _ = N * (c + 1) := by rw [Nat.mul_add, Nat.mul_one]
          _ ≤ N * (j + 1) := Nat.mul_le_mul_left N (by omega)
      rw [hf tag 1 _ (by omega) (fun _ => Or.inl hi)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ j + 2)] using h.basis c hcj i
  · intro c hc
    by_cases he : c = j
    · subst c
      simpa using han
    · rw [hf tag 2 c (by omega) (by omega)]
      simpa only [Function.update_of_ne (by omega : c + 1 ≠ j + 1)] using
        h.alpha c (by omega)
  · intro c hc
    by_cases he : c = j + 1
    · subst c
      simpa using hbn
    · rw [hf tag 3 c (by omega) (by omega)]
      simpa only [Function.update_of_ne he] using h.beta c (by omega)
  · rw [hf tag 4 0 (by omega) (by omega)]
    exact h.inputNorm
  · intro i
    simpa only [Function.update_of_ne (by omega : j + 1 ≠ j + 2)] using hp i
  · rw [hf tag 8 0 (by omega) (by omega)]
    exact h.zero

end NLAlib.LanczosImplementation
