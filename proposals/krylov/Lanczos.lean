/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.BLAS.Normalization
public import NLAlib.Computation.Model
public import NLAlib.Krylov.Processes.LanczosRecurrence

/-!
# Proposed concrete stored-matrix Lanczos program

This proposal fixes Paige's operation order, including the rounded norm and componentwise
division. It loads the matrix from ROM and executes the existing dense `gemv` kernel. Every
zero norm writes a zero next column and bypasses division; all requested steps then continue,
matching the total exact recurrence. This file is outside `NLAlib` pending target approval.

A checked program and target definition are not an execution proof of that target.
Design: `docs/design/Krylov-Implementation-Bridge.md`.

## Main definitions

* `NLAlib.lanczosProg`, `NLAlib.lanczosProg.compiled`.
* `NLAlib.lanczosCount`, `NLAlib.StoredEntriesLanczos`: proposed budget and exact target.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-- The concrete proposed stored-matrix Lanczos program. Declared buffers are the unchanged
input, all basis columns through the final state, alpha, beta, input norm and final previous
vector. Matrix and work storage are scoped. Initialization uses actual `nrm2` and `rscl`, and
zero continuation performs every requested step without dividing by a zero norm. -/
def lanczosProg {P ι VB VI : Type} (tag : P) (N q : IExp VI)
    (b V alpha beta inputNorm prev : VB) : Builder P ι VB VI Unit := scope do
  let A ← alloc tag (N * N)
  let work ← alloc tag N
  let scalars ← alloc tag 2
  forRange (N * N) fun i => stmt (.rom tag ⟨A, .var i⟩ (.var i))
  ins (.lit tag ⟨scalars, 0⟩ 0)
  ins (.lit tag ⟨beta, 0⟩ 0)
  forRange N fun i => ins (.lit tag ⟨prev, .var i⟩ 0)
  nrm2 tag ⟨inputNorm, 0⟩ b 0 N
  ifThenElse tag .eq ⟨inputNorm, 0⟩ ⟨scalars, 0⟩
    (forRange N fun i => ins (.lit tag ⟨V, .var i⟩ 0)) (do
      copyv tag b 0 V 0 N
      rscl tag ⟨inputNorm, 0⟩ V 0 N)
  forRange q fun j => do
    gemv tag N N A 0 V (N * .var j) work 0
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨beta, .var j⟩)
    axpy tag ⟨scalars, 1⟩ prev 0 work 0 N
    dot tag ⟨alpha, .var j⟩ V (N * .var j) work 0 N
    ins (.un tag .neg ⟨scalars, 1⟩ ⟨alpha, .var j⟩)
    axpy tag ⟨scalars, 1⟩ V (N * .var j) work 0 N
    nrm2 tag ⟨beta, .var j + 1⟩ work 0 N
    copyv tag V (N * .var j) prev 0 N
    ifThenElse tag .eq ⟨beta, .var j + 1⟩ ⟨scalars, 0⟩
      (forRange N fun i => ins (.lit tag ⟨V, N * (.var j + 1) + .var i⟩ 0)) (do
        copyv tag work 0 V (N * (.var j + 1)) N
        rscl tag ⟨beta, .var j + 1⟩ V (N * (.var j + 1)) N)

/-- The proposed first-order tree, compiled once at symbolic dimension and step count.
It has six free buffers and uses no matrix-vector oracle or random tape. -/
def lanczosProg.compiled {P ι : Type} (tag : P) : Prog P ι 1 6 :=
  (ProgFamily.compile fun _ _ N q h =>
    (lanczosProg tag N (q 0) (h 0) (h 1) (h 2) (h 3) (h 4) (h 5)).run).get rfl

/-- Componentwise upper operation counts for the concrete proposal. Early zero branches
replace copying and division by literal-zero writes. Each component is bounded separately,
so the bound includes both alternatives without asserting that both execute. -/
noncomputable def lanczosCount {P ι : Type} (tag : P) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.rom tag) (N ^ 2) +
  Finsupp.single (.bin tag .mul) (N + q * (N ^ 2 + 4 * N)) +
  Finsupp.single (.bin tag .add) (N + q * (N ^ 2 + 4 * N)) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (N * (q + 1)) +
  Finsupp.single (.un tag .sqrt) (q + 1) +
  Finsupp.single (.un tag .neg) (2 * q) +
  Finsupp.single (.lit tag) (2 * N + 3 + q * (2 * N + 2)) +
  Finsupp.single (.cmp tag) (q + 1) +
  Finsupp.single (.copy tag) (N + 2 * q * N)

/-- The approved exact target, awaiting its full realization proof and registration:
for every real ROM matrix and input, the concrete
compiled program succeeds within the stated counts and memory, and its actual output buffers
hold every basis column and recurrence coefficient, the input norm, and the final previous
vector of `lanczosState`. No symmetry, nonzero-input or nonbreakdown premise is imposed. -/
def StoredEntriesLanczos : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (tag : P),
    StoredEntries (𝕜 := ℝ) tag (lanczosProg.compiled (ι := ι) tag)
      (fun _ _ => True) (fun N _ => Fin N → ℝ)
      (fun N q b => ![(Array.ofFn b).map some, Array.replicate (N * (q 0 + 1)) none,
        Array.replicate (q 0) none, Array.replicate (q 0 + 1) none,
        Array.replicate 1 none, Array.replicate N none])
      (fun N _ => N ^ 2) (fun N q => lanczosCount tag N (q 0))
      (fun N q p => if p = tag then 2 * N ^ 2 + N * (q 0 + 4) + 2 * q 0 + 5 else 0)
      (fun N q b vals _ st =>
        let A : Matrix (Fin N) (Fin N) ℝ := fun i j => vals (i + N * j)
        Holds st.store tag 0 0 (fun i (_ : Fin 1) => b i) ∧
        Holds st.store tag 1 0 (lanczosMatrix A b (q 0 + 1)) ∧
        Holds st.store tag 2 0
          (fun (j : Fin (q 0)) (_ : Fin 1) => lanczosAlpha A (lanczosState A b j)) ∧
        Holds st.store tag 3 0
          (fun (j : Fin (q 0 + 1)) (_ : Fin 1) => (lanczosState A b j).beta) ∧
        st.store.read tag 4 0 = some ‖WithLp.toLp 2 b‖ ∧
        Holds st.store tag 5 0 (fun i (_ : Fin 1) => (lanczosState A b (q 0)).prev i))

/-- Exact execution of the two normalization kernels on a stored nonzero candidate gives
the initial current vector of the mathematical Lanczos recurrence. This is a kernel bridge;
it does not yet prove the surrounding copies, guards, loop or proposed cost target. -/
theorem exec_nrm2_rscl_eq_lanczosState_cur
    {P ι C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P) (st : St P ℝ C)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (b : Fin N → ℝ)
    (normCell : Cell ℕ ℕ) (V : ℕ) (vo : IExp ℕ)
    (hb : Holds st.store tag V vo.eval (fun i (_ : Fin 1) => b i))
    (hd : normCell.buf ≠ V)
    (hnorm : ∃ v s, st.store.write tag normCell.buf normCell.idx.eval v = some s)
    (hpos : 0 < ‖WithLp.toLp 2 b‖) :
    ∃ st₁ st₂,
      exec I (nrm2 tag normCell V vo (.const N)).run st = some st₁ ∧
      exec I (rscl tag normCell V vo (.const N)).run st₁ = some st₂ ∧
      st₂.store.read tag normCell.buf normCell.idx.eval = some ‖WithLp.toLp 2 b‖ ∧
      Holds st₂.store tag V vo.eval (fun i (_ : Fin 1) => (lanczosState A b 0).cur i) := by
  have hsem : IsRelErrSem (fun _ : P => 0) (fun (_ : P) (x : ℝ) => x)
      (fun _ _ => True) I.sem := by rw [hI]; exact isRelErrSem_exactSem
  have hz : AddsZeroExactly (fun (_ : P) (x : ℝ) => x) I.sem := by
    rw [hI]
    exact addsZeroExactly_exactSem
  let xs : ℕ → ℝ := fun i => if hi : i < N then b ⟨i, hi⟩ else 0
  have hvec : (fun i : Fin N => xs i) = b := by ext i; exact dif_pos i.2
  have hx : ∀ i < N, ∃ w, st.store.read tag V (vo.eval + i) = some w ∧ w = xs i := by
    intro i hi
    refine ⟨xs i, ?_, rfl⟩
    simpa only [xs, dif_pos hi, Fin.val_zero, mul_zero, add_zero] using hb ⟨i, hi⟩ 0
  obtain ⟨st₁, st₂, w, W, hrn, hwn, hrs, hws, hwpos, herr, hres, -, -⟩ :=
    hsem.exec_nrm2_rscl I tag st hz normCell V vo (.const N) xs
      (by norm_num) (by simp [roundingFactor]) hx
      (fun h => (hd h).elim) hnorm (by
        change 0 < ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖
        rw [hvec]
        exact hpos)
  change |‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ - w| ≤
    roundingFactor (N + 1) 0 * ‖WithLp.toLp 2 (fun i : Fin N => xs i)‖ at herr
  have hw : w = ‖WithLp.toLp 2 b‖ := by
    simp only [hvec, roundingFactor, mul_zero, zero_div, zero_mul] at herr
    exact (sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm herr (abs_nonneg _)))).symm
  simp only [zero_mul] at hres
  change ‖WithLp.toLp 2 (fun i : Fin N => xs i - w * W i)‖ ≤ 0 at hres
  have hres0 : WithLp.toLp 2 (fun i : Fin N => xs i - w * W i) = 0 := by
    apply norm_eq_zero.mp
    apply le_antisymm _ (norm_nonneg _)
    exact hres
  have hW : ∀ i : Fin N, W i = (lanczosState A b 0).cur i := by
    intro i
    have hi := congrArg (fun v : EuclideanSpace ℝ (Fin N) => v i) hres0
    change xs i - w * W i = 0 at hi
    have hmul : ‖WithLp.toLp 2 b‖ * W i = b i := by
      rw [hw, congrFun hvec i] at hi
      linarith
    change W i = ‖WithLp.toLp 2 b‖⁻¹ * b i
    rw [← hmul, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  refine ⟨st₁, st₂, hrn, hrs, ?_, ?_⟩
  · rw [Store.read_of_writeBlock_eq_some_of_ne hws (Or.inl hd),
      Store.read_of_write_eq_some hwn, hw]
  · intro i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    simpa only [Fin.val_zero, mul_zero, add_zero, IExp.eval_const, Array.getElem?_map,
      List.getElem?_toArray, List.getElem?_range i.2, Option.map_some, hW] using
        Store.read_of_writeBlock_eq_some_of_lt (j := (i : ℕ)) hws
          (by simp only [Array.size_map,
          List.size_toArray, List.length_range]; exact i.2)

end NLAlib
