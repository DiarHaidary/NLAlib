/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.MatvecRoutine
public import NLAlib.Matrix.Perturbation.OrthErr
public import NLAlib.Computation.RoutineSpec

/-!
# Orthogonalization routines: the execution certificate

`NLAlib.Computation.IsOrthRoutine` is the execution certificate of a routine that reduces a
vector against the columns of a stored basis and meets the decoded guarantee
`NLAlib.IsOrthErr`, the analogue of `NLAlib.Computation.IsMatvecRoutine`; the Lanczos analysis
with full reorthogonalization consumes only its parameters. Design:
`docs/design/Krylov-LanczosReorth.md` §1.

## Main definitions

* `NLAlib.Computation.IsOrthRoutine`: the execution certificate of an orthogonalization routine.

## Main results

* `NLAlib.Computation.IsOrthRoutine.mono`: larger parameters.
* `NLAlib.Computation.IsOrthRoutine.toBlockRoutine`: the footprint of the certificate.
* `NLAlib.Computation.IsOrthRoutine.routineSpec`: the certificate as a specification of the
  program logic (`NLAlib/Computation/ProgramLogic.lean`).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- **A certified orthogonalization routine** at parameters $(\eta_0, \varepsilon_1,
\varepsilon_2, \varepsilon_3)$: from any state satisfying `pre` whose buffer `Vb` holds a basis
$\mathbf{V}$ ($N \times j$, column-major from offset $0$), whose buffer `wb` holds $\mathbf{w}$
at `wo`, and whose buffer `hb` has room for $j$ coefficients at `ho`, the routine succeeds and
its only effect is to write the reduced vector at (`wb`, `wo`) and the coefficients at
(`hb`, `ho`); the decoded values meet `NLAlib.IsOrthErr`. Scratch storage is scoped, so the
shape of the store is preserved. The analogue of `NLAlib.Computation.IsMatvecRoutine`. -/
structure IsOrthRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P) (N j : ℕ)
    (η₀ ε₁ ε₂ ε₃ : ℝ) (pre : Store P K → Prop) (Vb wb hb : ℕ) (wo ho : IExp ℕ)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  /-- The routine composes with the following program. -/
  composable : ExecutionComposable I routine
  /-- Readable inputs and writable outputs imply execution, its frame and its guarantee. -/
  run : ∀ (st : St P K C) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ), pre st.store →
    HoldsDecoded st.store dec tag Vb 0 V →
    (∀ i : Fin N, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i) →
    (∀ i < N, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len) →
    (∀ i < j, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len) →
    hb ≠ wb → hb ≠ Vb → wb ≠ Vb →
    ∃ (out : St P K C) (W : Fin N → K) (Hw : Fin j → K) (mid : Store P K),
      exec I routine.run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn W) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hw) = some out.store ∧
      IsOrthErr η₀ ε₁ ε₂ ε₃ V w (fun i => dec tag (Hw i)) (fun i => dec tag (W i))

/-- A certified orthogonalization routine remains certified for a smaller precondition
$\eta_0' \le \eta_0$ and larger parameters $\varepsilon_i \le \varepsilon_i'$. -/
theorem IsOrthRoutine.mono {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N j : ℕ}
    {η₀ ε₁ ε₂ ε₃ η₀' ε₁' ε₂' ε₃' : ℝ} {pre : Store P K → Prop} {Vb wb hb : ℕ} {wo ho : IExp ℕ}
    {routine : Builder P ι ℕ ℕ Unit}
    (h : IsOrthRoutine I dec tag N j η₀ ε₁ ε₂ ε₃ pre Vb wb hb wo ho routine) (hη : η₀' ≤ η₀)
    (h₁ : ε₁ ≤ ε₁') (h₂ : ε₂ ≤ ε₂') (h₃ : ε₃ ≤ ε₃') :
    IsOrthRoutine I dec tag N j η₀' ε₁' ε₂' ε₃' pre Vb wb hb wo ho routine where
  composable := h.composable
  run st V w hp hV hw hwl hhl hbw hbV hwV := by
    obtain ⟨out, W, Hw, mid, hr, hm, hf, he⟩ := h.run st V w hp hV hw hwl hhl hbw hbV hwV
    exact ⟨out, W, Hw, mid, hr, hm, hf, he.mono hη h₁ h₂ h₃⟩

/-- The footprint of a certified orthogonalization routine with distinct buffers: from a state
satisfying `pre` that holds a basis in `Vb` and a vector at (`wb`, `wo`), it writes exactly the
reduced vector block and then the coefficient block (`NLAlib.Computation.IsBlockRoutine`). -/
theorem IsOrthRoutine.toBlockRoutine {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P}
    {N j : ℕ} {η₀ ε₁ ε₂ ε₃ : ℝ} {pre : Store P K → Prop} {Vb wb hb : ℕ} {wo ho : IExp ℕ}
    {routine : Builder P ι ℕ ℕ Unit}
    (h : IsOrthRoutine I dec tag N j η₀ ε₁ ε₂ ε₃ pre Vb wb hb wo ho routine)
    (hbw : hb ≠ wb) (hbV : hb ≠ Vb) (hwV : wb ≠ Vb) :
    IsBlockRoutine I tag (fun s => pre s ∧ ∃ (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ),
      HoldsDecoded s dec tag Vb 0 V ∧ ReadsDecoded s dec tag wb wo.eval w)
      [(wb, wo.eval, N), (hb, ho.eval, j)] routine where
  composable := h.composable
  run st hp hw := by
    obtain ⟨hp, V, w, hV, hwd⟩ := hp
    obtain ⟨out, W, Hw, mid, hr, h₁, h₂, -⟩ := h.run st V w hp hV hwd
      (hw _ List.mem_cons_self) (hw (hb, ho.eval, j) (by simp)) hbw hbV hwV
    exact ⟨out, [Array.ofFn W, Array.ofFn Hw], hr,
      Store.writeBlocks_pair_eq_some_iff.mpr ⟨by simp, by simp, mid, h₁, h₂⟩⟩

/-- **A certified orthogonalization routine as a specification**, for each stored basis
$\mathbf{V}$ and vector $\mathbf{w}$, with distinct buffers: it modifies only the reduced vector
and coefficient blocks, which then decode to values meeting `NLAlib.IsOrthErr`. -/
theorem IsOrthRoutine.routineSpec {I : Interp P ι K C} {dec : P → K → ℝ} {tag : P} {N j : ℕ}
    {η₀ ε₁ ε₂ ε₃ : ℝ} {pre : Store P K → Prop} {Vb wb hb : ℕ} {wo ho : IExp ℕ}
    {r : Builder P ι ℕ ℕ Unit}
    (h : IsOrthRoutine I dec tag N j η₀ ε₁ ε₂ ε₃ pre Vb wb hb wo ho r) (hbw : hb ≠ wb)
    (hbV : hb ≠ Vb) (hwV : wb ≠ Vb) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ) :
    RoutineSpec .total I (fun st => pre st.store ∧ HoldsDecoded st.store dec tag Vb 0 V ∧
        ReadsDecoded st.store dec tag wb wo.eval w ∧ Writable st.store tag wb wo.eval N ∧
        Writable st.store tag hb ho.eval j) r [(wb, wo.eval, N), (hb, ho.eval, j)]
      fun _ st' => ∃ (W : Fin N → ℝ) (H : Fin j → ℝ), ReadsDecoded st'.store dec tag wb wo.eval W ∧
        ReadsDecoded st'.store dec tag hb ho.eval H ∧ IsOrthErr η₀ ε₁ ε₂ ε₃ V w H W := by
  refine ⟨h.composable, fun st ⟨hp, hV, hw, hwl, hhl⟩ => ?_⟩
  obtain ⟨out, W, Hw, mid, hr, hm, hf, he⟩ := h.run st V w hp hV hw hwl hhl hbw hbV hwV
  have hmod := (Modifies.of_writeBlock hm).trans (Modifies.of_writeBlock hf)
  simp only [Array.size_ofFn, List.singleton_append] at hmod
  refine ⟨out, hr, hmod, fun i => dec tag (W i), fun i => dec tag (Hw i), fun i => ⟨W i, ?_, rfl⟩,
    fun i => ⟨Hw i, ?_, rfl⟩, he⟩
  · rw [Store.read_of_writeBlock_eq_some_of_ne hf (Or.inl hbw.symm),
      Store.read_of_writeBlock_eq_some_of_lt hm (by rw [Array.size_ofFn]; exact i.2)]
    simp
  · rw [Store.read_of_writeBlock_eq_some_of_lt hf (by rw [Array.size_ofFn]; exact i.2)]
    simp

end NLAlib.Computation
