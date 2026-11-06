/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.MatvecRoutine
public import NLAlib.Matrix.Perturbation.OrthErr

/-!
# Orthogonalization routines: the execution certificate

`NLAlib.Computation.IsOrthRoutine` is the execution certificate of a routine that reduces a
vector against the columns of a stored basis and meets the decoded guarantee
`NLAlib.IsOrthErr`, the analogue of `NLAlib.Computation.IsMatvecRoutine`; the Lanczos analysis
with full reorthogonalization consumes only its parameters. Design:
`docs/design/Krylov-LanczosReorth.md` §1.

## Main definitions

* `NLAlib.Computation.IsOrthRoutine`: the execution certificate of an orthogonalization routine.
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

end NLAlib.Computation
