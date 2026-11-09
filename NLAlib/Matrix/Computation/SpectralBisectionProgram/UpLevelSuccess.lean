/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgram.UpLevel

/-!
# The upward level of the spectral bisection program succeeds

Under the standard model with every value in range, one level of the upward pass of
`NLAlib.eighProg` (`NLAlib.eighUpLevel`) succeeds from arenas that hold the outputs of the depth
below and the records of its depth (`NLAlib.spec_eighUpLevel` in mode `total`).

## Main results

* `NLAlib.exists_exec_eighUpLevel`: the level succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-- One level of the upward pass succeeds: if kernel `mm` of `I` is the routine `mmR` on interleaved
pairs, under a relative-error semantics `I.sem` (unit roundoff `u`, decoding `dec`) with every value
in range and exact integer literals up to $n + 4$, the run of `NLAlib.eighUpLevel` at depth $d < D$
succeeds from a state whose arenas `H` are allocated (`NLAlib.EighArenas.Shaped` at size $n$ and
budget $D$) and hold the nodes and records of depth $d$ and the outputs of depth $d + 1$, with the
stored $\mathrm{fl}(2)$ in the cell `two`. No printed source. -/
theorem exists_exec_eighUpLevel {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hlit : IsExactIntLit dec I.sem (n + 4))
    (H : EighArenas) {two : Cell ℕ ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K}
    (hH : H.Shaped st.store p n D)
    (htwov : st.store.read p two.buf two.idx.eval = I.sem.lit p ((2 : ℕ) : ℚ))
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hrec : H.RecordHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hout : H.OutHolds st.store p (eighTapeMachine I p mmR qrR) n F D R₀ β ⟨n, A, R₀, ε, ℓ₀⟩
      (d + 1)) :
    ∃ st', exec I (eighUpLevel p mm (.const n) (.const d) H.Lv H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp
      two).run st = some st' := by
  obtain ⟨st', h, -⟩ := (spec_eighUpLevel hmm .total hsem p n ℓ₀ F d D hd hlit H
    (b := st.store.size)
    (two := two)).spec.exists_exec ⟨rfl, hH, htwov, hlev, hrec, hout⟩
  exact ⟨st', h⟩

end NLAlib
