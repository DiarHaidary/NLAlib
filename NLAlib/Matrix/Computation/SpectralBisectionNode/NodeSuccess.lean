/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode

/-!
# The node step of the spectral bisection program succeeds

Under the standard model at $u$ with every value in range, $u(p) < 1$, exact literals up to $2$ and
the exact floor conversion, if the kernels are routines on pairs, the window decodes to a positive
value, the depth counter is at least $1$ and the arenas are allocated, no operation of the node step
of `NLAlib.eighProg` fails: the divisions are by $\mathrm{fl}(2)$, $\ell$ and $b = \mathrm{fl}(2R)
\ne 0$, the sign step does not fail for want of steps, and the conversion is total.

## Main results

* `NLAlib.exists_exec_eighNodeBlock`: the node step succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {Su Sg : Type} {toNat : K → ℕ} {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}
  {unif : K → Su → K} {normal : Sg → K × K}

omit [Inhabited K] in
/-- A goal on a state, by a named state. -/
theorem exists_exec_of_forall_eq {X : Stmt P ι ℕ ℕ} {s : St P K C}
    (h : ∀ σ : St P K C, σ = s → ∃ st', exec I X σ = some st') :
    ∃ st', exec I X s = some st' := h s rfl

/-- The node step succeeds under the standard model at $u$ with every value in range,
$u(p) < 1$, exact literals up to $2$ and the exact floor conversion, if the kernels are routines on
pairs, the window decodes to a positive value, the depth counter $\ell_0 + d$ is at least $1$ and
the arenas are allocated (hypotheses on the inputs as `NLAlib.holds_of_exec_eighNodeBlock`): no
operation fails (the divisions are by $\mathrm{fl}(2)$, $\ell$ and $b = \mathrm{fl}(2R) \ne 0$, the
sign step does not fail for want of steps, the conversion is total). No printed source. -/
theorem exists_exec_eighNodeBlock {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2)
    (htn : IsExactToNat dec I.sem) (p : P) (hu : u p < 1) (n ℓ₀ F d lo k : ℕ)
    (hlitn : IsExactIntLit dec I.sem n) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (hℓ : 1 ≤ ℓ₀ + d) (H : EighArenas) {par Su Sg c : ℕ} {st : St P K C}
    {A : Matrix (Fin k) (Fin k) (K × K)} {R β : K}
    {D : ℕ} (hd : d < D) (hH : H.Shaped st.store p n D)
    (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R) (hR0 : 0 < dec p R)
    (hpar : st.store.read p par 2 = some β)
    (hSu : ∃ v, st.store.read p Su lo = some v)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      (∃ v, st.store.read p c 2 = some v) ∧ (∃ v, st.store.read p c 3 = some v) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighNodeBlock p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) (.const lo)
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩
        ⟨c, 4⟩).run st = some st' := by
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  obtain ⟨o, ho⟩ := hsem.lit_ok p 1 trivial
  obtain ⟨z₂, hz₂, hdz₂⟩ := hlit p 2 le_rfl
  obtain ⟨hc0, hc1, ⟨h, hc2⟩, ⟨m, hc3⟩, hc4⟩ := hc
  obtain ⟨v, hv⟩ := hSu
  have hlt := hH.forall_lt_size (hSg 0 hn2).choose_spec hpar ⟨lo, hv⟩ (hc0.trans ho)
  have hg : ∀ w < 4 * (n * n), st.store.read p Sg w =
      some (if hw : w < 4 * (n * n) then (hSg w hw).choose else default) := fun w hw => by
    rw [dif_pos hw]
    exact (hSg w hw).choose_spec
  exact ((spec_eighNodeBlock hmm hqr .total p n ℓ₀ F d lo k ⟨hsem, fun _ _ => trivial, hu⟩
    (hsem.decidesFlags (fun q m hm => hlit q m (by omega)) p) (hsem.cmp_le p)
    (fun q m hm => hlitn q m (by omega)) htn hk hk2 H hbufs hlt A _ _ _ R β v o z₂ h m _ _ rfl rfl
    rfl rfl).spec.exists_exec ⟨rfl, ⟨hA, hR, hpar, hv, hc0.trans ho, hc1.trans hz₂, hc2, hc3, hc4,
      hg⟩, nofun, by rw [hdz₂]; norm_num, hR0.ne', hℓ, writableBlocks_eighBranchWindow hk
        (by omega) hd hH, fun q => hsem.lit_ok p _ trivial⟩).imp fun _ h => h.1

end NLAlib
