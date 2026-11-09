/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionNode.NodeSuccess
public import NLAlib.Matrix.Computation.SpectralBisectionProgram.DownLevel

/-!
# The downward level of the spectral bisection program succeeds

Under the standard model with every value in range, one level of the downward pass of
`NLAlib.eighProg` (`NLAlib.eighDownLevel`) succeeds from arenas that hold the nodes of its depth.

## Main results

* `NLAlib.exists_exec_eighDownLevel`: the level succeeds.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C] [Inhabited K] {I : Interp P ι K C}
  {mmR : MatMulMap (K × K)} {qrR : QRMap (K × K)}

/-! #### Sequences of instructions that succeed -/

omit [Inhabited K] in
/-- An index literal, then the rest. -/
theorem exists_exec_seq_litIdx {p : P} {dst : Cell ℕ ℕ} {e : IExp ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {v : K} {s' : Store P K} (hv : I.sem.lit p (e.eval : ℚ) = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.lit p) } = some st') :
    ∃ st', exec I (.seq (.instr (.litIdx p dst e)) t) s = some st' := by
  rw [exec_seq_instr_litIdx I hv hw]
  exact h

omit [Inhabited K] in
/-- A binary operation, then the rest. -/
theorem exists_exec_seq_bin {p : P} {b : BinOp} {dst x y : Cell ℕ ℕ} {t : Stmt P ι ℕ ℕ}
    {s : St P K C} {a c v : K} {s' : Store P K} (hx : s.store.read p x.buf x.idx.eval = some a)
    (hy : s.store.read p y.buf y.idx.eval = some c) (hv : I.sem.bin p b a c = some v)
    (hw : s.store.write p dst.buf dst.idx.eval v = some s')
    (h : ∃ st', exec I t { s with store := s', cnt := s.cnt + I.charge (.bin p b) } = some st') :
    ∃ st', exec I (.seq (.instr (.bin p b dst x y)) t) s = some st' := by
  rw [exec_seq_instr_bin I hx hy hv hw]
  exact h

/-- One level of the downward pass succeeds: under the standard model at $u$ with every value in
range, $u(p) < 1$, exact integer literals up to $n + 4$ and the exact floor conversion, kernels
that are routines on pairs `mmR`, `qrR`, $\ell_0 \ge 1$, $R_0$ decoding to a nonnegative
value, and $M$ = `NLAlib.eighTapeMachine I p mmR qrR` with the root
$(n, \mathbf{A}, R_0, \varepsilon, \ell_0)$: a run of `NLAlib.eighDownLevel` at depth $d < D$ from
a state whose arenas are allocated and hold the nodes of depth $d$
(`NLAlib.EighArenas.LevelHolds`), with $R_0$, $\beta$ in `par`, sample buffers `Su`, `Sg` of
lengths at least $n$ and $4n^2$, the tape positions $nd$ (uniform) and $4n^2 d$ (Gaussian), and the
constants in `c` (cells $0$ to $4$: one, $\mathrm{fl}(2)$, $\mathrm{fl}(1/2)$, $-1$, the stored
$\sqrt{1/2}$), succeeds. No printed source. -/
theorem exists_exec_eighDownLevel {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (hu : u p < 1)
    (n ℓ₀ F d D : ℕ) (hd : d < D) (hℓ : 1 ≤ ℓ₀) (hlit : IsExactIntLit dec I.sem (n + 4))
    (htn : IsExactToNat dec I.sem) (H : EighArenas) {par Su Sg c : ℕ} {st : St P K C}
    {A : Matrix (Fin n) (Fin n) (K × K)} {R₀ ε β : K} (hR₀ : 0 ≤ dec p R₀)
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [par, Su, Sg, c]).Nodup)
    (hlev : H.LevelHolds I.sem st.store p (eighTapeMachine I p mmR qrR) n F ℓ₀ R₀ β
      ⟨n, A, R₀, ε, ℓ₀⟩ d)
    (hpar : st.store.read p par 0 = some R₀ ∧ st.store.read p par 2 = some β)
    (hSu : ∃ len, st.store.shape[Su]? = some (p, len) ∧ n ≤ len)
    (hSg : ∃ len, st.store.shape[Sg]? = some (p, len) ∧ 4 * (n * n) ≤ len)
    (hpos : st.pos .uniform = n * d ∧ st.pos .gaussian = 4 * (n * n) * d)
    (hc : st.store.read p c 0 = I.sem.lit p 1 ∧ st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ) ∧
      st.store.read p c 2 = some ((eighTapeMachine I p mmR qrR).div
        (eighTapeMachine I p mmR qrR).one ((eighTapeMachine I p mmR qrR).ofNat 2)) ∧
      st.store.read p c 3 = some ((eighTapeMachine I p mmR qrR).neg
        (eighTapeMachine I p mmR qrR).one) ∧
      st.store.read p c 4 = some (I.sem.sqrtHalf p)) :
    ∃ st', exec I (eighDownLevel p mm qr (.const n) (.const ℓ₀) (.const F) (.const d) par H.Lv
      Su Sg H.Ma H.Ua H.Qa H.Ea H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
        some st' := by
  obtain ⟨-, o1, -, hl1, -, -⟩ := hsem.decidesFlags
    (fun q k hk => hlit q k (hk.trans (by omega))) p
  obtain ⟨hnd, hMa, hUa, hQa, hEa, hSzs, hKd, hKp, hLv⟩ := id hH
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  have hlt : ∀ x ∈ H.handles ++ [par, c], x < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSzs, hsz hKd, hsz hKp, hsz hLv,
      Store.lt_size_of_read_eq_some hpar.1, Store.lt_size_of_read_eq_some (hc.1.trans hl1)⟩
  obtain ⟨len1, hSush, hlen1⟩ := hSu
  obtain ⟨len2, hSgsh, hlen2⟩ := hSg
  obtain ⟨st', hrun, -⟩ := (spec_eighDownLevel (u := u) (safe := fun _ _ => True) hmm hqr .total p
    n ℓ₀ F d D ⟨hsem, fun _ _ => trivial, hu⟩ (hsem.decidesFlags
      (fun q k hk => hlit q k (hk.trans (by omega))) p) (hsem.cmp_le p) hlit htn H hbufs
    hlt).spec.exists_exec ⟨rfl, hH, hlev, hpos, hpar, hc, fun i hi => ⟨len1, hSush, by omega⟩,
      fun i hi => ⟨len2, hSgsh, by omega⟩, hR₀, hℓ, hd⟩
  exact ⟨st', hrun⟩

end NLAlib
