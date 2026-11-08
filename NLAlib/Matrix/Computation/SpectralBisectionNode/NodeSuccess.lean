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
/-- A goal on a state with a new store and count, by a named state. -/
private theorem ex_name_node {X : Stmt P ι ℕ ℕ} {s : St P K C} {s1 : Store P K} {c : C}
    (h : ∀ σ : St P K C, σ.store = s1 → σ.pos = s.pos → ∃ st', exec I X σ = some st') :
    ∃ st', exec I X { s with store := s1, cnt := c } = some st' := h _ rfl rfl

omit [Inhabited K] in
/-- A kernel block, then the rest, succeeds if both do. -/
private theorem ex_bind_node {b : Builder P ι ℕ ℕ Unit} {X : Stmt P ι ℕ ℕ}
    (hb : ∀ k, ContT.run b k = .seq X (k ())) {f : Unit → Builder P ι ℕ ℕ Unit} {st : St P K C}
    (h₁ : ∃ σ, exec I b.run st = some σ)
    (h₂ : ∀ σ, exec I b.run st = some σ → ∃ st', exec I (f ()).run σ = some st') :
    ∃ st', exec I (b >>= f).run st = some st' := by
  obtain ⟨σ, hσ⟩ := h₁
  rw [exec_run_bind I hb, hσ, Option.bind_some]
  exact h₂ σ hσ

/-- A real trace succeeds when its matrix is stored and its destination can be written. -/
private theorem exists_exec_ztraceRe_node {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n : ℕ) {X : ℕ} {xo : IExp ℕ}
    {dst : Cell ℕ ℕ} {st : St P K C} {A : Matrix (Fin n) (Fin n) (K × K)}
    (hA : pairLayout.Holds st.store p X xo.eval A) (hdX : dst.buf ≠ X)
    (hdst : ∃ s, st.store.write p dst.buf dst.idx.eval default = some s) :
    ∃ st', exec I (ztraceRe (ι := ι) p (.const n) X xo dst).run st = some st' := by
  change ∃ st', exec I (.seq (.named _ _ (.seq (.instr _) (.seq (.loop _ _) .skip))) .skip) st =
    some st'
  rw [exec_seq_skip, exec_named]
  obtain ⟨z0, hz0⟩ := hsem.lit_ok p 0 trivial
  obtain ⟨s0, hs0⟩ := hdst
  obtain ⟨s1, hs1⟩ := Store.exists_write_eq_some_of_write_eq_some hs0 z0
  rw [exec_seq_instr_lit I hz0 hs1, exec_seq_skip]
  refine (exists_exec_loop_eq_some_of_forall (I := I)
    (fun _ s => (∃ v, s.store.read p dst.buf dst.idx.eval = some v) ∧
      ∀ q b i, b ≠ dst.buf → s.store.read q b i = st.store.read q b i)
    ⟨⟨z0, Store.read_of_write_eq_some hs1⟩,
      fun q b i hb => Store.read_of_write_eq_some_of_ne hs1 (Or.inl hb)⟩ ?_).imp
    fun _ h => h.1
  rintro i hi s ⟨⟨v, hv⟩, hfr⟩
  simp only [IExp.eval_const] at hi
  have hx := hA ⟨i, hi⟩ ⟨i, hi⟩ ⟨0, two_pos⟩
  obtain ⟨z, hz⟩ := hsem.bin_ok p .add v (pairLayout.put (A ⟨i, hi⟩ ⟨i, hi⟩) ⟨0, two_pos⟩) trivial
    (fun h => nomatch h) trivial
  obtain ⟨s', hs'⟩ := Store.exists_write_eq_some_of_read_eq_some (v := z) hv
  change ∃ st', exec I (.seq (.instr (.bin p .add dst dst
    ⟨X, xo + zidx (.const n) (.var i) (.var i)⟩)) .skip) s = some st' ∧ _
  rw [exec_seq_instr_bin I hv (by
      rw [hfr _ _ _ (Ne.symm hdX)]
      simpa [zidx, show pairLayout.width = 2 from rfl] using hx) hz hs', exec_skip]
  exact ⟨_, rfl, ⟨z, Store.read_of_write_eq_some hs'⟩, fun q b i' hb =>
    (Store.read_of_write_eq_some_of_ne hs' (Or.inl hb)).trans (hfr q b i' hb)⟩

/-- A child block succeeds. -/
private theorem child_exists_node {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (p : P) (n d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) {D : ℕ} (hd : d < D) (H : EighArenas) {sg : Cell ℕ ℕ} (code : ℕ)
    {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} (hH : H.Shaped st.store p n D)
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hsg : ∃ v, st.store.read p sg.buf sg.idx.eval = some v) (hsgM : sg.buf ≠ H.Ma) :
    ∃ st', exec I (eighChildBlock (ι := ι) p (.const k) H.Ma
        (eighBlockOff (.const n) (.const d) (.const lo))
        (eighBlockOff (.const n) (.const d + 1) (.const lo)) sg
        ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
        ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ code).run st = some st' := by
  obtain ⟨-, hMa, -, -, -, hSz, hKd, -, -⟩ := hH
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hkn : k ≤ n := by omega
  have hkk : k * k ≤ n * k := Nat.mul_le_mul_right _ hkn
  have hlok : n * lo + n * k ≤ n * n := by rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ hk
  have hdD : n * n * (d + 1) + n * n ≤ n * n * (D + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  obtain ⟨cv, hcv⟩ := hsg
  have hXY : blockDisjoint (H.Ma, (eighBlockOff (.const n) (.const d + 1) (.const lo)).eval,
      2 * (k * k)) (H.Ma, (eighBlockOff (.const n) (.const d) (.const lo)).eval, 2 * (k * k)) =
      true := by
    simp only [blockDisjoint, eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const,
      IExp.eval_ofNat, IExp.eval_one, bne_self_eq_false, Bool.false_or, Bool.or_eq_true,
          decide_eq_true_eq]
    right
    have e1 : 2 * (n * n) * (d + 1) = 2 * (n * n) * d + 2 * (n * n) := by ring
    have hkk2 : k * k ≤ n * n := Nat.mul_le_mul hkn hkn
    exact decide_eq_true (by linarith)
  have hcY : blockDisjoint (sg.buf, sg.idx.eval, 1)
      (H.Ma, (eighBlockOff (.const n) (.const d + 1) (.const lo)).eval, 2 * (k * k)) = true := by
    simp [blockDisjoint, hsgM]
  have hAm : pairLayout.Holds st.store p H.Ma (eighBlockOff (.const n) (.const d) (.const lo)).eval
      A := by
    simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat]
    exact hA
  have hY : ∃ len, st.store.shape[H.Ma]? = some (p, len) ∧
      (eighBlockOff (.const n) (.const d + 1) (.const lo)).eval + 2 * (k * k) ≤ len :=
    ⟨_, hMa, by
      simp only [eighBlockOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_ofNat,
        IExp.eval_one]
      linarith⟩
  refine ex_bind_node (fun _ => rfl)
    (exists_exec_zhermShift (I := I) p k (st := st) hAm hcv hXY hcY hsem hY) fun σ hσ => ?_
  obtain ⟨-, -, hsh, -⟩ := holds_of_exec_zhermShift (toNat := fun _ => 0)
    (mmR := @fun _ _ _ _ _ => Matrix.of fun _ _ => default)
    (qrR := @fun _ _ X => (Matrix.of fun _ _ => default, X)) (unif := fun x (_ : Unit) => x)
    (normal := fun (_ : Unit) => ((default : K), (default : K))) p k hAm hcv hXY hcY hσ
  obtain ⟨v1, hv1⟩ := hsem.lit_ok p ((IExp.const k).eval : ℚ) trivial
  obtain ⟨s1, hs1⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ.store) v1
    (by rw [hsh]; exact hSz)
    (show (eighSlotOff (.const n) (.const d + 1) (.const lo)).eval < n * (D + 1) + 1 by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const, IExp.eval_one]
      have : n * (d + 1) + n ≤ n * (D + 1) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega)
  rw [hr, exec_seq_instr_litIdx I hv1 hs1]
  obtain ⟨v2, hv2⟩ := hsem.lit_ok p ((IExp.const code).eval : ℚ) trivial
  obtain ⟨s2, hs2⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := s1) v2
    (by rw [Store.shape_of_write_eq_some hs1, hsh]; exact hKd)
    (show (eighSlotOff (.const n) (.const d) (.const lo)).eval < n * D by
      simp only [eighSlotOff, IExp.eval_add, IExp.eval_mul, IExp.eval_const]
      have : n * d + n ≤ n * D := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ hd
      omega)
  exact ⟨_, (exec_seq_instr_litIdx I hv2 hs2).trans (exec_skip I _)⟩

omit [Inhabited K] in
/-- A goal on a state with a new count, by a named state. -/
private theorem ex_cnt_node {X : Stmt P ι ℕ ℕ} {s : St P K C} {c : C}
    (h : ∀ σ : St P K C, σ.store = s.store → ∃ st', exec I X σ = some st') :
    ∃ st', exec I X { s with cnt := c } = some st' := h _ rfl

omit [Inhabited K] in
/-- A guarded block of no iterations, then the rest. -/
private theorem when_zero_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {s : St P K C} (he : (1 - (1 - e)).eval = 0) :
    exec I (eighWhen e b >>= f).run s = exec I (f ()).run s := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl)]
  change (exec I (.seq (.loop _ _) .skip) s).bind _ = _
  rw [exec_seq_skip, exec_loop, he]
  rfl

omit [Inhabited K] in
/-- A last guarded block of no iterations. -/
private theorem when_last_zero_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit} {s : St P K C}
    (he : (1 - (1 - e)).eval = 0) : exec I (eighWhen e b).run s = some s := by
  change exec I (.seq (.loop _ _) .skip) s = _
  rw [exec_seq_skip, exec_loop, he]
  rfl

omit [Inhabited K] in
/-- A guarded block of one iteration, then the rest. -/
private theorem when_one_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit}
    {f : Unit → Builder P ι ℕ ℕ Unit} {s : St P K C} (he : (1 - (1 - e)).eval = 1) :
    exec I (eighWhen e b >>= f).run s = (exec I b.run s).bind (exec I (f ()).run) := by
  rw [exec_run_bind I (b := eighWhen e b) (fun _ => rfl)]
  change (exec I (.seq (.loop _ _) .skip) s).bind _ = _
  rw [exec_seq_skip, exec_loop, he]
  simp [List.range_one]

omit [Inhabited K] in
/-- A last guarded block of one iteration. -/
private theorem when_last_one_ex_node {e : IExp ℕ} {b : Builder P ι ℕ ℕ Unit} {s : St P K C}
    (he : (1 - (1 - e)).eval = 1) : exec I (eighWhen e b).run s = exec I b.run s := by
  change exec I (.seq (.loop _ _) .skip) s = _
  rw [exec_seq_skip, exec_loop, he]
  simp [List.range_one]

-- The branch unfolds its three loops.
set_option maxHeartbeats 4000000 in
/-- The branch of a node step after the index binder succeeds, from a cell that converts to
$k_+ \le k$. -/
private theorem node_branch_exists_core {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2)
    (htn : IsExactToNat dec I.sem) (p : P) (hu : u p < 1) (n d lo k : ℕ) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {Sg c t Pp Pm : ℕ} {st : St P K C}
    {A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)} {σ0 : K} {D : ℕ} (hd : d < D)
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hcS : c ∉ H.handles ++ [Sg, Pp, Pm]) (htS : t ∉ H.handles ++ [Sg, Pp, Pm])
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppv) (hPm : pairLayout.Holds st.store p Pm 0 Pmv)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hsq : st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (ht0 : st.store.read p t 0 = some σ0)
    (ht1 : st.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg σ0))
    {wc : K} {x : ℕ} (ht6 : st.store.read p t 6 = some wc) (hwc : I.sem.toNat p wc = some x)
    (hxk : x ≤ k) :
    ∃ st', exec I (Builder.bindIdx p ⟨t, 6⟩ (.const k) fun kp => do
        eighWhen (1 - (.const k - .var kp))
          (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
            (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 0⟩
            ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
            ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 2)
        eighWhen (1 - .var kp)
          (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
            (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 1⟩
            ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
            ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 3)
        eighWhen (.var kp * (.const k - .var kp))
          (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.var kp) Sg Pp Pm
            H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨t, 0⟩ ⟨t, 1⟩ ⟨c, 4⟩) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  have htM : t ≠ H.Ma := fun h => htS (by simp [EighArenas.handles, h])
  change ∃ st', exec I (.seq (.bindIdx p ⟨t, 6⟩ (.const k) _) .skip) st = some st'
  rw [exec_seq_skip, exec_bindIdx]
  have hts : toNatStep I p ⟨t, 6⟩ st =
      some (x, { st with cnt := st.cnt + I.charge (.toNat p) }) := by
    unfold toNatStep
    rw [show st.store.read p (⟨t, 6⟩ : Cell ℕ ℕ).buf (⟨t, 6⟩ : Cell ℕ ℕ).idx.eval = some wc
      from ht6, Option.bind_some, hwc, Option.map_some]
  rw [hts, Option.bind_some]
  dsimp only
  rw [if_pos (show x ≤ (IExp.const k).eval from hxk)]
  refine ex_cnt_node fun S hS => ?_
  beta_reduce
  have hHS : H.Shaped S.store p n D := by rw [hS]; exact hH
  have hAS : pairLayout.Holds S.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A := by rw [hS]; exact
      hA
  have ev1 : (1 - (1 - (1 - (IExp.const k - IExp.var x)) : IExp ℕ)).eval = 1 - (1 - (1 - (k - x)))
      :=
    rfl
  have ev2 : (1 - (1 - (1 - IExp.var x)) : IExp ℕ).eval = 1 - (1 - (1 - x)) := rfl
  have ev3 : (1 - (1 - (IExp.var x * (IExp.const k - IExp.var x))) : IExp ℕ).eval =
      1 - (1 - x * (k - x)) := rfl
  by_cases h1 : x = k
  · subst h1
    have e1 : (1 - (1 - (1 - (IExp.const x - IExp.var x)) : IExp ℕ)).eval = 1 := by
      rw [ev1]; omega
    have e2 : (1 - (1 - (1 - IExp.var x)) : IExp ℕ).eval = 0 := by rw [ev2]; omega
    have e3 : (1 - (1 - (IExp.var x * (IExp.const x - IExp.var x))) : IExp ℕ).eval = 0 := by
      rw [ev3, Nat.sub_self, Nat.mul_zero]
    rw [when_one_ex_node e1]
    obtain ⟨σc, hc⟩ := child_exists_node (I := I) hsem p n d lo x hk hk2 hd H (sg := ⟨t, 0⟩) 2 hHS
        hAS
      ⟨σ0, by rw [hS]; exact ht0⟩ htM
    rw [hc, Option.bind_some, when_zero_ex_node e2, when_last_zero_ex_node e3]
    exact ⟨_, rfl⟩
  by_cases h0 : x = 0
  · subst h0
    have e1 : (1 - (1 - (1 - (IExp.const k - IExp.var 0)) : IExp ℕ)).eval = 0 := by
      rw [ev1]; omega
    have e2 : (1 - (1 - (1 - IExp.var 0)) : IExp ℕ).eval = 1 := by rw [ev2]
    have e3 : (1 - (1 - (IExp.var 0 * (IExp.const k - IExp.var 0))) : IExp ℕ).eval = 0 := by
      rw [ev3, Nat.zero_mul]
    rw [when_zero_ex_node e1, when_one_ex_node e2]
    obtain ⟨σc, hc⟩ := child_exists_node (I := I) hsem p n d lo k hk hk2 hd H (sg := ⟨t, 1⟩) 3 hHS
        hAS
      ⟨_, by rw [hS]; exact ht1⟩ htM
    rw [hc, Option.bind_some, when_last_zero_ex_node e3]
    exact ⟨_, rfl⟩
  have hpos : 1 ≤ x * (k - x) := Nat.mul_pos (by omega) (by omega)
  have e1 : (1 - (1 - (1 - (IExp.const k - IExp.var x)) : IExp ℕ)).eval = 0 := by
    rw [ev1]; omega
  have e2 : (1 - (1 - (1 - IExp.var x)) : IExp ℕ).eval = 0 := by rw [ev2]; omega
  have e3 : (1 - (1 - (IExp.var x * (IExp.const k - IExp.var x))) : IExp ℕ).eval = 1 := by
    rw [ev3]; omega
  rw [when_zero_ex_node e1, when_zero_ex_node e2, when_last_one_ex_node e3]
  refine exists_exec_eighSplitBlock_ex hmm hqr hsem hlit p hu n d lo k x hk (by omega) (by omega)
    (.var x) rfl H (two := ⟨c, 1⟩) (sg := ⟨t, 0⟩) (nsg := ⟨t, 1⟩) (sq := ⟨c, 4⟩)
    hd hHS hbufs hAS (by rw [hS]; exact hPp) (by rw [hS]; exact hPm)
    (by rw [hS]; exact hSg) (by rw [hS]; exact htwo)
    (by rw [hS]; exact ht0) (by rw [hS]; exact ht1) ?_ ?_
  · simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    exact ⟨hcS, htS, htS, hcS⟩
  · rw [hS]
    exact hsq

/-- The clamp of the split index and the branch of a node step succeed. -/
private theorem node_branch_exists {mm qr : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    (hqr : IsQRKernel I qr pairLayout qrR) {u : P → ℝ} {dec : P → K → ℝ}
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hlit : IsExactIntLit dec I.sem 2)
    (htn : IsExactToNat dec I.sem) (p : P) (hu : u p < 1) (n d lo k : ℕ)
    (hlitk : IsExactIntLit dec I.sem k) (hk : lo + k ≤ n)
    (hk2 : 2 ≤ k) (H : EighArenas) {Sg c t Pp Pm : ℕ} {st : St P K C}
    {A Ppv Pmv : Matrix (Fin k) (Fin k) (K × K)} {σ0 : K} {D : ℕ} (hd : d < D)
    (hH : H.Shaped st.store p n D) (hbufs : (H.handles ++ [Sg, Pp, Pm]).Nodup)
    (hcS : c ∉ H.handles ++ [Sg, Pp, Pm]) (htS : t ∉ H.handles ++ [Sg, Pp, Pm])
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hPp : pairLayout.Holds st.store p Pp 0 Ppv) (hPm : pairLayout.Holds st.store p Pm 0 Pmv)
    (hSg : ∀ w < 4 * (n * n), ∃ v, st.store.read p Sg w = some v)
    (htwo : st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hsq : st.store.read p c 4 = some (I.sem.sqrtHalf p))
    (ht0 : st.store.read p t 0 = some σ0)
    (ht1 : st.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg σ0))
    (ht6 : ∃ v, st.store.read p t 6 = some v) :
    ∃ st', exec I (do
        eighClampBlock p (.const k) ⟨t, 6⟩ ⟨t, 2⟩ ⟨t, 3⟩
        Builder.bindIdx p ⟨t, 6⟩ (.const k) fun kp => do
          eighWhen (1 - (.const k - .var kp))
            (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
              (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 0⟩
              ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
              ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 2)
          eighWhen (1 - .var kp)
            (eighChildBlock p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo))
              (eighBlockOff (.const n) (.const d + 1) (.const lo)) ⟨t, 1⟩
              ⟨H.Sz, eighSlotOff (.const n) (.const d + 1) (.const lo)⟩
              ⟨H.Kd, eighSlotOff (.const n) (.const d) (.const lo)⟩ 3)
          eighWhen (.var kp * (.const k - .var kp))
            (eighSplitBlock p mm qr (.const n) (.const d) (.const lo) (.const k) (.var kp) Sg Pp
              Pm H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 1⟩ ⟨t, 0⟩ ⟨t, 1⟩ ⟨c, 4⟩) :
        Builder P ι ℕ ℕ Unit).run st = some st' := by
  obtain ⟨w6, hw6⟩ := ht6
  obtain ⟨σ, hrun, ⟨wc, hwc, hwcn⟩, hfr, hsh, -⟩ :=
    exec_eighClampBlock_bind (I := I) (hsem.cmp_le p) hlitk htn hw6
  rw [hrun]
  have rd : ∀ q b i, b ≠ t → σ.store.read q b i = st.store.read q b i :=
    fun q b i hb => hfr q b i fun h => absurd h hb
  have rc : ∀ q b i, i < 2 ∨ i = 4 → σ.store.read q b i = st.store.read q b i :=
    fun q b i hi => hfr q b i fun _ => ⟨by omega, by omega, by omega⟩
  have nMa : H.Ma ≠ t := fun h => htS (by simp [EighArenas.handles, h])
  have nSg : Sg ≠ t := fun h => htS (by simp [h])
  have nPp : Pp ≠ t := fun h => htS (by simp [h])
  have nPm : Pm ≠ t := fun h => htS (by simp [h])
  have hH' : H.Shaped σ.store p n D := by unfold EighArenas.Shaped; rw [hsh]; exact hH
  exact node_branch_exists_core hmm hqr hsem hlit htn p hu n d lo k hk hk2 H (st := σ) (A := A) hd
    hH' hbufs hcS htS
    (fun i j t' => (rd _ _ _ nMa).trans (hA i j t'))
    (fun i j t' => (rd _ _ _ nPp).trans (hPp i j t'))
    (fun i j t' => (rd _ _ _ nPm).trans (hPm i j t'))
    (fun w hw => by rw [rd _ _ _ nSg]; exact hSg w hw)
    ((rc _ _ _ (by omega)).trans htwo) ((rc _ _ _ (by omega)).trans hsq)
    ((rc _ _ _ (by omega)).trans ht0) ((rc _ _ _ (by omega)).trans ht1) hwc hwcn
    (min_le_left _ _)

omit [Inhabited K] in
/-- A goal on a state, by a named state. -/
private theorem ex_gen_node {X : Stmt P ι ℕ ℕ} {s : St P K C}
    (h : ∀ σ : St P K C, σ = s → ∃ st', exec I X σ = some st') :
    ∃ st', exec I X s = some st' := h s rfl

-- The set-up runs sixteen steps.
set_option maxHeartbeats 4000000 in
/-- The set-up of a node step, up to the index binder, succeeds; only scratch buffers (at handles
from `s₀`) are written. -/
private theorem node_setup_exists {mm : ι} (hmm : IsMatMulKernel I mm pairLayout mmR)
    {u : P → ℝ} {dec : P → K → ℝ} (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hlit : IsExactIntLit dec I.sem 2) (p : P) (hu : u p < 1) (n ℓ₀ F d lo k : ℕ)
    (hk : lo + k ≤ n) (hk2 : 2 ≤ k) (hℓ : 1 ≤ ℓ₀ + d) (H : EighArenas) {par Su c : ℕ}
    {st : St P K C} {A : Matrix (Fin k) (Fin k) (K × K)} {R : K}
    (s₀ : ℕ) (hlt : ∀ b ∈ H.handles ++ [par, Su, c], b < s₀)
    (t sp W B T Pp Pm : ℕ) (hge : ∀ X ∈ [t, sp, W, B, T, Pp, Pm], s₀ ≤ X)
    (hnd : [t, sp, W, B, T, Pp, Pm].Nodup)
    (ht : st.store.shape[t]? = some (p, 7)) (hsp : st.store.shape[sp]? = some (p, 2))
    (hscr : ∀ X ∈ [W, B, T, Pp, Pm], st.store.shape[X]? = some (p, 2 * (n * n)))
    (hA : pairLayout.Holds st.store p H.Ma (2 * (n * n) * d + 2 * n * lo) A)
    (hR : st.store.read p H.Lv (2 * d) = some R) (hR0 : 0 < dec p R)
    (hpar : ∃ β, st.store.read p par 2 = some β)
    (hSu : ∃ v, st.store.read p Su lo = some v)
    (hc0 : st.store.read p c 0 = I.sem.lit p 1)
    (hc1 : st.store.read p c 1 = I.sem.lit p ((2 : ℕ) : ℚ))
    (hc2 : ∃ v, st.store.read p c 2 = some v) (hc3 : ∃ v, st.store.read p c 3 = some v)
    (rest : Builder P ι ℕ ℕ Unit)
    (hrest : ∀ σ : St P K C, (∀ q b i, b < s₀ → σ.store.read q b i = st.store.read q b i) →
      σ.store.shape = st.store.shape →
      (∃ v, σ.store.read p t 0 = some v ∧
        σ.store.read p t 1 = some ((eighTapeMachine I p mmR qrR).neg v)) →
      (∃ v, σ.store.read p t 6 = some v) →
      (∃ Q : Matrix (Fin k) (Fin k) (K × K), pairLayout.Holds σ.store p Pp 0 Q) →
      (∃ Q : Matrix (Fin k) (Fin k) (K × K), pairLayout.Holds σ.store p Pm 0 Q) →
      ∃ st', exec I rest.run σ = some st') :
    ∃ st', exec I (do
      ins (.bin p .div ⟨t, 0⟩ ⟨H.Lv, 2 * .const d⟩ ⟨c, 1⟩)
      ins (.un p .neg ⟨t, 1⟩ ⟨t, 0⟩)
      ins (.litIdx p ⟨t, 2⟩ (.const ℓ₀ + .const d))
      ins (.bin p .div ⟨t, 3⟩ ⟨H.Lv, 2 * .const d⟩ ⟨t, 2⟩)
      ins (.bin p .mul ⟨t, 4⟩ ⟨t, 3⟩ ⟨Su, .const lo⟩)
      zhermShift p (.const k) H.Ma (eighBlockOff (.const n) (.const d) (.const lo)) ⟨t, 4⟩ W 0
      ins (.copy p ⟨sp, 0⟩ ⟨par, 2⟩)
      ins (.bin p .mul ⟨sp, 1⟩ ⟨c, 1⟩ ⟨H.Lv, 2 * .const d⟩)
      eighSignBlock p mm (.const k) (.const F) W 0 sp 0 B 0
      zhermShift p (.const k) B 0 ⟨c, 3⟩ T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pp 0
      zhermShift p (.const k) B 0 ⟨c, 0⟩ T 0
      zneg p (.const k) (.const k) T 0 T 0
      zhermScale p (.const k) T 0 ⟨c, 1⟩ Pm 0
      ztraceRe p (.const k) Pp 0 ⟨t, 5⟩
      ins (.bin p .add ⟨t, 6⟩ ⟨t, 5⟩ ⟨c, 2⟩)
      rest : Builder P ι ℕ ℕ Unit).run st = some st' := by
  simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
    List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hlt hge hscr
  obtain ⟨lMa, lUa, lQa, lEa, lSz, lKd, lKp, lLv, lpar, lSu, lc⟩ := hlt
  obtain ⟨gt, gsp, gW, gB, gT, gPp, gPm⟩ := hge
  obtain ⟨hWs, hBs, hTs, hPps, hPms⟩ := hscr
  have dtsp : t = sp → False := fun h => by simp [h] at hnd
  have dtW : t = W → False := fun h => by simp [h] at hnd
  have dtB : t = B → False := fun h => by simp [h] at hnd
  have dtT : t = T → False := fun h => by simp [h] at hnd
  have dtPp : t = Pp → False := fun h => by simp [h] at hnd
  have dtPm : t = Pm → False := fun h => by simp [h] at hnd
  have dspW : sp = W → False := fun h => by simp [h] at hnd
  have dspB : sp = B → False := fun h => by simp [h] at hnd
  have dWB : W = B → False := fun h => by simp [h] at hnd
  have dBT : B = T → False := fun h => by simp [h] at hnd
  have dBPp : B = Pp → False := fun h => by simp [h] at hnd
  have dTPp : T = Pp → False := fun h => by simp [h] at hnd
  have dTPm : T = Pm → False := fun h => by simp [h] at hnd
  have dPpPm : Pp = Pm → False := fun h => by simp [h] at hnd
  have bdn : ∀ {b X i i' off len : ℕ}, (b = X → False) →
      blockDisjoint (b, i, i') (X, off, len) = true := fun h => by
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    exact Or.inl (Or.inl h)
  have hR' : st.store.read p H.Lv (2 * IExp.const d : IExp ℕ).eval = some R := by
    simpa using hR
  have hr : ∀ (i : Instr P ℕ ℕ) (b : Builder P ι ℕ ℕ Unit),
      (ins i >>= fun _ => b).run = .seq (.instr i) b.run := fun _ _ => rfl
  have hbo : (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval =
      2 * (n * n) * d + 2 * n * lo := by
    simp [eighBlockOff]
  have hkk : k * k ≤ n * n := Nat.mul_le_mul (by omega) (by omega)
  have hlit1 : IsExactIntLit dec I.sem 1 := fun q m hm => hlit q m (by omega)
  have hflag : I.sem.DecidesFlags p := by
    obtain ⟨z, hz, hdz⟩ := hlit p 0 (Nat.zero_le _)
    obtain ⟨o, ho, hdo⟩ := hlit p 1 (by norm_num)
    simp only [Nat.cast_zero, Nat.cast_one] at hz hdz ho hdo
    refine ⟨z, o, hz, ho, ?_, ?_⟩
    · rw [hsem.cmp_eq p z o, hdz, hdo]
      norm_num
    · rw [hsem.cmp_eq p o o]
      simp
  obtain ⟨z2, hz2, hdz2⟩ := hlit p 2 le_rfl
  have hc1' : st.store.read p c 1 = some z2 := hc1.trans hz2
  have hz20 : dec p z2 ≠ 0 := by rw [hdz2]; norm_num
  obtain ⟨o1, ho1⟩ := hsem.lit_ok p 1 trivial
  have hc0' : st.store.read p c 0 = some o1 := hc0.trans ho1
  obtain ⟨β, hβ⟩ := hpar
  obtain ⟨au, hau⟩ := hSu
  obtain ⟨c2v, hc2v⟩ := hc2
  obtain ⟨c3v, hc3v⟩ := hc3
  -- 1. σ = R / fl(2)
  obtain ⟨v0, hv0⟩ := hsem.bin_ok p .div R z2 trivial (fun _ => hz20) trivial
  obtain ⟨s1, hw1⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := st.store) v0 ht
    (show 0 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨H.Lv, (2 * IExp.const d : IExp ℕ)⟩) (y := ⟨c, 1⟩) (dst :=
      ⟨t, 0⟩) hR' hc1'
    hv0 hw1]
  refine ex_name_node fun σ1 e1 _ => ?_
  subst e1
  have sh1 : σ1.store.shape = st.store.shape := Store.shape_of_write_eq_some hw1
  have f1 : ∀ q b i, (b ≠ t ∨ i ≠ 0) → σ1.store.read q b i = st.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw1 hb
  -- 2. −σ
  obtain ⟨v1, hv1, -⟩ := hsem.neg p v0
  obtain ⟨s2, hw2⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ1.store) v1
    (sh1 ▸ ht) (show 1 < 7 by norm_num)
  rw [hr, exec_seq_instr_un I (x := ⟨t, 0⟩) (dst := ⟨t, 1⟩) (Store.read_of_write_eq_some hw1) hv1
    hw2]
  refine ex_name_node fun σ2 e2 _ => ?_
  subst e2
  have hMneg : (eighTapeMachine I p mmR qrR).neg v0 = v1 := by
    change (I.sem.un p .neg v0).getD default = v1; rw [hv1, Option.getD_some]
  have sh2 : σ2.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw2).trans sh1
  have f2 : ∀ q b i, (b ≠ t ∨ i ≠ 1) → σ2.store.read q b i = σ1.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw2 hb
  -- 3. ℓ
  obtain ⟨v2, hv2⟩ := hsem.lit_ok p ((ℓ₀ + d : ℕ) : ℚ) trivial
  obtain ⟨s3, hw3⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ2.store) v2
    (sh2 ▸ ht) (show 2 < 7 by norm_num)
  rw [hr, exec_seq_instr_litIdx I (dst := ⟨t, 2⟩) (e := .const ℓ₀ + .const d) hv2 hw3]
  refine ex_name_node fun σ3 e3 _ => ?_
  subst e3
  have hv20 : dec p v2 ≠ 0 := by
    obtain ⟨δ, hδ, hd2⟩ := hsem.lit_err p _ v2 hv2
    rw [hd2]
    have := abs_le.mp hδ
    refine mul_ne_zero ?_ (by linarith)
    exact_mod_cast (by omega : ℓ₀ + d ≠ 0)
  have sh3 : σ3.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw3).trans sh2
  have f3 : ∀ q b i, (b ≠ t ∨ i ≠ 2) → σ3.store.read q b i = σ2.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw3 hb
  have L3 : ∀ q b i, b < s₀ → σ3.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f3 _ _ _ (Or.inl (by omega)), f2 _ _ _ (Or.inl (by omega)), f1 _ _ _ (Or.inl (by omega))]
  -- 4. R / ℓ
  obtain ⟨v3, hv3⟩ := hsem.bin_ok p .div R v2 trivial (fun _ => hv20) trivial
  obtain ⟨s4, hw4⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ3.store) v3
    (sh3 ▸ ht) (show 3 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨H.Lv, (2 * IExp.const d : IExp ℕ)⟩) (y := ⟨t, 2⟩) (dst :=
      ⟨t, 3⟩)
    ((L3 _ _ _ lLv).trans hR') (Store.read_of_write_eq_some hw3) hv3 hw4]
  refine ex_name_node fun σ4 e4 _ => ?_
  subst e4
  have sh4 : σ4.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw4).trans sh3
  have f4 : ∀ q b i, (b ≠ t ∨ i ≠ 3) → σ4.store.read q b i = σ3.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw4 hb
  -- 5. the shift c
  obtain ⟨v4, hv4⟩ := hsem.bin_ok p .mul v3 au trivial (fun h => nomatch h) trivial
  obtain ⟨s5, hw5⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ4.store) v4
    (sh4 ▸ ht) (show 4 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨t, 3⟩) (y := ⟨Su, .const lo⟩) (dst := ⟨t, 4⟩)
    (Store.read_of_write_eq_some hw4)
    ((f4 p Su _ (Or.inl (by omega))).trans ((L3 _ _ _ lSu).trans hau)) hv4 hw5]
  refine ex_name_node fun σ5 e5 _ => ?_
  subst e5
  have sh5 : σ5.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw5).trans sh4
  have f5 : ∀ q b i, (b ≠ t ∨ i ≠ 4) → σ5.store.read q b i = σ4.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw5 hb
  have L5 : ∀ q b i, b < s₀ → σ5.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f5 _ _ _ (Or.inl (by omega)), f4 _ _ _ (Or.inl (by omega)), L3 _ _ _ hb]
  have t01_5 : σ5.store.read p t 0 = some v0 ∧ σ5.store.read p t 1 = some v1 := by
    refine ⟨?_, ?_⟩
    · rw [f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)),
        f3 _ _ _ (Or.inr (by omega)), f2 _ _ _ (Or.inr (by omega))]
      exact Store.read_of_write_eq_some hw1
    · rw [f5 _ _ _ (Or.inr (by omega)), f4 _ _ _ (Or.inr (by omega)),
        f3 _ _ _ (Or.inr (by omega))]
      exact Store.read_of_write_eq_some hw2
  -- 6. W = A − cI
  have hA5 : pairLayout.Holds σ5.store p H.Ma
      (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval A := by
    rw [hbo]; exact fun i j t' => (L5 _ _ _ lMa).trans (hA i j t')
  have hc4 : σ5.store.read p (⟨t, 4⟩ : Cell ℕ ℕ).buf (⟨t, 4⟩ : Cell ℕ ℕ).idx.eval = some v4 :=
    Store.read_of_write_eq_some hw5
  have hXY6 : blockDisjoint (W, (0 : IExp ℕ).eval, 2 * (k * k)) (H.Ma,
      (eighBlockOff (IExp.const n) (IExp.const d) (IExp.const lo)).eval, 2 * (k * k)) = true :=
    bdn (fun h => by omega)
  have hcY6 : blockDisjoint ((⟨t, 4⟩ : Cell ℕ ℕ).buf, (⟨t, 4⟩ : Cell ℕ ℕ).idx.eval, 1)
      (W, (0 : IExp ℕ).eval, 2 * (k * k)) = true := bdn dtW
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermShift (I := I) p k (st := σ5) hA5 hc4
    hXY6 hcY6 hsem ⟨_, by rw [sh5]; exact hWs, by simp only [IExp.eval_zero]; omega⟩)
    fun σ6 h6 => ?_
  obtain ⟨hW6, hf6, hsh6, -⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ5) (st' := σ6) hA5 hc4 hXY6 hcY6 h6
  have f6 : ∀ q b i, (b = W → False) → σ6.store.read q b i = σ5.store.read q b i :=
    fun q b i hb => hf6 q b i (bdn hb)
  have sh6 : σ6.store.shape = st.store.shape := hsh6.trans sh5
  -- 7. β
  obtain ⟨s7, hw7⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ6.store) β
    (sh6 ▸ hsp) (show 0 < 2 by norm_num)
  rw [hr, exec_seq_instr_copy I (src := ⟨par, 2⟩) (dst := ⟨sp, 0⟩)
    ((f6 p par _ (fun h => by omega)).trans ((L5 _ _ _ lpar).trans hβ)) hw7]
  refine ex_name_node fun σ7 e7 _ => ?_
  subst e7
  have sh7 : σ7.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw7).trans sh6
  have f7 : ∀ q b i, (b ≠ sp ∨ i ≠ 0) → σ7.store.read q b i = σ6.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw7 hb
  -- 8. fl(2) R
  obtain ⟨vb, hvb⟩ := hsem.bin_ok p .mul z2 R trivial (fun h => nomatch h) trivial
  have hvb0 : dec p vb ≠ 0 := by
    obtain ⟨δ, hδ, hdb⟩ := hsem.bin_err p .mul z2 R vb trivial hvb
    rw [hdb]
    simp only [BinOp.realOp]
    rw [hdz2]
    have := abs_le.mp hδ
    refine mul_ne_zero (mul_ne_zero (by norm_num) hR0.ne') (by linarith)
  obtain ⟨s8, hw8⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ7.store) vb
    (sh7 ▸ hsp) (show 1 < 2 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨c, 1⟩) (y := ⟨H.Lv, (2 * IExp.const d : IExp ℕ)⟩) (dst :=
      ⟨sp, 1⟩)
    ((f7 p c _ (Or.inl (by omega))).trans ((f6 p c _ (fun h => by omega)).trans
      ((L5 _ _ _ lc).trans hc1')))
    ((f7 p H.Lv _ (Or.inl (by omega))).trans ((f6 p H.Lv _ (fun h => by omega)).trans
      ((L5 _ _ _ lLv).trans hR'))) hvb hw8]
  refine ex_name_node fun σ8 e8 _ => ?_
  subst e8
  have sh8 : σ8.store.shape = st.store.shape := (Store.shape_of_write_eq_some hw8).trans sh7
  have f8 : ∀ q b i, (b ≠ sp ∨ i ≠ 1) → σ8.store.read q b i = σ7.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw8 hb
  have L8 : ∀ q b i, b < s₀ → σ8.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f8 _ _ _ (Or.inl (by omega)), f7 _ _ _ (Or.inl (by omega)),
      f6 _ _ _ (fun h => by omega), L5 _ _ _ hb]
  have hW8 : pairLayout.Holds σ8.store p W (0 : IExp ℕ).eval
      ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
        A v4) := fun i j t' => (f8 _ _ _ (Or.inl (fun h => dspW h.symm))).trans
      ((f7 _ _ _ (Or.inl (fun h => dspW h.symm))).trans (hW6 i j t'))
  have hsp0 : σ8.store.read p sp (0 : IExp ℕ).eval = some β :=
    (f8 _ _ _ (Or.inr (by simp))).trans (Store.read_of_write_eq_some hw7)
  have hsp1 : σ8.store.read p sp ((0 : IExp ℕ).eval + 1) = some vb :=
    Store.read_of_write_eq_some hw8
  have hXA9 : blockDisjoint (B, (0 : IExp ℕ).eval, 2 * (k * k)) (W, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dWB h.symm)
  have hXp9 : blockDisjoint (B, (0 : IExp ℕ).eval, 2 * (k * k)) (sp, (0 : IExp ℕ).eval, 2) =
      true := bdn (fun h => dspB h.symm)
  -- 9. the sign
  refine ex_bind_node (fun _ => rfl) (exists_exec_eighSignBlock hmm hsem hlit1 p hu k F
    (by omega) (st := σ8) hW8 hsp0 hsp1 hvb0 hXA9 hXp9
    ⟨_, by rw [sh8]; exact hBs, by simp only [IExp.eval_zero]; omega⟩) fun σ9 h9 => ?_
  obtain ⟨hB9, hf9, hsh9, -⟩ := holds_of_exec_eighSignBlock
    (toNat := fun x => (I.sem.toNat p x).getD 0) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    hmm p hflag k F (st := σ8) (st' := σ9) hW8 hsp0 hsp1 hXA9 hXp9
    ⟨_, by rw [sh8]; exact hBs, by simp only [IExp.eval_zero]; omega⟩ h9
  have f9 : ∀ q b i, (b = B → False) → σ9.store.read q b i = σ8.store.read q b i :=
    fun q b i hb => hf9 q b i (bdn hb)
  have sh9 : σ9.store.shape = st.store.shape := hsh9.trans sh8
  have L9 : ∀ q b i, b < s₀ → σ9.store.read q b i = st.store.read q b i := fun q b i hb => by
    rw [f9 _ _ _ (fun h => by omega), L8 _ _ _ hb]
  -- 10. T = B + I
  have hc3' : σ9.store.read p (⟨c, 3⟩ : Cell ℕ ℕ).buf (⟨c, 3⟩ : Cell ℕ ℕ).idx.eval = some c3v :=
    (L9 _ _ _ lc).trans hc3v
  have hXY10 : blockDisjoint (T, (0 : IExp ℕ).eval, 2 * (k * k)) (B, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dBT h.symm)
  have hcY10 : ∀ i : ℕ, blockDisjoint (c, i, 1) (T, (0 : IExp ℕ).eval, 2 * (k * k)) = true :=
    fun _ => bdn (fun h => by omega)
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermShift (I := I) p k (st := σ9) hB9 hc3'
    hXY10 (hcY10 _) hsem ⟨_, by rw [sh9]; exact hTs, by simp only [IExp.eval_zero]; omega⟩)
    fun σ10 h10 => ?_
  obtain ⟨hT10, hf10, hsh10, -⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ9) (st' := σ10) hB9 hc3' hXY10 (hcY10 _) h10
  have f10 : ∀ q b i, (b = T → False) → σ10.store.read q b i = σ9.store.read q b i :=
    fun q b i hb => hf10 q b i (bdn hb)
  have sh10 : σ10.store.shape = st.store.shape := hsh10.trans sh9
  -- 11. P₊
  have hc1_10 : σ10.store.read p (⟨c, 1⟩ : Cell ℕ ℕ).buf (⟨c, 1⟩ : Cell ℕ ℕ).idx.eval =
      some z2 := (f10 p c _ (fun h => by omega)).trans ((L9 _ _ _ lc).trans hc1')
  have hXY11 : blockDisjoint (Pp, (0 : IExp ℕ).eval, 2 * (k * k)) (T, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dTPp h.symm)
  have hcY11 : blockDisjoint (c, 1, 1) (Pp, (0 : IExp ℕ).eval, 2 * (k * k)) = true :=
    bdn (fun h => by omega)
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermScale (I := I) p k (st := σ10) hT10
    hc1_10 hXY11 hcY11 hsem hz20
    ⟨_, by rw [sh10]; exact hPps, by simp only [IExp.eval_zero]; omega⟩) fun σ11 h11 => ?_
  obtain ⟨hPp11, hf11, hsh11, -⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ10) (st' := σ11) hT10 hc1_10 hXY11 hcY11 h11
  have f11 : ∀ q b i, (b = Pp → False) → σ11.store.read q b i = σ10.store.read q b i :=
    fun q b i hb => hf11 q b i (bdn hb)
  have sh11 : σ11.store.shape = st.store.shape := hsh11.trans sh10
  -- 12. T = B − I
  have hB11 : pairLayout.Holds σ11.store p B (0 : IExp ℕ).eval
      (newtonSchulzSign (I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))) β vb F
        ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
        A v4)) :=
    fun i j t' => (f11 _ _ _ dBPp).trans ((f10 _ _ _ dBT).trans (hB9 i j t'))
  have hc0_11 : σ11.store.read p (⟨c, 0⟩ : Cell ℕ ℕ).buf (⟨c, 0⟩ : Cell ℕ ℕ).idx.eval =
      some o1 := (f11 p c _ (fun h => by omega)).trans
      ((f10 p c _ (fun h => by omega)).trans ((L9 _ _ _ lc).trans hc0'))
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermShift (I := I) p k (st := σ11) hB11
    hc0_11 hXY10 (hcY10 _) hsem
    ⟨_, by rw [sh11]; exact hTs, by simp only [IExp.eval_zero]; omega⟩) fun σ12 h12 => ?_
  obtain ⟨hT12, hf12, hsh12, -⟩ := holds_of_exec_zhermShift
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ11) (st' := σ12) hB11 hc0_11 hXY10 (hcY10 _) h12
  have f12 : ∀ q b i, (b = T → False) → σ12.store.read q b i = σ11.store.read q b i :=
    fun q b i hb => hf12 q b i (bdn hb)
  have sh12 : σ12.store.shape = st.store.shape := hsh12.trans sh11
  -- 13. T = −T
  refine ex_bind_node (fun _ => rfl) (exists_exec_zneg (I := I) p k k (st := σ12) hT12
    (Or.inr ⟨rfl, rfl⟩) hsem
    ⟨_, by rw [sh12]; exact hTs, by simp only [IExp.eval_zero]; omega⟩) fun σ13 h13 => ?_
  obtain ⟨hT13, hf13, hsh13, -⟩ := holds_of_exec_zneg
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k k (st := σ12) (st' := σ13) hT12 (Or.inr ⟨rfl, rfl⟩) h13
  have f13 : ∀ q b i, (b = T → False) → σ13.store.read q b i = σ12.store.read q b i :=
    fun q b i hb => hf13 q b i (bdn hb)
  have sh13 : σ13.store.shape = st.store.shape := hsh13.trans sh12
  -- 14. P₋
  have hc1_13 : σ13.store.read p (⟨c, 1⟩ : Cell ℕ ℕ).buf (⟨c, 1⟩ : Cell ℕ ℕ).idx.eval =
      some z2 := (f13 p c _ (fun h => by omega)).trans ((f12 p c _ (fun h => by omega)).trans
        ((f11 p c _ (fun h => by omega)).trans hc1_10))
  have hXY14 : blockDisjoint (Pm, (0 : IExp ℕ).eval, 2 * (k * k)) (T, (0 : IExp ℕ).eval,
      2 * (k * k)) = true := bdn (fun h => dTPm h.symm)
  have hcY14 : blockDisjoint (c, 1, 1) (Pm, (0 : IExp ℕ).eval, 2 * (k * k)) = true :=
    bdn (fun h => by omega)
  refine ex_bind_node (fun _ => rfl) (exists_exec_zhermScale (I := I) p k (st := σ13) hT13
    hc1_13 hXY14 hcY14 hsem hz20
    ⟨_, by rw [sh13]; exact hPms, by simp only [IExp.eval_zero]; omega⟩) fun σ14 h14 => ?_
  obtain ⟨hPm14, hf14, hsh14, -⟩ := holds_of_exec_zhermScale
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ13) (st' := σ14) hT13 hc1_13 hXY14 hcY14 h14
  have f14 : ∀ q b i, (b = Pm → False) → σ14.store.read q b i = σ13.store.read q b i :=
    fun q b i hb => hf14 q b i (bdn hb)
  have sh14 : σ14.store.shape = st.store.shape := hsh14.trans sh13
  have hPp14 : pairLayout.Holds σ14.store p Pp (0 : IExp ℕ).eval
      ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermScale
        ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
        (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
        (newtonSchulzSign (I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
          (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))) β vb F
          ((I.sem.toFloatMachine p (fun x => (I.sem.toNat p x).getD 0) mmR qrR
          (I.sem.tapeUnif p (I.tape .uniform)) (I.sem.tapeNormal p (I.tape .gaussian))).hermShift
          A v4)) c3v) z2) :=
    fun i j t' => (f14 _ _ _ dPpPm).trans ((f13 _ _ _ (fun h => dTPp h.symm)).trans
      ((f12 _ _ _ (fun h => dTPp h.symm)).trans (hPp11 i j t')))
  -- 15. the trace
  have L14t : ∀ i, σ14.store.read p t i = σ9.store.read p t i := fun i => by
    rw [f14 _ _ _ dtPm, f13 _ _ _ dtT, f12 _ _ _ dtT, f11 _ _ _ dtPp, f10 _ _ _ dtT]
  have L9t : ∀ i, σ9.store.read p t i = σ5.store.read p t i := fun i => by
    rw [f9 _ _ _ dtB, f8 _ _ _ (Or.inl dtsp), f7 _ _ _ (Or.inl dtsp), f6 _ _ _ dtW]
  refine ex_bind_node (fun _ => rfl) (exists_exec_ztraceRe_node (I := I) hsem p k (st := σ14)
    (dst := ⟨t, 5⟩) hPp14 dtPp (Store.exists_write_eq_some_of_getElem?_shape default
      (sh14 ▸ ht) (show 5 < 7 by norm_num))) fun σ15 h15 => ?_
  obtain ⟨htr15, hf15⟩ := read_of_exec_ztraceRe
    (toNat := fun x => (I.sem.toNat p x).getD 0) (mmR := mmR) (qrR := qrR)
    (unif := I.sem.tapeUnif p (I.tape .uniform)) (normal := I.sem.tapeNormal p (I.tape .gaussian))
    p k (st := σ14) (st' := σ15) hPp14 (bdn dtPp) h15
  obtain ⟨hsh15, -⟩ := shape_pos_of_exec_ztraceRe_node p k h15
  have f15 : ∀ q b i, (b ≠ t ∨ i ≠ 5) → σ15.store.read q b i = σ14.store.read q b i := by
    intro q b i hb
    refine hf15 q b i ?_
    simp only [blockDisjoint, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq]
    change (b ≠ t ∨ i + 1 ≤ 5) ∨ 5 + 1 ≤ i
    omega
  have sh15 : σ15.store.shape = st.store.shape := hsh15.trans sh14
  -- 16. t + 1/2
  obtain ⟨v6, hv6⟩ := hsem.bin_ok p .add _ c2v trivial (fun h => nomatch h) trivial
  obtain ⟨s16, hw16⟩ := Store.exists_write_eq_some_of_getElem?_shape (s := σ15.store) v6
    (sh15 ▸ ht) (show 6 < 7 by norm_num)
  rw [hr, exec_seq_instr_bin I (x := ⟨t, 5⟩) (y := ⟨c, 2⟩) (dst := ⟨t, 6⟩) htr15
    ((f15 p c _ (Or.inl (by omega))).trans ((f14 p c _ (fun h => by omega)).trans
      ((f13 p c _ (fun h => by omega)).trans ((f12 p c _ (fun h => by omega)).trans
        ((f11 p c _ (fun h => by omega)).trans ((f10 p c _ (fun h => by omega)).trans
          ((L9 _ _ _ lc).trans hc2v))))))) hv6 hw16]
  refine ex_name_node fun σ16 e16 _ => ?_
  subst e16
  have f16 : ∀ q b i, (b ≠ t ∨ i ≠ 6) → σ16.store.read q b i = σ15.store.read q b i :=
    fun q b i hb => Store.read_of_write_eq_some_of_ne hw16 hb
  refine hrest σ16 (fun q b i hb => ?_) ((Store.shape_of_write_eq_some hw16).trans sh15)
    ⟨v0, ?_, ?_⟩ ⟨v6, Store.read_of_write_eq_some hw16⟩
    ⟨_, fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPp h.symm))).trans (hPp14 i j t'))⟩
    ⟨_, fun i j t' => (f16 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans
      ((f15 _ _ _ (Or.inl (fun h => dtPm h.symm))).trans (hPm14 i j t'))⟩
  · rw [f16 _ _ _ (Or.inl (by omega)), f15 _ _ _ (Or.inl (by omega)),
      f14 _ _ _ (fun h => by omega), f13 _ _ _ (fun h => by omega),
      f12 _ _ _ (fun h => by omega), f11 _ _ _ (fun h => by omega),
      f10 _ _ _ (fun h => by omega), L9 _ _ _ hb]
  · rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), L14t, L9t]
    exact t01_5.1
  · rw [f16 _ _ _ (Or.inr (by omega)), f15 _ _ _ (Or.inr (by omega)), L14t, L9t, hMneg]
    exact t01_5.2

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
      (.const k) par H.Lv Su Sg H.Ma H.Qa H.Sz H.Kd H.Kp ⟨c, 0⟩ ⟨c, 1⟩ ⟨c, 2⟩ ⟨c, 3⟩ ⟨c, 4⟩).run st =
        some st' := by
  have hsz : ∀ {b : ℕ} {x : P × ℕ}, st.store.shape[b]? = some x → b < st.store.size :=
    fun h => by simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp h).1
  obtain ⟨-, hMa, hUa, hQa, hEa, hSz, hKd, hKp, hLv⟩ := id hH
  have hn2 : 0 < 4 * (n * n) := by have : 0 < n := (by omega); positivity
  obtain ⟨_, hSg0⟩ := hSg 0 hn2
  have lSg := Store.lt_size_of_read_eq_some hSg0
  have lpar := Store.lt_size_of_read_eq_some hpar
  obtain ⟨_, hSu'⟩ := hSu
  have lSu := Store.lt_size_of_read_eq_some hSu'
  obtain ⟨o1, ho1⟩ := hsem.lit_ok p 1 trivial
  have lc := Store.lt_size_of_read_eq_some (hc.1.trans ho1)
  obtain ⟨hc0, hc1, ⟨c2v, hc2⟩, ⟨c3v, hc3⟩, hc4⟩ := hc
  have hlt : ∀ b ∈ H.handles ++ [par, Su, Sg, c], b < st.store.size := by
    simp only [EighArenas.handles, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false]
    rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [hsz hMa, hsz hUa, hsz hQa, hsz hEa, hsz hSz, hsz hKd, hsz hKp, hsz hLv, lpar, lSu,
      lSg, lc]
  have hltH : ∀ b ∈ H.handles, b < st.store.size := fun b hb => hlt b (List.mem_append_left _ hb)
  have hlt3 : ∀ b ∈ H.handles ++ [par, Su, c], b < st.store.size := fun b hb => by
    rcases List.mem_append.mp hb with hb | hb
    · exact hltH b hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with rfl | rfl | rfl
      exacts [lpar, lSu, lc]
  have hout : ∀ x, st.store.size ≤ x → x ∉ H.handles ++ [Sg] := fun x hx hm => by
    rcases List.mem_append.mp hm with hm | hm
    · exact absurd (hltH x hm) (by omega)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm; omega
  have hcS3 : c ∉ H.handles ++ [Sg] := fun hm => by
    rcases List.mem_append.mp hm with hm | hm
    · have := (List.nodup_append.mp hbufs).2.2 c hm c (by simp) rfl
      exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      subst hm
      have hb := (List.nodup_append.mp hbufs).2.1
      simp at hb
  change ∃ st', exec I (.seq _ .skip) st = some st'
  rw [exec_seq_skip]
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  refine exists_exec_alloc_of_exists_split ?_
  beta_reduce
  refine ex_gen_node fun σ₇ hσ₇ => ?_
  have hσs := congrArg St.store hσ₇
  simp only at hσs
  simp only [Array.size_push]
  have hrd : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      σ₇.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσs]
    iterate 7 rw [Store.read_push_of_lt (by first | omega | (simp only [Array.size_push]; omega))]
  have hshp : ∀ {b : ℕ}, b < st.store.size → σ₇.store.shape[b]? = st.store.shape[b]? :=
    fun hb => by
      rw [hσs]
      iterate 7 rw [Store.getElem?_shape_push_of_lt _
        (by first | omega | (simp only [Array.size_push]; omega))]
  refine node_setup_exists (qrR := qrR) hmm hsem hlit p hu n ℓ₀ F d lo k hk hk2 hℓ H (par := par)
    (Su := Su)
    (c := c) (A := A) (R := R) (st := σ₇) st.store.size hlt3 _ _ _ _ _ _ _ (by simp <;> omega)
    (by simp [List.nodup_cons] <;> omega)
    (by rw [hσs]; simp [Store.shape, Array.getElem?_push, Array.getElem_push, Nat.add_assoc])
    (by rw [hσs]; simp [Store.shape, Array.getElem?_push, Array.getElem_push, Nat.add_assoc])
    (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro X (rfl | rfl | rfl | rfl | rfl) <;> rw [hσs] <;>
        simp [Store.shape, Array.getElem?_push, Array.getElem_push, Nat.add_assoc])
    (fun i j t => (hrd (hsz hMa)).trans (hA i j t)) ((hrd (hsz hLv)).trans hR) hR0
    ⟨_, (hrd lpar).trans hpar⟩ ⟨_, (hrd lSu).trans hSu'⟩ ((hrd lc).trans hc0)
    ((hrd lc).trans hc1) ⟨_, (hrd lc).trans hc2⟩ ⟨_, (hrd lc).trans hc3⟩ _ ?_
  intro σ hlo hsh ht01 ht6 hPpQ hPmQ
  obtain ⟨v, h0, h1⟩ := ht01
  obtain ⟨Q1, hQ1⟩ := hPpQ
  obtain ⟨Q2, hQ2⟩ := hPmQ
  have hshσ : ∀ {b : ℕ}, b < st.store.size → σ.store.shape[b]? = st.store.shape[b]? :=
    fun hb => by rw [hsh, hshp hb]
  have hHσ : H.Shaped σ.store p n D :=
    ⟨hH.1, by rw [hshσ (hsz hMa)]; exact hMa, by rw [hshσ (hsz hUa)]; exact hUa,
      by rw [hshσ (hsz hQa)]; exact hQa, by rw [hshσ (hsz hEa)]; exact hEa,
      by rw [hshσ (hsz hSz)]; exact hSz, by rw [hshσ (hsz hKd)]; exact hKd,
      by rw [hshσ (hsz hKp)]; exact hKp, by rw [hshσ (hsz hLv)]; exact hLv⟩
  have hrσ : ∀ {q : P} {b i : ℕ}, b < st.store.size →
      σ.store.read q b i = st.store.read q b i := fun hb => (hlo _ _ _ hb).trans (hrd hb)
  obtain ⟨hbS, -⟩ := nodup_scratch_node (Pp := st.store.size + 1 + 1 + 1 + 1 + 1)
    (Pm := st.store.size + 1 + 1 + 1 + 1 + 1 + 1) hbufs hlt (by omega) (by omega) (by omega)
  refine node_branch_exists hmm hqr hsem hlit htn p hu n d lo k
    (fun q m hm => hlitn q m (by omega)) hk hk2 H (st := σ) (A := A) hd hHσ
    hbS ?_ ?_ (fun i j t => (hrσ (hsz hMa)).trans (hA i j t)) hQ1 hQ2
    (fun w hw => (hSg w hw).imp fun _ h => (hrσ lSg).trans h)
    ((hrσ lc).trans hc1) ((hrσ lc).trans hc4) h0 h1 ht6
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hcS3 (List.mem_append_left _ hm)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact hcS3 (by simp [hm])
      · omega
      · omega
  · intro hm
    rcases List.mem_append.mp hm with hm | hm
    · exact hout _ le_rfl (List.mem_append_left _ hm)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with hm | hm | hm
      · exact hout _ le_rfl (by simp [hm])
      · omega
      · omega

end NLAlib
