/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.FirstOrder

/-!
# The bounded index binder and the index normal form

The run of an index binder (`NLAlib.Computation.Stmt.bindIdx`) on a stored value: it converts the
value to a natural number by the semantics (`NLAlib.Computation.ScalarSem.toNat`) and runs its body
at it, one charged conversion, and it fails above its bound or when the conversion fails. And the
index normal form (`NLAlib.Computation.Stmt.normIdx`): a statement runs as its normal form, so a
kernel lemma stated at constant sizes applies at sizes bound by a loop or a binder.

## Main results

* `NLAlib.Computation.exec_bindIdx_of_read`, `NLAlib.Computation.exec_bindIdx_eq_none_of_lt`,
  `NLAlib.Computation.exec_bindIdx_eq_none`: the run of a binder.
* `NLAlib.Computation.exec_normIdx`, `NLAlib.Computation.exec_eq_of_normIdx_eq`: a statement runs
  as its index normal form.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι K C : Type} [DecidableEq P]

/-! ### The run of a binder -/

/-- The run of an index binder on a stored value: if the cell `x` holds $v$ at tag `p`, the
semantics converts $v$ to $k$ and $k$ is at most the bound, the binder runs its body at $k$ after
one charged conversion. No printed source. -/
theorem exec_bindIdx_of_read [AddMonoid C] (I : Interp P ι K C) {p : P} {x : Cell ℕ ℕ}
    {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {v : K} {k : ℕ}
    (hx : st.store.read p x.buf x.idx.eval = some v) (hk : I.sem.toNat p v = some k)
    (hkb : k ≤ bound.eval) :
    exec I (.bindIdx p x bound body) st =
      exec I (body k) { st with cnt := st.cnt + I.charge (.toNat p) } := by
  simp only [exec_bindIdx, toNatStep, hx, hk, Option.bind_some, Option.map_some, if_pos hkb]

/-- An index binder fails above its bound: if the cell `x` holds $v$ and the semantics
converts $v$ to $k$ greater than the bound, the binder fails, whatever its body. No printed
source. -/
theorem exec_bindIdx_eq_none_of_lt [AddMonoid C] (I : Interp P ι K C) {p : P} {x : Cell ℕ ℕ}
    {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {v : K} {k : ℕ}
    (hx : st.store.read p x.buf x.idx.eval = some v) (hk : I.sem.toNat p v = some k)
    (hkb : bound.eval < k) :
    exec I (.bindIdx p x bound body) st = none := by
  simp only [exec_bindIdx, toNatStep, hx, hk, Option.bind_some, Option.map_some,
    if_neg (not_le.mpr hkb)]

/-- An index binder fails when the conversion fails: if the cell `x` holds $v$ and the
semantics does not convert $v$, the binder fails, whatever its body (the default conversion of a
semantics, so no existing semantics runs a binder). No printed source. -/
theorem exec_bindIdx_eq_none [AddMonoid C] (I : Interp P ι K C) {p : P} {x : Cell ℕ ℕ}
    {bound : IExp ℕ} {body : ℕ → Stmt P ι ℕ ℕ} {st : St P K C} {v : K}
    (hx : st.store.read p x.buf x.idx.eval = some v) (hk : I.sem.toNat p v = none) :
    exec I (.bindIdx p x bound body) st = none := by
  simp only [exec_bindIdx, toNatStep, hx, hk, Option.bind_some, Option.map_none, Option.bind_none]

/-! ### The index normal form -/

/-- A statement runs as its index normal form: for every statement at `VB := ℕ`, `VI := ℕ`,
the run of `NLAlib.Computation.Stmt.normIdx s` is the run of `s`, from every state, under every
interpretation. A kernel lemma stated at constant sizes then applies at any index expressions with
the same values: the two statements have the same normal form. No printed source. -/
theorem exec_normIdx [AddMonoid C] (I : Interp P ι K C) :
    ∀ (s : Stmt P ι ℕ ℕ) (st : St P K C), exec I s.normIdx st = exec I s st := by
  intro s
  induction s with
  | skip => intro st; simp only [Stmt.normIdx]
  | seq s t ihs iht =>
    intro st
    have h2 : exec I t.normIdx = exec I t := funext iht
    simp only [Stmt.normIdx, exec_seq, ihs, h2]
  | instr i =>
    intro st
    have hk : Instr.kind (ι := ι) i.normIdx = Instr.kind (ι := ι) i := by cases i <;> rfl
    have hr : ∀ s pos, i.normIdx.run I.sem I.tape s pos = i.run I.sem I.tape s pos := by
      intro s pos; cases i <;> rfl
    simp only [Stmt.normIdx, exec, hk, hr]
  | apply o p dst dOff src sOff cols =>
    intro st
    rfl
  | rom p dst i =>
    intro st
    simp only [Stmt.normIdx, exec, IExp.eval_const, Cell.normIdx]
  | alloc p len body ih =>
    intro st
    simp only [Stmt.normIdx, exec_alloc, IExp.eval_const, ih]
  | loop n body ih =>
    intro st
    have hb : (fun (st : St P K C) (i : ℕ) => exec I (body i).normIdx st) =
        (fun (st : St P K C) (i : ℕ) => exec I (body i) st) :=
      funext fun st => funext fun i => ih i st
    simp only [Stmt.normIdx, exec_loop, IExp.eval_const]
    rw [hb]
  | whileFuel fuel p c x y body ih =>
    intro st
    have hb : exec I body.normIdx = exec I body := funext ih
    have hc : ∀ st, cmpStep I p c x.normIdx y.normIdx st = cmpStep I p c x y st :=
      fun st => rfl
    simp only [Stmt.normIdx, exec, IExp.eval_const, hc, hb]
  | ite p c x y t e iht ihe =>
    intro st
    have ht : exec I t.normIdx = exec I t := funext iht
    have he : exec I e.normIdx = exec I e := funext ihe
    have hc : ∀ st, cmpStep I p c x.normIdx y.normIdx st = cmpStep I p c x y st :=
      fun st => rfl
    simp only [Stmt.normIdx, exec_ite, hc, ht, he]
  | named name args body ih =>
    intro st
    simp only [Stmt.normIdx, exec_named]
    exact ih st
  | kcall o p dims ins outs =>
    intro st
    simp only [Stmt.normIdx, exec, List.map_map, Function.comp_def, IExp.eval_const]
  | bindIdx p x bound body ih =>
    intro st
    have hc : toNatStep I p x.normIdx st = toNatStep I p x st := rfl
    simp only [Stmt.normIdx, exec_bindIdx, IExp.eval_const, hc, ih]

/-- Statements with the same index normal form run the same. No printed source. -/
theorem exec_eq_of_normIdx_eq [AddMonoid C] (I : Interp P ι K C) {s s' : Stmt P ι ℕ ℕ}
    (h : s.normIdx = s'.normIdx) (st : St P K C) : exec I s st = exec I s' st := by
  rw [← exec_normIdx I s st, h, exec_normIdx I s' st]

end NLAlib.Computation
