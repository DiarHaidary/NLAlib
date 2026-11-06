/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exec

/-!
# Index normal form of a statement

The run of a closed statement (`VB := ℕ`, `VI := ℕ`) reads every index expression only through
its value (`NLAlib.Computation.IExp.eval`). `NLAlib.Computation.Stmt.normIdx` replaces every
index expression of a statement, under every binder, by the constant of its value: two statements
with the same index normal form run the same (the result is in the design note
`docs/design/Computation-EighProgram.md`, stage COMPDYN S2a). A run lemma of a kernel stated at
constant sizes then applies at any sizes with those values, such as an index bound by a loop or
an index binder.

## Main definitions

* `NLAlib.Computation.Cell.normIdx`, `NLAlib.Computation.Instr.normIdx`,
  `NLAlib.Computation.Arg.normIdx`, `NLAlib.Computation.Stmt.normIdx`: the index normal forms.
-/

@[expose] public section

namespace NLAlib.Computation

variable {P ι : Type}

/-- A cell with its index replaced by the constant of its value. -/
def Cell.normIdx (c : Cell ℕ ℕ) : Cell ℕ ℕ := ⟨c.buf, .const c.idx.eval⟩

/-- An instruction with its index expressions replaced by the constants of their values. -/
def Instr.normIdx : Instr P ℕ ℕ → Instr P ℕ ℕ
  | .lit p d q => .lit p d.normIdx q
  | .litIdx p d e => .litIdx p d.normIdx (.const e.eval)
  | .bin p b d x y => .bin p b d.normIdx x.normIdx y.normIdx
  | .un p u d x => .un p u d.normIdx x.normIdx
  | .copy p d s => .copy p d.normIdx s.normIdx
  | .draw p dist d => .draw p dist d.normIdx
  | .convert p q d s => .convert p q d.normIdx s.normIdx

/-- A kernel argument with its index expressions replaced by the constants of their values. -/
def Arg.normIdx : Arg ℕ ℕ → Arg ℕ ℕ
  | .buf v => .buf v
  | .idx e => .idx (.const e.eval)
  | .cell c => .cell c.normIdx

/-- **The index normal form** of a statement: every index expression, under every binder,
replaced by the constant of its value. -/
def Stmt.normIdx : Stmt P ι ℕ ℕ → Stmt P ι ℕ ℕ
  | .skip => .skip
  | .seq s t => .seq s.normIdx t.normIdx
  | .instr i => .instr i.normIdx
  | .apply o p d dOff s sOff cols =>
      .apply o p d (.const dOff.eval) s (.const sOff.eval) (.const cols.eval)
  | .rom p d i => .rom p d.normIdx (.const i.eval)
  | .alloc p len body => .alloc p (.const len.eval) fun h => (body h).normIdx
  | .loop n body => .loop (.const n.eval) fun i => (body i).normIdx
  | .whileFuel fuel p c x y body =>
      .whileFuel (.const fuel.eval) p c x.normIdx y.normIdx body.normIdx
  | .ite p c x y t e => .ite p c x.normIdx y.normIdx t.normIdx e.normIdx
  | .named name args body => .named name (args.map Arg.normIdx) body.normIdx
  | .kcall o p dims ins outs =>
      .kcall o p (dims.map fun e => .const e.eval) (ins.map fun x => (x.1, .const x.2.eval))
        (outs.map fun x => (x.1, .const x.2.eval))
  | .bindIdx p x bound body => .bindIdx p x.normIdx (.const bound.eval) fun i => (body i).normIdx

end NLAlib.Computation
