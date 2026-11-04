/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import NLAlib.Computation.Syntax

/-!
# Compiling the builder into first-order programs

A program is written with the builder, a statement generic in its two variable sorts, and a
result is about a first-order tree (`NLAlib.Computation.FStmt`). The compiler
`NLAlib.Computation.Stmt.compile` reads a statement at `VB := ℕ`, `VI := ℕ` with handles and
index variables as de Bruijn levels: a binder is applied once, to the next level, and the body is
compiled in the larger scope; a variable out of scope (a handle forged from a number) makes the
compilation fail. A program family is compiled once, at symbolic sizes
(`NLAlib.Computation.ProgFamily.compile`, in `NLAlib/Computation/Model.lean`), so nothing the
builder computes can depend on the value of a size.

The compiler is not trusted: the theorems are about the compiled tree. What a library program
needs is its own instantiation equation, `c.toStmt N n = F.inst N n` by `rfl`, where
`NLAlib.Computation.FStmt.toStmt` is the converse map, which instantiates a first-order statement
as a statement of the current syntax; the bridge (`NLAlib/Computation/FirstOrder.lean`) proves
that the run of a first-order program is the run of its instantiation. Design:
`docs/design/Computation.md`, "First-order programs and target statements" (F3, F5).

## Main definitions

* `NLAlib.Computation.IExp.scope?`, `NLAlib.Computation.Cell.scope?`,
  `NLAlib.Computation.Instr.scope?`, `NLAlib.Computation.Arg.scope?`: scoping of the leaves.
* `NLAlib.Computation.Stmt.compile`: the compiler.
* `NLAlib.Computation.FStmt.toStmt`, `NLAlib.Computation.Prog.toStmt`: instantiation.

## Main results

None: the compiler is untrusted infrastructure, and each library program has its own
instantiation equation, by `rfl`, next to it.
-/

@[expose] public section

namespace NLAlib.Computation

/-! ### Scoping the leaves -/

/-- An index expression over `ℕ` read with its variables as levels below `ni`; `none` if a
variable is out of scope. -/
def IExp.scope? (ni : ℕ) : IExp ℕ → Option (IExp (Fin ni))
  | .var v => if h : v < ni then some (.var ⟨v, h⟩) else none
  | .const n => some (.const n)
  | .add a b => return .add (← a.scope? ni) (← b.scope? ni)
  | .sub a b => return .sub (← a.scope? ni) (← b.scope? ni)
  | .mul a b => return .mul (← a.scope? ni) (← b.scope? ni)
  | .mod a b => return .mod (← a.scope? ni) (← b.scope? ni)

/-- A handle read as a level below `nb`; `none` if it is out of scope. -/
def finScope? (nb v : ℕ) : Option (Fin nb) := if h : v < nb then some ⟨v, h⟩ else none

/-- A cell read with its handle below `nb` and its index variables below `ni`. -/
def Cell.scope? (nb ni : ℕ) (c : Cell ℕ ℕ) : Option (Cell (Fin nb) (Fin ni)) :=
  return ⟨← finScope? nb c.buf, ← c.idx.scope? ni⟩

/-- An instruction read with its handles below `nb` and its index variables below `ni`. -/
def Instr.scope? {P : Type} (nb ni : ℕ) : Instr P ℕ ℕ → Option (Instr P (Fin nb) (Fin ni))
  | .lit p d q => return .lit p (← d.scope? nb ni) q
  | .litIdx p d e => return .litIdx p (← d.scope? nb ni) (← e.scope? ni)
  | .bin p b d x y => return .bin p b (← d.scope? nb ni) (← x.scope? nb ni) (← y.scope? nb ni)
  | .un p u d x => return .un p u (← d.scope? nb ni) (← x.scope? nb ni)
  | .copy p d s => return .copy p (← d.scope? nb ni) (← s.scope? nb ni)
  | .draw p dist d => return .draw p dist (← d.scope? nb ni)
  | .convert p q d s => return .convert p q (← d.scope? nb ni) (← s.scope? nb ni)

/-- A kernel argument read with its handles below `nb` and its index variables below `ni`. -/
def Arg.scope? (nb ni : ℕ) : Arg ℕ ℕ → Option (Arg (Fin nb) (Fin ni))
  | .buf v => return .buf (← finScope? nb v)
  | .idx e => return .idx (← e.scope? ni)
  | .cell c => return .cell (← c.scope? nb ni)

/-! ### The compiler -/

/-- **The compiler**: a statement at `VB := ℕ`, `VI := ℕ`, read with handles and index variables
as de Bruijn levels, to a first-order statement with `nb` handles and `ni` index variables in
scope; `none` if a variable is out of scope. A binder is applied to the next level, once, and its
body compiled in the larger scope. -/
def Stmt.compile {P ι : Type} : Stmt P ι ℕ ℕ → (nb ni : ℕ) → Option (FStmt P ι nb ni)
  | .skip, _, _ => some .skip
  | .seq s t, nb, ni => return .seq (← s.compile nb ni) (← t.compile nb ni)
  | .instr i, nb, ni => return .instr (← i.scope? nb ni)
  | .apply o p d dOff s sOff cols, nb, ni =>
      return .apply o p (← finScope? nb d) (← dOff.scope? ni) (← finScope? nb s)
        (← sOff.scope? ni) (← cols.scope? ni)
  | .rom p d i, nb, ni => return .rom p (← d.scope? nb ni) (← i.scope? ni)
  | .alloc p len body, nb, ni =>
      return .alloc p (← len.scope? ni) (← (body nb).compile (nb + 1) ni)
  | .loop n body, nb, ni => return .loop (← n.scope? ni) (← (body ni).compile nb (ni + 1))
  | .whileFuel fuel p c x y body, nb, ni =>
      return .whileFuel (← fuel.scope? ni) p c (← x.scope? nb ni) (← y.scope? nb ni)
        (← body.compile nb ni)
  | .ite p c x y t e, nb, ni =>
      return .ite p c (← x.scope? nb ni) (← y.scope? nb ni) (← t.compile nb ni)
        (← e.compile nb ni)
  | .named name args body, nb, ni =>
      return .named name (← args.mapM (Arg.scope? nb ni)) (← body.compile nb ni)

/-! ### Instantiation -/

/-- A first-order statement as a statement of the current syntax at `VB := ℕ`, `VI := ℕ`:
handles renamed by `ρB`, index variables replaced by the index expressions `σ`; the handle bound
by `alloc` is the one the run supplies, and a loop variable is `.var i`. -/
def FStmt.toStmt {P ι : Type} : {nb ni : ℕ} → FStmt P ι nb ni → (Fin nb → ℕ) →
    (Fin ni → IExp ℕ) → Stmt P ι ℕ ℕ
  | _, _, .skip, _, _ => .skip
  | _, _, .seq s t, ρB, σ => .seq (s.toStmt ρB σ) (t.toStmt ρB σ)
  | _, _, .instr i, ρB, σ => .instr (i.subst ρB σ)
  | _, _, .apply o p d dOff s sOff cols, ρB, σ =>
      .apply o p (ρB d) (dOff.subst σ) (ρB s) (sOff.subst σ) (cols.subst σ)
  | _, _, .rom p d i, ρB, σ => .rom p (d.subst ρB σ) (i.subst σ)
  | _, _, .alloc p len body, ρB, σ =>
      .alloc p (len.subst σ) fun h => body.toStmt (Fin.snoc (α := fun _ => ℕ) ρB h) σ
  | _, _, .loop n body, ρB, σ =>
      .loop (n.subst σ) fun i => body.toStmt ρB (Fin.snoc (α := fun _ => IExp ℕ) σ (.var i))
  | _, _, .whileFuel fuel p c x y body, ρB, σ =>
      .whileFuel (fuel.subst σ) p c (x.subst ρB σ) (y.subst ρB σ) (body.toStmt ρB σ)
  | _, _, .ite p c x y t e, ρB, σ =>
      .ite p c (x.subst ρB σ) (y.subst ρB σ) (t.toStmt ρB σ) (e.toStmt ρB σ)
  | _, _, .named name args body, ρB, σ =>
      .named name (args.map (Arg.subst ρB σ)) (body.toStmt ρB σ)

/-- The statement a program instantiates to at the sizes $N$ and $n$, as
`NLAlib.Computation.ProgFamily.inst` builds it: declared buffer $j$ at handle $j$, the sizes
constants. -/
def Prog.toStmt {P ι : Type} {r b : ℕ} (prog : Prog P ι r b) (N : ℕ) (n : Fin r → ℕ) :
    Stmt P ι ℕ ℕ :=
  FStmt.toStmt prog (fun j => (j : ℕ)) (Fin.cons (.const N) fun i => .const (n i))

end NLAlib.Computation
