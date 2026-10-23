/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Control.Monad.Cont
public import Mathlib.Data.Rat.Defs

/-!
# Programs over memory buffers: the syntax

Algorithms are small imperative programs that work on buffers as BLAS code does: they allocate
scoped buffers, overwrite cells in place, call kernels, draw random numbers from a tape, and
multiply blocks of vectors by a matrix through an oracle. A program is a value of
`NLAlib.Computation.Stmt P ι VB VI`, a two-sorted parametric higher-order abstract syntax: `P` is
the type of precision tags, `ι` the type of oracle names, `VB` the sort of buffer handles (bound
by `alloc`) and `VI` the sort of index variables (bound by `loop`). A program is generic in `VB`
and `VI`, so a handle cannot be forged from a number or computed from an index: both are type
errors. The run (`NLAlib.Computation.exec`) instantiates both sorts as `ℕ`; the NumPy emitter of
the tools library instantiates them as `String`.

Programs are written in `do` notation through `NLAlib.Computation.Builder`, which is Mathlib's
continuation monad `ContT (Stmt P ι VB VI) Id`.

A result is about a **first-order program** (`NLAlib.Computation.Prog P ι r b`): one finite
syntax tree for all sizes, a `NLAlib.Computation.FStmt P ι nb ni` with `nb` handles and `ni`
index variables in scope, numbered by de Bruijn level, so that a handle or index out of scope is
a type error. The sizes are its free index variables and its declared buffers its free handles;
its literals are fixed in the tree, and it contains no Lean function. The builder is surface
syntax, compiled once into such a tree (`NLAlib/Computation/Compile.lean`). Design:
`docs/design/Computation.md` (D1, D11, D18, and "First-order programs and target statements",
F2).

## Main definitions

* `NLAlib.Computation.IExp`, `NLAlib.Computation.Cell`: index arithmetic and cells.
* `NLAlib.Computation.Instr`: the scalar instructions; `NLAlib.Computation.Stmt`: statements.
* `NLAlib.Computation.Builder`: `do` notation, with `NLAlib.Computation.Builder.alloc`,
  `NLAlib.Computation.Builder.forRange`, `NLAlib.Computation.Builder.ifThenElse`.
* `NLAlib.Computation.FStmt`, `NLAlib.Computation.Prog`: first-order statements and programs,
  scoped by their type, with handles and index variables as de Bruijn levels.
* `NLAlib.Computation.IExp.subst`, `NLAlib.Computation.IExp.evalIn`,
  `NLAlib.Computation.Cell.subst`, `NLAlib.Computation.Instr.subst`,
  `NLAlib.Computation.Arg.subst`: the structural maps the run of a first-order statement uses.

## Main results

* `NLAlib.Computation.Builder.run_stmt`, `NLAlib.Computation.Builder.run_pure`: how the builder
  unfolds into statements.
-/

@[expose] public section

namespace NLAlib

namespace Computation

/-! ### Index expressions and cells -/

/-- Index arithmetic over the index variables `VI`: constants, variables, `+`, truncated `-`,
`*` and `%`. Sizes, offsets and loop bounds of a program are index expressions, so that a program
is generic in its sizes. -/
inductive IExp (VI : Type) where
  /-- An index variable, bound by a loop. -/
  | var (v : VI)
  /-- A constant. -/
  | const (n : ℕ)
  /-- Addition. -/
  | add (a b : IExp VI)
  /-- Truncated subtraction. -/
  | sub (a b : IExp VI)
  /-- Multiplication. -/
  | mul (a b : IExp VI)
  /-- Remainder. -/
  | mod (a b : IExp VI)

/-- Numerals are constants. -/
instance {VI : Type} {n : ℕ} : OfNat (IExp VI) n := ⟨.const n⟩
/-- `+` on index expressions. -/
instance {VI : Type} : Add (IExp VI) := ⟨.add⟩
/-- `-` on index expressions (truncated). -/
instance {VI : Type} : Sub (IExp VI) := ⟨.sub⟩
/-- `*` on index expressions. -/
instance {VI : Type} : Mul (IExp VI) := ⟨.mul⟩
/-- `%` on index expressions. -/
instance {VI : Type} : Mod (IExp VI) := ⟨.mod⟩

/-- Substitute index expressions for the variables of an index expression. -/
def IExp.subst {α β : Type} (σ : α → IExp β) : IExp α → IExp β
  | .var v => σ v
  | .const n => .const n
  | .add a b => .add (a.subst σ) (b.subst σ)
  | .sub a b => .sub (a.subst σ) (b.subst σ)
  | .mul a b => .mul (a.subst σ) (b.subst σ)
  | .mod a b => .mod (a.subst σ) (b.subst σ)

/-- The value of an index expression in an environment `ρ` of its variables. -/
def IExp.evalIn {α : Type} (ρ : α → ℕ) : IExp α → ℕ
  | .var v => ρ v
  | .const n => n
  | .add a b => a.evalIn ρ + b.evalIn ρ
  | .sub a b => a.evalIn ρ - b.evalIn ρ
  | .mul a b => a.evalIn ρ * b.evalIn ρ
  | .mod a b => a.evalIn ρ % b.evalIn ρ

/-- A cell: a buffer handle and an index into the buffer. -/
structure Cell (VB VI : Type) where
  /-- The buffer. -/
  buf : VB
  /-- The index in the buffer. -/
  idx : IExp VI

/-- A cell under a renaming `f` of handles and a substitution `σ` of index expressions. -/
def Cell.subst {VB VB' VI VI' : Type} (f : VB → VB') (σ : VI → IExp VI') (c : Cell VB VI) :
    Cell VB' VI' :=
  ⟨f c.buf, c.idx.subst σ⟩

/-- Binary operations: field arithmetic, and integer and bitwise operations on words. -/
inductive BinOp where
  /-- Addition. -/
  | add
  /-- Subtraction. -/
  | sub
  /-- Multiplication. -/
  | mul
  /-- Division. -/
  | div
  /-- Shift left. -/
  | shl
  /-- Shift right. -/
  | shr
  /-- Bitwise and. -/
  | band
  /-- Bitwise or. -/
  | bor
  /-- Bitwise exclusive or. -/
  | bxor

/-- Unary operations. -/
inductive UnOp where
  /-- Negation. -/
  | neg
  /-- Complex conjugation. -/
  | conj
  /-- Real part. -/
  | re
  /-- Square root. -/
  | sqrt
  /-- Bitwise complement. -/
  | bnot

/-- Comparisons, the conditions of `ite` and `whileFuel`. -/
inductive CmpOp where
  /-- Equality. -/
  | eq
  /-- Strict order. -/
  | lt
  /-- Order. -/
  | le

/-- The distributions a program draws from; each has its own tape. -/
inductive Dist where
  /-- Standard Gaussian. -/
  | gaussian
  /-- Rademacher (random signs). -/
  | rademacher
  deriving DecidableEq

/-- The arguments of a named kernel call, recorded for the emitter. -/
inductive Arg (VB VI : Type) where
  /-- A buffer. -/
  | buf (v : VB)
  /-- An index expression. -/
  | idx (e : IExp VI)
  /-- A cell. -/
  | cell (c : Cell VB VI)

/-- A kernel argument under a renaming `f` of handles and a substitution `σ` of index
expressions. -/
def Arg.subst {VB VB' VI VI' : Type} (f : VB → VB') (σ : VI → IExp VI') :
    Arg VB VI → Arg VB' VI'
  | .buf v => .buf (f v)
  | .idx e => .idx (e.subst σ)
  | .cell c => .cell (c.subst f σ)

/-! ### Instructions and statements -/

/-- Scalar instructions: each reads cells (or the tape) at tag `p` and writes one destination
cell. -/
inductive Instr (P VB VI : Type) where
  /-- Write the rational literal `q`. -/
  | lit (p : P) (dst : Cell VB VI) (q : ℚ)
  /-- Write the value of an index expression, as a literal. -/
  | litIdx (p : P) (dst : Cell VB VI) (e : IExp VI)
  /-- A binary operation. -/
  | bin (p : P) (b : BinOp) (dst x y : Cell VB VI)
  /-- A unary operation. -/
  | un (p : P) (u : UnOp) (dst x : Cell VB VI)
  /-- A copy. -/
  | copy (p : P) (dst src : Cell VB VI)
  /-- Write the next value of the tape of `d`. -/
  | draw (p : P) (d : Dist) (dst : Cell VB VI)
  /-- Read a cell at tag `p`, write a cell at tag `q`: a change of format, or reinterpretation
  of a stored word at another tag. -/
  | convert (p q : P) (dst src : Cell VB VI)

/-- An instruction under a renaming `f` of handles and a substitution `σ` of index
expressions. -/
def Instr.subst {P VB VB' VI VI' : Type} (f : VB → VB') (σ : VI → IExp VI') :
    Instr P VB VI → Instr P VB' VI'
  | .lit p d q => .lit p (d.subst f σ) q
  | .litIdx p d e => .litIdx p (d.subst f σ) (e.subst σ)
  | .bin p b d x y => .bin p b (d.subst f σ) (x.subst f σ) (y.subst f σ)
  | .un p u d x => .un p u (d.subst f σ) (x.subst f σ)
  | .copy p d s => .copy p (d.subst f σ) (s.subst f σ)
  | .draw p dist d => .draw p dist (d.subst f σ)
  | .convert p q d s => .convert p q (d.subst f σ) (s.subst f σ)

/-- Statements over tags `P`, oracle names `ι`, handles `VB` and index variables `VI`.
`alloc` binds a handle to a fresh scoped buffer, `loop` binds an index. -/
inductive Stmt (P ι VB VI : Type) where
  /-- Do nothing. -/
  | skip
  /-- Sequence. -/
  | seq (s t : Stmt P ι VB VI)
  /-- A scalar instruction. -/
  | instr (i : Instr P VB VI)
  /-- An oracle call: the block of `cols` columns at `src[sOff]`, multiplied by the matrix of
  `o`, is written at `dst[dOff]`. -/
  | apply (o : ι) (p : P) (dst : VB) (dOff : IExp VI) (src : VB) (sOff : IExp VI)
      (cols : IExp VI)
  /-- Read entry `i` of the read-only data into `dst`. -/
  | rom (p : P) (dst : Cell VB VI) (i : IExp VI)
  /-- Allocate a fresh buffer of `len` cells at tag `p` for the body; it is freed at the end. -/
  | alloc (p : P) (len : IExp VI) (body : VB → Stmt P ι VB VI)
  /-- Run the body for each index below `n`, in order. -/
  | loop (n : IExp VI) (body : VI → Stmt P ι VB VI)
  /-- Run the body while the comparison holds. The comparison is tested at most `fuel` times,
  and the loop fails if every test it makes holds: a successful run executes the body at most
  `fuel - 1` times, and the loop fails if the body runs `fuel` times. -/
  | whileFuel (fuel : IExp VI) (p : P) (c : CmpOp) (x y : Cell VB VI) (body : Stmt P ι VB VI)
  /-- A conditional. -/
  | ite (p : P) (c : CmpOp) (x y : Cell VB VI) (t e : Stmt P ι VB VI)
  /-- A named kernel: runs as its body; the emitter may print it as a call. -/
  | named (name : String) (args : List (Arg VB VI)) (body : Stmt P ι VB VI)

/-! ### First-order statements and programs -/

/-- **First-order statements** over tags `P` and oracle names `ι`, with `nb` handles and `ni`
index variables in scope, numbered by de Bruijn level: `alloc` binds handle `nb`
(`Fin.last nb`) in its body and `loop` binds index variable `ni`, and the variables around a
binder keep their numbers. A handle or index variable out of scope is a type error. The
constructors are those of `NLAlib.Computation.Stmt`, with the binders made first-order. -/
inductive FStmt (P ι : Type) : ℕ → ℕ → Type where
  /-- Do nothing. -/
  | skip {nb ni : ℕ} : FStmt P ι nb ni
  /-- Sequence. -/
  | seq {nb ni : ℕ} (s t : FStmt P ι nb ni) : FStmt P ι nb ni
  /-- A scalar instruction. -/
  | instr {nb ni : ℕ} (i : Instr P (Fin nb) (Fin ni)) : FStmt P ι nb ni
  /-- An oracle call: the block of `cols` columns at `src[sOff]`, multiplied by the matrix of
  `o`, is written at `dst[dOff]`. -/
  | apply {nb ni : ℕ} (o : ι) (p : P) (dst : Fin nb) (dOff : IExp (Fin ni)) (src : Fin nb)
      (sOff cols : IExp (Fin ni)) : FStmt P ι nb ni
  /-- Read entry `i` of the read-only data into `dst`. -/
  | rom {nb ni : ℕ} (p : P) (dst : Cell (Fin nb) (Fin ni)) (i : IExp (Fin ni)) : FStmt P ι nb ni
  /-- Allocate a fresh buffer of `len` cells at tag `p`, handle `nb` in the body; it is freed at
  the end. -/
  | alloc {nb ni : ℕ} (p : P) (len : IExp (Fin ni)) (body : FStmt P ι (nb + 1) ni) :
      FStmt P ι nb ni
  /-- Run the body for each index below `n`, in order, the index as variable `ni`. -/
  | loop {nb ni : ℕ} (n : IExp (Fin ni)) (body : FStmt P ι nb (ni + 1)) : FStmt P ι nb ni
  /-- Run the body while the comparison holds. The comparison is tested at most `fuel` times,
  and the loop fails if every test it makes holds: a successful run executes the body at most
  `fuel - 1` times, and the loop fails if the body runs `fuel` times. -/
  | whileFuel {nb ni : ℕ} (fuel : IExp (Fin ni)) (p : P) (c : CmpOp)
      (x y : Cell (Fin nb) (Fin ni)) (body : FStmt P ι nb ni) : FStmt P ι nb ni
  /-- A conditional. -/
  | ite {nb ni : ℕ} (p : P) (c : CmpOp) (x y : Cell (Fin nb) (Fin ni)) (t e : FStmt P ι nb ni) :
      FStmt P ι nb ni
  /-- A named kernel: a label for the emitter; runs as its body. -/
  | named {nb ni : ℕ} (name : String) (args : List (Arg (Fin nb) (Fin ni)))
      (body : FStmt P ι nb ni) : FStmt P ι nb ni

/-- **A program**: a first-order statement with `b` declared buffers (handles `0`, …, `b - 1`),
the oracle dimension `N` (index variable `0`) and `r` further sizes (index variables `1`, …,
`r`) free. One finite tree for all sizes. -/
abbrev Prog (P ι : Type) (r b : ℕ) : Type := FStmt P ι b (r + 1)

/-! ### `do` notation -/

/-- Programs in `do` notation: Mathlib's continuation monad over statements,
`(β → Stmt P ι VB VI) → Stmt P ι VB VI`. -/
abbrev Builder (P ι VB VI β : Type) : Type := ContT (Stmt P ι VB VI) Id β

namespace Builder

variable {P ι VB VI : Type}

/-- The statement of a builder, ended by `skip`. -/
def run (b : Builder P ι VB VI Unit) : Stmt P ι VB VI := ContT.run b fun _ => .skip

/-- A statement, then the rest. -/
def stmt (s : Stmt P ι VB VI) : Builder P ι VB VI Unit := .mk fun k => .seq s (k ())

/-- A scalar instruction, then the rest. -/
def ins (i : Instr P VB VI) : Builder P ι VB VI Unit := stmt (.instr i)

/-- A fresh scoped buffer of `len` cells at tag `p`, live for the rest of the enclosing block. -/
def alloc (p : P) (len : IExp VI) : Builder P ι VB VI VB := .mk fun k => .alloc p len k

/-- A loop over the indices below `n`. -/
def forRange (n : IExp VI) (body : VI → Builder P ι VB VI Unit) : Builder P ι VB VI Unit :=
  .mk fun k => .seq (.loop n fun i => (body i).run) (k ())

/-- A conditional on a comparison of two cells. -/
def ifThenElse (p : P) (c : CmpOp) (x y : Cell VB VI) (t e : Builder P ι VB VI Unit) :
    Builder P ι VB VI Unit :=
  .mk fun k => .seq (.ite p c x y t.run e.run) (k ())

/-- A named kernel. -/
def named (name : String) (args : List (Arg VB VI)) (body : Builder P ι VB VI Unit) :
    Builder P ι VB VI Unit :=
  .mk fun k => .seq (.named name args body.run) (k ())

/-- A block: the buffers it allocates are freed at its end. -/
def scope (b : Builder P ι VB VI Unit) : Builder P ι VB VI Unit := .mk fun k => .seq b.run (k ())

/-- `stmt s` followed by `b` runs as `s` then `b`. -/
theorem run_stmt (s : Stmt P ι VB VI) (b : Builder P ι VB VI Unit) :
    (stmt s >>= fun _ => b).run = .seq s b.run := rfl

/-- `pure ()` runs as `skip`. -/
theorem run_pure : (pure () : Builder P ι VB VI Unit).run = .skip := rfl

end Builder

end Computation

end NLAlib
