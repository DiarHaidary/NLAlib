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
continuation monad `ContT (Stmt P ι VB VI) Id`. Design: `docs/design/Computation.md` (D1, D11,
D18).

## Main definitions

* `NLAlib.Computation.IExp`, `NLAlib.Computation.Cell`: index arithmetic and cells.
* `NLAlib.Computation.Instr`: the scalar instructions; `NLAlib.Computation.Stmt`: statements.
* `NLAlib.Computation.Builder`: `do` notation, with `NLAlib.Computation.Builder.alloc`,
  `NLAlib.Computation.Builder.forRange`, `NLAlib.Computation.Builder.ifThenElse`.

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

/-- A cell: a buffer handle and an index into the buffer. -/
structure Cell (VB VI : Type) where
  /-- The buffer. -/
  buf : VB
  /-- The index in the buffer. -/
  idx : IExp VI

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
  /-- Run the body while the comparison holds, at most `fuel` times; failing to stop fails. -/
  | whileFuel (fuel : IExp VI) (p : P) (c : CmpOp) (x y : Cell VB VI) (body : Stmt P ι VB VI)
  /-- A conditional. -/
  | ite (p : P) (c : CmpOp) (x y : Cell VB VI) (t e : Stmt P ι VB VI)
  /-- A named kernel: runs as its body; the emitter may print it as a call. -/
  | named (name : String) (args : List (Arg VB VI)) (body : Stmt P ι VB VI)

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
