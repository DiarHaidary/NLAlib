/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Estimation.Trace.HutchPlusPlusProgram

/-!
# Printing programs as NumPy

A program is data with Lean binders, so the emitter is one more structural function: it
instantiates both variable sorts as `String`, lets `alloc` and `loop` invent names, and prints
index expressions as Python arithmetic. Emission is size-generic: sizes are parameters of the
emitted function. `named` kernels are printed as calls into a short NumPy prelude
(`NLAlibTools.numpyPrelude`), or inlined as scalar loops. Fresh buffers are
`np.full(len, np.nan)`, so a read before a write shows as `nan`. The emitted code is an
unverified translation, for differential testing (`docs/design/Computation.md` §8).
-/

-- A tools file: `#eval` and `#guard` are its point.
set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

/-- An index expression as Python arithmetic (truncated subtraction as `max(·, 0)`). -/
def emitIExp : IExp String → String
  | .var v => v
  | .const n => toString n
  | .add a b => s!"({emitIExp a} + {emitIExp b})"
  | .sub a b => s!"max({emitIExp a} - {emitIExp b}, 0)"
  | .mul a b => s!"({emitIExp a} * {emitIExp b})"
  | .mod a b => s!"({emitIExp a} % {emitIExp b})"

/-- A cell as a Python subscript. -/
def emitCell (c : Cell String String) : String := s!"{c.buf}[{emitIExp c.idx}]"

/-- A kernel argument. -/
def emitArg : Arg String String → String
  | .buf v => v
  | .idx e => emitIExp e
  | .cell c => s!"{c.buf}, {emitIExp c.idx}"

/-- A comparison operator. -/
def emitCmp : CmpOp → String
  | .eq => "==" | .lt => "<" | .le => "<="

/-- Indentation. -/
def pad (n : ℕ) : String := String.ofList (List.replicate (4 * n) ' ')

/-- A scalar instruction as a Python assignment. -/
def emitInstr : Instr Unit String String → String
  | .lit _ dst q => s!"{emitCell dst} = {q.num} / {q.den}"
  | .litIdx _ dst e => s!"{emitCell dst} = float({emitIExp e})"
  | .bin _ b dst x y =>
      let o := match b with
        | .add => "+" | .sub => "-" | .mul => "*" | .div => "/" | .shl => "<<" | .shr => ">>"
        | .band => "&" | .bor => "|" | .bxor => "^"
      s!"{emitCell dst} = {emitCell x} {o} {emitCell y}"
  | .un _ u dst x =>
      let f := match u with
        | .neg => s!"-{emitCell x}" | .conj => s!"np.conj({emitCell x})"
        | .re => s!"np.real({emitCell x})" | .sqrt => s!"np.sqrt({emitCell x})"
        | .bnot => s!"~{emitCell x}"
      s!"{emitCell dst} = {f}"
  | .copy _ dst src => s!"{emitCell dst} = {emitCell src}"
  | .convert _ _ dst src => s!"{emitCell dst} = {emitCell src}"
  | .draw _ dist dst =>
      let f := match dist with | .gaussian => "draw_gaussian()" | .rademacher => "draw_rademacher()"
      s!"{emitCell dst} = {f}"

/-- A statement as Python lines at depth `d`, with a counter for fresh names. -/
def emitStmt (inline : Bool) : Stmt Unit Unit String String → ℕ → ℕ → List String × ℕ
  | .skip, _, c => ([], c)
  | .seq s t, d, c =>
      let (l₁, c₁) := emitStmt inline s d c
      let (l₂, c₂) := emitStmt inline t d c₁
      (l₁ ++ l₂, c₂)
  | .instr i, d, c => ([pad d ++ emitInstr i], c)
  | .apply _ _ dst dOff src sOff cols, d, c =>
      let w := s!"A.shape[0] * {emitIExp cols}"
      ([pad d ++ s!"{dst}[{emitIExp dOff}:{emitIExp dOff} + {w}] = (A @ {src}[{emitIExp sOff}:" ++
        s!"{emitIExp sOff} + {w}].reshape((A.shape[0], {emitIExp cols}), order='F'))" ++
        ".reshape(-1, order='F')"], c)
  | .rom _ dst i, d, c => ([pad d ++ s!"{emitCell dst} = ROM[{emitIExp i}]"], c)
  | .alloc _ len body, d, c =>
      let b := s!"b{c}"
      let (ls, c') := emitStmt inline (body b) d (c + 1)
      ([pad d ++ s!"{b} = np.full({emitIExp len}, np.nan)"] ++ ls ++ [pad d ++ s!"del {b}"], c')
  | .loop n body, d, c =>
      let i := s!"i{c}"
      let (ls, c') := emitStmt inline (body i) (d + 1) (c + 1)
      ([pad d ++ s!"for {i} in range({emitIExp n}):"] ++
        (if ls.isEmpty then [pad (d + 1) ++ "pass"] else ls), c')
  | .whileFuel fuel _ cmp x y body, d, c =>
      let (ls, c') := emitStmt inline body (d + 1) c
      ([pad d ++ s!"for _ in range({emitIExp fuel}):",
        pad (d + 1) ++ s!"if not ({emitCell x} {emitCmp cmp} {emitCell y}): break"] ++ ls ++
       [pad d ++ "else:", pad (d + 1) ++ "raise RuntimeError('out of fuel')"], c')
  | .ite _ cmp x y t e, d, c =>
      let (lt, c₁) := emitStmt inline t (d + 1) c
      let (le, c₂) := emitStmt inline e (d + 1) c₁
      ([pad d ++ s!"if {emitCell x} {emitCmp cmp} {emitCell y}:"] ++
        (if lt.isEmpty then [pad (d + 1) ++ "pass"] else lt) ++
        [pad d ++ "else:"] ++ (if le.isEmpty then [pad (d + 1) ++ "pass"] else le), c₂)
  | .named name args body, d, c =>
      if inline then emitStmt inline body d c
      else ([pad d ++ s!"{name}({", ".intercalate (args.map emitArg)})"], c)

/-- A Python function with the given header and body. -/
def emitFunction (inline : Bool) (header : String) (s : Stmt Unit Unit String String) : String :=
  "\n".intercalate ([header] ++ (emitStmt inline s 1 0).1)

/-- The NumPy prelude: the BLAS kernels the programs call by name. -/
def numpyPrelude : String := "\n".intercalate [
  "import numpy as np",
  "def dot(d, di, x, xo, y, yo, n): d[di] = np.vdot(x[xo:xo+n], y[yo:yo+n])",
  "def axpy(a, ai, x, xo, y, yo, n): y[yo:yo+n] += a[ai] * x[xo:xo+n]",
  "def scal(a, ai, x, xo, n): x[xo:xo+n] *= a[ai]",
  "def rscl(a, ai, x, xo, n): x[xo:xo+n] /= a[ai]",
  "def copy(x, xo, y, yo, n): y[yo:yo+n] = x[xo:xo+n]",
  "def nrm2(d, di, x, xo, n): d[di] = np.linalg.norm(x[xo:xo+n])"]

/-- `NLAlib.hutchppProg` as a size-generic NumPy function `hutchpp(A, N, k, l, out)`, with a
`draw_rademacher` hook. -/
def hutchppPython (inline : Bool) : String :=
  emitFunction inline "def hutchpp(A, N, k, l, out):"
    (hutchppProg () () .rademacher (.var "N") (.var "k") (.var "l") ⟨"out", .const 0⟩).run

#eval IO.println (numpyPrelude ++ "\n" ++ hutchppPython false)

end NLAlibTools
