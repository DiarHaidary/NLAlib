/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.Float

/-!
# Printing first-order programs as NumPy

The emitter prints a first-order tree (`NLAlib.Computation.FStmt`), so the code emitted for a
result is printed from the very tree the result is about: a registered tree such as
`NLAlib.hutchppProg.compiled` (`docs/design/Computation.md`, F1 and F11 step C). Variables are de
Bruijn levels: handle `j` is printed `b{j}` and index variable `j` is printed `i{j}`, so the free
variables of a program `Prog P ι r b` are the parameters of the emitted function: the oracle
dimension `i0`, the sizes `i1`, …, `i{r}` and the declared buffers `b0`, …, `b{b-1}`. An `alloc`
in scope of `nb` handles binds `b{nb}`, a `loop` in scope of `ni` indices binds `i{ni}`. Index
expressions are printed as Python arithmetic. `named` kernels are printed as calls into a short
NumPy prelude (`NLAlibTools.numpyPrelude`), or inlined. Fresh buffers are `np.full(len, np.nan)`,
so a read before a write shows as `nan`. The emitted code is an unverified translation, for
differential testing (`docs/design/Computation.md` §8): below, the emitted Hutch++ runs under
NumPy, when it is installed, and agrees with the Lean `Float` run of the same tree.
-/

-- A tools file: `#eval` and `#guard` are its point.
set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

/-- An index variable. -/
def idxName {ni : ℕ} (v : Fin ni) : String := s!"i{v.val}"

/-- A handle. -/
def bufName {nb : ℕ} (v : Fin nb) : String := s!"b{v.val}"

/-- An index expression as Python arithmetic (truncated subtraction as `max(·, 0)`). -/
def emitIExp {ni : ℕ} : IExp (Fin ni) → String
  | .var v => idxName v
  | .const n => toString n
  | .add a b => s!"({emitIExp a} + {emitIExp b})"
  | .sub a b => s!"max({emitIExp a} - {emitIExp b}, 0)"
  | .mul a b => s!"({emitIExp a} * {emitIExp b})"
  | .mod a b => s!"({emitIExp a} % {emitIExp b})"

/-- A cell as a Python subscript. -/
def emitCell {nb ni : ℕ} (c : Cell (Fin nb) (Fin ni)) : String :=
  s!"{bufName c.buf}[{emitIExp c.idx}]"

/-- A kernel argument. -/
def emitArg {nb ni : ℕ} : Arg (Fin nb) (Fin ni) → String
  | .buf v => bufName v
  | .idx e => emitIExp e
  | .cell c => s!"{bufName c.buf}, {emitIExp c.idx}"

/-- A comparison operator. -/
def emitCmp : CmpOp → String
  | .eq => "==" | .lt => "<" | .le => "<="

/-- Indentation. -/
def pad (n : ℕ) : String := String.ofList (List.replicate (4 * n) ' ')

/-- A scalar instruction as a Python assignment. -/
def emitInstr {P : Type} {nb ni : ℕ} : Instr P (Fin nb) (Fin ni) → String
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

/-- A first-order statement as Python lines at depth `d`. -/
def emitF {P ι : Type} (inline : Bool) : {nb ni : ℕ} → FStmt P ι nb ni → ℕ → List String
  | _, _, .skip, _ => []
  | _, _, .seq s t, d => emitF inline s d ++ emitF inline t d
  | _, _, .instr i, d => [pad d ++ emitInstr i]
  | _, _, .apply _ _ dst dOff src sOff cols, d =>
      let w := s!"A.shape[0] * {emitIExp cols}"
      [pad d ++ s!"{bufName dst}[{emitIExp dOff}:{emitIExp dOff} + {w}] = (A @ " ++
        s!"{bufName src}[{emitIExp sOff}:{emitIExp sOff} + {w}].reshape((A.shape[0], " ++
        s!"{emitIExp cols}), order='F')).reshape(-1, order='F')"]
  | _, _, .rom _ dst i, d => [pad d ++ s!"{emitCell dst} = ROM[{emitIExp i}]"]
  | nb, _, .alloc _ len body, d =>
      [pad d ++ s!"b{nb} = np.full({emitIExp len}, np.nan)"] ++ emitF inline body d ++
        [pad d ++ s!"del b{nb}"]
  | _, ni, .loop n body, d =>
      let ls := emitF inline body (d + 1)
      [pad d ++ s!"for i{ni} in range({emitIExp n}):"] ++
        (if ls.isEmpty then [pad (d + 1) ++ "pass"] else ls)
  | _, _, .whileFuel fuel _ cmp x y body, d =>
      [pad d ++ s!"for _ in range({emitIExp fuel}):",
        pad (d + 1) ++ s!"if not ({emitCell x} {emitCmp cmp} {emitCell y}): break"] ++
        emitF inline body (d + 1) ++
        [pad d ++ "else:", pad (d + 1) ++ "raise RuntimeError('out of fuel')"]
  | _, _, .ite _ cmp x y t e, d =>
      let lt := emitF inline t (d + 1)
      let le := emitF inline e (d + 1)
      [pad d ++ s!"if {emitCell x} {emitCmp cmp} {emitCell y}:"] ++
        (if lt.isEmpty then [pad (d + 1) ++ "pass"] else lt) ++
        [pad d ++ "else:"] ++ (if le.isEmpty then [pad (d + 1) ++ "pass"] else le)
  | _, _, .named name args body, d =>
      if inline then emitF inline body d
      else [pad d ++ s!"{name}({", ".intercalate (args.map emitArg)})"]

/-- A program `Prog P ι r b` as a Python function `name(A, i0, …, i{r}, b0, …, b{b-1})`. -/
def emitProg {P ι : Type} {r b : ℕ} (inline : Bool) (name : String) (prog : Prog P ι r b) :
    String :=
  let params := ["A"] ++ (List.range (r + 1)).map (s!"i{·}") ++ (List.range b).map (s!"b{·}")
  "\n".intercalate ([s!"def {name}({", ".intercalate params}):"] ++ emitF inline prog 1)

/-- The NumPy prelude: the BLAS kernels the programs call by name. -/
def numpyPrelude : String := "\n".intercalate [
  "import numpy as np",
  "def dot(d, di, x, xo, y, yo, n): d[di] = np.vdot(x[xo:xo+n], y[yo:yo+n])",
  "def axpy(a, ai, x, xo, y, yo, n): y[yo:yo+n] += a[ai] * x[xo:xo+n]",
  "def scal(a, ai, x, xo, n): x[xo:xo+n] *= a[ai]",
  "def rscl(a, ai, x, xo, n): x[xo:xo+n] /= a[ai]",
  "def copy(x, xo, y, yo, n): y[yo:yo+n] = x[xo:xo+n]",
  "def nrm2(d, di, x, xo, n): d[di] = np.linalg.norm(x[xo:xo+n])"]

/-- The registered tree `NLAlib.hutchppProg.compiled` as a NumPy function
`hutchpp(A, i0, i1, i2, b0)`: `i0` is $N$, `i1` is $k$, `i2` is $\ell$, and the estimate is
written to `b0[0]`; with a `draw_rademacher` hook. -/
def hutchppPython (inline : Bool) : String :=
  emitProg inline "hutchpp" (hutchppProg.compiled (P := Unit) (ι := Unit) () () .rademacher)

#eval IO.println (numpyPrelude ++ "\n" ++ hutchppPython false)

/-- A Python script that runs the emitted Hutch++ on the matrix `A₀` with the sign tape and
prints the estimate. -/
def hutchppScript (inline : Bool) (k ℓ : ℕ) : String :=
  let rows := ", ".intercalate (A₀.toList.map fun r => "[" ++ ", ".intercalate
    (r.toList.map toString) ++ "]")
  let tape := ", ".intercalate (signTape.map toString)
  "\n".intercalate [numpyPrelude, hutchppPython inline,
    s!"A = np.array([{rows}])", s!"tape = [{tape}]",
    "def draw_rademacher(): return tape.pop(0)",
    "out = np.full(1, np.nan)", s!"hutchpp(A, 5, {k}, {ℓ}, out)", "print(repr(float(out[0])))"]

/-- **Differential test**: the emitted Hutch++, run by NumPy, agrees with the Lean `Float` run
of the same registered tree (`NLAlibTools.hutchppTreeRun`) to six digits, in both modes and on
both rows of the design note's table; skipped when NumPy is not installed. -/
def differentialTest : IO Unit := do
  let probe ← IO.Process.output { cmd := "python3", args := #["-c", "import numpy"] }
    |>.toBaseIO
  match probe with
  | .ok out =>
    if out.exitCode != 0 then IO.println "differential test skipped: no NumPy"; return
  | .error _ => IO.println "differential test skipped: no python3"; return
  for (k, ℓ) in [(2, 1), (5, 1)] do
    for inline in [false, true] do
      let out ← IO.Process.output
        { cmd := "python3", args := #["-c", hutchppScript inline k ℓ] }
      let some lean := (hutchppTreeRun k ℓ).bind (·.1.head?)
        | throw <| IO.userError "the Lean run of the tree fails"
      let py := out.stdout.trimAscii.toString
      unless out.exitCode == 0 && (py.toList.all fun c => c.isDigit || c == '.' || c == '-') do
        throw <| IO.userError s!"the emitted code fails: {out.stderr}"
      unless (lean - parseFloat py).abs < 1e-6 do
        throw <| IO.userError s!"k = {k}, ℓ = {ℓ}: NumPy {py}, Lean {lean}"
      IO.println s!"k = {k}, ℓ = {ℓ}, inline {inline}: NumPy {py} agrees with Lean {lean}"
where
  /-- A decimal literal as a `Float`. -/
  parseFloat (s : String) : Float :=
    let (neg, s) := if s.startsWith "-" then (true, (s.drop 1).toString) else (false, s)
    let parts := s.splitOn "."
    let ip := (parts.head?.bind String.toNat?).getD 0
    let fp := parts[1]?.getD ""
    let v := Float.ofNat ip + Float.ofNat (fp.toNat?.getD 0) / Float.ofNat (10 ^ fp.length)
    if neg then -v else v

#eval differentialTest

end NLAlibTools
