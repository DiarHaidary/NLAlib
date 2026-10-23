/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import Mathlib.Data.Int.Bitwise
import NLAlib.Computation.BLAS
import NLAlib.Computation.Subst

/-!
# The fixed-point example: reducing an arithmetic to word operations

Two tags over one word carrier `ℤ` (D16 (i)): Q16 fixed point (`fx`, value $w/2^{16}$) and
plain integers (`int`). `NLAlibTools.fxSem` is fixed-point arithmetic on words and
`NLAlibTools.wordSem` has integer operations only; `NLAlibTools.fxImpl` implements fixed-point
addition and multiplication by reinterpretation, integer operations and a shift, so that
`NLAlib.Computation.Stmt.subst` turns a fixed-point program into a word-level one. The run of
`dot` at `fx` gives the same word at both levels (`docs/design/Computation.md` §7.4). The `int`
tag is unbounded, so the bit cost is a weighted count, not a certified 64-bit count.

The certificate `NLAlibTools.implementsInstr_fxImpl` and the error bound
`NLAlibTools.fxSem_mul_abs_sub_le` are stated, not proved: this is a test of the design, not part
of the library.
-/

-- A tools file: `#eval` and `#guard` are its point.
set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

/-- Two tags over one word carrier `ℤ`: Q16 fixed point and plain integers. -/
inductive FxTag where
  /-- Q16 fixed point: the word $w$ stands for $w/2^{16}$. -/
  | fx
  /-- Plain integers. -/
  | int
  deriving DecidableEq, Repr

/-- The value of a stored word: `w / 2^16` at `fx`, `w` at `int`. -/
def fxDecode : FxTag → ℤ → ℚ
  | .fx, w => (w : ℚ) / 65536
  | .int, w => w

/-- Integer and bitwise operations on unbounded words; shifts by a nonnegative amount. -/
def intBin (b : BinOp) (x y : ℤ) : Option ℤ :=
  match b with
  | .add => some (x + y) | .sub => some (x - y) | .mul => some (x * y)
  | .shr => if 0 ≤ y then some (Int.fdiv x (2 ^ y.toNat)) else none
  | .shl => if 0 ≤ y then some (x * 2 ^ y.toNat) else none
  | .band => some (Int.land x y) | .bor => some (Int.lor x y) | .bxor => some (Int.xor x y)
  | .div => none

/-- The higher-level semantics: fixed-point arithmetic on words (product truncated toward
`-∞`), integers on `int`. -/
def fxSem : ScalarSem FxTag ℤ where
  lit p q := match p with
    | .fx => some (Int.fdiv (q.num * 65536) q.den)
    | .int => if q.den = 1 then some q.num else none
  bin p b x y := match p, b with
    | .fx, .add => some (x + y) | .fx, .sub => some (x - y)
    | .fx, .mul => some (Int.fdiv (x * y) 65536)
    | .fx, _ => none
    | .int, b => intBin b x y
  un p u x := match p, u with
    | .fx, .conj => some x | .fx, .neg => some (-x) | .int, .neg => some (-x)
    | _, _ => none
  cmp _ c x y := match c with
    | .eq => some (decide (x = y)) | .lt => some (decide (x < y)) | .le => some (decide (x ≤ y))
  convert _ _ x := some x

/-- The word-level semantics: only integer operations; fixed point keeps its literals and
comparisons, and nothing else. -/
def wordSem : ScalarSem FxTag ℤ :=
  { fxSem with
    bin := fun p b x y => match p with | .fx => none | .int => intBin b x y
    un := fun p u x => match p, u with | .int, .neg => some (-x) | _, _ => none }

/-- **Fixed-point operations implemented by word operations.** `add` and `mul` at `fx` become
reinterpretations to `int`, integer operations and a shift; `conj` (the identity on reals) a
copy; everything else is kept. -/
def fxImpl {ι VB VI : Type} : Instr FxTag VB VI → Stmt FxTag ι VB VI
  | .bin .fx .add dst x y => Builder.run do
      let t ← Builder.alloc .int 3
      Builder.ins (.convert .fx .int ⟨t, 0⟩ x)
      Builder.ins (.convert .fx .int ⟨t, 1⟩ y)
      Builder.ins (.bin .int .add ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      Builder.ins (.convert .int .fx dst ⟨t, 2⟩)
  | .bin .fx .mul dst x y => Builder.run do
      let t ← Builder.alloc .int 4
      Builder.ins (.convert .fx .int ⟨t, 0⟩ x)
      Builder.ins (.convert .fx .int ⟨t, 1⟩ y)
      Builder.ins (.bin .int .mul ⟨t, 2⟩ ⟨t, 0⟩ ⟨t, 1⟩)
      Builder.ins (.litIdx .int ⟨t, 3⟩ 16)
      Builder.ins (.bin .int .shr ⟨t, 2⟩ ⟨t, 2⟩ ⟨t, 3⟩)
      Builder.ins (.convert .int .fx dst ⟨t, 2⟩)
  | .un .fx .conj dst x => .instr (.copy .fx dst x)
  | i => .instr i

/-- Counts for the demonstration: (fixed-point operations, integer operations, conversions,
bit cost with 64-bit words: `64` per add, shift and bitwise operation, `64²` per multiply). -/
def fxCharge : OpKind FxTag Unit → ℕ × ℕ × ℕ × ℕ
  | .bin .fx _ => (1, 0, 0, 0) | .un .fx _ => (1, 0, 0, 0)
  | .bin .int .mul => (0, 1, 0, 4096) | .bin .int _ => (0, 1, 0, 64)
  | .convert _ _ => (0, 0, 1, 0)
  | _ => (0, 0, 0, 0)

/-- The interpretation of the example: no oracles, no tape, 64-bit cells. -/
def fxInterp (sem : ScalarSem FxTag ℤ) : Interp FxTag Unit ℤ (ℕ × ℕ × ℕ × ℕ) where
  sem := sem
  charge := fxCharge
  tape _ _ := 0
  oracle _ _ _ := none
  height _ := 0
  rom _ := none
  romSize _ := 0
  width _ := 64

/-- The initial state of the example, memory counted from zero. -/
def fxState (bufs : List (FxTag × Array (Option ℤ))) : St FxTag ℤ (ℕ × ℕ × ℕ × ℕ) where
  store := bufs.toArray
  pos _ := 0
  cnt := 0
  cur _ := 0
  peak _ := 0
  curW := 0
  peakW := 0

/-- `x = (1.5, −2.25, 0.5)`, `y = (2, 0.75, −4)` in Q16; `xᵀy = −0.6875`. -/
def fxBufs : List (FxTag × Array (Option ℤ)) :=
  [(.fx, #[some 98304, some (-147456), some 32768]), (.fx, #[some 131072, some 49152,
    some (-262144)]), (.fx, #[none])]

/-- `dot` of the two vectors at `fx`, into buffer 2. -/
def fxDot : Stmt FxTag Unit ℕ ℕ :=
  (dot .fx ⟨2, .const 0⟩ 0 (.const 0) 1 (.const 0) (.const 3)).run

/-- The two runs: the fixed-point program and its word-level substitution, with the output word,
the counts and the bit peak. -/
def fxRuns :
    Option ((Option ℤ × (ℕ × ℕ × ℕ × ℕ) × ℕ) × (Option ℤ × (ℕ × ℕ × ℕ × ℕ) × ℕ)) := do
  let a ← exec (fxInterp fxSem) fxDot (fxState fxBufs)
  let w ← exec (fxInterp wordSem) (fxDot.subst fxImpl fun _ _ _ _ _ _ _ => .skip)
    (fxState fxBufs)
  some ((a.store.read .fx 2 0, a.cnt, a.peakW), (w.store.read .fx 2 0, w.cnt, w.peakW))

#eval fxRuns

-- The same word, `-0.6875 = -45056 / 2^16`, at both levels (§7.4).
#guard fxRuns == some ((some (-45056), (9, 0, 0, 0), 64), (some (-45056), (0, 9, 18, 12672), 320))

/-- The cost of each fixed-point kind at the word level. -/
noncomputable def fxCost : OpKind FxTag Unit → OpCount FxTag Unit
  | .bin .fx .add => Finsupp.single (.convert .fx .int) 2 + Finsupp.single (.bin .int .add) 1 +
      Finsupp.single (.convert .int .fx) 1
  | .bin .fx .mul => Finsupp.single (.convert .fx .int) 2 + Finsupp.single (.bin .int .mul) 1 +
      Finsupp.single (.lit .int) 1 + Finsupp.single (.bin .int .shr) 1 +
      Finsupp.single (.convert .int .fx) 1
  | .un .fx .conj => Finsupp.single (.copy .fx) 1
  | k => Finsupp.single k 1

/-- **The word-level implementation implements the fixed-point semantics**, at most four scratch
integer cells (256 bits). -/
theorem implementsInstr_fxImpl (I I' : Interp FxTag Unit ℤ (OpCount FxTag Unit))
    (hI : I.sem = fxSem) (hI' : I'.sem = wordSem) (hc' : ∀ k, I'.charge k = Finsupp.single k 1)
    (htape : I'.tape = I.tape) (hw : I'.width = fun _ => 64) :
    ImplementsInstr I I' fxImpl fxCost (fun q => if q = .int then 4 else 0) 256 := sorry

/-- The fixed-point product meets an absolute-error contract: `|ẑ − x̂ŷ| ≤ 2⁻¹⁶`. -/
theorem fxSem_mul_abs_sub_le {x y z : ℤ} (h : fxSem.bin .fx .mul x y = some z) :
    |fxDecode .fx z - fxDecode .fx x * fxDecode .fx y| ≤ 1 / 65536 := sorry


end NLAlibTools
