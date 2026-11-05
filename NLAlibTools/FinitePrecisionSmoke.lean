/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Computation.Float
import NLAlib.Computation.FixedPoint
import NLAlibTools.KrylovSmoke

/-!
# Finite-format execution of the registered CG program

These regressions run the existing compiled stored-entry CG tree under checked Lean Float
arithmetic. They distinguish bit patterns, so a tiny nonzero residual is never accepted as zero
by a test tolerance. The underflow cases exercise the actual initial self-dot and stopping
branch; overflow and nonfinite inputs fail through the checked primitive semantics.

The numerical library theorem about CG's residual kernel is in `CGProgramUnderflow.lean`.
These executions are regression tests, not a universal Float accuracy or no-overflow certificate.
Resource checks use the existing approved count formulas and include workspace cleanup.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools.FinitePrecisionSmoke

/-- A normal binary64 value equal to $2^{-600}$; its square rounds to zero. -/
def tinyNormal : Float := Float.ofBits 0x1a70000000000000

/-- The smallest positive binary64 subnormal, equal to $2^{-1074}$. -/
def tinySubnormal : Float := Float.ofBits 1

/-- The largest finite positive binary64 value. -/
def largest : Float := Float.ofBits 0x7fefffffffffffff

/-- The canonical quiet NaN bit pattern used in an invalid-input regression. -/
def invalid : Float := Float.ofBits 0x7ff8000000000000

/-- Five declared scalar buffers with their logical bit memory counted from the start. -/
def initial {K : Type} (width : Nat) (b : K) : St Unit K KrylovSmoke.Counts :=
  { inputState () [#[some b], #[none], #[none], #[none], #[none]] with
    curW := 5 * width
    peakW := 5 * width }

/-- One-dimensional stored CG with the library's checked Float arithmetic. -/
def runCG (a b : Float) (steps : Nat) : Option (St Unit Float KrylovSmoke.Counts) :=
  let interp := { KrylovSmoke.interp 1 #[a] with sem := checkedFloatSem }
  (cgProg.compiled (ι := Unit) ()).exec interp 1 ![steps] (initial 64 b)

/-- Check every returned word bit for bit, every operation kind's budget, bit workspace and
scope cleanup. In particular, subnormal values cannot pass this check as zero. -/
def checkCG (a b : Float) (steps : Nat) (x r p status : Float) : Bool :=
  let interp := { KrylovSmoke.interp 1 #[a] with sem := checkedFloatSem }
  match runCG a b steps with
  | none => false
  | some out =>
    KrylovSmoke.resources interp (initial 64 b) out (KrylovSmoke.cgBudget 1 steps) 18 &&
      decide (out.peakW + 64 ≤ 64 * 18) && out.curW == 5 * 64 &&
      ([b, x, r, p, status].zip (List.range 5)).all fun (expected, buf) =>
        match out.store.read () buf 0 with
        | none => false
        | some actual => actual.toBits == expected.toBits

-- Ordinary execution, an initially zero residual, and an exhausted iteration budget.
#guard checkCG 2 2 3 1 0 0 1
#guard checkCG 1 0 3 0 0 0 1
#guard checkCG 2 2 0 0 2 2 0

-- Both inputs are nonzero, and the first is normal. Their squared norms underflow to zero.
#guard tinyNormal.isFinite && tinyNormal.toBits != 0 && tinyNormal * tinyNormal == 0
#guard tinySubnormal.isFinite && tinySubnormal.toBits != 0 && tinySubnormal * tinySubnormal == 0
#guard checkCG 1 tinyNormal 3 0 tinyNormal tinyNormal 1
#guard checkCG 1 tinySubnormal 3 0 tinySubnormal tinySubnormal 1

-- Checked execution rejects overflow and a nonfinite residual input.
#guard largest.isFinite
#guard (runCG 1 largest 3).isNone
#guard (runCG 1 invalid 3).isNone

/-- A finite non-IEEE endpoint: grid spacing $1/16$, integer words from $-256$ to $256$.
Its 513 possible words fit in ten logical bits; native execution still uses Lean integers. -/
def fixedInterp (a : FixedPoint 256) : Interp Unit Unit (FixedPoint 256) KrylovSmoke.Counts where
  sem := fixedPointSem 16 256
  charge k j := if KrylovSmoke.opcode k == KrylovSmoke.opcode j then 1 else 0
  tape _ _ := ⟨0, by decide⟩
  oracle _ _ _ := none
  height _ := 1
  rom k := #[a][k]?
  romSize _ := 1
  width _ := 10

/-- Execute the same compiled CG tree with bounded fixed-point arithmetic. -/
def runFixedCG (a b : FixedPoint 256) (steps : Nat) :
    Option (St Unit (FixedPoint 256) KrylovSmoke.Counts) :=
  (cgProg.compiled (ι := Unit) ()).exec (fixedInterp a) 1 ![steps] (initial 10 b)

/-- Check every fixed-point word, every operation budget, logical bit memory and cleanup. -/
def checkFixedCG (a b : FixedPoint 256) (steps : Nat) (x r p status : Int) : Bool :=
  match runFixedCG a b steps with
  | none => false
  | some out =>
    KrylovSmoke.kinds.all (fun k => decide (out.cnt k ≤ KrylovSmoke.cgBudget 1 steps k)) &&
      decide (out.peak () + 1 ≤ 18) && decide (out.peakW + 10 ≤ 10 * 18) &&
      out.store.size == 5 && out.cur () == 5 && out.curW == 50 &&
      ([b.val, x, r, p, status].zip (List.range 5)).all fun (expected, buf) =>
        match out.store.read () buf 0 with
        | none => false
        | some actual => actual.val == expected

-- All expected values here are integer words, interpreted after division by 16.
#guard checkFixedCG ⟨32, by decide⟩ ⟨32, by decide⟩ 3 16 0 0 16
#guard checkFixedCG ⟨16, by decide⟩ ⟨1, by decide⟩ 3 0 1 1 16
#guard checkFixedCG ⟨32, by decide⟩ ⟨32, by decide⟩ 0 0 32 32 0
#guard (runFixedCG ⟨16, by decide⟩ ⟨256, by decide⟩ 3).isNone

/-- Use only finite Float words in the arithmetic carrier. Nonfinite external inputs are
rejected at entry; arithmetic overflow remains a checked execution failure. -/
def runFiniteCG (a b : Float) (steps : Nat) :
    Option (St Unit FiniteFloat KrylovSmoke.Counts) := do
  if ha : a.isFinite = true then
    if hb : b.isFinite = true then
      let a' : FiniteFloat := ⟨a, ha⟩
      let b' : FiniteFloat := ⟨b, hb⟩
      let interp : Interp Unit Unit FiniteFloat KrylovSmoke.Counts :=
        { sem := finiteFloatSem
          charge := fun k j => if KrylovSmoke.opcode k == KrylovSmoke.opcode j then 1 else 0
          tape := fun _ _ => ⟨0, by decide⟩
          oracle := fun _ _ _ => none
          height := fun _ => 1
          rom := fun k => #[a'][k]?
          romSize := fun _ => 1
          width := fun _ => 64 }
      (cgProg.compiled (ι := Unit) ()).exec interp 1 ![steps] (initial 64 b')
    else none
  else none

/-- Check that finite-word execution has the same returned words and program-level resource
accounting as the checked raw-word execution on the selected finite inputs. -/
def finiteMatches (a b : Float) (steps : Nat) : Bool :=
  match runCG a b steps, runFiniteCG a b steps with
  | none, none => true
  | some raw, some finite =>
    raw.cur () == finite.cur () && raw.curW == finite.curW &&
      raw.peak () == finite.peak () && raw.peakW == finite.peakW &&
      raw.store.size == finite.store.size &&
      KrylovSmoke.kinds.all (fun k => raw.cnt k == finite.cnt k) &&
      (List.range 5).all fun buf =>
        match raw.store.read () buf 0, finite.store.read () buf 0 with
        | some x, some y => x.toBits == y.val.toBits
        | _, _ => false
  | _, _ => false

#guard finiteMatches 2 2 3
#guard finiteMatches 1 tinyNormal 3
#guard finiteMatches 1 largest 3

/-- Run the existing checked square-root primitive on the finite-word carrier. -/
def runFiniteSqrt (x : Float) : Option Float :=
  if hx : x.isFinite = true then
    (finiteFloatSem.un () .sqrt ⟨x, hx⟩).map Subtype.val
  else none

-- Native endpoint checks include both exponent extremes and an invalid real domain.
#guard (runFiniteSqrt 0).map Float.toBits == some 0
#guard (runFiniteSqrt tinySubnormal).map Float.toBits == some ((486 : UInt64) <<< 52)
#guard match runFiniteSqrt largest with
  | some z => z.isFinite && z.toBits >>> 63 == 0
  | none => false
#guard (runFiniteSqrt (-1)).isNone

end NLAlibTools.FinitePrecisionSmoke
