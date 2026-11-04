/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.Float
import NLAlib.Krylov.LinearSystems.CGTargets
import NLAlib.Krylov.Processes.LanczosTargets

/-!
# Float smoke tests of the registered compiled Krylov programs

These examples execute the actual registered compiled trees with the existing
`NLAlibTools.floatSem`. Only the ROM and operation-count instrumentation are specialized.
Every case checks successful execution, all declared output buffers, input preservation,
componentwise approved operation bounds, peak memory including ROM, and workspace release.
They check selected executions; they do not certify a rounding contract for Float
or an IEEE implementation. No algorithm is reimplemented in the test harness.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools.KrylovSmoke

/-- An executable label for each operation kind at the single test tag and oracle name. -/
def opcode : OpKind Unit Unit → Nat
  | .bin _ .add => 0 | .bin _ .sub => 1 | .bin _ .mul => 2 | .bin _ .div => 3
  | .bin _ .shl => 4 | .bin _ .shr => 5 | .bin _ .band => 6 | .bin _ .bor => 7
  | .bin _ .bxor => 8
  | .un _ .neg => 9 | .un _ .conj => 10 | .un _ .re => 11 | .un _ .sqrt => 12
  | .un _ .bnot => 13
  | .lit _ => 14 | .cmp _ => 15 | .copy _ => 16
  | .draw _ .gaussian => 17 | .draw _ .rademacher => 18
  | .convert _ _ => 19 | .rom _ => 20 | .load _ _ => 21 | .matvec _ _ => 22

/-- All operation kinds, including those whose approved bound is zero. -/
def kinds : List (OpKind Unit Unit) :=
  [.bin () .add, .bin () .sub, .bin () .mul, .bin () .div,
    .bin () .shl, .bin () .shr, .bin () .band, .bin () .bor, .bin () .bxor,
    .un () .neg, .un () .conj, .un () .re, .un () .sqrt, .un () .bnot,
    .lit (), .cmp (), .copy (), .draw () .gaussian, .draw () .rademacher,
    .convert () (), .rom (), .load () (), .matvec () ()]

/-- The runtime bound check visits every possible operation kind. -/
theorem mem_kinds (k : OpKind Unit Unit) : k ∈ kinds := by
  cases k with
  | bin p b => cases p; cases b <;> simp [kinds]
  | un p u => cases p; cases u <;> simp [kinds]
  | draw p d => cases p; cases d <;> simp [kinds]
  | convert p q => cases p; cases q; simp [kinds]
  | lit p | cmp p | copy p | rom p => cases p; simp [kinds]
  | load p o | matvec p o => cases p; cases o; simp [kinds]

/-- The test instrumentation uses pointwise natural counts, without changing scalar arithmetic. -/
abbrev Counts := OpKind Unit Unit → Nat

/-- The existing Float arithmetic with column-major stored ROM and componentwise charges. -/
def interp (n : Nat) (rom : Array Float) : Interp Unit Unit Float Counts where
  sem := NLAlibTools.floatSem
  charge k j := if opcode k == opcode j then 1 else 0
  tape _ _ := 0
  oracle _ _ _ := none
  height _ := n
  rom k := rom[k]?
  romSize _ := rom.size
  width _ := 64

/-- Executable evaluation of the registered CG program's componentwise count formula. -/
def cgBudget (n q : Nat) : OpKind Unit Unit → Nat
  | .rom _ => n ^ 2
  | .bin _ .mul | .bin _ .add => n + q * (n ^ 2 + 5 * n)
  | .un _ .conj => n + 2 * q * n
  | .bin _ .div => 2 * q
  | .un _ .neg => q + 1
  | .lit _ => n + 3 + q * (n + 2)
  | .cmp _ => 1 + 3 * q
  | .copy _ => 2 * n + 2 * q + 2
  | _ => 0

/-- Executable evaluation of the registered Lanczos program's componentwise count formula. -/
def lanczosBudget (n q : Nat) : OpKind Unit Unit → Nat
  | .rom _ => n ^ 2
  | .bin _ .mul | .bin _ .add => n + q * (n ^ 2 + 4 * n)
  | .un _ .conj => n + 2 * q * n
  | .bin _ .div => n * (q + 1)
  | .un _ .sqrt => q + 1
  | .un _ .neg => 2 * q
  | .lit _ => 2 * n + 3 + q * (2 * n + 2)
  | .cmp _ => q + 1
  | .copy _ => n + 2 * q * n
  | _ => 0

/-- The executable CG bound is exactly the bound in the registered target. -/
theorem cgBudget_eq (n q : Nat) (k : OpKind Unit Unit) :
    cgBudget n q k = cgCount () n q k := by
  classical
  cases k with
  | bin p b => cases p; cases b <;> simp [cgBudget, cgCount]
  | un p u => cases p; cases u <;> simp [cgBudget, cgCount]
  | draw p d => cases p; cases d <;> simp [cgBudget, cgCount]
  | convert p q => cases p; cases q; simp [cgBudget, cgCount]
  | lit p | cmp p | copy p | rom p => cases p; simp [cgBudget, cgCount]
  | load p o | matvec p o => cases p; cases o; simp [cgBudget, cgCount]

/-- The executable Lanczos bound is exactly the bound in the registered target. -/
theorem lanczosBudget_eq (n q : Nat) (k : OpKind Unit Unit) :
    lanczosBudget n q k = lanczosCount () n q k := by
  classical
  cases k with
  | bin p b => cases p; cases b <;> simp [lanczosBudget, lanczosCount]
  | un p u => cases p; cases u <;> simp [lanczosBudget, lanczosCount]
  | draw p d => cases p; cases d <;> simp [lanczosBudget, lanczosCount]
  | convert p q => cases p; cases q; simp [lanczosBudget, lanczosCount]
  | lit p | cmp p | copy p | rom p => cases p; simp [lanczosBudget, lanczosCount]
  | load p o | matvec p o => cases p; cases o; simp [lanczosBudget, lanczosCount]

/-- Read a whole buffer without replacing absent or uninitialized cells by zero. -/
def readBuffer (st : St Unit Float Counts) (buf : Nat) : Option (Array Float) := do
  let (_, xs) ← st.store[buf]?
  xs.mapM id

/-- A strict length and numerical comparison; NaNs also cause failure. -/
def close (xs ys : Array Float) : Bool :=
  xs.size == ys.size && (List.range xs.size).all fun i => (xs[i]! - ys[i]!).abs < 1e-12

/-- Check every operation-count component, peak plus ROM, and scoped workspace release. -/
def resources (I : Interp Unit Unit Float Counts) (initial final : St Unit Float Counts)
    (bound : OpKind Unit Unit → Nat) (memory : Nat) : Bool :=
  kinds.all (fun k => decide (final.cnt k ≤ bound k)) &&
    decide (final.peak () + I.romSize () ≤ memory) &&
    final.store.size == initial.store.size && final.cur () == initial.cur () &&
    final.pos .gaussian == 0 && final.pos .rademacher == 0

/-- Execute the compiled CG tree and check all five declared buffers and the approved budgets. -/
def cgCase (rom b : Array Float) (q : Nat) (x r p : Array Float) (status : Float) : Bool :=
  let n := b.size
  let I := interp n rom
  let initial : St Unit Float Counts := inputState ()
    [b.map some, Array.replicate n none, Array.replicate n none,
      Array.replicate n none, Array.replicate 1 none]
  match (cgProg.compiled (ι := Unit) ()).exec I n ![q] initial with
  | none => false
  | some final =>
    resources I initial final (cgBudget n q) (2 * n ^ 2 + 5 * n + 11) &&
      ([b, x, r, p, #[status]].zip (List.range 5)).all fun (expected, i) =>
        match readBuffer final i with
        | none => false
        | some actual => close actual expected

/-- Execute the compiled Lanczos tree and check every coefficient, column and declared buffer. -/
def lanczosCase (rom b : Array Float) (q : Nat)
    (v alpha beta norm prev : Array Float) : Bool :=
  let n := b.size
  let I := interp n rom
  let initial : St Unit Float Counts := inputState ()
    [b.map some, Array.replicate (n * (q + 1)) none, Array.replicate q none,
      Array.replicate (q + 1) none, Array.replicate 1 none, Array.replicate n none]
  match (lanczosProg.compiled (ι := Unit) ()).exec I n ![q] initial with
  | none => false
  | some final =>
    resources I initial final (lanczosBudget n q)
      (2 * n ^ 2 + n * (q + 4) + 2 * q + 5) &&
      ([b, v, alpha, beta, norm, prev].zip (List.range 6)).all fun (expected, i) =>
        match readBuffer final i with
        | none => false
        | some actual => close actual expected

-- Column-major matrix inputs. Every expected branch below uses exactly representable arithmetic.
#guard cgCase #[1, 0, 0, 1] #[0, 0] 3 #[0, 0] #[0, 0] #[0, 0] 1
#guard cgCase #[1, 0, 0, 3] #[1, 2] 0 #[0, 0] #[1, 2] #[1, 2] 0
#guard cgCase #[1, 0, 0, 1] #[1, 0] 4 #[1, 0] #[0, 0] #[0, 0] 1
#guard cgCase #[2, 1, 1, 2] #[1, -1] 3 #[1, -1] #[0, 0] #[0, 0] 1
#guard cgCase #[1, 0, 0, 3] #[1, 1] 1 #[0.5, 0.5] #[0.5, -0.5] #[0.75, -0.25] 0
#guard cgCase #[-1, 0, 0, -1] #[1, 0] 3 #[0, 0] #[1, 0] #[1, 0] (-1)
#guard cgCase #[0, 0, 0, 0] #[1, 0] 3 #[0, 0] #[1, 0] #[1, 0] (-1)
#guard cgCase #[] #[] 2 #[] #[] #[] 1

#guard lanczosCase #[2, 0, 0, 3] #[0, 0] 3
  #[0, 0, 0, 0, 0, 0, 0, 0] #[0, 0, 0] #[0, 0, 0, 0] #[0] #[0, 0]
#guard lanczosCase #[2, 0, 0, 3] #[0, 2] 0 #[0, 1] #[] #[0] #[2] #[0, 0]
#guard lanczosCase #[2, 0, 0, 3] #[1, 0] 3
  #[1, 0, 0, 0, 0, 0, 0, 0] #[2, 0, 0] #[0, 0, 0, 0] #[1] #[0, 0]
#guard lanczosCase #[0, 1, 1, 0] #[1, 0] 3
  #[1, 0, 0, 1, 0, 0, 0, 0] #[0, 0, 0] #[0, 1, 0, 0] #[1] #[0, 0]
-- Nonsymmetry makes transposed or row-major ROM addressing observable.
#guard lanczosCase #[0, 1, 2, 0] #[1, 0] 2
  #[1, 0, 0, 1, 1, 0] #[0, 0] #[0, 1, 1] #[1] #[0, 1]
#guard lanczosCase #[] #[] 2 #[] #[0, 0] #[0, 0, 0] #[0] #[]

end NLAlibTools.KrylovSmoke
