/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlibTools.KrylovSmoke
import NLAlib.Krylov.LinearSystems.CGOracleTargets
import NLAlib.Krylov.Processes.LanczosOracleTargets

/-!
# Float smoke tests of approved matrix-free Krylov programs

The actual compiled programs run against a column-major Float matrix oracle. The tests check
all declared outputs, all operation kinds, both memory accounting units and workspace release.
The oracle is an external backend; its internal storage and arithmetic are excluded from the
matrix-free access model. These examples do not certify an IEEE rounding contract.
-/

set_option linter.hashCommand false

open NLAlib NLAlib.Computation NLAlibTools.KrylovSmoke

namespace NLAlibTools.OracleSmoke

/-- Existing Float scalar semantics with a matrix-vector oracle and no stored ROM. -/
def interp (n : Nat) (a : Array Float) : Interp Unit Unit Float Counts :=
  { KrylovSmoke.interp n #[] with
    oracle := fun _ cols x =>
      if x.size == n * cols then
        some (Array.ofFn fun i : Fin (n * cols) =>
          (List.range n).foldl (fun sum j =>
            sum + a[i.val % n + n * j]! * x[j + n * (i.val / n)]!) 0)
      else none }

/-- Executable evaluation of the approved matrix-free CG counts. -/
def cgBudget (n q : Nat) : OpKind Unit Unit → Nat
  | .load _ _ | .matvec _ _ => q
  | .bin _ .mul | .bin _ .add => n + 5 * q * n
  | .un _ .conj => n + 2 * q * n
  | .bin _ .div => 2 * q
  | .un _ .neg => q + 1
  | .lit _ => n + 3 + 2 * q
  | .cmp _ => 1 + 3 * q
  | .copy _ => 2 * n + 2 * q + 2
  | _ => 0

/-- Executable evaluation of the approved matrix-free Lanczos counts. -/
def lanczosBudget (n q : Nat) : OpKind Unit Unit → Nat
  | .load _ _ | .matvec _ _ => q
  | .bin _ .mul | .bin _ .add => n + 4 * q * n
  | .un _ .conj => n + 2 * q * n
  | .bin _ .div => n * (q + 1)
  | .un _ .sqrt => q + 1
  | .un _ .neg => 2 * q
  | .lit _ => 2 * n + 3 + q * (n + 2)
  | .cmp _ => q + 1
  | .copy _ => n + 2 * q * n
  | _ => 0

/-- The executable CG budget equals the formula in the approved target. -/
theorem cgBudget_eq (n q : Nat) (k : OpKind Unit Unit) :
    cgBudget n q k = cgOracleCount () () n q k := by
  classical
  cases k with
  | bin p b => cases p; cases b <;> simp [cgBudget, cgOracleCount]
  | un p u => cases p; cases u <;> simp [cgBudget, cgOracleCount]
  | draw p d => cases p; cases d <;> simp [cgBudget, cgOracleCount]
  | convert p q => cases p; cases q; simp [cgBudget, cgOracleCount]
  | lit p | cmp p | copy p | rom p => cases p; simp [cgBudget, cgOracleCount]
  | load p o | matvec p o => cases p; cases o; simp [cgBudget, cgOracleCount]

/-- The executable Lanczos budget equals the formula in the approved target. -/
theorem lanczosBudget_eq (n q : Nat) (k : OpKind Unit Unit) :
    lanczosBudget n q k = lanczosOracleCount () () n q k := by
  classical
  cases k with
  | bin p b => cases p; cases b <;> simp [lanczosBudget, lanczosOracleCount]
  | un p u => cases p; cases u <;> simp [lanczosBudget, lanczosOracleCount]
  | draw p d => cases p; cases d <;> simp [lanczosBudget, lanczosOracleCount]
  | convert p q => cases p; cases q; simp [lanczosBudget, lanczosOracleCount]
  | lit p | cmp p | copy p | rom p => cases p; simp [lanczosBudget, lanczosOracleCount]
  | load p o | matvec p o => cases p; cases o; simp [lanczosBudget, lanczosOracleCount]

/-- Execute the compiled CG tree and check all five declared buffers and the approved budgets. -/
def cgCase (rom b : Array Float) (q : Nat) (x r p : Array Float) (status : Float) : Bool :=
  let n := b.size
  let I := interp n rom
  let initial : St Unit Float Counts := inputState ()
    [b.map some, Array.replicate n none, Array.replicate n none,
      Array.replicate n none, Array.replicate 1 none]
  match (cgOracleProg.compiled () ()).exec I n ![q] initial with
  | none => false
  | some final =>
    resources I initial final (cgBudget n q) (5 * n + 11) &&
      decide (final.peakW ≤ 64 * (5 * n + 11)) &&
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
  match (lanczosOracleProg.compiled () ()).exec I n ![q] initial with
  | none => false
  | some final =>
    resources I initial final (lanczosBudget n q)
      (n * (q + 4) + 2 * q + 5) && decide (final.peakW ≤ 64 * (n * (q + 4) + 2 * q + 5)) &&
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

end NLAlibTools.OracleSmoke
