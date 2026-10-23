/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
import NLAlib.Estimation.Trace.HutchPlusPlusProgram

/-!
# Running programs in Lean with `Float`

A value semantics over `Float` (`NLAlibTools.floatSem`) and an interpretation with a dense
oracle (`NLAlibTools.floatInterp`), so that the library's programs run in Lean with
`NLAlib.Computation.exec` (the builder's statement) and with `NLAlib.Computation.Prog.exec` (the
registered tree), which agree on the rows below. Counts are (flops, loads, matvecs): one flop per
binary operation and square root. The runs below reproduce the Hutch++ rows of the table of
`docs/design/Computation.md` §6 on a $5 \times 5$ symmetric matrix. This is a tool for
differential testing, not part of the library: nothing here is proved about `Float`.
-/

-- A tools file: `#eval` and `#guard` are its point.
set_option linter.hashCommand false

open NLAlib NLAlib.Computation

namespace NLAlibTools

/-- Floating-point arithmetic in `Float`; division by zero and the square root of a negative
number fail; word operations fail. -/
def floatSem : ScalarSem Unit Float where
  lit _ q := some (Float.ofInt q.num / Float.ofNat q.den)
  bin _ b x y := match b with
    | .add => some (x + y) | .sub => some (x - y) | .mul => some (x * y)
    | .div => if y == 0 then none else some (x / y)
    | _ => none
  un _ u x := match u with
    | .neg => some (-x) | .conj => some x | .re => some x
    | .sqrt => if x < 0 then none else some x.sqrt
    | .bnot => none
  cmp _ c x y := match c with
    | .eq => some (x == y) | .lt => some (x < y) | .le => some (decide (x ≤ y))
  convert _ _ x := some x

/-- The charge (flops, loads, matvecs). -/
def floatCharge : OpKind Unit Unit → ℕ × ℕ × ℕ
  | .bin _ _ => (1, 0, 0)
  | .un _ .sqrt => (1, 0, 0)
  | .load _ _ => (0, 1, 0)
  | .matvec _ _ => (0, 0, 1)
  | _ => (0, 0, 0)

/-- The dense oracle of a matrix given by its rows, on column-major blocks. -/
def denseOracle (A : Array (Array Float)) (cols : ℕ) (X : Array Float) : Option (Array Float) :=
  let N := A.size
  some <| (List.range (N * cols)).toArray.map fun t =>
    (List.range N).foldl (fun acc j => acc + (A[t % N]!)[j]! * X[j + N * (t / N)]!) 0

/-- The interpretation: `Float` arithmetic, the dense oracle of `A`, the tape a list. -/
def floatInterp (A : Array (Array Float)) (tape : List Float) :
    Interp Unit Unit Float (ℕ × ℕ × ℕ) where
  sem := floatSem
  charge := floatCharge
  tape _ i := tape.getD i 0
  oracle _ cols X := denseOracle A cols X
  height _ := A.size
  rom _ := none
  romSize _ := 0
  width _ := 64

/-- The initial state with the given buffers, counted from the start. -/
def initState (bufs : List (Array (Option Float))) : St Unit Float (ℕ × ℕ × ℕ) where
  store := (bufs.map fun b => ((), b)).toArray
  pos _ := 0
  cnt := 0
  cur _ := (bufs.map Array.size).sum
  peak _ := (bufs.map Array.size).sum
  curW := 64 * (bufs.map Array.size).sum
  peakW := 64 * (bufs.map Array.size).sum

/-- The test matrix of the design note: $5 \times 5$ symmetric, trace $15$. -/
def A₀ : Array (Array Float) :=
  #[#[4, 1, 0, 0, 1], #[1, 3, 1, 0, 0], #[0, 1, 2, 1, 0], #[0, 0, 1, 5, 1], #[1, 0, 0, 1, 1]]

/-- Buffer `b` of a state, uninitialised cells shown as `0`. -/
def showBuf (st : St Unit Float (ℕ × ℕ × ℕ)) (b : ℕ) : List Float :=
  ((st.store[b]?).map fun x => x.2.toList.map fun v => v.getD 0).getD []

/-- A deterministic sign tape. -/
def signTape : List Float :=
  (List.range 100).map fun i => if (i * i * 31 + 7 * i + 3) % 11 < 5 then -1.0 else 1.0

/-- Run `NLAlib.hutchppProg` on `A₀` with the sign tape: the output, the counts and the peak. -/
def hutchppRun (k ℓ : ℕ) : Option (List Float × (ℕ × ℕ × ℕ) × ℕ) := do
  let prog : Stmt Unit Unit ℕ ℕ :=
    (hutchppProg () () .rademacher (.const 5) (.const k) (.const ℓ) ⟨0, .const 0⟩).run
  let st ← exec (floatInterp A₀ signTape) prog (initState [Array.replicate 1 none])
  some (showBuf st 0, st.cnt, st.peak ())

/-- Run the registered tree `NLAlib.hutchppProg.compiled` on `A₀` with the sign tape, by
`NLAlib.Computation.Prog.exec`: the output, the counts and the peak. -/
def hutchppTreeRun (k ℓ : ℕ) : Option (List Float × (ℕ × ℕ × ℕ) × ℕ) := do
  let st ← (hutchppProg.compiled (P := Unit) (ι := Unit) () () .rademacher).exec
    (floatInterp A₀ signTape) 5 ![k, ℓ] (initState [Array.replicate 1 none])
  some (showBuf st 0, st.cnt, st.peak ())

#eval (hutchppRun 2 1, hutchppRun 5 1)

-- The builder's run agrees with the run of the registered tree (`Prog.exec`) on the §6 rows.
#guard hutchppRun 2 1 == hutchppTreeRun 2 1
#guard hutchppRun 5 1 == hutchppTreeRun 5 1

-- The counts and peaks of the design note's table (§6).
#guard (hutchppRun 2 1).map (fun r => r.2) = some ((127, 2, 5), 34)
#guard (hutchppRun 5 1).map (fun r => r.2) = some ((448, 2, 11), 64)
-- With `k = N` the sketch captures the range and Hutch++ returns `tr A = 15`.
#guard ((hutchppRun 5 1).bind fun r => r.1.head?).all fun v => (v - 15).abs < 1e-9
#guard ((hutchppRun 2 1).bind fun r => r.1.head?).all fun v => (v - 19.326978).abs < 1e-5

end NLAlibTools
