/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Exact
public import NLAlib.Computation.Subst

/-!
# Access models: results whose program cannot see the data

A result about the cost of an algorithm is an instance of an access model: a definition that
takes the program first, as a family of programs built from the sizes alone, and quantifies over
the data afterwards. The binder order is the guarantee, as in CSLib's query model (its
`UpperBound`, in `Cslib/Algorithms/Lean/Query/Bounds.lean`, fixes the program before the oracle;
CSLib is not a dependency): the program cannot depend on the matrix, the tape or the declared
inputs, because they are bound after it, and the counts and the memory are functions of the sizes
alone. Lean's kernel checks this when it checks the statement; no script is involved.

* `NLAlib.Computation.ProgFamily P ι r b`: a program family, generic in both variable sorts, built
  from the oracle dimension $N$ and $r$ further sizes (as index expressions) and the handles of $b$
  declared buffers. `NLAlib.Computation.ProgFamily.inst` is the statement that runs at given sizes.
* `NLAlib.Computation.MatrixFree`: the matrix-free model. For every size satisfying the size
  condition, every declared input, every $N \times N$ matrix $\mathbf{A}$ (every oracle name means
  $\mathbf{A}$) and every tape, the program runs under exact arithmetic within the counts and the
  memory, from the initial state that holds the declared buffers only, and satisfies the
  postcondition.
* `NLAlib.Computation.StoredEntries`: the stored-entries model. The data are entries held as
  read-only data (counted reads, counted constant memory), and there is no oracle: every oracle
  call fails.

The probabilistic companion of the matrix-free model, whose tape has the law the definition
fixes, is `NLAlib.Computation.MatrixFreeProb` (`NLAlib/RandomMatrix/Tape.lean`, where the laws
of draws live). What each model proves and what it trusts is in `docs/design/Computation.md`,
"Guarantees: what is proved and what is trusted".

## Main definitions

* `NLAlib.Computation.ProgFamily`, `NLAlib.Computation.ProgFamily.inst`,
  `NLAlib.Computation.ProgFamily.substOracle`.
* `NLAlib.Computation.storedInterp`: the interpretation of the stored-entries model.
* `NLAlib.Computation.MatrixFree`, `NLAlib.Computation.StoredEntries`.

## Main results

* `NLAlib.Computation.exec_exactInterp_eq_of_exec_eq_some_of_cnt_load_le`: a run that makes no
  oracle call is the same for every matrix.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib.Computation

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- **A program family**: from the oracle dimension $N$ and $r$ further sizes, as index
expressions, and the handles of $b$ declared buffers, a statement generic in both variable sorts.
It receives no data: an access model applies it to the sizes alone and quantifies over the data
afterwards. -/
abbrev ProgFamily (P ι : Type) (r b : ℕ) : Type 1 :=
  (VB VI : Type) → IExp VI → (Fin r → IExp VI) → (Fin b → VB) → Stmt P ι VB VI

namespace ProgFamily

variable {r b : ℕ}

/-- The statement that runs at the sizes $N$ and $n$: both variable sorts `ℕ`, the sizes
constants, declared buffer $j$ at handle $j$ (its position in the initial store). -/
def inst (prog : ProgFamily P ι r b) (N : ℕ) (n : Fin r → ℕ) : Stmt P ι ℕ ℕ :=
  prog ℕ ℕ (.const N) (fun i => .const (n i)) fun j => (j : ℕ)

/-- A program family with its oracle calls replaced by an implementation family, which may use
the oracle dimension. -/
def substOracle {ι' : Type} (prog : ProgFamily P ι r b)
    (impl : (VB VI : Type) → IExp VI → ι → P → VB → IExp VI → VB → IExp VI → IExp VI →
      Stmt P ι' VB VI) : ProgFamily P ι' r b :=
  fun VB VI N n h => (prog VB VI N n h).substOracle (impl VB VI N)

end ProgFamily

/-- **The stored-entries interpretation**: exact arithmetic over $\Bbbk$ (`exactSem`), the
standard charge (one per operation), the tape $\xi$, no oracle (every oracle call fails), and the
first `len` entries of `vals` as read-only data, counted as `len` cells of constant memory at
tag `p₀`; width $0$. -/
noncomputable def storedInterp (len : ℕ) (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ) (p₀ : P) :
    Interp P ι 𝕜 (OpCount P ι) where
  sem := exactSem
  charge k := Finsupp.single k 1
  tape d i := (ξ d i : 𝕜)
  oracle _ _ _ := none
  height _ := 0
  rom e := if e < len then some (vals e) else none
  romSize q := if q = p₀ then len else 0
  width _ := 0

/-- **The matrix-free model.** The program family `prog` runs, for all sizes $N$, $n$ satisfying
`valid`, every declared input $x$ (of type `X N n`), every $N \times N$ matrix $\mathbf{A}$ and
every tape $\xi$, under exact arithmetic with every oracle name meaning $\mathbf{A}$ and the tape
$\xi$ (`exactInterp`, the standard charge), from the initial state that holds the declared
buffers `inputs N n x` at tag `p` and nothing else, within the counts `cost N n` and the memory
`mem N n`, and ends in a state satisfying `post N n x A ξ`.

The program is bound before the matrix, the tape and the declared inputs, and the counts and the
memory are functions of the sizes: the program learns $\mathbf{A}$ only through oracle calls,
the tape only through draws, and the inputs only by reading the store. -/
def MatrixFree {r b : ℕ} (p : P) (prog : ProgFamily P ι r b) (valid : ℕ → (Fin r → ℕ) → Prop)
    (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜))
    (cost : ℕ → (Fin r → ℕ) → OpCount P ι) (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (post : (N : ℕ) → (n : Fin r → ℕ) → X N n → Matrix (Fin N) (Fin N) 𝕜 → (Dist → ℕ → ℝ) →
      St P 𝕜 (OpCount P ι) → Prop) : Prop :=
  ∀ N n, valid N n → ∀ (x : X N n) (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ),
    RunsWithin (exactInterp (fun _ => A) ξ) (prog.inst N n)
      (inputState p (List.ofFn (inputs N n x))) (cost N n) (mem N n) (post N n x A ξ)

/-- **The stored-entries model.** The program family `prog` runs, for all sizes $N$, $n$
satisfying `valid`, every declared input $x$, all entries `vals` and every tape $\xi$, under
`storedInterp (len N n) vals ξ p` (exact arithmetic, the standard charge, no oracle, the first
`len N n` entries of `vals` as read-only data read one cell per counted read and counted as
constant memory), from the initial state that holds the declared buffers `inputs N n x` at tag
`p` and nothing else, within the counts `cost N n` and the memory `mem N n` (which includes the
read-only data), and ends in a state satisfying `post N n x vals ξ`.

The program is bound before the entries, the tape and the declared inputs. -/
def StoredEntries {r b : ℕ} (p : P) (prog : ProgFamily P ι r b)
    (valid : ℕ → (Fin r → ℕ) → Prop) (X : ℕ → (Fin r → ℕ) → Type)
    (inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option 𝕜))
    (len : ℕ → (Fin r → ℕ) → ℕ) (cost : ℕ → (Fin r → ℕ) → OpCount P ι)
    (mem : ℕ → (Fin r → ℕ) → P → ℕ)
    (post : (N : ℕ) → (n : Fin r → ℕ) → X N n → (ℕ → 𝕜) → (Dist → ℕ → ℝ) →
      St P 𝕜 (OpCount P ι) → Prop) : Prop :=
  ∀ N n, valid N n → ∀ (x : X N n) (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ),
    RunsWithin (storedInterp (len N n) vals ξ p) (prog.inst N n)
      (inputState p (List.ofFn (inputs N n x))) (cost N n) (mem N n) (post N n x vals ξ)

/-- A run under the exact interpretation of $\mathbf{A}$ that makes no oracle call (its load
counts do not grow) is the same run under the exact interpretation of any other matrix
$\mathbf{A}'$ of the same size: the oracle is the run's only access to the matrix. -/
theorem exec_exactInterp_eq_of_exec_eq_some_of_cnt_load_le {N : ℕ}
    {A A' : ι → Matrix (Fin N) (Fin N) 𝕜} {ξ : Dist → ℕ → ℝ} {s : Stmt P ι ℕ ℕ}
    {st st' : St P 𝕜 (OpCount P ι)} (h : exec (exactInterp A ξ) s st = some st')
    (hl : ∀ p o, st'.cnt (.load p o) ≤ st.cnt (.load p o)) :
    exec (exactInterp A' ξ) s st = some st' :=
  exec_eq_of_exec_eq_some_of_cnt_load_le (I := exactInterp A ξ) (fun _ => rfl)
    (exactInterp (P := P) A' ξ).oracle s h hl

end NLAlib.Computation
