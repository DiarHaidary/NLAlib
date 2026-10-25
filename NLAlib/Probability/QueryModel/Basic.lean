/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.MeasureTheory.MeasurableSpace.Pi
public import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Adaptive query algorithms

A deterministic algorithm that makes `q` adaptive queries to an oracle `f : Q → R` and then
outputs a value of type `β`: the `i`-th query is a function of the first `i` responses, and the
output is a function of all `q` of them. Randomness is not part of the object: a randomized
algorithm is a family `S → QueryAlgorithm Q R q β` indexed by a seed, and a random input is a
random variable on the probability space, so a lower bound is a statement about one product
probability space and needs no Markov kernels (design note
`docs/design/Probability-MatvecQueryModel.md` §2, decision QUERY-MODEL-SCOPE (a)).

The matrix–vector query model is the oracle `A.mulVec` of a matrix `A : Matrix m n 𝕜`: a query is
a vector $\mathbf{x}$, its response $\mathbf{A}\mathbf{x}$. Access to both $\mathbf{A}$ and
$\mathbf{A}^{\mathsf{H}}$ is the oracle `twoSidedMulVec A`: a query is a pair
$(\mathbf{x}, \mathbf{y})$ and its response
$(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$. Either side may be zero, and a zero
side costs nothing: `rightCount τ` and `leftCount τ` count the rounds whose right part
$\mathbf{x}$, respectively left part $\mathbf{y}$, is nonzero, so separate budgets for products
with $\mathbf{A}$ and with $\mathbf{A}^{\mathsf{H}}$ are hypotheses `rightCount τ ≤ q_R`,
`leftCount τ ≤ q_L` (design note `docs/design/Probability-MatvecQueryModel.md` §2.1, decisions
OQ2 (c), OQ9). The number `q` of rounds bounds both.

The definitions are total. `query i` is defined for every `i : ℕ`; only `i < q` is ever used.

## Main definitions

* `NLAlib.QueryAlgorithm Q R q β`: the algorithm.
* `NLAlib.QueryAlgorithm.history`, `NLAlib.QueryAlgorithm.queryAt`,
  `NLAlib.QueryAlgorithm.transcript`, `NLAlib.QueryAlgorithm.run`: running it against an oracle.
* `NLAlib.QueryAlgorithm.truncate`: the first `i` queries as an algorithm of its own.
* `NLAlib.QueryAlgorithm.queries`, `NLAlib.QueryAlgorithm.queryMatrix`: the queries recomputed
  from a transcript, and for vector queries the matrix with the queries as columns.
* `NLAlib.twoSidedMulVec`: the two-sided matrix–vector oracle.
* `NLAlib.QueryAlgorithm.rightQueryMatrix`, `NLAlib.QueryAlgorithm.leftQueryMatrix`,
  `NLAlib.QueryAlgorithm.rightCount`, `NLAlib.QueryAlgorithm.leftCount`,
  `NLAlib.QueryAlgorithm.IsOneSided`: the two sides of pair queries and their costs.
* `NLAlib.QueryAlgorithm.IsNonAdaptive`: the queries do not depend on the responses.
* `NLAlib.QueryAlgorithm.IsMeasurable`, `NLAlib.QueryAlgorithm.IsMeasurableFamily`: measurability
  of an algorithm and joint measurability of a seeded family.
* `NLAlib.QueryAlgorithm.gramSimulation`: a `2q`-round algorithm against the two-sided oracle of
  $\mathbf{X}$ that runs a `q`-query algorithm against $\mathbf{X}\mathbf{X}^{\mathsf{H}}$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- A deterministic **adaptive query algorithm** with `q` queries to an oracle `Q → R` and output
in `β`. The `i`-th query is `query i` applied to the first `i` responses; the output is `output`
applied to all `q` responses. Queries with index $i \ge q$ are never made. A randomized algorithm is
a family `S → QueryAlgorithm Q R q β` indexed by a seed (`QueryAlgorithm.IsMeasurableFamily`). -/
structure QueryAlgorithm (Q R : Type*) (q : ℕ) (β : Type*) where
  /-- The `i`-th query as a function of the first `i` responses. -/
  query : (i : ℕ) → (Fin i → R) → Q
  /-- The output as a function of the `q` responses. -/
  output : (Fin q → R) → β

/-- The **two-sided matrix–vector oracle** of $\mathbf{A} \in \Bbbk^{m \times n}$: the query
$(\mathbf{x}, \mathbf{y})$ returns $(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$,
one product with $\mathbf{A}$ (the right part) and one with $\mathbf{A}^{\mathsf{H}}$ (the left
part). A zero part returns zero and costs nothing (`QueryAlgorithm.rightCount`,
`QueryAlgorithm.leftCount`). -/
def twoSidedMulVec {𝕜 m n : Type*} [Fintype m] [Fintype n] [NonUnitalNonAssocSemiring 𝕜] [Star 𝕜]
    (A : Matrix m n 𝕜) (v : (n → 𝕜) × (m → 𝕜)) : (m → 𝕜) × (n → 𝕜) :=
  (A *ᵥ v.1, Aᴴ *ᵥ v.2)

namespace QueryAlgorithm

variable {Q R β : Type*} {q : ℕ}

/-- The first `i` responses of the algorithm run against the oracle `f`, by recursion on `i`:
the next query is computed from the responses so far and its response appended. -/
def history (alg : QueryAlgorithm Q R q β) (f : Q → R) : (i : ℕ) → Fin i → R
  | 0 => Fin.elim0
  | i + 1 => Fin.snoc (α := fun _ => R) (history alg f i) (f (alg.query i (history alg f i)))

/-- The `i`-th query the algorithm makes when run against the oracle `f`. -/
def queryAt (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) : Q :=
  alg.query i (alg.history f i)

/-- The **transcript**: the `q` responses of the algorithm run against the oracle `f`. -/
def transcript (alg : QueryAlgorithm Q R q β) (f : Q → R) : Fin q → R :=
  alg.history f q

/-- The output of the algorithm run against the oracle `f`. -/
def run (alg : QueryAlgorithm Q R q β) (f : Q → R) : β :=
  alg.output (alg.transcript f)

/-- The queries recomputed from a list `τ` of `q` responses: the `j`-th is `query j` applied to
the first `j` entries of `τ`. On the transcript they are the queries made
(`QueryAlgorithm.queryAt_eq_queries_transcript`). -/
def queries (alg : QueryAlgorithm Q R q β) (τ : Fin q → R) (j : Fin q) : Q :=
  alg.query j fun l => τ (Fin.castLE j.isLt.le l)

/-- For vector queries, the **query matrix** of a transcript `τ`: its column `j` is the `j`-th
query `alg.queries τ j`. -/
def queryMatrix {𝕜 n : Type*} (alg : QueryAlgorithm (n → 𝕜) R q β) (τ : Fin q → R) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun r j => alg.queries τ j r

section TwoSided

variable {𝕜 m n : Type*}

/-- For pair queries $(\mathbf{x}, \mathbf{y})$ (`twoSidedMulVec`), the **right query matrix**
of a transcript `τ`: its column `j` is the right part $\mathbf{x}_j$ of the `j`-th query. -/
def rightQueryMatrix (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    Matrix n (Fin q) 𝕜 :=
  Matrix.of fun r j => (alg.queries τ j).1 r

/-- For pair queries $(\mathbf{x}, \mathbf{y})$ (`twoSidedMulVec`), the **left query matrix** of
a transcript `τ`: its column `j` is the left part $\mathbf{y}_j$ of the `j`-th query. -/
def leftQueryMatrix (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    Matrix m (Fin q) 𝕜 :=
  Matrix.of fun r j => (alg.queries τ j).2 r

variable [Zero 𝕜]

/-- The **number of right products** of a transcript `τ`: the rounds whose right part
$\mathbf{x}_j$ is nonzero, each one product $\mathbf{A}\mathbf{x}_j$. A budget of $q_R$ products
with $\mathbf{A}$ is the hypothesis `∀ τ, alg.rightCount τ ≤ q_R`. -/
noncomputable def rightCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    ℕ :=
  {j : Fin q | (alg.queries τ j).1 ≠ 0}.ncard

/-- The **number of left products** of a transcript `τ`: the rounds whose left part
$\mathbf{y}_j$ is nonzero, each one product $\mathbf{A}^{\mathsf{H}}\mathbf{y}_j$. A budget of
$q_L$ products with $\mathbf{A}^{\mathsf{H}}$ is the hypothesis `∀ τ, alg.leftCount τ ≤ q_L`. -/
noncomputable def leftCount (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) (τ : Fin q → R) :
    ℕ :=
  {j : Fin q | (alg.queries τ j).2 ≠ 0}.ncard

/-- A pair-query algorithm is **one-sided** when it makes no product with
$\mathbf{A}^{\mathsf{H}}$: every left part is zero, for every transcript. -/
def IsOneSided (alg : QueryAlgorithm ((n → 𝕜) × (m → 𝕜)) R q β) : Prop :=
  ∀ τ, alg.leftCount τ = 0

end TwoSided

/-- The algorithm **truncated** to its first `i` queries, with no output: its transcript is the
history of length `i` (`QueryAlgorithm.transcript_truncate`). Inductions over the number of
queries (deferred decision) run through it. -/
def truncate (alg : QueryAlgorithm Q R q β) (i : ℕ) : QueryAlgorithm Q R i Unit where
  query := alg.query
  output _ := ()

/-- The truncated algorithm has the same histories. -/
@[simp]
theorem history_truncate (alg : QueryAlgorithm Q R q β) (f : Q → R) (i j : ℕ) :
    (alg.truncate i).history f j = alg.history f j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [history, history, ih]; rfl

/-- The transcript of the truncated algorithm is the history of length `i`. -/
@[simp]
theorem transcript_truncate (alg : QueryAlgorithm Q R q β) (f : Q → R) (i : ℕ) :
    (alg.truncate i).transcript f = alg.history f i :=
  history_truncate alg f i i

/-- A query algorithm is **non-adaptive** when each of its `q` queries is the same for every
history: the queries are fixed in advance (the sketching model). For pair queries both parts are
fixed in advance: a one-pass algorithm with $\ell$ products with $\mathbf{A}$ and $p$ with
$\mathbf{A}^{\mathsf{H}}$ is `IsNonAdaptive` with `rightCount ≤ ℓ` and `leftCount ≤ p`. -/
def IsNonAdaptive (alg : QueryAlgorithm Q R q β) : Prop :=
  ∀ i < q, ∀ h h' : Fin i → R, alg.query i h = alg.query i h'

/-- A query algorithm is **measurable** when each of its `q` query maps and the output map are
measurable (for the product σ-algebras on histories); the unused maps `query i`, $i \ge q$, are
unconstrained. Lower bounds quantify over these. -/
structure IsMeasurable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β]
    (alg : QueryAlgorithm Q R q β) : Prop where
  /-- Each of the `q` query maps is measurable. -/
  measurable_query : ∀ i < q, Measurable (alg.query i)
  /-- The output map is measurable. -/
  measurable_output : Measurable alg.output

/-- A seeded family of query algorithms, a **randomized algorithm** with seed space `S`, is
measurable when its query and output maps are jointly measurable in the seed and the history. -/
structure IsMeasurableFamily {S : Type*} [MeasurableSpace S] [MeasurableSpace Q]
    [MeasurableSpace R] [MeasurableSpace β] (alg : S → QueryAlgorithm Q R q β) : Prop where
  /-- Each of the `q` query maps is jointly measurable in the seed and the history. -/
  measurable_query : ∀ i < q, Measurable fun p : S × (Fin i → R) => (alg p.1).query i p.2
  /-- The output map is jointly measurable in the seed and the transcript. -/
  measurable_output : Measurable fun p : S × (Fin q → R) => (alg p.1).output p.2

/-- The **Gram simulation**: from an algorithm with `q` queries to
$\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$ (`X : Matrix d k 𝕜`), an algorithm with `2q`
rounds against `twoSidedMulVec X` with the same output. Round `2i` is the left query
$(\mathbf{0}, \mathbf{x}_i)$, which returns $\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the second
component; round `2i + 1` is the right query $(\mathbf{X}^{\mathsf{H}}\mathbf{x}_i, \mathbf{0})$,
which returns $\mathbf{X}\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the first. So it makes at most
`q` products with each of $\mathbf{X}$ and $\mathbf{X}^{\mathsf{H}}$. The original responses are the
first components of the odd responses (`QueryAlgorithm.run_gramSimulation`). It makes explicit
what [ZhangEtAl2026, Section 4.1] uses implicitly: the analysis works with the factor
$\mathbf{X}$ while the queries are to $\mathbf{X}\mathbf{X}^{\mathsf{T}}$. -/
def gramSimulation {𝕜 d : Type*} [Zero 𝕜] (k : Type*) (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) :
    QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) (2 * q) β where
  query j h :=
    if hj : j % 2 = 0 then
      (0, alg.query (j / 2) fun l => (h ⟨2 * l + 1, by have := l.isLt; omega⟩).1)
    else
      ((h ⟨j - 1, by omega⟩).2, 0)
  output h := alg.output fun l => (h ⟨2 * l + 1, by have := l.isLt; omega⟩).1

end QueryAlgorithm

end NLAlib
