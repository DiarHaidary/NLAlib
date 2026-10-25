/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs
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
$\mathbf{A}^{\mathsf{H}}$ is the oracle `(dilation A).mulVec` of the Hermitian dilation: the
query $(\mathbf{y}, \mathbf{x})$ returns
$(\mathbf{A}\mathbf{x}, \mathbf{A}^{\mathsf{H}}\mathbf{y})$, one product with each.
The cost of an algorithm is its number `q` of queries.

The definitions are total. `query i` is defined for every `i : ℕ`; only `i < q` is ever used.

## Main definitions

* `NLAlib.QueryAlgorithm Q R q β`: the algorithm.
* `NLAlib.QueryAlgorithm.history`, `NLAlib.QueryAlgorithm.queryAt`,
  `NLAlib.QueryAlgorithm.transcript`, `NLAlib.QueryAlgorithm.run`: running it against an oracle.
* `NLAlib.QueryAlgorithm.queries`, `NLAlib.QueryAlgorithm.queryMatrix`: the queries recomputed
  from a transcript, and for vector queries the matrix with the queries as columns.
* `NLAlib.QueryAlgorithm.IsNonAdaptive`: the queries do not depend on the responses.
* `NLAlib.QueryAlgorithm.IsMeasurable`, `NLAlib.QueryAlgorithm.IsMeasurableFamily`: measurability
  of an algorithm and joint measurability of a seeded family.
* `NLAlib.QueryAlgorithm.gramSimulation`: a `2q`-query algorithm against the dilation of
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

/-- A query algorithm is **non-adaptive** when each of its `q` queries is the same for every
history: the queries are fixed in advance (the sketching model). -/
def IsNonAdaptive (alg : QueryAlgorithm Q R q β) : Prop :=
  ∀ i < q, ∀ h h' : Fin i → R, alg.query i h = alg.query i h'

/-- A query algorithm is **measurable** when every query map and the output map are measurable
(for the product σ-algebras on histories). Lower bounds quantify over these. -/
structure IsMeasurable [MeasurableSpace Q] [MeasurableSpace R] [MeasurableSpace β]
    (alg : QueryAlgorithm Q R q β) : Prop where
  /-- Each query map is measurable. -/
  measurable_query : ∀ i, Measurable (alg.query i)
  /-- The output map is measurable. -/
  measurable_output : Measurable alg.output

/-- A seeded family of query algorithms, a **randomized algorithm** with seed space `S`, is
measurable when its query and output maps are jointly measurable in the seed and the history. -/
structure IsMeasurableFamily {S : Type*} [MeasurableSpace S] [MeasurableSpace Q]
    [MeasurableSpace R] [MeasurableSpace β] (alg : S → QueryAlgorithm Q R q β) : Prop where
  /-- Each query map is jointly measurable in the seed and the history. -/
  measurable_query : ∀ i, Measurable fun p : S × (Fin i → R) => (alg p.1).query i p.2
  /-- The output map is jointly measurable in the seed and the transcript. -/
  measurable_output : Measurable fun p : S × (Fin q → R) => (alg p.1).output p.2

/-- The **Gram simulation**: from an algorithm with `q` queries to
$\mathbf{A} = \mathbf{X}\mathbf{X}^{\mathsf{H}}$ (`X : Matrix d k 𝕜`), an algorithm with `2q`
queries to the dilation of $\mathbf{X}$ with the same output. Query `2i` is
$(\mathbf{x}_i, \mathbf{0})$, which returns $\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the
`k`-block; query `2i + 1` is $(\mathbf{0}, \mathbf{X}^{\mathsf{H}}\mathbf{x}_i)$, which returns
$\mathbf{X}\mathbf{X}^{\mathsf{H}}\mathbf{x}_i$ in the `d`-block. The original responses are the
`d`-blocks of the odd responses (`QueryAlgorithm.run_gramSimulation`). This is the reduction of
[ZhangEtAl2026, Section 4] from the Wishart oracle to two-sided queries to its factor. -/
def gramSimulation {𝕜 d : Type*} [Zero 𝕜] (k : Type*) (alg : QueryAlgorithm (d → 𝕜) (d → 𝕜) q β) :
    QueryAlgorithm (d ⊕ k → 𝕜) (d ⊕ k → 𝕜) (2 * q) β where
  query j h :=
    if hj : j % 2 = 0 then
      Sum.elim
        (alg.query (j / 2) fun l r => h ⟨2 * l + 1, by have := l.isLt; omega⟩ (Sum.inl r)) 0
    else
      Sum.elim 0 fun r => h ⟨j - 1, by omega⟩ (Sum.inr r)
  output h := alg.output fun l r => h ⟨2 * l + 1, by have := l.isLt; omega⟩ (Sum.inl r)

end QueryAlgorithm

end NLAlib
