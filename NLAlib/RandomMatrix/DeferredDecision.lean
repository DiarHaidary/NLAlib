/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import NLAlib.Matrix.Basic.Dilation
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Probability.QueryModel.Basic

/-!
# Deferred decision for adaptive matrix–vector queries

After an adaptive algorithm has queried a random matrix, the part of the matrix that the
queries have not touched is, conditionally on the transcript, distributed as before. For a
standard Gaussian $\mathbf{X} \in \mathbb{R}^{d \times k}$ queried through its dilation (products
$\mathbf{X}\mathbf{w}$ and $\mathbf{X}^{\mathsf{H}}\mathbf{u}$), the untouched part is
$\mathbf{E}\mathbf{X}\mathbf{F}$, with $\mathbf{E}$ and $\mathbf{F}$ the orthogonal projectors onto
the complements of the spans of the left queries $\mathbf{u}_i$ and of the right queries
$\mathbf{w}_i$; it can be replaced by an independent copy without changing the joint law of the
transcript and the matrix. This file defines the replaced matrix, `QueryAlgorithm.resample`; the
theorems are in the scaffold (design note `docs/design/Probability-MatvecQueryModel.md` §3.4).

## Main definitions

* `NLAlib.QueryAlgorithm.resample`: the matrix with its unqueried block replaced.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace QueryAlgorithm

variable {𝕜 : Type*} [RCLike 𝕜] {d k β : Type*} [Fintype d] [Fintype k] [DecidableEq d]
  [DecidableEq k] {q : ℕ}

/-- The **resampled matrix** of an algorithm with `q` queries to the dilation of
$\mathbf{X} \in \Bbbk^{d \times k}$: with $\mathbf{E} = \mathbf{I} - \mathbf{P}_{\mathbf{U}}$ and
$\mathbf{F} = \mathbf{I} - \mathbf{P}_{\mathbf{W}}$, where the columns of $\mathbf{U}$ and
$\mathbf{W}$ are the `d`-blocks (left queries) and the `k`-blocks (right queries) of the queries
made on $\mathbf{X}$,
$$\mathsf{resample}(\mathbf{X}, \mathbf{X}') = \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
\mathbf{E}\mathbf{X}'\mathbf{F}\,.$$
It agrees with $\mathbf{X}$ on every query, so the algorithm cannot tell them apart
(`QueryAlgorithm.transcript_resample`). -/
noncomputable def resample (alg : QueryAlgorithm (d ⊕ k → 𝕜) (d ⊕ k → 𝕜) q β)
    (X X' : Matrix d k 𝕜) : Matrix d k 𝕜 :=
  let V := alg.queryMatrix (alg.transcript (dilation X).mulVec)
  let E := 1 - rangeProjector V.toRows₁
  let F := 1 - rangeProjector V.toRows₂
  X - E * X * F + E * X' * F

end QueryAlgorithm

end NLAlib
