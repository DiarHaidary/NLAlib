/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Probability.QueryModel.Basic

/-!
# Deferred decision for adaptive matrix–vector queries

After an adaptive algorithm has queried a random matrix, the part of the matrix that the
queries have not touched is, conditionally on the transcript, distributed as before. For a
standard Gaussian $\mathbf{X} \in \mathbb{R}^{d \times k}$ queried through `twoSidedMulVec`
(products $\mathbf{X}\mathbf{w}$ and $\mathbf{X}^{\mathsf{H}}\mathbf{u}$), the untouched part is
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

/-- The **resampled matrix** of an algorithm with `q` pair queries to `twoSidedMulVec X`,
$\mathbf{X} \in \Bbbk^{d \times k}$: with $\mathbf{E} = \mathbf{I} - \mathbf{P}_{\mathbf{U}}$ and
$\mathbf{F} = \mathbf{I} - \mathbf{P}_{\mathbf{W}}$, where the columns of $\mathbf{U}$ and
$\mathbf{W}$ are the left parts and the right parts of the queries made on $\mathbf{X}$
(`QueryAlgorithm.leftQueryMatrix`, `QueryAlgorithm.rightQueryMatrix`),
$$\mathsf{resample}(\mathbf{X}, \mathbf{X}') = \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
\mathbf{E}\mathbf{X}'\mathbf{F}\,.$$
It agrees with $\mathbf{X}$ on every query, so the algorithm cannot tell them apart
(`QueryAlgorithm.transcript_resample`). -/
noncomputable def resample (alg : QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) q β)
    (X X' : Matrix d k 𝕜) : Matrix d k 𝕜 :=
  let τ := alg.transcript (twoSidedMulVec X)
  let E := 1 - rangeProjector (alg.leftQueryMatrix τ)
  let F := 1 - rangeProjector (alg.rightQueryMatrix τ)
  X - E * X * F + E * X' * F

end QueryAlgorithm

end NLAlib
