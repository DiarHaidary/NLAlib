/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Nearest points in finite-dimensional subspaces

A finite-dimensional subspace of a normed space over a proper field contains a nearest point to
every vector of the space; the space itself need not be finite-dimensional or complete. This is
the existence step of best uniform polynomial approximation
(`docs/design/Polynomial-BestApproximation.md`). An upstream candidate for
`Mathlib/Analysis/Normed/Module/FiniteDimension.lean`, next to
`IsCompact.exists_infDist_eq_dist`; its proof is deferred.

## Main results

* `Submodule.exists_infDist_eq_dist`: nearest points exist.
-/

@[expose] public section

namespace Submodule

/-- **Nearest points in finite-dimensional subspaces.** If $S$ is a finite-dimensional subspace
of a normed space $E$ over a proper nontrivially normed field, every $x \in E$ has a nearest
point in $S$: some $y \in S$ has $\operatorname{dist}(x, y) = \operatorname{dist}(x, S)$.
Proof: M, about 25 lines. The closed ball of radius $2\|x\|$ about $0$ in $S$ is compact
(`FiniteDimensional.proper`, `isCompact_closedBall`); minimise the continuous
$y \mapsto \|x - y\|$ on it (`IsCompact.exists_isMinOn`, with $0$ in the ball); outside the ball
$\|x - y\| \ge \|y\| - \|x\| > \|x\| = \|x - 0\|$. Then `Metric.le_infDist` and
`Metric.infDist_le_dist_of_mem`. Prototype: `NLAlib.exists_norm_sub_eq_infDist_of_finiteDimensional`
(`ForMathlib/Analysis/Normed/Approximation`), over $\mathbb{R}$. -/
theorem exists_infDist_eq_dist {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S]
    (x : E) : ∃ y ∈ S, Metric.infDist x (S : Set E) = dist x y := by
  sorry

end Submodule
