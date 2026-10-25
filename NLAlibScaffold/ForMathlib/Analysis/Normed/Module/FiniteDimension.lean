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
  have := FiniteDimensional.proper 𝕜 S
  set K : Set S := Metric.closedBall 0 (2 * ‖x‖) with hK
  have hKc : IsCompact K := isCompact_closedBall _ _
  have hf : Continuous fun p : S => ‖x - (p : E)‖ := by fun_prop
  obtain ⟨p, hpK, hpmin⟩ := hKc.exists_isMinOn ⟨0, by simp [hK]⟩ hf.continuousOn
  have hglobal : ∀ q : S, ‖x - (p : E)‖ ≤ ‖x - (q : E)‖ := by
    intro q
    by_cases hq : q ∈ K
    · exact hpmin hq
    · have hq' : 2 * ‖x‖ < ‖(q : E)‖ := by
        simp only [hK, Metric.mem_closedBall, dist_zero_right, not_le] at hq
        exact hq
      have h0 : ‖x - (p : E)‖ ≤ ‖x‖ := by
        have := hpmin (show (0 : S) ∈ K from by simp [hK])
        simpa using this
      have h1 : ‖(q : E)‖ ≤ ‖x - (q : E)‖ + ‖x‖ := by
        have := norm_sub_norm_le (q : E) x
        rw [norm_sub_rev] at this
        linarith [norm_sub_rev x (q : E)]
      linarith
  refine ⟨p, p.property, le_antisymm (Metric.infDist_le_dist_of_mem p.property) ?_⟩
  refine (Metric.le_infDist ⟨0, S.zero_mem⟩).2 ?_
  intro y hy
  rw [dist_eq_norm, dist_eq_norm]
  exact hglobal ⟨y, hy⟩

end Submodule
