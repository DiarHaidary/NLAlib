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
`IsCompact.exists_infDist_eq_dist`.

## Main results

* `Submodule.exists_infDist_eq_dist`: nearest points exist.
-/

@[expose] public section

namespace Submodule

/-- **Nearest points in finite-dimensional subspaces.** If $S$ is a finite-dimensional subspace
of a normed space $E$ over a proper nontrivially normed field, every $x \in E$ has a nearest
point in $S$: some $y \in S$ has $\operatorname{dist}(x, y) = \operatorname{dist}(x, S)$. -/
theorem exists_infDist_eq_dist {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] (S : Submodule 𝕜 E) [FiniteDimensional 𝕜 S]
    (x : E) : ∃ y ∈ S, Metric.infDist x (S : Set E) = dist x y := by
  have := FiniteDimensional.proper 𝕜 S
  -- minimise `‖x - p‖` over the compact ball of radius `2‖x‖` in `S`; `0` is in the ball
  obtain ⟨p, -, hpmin⟩ := (isCompact_closedBall (0 : S) (2 * ‖x‖)).exists_isMinOn ⟨0, by simp⟩
    (by fun_prop : Continuous fun p : S => ‖x - (p : E)‖).continuousOn
  have h0 : ‖x - (p : E)‖ ≤ ‖x‖ := by simpa using hpmin (show (0 : S) ∈ _ by simp)
  refine ⟨p, p.2, le_antisymm (Metric.infDist_le_dist_of_mem p.2)
    ((Metric.le_infDist ⟨0, S.zero_mem⟩).2 fun y hy => ?_)⟩
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hyK : (⟨y, hy⟩ : S) ∈ Metric.closedBall 0 (2 * ‖x‖)
  · exact hpmin hyK
  · -- outside the ball, `‖x - y‖ ≥ ‖y‖ - ‖x‖ > ‖x‖`
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hyK
    linarith [norm_sub_norm_le y x, norm_sub_rev x y, show ‖(⟨y, hy⟩ : S)‖ = ‖y‖ from rfl]

end Submodule
