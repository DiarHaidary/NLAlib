/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.Instances.Real.Lemmas

/-!
# A descent direction for the uniform norm

On a compact space, a continuous perturbation with the sign of a function at every point where
its modulus attains the uniform norm decreases the norm after a small positive step. This is the
perturbation step of the necessity half of Chebyshev's equioscillation theorem
(`docs/design/Polynomial-BestApproximation.md`). An upstream candidate for
`Mathlib/Topology/ContinuousMap/Compact.lean`; its proof is deferred.

## Main results

* `ContinuousMap.exists_pos_norm_sub_smul_lt`: the descent step.
-/

@[expose] public section

namespace ContinuousMap

/-- **A descent direction for the uniform norm.** Let $K$ be compact and $e, h$ continuous real
functions on $K$ with $\|e\| > 0$. If $e(x)h(x) > 0$ at every $x$ with
$\lvert e(x) \rvert = \|e\|$, then $\|e - th\| < \|e\|$ for some $t > 0$.
Proof: M, about 45 lines. Near a point with $\lvert e(x) \rvert = \|e\|$, continuity of
$(t, y) \mapsto -2e(y)h(y) + th(y)^2$ (negative at $(0, x)$) gives
$(e(y) - th(y))^2 < \|e\|^2$ for small $t > 0$; near any other point, continuity of
$(t, y) \mapsto \lvert e(y) - th(y) \rvert$ (below $\|e\|$ at $(0, x)$). Compactness makes the
neighbourhood of $t = 0$ uniform (`IsCompact.eventually_forall_of_forall_eventually`), and
`ContinuousMap.norm_lt_iff` concludes. Prototype:
`NLAlib.exists_pos_norm_sub_smul_lt_of_extremal_sign`
(`ForMathlib/Analysis/Normed/UniformApproximation`). -/
theorem exists_pos_norm_sub_smul_lt {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (e h : C(K, ℝ)) (he : 0 < ‖e‖) (hsign : ∀ x, |e x| = ‖e‖ → 0 < e x * h x) :
    ∃ t : ℝ, 0 < t ∧ ‖e - t • h‖ < ‖e‖ := by
  sorry

end ContinuousMap
