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
  have hle : ∀ y, |e y| ≤ ‖e‖ := fun y => by simpa using e.norm_coe_le_norm y
  -- near each `(0, x)`, a step `t > 0` keeps `|e - t h| < ‖e‖`
  have hpt : ∀ x : K, ∀ᶠ z : ℝ × K in nhds (0, x),
      0 < z.1 → |e z.2 - z.1 * h z.2| < ‖e‖ := by
    intro x
    by_cases hx : |e x| = ‖e‖
    · -- at an extremal point, `(e - t h)² = e² + t (-2 e h + t h²)` and the bracket is `< 0`
      have hev : ∀ᶠ z : ℝ × K in nhds (0, x), -2 * e z.2 * h z.2 + z.1 * h z.2 ^ 2 < 0 :=
        ((by fun_prop : Continuous fun z : ℝ × K => -2 * e z.2 * h z.2 + z.1 * h z.2 ^ 2)
          |>.continuousAt (x := (0, x))).eventually_lt continuousAt_const
          (by nlinarith [hsign x hx])
      filter_upwards [hev] with z hz hz0
      refine abs_lt_of_sq_lt_sq ?_ he.le
      nlinarith [mul_neg_of_pos_of_neg hz0 hz, sq_abs (e z.2),
        pow_le_pow_left₀ (abs_nonneg _) (hle z.2) 2]
    · -- elsewhere `|e x| < ‖e‖`, and `|e - t h|` is continuous in `(t, y)`
      filter_upwards [((by fun_prop : Continuous fun z : ℝ × K => |e z.2 - z.1 * h z.2|)
        |>.continuousAt (x := (0, x))).eventually_lt continuousAt_const
        (by simpa using (hle x).lt_of_ne hx)] with z hz _ using hz
  -- compactness makes the step uniform in `x`
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1
    (isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun t y => 0 < t → |e y - t * h y| < ‖e‖) fun y _ => hpt y)
  refine ⟨δ / 2, by positivity, (ContinuousMap.norm_lt_iff _ he).2 fun x => ?_⟩
  simpa using hball (by simpa [abs_of_pos hδ] using half_lt_self hδ) x (Set.mem_univ x)
    (by positivity)

end ContinuousMap
