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
  have he' : Continuous fun z : ℝ × K => e z.2 := e.continuous.comp continuous_snd
  have hh' : Continuous fun z : ℝ × K => h z.2 := h.continuous.comp continuous_snd
  have hpt : ∀ x : K, ∀ᶠ z : ℝ × K in nhds (0, x),
      0 < z.1 → |e z.2 - z.1 * h z.2| < ‖e‖ := by
    intro x
    by_cases hx : |e x| = ‖e‖
    · have hneg : -2 * e x * h x + 0 * h x ^ 2 < 0 := by
        have := hsign x hx
        nlinarith
      have hc : Continuous fun z : ℝ × K => -2 * e z.2 * h z.2 + z.1 * h z.2 ^ 2 := by
        fun_prop
      have hev : ∀ᶠ z : ℝ × K in nhds (0, x),
          -2 * e z.2 * h z.2 + z.1 * h z.2 ^ 2 < 0 :=
        (hc.continuousAt (x := (0, x))).eventually_lt continuousAt_const hneg
      filter_upwards [hev] with z hz hz0
      have hbound : ‖e z.2‖ ≤ ‖e‖ := e.norm_coe_le_norm z.2
      have h2 : (e z.2) ^ 2 ≤ ‖e‖ ^ 2 := by
        rw [← sq_abs, ← Real.norm_eq_abs]
        exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
      exact abs_lt_of_sq_lt_sq (by nlinarith [mul_neg_of_pos_of_neg hz0 hz]) he.le
    · have hle : |e x| ≤ ‖e‖ := by
        have := e.norm_coe_le_norm x
        rwa [Real.norm_eq_abs] at this
      have hlt : |e x| < ‖e‖ := lt_of_le_of_ne hle hx
      have hc : Continuous fun z : ℝ × K => |e z.2 - z.1 * h z.2| := by
        fun_prop
      have hev : ∀ᶠ z : ℝ × K in nhds (0, x),
          |e z.2 - z.1 * h z.2| < ‖e‖ :=
        (hc.continuousAt (x := (0, x))).eventually_lt continuousAt_const (by simpa using hlt)
      filter_upwards [hev] with z hz _
      exact hz
  have hall : ∀ᶠ t in nhds (0:ℝ), ∀ x ∈ (Set.univ : Set K), 0 < t → |e x - t * h x| < ‖e‖ := by
    refine isCompact_univ.eventually_forall_of_forall_eventually
      (P := fun t y => 0 < t → |e y - t * h y| < ‖e‖) ?_
    intro y _
    exact hpt y
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hall
  refine ⟨δ / 2, by positivity, (ContinuousMap.norm_lt_iff _ he).2 fun x => ?_⟩
  have h1 := hball (show dist (δ / 2) 0 < δ by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by positivity)]; linarith) x (Set.mem_univ x)
    (by positivity)
  rw [ContinuousMap.sub_apply, ContinuousMap.smul_apply, smul_eq_mul, Real.norm_eq_abs]
  exact h1

end ContinuousMap
