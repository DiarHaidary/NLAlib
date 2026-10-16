/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.ContinuousMap.Compact

/-!
# Uniform approximation with a fixed error

A pointwise metric error bound on a set, independent of continuity or polynomial degree.
These declarations are upstream candidates for Mathlib's uniform approximation API.

## Main results

* `Metric.IsUniformApproxOn`: uniform approximation with a specified error.
* `Metric.isUniformApproxOn_iff_dist_le`: the compact continuous-map distance bridge.
-/

@[expose] public section

namespace Metric

variable {α β : Type*} [PseudoMetricSpace β]
variable {g f : α → β} {s t : Set α} {ε η : ℝ}

/-- The function $g$ approximates $f$ on $s$ with metric error at most $\varepsilon$.
No continuity or nonnegative-error assumption is bundled; on the empty set this holds for
any error. This is the fixed-error pointwise condition underlying Mathlib's uniform approximation.
-/
def IsUniformApproxOn (g f : α → β) (s : Set α) (ε : ℝ) : Prop :=
  ∀ x ∈ s, dist (g x) (f x) ≤ ε

/-- Raw-condition constructor and elimination rule for uniform approximation. -/
theorem isUniformApproxOn_iff :
    IsUniformApproxOn g f s ε ↔ ∀ x ∈ s, dist (g x) (f x) ≤ ε := Iff.rfl

/-- Evaluate a uniform approximation bound at a point of its domain. -/
theorem IsUniformApproxOn.apply (h : IsUniformApproxOn g f s ε) {x : α}
    (hx : x ∈ s) : dist (g x) (f x) ≤ ε := h x hx

/-- A uniform approximation remains valid on a smaller set. -/
theorem IsUniformApproxOn.mono_set (h : IsUniformApproxOn g f s ε) (ht : t ⊆ s) :
    IsUniformApproxOn g f t ε := fun _ hx => h _ (ht hx)

/-- A uniform approximation remains valid with a larger error bound. -/
theorem IsUniformApproxOn.mono_error (h : IsUniformApproxOn g f s ε) (hεη : ε ≤ η) :
    IsUniformApproxOn g f s η := fun _ hx => (h _ hx).trans hεη

/-- An approximation error bound is nonnegative when its domain is nonempty. -/
theorem IsUniformApproxOn.nonneg (h : IsUniformApproxOn g f s ε) (hs : s.Nonempty) :
    0 ≤ ε := by
  obtain ⟨x, hx⟩ := hs
  exact (dist_nonneg : 0 ≤ dist (g x) (f x)).trans (h x hx)

/-- On a compact domain, uniform approximation is a continuous-map distance bound.
The nonnegative-error hypothesis covers the empty domain. This is Mathlib's
`ContinuousMap.dist_le` expressed through the fixed-error interface. -/
theorem isUniformApproxOn_iff_dist_le [TopologicalSpace α] [CompactSpace α]
    (g f : C(α, β)) (hε : 0 ≤ ε) :
    IsUniformApproxOn g f Set.univ ε ↔ dist g f ≤ ε := by
  simpa only [IsUniformApproxOn, Set.mem_univ, forall_const] using
    (ContinuousMap.dist_le hε (f := g) (g := f)).symm

end Metric
