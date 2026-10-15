/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Order.PiLex
public import Mathlib.Topology.Algebra.Module.FiniteDimension
public import Mathlib.Topology.Order.Compact

/-!
# Lexicographically least points of compact sets

A nonempty compact set in a finite-dimensional real topological vector space has a point whose
coordinates in a given basis are lexicographically least: minimise the first coordinate, then the
second over the minimisers of the first, and so on. Each step minimises a continuous function over
a nonempty compact set. The point is unique, so it is a canonical choice from the set; it is how
`NLAlib.svdU` and `NLAlib.svdV` choose a singular value decomposition. Upstream candidate for
`Mathlib.Topology.Algebra.Module.FiniteDimension`.

## Main results

* `IsCompact.exists_forall_toLex_equivFun_le`: a nonempty compact set has a lexicographically least
  point.
-/

@[expose] public section

open Module

/-- Two tuples with the same first entry compare lexicographically as their tails do. -/
private theorem Fin.toLex_le_toLex_of_tail {N : ℕ} {x y : Fin (N + 1) → ℝ} (h0 : x 0 = y 0)
    (h : toLex (Fin.tail x) ≤ toLex (Fin.tail y)) : toLex x ≤ toLex y := by
  rcases h.lt_or_eq with h | h
  · obtain ⟨i, hi, hlt⟩ := h
    refine le_of_lt ⟨i.succ, fun j hj => ?_, hlt⟩
    induction j using Fin.cases with
    | zero => exact h0
    | succ j => exact hi j (Fin.succ_lt_succ_iff.mp hj)
  · refine le_of_eq (congrArg toLex ?_)
    rw [← Fin.cons_self_tail x, ← Fin.cons_self_tail y, h0]
    exact congrArg _ (toLex.injective h)

/-- A nonempty compact set has a point at which a continuous map to `Fin N → ℝ` is
lexicographically least. -/
private theorem IsCompact.exists_forall_toLex_le {Y : Type*} [TopologicalSpace Y] :
    ∀ {N : ℕ} {c : Y → Fin N → ℝ}, Continuous c → ∀ {K : Set Y}, IsCompact K → K.Nonempty →
      ∃ y ∈ K, ∀ z ∈ K, toLex (c y) ≤ toLex (c z)
  | 0, c, _, K, _, ⟨y, hy⟩ => ⟨y, hy, fun z _ => le_of_eq (congrArg toLex (Subsingleton.elim _ _))⟩
  | N + 1, c, hc, K, hK, hne => by
    have hc0 : Continuous fun y => c y 0 := (continuous_apply 0).comp hc
    obtain ⟨y₀, hy₀, hmin⟩ := hK.exists_isMinOn hne hc0.continuousOn
    have hK' : IsCompact (K ∩ {z | c z 0 = c y₀ 0}) :=
      hK.inter_right (isClosed_eq hc0 continuous_const)
    have hct : Continuous fun y => Fin.tail (c y) :=
      continuous_pi fun i => (continuous_apply i.succ).comp hc
    obtain ⟨y, ⟨hyK, hy0⟩, hy⟩ :=
      IsCompact.exists_forall_toLex_le hct hK' ⟨y₀, hy₀, rfl⟩
    refine ⟨y, hyK, fun z hz => ?_⟩
    rcases eq_or_ne (c z 0) (c y₀ 0) with h | h
    · exact Fin.toLex_le_toLex_of_tail (hy0.trans h.symm) (hy z ⟨hz, h⟩)
    · have hlt : c y 0 < c z 0 := hy0 ▸ lt_of_le_of_ne (isMinOn_iff.mp hmin z hz) (Ne.symm h)
      exact le_of_lt ⟨0, fun j hj => absurd hj (Fin.not_lt_zero j), hlt⟩

/-- **A compact set has a lexicographically least point**: for a nonempty compact $K$ in a
finite-dimensional real Hausdorff topological vector space with a basis $(\mathbf{b}_i)_{i<N}$,
some $y \in K$ has coordinates lexicographically below those of every point of $K$. Its
coordinates are $c_i(y) = \min\{c_i(z) : z \in K,\ c_j(z) = c_j(y) \text{ for } j < i\}$, each a
minimum of a continuous function over a nonempty compact set. Upstream candidate. -/
theorem IsCompact.exists_forall_toLex_equivFun_le {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] {N : ℕ}
    (b : Basis (Fin N) ℝ Y) {K : Set Y} (hK : IsCompact K) (hne : K.Nonempty) :
    ∃ y ∈ K, ∀ z ∈ K, toLex (b.equivFun y) ≤ toLex (b.equivFun z) :=
  IsCompact.exists_forall_toLex_le (continuous_equivFun_basis b) hK hne
