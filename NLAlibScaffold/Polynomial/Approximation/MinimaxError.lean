/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.Polynomial
public import Mathlib.Topology.ContinuousMap.Weierstrass
public import Mathlib.Topology.MetricSpace.HausdorffDistance
public import NLAlib.Polynomial.Approximation.MinimaxError
public import NLAlibScaffold.ForMathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Approximation/MinimaxError.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.2). For $s$ compact and $f$ continuous on $s$
a best approximant of degree at most $n$ exists, so $E_n(f; s)$ is a minimum; $E_n$ is
nonnegative, antitone in $n$, monotone in $s$, invariant under adding a polynomial of degree at
most $n$, absolutely homogeneous, subadditive and invariant under affine changes of variable,
and tends to $0$ on an interval (Weierstrass).

## Main results

* `NLAlib.minimaxError_le_of_isUniformApproxOn`: every approximant bounds $E_n$.
* `NLAlib.exists_degree_le_isUniformApproxOn_minimaxError`: a best approximant exists.
* `NLAlib.isLeast_minimaxError`, `NLAlib.minimaxError_eq_infDist`: $E_n$ as a minimum and as
  Mathlib's distance to the restricted polynomials in `C(s, ℝ)`.
* `NLAlib.degree_minimaxPoly_le`, `NLAlib.isUniformApproxOn_minimaxPoly`: the chosen best
  approximation `NLAlib.minimaxPoly`.
* `NLAlib.antitone_minimaxError`, `NLAlib.minimaxError_le_minimaxError_of_subset`,
  `NLAlib.minimaxError_add_eval`, `NLAlib.minimaxError_const_mul`, `NLAlib.minimaxError_add_le`:
  the algebra of $E_n$.
* `NLAlib.minimaxError_comp_mul_add`, `NLAlib.minimaxError_comp_Icc_neg_one_one`: affine
  invariance and the change of interval to $[-1, 1]$.
* `NLAlib.tendsto_minimaxError_atTop`: $E_n(f; [a, b]) \to 0$.
-/

@[expose] public section

open Polynomial
open scoped Topology

namespace NLAlib

/-! ### Bounds and existence -/

/-- The minimax error is nonnegative: $0 \le E_n(f; s)$, for every $f$, $s$ and $n$ (the junk
values are $0$).
Proof: S, about 10 lines. If $s = \emptyset$ the set is `Set.univ` (`Metric.IsUniformApproxOn` is
vacuous) and `Real.sInf_univ`; otherwise every element is nonnegative
(`Metric.IsUniformApproxOn.nonneg`) and `Real.sInf_nonneg`. -/
theorem minimaxError_nonneg (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) : 0 ≤ minimaxError f s n := by
  unfold minimaxError
  rcases s.eq_empty_or_nonempty with rfl | hs
  · have h : {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
        Metric.IsUniformApproxOn (fun x => p.eval x) f ∅ ε} = Set.univ :=
      Set.eq_univ_of_forall fun ε => ⟨0, by simp, fun x hx => absurd hx (Set.notMem_empty x)⟩
    rw [h, Real.sInf_univ]
  · refine Real.sInf_nonneg fun ε hε => ?_
    obtain ⟨p, _, hpε⟩ := hε
    exact hpε.nonneg hs

/-- **Every approximant bounds the minimax error**: if $\deg p \le n$ and
$\lvert f(x) - p(x) \rvert \le \varepsilon$ on $s$ with $0 \le \varepsilon$, then
$E_n(f; s) \le \varepsilon$. The form in which a constructive approximation theorem (Jackson,
Bernstein ellipse, Chebyshev) bounds $E_n$.
Proof: S, about 8 lines. `csInf_le` with lower bound $0$ when $s$ is nonempty
(`Metric.IsUniformApproxOn.nonneg`); for $s = \emptyset$ the value is $0 \le \varepsilon$
(`minimaxError_nonneg` route, `Real.sInf_univ`). -/
theorem minimaxError_le_of_isUniformApproxOn {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ n) {ε : ℝ} (hε₀ : 0 ≤ ε)
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f s ε) : minimaxError f s n ≤ ε := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · have hbot : ¬ BddBelow {e : ℝ | ∃ q : ℝ[X], q.degree ≤ n ∧
        Metric.IsUniformApproxOn (fun x => q.eval x) f ∅ e} := by
      intro hb
      obtain ⟨m, hm⟩ := hb
      have hmem : m - 1 ∈ {e : ℝ | ∃ q : ℝ[X], q.degree ≤ n ∧
          Metric.IsUniformApproxOn (fun x => q.eval x) f ∅ e} :=
        ⟨p, hp, fun x hx => absurd hx (Set.notMem_empty x)⟩
      linarith [hm hmem]
    unfold minimaxError
    rw [Real.sInf_of_not_bddBelow hbot]
    exact hε₀
  · exact csInf_le ⟨0, fun _ ⟨_, _, h⟩ => h.nonneg hne⟩ ⟨p, hp, hε⟩

/-- **A best approximation exists**: for $s$ compact and $f$ continuous on $s$ there is a real
polynomial $p$ of degree at most $n$ with $\lvert f(x) - p(x) \rvert \le E_n(f; s)$ on $s$.
This is how a bound stated for an arbitrary approximant is restated with $E_n$.
[Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1] (locators to check); there on $[-1, 1]$ or an
interval, here on any compact set, the empty set included.
Proof: M, about 40 lines. Restrict $f$ to `C(s, ℝ)` (`hs.compactSpace`,
`ContinuousOn.restrict`); the image of `degreeLE ℝ n` under `toContinuousMapOnAlgHom s` is
finite-dimensional (`degreeLT_succ_eq_degreeLE`, `degreeLTEquiv`, `Submodule.map`), so
`Submodule.exists_infDist_eq_dist` gives a nearest $p$; `ContinuousMap.norm_coe_le_norm` turns
the norm into the pointwise bound, and `ContinuousMap.norm_le` shows that every element of the
set is at least $\|f - p\|$, so $\|f - p\| = E_n$ (`IsLeast.csInf_eq`). Prototype:
`NLAlib.exists_degree_le_norm_sub_eq_minimaxError` (`Polynomial/BestApproximation/MinimaxError`).
Result: best-approximation-existence -/
theorem exists_degree_le_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsCompact s) (hf : ContinuousOn f s) (n : ℕ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f s (minimaxError f s n) := by
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp, fun x hx => absurd hx (Set.notMem_empty x)⟩
  have := isCompact_iff_compactSpace.mp hs
  let g : C(s, ℝ) := ⟨s.domRestrict f, continuousOn_iff_continuous_domRestrict.mp hf⟩
  let P : Submodule ℝ C(s, ℝ) := (degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap
  have : FiniteDimensional ℝ (degreeLE ℝ n) := by
    rw [← degreeLT_succ_eq_degreeLE]
    exact LinearEquiv.finiteDimensional (degreeLTEquiv ℝ (n + 1)).symm
  have : FiniteDimensional ℝ P := inferInstance
  have hpt : ∀ (q : ℝ[X]) (z : s),
      dist (g z) (toContinuousMapOnAlgHom s q z) = dist (f z) (q.eval z) := by
    intro q z
    simp [g, Real.dist_eq]
  obtain ⟨y, hyP, hy⟩ := Submodule.exists_infDist_eq_dist P g
  obtain ⟨p, hpn, rfl⟩ := Submodule.mem_map.mp hyP
  have hleast : IsLeast {ε : ℝ | ∃ q : ℝ[X], q.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => q.eval x) f s ε}
      (dist g (toContinuousMapOnAlgHom s p)) := by
    refine ⟨⟨p, mem_degreeLE.mp hpn, fun x hx => ?_⟩, ?_⟩
    · have h := ContinuousMap.dist_apply_le_dist (f := g)
        (g := toContinuousMapOnAlgHom s p) ⟨x, hx⟩
      have h2 : dist (f x) (p.eval x) = dist (g ⟨x, hx⟩) (toContinuousMapOnAlgHom s p ⟨x, hx⟩) :=
        (hpt p ⟨x, hx⟩).symm
      rw [dist_comm, h2]
      exact h
    · rintro ε ⟨q, hqn, hq⟩
      have hε : 0 ≤ ε := hq.nonneg hne
      calc dist g (toContinuousMapOnAlgHom s p) = Metric.infDist g (P : Set C(s, ℝ)) := hy.symm
        _ ≤ dist g (toContinuousMapOnAlgHom s q) :=
          Metric.infDist_le_dist_of_mem (Submodule.mem_map_of_mem (mem_degreeLE.mpr hqn))
        _ ≤ ε := (ContinuousMap.dist_le hε).mpr fun z => by
          rw [hpt q z, dist_comm]; exact hq z z.2
  have hmin : minimaxError f s n = dist g (toContinuousMapOnAlgHom s p) := by
    unfold minimaxError
    exact hleast.csInf_eq
  refine ⟨p, mem_degreeLE.mp hpn, ?_⟩
  rw [hmin]
  intro x hx
  have h := ContinuousMap.dist_apply_le_dist (f := g)
    (g := toContinuousMapOnAlgHom s p) ⟨x, hx⟩
  have h2 : dist (f x) (p.eval x) = dist (g ⟨x, hx⟩) (toContinuousMapOnAlgHom s p ⟨x, hx⟩) :=
    (hpt p ⟨x, hx⟩).symm
  rw [dist_comm, h2]
  exact h

/-- The minimax error is a minimum: for $s$ compact and nonempty and $f$ continuous on $s$,
$E_n(f; s)$ is the least $\varepsilon$ such that some real polynomial of degree at most $n$ is
within $\varepsilon$ of $f$ on $s$. [Trefethen2019, Ch. 10].
Proof: S, about 6 lines. Membership from `exists_degree_le_isUniformApproxOn_minimaxError`, lower
bound from `csInf_le` (bounded below by $0$, `Metric.IsUniformApproxOn.nonneg`). -/
theorem isLeast_minimaxError {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s) (hne : s.Nonempty)
    (hf : ContinuousOn f s) (n : ℕ) :
    IsLeast {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f s ε} (minimaxError f s n) := by
  refine ⟨exists_degree_le_isUniformApproxOn_minimaxError hs hf n, ?_⟩
  rintro ε ⟨p, hp, hε⟩
  exact minimaxError_le_of_isUniformApproxOn hp (hε.nonneg hne) hε

/-- The bridge to Mathlib's distance: for compact $s$ and $g \in C(s, \mathbb{R})$ agreeing with
$f$ on $s$, $E_n(f; s)$ is the distance in $C(s, \mathbb{R})$ from $g$ to the restrictions of the
real polynomials of degree at most $n$.
Proof: M, about 30 lines. `exists_degree_le_isUniformApproxOn_minimaxError` (with
`hs := isCompact_iff_compactSpace.mpr`, continuity of $f$ on $s$ from `hg` and `g.continuous`)
gives $\operatorname{dist} \le E_n$ through `Metric.infDist_le_dist_of_mem` and
`ContinuousMap.norm_le`; `Metric.le_infDist` and `minimaxError_le_of_isUniformApproxOn` with
`ContinuousMap.norm_coe_le_norm` give the converse; the empty case by `Subsingleton`. -/
theorem minimaxError_eq_infDist {s : Set ℝ} [CompactSpace s] {f : ℝ → ℝ} (g : C(s, ℝ))
    (hg : ∀ x : s, g x = f x) (n : ℕ) :
    minimaxError f s n = Metric.infDist g
      ((degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap : Set C(s, ℝ)) := by
  have hmem : ∀ p : ℝ[X], p.degree ≤ n →
      p.toContinuousMapOn s ∈ ((degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap :
        Set C(s, ℝ)) := by
    intro p hp
    exact Submodule.mem_map_of_mem (mem_degreeLE.mpr hp)
  have hPne : (((degreeLE ℝ n).map (toContinuousMapOnAlgHom s).toLinearMap :
      Submodule ℝ C(s, ℝ)) : Set C(s, ℝ)).Nonempty :=
    ⟨_, hmem 0 (by simp)⟩
  have hf : ContinuousOn f s := by
    refine continuousOn_iff_continuous_domRestrict.mpr ?_
    have : s.domRestrict f = g := funext fun x => (hg x).symm
    rw [this]
    exact g.continuous
  apply le_antisymm
  · refine (Metric.le_infDist hPne).mpr ?_
    intro y hy
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hy
    refine minimaxError_le_of_isUniformApproxOn (mem_degreeLE.mp hq) dist_nonneg ?_
    intro x hx
    have h1 := ContinuousMap.norm_coe_le_norm (g - toContinuousMapOnAlgHom s q) ⟨x, hx⟩
    rw [← dist_eq_norm] at h1
    have h2 : ‖(g - toContinuousMapOnAlgHom s q) ⟨x, hx⟩‖ = |q.eval x - f x| := by
      simp [hg ⟨x, hx⟩, toContinuousMapOnAlgHom_apply, Real.norm_eq_abs, abs_sub_comm]
    rw [h2] at h1
    rw [Real.dist_eq]
    exact h1
  · obtain ⟨p, hp, hpε⟩ :=
      exists_degree_le_isUniformApproxOn_minimaxError (isCompact_iff_compactSpace.mpr inferInstance)
        hf n
    refine (Metric.infDist_le_dist_of_mem (hmem p hp)).trans ?_
    rw [dist_eq_norm, ← toContinuousMapOnAlgHom_apply]
    refine (ContinuousMap.norm_le _ (minimaxError_nonneg f s n)).mpr fun x => ?_
    have := hpε x x.2
    rw [Real.dist_eq] at this
    simp only [ContinuousMap.sub_apply, hg x, Real.norm_eq_abs]
    rw [abs_sub_comm]
    exact this

/-! ### The chosen best approximation -/

/-- The chosen best approximation has degree at most $n$:
$\deg(\mathrm{minimaxPoly}\ f\ s\ n) \le n$, for every $f$, $s$ and $n$ (the junk value is $0$).
Proof: S, about 4 lines. Unfold `minimaxPoly`; `split_ifs`: the chosen polynomial's
`h.choose_spec.1`, and `degree_zero` with `bot_le` for the junk value. -/
theorem degree_minimaxPoly_le (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) :
    (minimaxPoly f s n).degree ≤ n := by
  unfold minimaxPoly
  split_ifs with h
  · exact h.choose_spec.1
  · simp

/-- **The chosen best approximation attains the minimax error**: for $s$ compact and $f$
continuous on $s$, $\lvert f(x) - \mathrm{minimaxPoly}\ f\ s\ n\ (x) \rvert \le E_n(f; s)$ for
all $x \in s$.
Proof: S, about 4 lines. Unfold `minimaxPoly`; the condition holds by
`exists_degree_le_isUniformApproxOn_minimaxError hs hf n`, so `dif_pos` and
`h.choose_spec.2`. -/
theorem isUniformApproxOn_minimaxPoly {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (n : ℕ) :
    Metric.IsUniformApproxOn (fun x => (minimaxPoly f s n).eval x) f s
      (minimaxError f s n) := by
  have h := exists_degree_le_isUniformApproxOn_minimaxError hs hf n
  unfold minimaxPoly
  rw [dif_pos h]
  exact h.choose_spec.2

/-! ### The algebra of the minimax error -/

/-- The minimax error is antitone in the degree: for $s$ compact and $f$ continuous on $s$,
$E_m(f; s) \ge E_n(f; s)$ for $m \le n$.
Proof: S, about 8 lines. A best approximant of degree $m$
(`exists_degree_le_isUniformApproxOn_minimaxError`) has degree at most $n$
(`degree_le_of_le`); `minimaxError_le_of_isUniformApproxOn` with `minimaxError_nonneg`. -/
theorem antitone_minimaxError {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : Antitone (minimaxError f s) := by
  intro m n hmn
  obtain ⟨p, hp, hpx⟩ := exists_degree_le_isUniformApproxOn_minimaxError hs hf m
  exact minimaxError_le_of_isUniformApproxOn (hp.trans (by exact_mod_cast hmn))
    (minimaxError_nonneg f s m) hpx

/-- The minimax error is monotone in the set: for $t$ compact, $f$ continuous on $t$ and
$s \subseteq t$, $E_n(f; s) \le E_n(f; t)$.
Proof: S, about 6 lines. A best approximant on $t$
(`exists_degree_le_isUniformApproxOn_minimaxError`) restricted by
`Metric.IsUniformApproxOn.mono_set`; `minimaxError_le_of_isUniformApproxOn`. -/
theorem minimaxError_le_minimaxError_of_subset {f : ℝ → ℝ} {s t : Set ℝ} (ht : IsCompact t)
    (hf : ContinuousOn f t) (hst : s ⊆ t) (n : ℕ) :
    minimaxError f s n ≤ minimaxError f t n := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_minimaxError ht hf n
  exact minimaxError_le_of_isUniformApproxOn hp (minimaxError_nonneg f t n) (hε.mono_set hst)

/-- Adding a polynomial of degree at most $n$ does not change the minimax error:
$E_n(f + q; s) = E_n(f; s)$ for $\deg q \le n$, for every $f$ and $s$.
[Rivlin1981, Ch. 1] (locator to check).
Proof: S, about 12 lines. The two sets coincide: $p \mapsto p - q$ and $p \mapsto p + q$
preserve degree at most $n$ (`degree_sub_le`, `degree_add_le`) and the pointwise errors
(`eval_sub`, `eval_add`, `Real.dist_eq`); `congrArg sInf`. -/
theorem minimaxError_add_eval (f : ℝ → ℝ) (s : Set ℝ) {n : ℕ} {q : ℝ[X]} (hq : q.degree ≤ n) :
    minimaxError (fun x => f x + q.eval x) s n = minimaxError f s n := by
  unfold minimaxError
  congr 1
  ext ε
  constructor
  · rintro ⟨p, hp, hε⟩
    refine ⟨p - q, (degree_sub_le _ _).trans (max_le hp hq), fun x hx => ?_⟩
    have h := hε x hx
    simp only [Real.dist_eq, Polynomial.eval_sub] at h ⊢
    convert h using 2
    ring
  · rintro ⟨p, hp, hε⟩
    refine ⟨p + q, (degree_add_le _ _).trans (max_le hp hq), fun x hx => ?_⟩
    have h := hε x hx
    simp only [Polynomial.eval_add]
    rw [dist_add_right]
    exact h

/-- The minimax error is absolutely homogeneous: $E_n(cf; s) = \lvert c \rvert E_n(f; s)$, for
every $c$, $f$, $s$ and $n$ (junk values included). [Rivlin1981, Ch. 1] (locator to check).
Proof: M, about 20 lines. For $c = 0$ both sides are $0$ (`minimaxError_nonneg`, the zero
polynomial). For $c \ne 0$ the set for $cf$ is $\lvert c \rvert$ times the set for $f$
($p \mapsto C c \cdot p$, `degree_C_mul`, `abs_mul`); `Real.sInf_smul_of_nonneg`; the empty and
unbounded (empty $s$) cases give $0$ on both sides. -/
theorem minimaxError_const_mul (c : ℝ) (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) :
    minimaxError (fun x => c * f x) s n = |c| * minimaxError f s n := by
  rcases eq_or_ne c 0 with rfl | hc
  · have h0 : minimaxError (fun x => (0 : ℝ) * f x) s n = 0 :=
      le_antisymm
        (minimaxError_le_of_isUniformApproxOn (p := 0) (by simp) le_rfl
          (fun x _ => by simp))
        (minimaxError_nonneg _ _ _)
    rw [h0, abs_zero, zero_mul]
  · open scoped Pointwise in
    have hS : {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
        Metric.IsUniformApproxOn (fun x => p.eval x) (fun x => c * f x) s ε} =
        |c| • {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
        Metric.IsUniformApproxOn (fun x => p.eval x) f s ε} := by
      ext ε
      simp only [Set.mem_smul_set, Set.mem_ofPred_eq, smul_eq_mul, Metric.IsUniformApproxOn,
        Real.dist_eq]
      constructor
      · rintro ⟨p, hp, hε⟩
        refine ⟨|c|⁻¹ * ε, ⟨C c⁻¹ * p, by rw [degree_C_mul (inv_ne_zero hc)]; exact hp, ?_⟩,
          mul_inv_cancel_left₀ (abs_ne_zero.mpr hc) ε⟩
        intro x hx
        have key : c⁻¹ * p.eval x - f x = c⁻¹ * (p.eval x - c * f x) := by
          rw [mul_sub, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
        simp only [eval_mul, eval_C]
        rw [key, abs_mul, abs_inv]
        exact mul_le_mul_of_nonneg_left (hε x hx) (inv_nonneg.mpr (abs_nonneg c))
      · rintro ⟨η, ⟨p, hp, hη⟩, rfl⟩
        refine ⟨C c * p, by rw [degree_C_mul hc]; exact hp, ?_⟩
        intro x hx
        have key : c * p.eval x - c * f x = c * (p.eval x - f x) := by ring
        simp only [eval_mul, eval_C]
        rw [key, abs_mul]
        exact mul_le_mul_of_nonneg_left (hη x hx) (abs_nonneg c)
    unfold minimaxError
    rw [hS, Real.sInf_smul_of_nonneg (abs_nonneg c), smul_eq_mul]

/-- The minimax error is subadditive: for $s$ compact and $f, g$ continuous on $s$,
$E_n(f + g; s) \le E_n(f; s) + E_n(g; s)$. [Rivlin1981, Ch. 1] (locator to check).
Proof: S, about 10 lines. Best approximants $p$ of $f$ and $q$ of $g$
(`exists_degree_le_isUniformApproxOn_minimaxError`); $p + q$ has degree at most $n$ and error at
most the sum (`abs_add_le`); `minimaxError_le_of_isUniformApproxOn` with `minimaxError_nonneg`. -/
theorem minimaxError_add_le {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (n : ℕ) :
    minimaxError (fun x => f x + g x) s n ≤ minimaxError f s n + minimaxError g s n := by
  obtain ⟨p, hp, hpε⟩ := exists_degree_le_isUniformApproxOn_minimaxError hs hf n
  obtain ⟨q, hq, hqε⟩ := exists_degree_le_isUniformApproxOn_minimaxError hs hg n
  refine minimaxError_le_of_isUniformApproxOn (p := p + q)
    ((degree_add_le _ _).trans (max_le hp hq))
    (add_nonneg (minimaxError_nonneg _ _ _) (minimaxError_nonneg _ _ _)) ?_
  intro x hx
  have h1 := hpε x hx
  have h2 := hqε x hx
  simp only [Polynomial.eval_add]
  calc |p.eval x + q.eval x - (f x + g x)|
      = |(p.eval x - f x) + (q.eval x - g x)| := by ring_nf
    _ ≤ |p.eval x - f x| + |q.eval x - g x| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- **Affine invariance of the minimax error**: for $\alpha \ne 0$,
$E_n\bigl(f(\alpha\,\cdot + \beta); \{t : \alpha t + \beta \in s\}\bigr) = E_n(f; s)$, for every
$f$ and $s$. [Trefethen2019, Ch. 10].
Proof: M, about 30 lines. The two sets coincide: $p \mapsto p \circ (\alpha X + \beta)$ is a
degree-preserving bijection of the polynomials of degree at most $n$, with inverse
$q \mapsto q \circ (\alpha^{-1}X - \alpha^{-1}\beta)$ (`natDegree_comp_le`, `eval_comp`,
`comp_assoc`), and it carries pointwise errors on the preimage to those on $s$. Prototype:
`NLAlib.minimaxError_comp_homeomorph_of_affine` (`Polynomial/BestApproximation/Affine`). -/
theorem minimaxError_comp_mul_add (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) {α : ℝ} (hα : α ≠ 0)
    (β : ℝ) :
    minimaxError (fun t => f (α * t + β)) ((fun t => α * t + β) ⁻¹' s) n =
      minimaxError f s n := by
  have hdeg : ∀ (p L : ℝ[X]), p.degree ≤ n → L.natDegree ≤ 1 → (p.comp L).degree ≤ n := by
    intro p L hp hL
    refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
    have := natDegree_le_of_degree_le hp
    nlinarith [Nat.mul_le_mul this hL]
  unfold minimaxError
  congr 1
  ext ε
  constructor
  · rintro ⟨q, hq, hε⟩
    refine ⟨q.comp (C α⁻¹ * X - C (α⁻¹ * β)), hdeg _ _ hq ?_, fun y hy => ?_⟩
    · compute_degree!
    · have e2 : α * (α⁻¹ * (y - β)) + β = y := by field_simp; ring
      have ht : α * (α⁻¹ * (y - β)) + β ∈ s := by rw [e2]; exact hy
      have := hε _ ht
      have h3 : f (α * (α⁻¹ * (y - β)) + β) = f y := by rw [e2]
      have e : α⁻¹ * y - α⁻¹ * β = α⁻¹ * (y - β) := by ring
      simp only [eval_comp, eval_sub, eval_mul, eval_C, eval_X]
      rw [e, ← h3]
      exact this
  · rintro ⟨p, hp, hε⟩
    refine ⟨p.comp (C α * X + C β), hdeg _ _ hp ?_, fun t ht => ?_⟩
    · compute_degree!
    · have := hε _ ht
      simp only [eval_comp, eval_add, eval_mul, eval_C, eval_X]
      exact this

/-- **Change of interval**: for $a < b$, pulling $f$ back from $[a, b]$ to $[-1, 1]$ by
$t \mapsto ((b - a)t + b + a)/2$, the map used by the Chebyshev and Bernstein-ellipse
approximations, preserves the minimax error. [Trefethen2019, Ch. 10].
Proof: S, about 10 lines. `minimaxError_comp_mul_add` with $\alpha = (b - a)/2$,
$\beta = (b + a)/2$, after rewriting the function (`funext`, `ring`) and the preimage of
$[a, b]$ as $[-1, 1]$ (`Set.ext`, `le_div_iff₀`, `div_le_iff₀`). -/
theorem minimaxError_comp_Icc_neg_one_one (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (n : ℕ) :
    minimaxError (fun t => f (((b - a) * t + b + a) / 2)) (Set.Icc (-1) 1) n =
      minimaxError f (Set.Icc a b) n := by
  have hpos : 0 < (b - a) / 2 := by linarith
  have h := minimaxError_comp_mul_add f (Set.Icc a b) n hpos.ne' ((b + a) / 2)
  have hf : (fun t => f (((b - a) * t + b + a) / 2)) =
      fun t => f ((b - a) / 2 * t + (b + a) / 2) := by
    funext t
    congr 1
    ring
  have hs : (fun t : ℝ => (b - a) / 2 * t + (b + a) / 2) ⁻¹' Set.Icc a b = Set.Icc (-1) 1 := by
    ext t
    simp only [Set.mem_preimage, Set.mem_Icc]
    constructor <;> intro <;> constructor <;> nlinarith
  rw [hf, ← hs]
  exact h

/-- **The minimax error tends to zero** on an interval: for $f$ continuous on $[a, b]$,
$E_n(f; [a, b]) \to 0$ as $n \to \infty$ (Weierstrass). [Trefethen2019, Ch. 6].
Proof: S, about 15 lines. Mathlib's `exists_polynomial_near_of_continuousOn` gives $p$ within
$\varepsilon$; for $n \ge \deg p$, `minimaxError_le_of_isUniformApproxOn` (`degree_le_natDegree`);
`Metric.tendsto_atTop` with `minimaxError_nonneg`. -/
theorem tendsto_minimaxError_atTop {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    Filter.Tendsto (minimaxError f (Set.Icc a b)) Filter.atTop (𝓝 0) := by
  refine Metric.tendsto_atTop.mpr fun ε hε => ?_
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf (ε / 2) (by linarith)
  refine ⟨p.natDegree, fun n hn => ?_⟩
  have hdeg : p.degree ≤ n := Polynomial.degree_le_natDegree.trans (by exact_mod_cast hn)
  have hunif : Metric.IsUniformApproxOn (fun x => eval x p) f (Set.Icc a b) (ε / 2) :=
    fun x hx => by rw [Real.dist_eq]; exact (hp x hx).le
  have hle := minimaxError_le_of_isUniformApproxOn hdeg (by linarith) hunif
  have hnn := minimaxError_nonneg f (Set.Icc a b) n
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnn]
  linarith

end NLAlib
