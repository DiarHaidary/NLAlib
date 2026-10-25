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
  sorry

/-- The minimax error is a minimum: for $s$ compact and nonempty and $f$ continuous on $s$,
$E_n(f; s)$ is the least $\varepsilon$ such that some real polynomial of degree at most $n$ is
within $\varepsilon$ of $f$ on $s$. [Trefethen2019, Ch. 10].
Proof: S, about 6 lines. Membership from `exists_degree_le_isUniformApproxOn_minimaxError`, lower
bound from `csInf_le` (bounded below by $0$, `Metric.IsUniformApproxOn.nonneg`). -/
theorem isLeast_minimaxError {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s) (hne : s.Nonempty)
    (hf : ContinuousOn f s) (n : ℕ) :
    IsLeast {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f s ε} (minimaxError f s n) := by
  sorry

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
  sorry

/-! ### The chosen best approximation -/

/-- The chosen best approximation has degree at most $n$:
$\deg(\mathrm{minimaxPoly}\ f\ s\ n) \le n$, for every $f$, $s$ and $n$ (the junk value is $0$).
Proof: S, about 4 lines. Unfold `minimaxPoly`; `split_ifs`: the chosen polynomial's
`h.choose_spec.1`, and `degree_zero` with `bot_le` for the junk value. -/
theorem degree_minimaxPoly_le (f : ℝ → ℝ) (s : Set ℝ) (n : ℕ) :
    (minimaxPoly f s n).degree ≤ n := by
  sorry

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
  sorry

/-! ### The algebra of the minimax error -/

/-- The minimax error is antitone in the degree: for $s$ compact and $f$ continuous on $s$,
$E_m(f; s) \ge E_n(f; s)$ for $m \le n$.
Proof: S, about 8 lines. A best approximant of degree $m$
(`exists_degree_le_isUniformApproxOn_minimaxError`) has degree at most $n$
(`degree_le_of_le`); `minimaxError_le_of_isUniformApproxOn` with `minimaxError_nonneg`. -/
theorem antitone_minimaxError {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) : Antitone (minimaxError f s) := by
  sorry

/-- The minimax error is monotone in the set: for $t$ compact, $f$ continuous on $t$ and
$s \subseteq t$, $E_n(f; s) \le E_n(f; t)$.
Proof: S, about 6 lines. A best approximant on $t$
(`exists_degree_le_isUniformApproxOn_minimaxError`) restricted by
`Metric.IsUniformApproxOn.mono_set`; `minimaxError_le_of_isUniformApproxOn`. -/
theorem minimaxError_le_minimaxError_of_subset {f : ℝ → ℝ} {s t : Set ℝ} (ht : IsCompact t)
    (hf : ContinuousOn f t) (hst : s ⊆ t) (n : ℕ) :
    minimaxError f s n ≤ minimaxError f t n := by
  sorry

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
  sorry

/-- The minimax error is subadditive: for $s$ compact and $f, g$ continuous on $s$,
$E_n(f + g; s) \le E_n(f; s) + E_n(g; s)$. [Rivlin1981, Ch. 1] (locator to check).
Proof: S, about 10 lines. Best approximants $p$ of $f$ and $q$ of $g$
(`exists_degree_le_isUniformApproxOn_minimaxError`); $p + q$ has degree at most $n$ and error at
most the sum (`abs_add_le`); `minimaxError_le_of_isUniformApproxOn` with `minimaxError_nonneg`. -/
theorem minimaxError_add_le {f g : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) (n : ℕ) :
    minimaxError (fun x => f x + g x) s n ≤ minimaxError f s n + minimaxError g s n := by
  sorry

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
  sorry

/-- **The minimax error tends to zero** on an interval: for $f$ continuous on $[a, b]$,
$E_n(f; [a, b]) \to 0$ as $n \to \infty$ (Weierstrass). [Trefethen2019, Ch. 6].
Proof: S, about 15 lines. Mathlib's `exists_polynomial_near_of_continuousOn` gives $p$ within
$\varepsilon$; for $n \ge \deg p$, `minimaxError_le_of_isUniformApproxOn` (`degree_le_natDegree`);
`Metric.tendsto_atTop` with `minimaxError_nonneg`. -/
theorem tendsto_minimaxError_atTop {f : ℝ → ℝ} {a b : ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    Filter.Tendsto (minimaxError f (Set.Icc a b)) Filter.atTop (𝓝 0) := by
  sorry

end NLAlib
