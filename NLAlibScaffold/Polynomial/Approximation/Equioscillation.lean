/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Approximation.Equioscillation
public import NLAlibScaffold.Polynomial.Approximation.MinimaxError
public import NLAlibScaffold.ForMathlib.Topology.Order.IntermediateValue
public import NLAlibScaffold.ForMathlib.Topology.ContinuousMap.Compact

/-!
# Equioscillation: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Approximation/Equioscillation.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.3). De la Vallée Poussin: an error
$f - p$, $\deg p \le n$, that alternates at $n + 2$ points of $s$ with level $\varepsilon$ gives
$\varepsilon \le E_n(f; s)$, on any set and for any $f$. Chebyshev: on $[a, b]$, $a < b$, with
$f$ continuous, $p$ is a best approximation if and only if $f - p$ equioscillates at $n + 2$
points; the best approximation is unique and interpolates $f$ at $n + 1$ interior points. The
Chebyshev polynomial $T_n$ alternates at $n + 1$ points, which gives
$E_n(x^{n + 1}; [-1, 1]) = 2^{-n}$.

## Main results

* `NLAlib.AlternatesOn.mono`, `NLAlib.AlternatesOn.exists_eq_of_abs_le`: the API of the
  predicate.
* `NLAlib.AlternatesOn.exists_le_abs_sub_eval`, `NLAlib.AlternatesOn.le_minimaxError`: de la
  Vallée Poussin's lower bound.
* `NLAlib.AlternatesOn.minimaxError_eq`: an equioscillating error is the minimax error.
* `NLAlib.alternatesOn_of_isUniformApproxOn_minimaxError`,
  `NLAlib.isUniformApproxOn_minimaxError_iff_exists_alternatesOn`: Chebyshev's equioscillation
  theorem.
* `NLAlib.eq_of_isUniformApproxOn_minimaxError`: uniqueness.
* `NLAlib.exists_eval_eq_of_isUniformApproxOn_minimaxError`: the best approximation interpolates.
* `NLAlib.alternatesOn_minimaxPoly`, `NLAlib.eq_minimaxPoly_of_isUniformApproxOn_minimaxError`:
  the chosen best approximation `NLAlib.minimaxPoly` equioscillates and is the best one.
* `NLAlib.exists_degree_le_or_alternatesOn`: the sign-block lemma, for later strengthenings.
* `NLAlib.alternatesOn_eval_T_real`, `NLAlib.minimaxError_pow_Icc_neg_one_one`: the Chebyshev
  example.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-! ### The predicate -/

/-- Alternation is monotone: if $g$ alternates on $s$ at $k$ points with level $\varepsilon$,
then it alternates on every $t \supseteq s$ with every level $\eta \le \varepsilon$.
Proof: S, about 4 lines. The same points and sign; `le_trans`. -/
theorem AlternatesOn.mono {g : ℝ → ℝ} {s t : Set ℝ} {k : ℕ} {ε η : ℝ}
    (h : AlternatesOn g s k ε) (hst : s ⊆ t) (hηε : η ≤ ε) : AlternatesOn g t k η := by
  obtain ⟨x, hx, hxs, σ, hσ, h⟩ := h
  exact ⟨x, hx, fun i => hst (hxs i), σ, hσ, fun i => hηε.trans (h i)⟩

/-- An alternation at the level of the uniform bound is an equioscillation: if $g$ alternates on
$s$ at $k$ points with level $\varepsilon$ and $\lvert g \rvert \le \varepsilon$ on $s$, then
there are $x_0 < \dots < x_{k-1}$ in $s$ and $\sigma \in \{1, -1\}$ with
$g(x_i) = \sigma(-1)^i\varepsilon$.
Proof: S, about 10 lines. The same points and sign: $\varepsilon \le \sigma(-1)^ig(x_i) \le
\lvert g(x_i) \rvert \le \varepsilon$ (`le_abs_self`, `abs_mul`, $\lvert\sigma(-1)^i\rvert = 1$),
so $\sigma(-1)^ig(x_i) = \varepsilon$; multiply by $\sigma(-1)^i$ (its square is $1$). -/
theorem AlternatesOn.exists_eq_of_abs_le {g : ℝ → ℝ} {s : Set ℝ} {k : ℕ} {ε : ℝ}
    (h : AlternatesOn g s k ε) (hg : ∀ x ∈ s, |g x| ≤ ε) :
    ∃ x : Fin k → ℝ, StrictMono x ∧ (∀ i, x i ∈ s) ∧
      ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ i : Fin k, g (x i) = σ * (-1) ^ (i : ℕ) * ε := by
  obtain ⟨x, hmono, hx, σ, hσ, hle⟩ := h
  refine ⟨x, hmono, hx, σ, hσ, fun i => ?_⟩
  have h2 : (-1 : ℝ) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]; norm_num
  have hsq : (σ * (-1) ^ (i : ℕ)) * (σ * (-1) ^ (i : ℕ)) = 1 := by
    rcases hσ with rfl | rfl <;> linear_combination h2
  have habs : |σ * (-1) ^ (i : ℕ) * g (x i)| = |g (x i)| := by
    rcases hσ with rfl | rfl <;> simp [abs_mul, abs_pow]
  have hgi : |g (x i)| ≤ ε := hg _ (hx i)
  have heq : σ * (-1) ^ (i : ℕ) * g (x i) = ε :=
    le_antisymm ((le_abs_self _).trans (habs.le.trans hgi)) (hle i)
  calc g (x i) = (σ * (-1) ^ (i : ℕ)) * (σ * (-1) ^ (i : ℕ)) * g (x i) := by rw [hsq, one_mul]
    _ = σ * (-1) ^ (i : ℕ) * ε := by rw [mul_assoc, heq]

/-! ### De la Vallée Poussin -/

/-- **De la Vallée Poussin's theorem, pointwise.** If $\deg p \le n$ and $f - p$ alternates on
$s$ at $n + 2$ points with level $\varepsilon$, then every real polynomial $q$ of degree at most
$n$ has $\varepsilon \le \lvert f(x) - q(x) \rvert$ at some $x \in s$. No continuity of $f$ and
no structure of $s$ are needed. [Rivlin1981, Ch. 1]; [Trefethen2019, Ch. 10] (locators to check).
Proof: M, about 30 lines. Suppose $\lvert f - q \rvert < \varepsilon$ at all $n + 2$ points
$x_i$ (so $\varepsilon > 0$). Then $\sigma(-1)^i(q - p)(x_i) = \sigma(-1)^i(f - p)(x_i) -
\sigma(-1)^i(f - q)(x_i) > 0$, so the polynomial $q - p$ changes sign between consecutive points;
`exists_strictMono_eq_zero_of_mul_neg` gives $n + 1$ distinct zeros, and
`Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero` (degree at most $n$, `degree_sub_le`)
makes $q = p$, contradicting $\lvert f - p \rvert \ge \varepsilon > \lvert f - q \rvert$ at $x_0$.
Prototype: `NLAlib.exists_abs_sub_eval_ge_of_alternation`
(`Polynomial/BestApproximation/AlternationLowerBound`). -/
theorem AlternatesOn.exists_le_abs_sub_eval {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n) {q : ℝ[X]}
    (hq : q.degree ≤ n) : ∃ x ∈ s, ε ≤ |f x - q.eval x| := by
  obtain ⟨x, hx, hxs, σ, hσ, h⟩ := h
  by_contra! H
  have hσsq : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have key : ∀ i : Fin (n + 2), 0 < σ * (-1) ^ (i : ℕ) * (q - p).eval (x i) := by
    intro i
    have h1 : ε ≤ σ * (-1) ^ (i : ℕ) * (f (x i) - p.eval (x i)) := h i
    have h2 := H (x i) (hxs i)
    have ha : |σ * (-1) ^ (i : ℕ)| = 1 := by
      rcases hσ with rfl | rfl <;> simp [abs_pow]
    have h3 : σ * (-1) ^ (i : ℕ) * (f (x i) - q.eval (x i)) ≤ |f (x i) - q.eval (x i)| := by
      calc _ ≤ |σ * (-1) ^ (i : ℕ) * (f (x i) - q.eval (x i))| := le_abs_self _
        _ = |f (x i) - q.eval (x i)| := by rw [abs_mul, ha, one_mul]
    have h4 : σ * (-1) ^ (i : ℕ) * (q - p).eval (x i)
        = σ * (-1) ^ (i : ℕ) * (f (x i) - p.eval (x i))
          - σ * (-1) ^ (i : ℕ) * (f (x i) - q.eval (x i)) := by
      simp only [eval_sub]; ring
    linarith
  have hpair : ∀ i : Fin (n + 1), (q - p).eval (x i.castSucc) * (q - p).eval (x i.succ) < 0 := by
    intro i
    have hA := key i.castSucc
    have hB := key i.succ
    have hs : ((-1 : ℝ) ^ (i : ℕ)) * (-1) ^ (i : ℕ) = 1 := by
      rw [← mul_pow]; norm_num
    have hpow : (-1 : ℝ) ^ ((i.succ : Fin (n + 2)) : ℕ) = -(-1) ^ (i : ℕ) := by
      rw [Fin.val_succ, pow_succ]; ring
    have hpow' : (-1 : ℝ) ^ ((i.castSucc : Fin (n + 2)) : ℕ) = (-1) ^ (i : ℕ) := by
      rw [Fin.val_castSucc]
    rw [hpow] at hB
    rw [hpow'] at hA
    have hprod : (σ * (-1) ^ (i : ℕ) * (q - p).eval (x i.castSucc))
        * (σ * -(-1) ^ (i : ℕ) * (q - p).eval (x i.succ))
        = -((q - p).eval (x i.castSucc) * (q - p).eval (x i.succ)) := by
      linear_combination (-((q - p).eval (x i.castSucc) * (q - p).eval (x i.succ))
        * ((-1 : ℝ) ^ (i : ℕ) * (-1) ^ (i : ℕ))) * hσsq
        + (-((q - p).eval (x i.castSucc) * (q - p).eval (x i.succ))) * hs
    linarith [mul_pos hA hB, hprod]
  obtain ⟨c, hc, hzero⟩ := exists_strictMono_eq_zero_of_mul_neg (k := n + 1)
    (f := fun t => (q - p).eval t) (v := x) hx (q - p).continuous.continuousOn hpair
  have hd : q - p = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (s := Finset.univ)
      (v := c) hc.injective.injOn ?_ (fun i _ => (hzero i).2)
    have hdeg : (q - p).degree ≤ n := (degree_sub_le q p).trans (max_le hq hp)
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt hdeg (by exact_mod_cast Nat.lt_succ_self n)
  have k0 := key 0
  rw [hd, eval_zero, mul_zero] at k0
  exact lt_irrefl _ k0

/-- **De la Vallée Poussin's lower bound.** If $\deg p \le n$, $p$ is within some finite
$\eta$ of $f$ on $s$, and $f - p$ alternates on $s$ at $n + 2$ points with level
$\varepsilon$, then $\varepsilon \le E_n(f; s)$. The set $s$ is arbitrary (a finite spectrum, a
union of intervals); the finite $\eta$ only excludes the junk value of `minimaxError`.
[Rivlin1981, Ch. 1]; [Trefethen2019, Ch. 10] (locators to check).
Proof: S, about 10 lines. The set defining $E_n$ is nonempty ($\eta$, `hη`); every element
$\varepsilon'$, witnessed by $q$, satisfies $\varepsilon \le \lvert f(x) - q(x) \rvert \le
\varepsilon'$ at the point of `AlternatesOn.exists_le_abs_sub_eval`; `le_csInf`. Prototype:
`NLAlib.le_minimaxError_of_alternation`.
Result: de-la-vallee-poussin -/
theorem AlternatesOn.le_minimaxError {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n) {η : ℝ}
    (hη : Metric.IsUniformApproxOn (fun x => p.eval x) f s η) : ε ≤ minimaxError f s n := by
  unfold minimaxError
  refine le_csInf ⟨η, p, hp, hη⟩ ?_
  rintro ε' ⟨q, hq, hq'⟩
  obtain ⟨x, hxs, hx⟩ := h.exists_le_abs_sub_eval hp hq
  have hdist := hq' x hxs
  rw [Real.dist_eq, abs_sub_comm] at hdist
  exact hx.trans hdist

/-- **An equioscillating error is the minimax error**: if $\deg p \le n$,
$\lvert f - p \rvert \le \varepsilon$ on $s$ and $f - p$ alternates on $s$ at $n + 2$ points
with level $\varepsilon$, then $E_n(f; s) = \varepsilon$, and $p$ is a best approximation. On
any set, for any $f$: the certificate direction of the equioscillation theorem.
[Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1] (locators to check).
Proof: S, about 6 lines. `AlternatesOn.le_minimaxError` with $\eta = \varepsilon$, and
`minimaxError_le_of_isUniformApproxOn` with $0 \le \varepsilon$ (`Metric.IsUniformApproxOn.nonneg`,
$s$ nonempty from `h`). Prototype: `NLAlib.norm_sub_eq_minimaxError_of_equioscillation`
(`Polynomial/BestApproximation/EquioscillationCertificate`).
Result: equioscillation -/
theorem AlternatesOn.minimaxError_eq {f : ℝ → ℝ} {s : Set ℝ} {n : ℕ} {p : ℝ[X]} {ε : ℝ}
    (h : AlternatesOn (fun x => f x - p.eval x) s (n + 2) ε) (hp : p.degree ≤ n)
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f s ε) : minimaxError f s n = ε := by
  have hne : s.Nonempty := by
    obtain ⟨x, -, hxs, -⟩ := h
    exact ⟨x 0, hxs 0⟩
  exact le_antisymm (minimaxError_le_of_isUniformApproxOn hp (hε.nonneg hne) hε)
    (h.le_minimaxError hp hε)

/-! ### Chebyshev's equioscillation theorem -/

/-- Prepending a point of opposite sign to an alternation lengthens it by one. -/
private theorem alternatesOn_vecCons {e : ℝ → ℝ} {s : Set ℝ} {k : ℕ} {E r σ : ℝ}
    {v : Fin (k + 1) → ℝ} (hv : StrictMono v) (hvs : ∀ i, v i ∈ s) (hσ : σ = 1 ∨ σ = -1)
    (hvE : ∀ i : Fin (k + 1), E ≤ σ * (-1) ^ (i : ℕ) * e (v i)) (hr : r ∈ s) (hrv : r < v 0)
    (her : E ≤ -σ * e r) : AlternatesOn e s (k + 2) E := by
  refine ⟨Matrix.vecCons r v, hv.vecCons hrv, Fin.cases hr hvs, -σ,
    by rcases hσ with rfl | rfl <;> norm_num, Fin.cases (by simpa using her) fun i => ?_⟩
  simp only [Matrix.cons_val_succ, Fin.val_succ, pow_succ]
  linarith [hvE i]

/-- The constant $e(a)$ has the sign of $e$ at the extremal points when $e$ never takes the
value $-e(a)$ on $[a, b]$. -/
private theorem exists_degree_le_const {e : ℝ → ℝ} {a b E : ℝ} (n : ℕ) (hE : 0 < E)
    (hea : |e a| = E) (hT : ¬ ∃ y ∈ Set.Icc a b, e y = -e a) :
    ∃ q : ℝ[X], q.degree ≤ n ∧ (∀ x ∈ Set.Icc a b, |e x| = E → 0 < e x * q.eval x) ∧
      ∀ x ≤ a, 0 < e a * q.eval x := by
  have ha : e a ≠ 0 := fun h => by simp [h] at hea; linarith
  refine ⟨C (e a), degree_C_le.trans (WithBot.coe_le_coe.2 (Nat.zero_le n)), fun x hx hxE => ?_,
    fun x _ => by simpa using mul_self_pos.2 ha⟩
  rcases abs_eq_abs.1 (hxE.trans hea.symm) with h | h
  · simpa [h] using mul_self_pos.2 ha
  · exact absurd ⟨x, hx, h⟩ hT

/-- The pivot of the sign-block lemma: the least point $y$ of $[a, b]$ with $e(y) = -e(a)$, and
a point $z \in (a, y)$ above every extremal point below $y$. -/
private theorem exists_pivot {e : ℝ → ℝ} {a b E : ℝ} (he : ContinuousOn e (Set.Icc a b))
    (hE : 0 < E) (hea : |e a| = E) (hT : ∃ y ∈ Set.Icc a b, e y = -e a) :
    ∃ y z, a < z ∧ z < y ∧ y ≤ b ∧ e y = -e a ∧
      ∀ x ∈ Set.Icc a b, |e x| = E → x < y → e x = e a ∧ x < z := by
  have ha : e a ≠ 0 := fun h => by simp [h] at hea; linarith
  have hcl := he.preimage_isClosed_of_isClosed isClosed_Icc (isClosed_singleton (x := -e a))
  obtain ⟨y, ⟨hyI, hy⟩, hyl⟩ :=
    (isCompact_Icc.of_isClosed_subset hcl Set.inter_subset_left).exists_isLeast hT
  have hy' : e y = -e a := hy
  have hay : a < y := lt_of_le_of_ne hyI.1 fun h => ha (by subst h; linarith)
  have hcl' := (he.mono (Set.Icc_subset_Icc_right hyI.2)).preimage_isClosed_of_isClosed
    isClosed_Icc (isClosed_singleton (x := e a))
  obtain ⟨u, ⟨huI, hu⟩, hug⟩ := (isCompact_Icc.of_isClosed_subset hcl'
    Set.inter_subset_left).exists_isGreatest ⟨a, ⟨le_rfl, hay.le⟩, rfl⟩
  have hu' : e u = e a := hu
  have huy : u < y := lt_of_le_of_ne huI.2 fun h => ha (by subst h; linarith)
  refine ⟨y, (u + y) / 2, by linarith [huI.1], by linarith, hyI.2, hy', fun x hx hxE hxy => ?_⟩
  rcases abs_eq_abs.1 (hxE.trans hea.symm) with h | h
  · exact ⟨h, by linarith [hug ⟨⟨hx.1, hxy.le⟩, h⟩]⟩
  · exact absurd (hyl ⟨hx, h⟩) (not_le.2 hxy)

/-- **The sign-block lemma** behind the equioscillation theorem. Let $e$ be continuous on
$[a, b]$, $E > 0$ and $\lvert e(a) \rvert = E$. Either some real $q$ of degree at most $n$ has the
sign of $e$ at its extremal points, $e(x)q(x) > 0$ at every $x \in [a, b]$ with
$\lvert e(x) \rvert = E$, and the sign of $e(a)$ to the left of $a$, $e(a)q(x) > 0$ for every
$x \le a$; or $e$ alternates at $n + 2$ points of $\{x \in [a, b] : \lvert e(x) \rvert = E\}$
with level $E$. The second clause of the first alternative is what makes the induction on $n$
compose; the lemma is public so that the equioscillation theorem on compact sets and its
weighted form (`docs/design/Polynomial-BestApproximation.md`, §11) reuse it.
[Trefethen2019, Theorem 10.1] (the perturbation argument there, locator to check).
Proof: L, about 120 lines, by induction on $n$ generalising $a$. If $e$ never takes $-e(a)$ at
an extremal point of $[a, b]$, the constant $q = e(a)$ works. Otherwise let $y$ be the least
point of $[a, b]$ with $e(y) = -e(a)$ (compact level set, `IsCompact.exists_isLeast`), $u$ the
greatest point of $[a, y]$ with $e(u) = e(a)$ (`IsCompact.exists_isGreatest`) and
$z = (u + y)/2$; every extremal point below $y$ has value $e(a)$ and lies in $[a, u]$. Apply the
hypothesis at $y$ (degree $n - 1$, `Nat` induction): its polynomial $q'$ gives
$q = (X - z)q'$ (degree by `degree_mul_le`, signs by `nlinarith` on the two sides of $z$); its
alternation, preceded by $y$ or $a$ (whichever has the opposite sign to the first point), gives
the $n + 2$ points (`Fin.cons`, `Fin.strictMono_cons`). The base case $n = 0$ is the same split
with $q$ constant and the pair $(a, y)$. Prototype:
`NLAlib.exists_polynomial_extremal_sign_or_alternation`
(`Polynomial/BestApproximation/ExtremalSigns`, 150 lines, proved). -/
theorem exists_degree_le_or_alternatesOn (n : ℕ) {e : ℝ → ℝ} {a b E : ℝ}
    (he : ContinuousOn e (Set.Icc a b)) (hE : 0 < E) (hab : a ≤ b) (hea : |e a| = E) :
    (∃ q : ℝ[X], q.degree ≤ n ∧ (∀ x ∈ Set.Icc a b, |e x| = E → 0 < e x * q.eval x) ∧
      ∀ x ≤ a, 0 < e a * q.eval x) ∨
    AlternatesOn e {x | x ∈ Set.Icc a b ∧ |e x| = E} (n + 2) E := by
  induction n generalizing a with
  | zero =>
    by_cases hT : ∃ y ∈ Set.Icc a b, e y = -e a
    · right
      obtain ⟨y, z, haz, hzy, hyb, hy, -⟩ := exists_pivot he hE hea hT
      have hyE : |e y| = E := by rw [hy, abs_neg, hea]
      have hys : y ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨by linarith, hyb⟩, hyE⟩
      have has : a ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨le_rfl, hab⟩, hea⟩
      rcases (abs_eq hE.le).1 hea with h | h
      · exact alternatesOn_vecCons (v := ![y]) (σ := -1) strictMono_vecEmpty
          (Fin.forall_fin_one.2 hys) (Or.inr rfl) (Fin.forall_fin_one.2 (by simp; linarith))
          has (by simp; linarith) (by linarith)
      · exact alternatesOn_vecCons (v := ![y]) (σ := 1) strictMono_vecEmpty
          (Fin.forall_fin_one.2 hys) (Or.inl rfl) (Fin.forall_fin_one.2 (by simp; linarith))
          has (by simp; linarith) (by linarith)
    · exact Or.inl (exists_degree_le_const 0 hE hea hT)
  | succ n ih =>
    by_cases hT : ∃ y ∈ Set.Icc a b, e y = -e a
    · obtain ⟨y, z, haz, hzy, hyb, hy, hlow⟩ := exists_pivot he hE hea hT
      have hyE : |e y| = E := by rw [hy, abs_neg, hea]
      rcases ih (he.mono (Set.Icc_subset_Icc_left (by linarith))) hyb hyE with
        ⟨q, hq, hqs, hql⟩ | ⟨v, hv, hvs, σ, hσ, hvE⟩
      · left
        refine ⟨(X - C z) * q, ?_, fun x hx hxE => ?_, fun x hx => ?_⟩
        · refine (degree_mul_le _ _).trans ?_
          rw [degree_X_sub_C, Nat.cast_succ, add_comm]
          exact add_le_add_left hq 1
        · simp only [eval_mul, eval_sub, eval_X, eval_C]
          rcases lt_or_ge x y with hxy | hxy
          · obtain ⟨h1, h2⟩ := hlow x hx hxE hxy
            have := hql x hxy.le
            rw [hy] at this
            rw [h1]
            nlinarith
          · have := hqs x ⟨hxy, hx.2⟩ hxE
            nlinarith
        · simp only [eval_mul, eval_sub, eval_X, eval_C]
          have := hql x (by linarith)
          rw [hy] at this
          nlinarith
      · right
        have h0 := hvE 0
        obtain ⟨⟨hv0y, -⟩, -⟩ := hvs 0
        have hvs' : ∀ i, v i ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := fun i =>
          ⟨⟨by linarith [(hvs i).1.1], (hvs i).1.2⟩, (hvs i).2⟩
        have hys : y ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨by linarith, hyb⟩, hyE⟩
        have has : a ∈ {x | x ∈ Set.Icc a b ∧ |e x| = E} := ⟨⟨le_rfl, hab⟩, hea⟩
        simp only [Fin.val_zero, pow_zero, mul_one] at h0
        rcases (abs_eq hE.le).1 hea with h | h
        · rcases hσ with rfl | rfl
          · exact alternatesOn_vecCons hv hvs' (Or.inl rfl) hvE hys
              (lt_of_le_of_ne hv0y fun h' => by rw [← h'] at h0; linarith) (by linarith)
          · exact alternatesOn_vecCons hv hvs' (Or.inr rfl) hvE has (by linarith)
              (by linarith)
        · rcases hσ with rfl | rfl
          · exact alternatesOn_vecCons hv hvs' (Or.inl rfl) hvE has (by linarith)
              (by linarith)
          · exact alternatesOn_vecCons hv hvs' (Or.inr rfl) hvE hys
              (lt_of_le_of_ne hv0y fun h' => by rw [← h'] at h0; linarith) (by linarith)
    · exact Or.inl (exists_degree_le_const _ hE hea hT)

/-- An error that vanishes on $[a, b]$, $a < b$, alternates there at any number $k$ of points
with level $0$: the zero-error case of the equioscillation theorem.
Proof: S, about 20 lines. The equispaced points $x_i = a + (b - a)i/(k + 1)$ (strictly increasing,
in $[a, b]$: `div_lt_div_of_pos_right`, `div_le_iff₀`; prototype
`exists_equioscillation_of_norm_sub_eq_minimaxError`, zero branch), $\sigma = 1$, and
$0 \le 1 \cdot (-1)^i \cdot 0$ by `hg`. -/
private theorem alternatesOn_Icc_zero_of_eq_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a < b) (k : ℕ)
    (hg : ∀ x ∈ Set.Icc a b, g x = 0) : AlternatesOn g (Set.Icc a b) k 0 := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hmem : ∀ i : Fin k, a + (b - a) * ((i : ℕ) : ℝ) / (k + 1) ∈ Set.Icc a b := by
    intro i
    have hi : ((i : ℕ) : ℝ) ≤ k := Nat.cast_le.mpr (le_of_lt i.isLt)
    have h0 : 0 ≤ (b - a) * ((i : ℕ) : ℝ) / (k + 1) :=
      div_nonneg (mul_nonneg hba.le (Nat.cast_nonneg _)) hk.le
    have h1 : (b - a) * ((i : ℕ) : ℝ) / (k + 1) ≤ b - a := by
      rw [div_le_iff₀ hk]
      nlinarith
    exact ⟨by linarith, by linarith⟩
  refine ⟨fun i => a + (b - a) * ((i : ℕ) : ℝ) / (k + 1), ?_, fun i => hmem i, 1, Or.inl rfl,
    fun i => ?_⟩
  · intro i j hij
    have h1 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := Nat.cast_lt.mpr hij
    have h3 : (b - a) * ((i : ℕ) : ℝ) < (b - a) * ((j : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left h1 hba
    have := div_lt_div_of_pos_right h3 hk
    change a + (b - a) * ((i : ℕ) : ℝ) / (k + 1) < a + (b - a) * ((j : ℕ) : ℝ) / (k + 1)
    linarith
  · rw [hg _ (hmem i), mul_zero]

/-- A best approximation with positive error attains it: if $\deg p \le n$,
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$ and $E_n(f; [a, b]) > 0$, the extremal set
$\{x \in [a, b] : \lvert f(x) - p(x) \rvert = E_n\}$ has a least element.
Proof: M, about 25 lines. The extremal set is closed in the compact $[a, b]$
(`ContinuousOn.preimage_isClosed_of_isClosed` with `(hf.sub p.continuousOn).abs`,
`isClosed_singleton`), so `IsCompact.exists_isLeast` once it is nonempty. Nonempty: otherwise
$\lvert f - p \rvert < E_n$ on $[a, b]$ (`hbest`, `lt_of_le_of_ne`); $[a, b]$ is nonempty (else
$E_n = 0$: `Set.Icc_eq_empty`, `Real.sInf_univ`), so `IsCompact.exists_isMaxOn` gives
$M = \max \lvert f - p \rvert < E_n$ and `minimaxError_le_of_isUniformApproxOn hp` with $M$
contradicts it. -/
private theorem exists_isLeast_abs_sub_eval_eq_minimaxError {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n))
    (hE : 0 < minimaxError f (Set.Icc a b) n) :
    ∃ c, IsLeast {x | x ∈ Set.Icc a b ∧ |f x - p.eval x| = minimaxError f (Set.Icc a b) n} c := by
  have he : ContinuousOn (fun x => |f x - p.eval x|) (Set.Icc a b) :=
    (hf.sub p.continuous.continuousOn).abs
  have hK : IsClosed (Set.Icc a b ∩ (fun x => |f x - p.eval x|) ⁻¹'
      {minimaxError f (Set.Icc a b) n}) :=
    he.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hKc := isCompact_Icc.of_isClosed_subset hK Set.inter_subset_left
  have hKne : (Set.Icc a b ∩ (fun x => |f x - p.eval x|) ⁻¹'
      {minimaxError f (Set.Icc a b) n}).Nonempty := by
    by_contra hne
    have hIcc : (Set.Icc a b).Nonempty := by
      by_contra h0
      rw [Set.not_nonempty_iff_eq_empty] at h0
      have h1 := minimaxError_le_of_isUniformApproxOn (f := f) (s := Set.Icc a b) hp
        (le_refl (0:ℝ)) (fun x hx => by simp [h0] at hx)
      linarith
    have hle : ∀ x ∈ Set.Icc a b, |f x - p.eval x| ≤ minimaxError f (Set.Icc a b) n := by
      intro x hx
      have := hbest x hx
      rwa [Real.dist_eq, abs_sub_comm] at this
    have hlt : ∀ x ∈ Set.Icc a b, |f x - p.eval x| < minimaxError f (Set.Icc a b) n :=
      fun x hx => lt_of_le_of_ne (hle x hx) (fun h => hne ⟨x, hx, h⟩)
    obtain ⟨x₀, hx₀, hmax⟩ := isCompact_Icc.exists_isMaxOn hIcc he
    have hmax' := isMaxOn_iff.mp hmax
    have h2 := minimaxError_le_of_isUniformApproxOn (s := Set.Icc a b) hp
      (abs_nonneg (f x₀ - p.eval x₀)) (fun x hx => by
        rw [Real.dist_eq, abs_sub_comm]
        exact hmax' x hx)
    linarith [hlt x₀ hx₀]
  exact hKc.exists_isLeast hKne

/-- The descent step: a best approximation $p$ with positive error admits no correction $q$ of
degree at most $n$ with the sign of $f - p$ at every extremal point of $[a, b]$.
Proof: M, about 45 lines. Suppose $q$ has the signs; $E := E_n > 0$. Restrict to
`C(Set.Icc a b, ℝ)` (compact by `isCompact_Icc`): $g$ the restriction of $f - p$
(`ContinuousOn.restrict`), $h :=$ `q.toContinuousMapOn (Set.Icc a b)`. Then
$\lVert g \rVert = E$: $\le$ by `ContinuousMap.norm_le` and `hbest`; $\ge$ because
`minimaxError_le_of_isUniformApproxOn hp` with $\lVert g \rVert$ (`ContinuousMap.norm_coe_le_norm`)
gives $E \le \lVert g \rVert$. `ContinuousMap.exists_pos_norm_sub_smul_lt g h` (signs from the
hypothesis at $|g x| = \lVert g \rVert$) gives $t > 0$ with $\lVert g - t h \rVert < E$; the
polynomial $p + t q$ has degree at most $n$ (`degreeLE`, `Submodule.add_mem`, `smul_mem`) and
error at most $\lVert g - t h \rVert$ on $[a, b]$ (`eval_add`, `eval_smul`, `ring`), so
`minimaxError_le_of_isUniformApproxOn` gives $E \le \lVert g - t h \rVert < E$. Prototype: the
left case of `NLAlib.exists_alternating_extrema_of_norm_sub_eq_minimaxError`. -/
private theorem not_forall_mul_pos_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n))
    (hE : 0 < minimaxError f (Set.Icc a b) n) {q : ℝ[X]} (hq : q.degree ≤ n) :
    ¬ ∀ x ∈ Set.Icc a b, |f x - p.eval x| = minimaxError f (Set.Icc a b) n →
      0 < (f x - p.eval x) * q.eval x := by
  intro hsign
  have : CompactSpace (Set.Icc a b) := isCompact_iff_compactSpace.mp isCompact_Icc
  set E := minimaxError f (Set.Icc a b) n with hEdef
  let g : C(Set.Icc a b, ℝ) :=
    ⟨fun x : Set.Icc a b => f x - p.eval (x : ℝ),
      (hf.sub (Polynomial.continuous p).continuousOn).domRestrict⟩
  let h : C(Set.Icc a b, ℝ) := q.toContinuousMapOn (Set.Icc a b)
  have hgx : ∀ x : Set.Icc a b, |g x| ≤ E := fun x => by
    have := hbest x x.2
    rw [Real.dist_eq, abs_sub_comm] at this
    exact this
  have hgE : ‖g‖ = E := by
    refine le_antisymm ((ContinuousMap.norm_le g hE.le).mpr fun x => ?_) ?_
    · rw [Real.norm_eq_abs]; exact hgx x
    · refine minimaxError_le_of_isUniformApproxOn hp (norm_nonneg g) fun x hx => ?_
      have := g.norm_coe_le_norm ⟨x, hx⟩
      rw [Real.norm_eq_abs] at this
      rw [Real.dist_eq, abs_sub_comm]
      exact this
  obtain ⟨t, ht, htlt⟩ := ContinuousMap.exists_pos_norm_sub_smul_lt g h (by rwa [hgE])
    (fun x hx => hsign x x.2 (by rw [← hgE]; exact hx))
  have hdeg : (p + t • q).degree ≤ n := by
    have hmem : p + t • q ∈ degreeLE ℝ n :=
      (degreeLE ℝ n).add_mem (mem_degreeLE.mpr hp) ((degreeLE ℝ n).smul_mem t (mem_degreeLE.mpr hq))
    exact mem_degreeLE.mp hmem
  have herr : Metric.IsUniformApproxOn (fun x => (p + t • q).eval x) f (Set.Icc a b)
      ‖g - t • h‖ := fun x hx => by
    have h1 := (g - t • h).norm_coe_le_norm ⟨x, hx⟩
    have e : (g - t • h) ⟨x, hx⟩ = f x - (p.eval x + t * q.eval x) := by
      change f x - p.eval x - t * q.eval x = f x - (p.eval x + t * q.eval x)
      ring
    rw [e, Real.norm_eq_abs] at h1
    rw [Real.dist_eq, abs_sub_comm]
    dsimp only
    rw [Polynomial.eval_add, Polynomial.eval_smul, smul_eq_mul]
    exact h1
  have := minimaxError_le_of_isUniformApproxOn hdeg (norm_nonneg _) herr
  linarith

/-- **Chebyshev's equioscillation theorem, necessity.** Let $a < b$, $f$ continuous on
$[a, b]$, and $p$ a real polynomial of degree at most $n$ with
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$ (a best approximation). Then $f - p$
alternates on $[a, b]$ at $n + 2$ points with level $E_n(f; [a, b])$: it equioscillates
(`AlternatesOn.exists_eq_of_abs_le`). [Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1]
(locators to check).
Proof: M, about 25 lines here, about 110 with the three private lemmas above it (the split is
planned: zero case, attained extremal set, descent step). If $E_n = 0$, $f = p$ on $[a, b]$
(`hbest`: `dist_le_zero`) and `alternatesOn_Icc_zero_of_eq_zero`. If $E = E_n > 0$
(`minimaxError_nonneg`), `exists_isLeast_abs_sub_eval_eq_minimaxError` gives the least
extremal point $c$. Apply `exists_degree_le_or_alternatesOn n` to $e = f - p$ on $[c, b]$
(`(hf.sub p.continuousOn).mono (Set.Icc_subset_Icc_left _)`): the alternation is the
conclusion by `AlternatesOn.mono` (the extremal set of $[c, b]$ lies in $[a, b]$, level $E$); a
sign-matching $q$ has the sign of $e$ at every extremal point of $[a, b]$ (each is $\ge c$, by
leastness), contradicting `not_forall_mul_pos_of_isUniformApproxOn_minimaxError`. Prototype:
`NLAlib.exists_alternating_extrema_of_norm_sub_eq_minimaxError`
(`Polynomial/BestApproximation/Equioscillation`, proved).
Result: equioscillation -/
theorem alternatesOn_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) :
    AlternatesOn (fun x => f x - p.eval x) (Set.Icc a b) (n + 2)
      (minimaxError f (Set.Icc a b) n) := by
  rcases (minimaxError_nonneg f _ n).eq_or_lt with hE | hE
  · have hz : ∀ x ∈ Set.Icc a b, f x - p.eval x = 0 := fun x hx => by
      have h0 : dist (p.eval x) (f x) ≤ 0 := (hbest x hx).trans_eq hE.symm
      exact sub_eq_zero.mpr (dist_le_zero.mp h0).symm
    rw [← hE]
    exact alternatesOn_Icc_zero_of_eq_zero hab (n + 2) hz
  · obtain ⟨c, hc⟩ := exists_isLeast_abs_sub_eval_eq_minimaxError hf hp hbest hE
    rcases exists_degree_le_or_alternatesOn n
        (e := fun x => f x - p.eval x) (a := c) (b := b)
        ((hf.sub p.continuousOn).mono (Set.Icc_subset_Icc_left hc.1.1.1)) hE hc.1.1.2 hc.1.2
      with ⟨q, hq, hqs, -⟩ | halt
    · exfalso
      exact not_forall_mul_pos_of_isUniformApproxOn_minimaxError hf hp hbest hE hq
        (fun x hx hxe => hqs x ⟨hc.2 ⟨hx, hxe⟩, hx.2⟩ hxe)
    · refine halt.mono (fun x hx => ?_) le_rfl
      exact ⟨hc.1.1.1.trans hx.1.1, hx.1.2⟩

/-- **Chebyshev's equioscillation theorem.** Let $a < b$, $f$ continuous on $[a, b]$ and $p$ a
real polynomial of degree at most $n$. Then $p$ is a best approximation,
$\lvert f - p \rvert \le E_n(f; [a, b])$ on $[a, b]$, if and only if for some $\varepsilon$,
$\lvert f - p \rvert \le \varepsilon$ on $[a, b]$ and $f - p$ alternates at $n + 2$ points of
$[a, b]$ with level $\varepsilon$ (and then $\varepsilon = E_n(f; [a, b])$).
[Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1] (locators to check).
Proof: S, about 8 lines. Forward: `alternatesOn_of_isUniformApproxOn_minimaxError` with
$\varepsilon = E_n$. Backward: `AlternatesOn.minimaxError_eq` rewrites $E_n = \varepsilon$.
Result: equioscillation -/
theorem isUniformApproxOn_minimaxError_iff_exists_alternatesOn {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n) :
    Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
        (minimaxError f (Set.Icc a b) n) ↔
      ∃ ε : ℝ, Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε ∧
        AlternatesOn (fun x => f x - p.eval x) (Set.Icc a b) (n + 2) ε := by
  constructor
  · intro h
    exact ⟨_, h, alternatesOn_of_isUniformApproxOn_minimaxError hab hf hp h⟩
  · rintro ⟨ε, hε, halt⟩
    rw [halt.minimaxError_eq hp hε]
    exact hε

/-- **The best approximation is unique**: for $a < b$ and $f$ continuous on $[a, b]$, two real
polynomials $p, q$ of degree at most $n$ that are both within $E_n(f; [a, b])$ of $f$ on
$[a, b]$ are equal. [Trefethen2019, Theorem 10.1]; [Rivlin1981, Ch. 1] (locators to check).
Proof: M, about 40 lines. The midpoint $r = (p + q)/2$ is also best (triangle inequality,
`minimaxError_le_of_isUniformApproxOn` both ways). By
`alternatesOn_of_isUniformApproxOn_minimaxError` and `AlternatesOn.exists_eq_of_abs_le`,
$\lvert f - r \rvert = E_n$ at $n + 2$ points; there
$\lvert f - p \rvert, \lvert f - q \rvert \le E_n$ and $2(f - r) = (f - p) + (f - q)$ force
$p = q$ (`abs_le`, `nlinarith`); `Polynomial.eq_of_degree_sub_lt_of_eval_index_eq` with $n + 2$
distinct nodes. Prototype: `NLAlib.eq_of_norm_sub_eq_minimaxError`
(`Polynomial/BestApproximation/Equioscillation`, proved).
Result: best-approximation-uniqueness -/
theorem eq_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p q : ℝ[X]} (hp : p.degree ≤ n)
    (hq : q.degree ≤ n)
    (hpb : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n))
    (hqb : Metric.IsUniformApproxOn (fun x => q.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) : p = q := by
  have hdeg : ((1 / 2 : ℝ) • (p + q)).degree ≤ n :=
    (Polynomial.degree_smul_le _ _).trans ((Polynomial.degree_add_le _ _).trans (max_le hp hq))
  have hev : ∀ x, ((1 / 2 : ℝ) • (p + q)).eval x = 1 / 2 * (p.eval x + q.eval x) := by
    intro x
    simp only [Polynomial.eval_smul, Polynomial.eval_add, smul_eq_mul]
  have hrb : Metric.IsUniformApproxOn (fun x => ((1 / 2 : ℝ) • (p + q)).eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n) := by
    intro x hx
    change dist (((1 / 2 : ℝ) • (p + q)).eval x) (f x) ≤ _
    have h1 : dist (p.eval x) (f x) ≤ minimaxError f (Set.Icc a b) n := hpb x hx
    have h2 : dist (q.eval x) (f x) ≤ minimaxError f (Set.Icc a b) n := hqb x hx
    rw [Real.dist_eq, abs_le] at h1 h2 ⊢
    rw [hev x]
    constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
  have halt := alternatesOn_of_isUniformApproxOn_minimaxError hab hf hdeg hrb
  have hb : ∀ x ∈ Set.Icc a b,
      |f x - ((1 / 2 : ℝ) • (p + q)).eval x| ≤ minimaxError f (Set.Icc a b) n := by
    intro x hx
    rw [abs_sub_comm, ← Real.dist_eq]
    exact hrb x hx
  obtain ⟨x, hxm, hxmem, σ, hσ, hxeq⟩ := halt.exists_eq_of_abs_le hb
  have hpq : ∀ i : Fin (n + 2), p.eval (x i) = q.eval (x i) := by
    intro i
    have hi : f (x i) - ((1 / 2 : ℝ) • (p + q)).eval (x i)
        = σ * (-1) ^ (i : ℕ) * minimaxError f (Set.Icc a b) n := hxeq i
    have h1 : dist (p.eval (x i)) (f (x i)) ≤ minimaxError f (Set.Icc a b) n :=
      hpb (x i) (hxmem i)
    have h2 : dist (q.eval (x i)) (f (x i)) ≤ minimaxError f (Set.Icc a b) n :=
      hqb (x i) (hxmem i)
    rw [Real.dist_eq, abs_le] at h1 h2
    rw [hev] at hi
    rcases hσ with rfl | rfl <;> rcases neg_one_pow_eq_or ℝ (i : ℕ) with h | h <;>
      rw [h] at hi <;> linarith [h1.1, h1.2, h2.1, h2.2]
  refine Polynomial.eq_of_degree_sub_lt_of_eval_index_eq Finset.univ
    (fun i _ j _ hij => hxm.injective hij) ?_ (fun i _ => hpq i)
  refine lt_of_le_of_lt ((Polynomial.degree_sub_le p q).trans (max_le hp hq)) ?_
  rw [Finset.card_univ, Fintype.card_fin]
  exact_mod_cast (by omega : n < n + 2)

/-- **The best approximation interpolates**: for $a < b$, $f$ continuous on $[a, b]$ and $p$ a
best approximation of degree at most $n$, there are $n + 1$ distinct points of $(a, b)$ at which
$p = f$; $p$ is the Lagrange interpolant of $f$ there (`Lagrange.eq_interpolate_of_eval_eq`).
[Trefethen2019, Ch. 10] (locator to check); there on $[-1, 1]$.
Proof: M, about 40 lines. If $E_n > 0$, `alternatesOn_of_isUniformApproxOn_minimaxError`
gives $n + 2$ points where $f - p$ changes sign, and `exists_strictMono_eq_zero_of_mul_neg`
gives $n + 1$ ordered zeros strictly inside, hence in $(a, b)$; take their image `Finset`
(`Finset.card_image_of_injective`). If $E_n = 0$, $f = p$ on $[a, b]$ and any $n + 1$
equispaced interior points work. Prototype:
`NLAlib.exists_interpolate_eq_of_norm_sub_eq_minimaxError`
(`Polynomial/BestApproximation/BestInterpolant`, proved).
Result: best-approximant-interpolates -/
theorem exists_eval_eq_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) :
    ∃ t : Finset ℝ, t.card = n + 1 ∧ (t : Set ℝ) ⊆ Set.Ioo a b ∧ ∀ x ∈ t, p.eval x = f x := by
  have key : ∃ c : Fin (n + 1) → ℝ, StrictMono c ∧ (∀ i, c i ∈ Set.Ioo a b) ∧
      ∀ i, p.eval (c i) = f (c i) := by
    rcases (minimaxError_nonneg f (Set.Icc a b) n).eq_or_lt with hE | hE
    · have hba : 0 < b - a := sub_pos.mpr hab
      have hmem : ∀ i : Fin (n + 1), a + (b - a) * ((i : ℝ) + 1) / (n + 2) ∈ Set.Ioo a b := by
        intro i
        have hi : ((i : ℕ) : ℝ) ≤ n := by
          have := Nat.lt_succ_iff.mp i.isLt
          exact_mod_cast this
        have hq0 : 0 < (b - a) * ((i : ℝ) + 1) / (n + 2) :=
          div_pos (mul_pos hba (by positivity)) (by positivity)
        have hq1 : (b - a) * ((i : ℝ) + 1) / (n + 2) < b - a := by
          rw [div_lt_iff₀ (by positivity)]
          nlinarith
        constructor <;> linarith
      refine ⟨fun i => a + (b - a) * ((i : ℝ) + 1) / (n + 2), ?_, hmem, ?_⟩
      · intro i j hij
        have h1 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast Fin.lt_def.mp hij
        have h2 : (b - a) * ((i : ℝ) + 1) < (b - a) * ((j : ℝ) + 1) :=
          mul_lt_mul_of_pos_left (by linarith) hba
        have h3 : (b - a) * ((i : ℝ) + 1) / (n + 2) < (b - a) * ((j : ℝ) + 1) / (n + 2) :=
          div_lt_div_of_pos_right h2 (by positivity)
        change a + _ < a + _
        linarith
      · intro i
        have h := hbest _ (Set.Ioo_subset_Icc_self (hmem i))
        rw [← hE] at h
        exact dist_le_zero.mp h
    · obtain ⟨x, hxmono, hxmem, σ, hσ, hx⟩ := alternatesOn_iff.mp
        (alternatesOn_of_isUniformApproxOn_minimaxError hab hf hp hbest)
      have hsign : ∀ i : Fin (n + 1),
          (f (x i.castSucc) - p.eval (x i.castSucc)) * (f (x i.succ) - p.eval (x i.succ)) < 0 := by
        intro i
        have hs := hx i.castSucc
        have ht := hx i.succ
        simp only [Fin.val_castSucc, Fin.val_succ, pow_succ] at hs ht
        have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
        have hs2 : (-1 : ℝ) ^ (i : ℕ) * (-1) ^ (i : ℕ) = 1 := by
          rw [← mul_pow]; norm_num
        have hprod := mul_pos (lt_of_lt_of_le hE hs) (lt_of_lt_of_le hE ht)
        have hid : (σ * (-1) ^ (i : ℕ) * (f (x i.castSucc) - p.eval (x i.castSucc))) *
            (σ * ((-1) ^ (i : ℕ) * -1) * (f (x i.succ) - p.eval (x i.succ))) =
            -((f (x i.castSucc) - p.eval (x i.castSucc)) * (f (x i.succ) - p.eval (x i.succ))) := by
          linear_combination (-((f (x i.castSucc) - p.eval (x i.castSucc)) *
            (f (x i.succ) - p.eval (x i.succ)) * ((-1 : ℝ) ^ (i : ℕ) * (-1) ^ (i : ℕ)))) * hσ2 +
            (-((f (x i.castSucc) - p.eval (x i.castSucc)) *
            (f (x i.succ) - p.eval (x i.succ)))) * hs2
        linarith
      have hf' : ContinuousOn (fun x => f x - p.eval x) (Set.Icc (x 0) (x (Fin.last (n + 1)))) :=
        (hf.sub p.continuousOn).mono (Set.Icc_subset_Icc (hxmem 0).1 (hxmem _).2)
      obtain ⟨c, hcmono, hcspec⟩ := exists_strictMono_eq_zero_of_mul_neg hxmono hf' hsign
      refine ⟨c, hcmono, fun i => ?_, fun i => ?_⟩
      · obtain ⟨h1, h2⟩ := hcspec i
        exact ⟨lt_of_le_of_lt (hxmem _).1 h1.1, lt_of_lt_of_le h1.2 (hxmem _).2⟩
      · have h : f (c i) - p.eval (c i) = 0 := (hcspec i).2
        linarith
  obtain ⟨c, hcm, hcin, hceq⟩ := key
  refine ⟨Finset.univ.image c, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hcm.injective]
    simp
  · intro y hy
    rw [Finset.mem_coe, Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hcin i
  · intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hceq i

/-! ### The chosen best approximation on an interval -/

/-- **The chosen best approximation equioscillates**: for $a < b$ and $f$ continuous on $[a, b]$,
$f - \mathrm{minimaxPoly}\ f\ [a, b]\ n$ alternates on $[a, b]$ at $n + 2$ points with level
$E_n(f; [a, b])$. [Trefethen2019, Theorem 10.1].
Proof: S, about 3 lines. `alternatesOn_of_isUniformApproxOn_minimaxError` with
`degree_minimaxPoly_le` and `isUniformApproxOn_minimaxPoly isCompact_Icc hf`.
Result: equioscillation -/
theorem alternatesOn_minimaxPoly {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) (n : ℕ) :
    AlternatesOn (fun x => f x - (minimaxPoly f (Set.Icc a b) n).eval x) (Set.Icc a b) (n + 2)
      (minimaxError f (Set.Icc a b) n) :=
  alternatesOn_of_isUniformApproxOn_minimaxError hab hf (degree_minimaxPoly_le f _ n)
    (isUniformApproxOn_minimaxPoly isCompact_Icc hf n)

/-- **Every best approximation is the chosen one**: for $a < b$, $f$ continuous on $[a, b]$ and
$p$ a real polynomial of degree at most $n$ with $\lvert f - p \rvert \le E_n(f; [a, b])$ on
$[a, b]$, $p = \mathrm{minimaxPoly}\ f\ [a, b]\ n$. [Trefethen2019, Theorem 10.1].
Proof: S, about 3 lines. `eq_of_isUniformApproxOn_minimaxError` with `degree_minimaxPoly_le` and
`isUniformApproxOn_minimaxPoly isCompact_Icc hf`.
Result: best-approximation-uniqueness -/
theorem eq_minimaxPoly_of_isUniformApproxOn_minimaxError {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hf : ContinuousOn f (Set.Icc a b)) {n : ℕ} {p : ℝ[X]} (hp : p.degree ≤ n)
    (hbest : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b)
      (minimaxError f (Set.Icc a b) n)) : p = minimaxPoly f (Set.Icc a b) n :=
  eq_of_isUniformApproxOn_minimaxError hab hf hp (degree_minimaxPoly_le f _ n) hbest
    (isUniformApproxOn_minimaxPoly isCompact_Icc hf n)

/-! ### The Chebyshev example -/

/-- **$T_n$ alternates at $n + 1$ points**: the Chebyshev polynomial $T_n$ alternates on
$[-1, 1]$ at $n + 1$ points with level $1$, at the extrema $\cos(j\pi/n)$ in increasing order.
[Trefethen2019, Ch. 3].
Proof: M, about 15 lines. The points $x_i = $ `Polynomial.Chebyshev.node n (n - i)`, strictly
increasing by Mathlib's `node_lt` (`node_lt (hj : j ≤ n) (hij : i < j) : node n j < node n i`,
with `Nat.sub_le` and `omega`); `eval_T_real_node` gives $T_n(x_i) = (-1)^{n - i}$, so
$\sigma = (-1)^n$ (`pow_sub`, or parity cases); `node_mem_Icc`. The case $n = 0$ ($T_0 = 1$,
one point) is covered by the same formula. -/
theorem alternatesOn_eval_T_real (n : ℕ) :
    AlternatesOn (fun x => (Chebyshev.T ℝ (n : ℤ)).eval x) (Set.Icc (-1) 1) (n + 1) 1 := by
  rw [alternatesOn_iff]
  refine ⟨fun i => Polynomial.Chebyshev.node n (n - (i : ℕ)), ?_, ?_, (-1) ^ n, ?_, ?_⟩
  · intro i j hij
    exact Polynomial.Chebyshev.node_lt (Nat.sub_le n _)
      (by have := Fin.lt_def.mp hij; have := j.isLt; omega)
  · intro i
    exact Polynomial.Chebyshev.node_mem_Icc
  · rcases neg_one_pow_eq_or ℝ n with h | h
    · exact Or.inl h
    · exact Or.inr h
  · intro i
    have hi : (i : ℕ) ≤ n := by have := i.isLt; omega
    change 1 ≤ (-1) ^ n * (-1) ^ (i : ℕ) * eval (Polynomial.Chebyshev.node n (n - (i : ℕ)))
      (Polynomial.Chebyshev.T ℝ (n : ℤ))
    rw [Polynomial.Chebyshev.eval_T_real_node (Finset.mem_Iic.mpr (Nat.sub_le n _))]
    rw [← pow_add, ← pow_add]
    have e : n + (i : ℕ) + (n - (i : ℕ)) = 2 * n := by omega
    rw [e, pow_mul]
    norm_num

/-- **The minimax error of $x^{n + 1}$**: on $[-1, 1]$, the best approximation of $x^{n + 1}$ by
polynomials of degree at most $n$ has error $E_n(x^{n + 1}; [-1, 1]) = 2^{-n}$, attained by
$x^{n + 1} - 2^{-n}T_{n + 1}$; equivalently, $2^{-n}T_{n + 1}$ is the monic polynomial of degree
$n + 1$ of least uniform norm on $[-1, 1]$. [GolubMeurant2010, §2.5.1, Theorem 2.15];
[Trefethen2019, Ch. 10].
Proof: M, about 20 lines. `AlternatesOn.minimaxError_eq` with $p = X^{n + 1} - 2^{-n}T_{n + 1}$,
of degree at most $n$ (`leadingCoeff_T`, `natDegree_T`, `degree_sub_lt`), error
$2^{-n}T_{n + 1}$, bounded by $2^{-n}$ (`abs_eval_T_real_le_one`) and alternating by
`alternatesOn_eval_T_real` scaled by $2^{-n} > 0$. Alternatively from
`Polynomial.Chebyshev.isLeast_chebyshev_monic_minimax`.
Result: chebyshev-monic-minimal -/
theorem minimaxError_pow_Icc_neg_one_one (n : ℕ) :
    minimaxError (fun x => x ^ (n + 1)) (Set.Icc (-1) 1) n = ((2 : ℝ) ^ n)⁻¹ := by
  have hc0 : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have hTlead : (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).leadingCoeff = 2 ^ n := by
    rw [Chebyshev.leadingCoeff_T]
    simp; omega
  have hTdeg : (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).natDegree = n + 1 := by
    rw [Chebyshev.natDegree_T]
    rfl
  have hT0 : Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ) ≠ 0 := by
    intro h
    rw [h, Polynomial.leadingCoeff_zero] at hTlead
    exact (by positivity : (2 : ℝ) ^ n ≠ 0) hTlead.symm
  have hfun : (fun x : ℝ => x ^ (n + 1) - (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ *
      Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x) =
      fun x => ((2 : ℝ) ^ n)⁻¹ * (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x := by
    funext x
    simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C]
    ring
  have hdeg : (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ *
      Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).degree ≤ (n : WithBot ℕ) := by
    have hq : (C ((2 : ℝ) ^ n)⁻¹ * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).degree =
        ((n + 1 : ℕ) : WithBot ℕ) := by
      rw [degree_C_mul hc0.ne', degree_eq_natDegree hT0, hTdeg]
    have hlc : (X ^ (n + 1) : ℝ[X]).leadingCoeff =
        (C ((2 : ℝ) ^ n)⁻¹ * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).leadingCoeff := by
      rw [leadingCoeff_X_pow, leadingCoeff_mul, leadingCoeff_C, hTlead]
      exact (inv_mul_cancel₀ (by positivity)).symm
    have hlt := degree_sub_lt_left (by rw [degree_X_pow, hq]) (pow_ne_zero _ X_ne_zero) hlc
    rw [degree_X_pow] at hlt
    exact Order.le_of_lt_succ hlt
  have halt : AlternatesOn (fun x : ℝ => x ^ (n + 1) - (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ *
      Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x) (Set.Icc (-1) 1) (n + 2) ((2 : ℝ) ^ n)⁻¹ := by
    rw [hfun]
    obtain ⟨x, hx, hxs, σ, hσ, h⟩ := alternatesOn_eval_T_real (n + 1)
    refine ⟨x, hx, hxs, σ, hσ, fun i => ?_⟩
    have := mul_le_mul_of_nonneg_left (h i) hc0.le
    linarith
  have hbound : Metric.IsUniformApproxOn
      (fun x => (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x)
      (fun x => x ^ (n + 1)) (Set.Icc (-1) 1) ((2 : ℝ) ^ n)⁻¹ := by
    intro x hx
    have hsub : (X ^ (n + 1) - C ((2 : ℝ) ^ n)⁻¹ * Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x
        - x ^ (n + 1) = -(((2 : ℝ) ^ n)⁻¹ * (Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x) := by
      simp only [eval_sub, eval_pow, eval_X, eval_mul, eval_C]
      ring
    rw [Real.dist_eq, hsub, abs_neg, abs_mul, abs_of_pos hc0]
    have hsub : x ∈ Set.Icc (Real.cos Real.pi) (Real.cos 0) := by
      rw [Real.cos_pi, Real.cos_zero]
      exact hx
    obtain ⟨θ, -, hθ⟩ :=
      intermediate_value_Icc' Real.pi_pos.le Real.continuous_cos.continuousOn hsub
    have hcos := Chebyshev.T_real_cos θ ((n + 1 : ℕ) : ℤ)
    rw [hθ] at hcos
    have hT1 : |(Chebyshev.T ℝ ((n + 1 : ℕ) : ℤ)).eval x| ≤ 1 := by
      rw [hcos]
      exact Real.abs_cos_le_one _
    exact mul_le_of_le_one_right hc0.le hT1
  exact halt.minimaxError_eq hdeg hbound

end NLAlib
