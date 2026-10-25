/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Polynomial.Order
public import NLAlib.Polynomial.Orthogonal.Zeros
public import NLAlibScaffold.Polynomial.Orthogonal.Recurrence

/-!
# Zeros of orthogonal polynomials: the theorems of stage KS7

Statements for `NLAlib/Polynomial/Orthogonal/Zeros.lean` whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.5). If a finite measure $\mu$ supported in
$[a, b]$ is positive definite up to degree $k$, the orthogonal polynomial $\pi_k$ has $k$ real
simple zeros, all in $[a, b]$, and is the nodal polynomial of the Gauss nodes; otherwise $\mu$ is
carried by the Gauss nodes. Either way the nodal polynomial of the Gauss nodes is orthogonal to
the lower degrees.

## Main results

* `NLAlib.card_gaussNodes_le`: at most $k$ Gauss nodes.
* `NLAlib.IsMomentPosDef.card_roots_orthogonalPolynomial`,
  `NLAlib.IsMomentPosDef.nodup_roots_orthogonalPolynomial`: real simple zeros.
* `NLAlib.IsMomentPosDef.nodal_gaussNodes`, `NLAlib.IsMomentPosDef.card_gaussNodes`,
  `NLAlib.IsMomentPosDef.gaussNodes_subset_Icc`: $k$ nodes in $[a, b]$, with nodal polynomial
  $\pi_k$.
* `NLAlib.ae_mem_gaussNodes_of_not_isMomentPosDef`: the degenerate case.
* `NLAlib.isOrthogonalPolynomial_nodal_gaussNodes`: the Gauss hypothesis for every $k$.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- There are at most $k$ Gauss nodes of order $k$, for every measure $\mu$ on $\mathbb{R}$.
Proof: S, about 5 lines. `Multiset.toFinset_card_le`, `card_roots'`,
`natDegree_orthogonalPolynomial`. -/
theorem card_gaussNodes_le (μ : Measure ℝ) (k : ℕ) : (gaussNodes μ k).card ≤ k := by
  unfold gaussNodes
  calc (orthogonalPolynomial μ k).roots.toFinset.card ≤
      Multiset.card (orthogonalPolynomial μ k).roots := Multiset.toFinset_card_le _
    _ ≤ (orthogonalPolynomial μ k).natDegree := card_roots' _
    _ = k := natDegree_orthogonalPolynomial μ k

section Definite

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- The shared step of the three zero theorems: if $\mu$, finite and supported in $[a, b]$, is
positive definite up to degree $k$, $p$ is orthogonal to the polynomials of degree less than $k$,
$\deg r < k$, $pr \ge 0$ $\mu$-almost everywhere, and the zeros of $pr$ in $[a, b]$ lie in a set
$s$ of fewer than $k$ points, then we have a contradiction.
Proof: M, about 25 lines. $\int pr = 0$ (`hp`, `hr`) and $pr \ge 0$ a.e., so $pr = 0$ a.e.
(`integral_eq_zero_iff_of_nonneg_ae`, integrability `integrable_eval_of_ae_mem_Icc`); with `hμ`
and `hz`, $\mu$ is carried by $s$; `isMomentPosDef_iff_forall_finset` contradicts `hs`. -/
private theorem IsMomentPosDef.false_of_ae_nonneg_mul {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : IsOrthogonalPolynomial μ k p) {r : ℝ[X]}
    (hr : r.degree < k) (hnn : ∀ᵐ x ∂μ, 0 ≤ (p * r).eval x) {s : Finset ℝ} (hs : s.card < k)
    (hz : ∀ x ∈ Set.Icc a b, (p * r).eval x = 0 → x ∈ s) : False := by
  have hint : ∫ x, (p * r).eval x ∂μ = 0 := by simpa using hp r hr
  have hzero : ∀ᵐ x ∂μ, (p * r).eval x = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_eval_of_ae_mem_Icc hμ _)).mp hint
  have hcar : ∀ᵐ x ∂μ, x ∈ s := (hμ.and hzero).mono fun x hx => hz x hx.1 hx.2
  exact Nat.lt_irrefl s.card
    (Nat.lt_of_lt_of_le hs ((isMomentPosDef_iff_forall_finset hμ k).mp h s hcar))

/-- **The zeros of the orthogonal polynomial are real**: if $\mu$, finite and supported in
$[a, b]$, is positive definite up to degree $k$, then $\pi_k$ has $k$ real zeros counted with
multiplicity. [Gautschi2004, Theorem 1.19]; [Szego1975, Theorem 3.3.1] (locators to check).
Proof: M, about 35 lines. `exists_prod_multiset_X_sub_C_mul`: $\pi_k = Rg$ with $g$ root-free and
monic (`Monic.of_mul_monic_left`, `monic_multisetProd_X_sub_C`), so $g > 0$ everywhere (Mathlib's
`Polynomial.zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg`, root hypothesis vacuous); if
$\deg R < k$, `IsMomentPosDef.false_of_ae_nonneg_mul` with $r = R$ ($\pi_k R = R^2 g \ge 0$) and
$s$ the roots of $R$; orthogonality from `isOrthogonalPolynomial_orthogonalPolynomial`.
Result: orthogonal-polynomial-zeros -/
theorem IsMomentPosDef.card_roots_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : Multiset.card (orthogonalPolynomial μ k).roots = k := by
  set π := orthogonalPolynomial μ k with hπ
  have hdeg : π.natDegree = k := natDegree_orthogonalPolynomial μ k
  have hle : Multiset.card π.roots ≤ k := hdeg ▸ card_roots' π
  refine hle.antisymm (not_lt.mp fun hlt => ?_)
  obtain ⟨g, hg, -, hg0⟩ := exists_prod_multiset_X_sub_C_mul π
  set R : ℝ[X] := (π.roots.map fun a => X - C a).prod with hR
  have hRm : R.Monic := monic_multisetProd_X_sub_C _
  have hgm : g.Monic := Monic.of_mul_monic_left hRm (hg ▸ monic_orthogonalPolynomial μ k)
  have hgpos : ∀ x, 0 < g.eval x := fun x =>
    zero_lt_eval_of_roots_lt_of_leadingCoeff_nonneg
      (fun y hy => by
        have := (mem_roots hgm.ne_zero).mpr hy
        simp [hg0] at this)
      (by rw [hgm.leadingCoeff]; exact zero_le_one)
  have hRdeg : R.degree < k := by
    rw [hR, degree_eq_natDegree hRm.ne_zero, natDegree_multiset_prod_X_sub_C_eq_card]
    exact_mod_cast hlt
  refine h.false_of_ae_nonneg_mul hμ (isOrthogonalPolynomial_orthogonalPolynomial hμ k) hRdeg
    (Filter.Eventually.of_forall fun x => ?_) (s := R.roots.toFinset) ?_ ?_
  · rw [← hπ, ← hg]
    have : (R * g * R).eval x = (R.eval x) ^ 2 * g.eval x := by simp only [eval_mul]; ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) (hgpos x).le
  · refine (Multiset.toFinset_card_le _).trans_lt ?_
    refine (card_roots' R).trans_lt ?_
    rw [hR, natDegree_multiset_prod_X_sub_C_eq_card]
    exact hlt
  · intro x _ hx
    rw [← hπ, ← hg] at hx
    have : (R * g * R).eval x = (R.eval x) ^ 2 * g.eval x := by simp only [eval_mul]; ring
    rw [this] at hx
    rcases mul_eq_zero.mp hx with h0 | h0
    · simpa [Multiset.mem_toFinset, mem_roots hRm.ne_zero] using pow_eq_zero_iff (two_ne_zero) |>.mp h0
    · exact absurd h0 (hgpos x).ne'

/-- The zeros of the orthogonal polynomial are simple: if $\mu$, finite and supported in
$[a, b]$, is positive definite up to degree $k$, then the real zeros of $\pi_k$ are distinct.
[Gautschi2004, Theorem 1.19]; [Szego1975, Theorem 3.3.1] (locators to check).
Proof: M, about 30 lines. `Multiset.nodup_iff_count_le_one`, `count_roots`; a zero $x$ of
multiplicity at least $2$ (`le_rootMultiplicity_iff`) gives $\pi_k = (X - x)^2h$;
`IsMomentPosDef.false_of_ae_nonneg_mul` with $r = h$ ($\pi_k h = ((X - x)h)^2 \ge 0$) and $s$ the
roots of $(X - x)h$, of card at most $k - 1$. -/
theorem IsMomentPosDef.nodup_roots_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (orthogonalPolynomial μ k).roots.Nodup := by
  sorry

/-- The orthogonal polynomial is the nodal polynomial of the Gauss nodes: if $\mu$, finite and
supported in $[a, b]$, is positive definite up to degree $k$, then
$\pi_k(z) = \prod_{x\in G}(z - x)$, $G$ the Gauss nodes of order $k$.
Proof: S, about 15 lines. `prod_multiset_X_sub_C_of_monic_of_roots_card_eq` with
`IsMomentPosDef.card_roots_orthogonalPolynomial`; `Lagrange.nodal_eq`; `Multiset.toFinset_val`,
`Multiset.Nodup.dedup` with `IsMomentPosDef.nodup_roots_orthogonalPolynomial`. -/
theorem IsMomentPosDef.nodal_gaussNodes {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    Lagrange.nodal (gaussNodes μ k) id = orthogonalPolynomial μ k := by
  have hnd := h.nodup_roots_orthogonalPolynomial hμ
  rw [Lagrange.nodal_eq]
  have : (gaussNodes μ k).val = (orthogonalPolynomial μ k).roots := by
    simp only [gaussNodes, Multiset.toFinset_val, hnd.dedup]
  simp only [Function.comp_def, id, Finset.prod_eq_multiset_prod, this]
  exact Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq
    (monic_orthogonalPolynomial μ k) (by rw [h.card_roots_orthogonalPolynomial hμ,
      natDegree_orthogonalPolynomial])

/-- There are exactly $k$ Gauss nodes: if $\mu$, finite and supported in $[a, b]$, is positive
definite up to degree $k$, then $\pi_k$ has $k$ distinct real zeros.
Proof: S, about 5 lines. `Multiset.toFinset_card_of_nodup` with
`IsMomentPosDef.nodup_roots_orthogonalPolynomial` and
`IsMomentPosDef.card_roots_orthogonalPolynomial`. -/
theorem IsMomentPosDef.card_gaussNodes {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (gaussNodes μ k).card = k := by
  sorry

/-- The Gauss nodes lie in every interval carrying the measure: if $\mu$, finite and supported in
$[a, b]$, is positive definite up to degree $k$, then every real zero of $\pi_k$ lies in
$[a, b]$, hence in the convex hull of the support of $\mu$.
Proof: M, about 35 lines. A root $x < a$ gives $\pi_k = (X - x)h$
(`mul_divByMonic_eq_iff_isRoot`); `IsMomentPosDef.false_of_ae_nonneg_mul` with $r = h$
($\pi_k h = (X - x)h^2 \ge 0$ on $[a, b]$, a.e. by `hμ`) and $s$ the roots of $h$; a root $x > b$
with $r = -h$. -/
theorem IsMomentPosDef.gaussNodes_subset_Icc {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) : (gaussNodes μ k : Set ℝ) ⊆ Set.Icc a b := by
  sorry

/-- The degenerate case: if $\mu$, finite and supported in $[a, b]$, is not positive definite up
to degree $k$, then $\mu$ is carried by the Gauss nodes of order $k$, the zeros of $\pi_k$.
Proof: M, about 35 lines. $k = j + 1$ (definiteness at $0$ is vacuous); `isMomentPosDef_succ_iff`
gives $\|\pi_j\|^2 = 0$, `integral_orthogonalPolynomial_succ_sq` gives $\|\pi_k\|^2 = 0$,
`ae_eval_eq_zero_of_integral_sq_eq_zero` a.e. vanishing; a zero of the monic (nonzero) $\pi_k$ is
in `roots.toFinset` (`Multiset.mem_toFinset`, `mem_roots`). -/
theorem ae_mem_gaussNodes_of_not_isMomentPosDef (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ¬ IsMomentPosDef μ k) : ∀ᵐ x ∂μ, x ∈ gaussNodes μ k := by
  sorry

/-- The Gauss hypothesis holds for every order: for a finite measure $\mu$ supported in $[a, b]$
and every $k$, the nodal polynomial of the Gauss nodes $G$ of order $k$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert G\rvert$; this is the hypothesis
of every Gauss theorem on `interpolatoryQuadrature`.
Proof: M, about 30 lines. `by_cases` on `IsMomentPosDef μ k`; definite:
`IsMomentPosDef.nodal_gaussNodes`, `IsMomentPosDef.card_gaussNodes`,
`isOrthogonalPolynomial_orthogonalPolynomial`; else the nodal polynomial vanishes on the nodes
(`Lagrange.eval_nodal_at_node`), which carry $\mu$ (`ae_mem_gaussNodes_of_not_isMomentPosDef`),
so `integral_eq_zero_of_ae`. -/
theorem isOrthogonalPolynomial_nodal_gaussNodes (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsOrthogonalPolynomial μ (gaussNodes μ k).card (Lagrange.nodal (gaussNodes μ k) id) := by
  sorry

end Definite

end NLAlib
