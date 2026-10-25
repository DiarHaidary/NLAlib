/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Zeros

/-!
# The Gauss nodes are interior: the theorems of stage KS8

Statements for `NLAlib/Polynomial/Orthogonal/Zeros.lean` whose proofs are deferred
(`docs/design/Polynomial-QuadratureRemainder.md`, Z1). If a finite measure supported in $[a, b]$
has more than $k$ support points, the zeros of its orthogonal polynomial $\pi_k$ lie in the open
interval $(a, b)$; with exactly $k$ support points they are the support points and may sit at
$a$ or $b$.

## Main results

* `NLAlib.IsMomentPosDef.gaussNodes_subset_Ioo`: interior Gauss nodes.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- Shared step for `IsMomentPosDef.gaussNodes_subset_Ioo`: if $\pi_k(x) = 0$ and
$(t - x)c \ge 0$ on $[a, b]$, then $\mu$ (supported in $[a, b]$) is not positive definite up to
degree $k + 1$. With $\pi_k = (X - x)g$, $\pi_k \cdot (c g) = (t-x)c\,g^2 \ge 0$ on $[a, b]$ and
$\int \pi_k\,cg\,d\mu = 0$, so $\pi_k^2 = 0$ a.e. -/
private theorem IsMomentPosDef.false_of_isRoot_endpoint {μ : Measure ℝ} [IsFiniteMeasure μ]
    {a b : ℝ} {k : ℕ} (h : IsMomentPosDef μ (k + 1)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {x c : ℝ} (hx : (orthogonalPolynomial μ k).IsRoot x) (hc : c ≠ 0)
    (hsgn : ∀ t ∈ Set.Icc a b, 0 ≤ (t - x) * c) : False := by
  set g := orthogonalPolynomial μ k /ₘ (X - C x)
  have hπ : orthogonalPolynomial μ k = (X - C x) * g := (mul_divByMonic_eq_iff_isRoot.mpr hx).symm
  have hg : g ≠ 0 := fun hg0 =>
    (monic_orthogonalPolynomial μ k).ne_zero (by rw [hπ, hg0, mul_zero])
  have hgk : g.natDegree < k := by
    have hdeg := natDegree_mul (X_sub_C_ne_zero x) hg
    rw [← hπ, natDegree_orthogonalPolynomial, natDegree_X_sub_C] at hdeg
    omega
  have hint : ∫ t, (orthogonalPolynomial μ k * (C c * g)).eval t ∂μ = 0 := by
    simpa only [eval_mul] using
      isOrthogonalPolynomial_orthogonalPolynomial hμ k (C c * g)
        ((degree_C_mul hc).trans_lt (degree_le_natDegree.trans_lt (by exact_mod_cast hgk)))
  have hnn : ∀ᵐ t ∂μ, 0 ≤ (orthogonalPolynomial μ k * (C c * g)).eval t := by
    filter_upwards [hμ] with t ht
    rw [hπ]
    simp only [eval_mul, eval_sub, eval_X, eval_C]
    nlinarith [mul_nonneg (hsgn t ht) (sq_nonneg (g.eval t))]
  have hzero : ∀ᵐ t ∂μ, (orthogonalPolynomial μ k * (C c * g)).eval t = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnn (integrable_eval_of_ae_mem_Icc hμ _)).mp hint
  have hsq : ∀ᵐ t ∂μ, (orthogonalPolynomial μ k).eval t ^ 2 = 0 := by
    filter_upwards [hzero] with t ht
    rw [hπ] at ht ⊢
    simp only [eval_mul, eval_sub, eval_X, eval_C] at ht ⊢
    have h1 : (t - x) * g.eval t ^ 2 = 0 := by
      have : c * ((t - x) * g.eval t ^ 2) = 0 := by linear_combination ht
      exact (mul_eq_zero.mp this).resolve_left hc
    linear_combination (t - x) * h1
  have hdeg : (orthogonalPolynomial μ k).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_eq_natDegree (monic_orthogonalPolynomial μ k).ne_zero,
      natDegree_orthogonalPolynomial]
    exact_mod_cast Nat.lt_succ_self k
  have hpos := h (orthogonalPolynomial μ k) (monic_orthogonalPolynomial μ k).ne_zero hdeg
  exact hpos.ne' (integral_eq_zero_of_ae (hsq.mono fun t ht => ht))

/-- **The Gauss nodes are interior**: if a finite measure $\mu$ supported in $[a, b]$ is positive
definite up to degree $k + 1$ (it has more than $k$ support points), then every zero of the
orthogonal polynomial $\pi_k$ lies in $(a, b)$. Definiteness up to degree $k$ is not enough:
$\mu = \delta_a + \delta_b$ has $\pi_2 = (x - a)(x - b)$. [Gautschi2004, Theorem 1.19];
[Szego1975, Theorem 3.3.1] (locators to check); there in the interior of the support interval.
Proof: M, about 40 lines. By `IsMomentPosDef.gaussNodes_subset_Icc` (from `h.mono`) the zeros lie
in $[a, b]$; suppose $\pi_k(a) = 0$ (the case $b$ is symmetric), so $\pi_k = (x - a)r$ with
$\deg r = k - 1$ (`mul_divByMonic_eq_iff_isRoot`). Orthogonality
(`isOrthogonalPolynomial_orthogonalPolynomial`) gives
$0 = \int\pi_k r\,d\mu = \int(x - a)r^2\,d\mu$ with a nonnegative integrand on $[a, b]$, so
$(x - a)r^2 = 0$ a.e. (`integral_eq_zero_iff_of_nonneg_ae`), hence
$\int((x - a)r)^2\,d\mu = \int(x - a)\cdot(x - a)r^2\,d\mu = 0$, contradicting definiteness at
the nonzero $\pi_k = (x - a)r$ of degree $k < k + 1$. -/
theorem IsMomentPosDef.gaussNodes_subset_Ioo {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}
    {k : ℕ} (h : IsMomentPosDef μ (k + 1)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    (gaussNodes μ k : Set ℝ) ⊆ Set.Ioo a b := by
  intro y hy
  have hroot : (orthogonalPolynomial μ k).IsRoot y := by
    rwa [Finset.mem_coe, gaussNodes, Multiset.mem_toFinset,
      mem_roots (monic_orthogonalPolynomial μ k).ne_zero] at hy
  have hIcc : y ∈ Set.Icc a b :=
    (h.mono (by omega)).gaussNodes_subset_Icc hμ hy
  exact ⟨lt_of_le_of_ne hIcc.1 fun e => h.false_of_isRoot_endpoint hμ hroot one_ne_zero
      fun t ht => by linarith [ht.1, e],
    lt_of_le_of_ne hIcc.2 fun e => h.false_of_isRoot_endpoint hμ hroot
      (neg_ne_zero.mpr one_ne_zero) fun t ht => by linarith [ht.2, e]⟩

end NLAlib
