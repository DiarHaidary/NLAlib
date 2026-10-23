/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Moments

/-!
# Orthogonality to lower degrees

A real polynomial $p$ is orthogonal to the polynomials of degree less than $k$ in
$L^2(\mu)$ when $\int p\,r\,d\mu = 0$ for every real polynomial $r$ with $\deg r < k$. Monicity
and the degree of $p$ are separate hypotheses where a statement needs them; the predicate is the
hypothesis of Gauss quadrature (`NLAlib.Polynomial.Orthogonal.Gauss`) and the conclusion of the
Ritz-polynomial theorem of Lanczos quadrature. It depends on $\mu$ only through finitely many
moments.

## Main definitions

* `NLAlib.IsOrthogonalPolynomial`: orthogonality to every polynomial of degree less than $k$.

## Main results

* `NLAlib.IsOrthogonalPolynomial.mono`: orthogonality to fewer degrees.
* `NLAlib.MatchesMoments.isOrthogonalPolynomial_iff`: orthogonality depends only on the moments.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- $p$ is **orthogonal to every polynomial of degree less than $k$** in $L^2(\mu)$:
$\int p\,r\,d\mu = 0$ for every real polynomial $r$ with $\deg r < k$. -/
def IsOrthogonalPolynomial (μ : Measure ℝ) (k : ℕ) (p : ℝ[X]) : Prop :=
  ∀ r : ℝ[X], r.degree < k → ∫ x, p.eval x * r.eval x ∂μ = 0

/-- Orthogonality to the polynomials of degree less than $k$ gives orthogonality to those of
degree less than $j \le k$. -/
theorem IsOrthogonalPolynomial.mono {μ : Measure ℝ} {j k : ℕ} {p : ℝ[X]}
    (h : IsOrthogonalPolynomial μ k p) (hjk : j ≤ k) : IsOrthogonalPolynomial μ j p :=
  fun r hr => h r (hr.trans_le (by exact_mod_cast hjk))

/-- Orthogonality depends only on the moments: if $\mu$ and $\nu$ match their first $N$
moments and $\deg p + k \le N$, then $p$ is orthogonal to the polynomials of degree less than $k$
in $L^2(\mu)$ exactly when it is in $L^2(\nu)$. -/
theorem MatchesMoments.isOrthogonalPolynomial_iff {μ ν : Measure ℝ} {N k : ℕ} {p : ℝ[X]}
    (h : MatchesMoments μ ν N) (hN : p.natDegree + k ≤ N) :
    IsOrthogonalPolynomial μ k p ↔ IsOrthogonalPolynomial ν k p := by
  have key : ∀ r : ℝ[X], r.degree < k →
      ∫ x, p.eval x * r.eval x ∂μ = ∫ x, p.eval x * r.eval x ∂ν := by
    intro r hr
    simp_rw [← eval_mul]
    apply h
    by_cases hpr : p * r = 0
    · rw [hpr, degree_zero]
      exact WithBot.bot_lt_coe _
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact hpr (mul_zero p)
    rw [degree_eq_natDegree hpr, Nat.cast_lt]
    have h1 := (natDegree_lt_iff_degree_lt hr0).mpr hr
    have h2 := natDegree_mul_le (p := p) (q := r)
    omega
  exact forall₂_congr fun r hr => by rw [key r hr]

end NLAlib
