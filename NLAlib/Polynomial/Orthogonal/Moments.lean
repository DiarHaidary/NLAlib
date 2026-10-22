/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Dirac
public import Mathlib.RingTheory.Polynomial.Basic
public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation

/-!
# Moment matching

Two measures on $\mathbb{R}$ match their first $N$ moments when they give every real
polynomial of degree less than $N$ the same integral. The degree bound is strict, as in Mathlib's
`Polynomial.degreeLT` and Chebyshev–Gauss quadrature: an $n$-node Gauss rule matches $2n$
moments, and $q$ Lanczos steps match $2q$. At $N = 0$ the statement is vacuous.

Moment matching transfers uniform polynomial approximation: if $\mu$ and $\nu$ are finite,
supported in $[a, b]$, match $N$ moments, and $f$ is within $\varepsilon$ of a polynomial of
degree less than $N$ on $[a, b]$, then
$\lvert\int f\,d\mu - \int f\,d\nu\rvert \le (\mu(\mathbb{R}) + \nu(\mathbb{R}))\varepsilon$.
This is the bridge from polynomial approximation to quadrature errors and to
spectral-distribution bounds.

The support hypothesis is `[IsFiniteMeasure μ]` with `∀ᵐ x ∂μ, x ∈ Set.Icc a b`; it admits
discrete measures (spectral measures, quadrature rules).

## Main definitions

* `NLAlib.MatchesMoments`: the first $N$ moments agree.

## Main results

* `NLAlib.matchesMoments_iff_forall_mem_degreeLT`: the bridge to `Polynomial.degreeLT`.
* `NLAlib.matchesMoments_iff_forall_integral_pow`: the monomial form.
* `NLAlib.MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn`: the transfer of
  uniform approximation.
* `NLAlib.matchesMoments_measureT`: Mathlib's Chebyshev–Gauss quadrature in this vocabulary.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped ENNReal

namespace NLAlib

variable {μ ν : Measure ℝ} {N : ℕ}

/-- $\mu$ and $\nu$ **match the first $N$ moments**: $\int p\,d\mu = \int p\,d\nu$ for every
real polynomial of degree less than $N$. Total; its equivalence with monomial moments needs
integrability (`matchesMoments_iff_forall_integral_pow`). -/
def MatchesMoments (μ ν : Measure ℝ) (N : ℕ) : Prop :=
  ∀ p : ℝ[X], p.degree < N → ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν

/-- The raw-condition constructor of `MatchesMoments`, by definition. -/
theorem matchesMoments_iff : MatchesMoments μ ν N ↔
    ∀ p : ℝ[X], p.degree < N → ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := Iff.rfl

/-- Every measure matches all its own moments. -/
theorem MatchesMoments.refl (μ : Measure ℝ) (N : ℕ) : MatchesMoments μ μ N :=
  fun _ _ => rfl

/-- Moment matching is symmetric. -/
theorem MatchesMoments.symm (h : MatchesMoments μ ν N) : MatchesMoments ν μ N :=
  fun p hp => (h p hp).symm

/-- Moment matching is transitive. -/
theorem MatchesMoments.trans {ξ : Measure ℝ} (h : MatchesMoments μ ν N)
    (h' : MatchesMoments ν ξ N) : MatchesMoments μ ξ N :=
  fun p hp => (h p hp).trans (h' p hp)

/-- Matching $N$ moments gives matching $M \le N$ moments. -/
theorem MatchesMoments.mono {M : ℕ} (h : MatchesMoments μ ν N) (hMN : M ≤ N) :
    MatchesMoments μ ν M :=
  fun p hp => h p (hp.trans_le (by exact_mod_cast hMN))

/-- Every two measures match zero moments. -/
theorem matchesMoments_zero (μ ν : Measure ℝ) : MatchesMoments μ ν 0 := fun p hp => by
  rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hp
  simp only [hp, eval_zero, integral_zero]

/-- Moment matching in terms of Mathlib's `Polynomial.degreeLT`: $\mu$ and $\nu$ match $N$
moments exactly when they agree on the polynomials of degree less than $N$. -/
theorem matchesMoments_iff_forall_mem_degreeLT : MatchesMoments μ ν N ↔
    ∀ p ∈ Polynomial.degreeLT ℝ N, ∫ x, p.eval x ∂μ = ∫ x, p.eval x ∂ν := by
  simp only [MatchesMoments, Polynomial.mem_degreeLT]

/-- Moment matching is matching of the monomial moments: for finite $\mu$ and $\nu$
supported in $[a, b]$, they match $N$ moments exactly when
$\int x^k\,d\mu = \int x^k\,d\nu$ for every $k < N$; these are Mathlib's
`ProbabilityTheory.moment id k`. -/
theorem matchesMoments_iff_forall_integral_pow [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) :
    MatchesMoments μ ν N ↔ ∀ k < N, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν := by
  sorry

/-- Measures that match at least one moment have the same mass. -/
theorem MatchesMoments.measureReal_univ_eq (h : MatchesMoments μ ν N) (hN : 0 < N) :
    μ.real Set.univ = ν.real Set.univ := by
  have h1 := h (C 1) (by
    rw [degree_C one_ne_zero]
    exact_mod_cast hN)
  simpa only [eval_C, integral_const, smul_eq_mul, mul_one] using h1

/-- Moment matching transfers uniform approximation: let $\mu$ and $\nu$ be finite
measures supported in $[a, b]$ that match their first $N$ moments, $f$ integrable against both,
and $p$ a real polynomial of degree less than $N$ within $\varepsilon$ of $f$ on $[a, b]$. Then
$$\Bigl\lvert\int f\,d\mu - \int f\,d\nu\Bigr\rvert \le
(\mu(\mathbb{R}) + \nu(\mathbb{R}))\,\varepsilon\,;$$
for probability measures the bound is $2\varepsilon$. -/
theorem MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn
    (h : MatchesMoments μ ν N) [IsFiniteMeasure μ] [IsFiniteMeasure ν] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) {f : ℝ → ℝ}
    (hfμ : Integrable f μ) (hfν : Integrable f ν) {p : ℝ[X]} (hp : p.degree < N) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε) :
    |∫ x, f x ∂μ - ∫ x, f x ∂ν| ≤ (μ.real Set.univ + ν.real Set.univ) * ε := by
  sorry

/-- Chebyshev–Gauss quadrature as moment matching: for $k \ne 0$, the Chebyshev measure
$(1 - x^2)^{-1/2}\,dx$ on $[-1, 1]$ (Mathlib's `Polynomial.Chebyshev.measureT`) and the rule
$$\frac{\pi}{k}\sum_{i<k}\delta_{\cos((2i + 1)\pi/(2k))}$$
match their first $2k$ moments. Mathlib's `Polynomial.Chebyshev.integral_eq_sumZeroes`, stated
through `MatchesMoments`. -/
theorem matchesMoments_measureT {k : ℕ} (hk : k ≠ 0) :
    MatchesMoments Polynomial.Chebyshev.measureT
      (ENNReal.ofReal (Real.pi / k) • ∑ i ∈ Finset.range k,
        Measure.dirac (Real.cos ((2 * i + 1) / (2 * k) * Real.pi))) (2 * k) := by
  sorry

end NLAlib
