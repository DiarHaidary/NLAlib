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
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Topology.Algebra.Polynomial
import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.ChebyshevGauss
public import Mathlib.LinearAlgebra.Lagrange

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
* `NLAlib.ae_eval_eq_zero_of_integral_sq_eq_zero`: a polynomial of norm zero vanishes a.e.
* `NLAlib.integral_eval_mul_eq_zero_of_integral_sq_eq_zero`: and is orthogonal to everything.
* `NLAlib.MatchesMoments.eq_of_ae_mem`: moment determinacy on a finite set.
* `NLAlib.MatchesMoments.smul`, `NLAlib.MatchesMoments.finsetSum`: linearity in the pair.
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

/-- A real polynomial is integrable against a finite measure supported in $[a, b]$. -/
theorem integrable_eval_of_ae_mem_Icc [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (p : ℝ[X]) : Integrable (fun x => p.eval x) μ := by
  obtain ⟨C, hC⟩ :=
    isCompact_Icc.exists_bound_of_continuousOn (f := fun x => p.eval x) p.continuous.continuousOn
  exact Integrable.of_bound p.continuous.aestronglyMeasurable C (by
    filter_upwards [hμ] with x hx using hC x hx)

/-- Moment matching is matching of the monomial moments: for finite $\mu$ and $\nu$
supported in $[a, b]$, they match $N$ moments exactly when
$\int x^k\,d\mu = \int x^k\,d\nu$ for every $k < N$; these are Mathlib's
`ProbabilityTheory.moment id k`. -/
theorem matchesMoments_iff_forall_integral_pow [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hν : ∀ᵐ x ∂ν, x ∈ Set.Icc a b) :
    MatchesMoments μ ν N ↔ ∀ k < N, ∫ x, x ^ k ∂μ = ∫ x, x ^ k ∂ν := by
  constructor
  · intro h k hk
    have := h (X ^ k) (by rw [degree_X_pow]; exact_mod_cast hk)
    simpa only [eval_X_pow] using this
  · intro h p hp
    by_cases hp0 : p = 0
    · simp only [hp0, eval_zero, integral_zero]
    have hnat : p.natDegree < N := by
      rw [degree_eq_natDegree hp0] at hp
      exact_mod_cast hp
    have hint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ Set.Icc a b) →
        ∀ i, Integrable (fun x => p.coeff i * x ^ i) ρ := fun ρ _ hρ i => by
      simpa only [eval_X_pow] using (integrable_eval_of_ae_mem_Icc hρ (X ^ i)).const_mul (p.coeff i)
    simp_rw [eval_eq_sum_range]
    rw [integral_finsetSum _ fun i _ => hint μ hμ i, integral_finsetSum _ fun i _ => hint ν hν i]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [integral_const_mul, integral_const_mul,
      h i ((Finset.mem_range.mp hi).trans_le (Nat.succ_le_of_lt hnat))]

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
  have hpμ := integrable_eval_of_ae_mem_Icc hμ p
  have hpν := integrable_eval_of_ae_mem_Icc hν p
  have hbound : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ Set.Icc a b) →
      |∫ x, (f x - p.eval x) ∂ρ| ≤ ε * ρ.real Set.univ := fun ρ _ hρ => by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le_const ?_
    filter_upwards [hρ] with x hx
    rw [← dist_eq_norm, dist_comm]
    exact hε x hx
  have heq : ∫ x, f x ∂μ - ∫ x, f x ∂ν =
      ∫ x, (f x - p.eval x) ∂μ - ∫ x, (f x - p.eval x) ∂ν := by
    rw [integral_sub hfμ hpμ, integral_sub hfν hpν, h p hp]
    ring
  rw [heq]
  calc |∫ x, (f x - p.eval x) ∂μ - ∫ x, (f x - p.eval x) ∂ν|
      ≤ |∫ x, (f x - p.eval x) ∂μ| + |∫ x, (f x - p.eval x) ∂ν| := abs_sub _ _
    _ ≤ ε * μ.real Set.univ + ε * ν.real Set.univ := add_le_add (hbound μ hμ) (hbound ν hν)
    _ = (μ.real Set.univ + ν.real Set.univ) * ε := by ring

/-- Chebyshev–Gauss quadrature as moment matching: for $k \ne 0$, the Chebyshev measure
$(1 - x^2)^{-1/2}\,dx$ on $[-1, 1]$ (Mathlib's `Polynomial.Chebyshev.measureT`) and the rule
$$\frac{\pi}{k}\sum_{i<k}\delta_{\cos((2i + 1)\pi/(2k))}$$
match their first $2k$ moments. Mathlib's `Polynomial.Chebyshev.integral_eq_sumZeroes`, stated
through `MatchesMoments`. -/
theorem matchesMoments_measureT {k : ℕ} (hk : k ≠ 0) :
    MatchesMoments Polynomial.Chebyshev.measureT
      (ENNReal.ofReal (Real.pi / k) • ∑ i ∈ Finset.range k,
        Measure.dirac (Real.cos ((2 * i + 1) / (2 * k) * Real.pi))) (2 * k) := by
  intro p hp
  rw [Chebyshev.integral_eq_sumZeroes hk (by exact_mod_cast hp), integral_smul_measure,
    integral_finsetSum_measure fun i _ => integrable_dirac enorm_lt_top,
    ENNReal.toReal_ofReal (by positivity)]
  simp only [integral_dirac, smul_eq_mul, Chebyshev.sumZeroes_def]

/-- A polynomial of norm zero vanishes almost everywhere: for a finite measure $\mu$ supported
in $[a, b]$ and a real polynomial $p$ with $\int p^2\,d\mu = 0$, $p = 0$ $\mu$-almost
everywhere. -/
theorem ae_eval_eq_zero_of_integral_sq_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : ∫ x, p.eval x ^ 2 ∂μ = 0) :
    ∀ᵐ x ∂μ, p.eval x = 0 := by
  have hint : Integrable (fun x => p.eval x ^ 2) μ :=
    (integrable_eval_of_ae_mem_Icc hμ (p ^ 2)).congr (ae_of_all μ fun x => eval_pow 2)
  refine Filter.Eventually.mono
    ((integral_eq_zero_iff_of_nonneg_ae (ae_of_all μ fun x => sq_nonneg _) hint).mp hp) ?_
  intro x hx
  exact pow_eq_zero_iff two_ne_zero |>.mp hx

/-- A polynomial of norm zero is orthogonal to everything: for a finite measure $\mu$ supported
in $[a, b]$, a real polynomial $p$ with $\int p^2\,d\mu = 0$ and every real polynomial $r$,
$\int p\,r\,d\mu = 0$. The degenerate branch of every recurrence proof. -/
theorem integral_eval_mul_eq_zero_of_integral_sq_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : ∫ x, p.eval x ^ 2 ∂μ = 0) (r : ℝ[X]) :
    ∫ x, p.eval x * r.eval x ∂μ = 0 := by
  have hae : ∀ᵐ x ∂μ, p.eval x = 0 :=
    ae_eval_eq_zero_of_integral_sq_eq_zero hμ hp
  exact integral_eq_zero_of_ae (hae.mono fun x hx => by simp [hx])

/-- **Moment determinacy on a finite set**: two finite measures $\mu$, $\nu$ carried by a finite
set $s \subseteq \mathbb{R}$ that match their first $\lvert s\rvert$ moments are equal. No printed
source. -/
theorem MatchesMoments.eq_of_ae_mem [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Finset ℝ}
    (h : MatchesMoments μ ν s.card) (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) : μ = ν := by
  -- the Lagrange basis polynomial `ℓ_x` integrates to the weight at `x` of a measure on `s`
  have hweight : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ s) → ∀ x ∈ s,
      ∫ t, (Lagrange.basis s id x).eval t ∂ρ = ρ.real {x} := fun ρ _ hρ x hx => by
    have := setIntegral_finset s ((Lagrange.basis s id x).continuous.continuousOn
      |>.integrableOn_compact (μ := ρ) s.finite_toSet.isCompact)
    rw [Measure.restrict_eq_self_of_ae_mem hρ] at this
    rw [this, Finset.sum_eq_single_of_mem x hx,
      show (Lagrange.basis s id x).eval x = 1 from Lagrange.eval_basis_self (Set.injOn_id _) hx,
      smul_eq_mul, mul_one]
    exact fun y hy hyx => smul_eq_zero_of_right _ (Lagrange.eval_basis_of_ne (v := id) hyx.symm hy)
  rw [Measure.ae_mem_finset_iff.mp hμ, Measure.ae_mem_finset_iff.mp hν]
  refine Finset.sum_congr rfl fun x hx => ?_
  have hdeg : (Lagrange.basis s id x).degree < s.card := by
    rw [Lagrange.degree_basis (Set.injOn_id _) hx]
    exact_mod_cast Nat.sub_lt (Finset.card_pos.mpr ⟨x, hx⟩) one_pos
  rw [← ofReal_measureReal, ← ofReal_measureReal, ← hweight μ hμ x hx, ← hweight ν hν x hx,
    h _ hdeg]

/-- Moment matching is preserved by scaling: if $\mu$ and $\nu$ match their first $N$ moments,
then so do $c\mu$ and $c\nu$ for every $c \in [0, \infty]$. -/
theorem MatchesMoments.smul {N : ℕ} (h : MatchesMoments μ ν N) (c : ℝ≥0∞) :
    MatchesMoments (c • μ) (c • ν) N := by
  intro p hp
  rw [integral_smul_measure, integral_smul_measure]
  exact congrArg _ (h p hp)

/-- Moment matching is preserved by finite sums: if finite measures $\mu_i$ and $\nu_i$, all
supported in $[a, b]$, match their first $N$ moments for each $i \in s$, then
$\sum_{i\in s}\mu_i$ and $\sum_{i\in s}\nu_i$ match their first $N$ moments. The average of
per-probe Gauss rules matches $2q$ moments of the average of the probe spectral measures. -/
theorem MatchesMoments.finsetSum {ι : Type*} {s : Finset ι} {μs νs : ι → Measure ℝ}
    [∀ i, IsFiniteMeasure (μs i)] [∀ i, IsFiniteMeasure (νs i)] {N : ℕ} {a b : ℝ}
    (hμs : ∀ i ∈ s, ∀ᵐ x ∂μs i, x ∈ Set.Icc a b) (hνs : ∀ i ∈ s, ∀ᵐ x ∂νs i, x ∈ Set.Icc a b)
    (h : ∀ i ∈ s, MatchesMoments (μs i) (νs i) N) :
    MatchesMoments (∑ i ∈ s, μs i) (∑ i ∈ s, νs i) N := by
  intro p hp
  rw [integral_finsetSum_measure fun i hi => integrable_eval_of_ae_mem_Icc (hμs i hi) p,
    integral_finsetSum_measure fun i hi => integrable_eval_of_ae_mem_Icc (hνs i hi) p]
  exact Finset.sum_congr rfl fun i hi => h i hi p hp

end NLAlib
