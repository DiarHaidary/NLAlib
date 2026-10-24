/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Moments

/-!
# Moment matching: the additions of stage KS7

Statements for `NLAlib/Polynomial/Orthogonal/Moments.lean` whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.1 and "Interface for SLQ" item 5). A
polynomial of $L^2(\mu)$ norm zero vanishes almost everywhere and is orthogonal to everything;
two finite measures carried by a finite set $s$ that match $\lvert s\rvert$ moments are equal;
moment matching is preserved by scaling and by finite sums of measures supported in one
interval.

## Main results

* `NLAlib.ae_eval_eq_zero_of_integral_sq_eq_zero`: a polynomial of norm zero vanishes a.e.
* `NLAlib.integral_eval_mul_eq_zero_of_integral_sq_eq_zero`: and is orthogonal to everything.
* `NLAlib.MatchesMoments.eq_of_ae_mem`: moment determinacy on a finite set.
* `NLAlib.MatchesMoments.smul`, `NLAlib.MatchesMoments.finsetSum`: linearity in the pair.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped ENNReal

namespace NLAlib

variable {μ ν : Measure ℝ}

/-- A polynomial of norm zero vanishes almost everywhere: for a finite measure $\mu$ supported
in $[a, b]$ and a real polynomial $p$ with $\int p^2\,d\mu = 0$, $p = 0$ $\mu$-almost
everywhere.
Proof: S, about 10 lines. `integral_eq_zero_iff_of_nonneg_ae` (the integrand is nonnegative,
`sq_nonneg`, and integrable, `integrable_eval_of_ae_mem_Icc` applied to `p ^ 2` with `eval_pow`),
then `sq_eq_zero_iff` pointwise. -/
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
$\int p\,r\,d\mu = 0$. The degenerate branch of every recurrence proof.
Proof: S, about 10 lines. `ae_eval_eq_zero_of_integral_sq_eq_zero`, then `integral_eq_zero_of_ae`
with the `Filter.EventuallyEq` from `mul_eq_zero` (`zero_mul`). -/
theorem integral_eval_mul_eq_zero_of_integral_sq_eq_zero [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : ∫ x, p.eval x ^ 2 ∂μ = 0) (r : ℝ[X]) :
    ∫ x, p.eval x * r.eval x ∂μ = 0 := by
  have hae : ∀ᵐ x ∂μ, p.eval x = 0 :=
    ae_eval_eq_zero_of_integral_sq_eq_zero hμ hp
  exact integral_eq_zero_of_ae (hae.mono fun x hx => by simp [hx])

/-- **Moment determinacy on a finite set**: two finite measures $\mu$, $\nu$ carried by a finite
set $s \subseteq \mathbb{R}$ that match their first $\lvert s\rvert$ moments are equal. No printed
source.
Proof: M, about 40 lines. `Measure.ae_mem_finset_iff` writes both as $\sum_{x\in s}
\mu\{x\}\,\delta_x$; for $x \in s$, $\mu\{x\} = \int\ell_x\,d\mu$ via `setIntegral_finset`,
`Measure.restrict_eq_self_of_ae_mem`, `Lagrange.eval_basis_self`, `Lagrange.eval_basis_of_ne`;
`Lagrange.degree_basis` gives $\deg\ell_x < \lvert s\rvert$, so `h` equates the weights;
`ofReal_measureReal`. -/
theorem MatchesMoments.eq_of_ae_mem [IsFiniteMeasure μ] [IsFiniteMeasure ν] {s : Finset ℝ}
    (h : MatchesMoments μ ν s.card) (hμ : ∀ᵐ x ∂μ, x ∈ s) (hν : ∀ᵐ x ∂ν, x ∈ s) : μ = ν := by
  -- integrating a polynomial against a measure carried by `s` is a weighted sum over `s`
  have hint : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ s) → ∀ p : ℝ[X],
      ∫ x, p.eval x ∂ρ = ∑ y ∈ s, ρ.real {y} • p.eval y := fun ρ _ hρ p => by
    rw [← setIntegral_finset s
      (p.continuous.continuousOn.integrableOn_compact s.finite_toSet.isCompact),
      Measure.restrict_eq_self_of_ae_mem hρ]
  -- the Lagrange-type polynomial vanishing on `s \ {x}` picks out the weight at `x`
  have hw : ∀ x ∈ s, μ.real {x} = ν.real {x} := fun x hx => by
    set p : ℝ[X] := ∏ y ∈ s.erase x, (X - C y)
    have hsum : ∀ (ρ : Measure ℝ) [IsFiniteMeasure ρ], (∀ᵐ x ∂ρ, x ∈ s) →
        ∫ x, p.eval x ∂ρ = ρ.real {x} * p.eval x := fun ρ _ hρ => by
      rw [hint ρ hρ, ← Finset.add_sum_erase s _ hx, smul_eq_mul, add_eq_left]
      refine Finset.sum_eq_zero fun y hy => ?_
      simp only [p, eval_prod, eval_sub, eval_X, eval_C]
      rw [Finset.prod_eq_zero hy (sub_self y), smul_zero]
    have hpx : p.eval x ≠ 0 := by
      simp only [p, eval_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_ne_zero_iff.mpr fun y hy => sub_ne_zero.mpr (Finset.ne_of_mem_erase hy).symm
    have hdeg : p.degree < s.card := by
      rw [degree_eq_natDegree (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C y).ne_zero,
        natDegree_finsetProd_X_sub_C_eq_card, Finset.card_erase_of_mem hx]
      exact_mod_cast Nat.sub_lt (Finset.card_pos.mpr ⟨x, hx⟩) one_pos
    have := h p hdeg
    rw [hsum μ hμ, hsum ν hν] at this
    exact mul_right_cancel₀ hpx this
  rw [Measure.ae_mem_finset_iff.mp hμ, Measure.ae_mem_finset_iff.mp hν]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [← ofReal_measureReal, ← ofReal_measureReal, hw x hx]

/-- Moment matching is preserved by scaling: if $\mu$ and $\nu$ match their first $N$ moments,
then so do $c\mu$ and $c\nu$ for every $c \in [0, \infty]$.
Proof: S, about 5 lines. `integral_smul_measure` on both sides, then `congrArg` with `h`. -/
theorem MatchesMoments.smul {N : ℕ} (h : MatchesMoments μ ν N) (c : ℝ≥0∞) :
    MatchesMoments (c • μ) (c • ν) N := by
  intro p hp
  rw [integral_smul_measure, integral_smul_measure]
  exact congrArg _ (h p hp)

/-- Moment matching is preserved by finite sums: if finite measures $\mu_i$ and $\nu_i$, all
supported in $[a, b]$, match their first $N$ moments for each $i \in s$, then
$\sum_{i\in s}\mu_i$ and $\sum_{i\in s}\nu_i$ match their first $N$ moments. The average of
per-probe Gauss rules matches $2q$ moments of the average of the probe spectral measures.
Proof: S, about 20 lines. `integral_finsetSum_measure` on both sides, each summand integrable by
`integrable_eval_of_ae_mem_Icc`; `Finset.sum_congr` with `h`. -/
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
