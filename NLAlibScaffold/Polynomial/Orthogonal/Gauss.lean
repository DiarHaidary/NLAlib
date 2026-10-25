/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# The Gauss rule and the minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Orthogonal/Gauss.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.4): the error of the $(k + 1)$-point Gauss
rule restated with the minimax error in degree $2k + 1$.

## Main results

* `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_continuousOn`: the bound
  $2E_{2k + 1}(f)\mu(\mathbb{R})$.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- **The Gauss-rule error and the minimax error**: for a finite measure $\mu$ supported in
$[a, b]$ and $f$ continuous on $[a, b]$, the $(k + 1)$-point Gauss rule satisfies
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k + 1)\Bigr\rvert \le
2E_{2k + 1}(f; [a, b])\,\mu(\mathbb{R})\,,$$
$E_{2k + 1}$ the error of the best uniform approximation of $f$ on $[a, b]$ by polynomials of
degree at most $2k + 1$ (`minimaxError`). [GolubMeurant2010, Ch. 6]; [Trefethen2019, Ch. 19]
(locator to check).
Proof: S, about 10 lines. Integrability of $f$ from `ContinuousOn.integrableOn_Icc` and
`Measure.restrict_eq_self_of_ae_mem` (as in
`abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith`);
`exists_degree_le_isUniformApproxOn_minimaxError` in degree $2k + 1 < 2(k + 1)$; then
`abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn`. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_continuousOn
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) (k : ℕ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      2 * minimaxError f (Set.Icc a b) (2 * k + 1) * μ.real Set.univ := by
  have hint : Integrable f μ := by
    have h := hf.integrableOn_Icc (μ := μ)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  -- the zero polynomial is a uniform approximation with error `C`, so the set is nonempty
  have hne : {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ ((2 * k + 1 : ℕ) : WithBot ℕ) ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε}.Nonempty :=
    ⟨C, 0, by simp, fun x hx => by simpa [Real.dist_eq] using hC x hx⟩
  have key : ∀ δ > 0, |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      2 * (minimaxError f (Set.Icc a b) (2 * k + 1) + δ) * μ.real Set.univ := by
    intro δ hδ
    have hlt0 : minimaxError f (Set.Icc a b) (2 * k + 1) < _ := lt_add_of_pos_right _ hδ
    obtain ⟨ε, ⟨p, hp, hε⟩, hlt⟩ := exists_lt_of_csInf_lt hne hlt0
    have hp' : p.degree < 2 * ((k + 1 : ℕ) : WithBot ℕ) :=
      hp.trans_lt (by exact_mod_cast (by omega : 2 * k + 1 < 2 * (k + 1)))
    have h := abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn hμ hint hp' hε
    have hm : 0 ≤ μ.real Set.univ := measureReal_nonneg
    nlinarith [mul_le_mul_of_nonneg_right hlt.le hm]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hm : 0 ≤ μ.real Set.univ := measureReal_nonneg
  refine (key (ε / (2 * (μ.real Set.univ + 1))) (by positivity)).trans ?_
  have h2 : 2 * (ε / (2 * (μ.real Set.univ + 1))) * μ.real Set.univ ≤ ε := by
    have h3 : 2 * (ε / (2 * (μ.real Set.univ + 1))) * μ.real Set.univ =
        ε * (μ.real Set.univ / (μ.real Set.univ + 1)) := by
      have h0 : μ.real Set.univ + 1 ≠ 0 := by positivity
      field_simp
    have h4 : μ.real Set.univ / (μ.real Set.univ + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    rw [h3]
    nlinarith
  linarith

end NLAlib
