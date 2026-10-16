/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Order.Interval.Set.Infinite
public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Chebyshev modulus comparison and monic minimax

External modulus comparison and monic minimality, derived from Mathlib's extremal inequalities.
These declarations are upstream candidates; all approximation bounds use the shared metric API.

## Main results

* `Polynomial.Chebyshev.abs_eval_le_abs_eval_T_real_of_isUniformApproxOn`:
  external comparison with a polynomial bounded by one.
* `Polynomial.Chebyshev.abs_eval_le_mul_abs_eval_T_real_of_isUniformApproxOn`:
  comparison with an arbitrary uniform bound.
* `Polynomial.Chebyshev.inv_two_pow_le_of_monic_of_isUniformApproxOn`: monic lower bound.
* `Polynomial.Chebyshev.isLeast_chebyshev_monic_minimax`: exact monic minimax value.
-/

@[expose] public section

namespace Polynomial.Chebyshev

private lemma abs_eval_le_eval_T_of_one_le {q : ℕ} {p : ℝ[X]} {x : ℝ}
    (hp : p.degree ≤ (q : WithBot ℕ))
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) 1)
    (hx : 1 ≤ x) : |p.eval x| ≤ (T ℝ (q : ℤ)).eval x := by
  have hb' : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |p.eval y| ≤ 1 := by
    intro y hy
    simpa only [Real.dist_eq, sub_zero] using hb.apply hy
  have h₁ := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) hx hp hb'
  have h₂ := eval_iterate_derivative_le_of_forall_abs_le_one (k := 0) (P := -p) hx
    (by rwa [degree_neg]) (fun y hy => by simpa only [eval_neg, abs_neg] using hb' y hy)
  simp only [Function.iterate_zero, id_eq, eval_neg] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, h₁⟩

/-- If $\deg p\le q$ and $|p|\le1$ on $[-1,1]$, then
$|p(x)|\le|T_q(x)|$ for $|x|\ge1$. This is an external-comparison corollary of
[Saad2003, Theorem 6.25]; the proof uses Mathlib's extremal derivative inequality at order zero.

Result: chebyshev-extremal
-/
theorem abs_eval_le_abs_eval_T_real_of_isUniformApproxOn
    {q : ℕ} {p : ℝ[X]} {x : ℝ}
    (hp : p.degree ≤ (q : WithBot ℕ))
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) 1)
    (hx : 1 ≤ |x|) : |p.eval x| ≤ |(T ℝ (q : ℤ)).eval x| := by
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    exact (abs_eval_le_eval_T_of_one_le hp hb hx).trans (le_abs_self _)
  · rw [abs_of_neg h0] at hx
    have hQ : (p.comp (-X)).degree ≤ (q : WithBot ℕ) := by
      refine degree_le_natDegree.trans ?_
      have hn : (p.comp (-X)).natDegree ≤ q := by
        refine natDegree_comp_le.trans ?_
        rw [natDegree_neg, natDegree_X, mul_one]
        exact natDegree_le_iff_degree_le.mpr hp
      exact_mod_cast hn
    have hQb : Metric.IsUniformApproxOn (p.comp (-X)).eval (fun _ => 0)
        (Set.Icc (-1 : ℝ) 1) 1 := by
      intro y hy
      simpa only [Real.dist_eq, sub_zero, eval_comp, eval_neg, eval_X] using
        hb.apply (show -y ∈ Set.Icc (-1 : ℝ) 1 from ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    have h := abs_eval_le_eval_T_of_one_le hQ hQb hx
    simp only [eval_comp, eval_neg, eval_X, neg_neg] at h
    refine h.trans ((le_abs_self _).trans (le_of_eq ?_))
    rw [← neg_neg x, T_eval_neg, neg_neg, abs_mul, abs_unit_intCast, one_mul]

private lemma eq_zero_of_nonpos_error {p : ℝ[X]} {M : ℝ} (hM : M ≤ 0)
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M) : p = 0 := by
  apply Polynomial.eq_zero_of_infinite_isRoot
  refine Set.Infinite.mono (fun x hx => ?_) (Set.Icc_infinite (by norm_num : (-1 : ℝ) < 1))
  have h : |p.eval x| ≤ M := by simpa only [Real.dist_eq, sub_zero] using hb.apply hx
  exact abs_eq_zero.mp (le_antisymm (h.trans hM) (abs_nonneg _))

/-- If $\deg p\le q$ and $|p|\le M$ on $[-1,1]$, then
$|p(x)|\le M|T_q(x)|$ for $|x|\ge1$, including $M=0$.
A scaled corollary of [Saad2003, Theorem 6.25], proved via Mathlib's extremal inequality. -/
theorem abs_eval_le_mul_abs_eval_T_real_of_isUniformApproxOn
    {q : ℕ} {p : ℝ[X]} {M x : ℝ}
    (hp : p.degree ≤ (q : WithBot ℕ))
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M)
    (hx : 1 ≤ |x|) : |p.eval x| ≤ M * |(T ℝ (q : ℤ)).eval x| := by
  rcases le_or_gt M 0 with hM | hM
  · have hM0 := hb.nonneg ⟨0, by norm_num⟩
    rw [eq_zero_of_nonpos_error hM hb, eval_zero, abs_zero]
    exact mul_nonneg hM0 (abs_nonneg _)
  · have hQ : (Polynomial.C M⁻¹ * p).degree ≤ (q : WithBot ℕ) :=
      ((congrArg degree (C_mul' _ _)).trans_le (degree_smul_le _ _)).trans hp
    have hQb : Metric.IsUniformApproxOn (Polynomial.C M⁻¹ * p).eval (fun _ => 0)
        (Set.Icc (-1 : ℝ) 1) 1 := by
      intro y hy
      change |(Polynomial.C M⁻¹ * p).eval y - 0| ≤ 1
      rw [sub_zero, eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hM),
        inv_mul_le_iff₀ hM, mul_one]
      simpa only [Real.dist_eq, sub_zero] using hb.apply hy
    have h := abs_eval_le_abs_eval_T_real_of_isUniformApproxOn hQ hQb hx
    rwa [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hM), inv_mul_le_iff₀ hM] at h

/-- A monic real polynomial of degree $q$ uniformly bounded by $M$ on $[-1,1]$ satisfies
$$\frac1{2^{q-1}}\le M.$$
[GolubMeurant2010, §2.5.1, Theorem 2.15] for $q\ge1$, extended here to $q=0$ with value one
using natural subtraction. The proof uses Mathlib's extremal leading-coefficient bound. -/
theorem inv_two_pow_le_of_monic_of_isUniformApproxOn
    {q : ℕ} {p : ℝ[X]} {M : ℝ} (hp : p.Monic) (hdeg : p.natDegree = q)
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M) :
    ((2 : ℝ) ^ (q - 1))⁻¹ ≤ M := by
  have hM : 0 < M := by
    by_contra hM
    exact hp.ne_zero (eq_zero_of_nonpos_error (not_lt.mp hM) hb)
  have hQ : (Polynomial.C M⁻¹ * p).degree ≤ (q : WithBot ℕ) := by
    refine ((congrArg degree (C_mul' _ _)).trans_le (degree_smul_le _ _)).trans ?_
    rw [← hdeg]
    exact degree_le_natDegree
  have hQb : ∀ y ∈ Set.Icc (-1 : ℝ) 1, |(Polynomial.C M⁻¹ * p).eval y| ≤ 1 := by
    intro y hy
    rw [eval_mul, eval_C, abs_mul, abs_of_pos (inv_pos.mpr hM), inv_mul_le_iff₀ hM, mul_one]
    simpa only [Real.dist_eq, sub_zero] using hb.apply hy
  have h := leadingCoeff_le_of_forall_abs_le_one hQ hQb
  rw [leadingCoeff_mul, leadingCoeff_C, hp.leadingCoeff, mul_one] at h
  exact inv_le_of_inv_le₀ hM h

/-- Among monic real polynomials of degree $q$, the least uniform bound on $[-1,1]$ is
$1/2^{q-1}$, attained by $T_q/2^{q-1}$.
[GolubMeurant2010, §2.5.1, Theorem 2.15] for $q\ge1$. The $q=0$ extension has witness one
and value one; the exponent uses natural subtraction.

Result: chebyshev-monic-minimal
-/
theorem isLeast_chebyshev_monic_minimax (q : ℕ) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.Monic ∧ p.natDegree = q ∧
      Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc (-1 : ℝ) 1) M}
      (((2 : ℝ) ^ (q - 1))⁻¹) := by
  refine ⟨⟨Polynomial.C (((2 : ℝ) ^ (q - 1))⁻¹) * T ℝ (q : ℤ), ?_, ?_, ?_⟩, ?_⟩
  · rw [Monic, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_T, Int.natAbs_natCast]
    exact inv_mul_cancel₀ (by positivity)
  · rw [natDegree_C_mul (by positivity), natDegree_T, Int.natAbs_natCast]
  · intro x hx
    change |(Polynomial.C (((2 : ℝ) ^ (q - 1))⁻¹) * T ℝ (q : ℤ)).eval x - 0| ≤ _
    rw [sub_zero, eval_mul, eval_C, abs_mul, abs_of_pos (by positivity)]
    exact mul_le_of_le_one_right (by positivity) (abs_eval_T_real_le_one _ (abs_le.mpr hx))
  · rintro M ⟨p, hp, hdeg, hb⟩
    exact inv_two_pow_le_of_monic_of_isUniformApproxOn hp hdeg hb

end Polynomial.Chebyshev
