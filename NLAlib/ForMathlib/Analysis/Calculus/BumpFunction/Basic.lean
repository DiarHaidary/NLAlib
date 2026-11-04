/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# A smooth cutoff sequence

On a finite-dimensional real inner product space there are $C^1$ cutoffs
$\chi_n = \varphi(\cdot / (n + 1))$, for a fixed bump function $\varphi$: compactly supported,
with values in $[0, 1]$, derivatives bounded uniformly in $n$, and eventually equal to $1$ near
every point. They approximate a function of finite energy by compactly supported ones (the
log-Sobolev inequalities). Upstream candidate for
`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean`.


## Main results

* `exists_seq_contDiff_hasCompactSupport_eventuallyEq_one`.
-/

@[expose] public section

open Filter
open scoped Topology

/-- A smooth cutoff sequence: there are $C^1$, compactly supported $\chi_n : E \to [0, 1]$ whose
derivatives are bounded by one constant $K$ for every $n$, and which eventually equal $1$ on a
neighbourhood of every point; $\chi_n = \varphi(\cdot / (n + 1))$ for a bump function
$\varphi$ equal to $1$ on the unit ball. Upstream candidate. -/
theorem exists_seq_contDiff_hasCompactSupport_eventuallyEq_one {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    ∃ (χ : ℕ → E → ℝ) (K : ℝ), (∀ n, ContDiff ℝ 1 (χ n)) ∧ (∀ n, HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧ (∀ n x, ‖fderiv ℝ (χ n) x‖ ≤ K) ∧
      (∀ x, ∀ᶠ n in atTop, χ n =ᶠ[𝓝 x] fun _ => 1) := by
  let φ : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩
  have hφc : ContDiff ℝ 1 (fun x => φ x) := φ.contDiff
  obtain ⟨K, hK⟩ := (hφc.continuous_fderiv one_ne_zero).bounded_above_of_compact_support
    (φ.hasCompactSupport.fderiv (𝕜 := ℝ))
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  have ha (n : ℕ) : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
  have ha1 (n : ℕ) : ((n : ℝ) + 1)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hnorm (n : ℕ) (x : E) : ‖((n : ℝ) + 1)⁻¹ • x‖ = ((n : ℝ) + 1)⁻¹ * ‖x‖ := by
    rw [norm_smul, Real.norm_of_nonneg (ha n).le]
  refine ⟨fun n x => φ (((n : ℝ) + 1)⁻¹ • x), K,
    fun n => hφc.comp (contDiff_const_smul _), fun n => ?_, fun n x => ⟨φ.nonneg, φ.le_one⟩,
    fun n x => ?_, fun x => ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : E) (2 * ((n : ℝ) + 1)))
      fun x hx => φ.zero_of_le_dist ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    rw [dist_zero_right, hnorm, ← div_eq_inv_mul, le_div_iff₀ (by positivity)]
    exact hx.le
  · have h := ((hφc.differentiable one_ne_zero) (((n : ℝ) + 1)⁻¹ • x)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).const_smul ((n : ℝ) + 1)⁻¹)
    change ‖fderiv ℝ ((fun x => φ x) ∘ HSMul.hSMul ((n : ℝ) + 1)⁻¹) x‖ ≤ K
    rw [h.fderiv]
    calc ‖(fderiv ℝ (fun x => φ x) (((n : ℝ) + 1)⁻¹ • x)).comp
          (((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E)‖
        ≤ ‖fderiv ℝ (fun x => φ x) (((n : ℝ) + 1)⁻¹ • x)‖ *
          ‖((n : ℝ) + 1)⁻¹ • ContinuousLinearMap.id ℝ E‖ := ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ K * 1 := by
          gcongr
          · exact hK _
          · rw [norm_smul, Real.norm_of_nonneg (ha n).le]
            exact (mul_le_mul (ha1 n) (ContinuousLinearMap.norm_id_le) (norm_nonneg _)
              zero_le_one).trans_eq (one_mul 1)
      _ = K := mul_one K
  · obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
    refine eventually_atTop.2 ⟨N, fun n hn => ?_⟩
    have hx : ‖x‖ < (n : ℝ) + 1 := by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hx] with y hy
    refine φ.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_zero_right, hnorm, ← div_eq_inv_mul,
      div_le_one (by positivity)]
    exact (show ‖y‖ < (n : ℝ) + 1 from hy).le
