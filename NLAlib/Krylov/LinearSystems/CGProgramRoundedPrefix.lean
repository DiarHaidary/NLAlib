/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGProgramRoundedInitialization

/-!
# Extending an extracted rounded CG prefix

The next run record appends defects already extracted from an actual canonical step.
Existing fields below the endpoint are retained. This is bookkeeping for `CGRun`, not
an alternate arithmetic or iteration model.

## Main results

* `NLAlib.CGImplementation.exists_cgRun_succ`: append one extracted step.
-/

@[expose] public section

namespace NLAlib.CGImplementation

open scoped Matrix

private theorem forall_le_succ {k : ℕ} {Q : ℕ → Prop}
    (h : ∀ j ≤ k, Q j) (hs : Q (k + 1)) : ∀ j ≤ k + 1, Q j := by
  intro j hj
  rcases Nat.eq_or_lt_of_le hj with rfl | hj
  · exact hs
  · exact h j (by omega)

private theorem forall_lt_succ {k : ℕ} {Q : ℕ → Prop}
    (h : ∀ j < k, Q j) (hs : Q k) : ∀ j < k + 1, Q j := by
  intro j hj
  rcases Nat.eq_or_lt_of_le (Nat.le_of_lt_succ hj) with rfl | hj
  · exact hs
  · exact h j hj

private theorem cache_fields {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (ν θ μ γ eγ δ eδ : ℝ)
    (hνpos : 0 < R.ν k) (hν : ν = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ))
    (hθ : |θ| ≤ R.ε) (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε) :
    (∀ j ≤ k + 1, (Function.update R.ν (k + 1) (ν)) j = ‖WithLp.toLp 2 ((Function.update R.r (k
      + 1) (next.r)) j)‖ ^ 2 * (1 + (Function.update R.θ (k + 1) (θ)) j)) ∧
    (∀ j ≤ k + 1, |(Function.update R.θ (k + 1) (θ)) j| ≤ R.ε) ∧
    (∀ j < k + 1, 0 < (Function.update R.ν (k + 1) (ν)) j) ∧
    (∀ j < k + 1, (Function.update R.γ k (γ)) j = (Function.update R.ν (k + 1) (ν)) j /
      (Function.update R.μ k (μ)) j * (1 + (Function.update R.eγ k (eγ)) j)) ∧
    (∀ j < k + 1, |(Function.update R.eγ k (eγ)) j| ≤ R.ε) ∧
    (∀ j < k + 1, (Function.update R.δ k (δ)) j = (Function.update R.ν (k + 1) (ν)) (j + 1) /
      (Function.update R.ν (k + 1) (ν)) j * (1 + (Function.update R.eδ k (eδ)) j)) ∧
    (∀ j < k + 1, |(Function.update R.eδ k (eδ)) j| ≤ R.ε) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact forall_le_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using R.ν_eq j hj) (by
      simpa only [Function.update_self, WithLp.toLp_neg, norm_neg, abs_neg] using hν)
  · exact forall_le_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using R.abs_θ_le j hj) (by
      simpa only [Function.update_self, WithLp.toLp_neg, norm_neg, abs_neg] using hθ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.ν_pos j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hνpos)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.γ_eq j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hγ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.abs_eγ_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using heγ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.δ_eq j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hδ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.abs_eδ_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using heδ)

private theorem product_fields {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ) (μ : ℝ) (hμpos : 0 < μ)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖) :
    (∀ j < k + 1, (Function.update R.s k (sv)) j = R.A *ᵥ ((Function.update R.p (k + 1)
      (next.p)) j) + (Function.update R.es k (-(R.A *ᵥ R.p k - sv))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.es k (-(R.A *ᵥ R.p k - sv))) j)‖ ≤ R.ε *
      specNorm R.A * ‖WithLp.toLp 2 ((Function.update R.p (k + 1) (next.p)) j)‖) ∧
    (∀ j < k + 1, (Function.update R.μ k (μ)) j = ((Function.update R.p (k + 1) (next.p)) j) ⬝ᵥ
      ((Function.update R.s k (sv)) j) + (Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ))) j) ∧
    (∀ j < k + 1, |(Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ))) j| ≤ R.ε * ‖WithLp.toLp 2
      ((Function.update R.p (k + 1) (next.p)) j)‖ * ‖WithLp.toLp 2 ((Function.update R.s k (sv))
      j)‖) ∧
    (∀ j < k + 1, 0 < (Function.update R.μ k (μ)) j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.s_eq j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_es_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hs)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.μ_eq j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.abs_eμ_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hμ)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.μ_pos j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hμpos)

private theorem update_fields {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ) (γ δ : ℝ)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    (∀ j < k + 1, (Function.update R.x (k + 1) (next.x)) (j + 1) = (Function.update R.x (k + 1)
      (next.x)) j + ((Function.update R.γ k (γ)) j) • ((Function.update R.p (k + 1) (next.p)) j)
      + (Function.update R.ex k (-(R.x k + γ • R.p k - next.x))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.ex k (-(R.x k + γ • R.p k - next.x))) j)‖ ≤
      R.ε * (‖WithLp.toLp 2 ((Function.update R.x (k + 1) (next.x)) j)‖ + |(Function.update R.γ
      k (γ)) j| * ‖WithLp.toLp 2 ((Function.update R.p (k + 1) (next.p)) j)‖)) ∧
    (∀ j < k + 1, (Function.update R.r (k + 1) (next.r)) (j + 1) = (Function.update R.r (k + 1)
      (next.r)) j - ((Function.update R.γ k (γ)) j) • ((Function.update R.s k (sv)) j) +
      (Function.update R.er k (-(R.r k - γ • sv - next.r))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.er k (-(R.r k - γ • sv - next.r))) j)‖ ≤
      R.ε * (‖WithLp.toLp 2 ((Function.update R.r (k + 1) (next.r)) j)‖ + |(Function.update R.γ
      k (γ)) j| * ‖WithLp.toLp 2 ((Function.update R.s k (sv)) j)‖)) ∧
    (∀ j < k + 1, (Function.update R.p (k + 1) (next.p)) (j + 1) = (Function.update R.r (k + 1)
      (next.r)) (j + 1) + ((Function.update R.δ k (δ)) j) • ((Function.update R.p (k + 1)
      (next.p)) j) + (Function.update R.ep k (-(next.r + δ • R.p k - next.p))) j) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.ep k (-(next.r + δ • R.p k - next.p))) j)‖
      ≤ R.ε * (‖WithLp.toLp 2 ((Function.update R.r (k + 1) (next.r)) (j + 1))‖ +
      |(Function.update R.δ k (δ)) j| * ‖WithLp.toLp 2 ((Function.update R.p (k + 1) (next.p))
      j)‖)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.x_succ j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_ex_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hex)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.r_succ j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_er_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using her)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.p_succ j hj) (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega), neg_sub]
      abel)
  · exact forall_lt_succ (fun j hj => by
        simpa only [Function.update_of_ne (show j ≠ k by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 1 by omega)] using R.norm_ep_le j hj) (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hep)

/-- Append one step's extracted data to the existing run. The hypotheses here are supplied
by actual primitive execution in the bridge, and are not assumptions of its input theorem. -/
private noncomputable def extendRoundedRun {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ν θ μ γ eγ δ eδ : ℝ) (hνpos : 0 < R.ν k) (hμpos : 0 < μ)
    (hν : ν = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ)) (hθ : |θ| ≤ R.ε)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    CGRun N (k + 1) := by
  have hc := cache_fields R next ν θ μ γ eγ δ eδ hνpos hν hθ hγ heγ hδ heδ
  have hp := product_fields R next sv μ hμpos hs hμ
  have hu := update_fields R next sv γ δ hex her hep
  exact {
    A := R.A
    b := R.b
    x := Function.update R.x (k + 1) (next.x)
    r := Function.update R.r (k + 1) (next.r)
    p := Function.update R.p (k + 1) (next.p)
    ν := Function.update R.ν (k + 1) (ν)
    θ := Function.update R.θ (k + 1) (θ)
    s := Function.update R.s k (sv)
    μ := Function.update R.μ k (μ)
    γ := Function.update R.γ k (γ)
    δ := Function.update R.δ k (δ)
    es := Function.update R.es k (-(R.A *ᵥ R.p k - sv))
    eμ := Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ))
    eγ := Function.update R.eγ k (eγ)
    ex := Function.update R.ex k (-(R.x k + γ • R.p k - next.x))
    er := Function.update R.er k (-(R.r k - γ • sv - next.r))
    eδ := Function.update R.eδ k (eδ)
    ep := Function.update R.ep k (-(next.r + δ • R.p k - next.p))
    ε := R.ε
    transpose_A := R.transpose_A
    ε_nonneg := R.ε_nonneg
    ε_le := R.ε_le
    k_pos := by omega
    x_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.x_zero
    r_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.r_zero
    p_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.p_zero
    ν_eq := hc.1
    abs_θ_le := hc.2.1
    ν_pos := hc.2.2.1
    s_eq := hp.1
    norm_es_le := hp.2.1
    μ_eq := hp.2.2.1
    abs_eμ_le := hp.2.2.2.1
    μ_pos := hp.2.2.2.2
    γ_eq := hc.2.2.2.1
    abs_eγ_le := hc.2.2.2.2.1
    x_succ := hu.1
    norm_ex_le := hu.2.1
    r_succ := hu.2.2.1
    norm_er_le := hu.2.2.2.1
    δ_eq := hc.2.2.2.2.2.1
    abs_eδ_le := hc.2.2.2.2.2.2
    p_succ := hu.2.2.2.2.1
    norm_ep_le := hu.2.2.2.2.2
  }

/-- The existing run can be extended by the defects derived from one actual next step.
All previous numerical data are retained by point updates; no extra run interface is used. -/
theorem exists_cgRun_succ {N k : ℕ} (R : CGRun N k)
    (next : CGState ℝ (Fin N)) (sv : Fin N → ℝ)
    (ν θ μ γ eγ δ eδ : ℝ) (hνpos : 0 < R.ν k) (hμpos : 0 < μ)
    (hν : ν = ‖WithLp.toLp 2 next.r‖ ^ 2 * (1 + θ)) (hθ : |θ| ≤ R.ε)
    (hs : ‖WithLp.toLp 2 (R.A *ᵥ R.p k - sv)‖ ≤
      R.ε * specNorm R.A * ‖WithLp.toLp 2 (R.p k)‖)
    (hμ : |R.p k ⬝ᵥ sv - μ| ≤ R.ε * ‖WithLp.toLp 2 (R.p k)‖ * ‖WithLp.toLp 2 sv‖)
    (hγ : γ = R.ν k / μ * (1 + eγ)) (heγ : |eγ| ≤ R.ε)
    (hδ : δ = ν / R.ν k * (1 + eδ)) (heδ : |eδ| ≤ R.ε)
    (hex : ‖WithLp.toLp 2 (R.x k + γ • R.p k - next.x)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.x k)‖ + |γ| * ‖WithLp.toLp 2 (R.p k)‖))
    (her : ‖WithLp.toLp 2 (R.r k - γ • sv - next.r)‖ ≤
      R.ε * (‖WithLp.toLp 2 (R.r k)‖ + |γ| * ‖WithLp.toLp 2 sv‖))
    (hep : ‖WithLp.toLp 2 (next.r + δ • R.p k - next.p)‖ ≤
      R.ε * (‖WithLp.toLp 2 next.r‖ + |δ| * ‖WithLp.toLp 2 (R.p k)‖)) :
    ∃ S : CGRun N (k + 1), S.A = R.A ∧ S.b = R.b ∧ S.ε = R.ε ∧
      S.x = Function.update R.x (k + 1) (next.x) ∧
      S.r = Function.update R.r (k + 1) (next.r) ∧
      S.p = Function.update R.p (k + 1) (next.p) ∧
      S.ν = Function.update R.ν (k + 1) (ν) ∧
      S.θ = Function.update R.θ (k + 1) (θ) ∧
      S.s = Function.update R.s k (sv) ∧
      S.μ = Function.update R.μ k (μ) ∧
      S.γ = Function.update R.γ k (γ) ∧
      S.δ = Function.update R.δ k (δ) ∧
      S.es = Function.update R.es k (-(R.A *ᵥ R.p k - sv)) ∧
      S.eμ = Function.update R.eμ k (-(R.p k ⬝ᵥ sv - μ)) ∧
      S.eγ = Function.update R.eγ k (eγ) ∧
      S.ex = Function.update R.ex k (-(R.x k + γ • R.p k - next.x)) ∧
      S.er = Function.update R.er k (-(R.r k - γ • sv - next.r)) ∧
      S.eδ = Function.update R.eδ k (eδ) ∧
      S.ep = Function.update R.ep k (-(next.r + δ • R.p k - next.p)) := by
  exact ⟨extendRoundedRun R next sv ν θ μ γ eγ δ eδ hνpos hμpos hν hθ hs hμ
    hγ heγ hδ heδ hex her hep, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  {u : P → ℝ} {dec : P → K → ℝ} {storedMatrix : Bool}
  {mv : Computation.Builder P ι ℕ ℕ Unit}

open Computation

/-- An actual active header executes the complete next canonical step and extends its
previously extracted run. Positive curvature follows from spectral input precision and a
nonzero decoded direction; all new defects are conclusions of primitive execution. -/
theorem cgRun_succ_of_active_header (I : Interp P ι K C) (tag : P)
    (hsem : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem)
    (st : St P K C) {N k : ℕ} (R : CGRun N k) (flag : ℝ)
    (h : StoreContext tag dec N R.A R.b ⟨R.x k, R.r k, R.p k⟩ (R.ν k) 0 flag
      st.store storedMatrix)
    (hε : R.ε = cgImplementationRoundoffBound N (u tag)) (hνpos : 0 < R.ν k)
    (hN : 0 < N) (hsmall : cgImplementationRoundoffBound N (u tag) ≤ 1 / 100)
    {a a' : ℝ} (ha : 0 < a) (hspec : spectrum ℝ R.A ⊆ Set.Icc a a')
    (hprec : 3 * cgImplementationRoundoffBound N (u tag) * a' ≤ a) (hp : R.p k ≠ 0)
    (hmv : IsMatvecRoutine I dec tag R.A (cgImplementationRoundoffBound N (u tag) *
      specNorm R.A) (fun store => if storedMatrix then HoldsDecoded store dec tag 5 0 R.A
      else True) 3 6 0 0 mv) :
    ∃ (prestate out : St P K C) (S : CGRun N (k + 1)),
      exec I (Builder.ifThenElse tag .eq ⟨4, 0⟩ ⟨7, 6⟩
      (do
      mv
      dot tag ⟨7, 2⟩ 3 0 6 0 (.const N)
      (Builder.ifThenElse tag .lt ⟨7, 6⟩ ⟨7, 2⟩ (do
      Builder.ins (.bin tag .div ⟨7, 3⟩ ⟨7, 0⟩ ⟨7, 2⟩)
      axpy tag ⟨7, 3⟩ 3 0 1 0 (.const N)
      Builder.ins (.un tag .neg ⟨7, 5⟩ ⟨7, 3⟩)
      axpy tag ⟨7, 5⟩ 6 0 2 0 (.const N)
      dot tag ⟨7, 1⟩ 2 0 2 0 (.const N)
      Builder.ins (.bin tag .div ⟨7, 4⟩ ⟨7, 1⟩ ⟨7, 0⟩)
      Builder.forRange (.const N) fun i => do
        Builder.ins (.bin tag .mul ⟨7, 2⟩ ⟨7, 4⟩ ⟨3, .var i⟩)
        Builder.ins (.bin tag .add ⟨3, .var i⟩ ⟨2, .var i⟩ ⟨7, 2⟩)
      Builder.ins (.copy tag ⟨7, 0⟩ ⟨7, 1⟩)
      Builder.ifThenElse tag .eq ⟨7, 0⟩ ⟨7, 6⟩
        (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 7⟩)) (pure ()))
      (Builder.ins (.copy tag ⟨4, 0⟩ ⟨7, 8⟩))) : Builder P ι ℕ ℕ Unit)
      (pure ())).run st = some out ∧
      S.A = R.A ∧ S.b = R.b ∧ S.ε = R.ε ∧
      StoreContext tag dec N S.A S.b ⟨S.x (k + 1), S.r (k + 1), S.p (k + 1)⟩ (S.ν (k + 1))
        (if S.ν (k + 1) = 0 then flag else 0) flag
        out.store storedMatrix ∧
      (∀ j ≤ k, S.x j = R.x j ∧ S.r j = R.r j ∧ S.p j = R.p j ∧ S.ν j = R.ν j) ∧
      (∀ i : Fin N, ∃ w, prestate.store.read tag 6 i = some w ∧ dec tag w = S.s k i) ∧
      (∃ w, prestate.store.read tag 7 2 = some w ∧ dec tag w = S.μ k) ∧
      (∃ w, out.store.read tag 7 3 = some w ∧ dec tag w = S.γ k) ∧
      (∃ w, out.store.read tag 7 4 = some w ∧ dec tag w = S.δ k) := by
  obtain ⟨prestate, out, next, sv, μ, ν, θ, γ, eγ, δ, eδ, _, hrun, hctx,
      hs, hμ, hμpos, hes, heμ, hνeq, hθ, _, _, hγeq, heγ, _, hδeq, heδ,
      hex, her, hep, hγ, hδ⟩ := exec_rounded_positive_step (hmv := hmv) I tag hsem hz st N R.A R.b
        ⟨R.x k, R.r k, R.p k⟩ (R.ν k) flag h hνpos hN hsmall R.transpose_A ha hspec hprec hp
  rw [← hε] at hes heμ hθ heγ heδ hex her hep
  let S := extendRoundedRun R next sv ν θ μ γ eγ δ eδ hνpos hμpos hνeq hθ hes heμ
    hγeq heγ hδeq heδ hex her hep
  refine ⟨prestate, out, S, hrun, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, extendRoundedRun, Function.update_self] using hctx
  · intro j hj
    simp only [S, extendRoundedRun, Function.update_of_ne (show j ≠ k + 1 by omega), and_self]
  · simpa only [S, extendRoundedRun, Function.update_self] using hs
  · simpa only [S, extendRoundedRun, Function.update_self] using hμ
  · simpa only [S, extendRoundedRun, Function.update_self] using hγ
  · simpa only [S, extendRoundedRun, Function.update_self] using hδ

end NLAlib.CGImplementation
