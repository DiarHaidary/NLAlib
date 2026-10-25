/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Order.Fin.Basic

/-!
# Ordered zeros between sign changes

The intermediate value theorem, applied between consecutive points of an ordered tuple at which
a continuous real function changes sign, gives one zero in each gap, so strictly ordered zeros.
This is the root-counting step of de la Vallée Poussin's theorem and of the interpolation property
of best approximants (`docs/design/Polynomial-BestApproximation.md`). An upstream candidate for
`Mathlib/Topology/Order/IntermediateValue.lean`.

## Main results

* `exists_strictMono_eq_zero_of_mul_neg`: ordered zeros between sign changes.
-/

@[expose] public section

/-- **Ordered zeros between sign changes.** If $v_0 < v_1 < \dots < v_k$ and $f$ is continuous on
$[v_0, v_k]$ with $f(v_i)f(v_{i+1}) < 0$ for every $i < k$, then $f$ has zeros
$c_0 < c_1 < \dots < c_{k-1}$ with $v_i < c_i < v_{i+1}$. -/
theorem exists_strictMono_eq_zero_of_mul_neg {k : ℕ} {f : ℝ → ℝ} {v : Fin (k + 1) → ℝ}
    (hv : StrictMono v) (hf : ContinuousOn f (Set.Icc (v 0) (v (Fin.last k))))
    (hsign : ∀ i : Fin k, f (v i.castSucc) * f (v i.succ) < 0) :
    ∃ c : Fin k → ℝ, StrictMono c ∧
      ∀ i, c i ∈ Set.Ioo (v i.castSucc) (v i.succ) ∧ f (c i) = 0 := by
  have key : ∀ i : Fin k, ∃ c, c ∈ Set.Ioo (v i.castSucc) (v i.succ) ∧ f c = 0 := by
    intro i
    have hab : v i.castSucc ≤ v i.succ := (hv Fin.castSucc_lt_succ).le
    have hcont : ContinuousOn f (Set.Icc (v i.castSucc) (v i.succ)) :=
      hf.mono (Set.Icc_subset_Icc (hv.monotone (Fin.zero_le _)) (hv.monotone (Fin.le_last _)))
    rcases mul_neg_iff.1 (hsign i) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact intermediate_value_Ioo' hab hcont ⟨h2, h1⟩
    · exact intermediate_value_Ioo hab hcont ⟨h1, h2⟩
  choose c hc using key
  refine ⟨c, fun i j hij => ?_, hc⟩
  calc c i < v i.succ := (hc i).1.2
    _ ≤ v j.castSucc := hv.monotone (Fin.succ_le_castSucc_iff.2 hij)
    _ < c j := (hc j).1.1
