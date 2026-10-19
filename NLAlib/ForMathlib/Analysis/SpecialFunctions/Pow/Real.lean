/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# A ratio inequality for real powers

For $0 < a$, $x, y \in [a, a']$, $t \ge 0$ and real $\alpha$, the ratio of
$z^\alpha / (z + t)$ at $x$ and $y$ is at most $(a'/a)^{\max(\alpha, 1 - \alpha)}$: the kernel
inequality behind the near-optimality of Krylov methods for $\mathbf{A}^\alpha$. Upstream
candidate for `Mathlib.Analysis.SpecialFunctions.Pow.Real`.

## Main results

* `Real.rpow_mul_add_le`:
  $x^\alpha (y + t) \le (a'/a)^{\max(\alpha, 1 - \alpha)}\, y^\alpha (x + t)$.
-/

@[expose] public section

namespace Real

/-- For $1 \le s \le K$ and $\beta \le E$ with $E \ge 0$, $s^\beta \le K^E$. -/
private theorem rpow_le_rpow_of_one_le {s K β E : ℝ} (hs : 1 ≤ s) (hsK : s ≤ K) (hβ : β ≤ E)
    (hE : 0 ≤ E) : s ^ β ≤ K ^ E :=
  calc s ^ β ≤ s ^ max β 0 := Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _)
    _ ≤ K ^ max β 0 := Real.rpow_le_rpow (by linarith) hsK (le_max_right _ _)
    _ ≤ K ^ E := Real.rpow_le_rpow_of_exponent_le (hs.trans hsK) (max_le hβ hE)

/-- **The kernel ratio for the power weights**: for $0 < a$, $x, y \in [a, a']$, $t \ge 0$ and
real $\alpha$,
$$\frac{x^\alpha}{x + t} \le \Bigl(\frac{a'}{a}\Bigr)^{\max(\alpha, 1 - \alpha)}
\frac{y^\alpha}{y + t} \,,$$
written without division: the kernel $z^\alpha / (z + t)$ of a weighted Stieltjes function varies
by at most that factor on $[a, a']$. [ChenPersson2026, Lemma 6], there for the extreme
eigenvalues and integrated against a measure. -/
theorem rpow_mul_add_le {a a' x y t : ℝ} (ha : 0 < a) (hx : x ∈ Set.Icc a a')
    (hy : y ∈ Set.Icc a a') (ht : 0 ≤ t) (α : ℝ) :
    x ^ α * (y + t) ≤ (a' / a) ^ max α (1 - α) * (y ^ α * (x + t)) := by
  obtain ⟨hax, hxa⟩ := hx
  obtain ⟨hay, hya⟩ := hy
  have hx0 : 0 < x := ha.trans_le hax
  have hy0 : 0 < y := ha.trans_le hay
  have hE : 0 ≤ max α (1 - α) := by
    rcases le_total α (1 - α) with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith
  have hxt : 0 < x + t := by linarith
  rcases le_total x y with hxy | hyx
  · -- $y = r x$ with $1 \le r \le a'/a$
    set r := y / x
    have hr1 : 1 ≤ r := (one_le_div hx0).mpr hxy
    have hrK : r ≤ a' / a := div_le_div₀ (by linarith) hya ha hax
    have hyr : y = r * x := by simp only [r]; field_simp
    have hyα : y ^ α = r ^ α * x ^ α := by rw [hyr, Real.mul_rpow (by linarith) hx0.le]
    have hr : r ^ (1 - α) * r ^ α = r := by
      rw [← Real.rpow_add (by linarith), sub_add_cancel, Real.rpow_one]
    have hyt : y + t ≤ r * (x + t) := by rw [hyr]; nlinarith
    have hK := rpow_le_rpow_of_one_le hr1 hrK (le_max_right α (1 - α)) hE
    have hxα : 0 < x ^ α := Real.rpow_pos_of_pos hx0 α
    calc x ^ α * (y + t) ≤ x ^ α * (r * (x + t)) := by gcongr
      _ = r ^ (1 - α) * (y ^ α * (x + t)) := by
          rw [hyα]
          conv_lhs => rw [← hr]
          ring
      _ ≤ (a' / a) ^ max α (1 - α) * (y ^ α * (x + t)) := by gcongr
  · -- $x = s y$ with $1 \le s \le a'/a$
    set s := x / y
    have hs1 : 1 ≤ s := (one_le_div hy0).mpr hyx
    have hsK : s ≤ a' / a := div_le_div₀ (by linarith) hxa ha hay
    have hxs : x = s * y := by simp only [s]; field_simp
    have hxα : x ^ α = s ^ α * y ^ α := by rw [hxs, Real.mul_rpow (by linarith) hy0.le]
    have hK := rpow_le_rpow_of_one_le hs1 hsK (le_max_left α (1 - α)) hE
    have hyα : 0 < y ^ α := Real.rpow_pos_of_pos hy0 α
    calc x ^ α * (y + t) ≤ x ^ α * (x + t) := by gcongr
      _ = s ^ α * (y ^ α * (x + t)) := by rw [hxα]; ring
      _ ≤ (a' / a) ^ max α (1 - α) * (y ^ α * (x + t)) := by gcongr

end Real
