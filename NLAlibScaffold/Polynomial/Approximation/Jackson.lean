/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.Jackson
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Jackson's theorem for the minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Approximation/Jackson.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.4): Jackson's theorem on an interval in the
form $E_N(f) \le \dots$ in which it is usually printed.

## Main results

* `NLAlib.minimaxError_le_of_lipschitzOnWith`: Jackson's bound on $E_N(f; [a, b])$.
-/

@[expose] public section

open scoped NNReal

namespace NLAlib

/-- **Jackson's theorem for the minimax error**: an $L$-Lipschitz real $f$ on $[a, b]$, $a < b$,
satisfies <!-- value jacksonApproximationConstant -->
$$E_N(f; [a, b]) \le \frac{\pi L(b - a)}{2(N + 2)}$$
(the constant is `jacksonApproximationConstant`). [ChenTrogdonUbaru2022, Appendix C,
Theorem 38]; there on $[-1, 1]$ with the factor $\pi^2/2$; [Rivlin1981, Ch. 1] (locator to
check), the classical $E_N$ form.
Proof: S, about 6 lines. `exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith`
(`𝕜 := ℝ`), simplified with `RCLike.ofReal_real_eq_id`, then
`minimaxError_le_of_isUniformApproxOn` (nonnegativity by `positivity`,
`jacksonApproximationConstant_pos`).
Result: jackson-lipschitz -/
theorem minimaxError_le_of_lipschitzOnWith {f : ℝ → ℝ} {L : ℝ≥0} {a b : ℝ} (hab : a < b)
    (hf : LipschitzOnWith L f (Set.Icc a b)) (N : ℕ) :
    minimaxError f (Set.Icc a b) N ≤
      jacksonApproximationConstant * L * (b - a) / (2 * (N + 2)) := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) hab hf N
  simp only [RCLike.ofReal_real_eq_id, id] at hε
  unfold minimaxError
  refine csInf_le ⟨0, ?_⟩ ⟨p, hp, hε⟩
  rintro ε' ⟨q, -, hq⟩
  obtain ⟨x, hx⟩ : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
  exact (abs_nonneg _).trans (hq x hx)

end NLAlib
