/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.AnalyticApproximation
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Analytic functions and the minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Polynomial/Approximation/AnalyticApproximation.lean` whose proofs are
deferred (`docs/design/Polynomial-BestApproximation.md`, §3.4): the Bernstein-ellipse rate as a
bound on $E_N(f; [a, b])$.

## Main results

* `NLAlib.minimaxError_le_of_differentiableOn`: the Bernstein-ellipse bound on $E_N$.
-/

@[expose] public section

namespace NLAlib

/-- **Analytic functions and the minimax error.** On $[a, b]$, $a < b$, if the pullback
$t \mapsto f(((b - a)t + b + a)/2)$ of a real $f$ extends to a function holomorphic and bounded by
$M$ on the open Bernstein ellipse $E_\rho$, $\rho > 1$, then
$$E_N(f; [a, b]) \le \frac{2M}{\rho^N(\rho - 1)}\,.$$
[Trefethen2019, Theorem 8.2] (locator from the quarry), there on $[-1, 1]$ for the Chebyshev
truncation.
Proof: S, about 8 lines. `exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn`
(`𝕜 := ℝ`, the extension hypothesis through `RCLike.toComplex_ofReal`), then
`minimaxError_le_of_isUniformApproxOn`; $M \ge 0$ from `hM` at $0 \in E_\rho$
(`ofReal_mem_openBernsteinEllipse`), so the bound is nonnegative (`positivity`).
Result: bernstein-ellipse-approx -/
theorem minimaxError_le_of_differentiableOn {f : ℝ → ℝ} {F : ℂ → ℂ} {a b ρ M : ℝ} (hab : a < b)
    (hρ : 1 < ρ) (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((b - a) * t + b + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1)) (N : ℕ) :
    minimaxError f (Set.Icc a b) N ≤ 2 * M / (ρ ^ N * (ρ - 1)) := by
  obtain ⟨p, hdeg, hp⟩ := exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn (𝕜 := ℝ)
    (f := f) hab hρ hFd hM
    (fun t ht => by rw [← hExt ht]; exact RCLike.toComplex_ofReal (𝕜 := ℝ) _) N
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab.le
  refine csInf_le ⟨0, ?_⟩ ⟨p, hdeg, hp⟩
  rintro ε ⟨q, -, hq⟩
  exact hq.nonneg hne

end NLAlib
