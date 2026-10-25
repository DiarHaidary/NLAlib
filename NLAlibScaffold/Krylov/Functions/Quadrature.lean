/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.Quadrature
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Lanczos quadrature and the minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Krylov/Functions/Quadrature.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.4): the quadrature error of $q + 1$ Lanczos
steps restated with the minimax error in degree $2q + 1$.

## Main results

* `Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_continuousOn`: the bound
  $2E_{2q + 1}(f)\|\mathbf{b}\|^2$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Near-best approximants: for $f$ continuous on $[a, a']$ and $\delta > 0$, some real
polynomial of degree at most $n$ is within $E_n(f) + \delta$ of $f$ on $[a, a']$. -/
private theorem exists_degree_le_isUniformApproxOn_minimaxError_add {f : ℝ → ℝ} {a a' : ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) (n : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : ℝ[X], p.degree ≤ n ∧ Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a')
      (minimaxError f (Set.Icc a a') n + δ) := by
  rcases (Set.Icc a a').eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp, fun x hx => by simp [he] at hx⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hS : {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ n ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε}.Nonempty :=
    ⟨C, 0, by simp, fun x hx => by simpa [dist_comm, Real.dist_eq] using hC x hx⟩
  obtain ⟨ε, ⟨p, hp, hpε⟩, hlt⟩ := exists_lt_of_csInf_lt hS
    (lt_add_of_pos_right (minimaxError f (Set.Icc a a') n) hδ)
  exact ⟨p, hp, hpε.mono_error hlt.le⟩

/-- **Lanczos quadrature and the minimax error**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a']$ and $f$ continuous on $[a, a']$, $q + 1$ Lanczos steps give
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\bigr)\bigr\rvert \le
2E_{2q + 1}(f; [a, a'])\|\mathbf{b}\|^2\,,$$
$E_{2q + 1}$ the error of the best uniform approximation of $f$ on $[a, a']$ by polynomials of
degree at most $2q + 1$ (`minimaxError`), the degree of exactness of the Gauss rule.
[GolubMeurant2010, Ch. 6], the exactness it rests on.
Proof: S, about 8 lines. `exists_degree_le_isUniformApproxOn_minimaxError` in degree $2q + 1$;
$2q + 1 < 2(q + 1)$ (`omega`, `exact_mod_cast`); then
`Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`.
Result: lanczos-gauss-quadrature -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_continuousOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      2 * minimaxError f (Set.Icc a a') (2 * q + 1) * ‖WithLp.toLp 2 b‖ ^ 2 := by
  set c := ‖WithLp.toLp 2 b‖ ^ 2
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hc : 0 ≤ c := by positivity
  obtain ⟨p, hp, hpε⟩ := exists_degree_le_isUniformApproxOn_minimaxError_add hf (2 * q + 1)
    (δ := ε / (2 * (c + 1))) (by positivity)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  refine (hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hpε
    b).trans ?_
  have : ε / (2 * (c + 1)) * (2 * c) ≤ ε := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith
  nlinarith

end NLAlib
