/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.LanczosFA
public import NLAlibScaffold.Polynomial.Approximation.MinimaxError

/-!
# Lanczos-FA and the minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Krylov/Functions/LanczosFA.lean` whose proofs are deferred
(`docs/design/Polynomial-BestApproximation.md`, §3.4): the uniform-approximation bound of
Lanczos-FA restated with the minimax error, as the papers state it.

## Main results

* `Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_continuousOn`: the bound
  $2E_q(f)\|\mathbf{b}\|$ after $q + 1$ steps.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Lanczos-FA and the minimax error**: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$
and $f$ continuous on $[a, a']$, $q + 1$ steps of Lanczos-FA satisfy
$$\|f(\mathbf{A})\mathbf{b} - \mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\| \le
2E_q(f; [a, a'])\|\mathbf{b}\|\,,$$
$E_q$ the error of the best uniform approximation of $f$ on $[a, a']$ by polynomials of degree
at most $q$ (`minimaxError`). [ChenPersson2026, (2)]; [Saad1992, §3]; there with $E_q$.
Proof: S, about 6 lines. `exists_degree_le_isUniformApproxOn_minimaxError` (`isCompact_Icc`)
gives a best $p$ with `degree_le` $q < q + 1$; then
`Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`.
Result: lanczos-fa-uniform-bound -/
theorem _root_.Matrix.IsHermitian.norm_cfc_mulVec_sub_lanczosFA_le_of_continuousOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      2 * minimaxError f (Set.Icc a a') q * ‖WithLp.toLp 2 b‖ := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf q
  exact hA.norm_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs
    (hp.trans_lt (by exact_mod_cast Nat.lt_succ_self q)) hε b

end NLAlib
