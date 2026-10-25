/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.Quadrature
public import NLAlibScaffold.Polynomial.Approximation.MinimaxError

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
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_minimaxError isCompact_Icc hf (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  exact hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b

end NLAlib
