/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CG
public import NLAlibScaffold.Krylov.Functions.QuadratureBounds

/-!
# The CG error as a quadrature error

For positive definite $\mathbf{A}$, the squared $\mathbf{A}$-norm error of CG after $q$ steps is
the Gauss quadrature error of $x \mapsto x^{-1}$ for the spectral measure of the initial
residual:
$$\|\mathbf{x}_\star - \mathbf{x}_q\|_{\mathbf{A}}^2 = \int x^{-1}\,d\mu_{\mathbf{A},\mathbf{r}_0}
- \int x^{-1}\,d\,\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\mathbf{r}_0}, q)\,.$$
With the Radau rules at bounds $0 < a \le \lambda_{\min}$ and $a' \ge \lambda_{\max}$ this gives
the computable two-sided estimates of Golub and Meurant (Golub–Strakoš): the left Radau rule
bounds the error from above, the right Radau rule from below.

Design: `docs/design/Polynomial-QuadratureRemainder.md`, C1–C3.

## Main results

* `Matrix.PosDef.re_quadForm_sub_cgIterate_eq_integral_sub`: the error identity.
* `Matrix.PosDef.re_quadForm_sub_cgIterate_le_integral_radauQuadrature_sub`: the upper bound.
* `Matrix.PosDef.integral_radauQuadrature_sub_le_re_quadForm_sub_cgIterate`: the lower bound.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The CG error is a Gauss quadrature error**: for positive definite $\mathbf{A}$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, every $\mathbf{x}_0$ and $q$, with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$ and $\mathbf{x}_q =
\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)$,
$$\|\mathbf{x}_\star - \mathbf{x}_q\|_{\mathbf{A}}^2 = \int x^{-1}\,d\mu_{\mathbf{A},\mathbf{r}_0}
- \int x^{-1}\,d\,\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\mathbf{r}_0}, q)\,.$$
[GolubMeurant2010, Ch. 12]; [GolubStrakos1994, §3] (locators to check).
Proof: M, about 40 lines. `cgIterate` gives $\mathbf{x}_q = \mathbf{x}_0 + \mathbf{y}$ with
$\mathbf{y} = \mathsf{cgIterate}(\mathbf{A}, \mathbf{r}_0, \mathbf{0}, q)$ (unfold,
`Matrix.mulVec_zero`, `sub_zero`) $= \mathsf{lanczosFA}(\mathbf{A}, x^{-1}, \mathbf{r}_0, q)$
(`Matrix.IsHermitian.lanczosFA_inv_eq_cgIterate`), and
$\mathbf{x}_\star - \mathbf{x}_0 = \mathbf{A}^{-1}\mathbf{r}_0$. Galerkin orthogonality
(`Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero`, with
$\mathbf{y} \in \mathcal{K}_q$ from `cgIterate_sub_mem_krylovSpace`) gives
$\mathbf{y}^{\mathsf{H}}(\mathbf{r}_0 - \mathbf{A}\mathbf{y}) = 0$, so the error is
$\operatorname{Re}\mathbf{r}_0^{\mathsf{H}}\mathbf{A}^{-1}\mathbf{r}_0 -
\operatorname{Re}\mathbf{r}_0^{\mathsf{H}}\mathbf{y}$. The first term is
$\int x^{-1}\,d\mu_{\mathbf{A},\mathbf{r}_0}$ (`integral_spectralMeasure`,
`Matrix.IsHermitian.cfc_inv_eq_pinv`-style with `Matrix.PosDef` invertible), the second the
Gauss rule (`integral_lanczosQuadrature`,
`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`).
Result: cg-error-gauss-quadrature -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_eq_integral_sub {A : Matrix n n 𝕜}
    (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) =
      ∫ x, x⁻¹ ∂spectralMeasure A (b - A *ᵥ x₀) -
        ∫ x, x⁻¹ ∂gaussQuadrature (spectralMeasure A (b - A *ᵥ x₀)) q := by
  sorry

/-- **The Gauss–Radau upper bound on the CG error**: for positive definite $\mathbf{A}$ with
spectrum in $[a, a']$, $0 < a < a'$, $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, every
$\mathbf{x}_0$ and $q$, with $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$ and $\mu =
\mu_{\mathbf{A},\mathbf{r}_0}$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le \int x^{-1}\,d\,\mathsf{radauQuadrature}(\mu, a, q) -
\int x^{-1}\,d\,\mathsf{gaussQuadrature}(\mu, q)\,:$$
the left Radau rule with $q$ free nodes overestimates $\int x^{-1}\,d\mu$ because
$(x^{-1})^{(2q+1)} < 0$. [GolubMeurant2010, Ch. 12]; [GolubStrakos1994, §3] (locators to
check).
Proof: M, about 25 lines. `Matrix.PosDef.re_quadForm_sub_cgIterate_eq_integral_sub` and
`re_quadForm_cfc_le_integral_radauQuadrature_of_iteratedDeriv_nonpos` for $f(x) = x^{-1}$,
rewritten by `integral_spectralMeasure`: $f$ is continuous on $[a, a']$ and smooth on
$(a, a')$ (`contDiffOn_inv`-style, $0 < a$), and
$f^{(2q+1)}(x) = -(2q+1)!\,x^{-2q-2} \le 0$ (`iteratedDeriv_eq_iterate`, `iter_deriv_inv`,
`Even.neg_one_pow`).
Result: cg-error-gauss-radau-bounds -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_integral_radauQuadrature_sub
    {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ} (ha : 0 < a) (haa' : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      ∫ x, x⁻¹ ∂radauQuadrature (spectralMeasure A (b - A *ᵥ x₀)) a q -
        ∫ x, x⁻¹ ∂gaussQuadrature (spectralMeasure A (b - A *ᵥ x₀)) q := by
  sorry

/-- **The Gauss–Radau lower bound on the CG error**: for positive definite $\mathbf{A}$ with
spectrum in $[a, a']$, $0 < a < a'$, $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, every
$\mathbf{x}_0$ and $q$, with $\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$ and $\mu =
\mu_{\mathbf{A},\mathbf{r}_0}$,
$$\int x^{-1}\,d\,\mathsf{radauQuadrature}(\mu, a', q) -
\int x^{-1}\,d\,\mathsf{gaussQuadrature}(\mu, q) \le
\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\,.$$
[GolubMeurant2010, Ch. 12]; [GolubStrakos1994, §3] (locators to check).
Proof: S, about 15 lines. As
`Matrix.PosDef.re_quadForm_sub_cgIterate_le_integral_radauQuadrature_sub`, with
`integral_radauQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonpos` at $a'$. -/
theorem _root_.Matrix.PosDef.integral_radauQuadrature_sub_le_re_quadForm_sub_cgIterate
    {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ} (ha : 0 < a) (haa' : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    ∫ x, x⁻¹ ∂radauQuadrature (spectralMeasure A (b - A *ᵥ x₀)) a' q -
        ∫ x, x⁻¹ ∂gaussQuadrature (spectralMeasure A (b - A *ᵥ x₀)) q ≤
      RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) := by
  sorry

end NLAlib
