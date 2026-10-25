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
$$\|\mathbf{x}_\star - \mathbf{x}_q\|_{\mathbf{A}}^2 = \int x^{-1}\,d\mu_{\mathbf{A},\mathbf{r}_0} -
\int x^{-1}\,d\,\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\mathbf{r}_0}, q)\,.$$
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

omit [DecidableEq n] in
/-- Expansion of the error quadratic form under the Galerkin condition (helper). -/
private lemma quadForm_sub_eq_of_galerkin {A : Matrix n n 𝕜} (hH : A.IsHermitian) {d r y : n → 𝕜}
    (hd : A *ᵥ d = r) (hgal : star y ⬝ᵥ (r - A *ᵥ y) = 0) :
    quadForm A (d - y) = star d ⬝ᵥ r - star r ⬝ᵥ y := by
  have hdy : star d ⬝ᵥ (A *ᵥ y) = star r ⬝ᵥ y := by
    rw [← hd, Matrix.star_mulVec, hH.eq, Matrix.dotProduct_mulVec]
  have hgal' : star y ⬝ᵥ (A *ᵥ y) = star y ⬝ᵥ r := by
    rw [dotProduct_sub, sub_eq_zero] at hgal
    exact hgal.symm
  rw [quadForm_def, star_sub, Matrix.mulVec_sub, hd, sub_dotProduct, dotProduct_sub,
    dotProduct_sub, hdy, hgal']
  ring

/-- **The CG error is a Gauss quadrature error**: for positive definite $\mathbf{A}$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, every $\mathbf{x}_0$ and $q$, with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$ and $\mathbf{x}_q =
\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)$,
$$\|\mathbf{x}_\star - \mathbf{x}_q\|_{\mathbf{A}}^2 = \int x^{-1}\,d\mu_{\mathbf{A},\mathbf{r}_0} -
\int x^{-1}\,d\,\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\mathbf{r}_0}, q)\,.$$
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
  have hH : A.IsHermitian := hA.isHermitian
  have hd : A *ᵥ (xs - x₀) = b - A *ᵥ x₀ := by rw [Matrix.mulVec_sub, hxs]
  have hcg : cgIterate A b x₀ q = x₀ + cgIterate A (b - A *ᵥ x₀) 0 q := by
    rw [cgIterate, cgIterate, Matrix.mulVec_zero, sub_zero, zero_add]
  have hmem : cgIterate A (b - A *ᵥ x₀) 0 q ∈ krylovSpace A (b - A *ᵥ x₀) q := by
    simpa using cgIterate_sub_mem_krylovSpace A (b - A *ᵥ x₀) 0 q
  obtain ⟨c, hc⟩ := LinearMap.mem_range.1 hmem
  simp only [Matrix.mulVecLin_apply] at hc
  have hG := hA.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero (b - A *ᵥ x₀) 0 q
  simp only [Matrix.mulVec_zero, sub_zero] at hG
  have hgal : star (cgIterate A (b - A *ᵥ x₀) 0 q) ⬝ᵥ
      ((b - A *ᵥ x₀) - A *ᵥ cgIterate A (b - A *ᵥ x₀) 0 q) = 0 := by
    nth_rw 1 [← hc]
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hG, dotProduct_zero]
  have hinv : A⁻¹ *ᵥ (b - A *ᵥ x₀) = xs - x₀ := by
    rw [← hd, Matrix.mulVec_mulVec,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit), Matrix.one_mulVec]
  rw [hcg, show xs - (x₀ + cgIterate A (b - A *ᵥ x₀) 0 q) =
      (xs - x₀) - cgIterate A (b - A *ᵥ x₀) 0 q by abel,
    quadForm_sub_eq_of_galerkin hH hd hgal, map_sub]
  congr 1
  · have hsym : ∀ u v : n → 𝕜, star u ⬝ᵥ v = star (star v ⬝ᵥ u) := by
      intro u v
      simp [dotProduct, mul_comm]
    rw [integral_spectralMeasure, ← hA.inv_eq_cfc, quadForm_def, hinv, hsym (xs - x₀)]
    exact RCLike.conj_re _
  · rw [← hA.isHermitian.lanczosQuadrature_eq_gaussQuadrature, integral_lanczosQuadrature,
      hH.lanczosFA_inv_eq_cgIterate]

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
  have hf : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc a a') :=
    continuousOn_inv₀.mono fun x hx => (ha.trans_le hx.1).ne'
  have hf' : ContDiffOn ℝ (2 * q + 1 : ℕ) (fun x : ℝ => x⁻¹) (Set.Ioo a a') :=
    (contDiffOn_inv (𝕜 := ℝ)).mono fun x hx => (ha.trans hx.1).ne'
  have hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q + 1) (fun x : ℝ => x⁻¹) x ≤ 0 := by
    intro x hx
    have hx0 : (0 : ℝ) < x := ha.trans hx.1
    have h1 : (0 : ℝ) < x ^ (-1 - ((2 * q + 1 : ℕ) : ℤ)) := zpow_pos hx0 _
    have h2 : (0 : ℝ) < ((2 * q + 1).factorial : ℝ) := by positivity
    rw [iteratedDeriv_eq_iterate, iter_deriv_inv', Odd.neg_one_pow ⟨q, rfl⟩]
    nlinarith [mul_pos h2 h1]
  have h := re_quadForm_cfc_le_integral_radauQuadrature_of_iteratedDeriv_nonpos hs haa' hf q hf' hD
    (b - A *ᵥ x₀)
  rw [Matrix.PosDef.re_quadForm_sub_cgIterate_eq_integral_sub hA hxs x₀ q]
  refine sub_le_sub_right ?_ _
  exact (integral_spectralMeasure A (b - A *ᵥ x₀) (fun x : ℝ => x⁻¹)).symm ▸ h

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
  have hf : ContinuousOn (fun x : ℝ => x⁻¹) (Set.Icc a a') :=
    continuousOn_inv₀.mono fun x hx => ne_of_gt (lt_of_lt_of_le ha hx.1)
  have hf' : ContDiffOn ℝ (2 * q + 1 : ℕ) (fun x : ℝ => x⁻¹) (Set.Ioo a a') :=
    contDiffOn_id.inv fun x hx => ne_of_gt (ha.trans hx.1)
  have hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q + 1) (fun x : ℝ => x⁻¹) x ≤ 0 := by
    intro x hx
    have hx0 : 0 < x := ha.trans hx.1
    rw [iteratedDeriv_eq_iterate, show (fun x : ℝ => x⁻¹) = Inv.inv from rfl, iter_deriv_inv]
    have hodd : (-1 : ℝ) ^ (2 * q + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [hodd]
    have hpos : (0 : ℝ) < x ^ (-1 - ((2 * q + 1 : ℕ) : ℤ)) := zpow_pos hx0 _
    have hfac : (0 : ℝ) < ((2 * q + 1).factorial : ℝ) := by positivity
    nlinarith [mul_pos hfac hpos]
  have h := integral_radauQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonpos hs haa' hf q hf' hD
    (b - A *ᵥ x₀)
  have h2 := Matrix.PosDef.re_quadForm_sub_cgIterate_eq_integral_sub hA hxs x₀ q
  rw [integral_spectralMeasure] at h2
  linarith

end NLAlib
