/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.Quadrature
public import NLAlibScaffold.Polynomial.Orthogonal.RadauLobatto

/-!
# Two-sided bounds on quadratic forms of matrix functions

For Hermitian $\mathbf{A}$ with spectrum in $[a, a']$ and $f$ whose derivatives of the relevant
order have a sign on $(a, a')$, the Gauss (Lanczos), Gauss–Radau and Gauss–Lobatto rules of the
spectral measure $\mu_{\mathbf{A},\mathbf{b}}$ bracket
$\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b} = \int f\,d\mu_{\mathbf{A},\mathbf{b}}$
(Golub and Meurant). With $q$ Lanczos steps:

* the Lanczos quadrature $\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$
  is a lower bound when $f^{(2q)} \ge 0$ and an upper bound when $f^{(2q)} \le 0$, with the error
  $\frac{f^{(2q)}(\xi)}{(2q)!}\|\pi_q(\mathbf{A})\mathbf{b}\|^2$;
* the Radau rule with $q$ free nodes and prescribed node $a$ (resp. $a'$) is a lower (resp.
  upper) bound when $f^{(2q+1)} \ge 0$, and the other way round when $f^{(2q+1)} \le 0$;
* the Lobatto rule with $q$ free nodes is an upper bound when $f^{(2q+2)} \ge 0$ and a lower bound
  when $f^{(2q+2)} \le 0$.

For $f(x) = x^{-1}$ on $[a, a']$, $a > 0$, Gauss and the right Radau rule bound from below, the
left Radau rule from above. The Radau rules are computed from the modified Lanczos tridiagonal
(`Matrix.IsHermitian.integral_radauQuadrature_spectralMeasure`).

Design: `docs/design/Polynomial-QuadratureRemainder.md`, K1–K9.

## Main results

* `Matrix.IsHermitian.exists_re_quadForm_cfc_sub_re_star_dotProduct_lanczosFA_eq`: the Lanczos
  quadrature error.
* `Matrix.IsHermitian.re_star_dotProduct_lanczosFA_le_of_iteratedDeriv_nonneg`,
  `Matrix.IsHermitian.re_quadForm_cfc_le_re_star_dotProduct_lanczosFA_of_iteratedDeriv_nonpos`:
  Gauss bounds.
* `NLAlib.integral_radauQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonneg` and
  three siblings: Radau bounds.
* `NLAlib.re_quadForm_cfc_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg`,
  `NLAlib.integral_lobattoQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonpos`:
  Lobatto bounds.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Gauss (Lanczos) quadrature -/

/-- **The Lanczos quadrature error**: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$,
$a < a'$, $q > 0$, $f$ continuous on $[a, a']$ and $C^{2q}$ on $(a, a')$, and every
$\mathbf{b}$, there is $\xi \in (a, a')$ with
$$\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b} -
\operatorname{Re}\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) =
\frac{f^{(2q)}(\xi)}{(2q)!}\|\pi_q(\mathbf{A})\mathbf{b}\|^2\,,$$
$\pi_q$ the monic orthogonal polynomial of degree $q$ of $\mu_{\mathbf{A},\mathbf{b}}$ (the
characteristic polynomial of the Lanczos tridiagonal below the grade); past the grade both
sides are $0$. [GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: M, about 30 lines. `exists_integral_sub_integral_gaussQuadrature_eq` for
$\mu_{\mathbf{A},\mathbf{b}}$ (support `ae_mem_Icc_spectralMeasure`); rewrite
$\int f\,d\mu_{\mathbf{A},\mathbf{b}}$ by `integral_spectralMeasure` and the Gauss rule by
`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`, `integral_lanczosQuadrature`; and
$\int\pi_q^2\,d\mu_{\mathbf{A},\mathbf{b}} = \operatorname{Re}\mathbf{b}^{\mathsf{H}}
\pi_q(\mathbf{A})^2\mathbf{b} = \|\pi_q(\mathbf{A})\mathbf{b}\|^2$
(`Matrix.IsHermitian.integral_eval_spectralMeasure` with $\pi_q^2$, `map_pow`, the Hermitian
$\pi_q(\mathbf{A})$, `quadForm`, `EuclideanSpace.inner_eq_star_dotProduct`-style). -/
theorem _root_.Matrix.IsHermitian.exists_re_quadForm_cfc_sub_re_star_dotProduct_lanczosFA_eq
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a')) (b : n → 𝕜) :
    ∃ ξ ∈ Set.Ioo a a', RCLike.re (quadForm (cfc f A) b) -
        RCLike.re (star b ⬝ᵥ lanczosFA A f b q) =
      iteratedDeriv (2 * q) f ξ / (2 * q).factorial *
        ‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) q) *ᵥ b)‖ ^ 2 := by
  sorry

/-- **Lanczos quadrature is a lower bound** for $f$ with nonnegative derivative of order $2q$
(Golub–Meurant): for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, $a < a'$, $q > 0$, $f$
continuous on $[a, a']$, $C^{2q}$ on $(a, a')$ with $f^{(2q)} \ge 0$ there, and every
$\mathbf{b}$,
$$\operatorname{Re}\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q) \le
\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 10 lines. `integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg` for
$\mu_{\mathbf{A},\mathbf{b}}$, with `integral_spectralMeasure`,
`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature` and `integral_lanczosQuadrature`. -/
theorem _root_.Matrix.IsHermitian.re_star_dotProduct_lanczosFA_le_of_iteratedDeriv_nonneg
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q) f x) (b : n → 𝕜) :
    RCLike.re (star b ⬝ᵥ lanczosFA A f b q) ≤ RCLike.re (quadForm (cfc f A) b) := by
  sorry

/-- **Lanczos quadrature is an upper bound** for $f$ with nonpositive derivative of order $2q$:
for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, $a < a'$, $q > 0$, $f$ continuous on
$[a, a']$, $C^{2q}$ on $(a, a')$ with $f^{(2q)} \le 0$ there, and every $\mathbf{b}$,
$$\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b} \le
\operatorname{Re}\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 10 lines. As
`Matrix.IsHermitian.re_star_dotProduct_lanczosFA_le_of_iteratedDeriv_nonneg`, with
`integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos`. -/
theorem
_root_.Matrix.IsHermitian.re_quadForm_cfc_le_re_star_dotProduct_lanczosFA_of_iteratedDeriv_nonpos
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q) f x ≤ 0) (b : n → 𝕜) :
    RCLike.re (quadForm (cfc f A) b) ≤ RCLike.re (star b ⬝ᵥ lanczosFA A f b q) := by
  sorry

/-! ### Gauss–Radau -/

/-- **The left Radau rule is a lower bound** for $f$ with nonnegative derivative of order
$2q + 1$: for $\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$),
$a < a'$, every $q$, $f$
continuous on $[a, a']$, $C^{2q+1}$ on $(a, a')$ with $f^{(2q+1)} \ge 0$ there, and every
$\mathbf{b}$,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, a, q) \le
\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 6 lines. `integral_radauQuadrature_le_integral_of_iteratedDeriv_nonneg` for
$\mu_{\mathbf{A},\mathbf{b}}$ (`ae_mem_Icc_spectralMeasure`) and `integral_spectralMeasure`.
No Hermitian hypothesis is needed: neither lemma uses one. -/
theorem integral_radauQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonneg {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ)
    (hf' : ContDiffOn ℝ (2 * q + 1 : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q + 1) f x) (b : n → 𝕜) :
    ∫ x, f x ∂radauQuadrature (spectralMeasure A b) a q ≤ RCLike.re (quadForm (cfc f A) b) := by
  sorry

/-- **The left Radau rule is an upper bound** for $f$ with nonpositive derivative of order
$2q + 1$: for $\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$),
$a < a'$, every $q$, $f$
continuous on $[a, a']$, $C^{2q+1}$ on $(a, a')$ with $f^{(2q+1)} \le 0$ there, and every
$\mathbf{b}$,
$$\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b} \le
\int f\,d\,\mathsf{radauQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, a, q)\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 6 lines. `integral_le_integral_radauQuadrature_of_iteratedDeriv_nonpos` and
`integral_spectralMeasure`. -/
theorem re_quadForm_cfc_le_integral_radauQuadrature_of_iteratedDeriv_nonpos {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ)
    (hf' : ContDiffOn ℝ (2 * q + 1 : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q + 1) f x ≤ 0) (b : n → 𝕜) :
    RCLike.re (quadForm (cfc f A) b) ≤ ∫ x, f x ∂radauQuadrature (spectralMeasure A b) a q := by
  sorry

/-- **The right Radau rule is an upper bound** for $f$ with nonnegative derivative of order
$2q + 1$: for $\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$),
$a < a'$, every $q$, $f$
continuous on $[a, a']$, $C^{2q+1}$ on $(a, a')$ with $f^{(2q+1)} \ge 0$ there, and every
$\mathbf{b}$,
$$\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b} \le
\int f\,d\,\mathsf{radauQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, a', q)\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 6 lines. `integral_le_integral_radauQuadrature_of_iteratedDeriv_nonneg` and
`integral_spectralMeasure`. -/
theorem re_quadForm_cfc_le_integral_radauQuadrature_of_iteratedDeriv_nonneg {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ)
    (hf' : ContDiffOn ℝ (2 * q + 1 : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q + 1) f x) (b : n → 𝕜) :
    RCLike.re (quadForm (cfc f A) b) ≤ ∫ x, f x ∂radauQuadrature (spectralMeasure A b) a' q := by
  sorry

/-- **The right Radau rule is a lower bound** for $f$ with nonpositive derivative of order
$2q + 1$: for $\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$),
$a < a'$, every $q$, $f$
continuous on $[a, a']$, $C^{2q+1}$ on $(a, a')$ with $f^{(2q+1)} \le 0$ there, and every
$\mathbf{b}$,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, a', q) \le
\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 6 lines. `integral_radauQuadrature_le_integral_of_iteratedDeriv_nonpos` and
`integral_spectralMeasure`. -/
theorem integral_radauQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonpos {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ)
    (hf' : ContDiffOn ℝ (2 * q + 1 : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q + 1) f x ≤ 0) (b : n → 𝕜) :
    ∫ x, f x ∂radauQuadrature (spectralMeasure A b) a' q ≤ RCLike.re (quadForm (cfc f A) b) := by
  sorry

/-! ### Gauss–Lobatto -/

/-- **The Lobatto rule is an upper bound** for $f$ with nonnegative derivative of order
$2q + 2$: for $\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$),
$a < a'$, every $q$, $f$
continuous on $[a, a']$, $C^{2q+2}$ on $(a, a')$ with $f^{(2q+2)} \ge 0$ there, and every
$\mathbf{b}$,
$$\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b} \le
\int f\,d\,\mathsf{lobattoQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, a, a', q)\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 6 lines. `integral_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg` and
`integral_spectralMeasure`. -/
theorem re_quadForm_cfc_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ)
    (hf' : ContDiffOn ℝ (2 * q + 2 : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q + 2) f x) (b : n → 𝕜) :
    RCLike.re (quadForm (cfc f A) b) ≤
      ∫ x, f x ∂lobattoQuadrature (spectralMeasure A b) a a' q := by
  sorry

/-- **The Lobatto rule is a lower bound** for $f$ with nonpositive derivative of order
$2q + 2$: for $\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$),
$a < a'$, every $q$, $f$
continuous on $[a, a']$, $C^{2q+2}$ on $(a, a')$ with $f^{(2q+2)} \le 0$ there, and every
$\mathbf{b}$,
$$\int f\,d\,\mathsf{lobattoQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, a, a', q) \le
\operatorname{Re}\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}\,.$$
[GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: S, about 6 lines. `integral_lobattoQuadrature_le_integral_of_iteratedDeriv_nonpos` and
`integral_spectralMeasure`. -/
theorem integral_lobattoQuadrature_le_re_quadForm_cfc_of_iteratedDeriv_nonpos {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (haa' : a < a') {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ)
    (hf' : ContDiffOn ℝ (2 * q + 2 : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q + 2) f x ≤ 0) (b : n → 𝕜) :
    ∫ x, f x ∂lobattoQuadrature (spectralMeasure A b) a a' q ≤
      RCLike.re (quadForm (cfc f A) b) := by
  sorry

end NLAlib
