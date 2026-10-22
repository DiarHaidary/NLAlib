/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Krylov.Functions.LanczosFA
public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Gauss

/-!
# Lanczos quadrature

The quadratic form $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ of a Hermitian $\mathbf{A}$
is the integral of $f$ against the spectral measure $\mu_{\mathbf{A},\mathbf{b}}$. Its Lanczos
(Gauss) quadrature after $q$ steps is
$\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)$, the integral of $f$
against the Lanczos rule
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) =
\mu_{\mathbf{P}\mathbf{A}\mathbf{P},\,\mathbf{P}\mathbf{b}}$,
$\mathbf{P}$ the orthogonal projector onto $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$. For any
orthonormal basis $\mathbf{Q}$ of the Krylov space the rule is the spectral measure of
$(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}, \mathbf{Q}^{\mathsf{H}}\mathbf{b})$: its nodes are
the Ritz values. From the Lanczos recurrence it is
$\|\mathbf{b}\|^2$ times the spectral measure of $(\mathbf{T}, \mathbf{e}_0)$, and in an
eigenbasis of $\mathbf{T}$ its weights are the squared first eigenvector entries (Golub–Welsch).

The rule is exact through degree $2q - 1$: it matches the first $2q$ moments of
$\mu_{\mathbf{A},\mathbf{b}}$. If $f$ is within $\varepsilon$ of a polynomial of degree less
than $2q$ on an interval containing the spectrum, the quadrature error is at most
$2\varepsilon\|\mathbf{b}\|^2$; explicit rates follow for analytic and for Lipschitz $f$.
Below the grade the Ritz values are distinct, their nodal polynomial is the degree-$q$
orthogonal polynomial of $\mu_{\mathbf{A},\mathbf{b}}$, the Lanczos rule is the Gauss rule of
$\mu_{\mathbf{A},\mathbf{b}}$, and every Ritz value carries positive weight. None of this needs
tridiagonal theory: the compression lemmas of `NLAlib.Krylov.Basic.Compression` carry it.

## Main definitions

* `NLAlib.lanczosQuadrature`: the Lanczos rule as a measure.

## Main results

* `NLAlib.integral_lanczosQuadrature`: its integrals are the Lanczos quadratures.
* `NLAlib.HasOrthonormalCols.lanczosQuadrature_eq`,
  `Matrix.IsHermitian.lanczosQuadrature_succ_eq`,
  `Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`: the frame, tridiagonal and Golub–Welsch
  forms.
* `Matrix.IsHermitian.star_dotProduct_lanczosFA_eval`: exactness through degree $2q - 1$.
* `Matrix.IsHermitian.matchesMoments_lanczosQuadrature`: the rule matches $2q$ moments.
* `Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn`:
  the $2\varepsilon\|\mathbf{b}\|^2$ bound, with its analytic and Lipschitz rates.
* `NLAlib.HasOrthonormalCols.lanczosQuadrature_eq_interpolatoryQuadrature`: the Lanczos rule is
  the Gauss rule of the spectral measure.
* `NLAlib.HasOrthonormalCols.lanczosQuadrature_real_singleton_pos`: positive weights below
  the grade.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder MatrixOrder NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-! ### The Lanczos rule -/

/-- The **Lanczos (Gauss) quadrature rule** of $q$ steps from $\mathbf{b}$:
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) := \mu_{\mathbf{P}\mathbf{A}\mathbf{P},
\mathbf{P}\mathbf{b}}$ with $\mathbf{P} = \mathbf{P}_{\mathbf{K}_q(\mathbf{A},\mathbf{b})}$; for
any orthonormal basis $\mathbf{Q}$ of the Krylov space it is the spectral measure of
$(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}, \mathbf{Q}^{\mathsf{H}}\mathbf{b})$
(`HasOrthonormalCols.lanczosQuadrature_eq`): atoms at the Ritz values. Junk: $0$ at $q = 0$ and
when the compression is not Hermitian. [GolubMeurant2010, Theorem 6.6] (locator from the
quarry). -/
noncomputable def lanczosQuadrature (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : Measure ℝ :=
  spectralMeasure (rangeProjector (krylovMatrix A b q) * A * rangeProjector (krylovMatrix A b q))
    (rangeProjector (krylovMatrix A b q) *ᵥ b)

/-- The Lanczos rule is a finite measure. -/
instance isFiniteMeasure_lanczosQuadrature (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    IsFiniteMeasure (lanczosQuadrature A b q) := by
  unfold lanczosQuadrature
  infer_instance

/-- The Lanczos rule integrates to the Lanczos quadrature: for every square $\mathbf{A}$,
every $f : \mathbb{R} \to \mathbb{R}$, $\mathbf{b}$ and $q$,
$$\int f\,d\,\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) =
\operatorname{Re}\,\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\,;$$
both sides are built from the same compression. -/
theorem integral_lanczosQuadrature (A : Matrix n n 𝕜) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ∫ x, f x ∂lanczosQuadrature A b q = RCLike.re (star b ⬝ᵥ lanczosFA A f b q) := by
  sorry

/-- The Lanczos rule in any orthonormal basis of the Krylov space: for Hermitian
$\mathbf{A}$ and $\mathbf{Q}$ with orthonormal columns spanning
$\mathcal{K}_q(\mathbf{A}, \mathbf{b})$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q) =
\mu_{\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q},\,\mathbf{Q}^{\mathsf{H}}\mathbf{b}}$; its atoms
are the Ritz values. -/
theorem HasOrthonormalCols.lanczosQuadrature_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    lanczosQuadrature A b q = spectralMeasure (Qᴴ * A * Q) (Qᴴ *ᵥ b) := by
  sorry

/-- The Lanczos rule from the Lanczos recurrence: for Hermitian $\mathbf{A}$ and every $q$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q + 1) =
\mu_{\mathbf{T},\,\|\mathbf{b}\|\mathbf{e}_0}$, with $\mathbf{T}$ the tridiagonal matrix of
$q + 1$ steps of the recurrence (`lanczosTridiagonal`). Past the grade the recurrence pads
$\mathbf{T}$ with zeros, and the statement still holds. -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_succ_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosQuadrature A b (q + 1) =
      spectralMeasure (lanczosTridiagonal A b (q + 1))
        ((‖WithLp.toLp 2 b‖ : 𝕜) • Pi.single 0 1) := by
  sorry

/-- **The Lanczos quadrature from the tridiagonal matrix**: for Hermitian $\mathbf{A}$, every
$f : \mathbb{R} \to \mathbb{R}$ and every $q$,
$$\int f\,d\,\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q + 1) =
\|\mathbf{b}\|^2\operatorname{Re}\,\mathbf{e}_0^{\mathsf{H}}f(\mathbf{T})\mathbf{e}_0\,,$$
with $\mathbf{T}$ the tridiagonal matrix of $q + 1$ steps of the Lanczos recurrence.
[GolubMeurant2010, Theorem 6.6] (locator from the quarry). -/
theorem _root_.Matrix.IsHermitian.integral_lanczosQuadrature_succ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ∫ x, f x ∂lanczosQuadrature A b (q + 1) =
      ‖WithLp.toLp 2 b‖ ^ 2 * RCLike.re (cfc f (lanczosTridiagonal A b (q + 1)) 0 0) := by
  sorry

/-- **Golub–Welsch**: for Hermitian $\mathbf{A}$, every $q$, and a unitary diagonalisation
$\mathbf{T} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ of the
tridiagonal matrix of $q + 1$ steps of the Lanczos recurrence,
$$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q + 1) =
\sum_i \|\mathbf{b}\|^2\lvert\mathbf{U}_{0,i}\rvert^2\,\delta_{\mathbf{d}_i}\,:$$
the nodes are the eigenvalues of $\mathbf{T}$, the weights the squared first entries of its
eigenvectors. [GolubMeurant2010, Ch. 6] (locator from the quarry).
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) {U : Matrix (Fin (q + 1)) (Fin (q + 1)) 𝕜}
    (hU : HasOrthonormalCols U) {d : Fin (q + 1) → ℝ}
    (hT : lanczosTridiagonal A b (q + 1) = U * Matrix.diagonal (fun i => ((d i : ℝ) : 𝕜)) * Uᴴ) :
    lanczosQuadrature A b (q + 1) =
      ∑ i, ENNReal.ofReal (‖WithLp.toLp 2 b‖ ^ 2 * ‖U 0 i‖ ^ 2) • Measure.dirac (d i) := by
  sorry

/-- The Lanczos rule lives in every interval containing the spectrum: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, almost every point of
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)$ lies in $[a, a']$ (the Ritz values do). -/
theorem _root_.Matrix.IsHermitian.ae_mem_Icc_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) (q : ℕ) :
    ∀ᵐ x ∂lanczosQuadrature A b q, x ∈ Set.Icc a a' := by
  sorry

/-- The mass of the Lanczos rule: for Hermitian $\mathbf{A}$ and $q > 0$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)(\mathbb{R}) = \|\mathbf{b}\|^2$, the mass
of $\mu_{\mathbf{A},\mathbf{b}}$. -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} (hq : 0 < q) :
    (lanczosQuadrature A b q).real Set.univ = ‖WithLp.toLp 2 b‖ ^ 2 := by
  sorry

/-! ### Exactness -/

/-- **Gauss (Lanczos) quadrature is exact through degree $2q - 1$**: for Hermitian
$\mathbf{A}$ and a real polynomial $p$ with $\deg p < 2q$,
$\mathbf{b}^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, p, \mathbf{b}, q) =
\mathbf{b}^{\mathsf{H}}p(\mathbf{A})\mathbf{b}$; Lanczos-FA itself is exact only through degree
$q - 1$. [GolubMeurant2010, Theorem 6.6] (locator from the quarry).
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_lanczosFA_eval {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) :
    star b ⬝ᵥ lanczosFA A (fun x => p.eval x) b q = quadForm (aeval A p) b := by
  sorry

/-- **Lanczos quadrature matches the first $2q$ moments of the spectral measure**: for
Hermitian $\mathbf{A}$, every $\mathbf{b}$ and every $q$,
$\int p\,d\mu_{\mathbf{A},\mathbf{b}} = \int p\,d\,\mathsf{lanczosQuadrature}(\mathbf{A},
\mathbf{b}, q)$ for every real polynomial $p$ of degree less than $2q$.
[GolubMeurant2010, Theorem 6.6]. Chen, Trogdon and Ubaru (2022) start their
spectrum-approximation bounds from this form; locator to check.
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.matchesMoments_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    MatchesMoments (spectralMeasure A b) (lanczosQuadrature A b q) (2 * q) := by
  sorry

/-! ### Error bounds -/

/-- **The Lanczos quadrature error from uniform approximation**: for Hermitian $\mathbf{A}$
with spectrum in $[a, a']$, if a real polynomial $p$ of degree less than $2q$ is within
$\varepsilon$ of $f$ on $[a, a']$, then
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q)\bigr)\bigr\rvert \le
2\varepsilon\|\mathbf{b}\|^2\,:$$
the quadrature is exact on $p$, and $f - p$ is at most $\varepsilon$ on the spectrum and on
the Ritz values. [GolubMeurant2010, Theorem 6.6] (locator from the quarry), the exactness it
rests on. -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) (b : n → 𝕜) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b q)‖ ≤ 2 * ε * ‖WithLp.toLp 2 b‖ ^ 2 := by
  sorry

/-- **Lanczos quadrature for analytic functions**: let $\mathbf{A}$ be Hermitian with spectrum
in $[a, a']$, $a < a'$, and let $f$ on $[a, a']$, pulled back to $[-1, 1]$ by
$t \mapsto ((a' - a)t + a' + a)/2$, extend to a function holomorphic and bounded by $M$ on the
open Bernstein ellipse $E_\rho$, $\rho > 1$. Then $q + 1$ steps give
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\bigr)\bigr\rvert \le
\frac{4M}{\rho^{2q + 1}(\rho - 1)}\|\mathbf{b}\|^2\,,$$
twice the rate of Lanczos-FA in the exponent, from the Chebyshev truncation of degree
$2q + 1$. [Trefethen2019, Theorem 8.2] (locator from the quarry), the approximation rate;
constants composed here.
Result: lanczos-gauss-quadrature -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * ‖WithLp.toLp 2 b‖ ^ 2 := by
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn (𝕜 := ℝ)
    (f := f) haa hρ hFd hM (fun t ht => by
      rw [← hExt ht]
      exact RCLike.toComplex_ofReal (𝕜 := ℝ) _) (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  have h := hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b
  refine h.trans_eq ?_
  ring

/-- **Lanczos quadrature for Lipschitz functions**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a']$, $a < a'$, and $f$ $L$-Lipschitz on $[a, a']$, $q + 1$ steps
give <!-- value jacksonApproximationConstant -->
$$\bigl\lvert\mathbf{b}^{\mathsf{H}}\bigl(f(\mathbf{A})\mathbf{b} -
\mathsf{lanczosFA}(\mathbf{A}, f, \mathbf{b}, q + 1)\bigr)\bigr\rvert \le
\frac{\pi L(a' - a)}{2q + 3}\|\mathbf{b}\|^2\,,$$
from Jackson's theorem on $[a, a']$ in degree $2q + 1$ (the constant is
`jacksonApproximationConstant`). The approximation step is
[ChenTrogdonUbaru2022, Appendix C, Theorem 38]; constants composed here.
Result: lanczos-gauss-quadrature -/
theorem
_root_.Matrix.IsHermitian.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (b : n → 𝕜) (q : ℕ) :
    ‖star b ⬝ᵥ (cfc f A *ᵥ b - lanczosFA A f b (q + 1))‖ ≤
      jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) * ‖WithLp.toLp 2 b‖ ^ 2 := by
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) haa hf (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  have h := hA.norm_star_dotProduct_cfc_mulVec_sub_lanczosFA_le_of_isUniformApproxOn hs hp' hε b
  refine h.trans_eq ?_
  push_cast
  field_simp
  ring

/-! ### The orthogonal-polynomial reading -/

/-- **Distinct Ritz values below the grade**: for Hermitian $\mathbf{A}$, $\mathbf{Q}$ with
orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and $q$ at most the grade
of $\mathbf{b}$, the compression $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ has exactly $q$
distinct eigenvalues: a nodal polynomial of fewer Ritz values would make $\pi(\mathbf{A})\mathbf{b}$
a vector of $\mathcal{K}_q$ orthogonal to $\mathcal{K}_q$, hence zero, against the grade. -/
theorem HasOrthonormalCols.card_spectrum_conjTranspose_mul_mul_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b) :
    Nat.card (spectrum ℝ (Qᴴ * A * Q)) = q := by
  sorry

/-- **The Ritz polynomial is the orthogonal polynomial**: for Hermitian $\mathbf{A}$ and
$\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, the
nodal polynomial $\pi(z) = \prod_{\theta\in s}(z - \theta)$ of the set $s$ of distinct Ritz values
(the eigenvalues of $\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$) is orthogonal in
$L^2(\mu_{\mathbf{A},\mathbf{b}})$ to every real polynomial of degree less than $q$.
[GolubMeurant2010, §4]; there through the Lanczos polynomials. -/
theorem HasOrthonormalCols.isOrthogonalPolynomial_nodal {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) {s : Finset ℝ}
    (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    IsOrthogonalPolynomial (spectralMeasure A b) q (Lagrange.nodal s id) := by
  sorry

/-- **Lanczos quadrature is the Gauss rule of the spectral measure**: for Hermitian
$\mathbf{A}$, $\mathbf{Q}$ with orthonormal columns spanning
$\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ and $q$ at most the grade of $\mathbf{b}$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)$ is the interpolatory rule of
$\mu_{\mathbf{A},\mathbf{b}}$ at the set $s$ of the $q$ distinct Ritz values (the eigenvalues of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$).
[GolubMeurant2010, Theorem 6.6] (locator from the quarry).
Result: lanczos-gauss-quadrature -/
theorem HasOrthonormalCols.lanczosQuadrature_eq_interpolatoryQuadrature {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    lanczosQuadrature A b q = interpolatoryQuadrature (spectralMeasure A b) s := by
  sorry

/-- **Every Ritz value below the grade carries positive weight**: for Hermitian $\mathbf{A}$,
$\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, $q$ at
most the grade of $\mathbf{b}$ and a Ritz value $x$ (an eigenvalue of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$),
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)(\{x\}) > 0$; so the support of the
Lanczos rule is exactly the set of Ritz values. The weight is
$\int\ell_x\,d\mu_{\mathbf{A},\mathbf{b}} = \|\ell_x(\mathbf{A})\mathbf{b}\|^2$, $\ell_x$ the
Lagrange basis polynomial of $x$ at the Ritz values, and $\ell_x(\mathbf{A})\mathbf{b} \ne
\mathbf{0}$ because $\ell_x$ is a nonzero polynomial of degree less than the grade. -/
theorem HasOrthonormalCols.lanczosQuadrature_real_singleton_pos {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {x : ℝ} (hx : x ∈ spectrum ℝ (Qᴴ * A * Q)) :
    0 < (lanczosQuadrature A b q).real {x} := by
  sorry

end NLAlib
