/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Chebyshev.EvenFilter
public import NLAlib.Polynomial.Chebyshev.Residual

/-!
# Ritz values

Bounds on the largest Ritz value $\theta_0 = \lambda_0(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})$
of a Krylov space $\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (that is, $q$ multiplications by
$\mathbf{A}$), $\mathbf{Q}$ any orthonormal basis of it, below the largest eigenvalue
$\lambda_0 = \lambda_0(\mathbf{A})$. The lower bound $\theta_0 \le \lambda_0$ is Poincaré
separation (`Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le`). The start enters only
through the squared tangent of its angle with the top eigenspace $E_{\lambda_0}$, read off the
spectral measure, $\tan^2\angle(\mathbf{b}, E_{\lambda_0}) =
\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ (`NLAlib.spectralTangentSq`); a repeated top
eigenvalue needs no extra work.

Three bounds: the gapped Kaniel–Paige–Saad bound, from the filter theorem
`Matrix.IsHermitian.abs_sub_rayleighQuotient_cfc_mulVec_le` with a reflected Chebyshev residual;
the gap-free bound $\varepsilon\lambda_0 + 4e^{-4q\sqrt{\varepsilon}}\lambda_0\tan^2$ for positive
semidefinite $\mathbf{A}$; and Kuczyński and Woźniakowski's gap-free squared-logarithmic bound,
from the even Chebyshev filter. The last two are incomparable: the first is better for a fixed
accuracy with a good start, the second needs no $\varepsilon$ and degrades only logarithmically
with a poor start, which is the random-start regime.

## Main results

* `Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le`: Kaniel–Paige–Saad.
* `Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add`: the gap-free
  bound.
* `Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`: the
  Kuczyński–Woźniakowski bound.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-- **Kaniel–Paige–Saad**: for Hermitian $\mathbf{A}$ whose eigenvalues other than
$\lambda_0 = \lambda_0(\mathbf{A})$ lie in $[a, c]$, $a < c < \lambda_0$, a vector $\mathbf{b}$
with a component in the top eigenspace $E_{\lambda_0}$, and the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (the largest eigenvalue of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for $\mathbf{Q}$ with orthonormal columns spanning
it),
$$\lambda_0 - \theta_0 \le 4(\lambda_0 - a)\tan^2\angle(\mathbf{b}, E_{\lambda_0})
\Bigl(\frac{\sqrt{\lambda_0 - a} - \sqrt{\lambda_0 - c}}{\sqrt{\lambda_0 - a} +
\sqrt{\lambda_0 - c}}\Bigr)^{2q}\,,$$
$\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure.
The proof gives the sharp factor $1/T_q\bigl(1 + 2(\lambda_0 - c)/(c - a)\bigr)^2$ in place of
$4(\cdot)^{2q}$; they differ by $(1 + \rho^{2q})^2 \le 4$ (rule B6). [Saad2011, Theorem 6.4] (the
case $i = 1$; locator from the quarry and PORT_KRYLOV §9, to verify); there with
$a = \lambda_{n}$, $c = \lambda_1$, an eigenvector of a simple eigenvalue and the Chebyshev form.
Result: kaniel-paige-saad -/
theorem _root_.Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a c : ℝ} (hac : a < c) (hc : c < eigenvalue A 0)
    (hs : spectrum ℝ A ⊆ Set.Icc a c ∪ {eigenvalue A 0}) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      4 * (eigenvalue A 0 - a) * spectralTangentSq A b (eigenvalue A 0) *
        ((√(eigenvalue A 0 - a) - √(eigenvalue A 0 - c)) /
          (√(eigenvalue A 0 - a) + √(eigenvalue A 0 - c))) ^ (2 * q) := by
  sorry

/-- **The gap-free Ritz-value bound**: for positive semidefinite $\mathbf{A}$,
$0 < \varepsilon < 1$, a vector $\mathbf{b}$ with a component in the top eigenspace
$E_{\lambda_0}$ of $\lambda_0 = \lambda_0(\mathbf{A})$, and the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (the largest eigenvalue of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for $\mathbf{Q}$ with orthonormal columns spanning
it),
$$\lambda_0 - \theta_0 \le \varepsilon\lambda_0 +
4e^{-4q\sqrt{\varepsilon}}\lambda_0\tan^2\angle(\mathbf{b}, E_{\lambda_0})\,,$$
$\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure.
Sharp form: $1/T_q((1 + \varepsilon)/(1 - \varepsilon))^2$ in place of $4e^{-4q\sqrt\varepsilon}$
(`exp_mul_sqrt_div_two_le_eval_T_real`); the factor lost is
$e^{4q(\operatorname{artanh}\sqrt\varepsilon - \sqrt\varepsilon)}(1 + \rho^{2q})^2$ with
$\rho = (1 - \sqrt\varepsilon)/(1 + \sqrt\varepsilon)$, which is unbounded in $q$ at fixed
$\varepsilon$ (its exponent is about $4q\varepsilon^{3/2}/3$ for small $\varepsilon$). Incomparable
with `Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq`: this bound is
better for a fixed target accuracy with a good start, that one needs no $\varepsilon$ and degrades
only logarithmically with a poor start. [MuscoMusco2015, Theorem 1] (single-vector case; locator
to check; the library cites this paper as Theorem 10 (proof), Lemmas 2, 5, 9 and Algorithm 2, all
for the block method); there with $(1 + \sqrt{2\varepsilon/(1-\varepsilon)})^{-2q}$, weaker for
small $\varepsilon$ and stronger as $\varepsilon \to 1$; constants composed here.
Result: ritz-value-gap-free -/
theorem _root_.Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {ε : ℝ} (hε₀ : 0 < ε) (hε₁ : ε < 1) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      ε * eigenvalue A 0 +
        4 * Real.exp (-4 * q * √ε) * eigenvalue A 0 * spectralTangentSq A b (eigenvalue A 0) := by
  sorry

/-- **Kuczyński–Woźniakowski, deterministic Lanczos step**: for positive semidefinite
$\mathbf{A}$, a vector $\mathbf{b}$ with a component in the top eigenspace $E_{\lambda_0}$ of
$\lambda_0 = \lambda_0(\mathbf{A})$, $q \ge 1$, and the largest Ritz value $\theta_0$ of
$\mathcal{K}_{q+1}(\mathbf{A}, \mathbf{b})$ (the largest eigenvalue of
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ for $\mathbf{Q}$ with orthonormal columns spanning
it),
$$\lambda_0 - \theta_0 \le \frac{4\lambda_0}{q^2}\Bigl(1 +
\frac{\log(1 + \tan^2\angle(\mathbf{b}, E_{\lambda_0}))}{\log 2}\Bigr)^2\,,$$
$\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure: a squared logarithmic
dependence on the start and no gap. Incomparable with
`Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_add`: this bound needs no
$\varepsilon$ and degrades only logarithmically with a poor start, that one is better for a fixed
target accuracy with a good start. [KuczynskiWozniakowski1992, Theorem 4.2] (locator from the
quarry, to check); there as a relative error for a random start, here deterministic.
Result: ritz-value-gap-free -/
theorem _root_.Matrix.PosSemidef.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le_div_sq
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {b : n → 𝕜}
    (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0}) {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {q : ℕ} (hq : 1 ≤ q)
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b (q + 1)) :
    eigenvalue A 0 - eigenvalue (Qᴴ * A * Q) 0 ≤
      4 * eigenvalue A 0 *
        (1 + Real.log (1 + spectralTangentSq A b (eigenvalue A 0)) / Real.log 2) ^ 2 / q ^ 2 := by
  sorry

end NLAlib
