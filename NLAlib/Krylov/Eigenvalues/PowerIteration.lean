/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import NLAlib.Matrix.Spectral.SpectralMeasure

/-!
# The power method and inverse iteration

The power method after $q$ multiplications estimates an eigenvalue $c$ of a Hermitian
$\mathbf{A}$ by the Rayleigh quotient $\rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b})$; inverse
iteration with shift $\sigma$ by
$\rho_{\mathbf{A}}((\mathbf{A} - \sigma\mathbf{I})^{-q}\mathbf{b})$.
There is no definition of an iterate: both are powers applied to the start. The start enters
only through the squared tangent of its angle with the eigenspace $E_c$, read off the spectral
measure, $\tan^2\angle(\mathbf{b}, E_c) =
\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$
(`NLAlib.spectralTangentSq`).

The gapped bounds are instances of the filter theorem
`Matrix.IsHermitian.abs_sub_rayleighQuotient_cfc_mulVec_le`, with the filters $x^q$ and
$(x - \sigma)^{-q}$. For positive semidefinite $\mathbf{A}$, Kuczyński and Woźniakowski's
gap-free step bounds $\lambda_0 - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b})$ by
$\lambda_0\log(1 + \tan^2)/(2q + 1)$, the input of the random-start power method.

## Main results

* `Matrix.IsHermitian.abs_sub_rayleighQuotient_pow_mulVec_le`: the gapped power method.
* `Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le`: the gap-free step.
* `Matrix.IsHermitian.abs_sub_rayleighQuotient_inv_pow_mulVec_le`: inverse iteration.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **The power method, gapped**: for Hermitian $\mathbf{A}$ with spectrum in
$[-r, r] \cup \{c\}$, $r < \lvert c\rvert$, and $\mathbf{b}$ with a component in the eigenspace
$E_c$ of $c$, after $q$ multiplications
$$\bigl\lvert c - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b})\bigr\rvert \le
(\lvert c\rvert + r)\Bigl(\frac{r}{\lvert c\rvert}\Bigr)^{2q}\tan^2\angle(\mathbf{b}, E_c)\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$ of the
spectral measure. [TrefethenBau1997, Theorem 27.1]; [GolubVanLoan2013, Theorem 8.2.1] (locators
from the quarry); there for a simple dominant eigenvalue and an eigenvector, here any
multiplicity.
Result: power-iteration -/
theorem _root_.Matrix.IsHermitian.abs_sub_rayleighQuotient_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {c r : ℝ} (hrc : r < |c|) (hs : spectrum ℝ A ⊆ Set.Icc (-r) r ∪ {c})
    (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) (q : ℕ) :
    |c - rayleighQuotient A (A ^ q *ᵥ b)| ≤
      (|c| + r) * (r / |c|) ^ (2 * q) * spectralTangentSq A b c := by
  sorry

/-- **Kuczyński–Woźniakowski, deterministic power step**: for positive semidefinite
$\mathbf{A}$ and $\mathbf{b}$ with a component in the top eigenspace $E_{\lambda_0}$ of
$\lambda_0 = \lambda_0(\mathbf{A})$, after $q$ multiplications
$$\lambda_0 - \rho_{\mathbf{A}}(\mathbf{A}^q\mathbf{b}) \le
\frac{\lambda_0\log(1 + \tan^2\angle(\mathbf{b}, E_{\lambda_0}))}{2q + 1}\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_{\lambda_0})$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{\lambda_0\})/
\mu_{\mathbf{A},\mathbf{b}}(\{\lambda_0\})$ of the spectral measure; no gap, every $q$ including
$0$. [KuczynskiWozniakowski1992, Theorem 4.1] (locator from the quarry, to check); there as a
relative error for a random start, here deterministic. -/
theorem _root_.Matrix.PosSemidef.eigenvalue_sub_rayleighQuotient_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {eigenvalue A 0})
    (q : ℕ) :
    eigenvalue A 0 - rayleighQuotient A (A ^ q *ᵥ b) ≤
      eigenvalue A 0 * Real.log (1 + spectralTangentSq A b (eigenvalue A 0)) / (2 * q + 1) := by
  sorry

/-- **Inverse iteration**: for Hermitian $\mathbf{A}$ with spectrum in $s \cup \{c\}$, a shift
$\sigma \ne c$ with $d \le \lvert x - \sigma\rvert$ for $x \in s$, $d > 0$,
$\lvert x - c\rvert \le D$ for $x \in s$, and $\mathbf{b}$ with a component in the eigenspace
$E_c$ of $c$, after $q$ steps
$$\bigl\lvert c - \rho_{\mathbf{A}}((\mathbf{A} - \sigma\mathbf{I})^{-q}\mathbf{b})\bigr\rvert
\le D\Bigl(\frac{\lvert c - \sigma\rvert}{d}\Bigr)^{2q}\tan^2\angle(\mathbf{b}, E_c)\,,$$
$\rho_{\mathbf{A}}$ the Rayleigh quotient and $\tan^2\angle(\mathbf{b}, E_c)$ the ratio
$\mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}\setminus\{c\})/\mu_{\mathbf{A},\mathbf{b}}(\{c\})$ of the
spectral measure. [TrefethenBau1997, Theorem 27.2] (locator from the quarry); there for a simple
eigenvalue and an eigenvector, here any multiplicity. -/
theorem _root_.Matrix.IsHermitian.abs_sub_rayleighQuotient_inv_pow_mulVec_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : Set ℝ} {c σ d D : ℝ} (hs : spectrum ℝ A ⊆ s ∪ {c})
    (hσc : σ ≠ c) (hd : 0 < d) (hds : ∀ x ∈ s, d ≤ |x - σ|)
    (hD : ∀ x ∈ s, |x - c| ≤ D) (b : n → 𝕜) (hb : 0 < (spectralMeasure A b).real {c}) (q : ℕ) :
    |c - rayleighQuotient A ((A - σ • (1 : Matrix n n 𝕜))⁻¹ ^ q *ᵥ b)| ≤
      D * (|c - σ| / d) ^ (2 * q) * spectralTangentSq A b c := by
  sorry

end NLAlib
