/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.Quadrature
public import NLAlibScaffold.Polynomial.Orthogonal.RadauLobatto

/-!
# Golub–Welsch for the Radau rule: the theorems of stage KS8

Statements for `NLAlib/Krylov/Functions/Quadrature.lean` whose proofs are deferred
(`docs/design/Polynomial-QuadratureRemainder.md`, J4, J5). The Radau rule of a measure with more
than $k$ support points is the spectral measure of its Radau Jacobi matrix at
$\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$, as the Gauss rule is that of the Jacobi matrix
(`spectralMeasure_jacobiMatrix`). For a spectral measure $\mu_{\mathbf{A},\mathbf{b}}$ the
Radau Jacobi matrix is the Lanczos tridiagonal with its last diagonal entry modified, and the
Radau quadrature is $\|\mathbf{b}\|^2 f(\tilde{\mathbf{J}})_{0,0}$, the form Golub and Meurant
compute.

## Main results

* `NLAlib.spectralMeasure_radauJacobiMatrix`: Golub–Welsch for the Radau rule.
* `Matrix.IsHermitian.integral_radauQuadrature_spectralMeasure`: the Radau quadrature of
  $\mathbf{b}^{\mathsf{H}}f(\mathbf{A})\mathbf{b}$ from the modified tridiagonal.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **Golub–Welsch for the Radau rule**: for a finite measure $\mu$ supported in $[a, b]$,
positive definite up to degree $k + 1$, and $c \in \{a, b\}$, the Radau rule of $\mu$ with
prescribed node $c$ and $k$ free nodes is the spectral measure of the Radau Jacobi matrix
$\tilde{\mathbf{J}}$ of order $k + 1$ and $\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$: its nodes are
the eigenvalues of $\tilde{\mathbf{J}}$ (one of them $c$) and its weights $\mu(\mathbb{R})$ times
the squared first eigenvector components. [Golub1973, §7]; [GolubMeurant2010, Ch. 6] (locators
to check).
Proof: M, about 45 lines. Let $\nu$ be the spectral measure. Moments: for $\deg p \le 2k$,
$\int p\,d\nu = \mu(\mathbb{R})\,p(\tilde{\mathbf{J}})_{0,0}$
(`Matrix.IsHermitian.integral_eval_spectralMeasure`, `quadForm` at a multiple of
`Pi.single 0 1`, `isHermitian_jacobiMatrix` for the symmetry of $\tilde{\mathbf{J}}$), which by
`radauJacobiMatrix_pow_apply_zero_zero` (through `Polynomial.aeval_eq_sum_range`) is
$\mu(\mathbb{R})\,p(\mathbf{J}_{k+1})_{0,0} = \int p\,d\,\mathsf{gaussQuadrature}(\mu, k + 1)$
(`spectralMeasure_jacobiMatrix`) $= \int p\,d\mu$ (`matchesMoments_gaussQuadrature`,
$2k < 2k + 2$). Support: $\nu$ is carried by the spectrum of $\tilde{\mathbf{J}}$
(`spectralMeasure_compl_spectrum_eq_zero`), a set of at most $k + 1$ points containing $c$
(`IsMomentPosDef.mem_spectrum_radauJacobiMatrix`, `Matrix.finite_real_spectrum`,
`card_spectrum_le`-style bound by the size), so take $s$ the spectrum without $c$; then
`MatchesMoments.eq_radauQuadrature`.
Result: gauss-radau-jacobi-matrix -/
theorem spectralMeasure_radauJacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a b c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) {k : ℕ} (h : IsMomentPosDef μ (k + 1)) :
    spectralMeasure (radauJacobiMatrix μ c k) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
      radauQuadrature μ c k := by
  sorry

/-- **The Radau quadrature of a quadratic form from the modified tridiagonal**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $c \in \{a, a'\}$, $q + 1$ at most the grade of
$\mathbf{b}$, and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu_{\mathbf{A},\mathbf{b}}, c, q) =
\|\mathbf{b}\|^2 f(\tilde{\mathbf{J}})_{0,0}\,,$$
$\tilde{\mathbf{J}}$ the Radau Jacobi matrix of order $q + 1$ of $\mu_{\mathbf{A},\mathbf{b}}$:
the Lanczos tridiagonal of order $q + 1$ (`Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix`)
with its last diagonal entry replaced. [GolubMeurant2010, Ch. 6, Ch. 7] (locators to check).
Proof: M, about 25 lines. `spectralMeasure_radauJacobiMatrix` (definiteness from
`Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff`, support from
`ae_mem_Icc_spectralMeasure`), `integral_spectralMeasure` for the real matrix
$\tilde{\mathbf{J}}$, `quadForm` at $\sqrt{\beta_0}\,\mathbf{e}_0$ is $\beta_0$ times the
$(0, 0)$ entry (`Matrix.mulVec_single`, `dotProduct_single`), and
$\beta_0 = \mu_{\mathbf{A},\mathbf{b}}(\mathbb{R}) = \|\mathbf{b}\|^2$
(`Matrix.IsHermitian.spectralMeasure_real_univ`, `Real.sq_sqrt`). -/
theorem _root_.Matrix.IsHermitian.integral_radauQuadrature_spectralMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' c : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (hc : c = a ∨ c = a')
    (b : n → 𝕜) {q : ℕ} (hq : q + 1 ≤ krylovGrade A b) (f : ℝ → ℝ) :
    ∫ x, f x ∂radauQuadrature (spectralMeasure A b) c q =
      ‖WithLp.toLp 2 b‖ ^ 2 * cfc f (radauJacobiMatrix (spectralMeasure A b) c q) 0 0 := by
  sorry

end NLAlib
