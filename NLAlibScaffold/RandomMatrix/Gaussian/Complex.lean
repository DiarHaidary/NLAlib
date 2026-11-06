/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.Matrix.Perturbation.Pseudospectrum

/-!
# Sharper tails for complex Gaussian matrices (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/RandomMatrix/Gaussian/Complex.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I5 and I6): the upper tail
of $\lvert z \rvert^2$, a norm tail with the full Gaussian exponent, and a smallest singular value
tail linear in the size, within a factor $e$ of Edelman's exact law [Edelman1988].

## Main results

* `NLAlib.measureReal_le_normSq_le_of_hasLaw_complexGaussian` (CG7): $\mathbb{P}[s \le
  \lvert z\rvert^2] \le e^{-s}$.
* `NLAlib.measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix` (CG4'): tail
  $e^{-t^2}$ above $\sqrt2(\sqrt m + \sqrt n)$.
* `NLAlib.measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix` (CG6'):
  $\mathbb{P}[\sigma_{\min}(\mathbf{G}) \le x] \le e\,r x^2$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n]

/-- **Exponential upper tail of a standard complex Gaussian** (CG7): for $z \sim
\mathcal{N}_{\mathbb C}(0, 1)$ and every real $s$, $\mathbb{P}[s \le \lvert z \rvert^2] \le
e^{-s}$ ($\lvert z\rvert^2$ is exponential of mean $1$).
Proof: by `NLAlib.complexGaussian_eq_map_stdGaussian`, $2\lvert z \rvert^2$ is
$\chi^2_2$ (`NLAlib.hasLaw_norm_sq_of_hasLaw_gaussianVector` on the realification, or a direct
computation of the product of two `gaussianReal 0 2⁻¹`); the $\chi^2_2$ upper tail is
$e^{-x/2}$ in closed form; for $s < 0$ the bound is at least $1$. M, about 50 lines. -/
theorem measureReal_le_normSq_le_of_hasLaw_complexGaussian {z : Ω → ℂ}
    (hz : HasLaw z complexGaussian μ) (s : ℝ) :
    μ.real {ω | s ≤ ‖z ω‖ ^ 2} ≤ Real.exp (-s) := by
  sorry

/-- **Norm tail of a complex Gaussian matrix with the full exponent** (CG4'): for
$\mathbf{G}$ an $m \times n$ standard complex Gaussian matrix and $t \ge 0$,
$\mathbb{P}[\sqrt2(\sqrt m + \sqrt n) + t \le \|\mathbf{G}\|_2] \le e^{-t^2}$. Compared with
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`, the deviation $t$ is not
multiplied by $\sqrt2$ and there is no union bound over the two parts. The sharp mean
$\sqrt m + \sqrt n$ is not claimed (design note, item I6).
Proof: by `NLAlib.complexGaussianMatrix_eq_map_gaussianMatrix`, $\mathbf{G} = (\mathbf{G}_1 +
i\mathbf{G}_2)/\sqrt2$ with $(\mathbf{G}_1; \mathbf{G}_2)$ a real $2m \times n$ Gaussian matrix;
$X \mapsto \|(X_1 + iX_2)/\sqrt2\|_2$ is $2^{-1/2}$-Lipschitz for the Frobenius norm, so
`NLAlib.measureReal_ge_integral_add_le_of_hasLaw_gaussianMatrix` gives the tail $e^{-t^2}$ above the
mean; the mean is at most $\sqrt2(\sqrt m + \sqrt n)$ by the triangle inequality and
`NLAlib.integral_specNorm_le_of_hasLaw_gaussianMatrix` on each part. M, about 80 lines. -/
theorem measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ)) + t ≤ specNorm (G ω)} ≤
      Real.exp (-t ^ 2) := by
  sorry

/-- **Smallest singular value of a square complex Gaussian matrix, linear in the size** (CG6'):
for $\mathbf{G}$ an $r \times r$ standard complex Gaussian matrix and $x \ge 0$,
$\mathbb{P}[\sigma_{\min}(\mathbf{G}) \le x] \le e\,r x^2$. Edelman's exact law
$1 - e^{-r x^2}$ [Edelman1988] is smaller by the factor $e$; the elementary
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix` has $r^2x^2$. The probe
argument of [SankarSpielmanTeng2006, Lemma 3.2], complex version.
Proof: let $\mathbf{g}$ be an independent standard complex Gaussian vector (work on the product
of the law of $\mathbf{G}$ with `NLAlib.complexGaussianVector`, as in the helper of CG6). If
$\sigma_{\min}(\mathbf{G}) \le x$ then $\|\mathbf{G}^{-1}\|_2 \ge 1/x$
(`NLAlib.singularValues_le_iff_mem_spectrum_or_le_specNorm_inv`, invertibility a.s. from
CG6 at $x = 0$), and $\|\mathbf{G}^{-1}\mathbf{g}\| \ge \|\mathbf{G}^{-1}\|\,\lvert
\mathbf{b}^{\mathsf H}\mathbf{g}\rvert$ for a top right singular vector $\mathbf{b}$ of
$\mathbf{G}^{-1}$; given $\mathbf{G}$, $\mathbf{b}^{\mathsf H}\mathbf{g}$ is standard complex
Gaussian (`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`), so
$\mathbb{P}[\lvert\mathbf{b}^{\mathsf H}\mathbf{g}\rvert^2 \ge 1] = e^{-1}$ (CG7, and its
equality version). Conversely, given $\mathbf{g} \ne 0$, a unitary $\mathbf{Q}$ with
$\mathbf{Q}\mathbf{g} = \|\mathbf{g}\|\mathbf{e}_1$ gives $\|\mathbf{G}^{-1}\mathbf{g}\| =
\|\mathbf{g}\|\,\|(\mathbf{Q}\mathbf{G})^{-1}\mathbf{e}_1\|$ with $\mathbf{Q}\mathbf{G}$ again
standard, and $\|\mathbf{H}^{-1}\mathbf{e}_1\| = 1/\operatorname{dist}(\text{row}_1,
\text{span of the other rows})$, whose square is at least $1/T$ with probability at most $1/T$
(the CG5 step of CG6, on rows); averaging over $\mathbf{g}$ gives
$\mathbb{P}[\|\mathbf{G}^{-1}\mathbf{g}\|^2 \ge T] \le \mathbb{E}\|\mathbf{g}\|^2/T = r/T$. With
$T = 1/x^2$: $e^{-1}\,\mathbb{P}[\sigma_{\min} \le x] \le r x^2$. L, about 350 lines. -/
theorem measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix
    {r : Type*} [Fintype r] {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ)
    {k : ℕ} (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ Real.exp 1 * (Fintype.card r : ℝ) * x ^ 2 := by
  sorry

end NLAlib
