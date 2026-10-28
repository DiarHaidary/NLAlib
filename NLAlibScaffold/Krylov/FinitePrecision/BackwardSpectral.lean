/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.Backward
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Spectral.CourantFischer

/-!
# Spectral consequences of the backward model

From the backward model $\tilde{\mathbf{H}}$ of a run `L : NLAlib.LanczosRun n k`
(`NLAlib.LanczosRun.backwardH`), with $\delta = 2000k^4\varepsilon\|\mathbf{H}\|_2$:

* every eigenvalue of $\tilde{\mathbf{H}}$ is within $\delta$ of an eigenvalue of $\mathbf{H}$;
* a computed Ritz value $\theta$ with unit eigenvector $\mathbf{y}$ of $\mathbf{T}_k$ is within
  $\beta_k\lvert y_{k-1}\rvert + \delta$ of an eigenvalue of $\mathbf{H}$ (Paige's localization of
  stabilised Ritz values);
* every computed Ritz value lies in $[\lambda_{\min}(\mathbf{H}) - \delta,
  \lambda_{\max}(\mathbf{H}) + \delta]$ (containment);
* for every $1$-Lipschitz $f$, $\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1
  - \tilde{\mathbf{v}}^{\mathsf{T}}f(\tilde{\mathbf{H}})\tilde{\mathbf{v}}\rvert \le \delta$: the
  spectral measures of $(\mathbf{H}, \bar{\mathbf{v}}_1)$ and $(\tilde{\mathbf{H}},
  \tilde{\mathbf{v}})$ are $\delta$-close in the Wasserstein distance.

The last rests on `NLAlib.frobNorm_cfc_sub_cfc_le` (Kittaneh): a $1$-Lipschitz function is
$1$-Lipschitz in the Frobenius norm on symmetric matrices.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `rem:wasserstein`, `thm:stabilized`, `thm:containment`;
[Paige1980, Lemma 3.1, Theorem 3.1, (3.48)] for the classical forms.

## Main results

* `NLAlib.LanczosRun.exists_abs_eigenvalue_backwardH_sub_eigenvalue_le`: localization of the
  model's spectrum.
* `NLAlib.LanczosRun.exists_abs_sub_eigenvalue_le_of_mulVec_eq_smul`: stabilised Ritz values.
* `NLAlib.LanczosRun.eigenvalue_last_sub_le_of_mulVec_eq_smul`,
  `NLAlib.LanczosRun.le_eigenvalue_zero_add_of_mulVec_eq_smul`: containment.
* `NLAlib.frobNorm_cfc_sub_cfc_le`: Lipschitz functions in the Frobenius norm.
* `NLAlib.LanczosRun.abs_dotProduct_cfc_mulVec_sub_le`: closeness of the spectral measures.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- **A $1$-Lipschitz function is $1$-Lipschitz in the Frobenius norm on symmetric matrices**:
for real symmetric $\mathbf{A}$, $\mathbf{B}$ and $f$ with $\lvert f(x) - f(y)\rvert \le
\lvert x - y\rvert$,
$\|f(\mathbf{A}) - f(\mathbf{B})\|_{\mathsf{F}} \le \|\mathbf{A} - \mathbf{B}\|_{\mathsf{F}}$.
[Kittaneh1985], for normal operators and the Hilbert–Schmidt norm.
Proof: in eigenbases $\mathbf{U}^{\mathsf{T}}(f(\mathbf{A}) - f(\mathbf{B}))\mathbf{W}$ has
entries $(f(a_i) - f(b_j))q_{ij}$ and $\mathbf{U}^{\mathsf{T}}(\mathbf{A} - \mathbf{B})\mathbf{W}$
has entries $(a_i - b_j)q_{ij}$; moderate.
Result: lipschitz-cfc-frobenius -/
theorem frobNorm_cfc_sub_cfc_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) {f : ℝ → ℝ}
    (hf : LipschitzWith 1 f) :
    frobNorm (cfc f A - cfc f B) ≤ frobNorm (A - B) := by
  have hdec : ∀ {C : Matrix ι ι ℝ} (hC : C.IsHermitian) (g : ℝ → ℝ),
      cfc g C = (hC.eigenvectorUnitary : Matrix ι ι ℝ) *
        Matrix.diagonal (fun i => g (hC.eigenvalues i)) *
          (hC.eigenvectorUnitary : Matrix ι ι ℝ)ᵀ := by
    intro C hC g
    rw [hC.cfc_eq, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
    rfl
  set U := (hA.eigenvectorUnitary : Matrix ι ι ℝ)
  set V := (hB.eigenvectorUnitary : Matrix ι ι ℝ)
  set a := hA.eigenvalues
  set b := hB.eigenvalues
  have hU := hA.hasOrthonormalCols_eigenvectorUnitary
  have hV := hB.hasOrthonormalCols_eigenvectorUnitary
  have hUt : HasOrthonormalCols Uᵀ := by
    have := hU.conjTranspose
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hUU : Uᵀ * U = 1 := by
    have := hU.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hVV : Vᵀ * V = 1 := by
    have := hV.conjTranspose_mul_self
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hA' : A = U * Matrix.diagonal a * Uᵀ := by
    have := hdec hA (fun x => x)
    rwa [cfc_id' ℝ A] at this
  have hB' : B = V * Matrix.diagonal b * Vᵀ := by
    have := hdec hB (fun x => x)
    rwa [cfc_id' ℝ B] at this
  -- conjugate both differences by the two eigenbases
  have hconj : ∀ (d e : ι → ℝ), Uᵀ * (U * Matrix.diagonal d * Uᵀ - V * Matrix.diagonal e * Vᵀ) * V =
      Matrix.diagonal d * (Uᵀ * V) - Uᵀ * V * Matrix.diagonal e := by
    intro d e
    simp only [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, hUU, Matrix.one_mul]
    simp only [Matrix.mul_assoc, hVV, Matrix.mul_one]
  have hfrob : ∀ X : Matrix ι ι ℝ, frobNorm X = frobNorm (Uᵀ * X * V) := fun X => by
    rw [Matrix.mul_assoc, hUt.frobNorm_mul_left, hV.frobNorm_mul_right]
  have hAB : A - B = U * Matrix.diagonal a * Uᵀ - V * Matrix.diagonal b * Vᵀ := by
    rw [← hA', ← hB']
  rw [hfrob, hfrob (A - B), hdec hA f, hdec hB f, hconj, hAB, hconj]
  have hsq : frobNorm (Matrix.diagonal (fun i => f (a i)) * (Uᵀ * V) -
      Uᵀ * V * Matrix.diagonal (fun i => f (b i))) ^ 2 ≤
      frobNorm (Matrix.diagonal a * (Uᵀ * V) - Uᵀ * V * Matrix.diagonal b) ^ 2 := by
    rw [frobNorm_sq_eq_sum_sq, frobNorm_sq_eq_sum_sq]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    simp only [Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
    have hl : |f (a i) - f (b j)| ≤ |a i - b j| := by
      have := hf.dist_le_mul (a i) (b j)
      simpa [Real.dist_eq] using this
    rw [show f (a i) * (Uᵀ * V) i j - (Uᵀ * V) i j * f (b j) =
        (f (a i) - f (b j)) * (Uᵀ * V) i j by ring,
      show a i * (Uᵀ * V) i j - (Uᵀ * V) i j * b j = (a i - b j) * (Uᵀ * V) i j by ring,
      mul_pow, mul_pow, ← sq_abs (f (a i) - f (b j)), ← sq_abs (a i - b j)]
    gcongr
  exact (sq_le_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).1 hsq

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The dilated matrix is symmetric. -/
theorem isHermitian_dilatedH : L.dilatedH.IsHermitian := by
  sorry

/-- The backward model is symmetric. -/
theorem isHermitian_backwardH : L.backwardH.IsHermitian := by
  sorry

/-- **The spectrum of the backward model is near that of $\mathbf{H}$**: every eigenvalue of
$\tilde{\mathbf{H}}$ is within $2000k^4\varepsilon\|\mathbf{H}\|_2$ of an eigenvalue of
$\mathbf{H}$. No printed source; the maintainer's draft, `rem:wasserstein` (by Weyl's
inequality there).
Proof: a unit eigenvector of $\tilde{\mathbf{H}}$ has residual at most $\|\boldsymbol{\Delta}\|$
for $\hat{\mathbf{H}}$, whose eigenvalues are eigenvalues of $\mathbf{H}$; easy. -/
theorem exists_abs_eigenvalue_backwardH_sub_eigenvalue_le {i : ℕ}
    (hi : i < Fintype.card (Fin n × Fin (k + 1))) :
    ∃ j < n, |eigenvalue L.backwardH i - eigenvalue L.H j| ≤
      2000 * k ^ 4 * L.ε * specNorm L.H := by
  sorry

/-- **Localization of stabilised Ritz values** (Paige): for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$ of the computed tridiagonal matrix, some eigenvalue
$\lambda$ of $\mathbf{H}$ satisfies
$$\lvert\theta - \lambda\rvert \le \beta_k\lvert y_{k-1}\rvert
+ 2000k^4\varepsilon\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `thm:stabilized`, states
$\lesssim_k \beta_k\lvert\mathbf{e}_k^{\mathsf{T}}\mathbf{y}\rvert + \varepsilon\|\mathbf{A}\|$;
[Paige1980, Theorem 3.1].
Proof: $\hat{\mathbf{x}} = \hat{\mathbf{V}}_k\mathbf{y}$ is a unit vector with
$(\tilde{\mathbf{H}} - \theta)\hat{\mathbf{x}} = \beta_k y_{k-1}\hat{\mathbf{v}}_{k+1}$; then
`Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le` for $\hat{\mathbf{H}}$; easy.
Result: paige-stabilized-ritz-values -/
theorem exists_abs_sub_eigenvalue_le_of_mulVec_eq_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ j < n, |θ - eigenvalue L.H j| ≤
      L.β k * |y L.lastIndex| + 2000 * k ^ 4 * L.ε * specNorm L.H := by
  sorry

/-- **Containment of the computed Ritz values, below** (Paige): every eigenvalue $\theta$ of the
computed tridiagonal matrix satisfies $\lambda_{\min}(\mathbf{H}) - \theta \le
2000k^4\varepsilon\|\mathbf{H}\|_2$, where $\lambda_{\min}(\mathbf{H}) = \lambda_m(\mathbf{H})$,
$m + 1 = n$. No printed source; the maintainer's draft, `thm:containment`;
[Paige1980, (3.48)].
Proof: $\theta = \hat{\mathbf{x}}^{\mathsf{T}}\hat{\mathbf{H}}\hat{\mathbf{x}} +
\hat{\mathbf{x}}^{\mathsf{T}}\boldsymbol{\Delta}\hat{\mathbf{x}}$ and the Rayleigh bounds of
$\mathbf{H}$ on each block; easy.
Result: paige-ritz-containment -/
theorem eigenvalue_last_sub_le_of_mulVec_eq_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) {m : ℕ} (hm : m + 1 = n) :
    eigenvalue L.H m - θ ≤ 2000 * k ^ 4 * L.ε * specNorm L.H := by
  sorry

/-- **Containment of the computed Ritz values, above** (Paige): every eigenvalue $\theta$ of the
computed tridiagonal matrix satisfies $\theta - \lambda_{\max}(\mathbf{H}) \le
2000k^4\varepsilon\|\mathbf{H}\|_2$, where $\lambda_{\max}(\mathbf{H}) = \lambda_0(\mathbf{H})$.
No printed source; the maintainer's draft, `thm:containment`; [Paige1980, (3.48)].
Proof: as `NLAlib.LanczosRun.eigenvalue_last_sub_le_of_mulVec_eq_smul`; easy.
Result: paige-ritz-containment -/
theorem sub_eigenvalue_zero_le_of_mulVec_eq_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    θ - eigenvalue L.H 0 ≤ 2000 * k ^ 4 * L.ε * specNorm L.H := by
  sorry

/-- The quadratic forms of $f(\hat{\mathbf{H}})$ at the dilated start and of $f(\mathbf{H})$ at
$\bar{\mathbf{v}}_1$ agree: the spectral measure of $(\hat{\mathbf{H}}, \tilde{\mathbf{v}})$ is that
of $(\mathbf{H}, \bar{\mathbf{v}}_1)$.
Proof: $f(\hat{\mathbf{H}})$ is block diagonal with blocks $f(\mathbf{H})$; moderate. -/
theorem dotProduct_cfc_dilatedH_mulVec (f : ℝ → ℝ) :
    L.dilatedStart ⬝ᵥ (cfc f L.dilatedH *ᵥ L.dilatedStart) =
      L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) := by
  sorry

/-- **The spectral measures are Wasserstein-close**: for every $1$-Lipschitz $f$,
$$\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
\tilde{\mathbf{v}}^{\mathsf{T}}f(\tilde{\mathbf{H}})\tilde{\mathbf{v}}\rvert
\le 2000k^4\varepsilon\|\mathbf{H}\|_2 \,,$$
so the spectral measure of $(\mathbf{H}, \bar{\mathbf{v}}_1)$ and that of the backward model
$(\tilde{\mathbf{H}}, \tilde{\mathbf{v}})$, on which exact Lanczos computes $\mathbf{T}_k$, are
within that distance in $W_1$.
No printed source; the maintainer's draft, `rem:wasserstein`, bounds the difference by
$\sqrt{2k}\|\boldsymbol{\Delta}\|$ (through the rank of $\boldsymbol{\Delta}$); here directly by
$\|\boldsymbol{\Delta}\|_{\mathsf{F}}$.
Proof: `NLAlib.LanczosRun.dotProduct_cfc_dilatedH_mulVec`, `NLAlib.frobNorm_cfc_sub_cfc_le` and
`NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le`; easy.
Result: lanczos-spectral-measure-wasserstein -/
theorem abs_dotProduct_cfc_mulVec_sub_le {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    |L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) -
        L.dilatedStart ⬝ᵥ (cfc f L.backwardH *ᵥ L.dilatedStart)| ≤
      2000 * k ^ 4 * L.ε * specNorm L.H := by
  sorry

end LanczosRun

end NLAlib
