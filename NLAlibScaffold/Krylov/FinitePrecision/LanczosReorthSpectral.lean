/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.LanczosReorthBackward
public import NLAlib.Matrix.Spectral.Interlacing
public import NLAlib.Krylov.Eigenvalues.Ritz
public import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# Spectral consequences of the backward model of a reorthogonalized run (scaffold)

Statements for `NLAlib/Krylov/FinitePrecision/LanczosReorthSpectral.lean` (stage
LANCZOS-REORTH, design note `docs/design/Krylov-LanczosReorth.md` §3.2 S4a–S4d, ids F1–F7), with
$e$ = `NLAlib.LanczosReorthRun.backwardRadius`: the Ritz values interlace the eigenvalues of
$\mathbf{H}$ up to $e$; converged Ritz values are not duplicated (a residual-gated count;
interlacing alone gives no count, see the note's counterexample); Ritz-pair residuals; the
Kaniel–Paige–Saad bound for the backward model; Gauss quadrature exactness and its transfer to
$\mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}$ for Lipschitz $f$. Eigenvalues are indexed
decreasingly from $0$ (`NLAlib.eigenvalue`).

Common hypotheses as in `NLAlibScaffold/Krylov/FinitePrecision/LanczosReorthRun.lean`.

## Main results

* `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add`,
  `NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal`: interlacing (F1).
* `NLAlib.LanczosReorthRun.card_le_card_eigenvalue_mem`: no duplicated converged Ritz values (F2).
* `NLAlib.LanczosReorthRun.exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul`,
  `NLAlib.LanczosReorthRun.exists_abs_eigenvalue_sub_le_of_β_le`: Ritz residuals (F3).
* `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_mem_Icc`: containment (F4).
* `NLAlib.LanczosReorthRun.exists_backward_kaniel_paige_saad`: KPS transfer (F5).
* `NLAlib.LanczosReorthRun.exists_pure_backward_gauss`,
  `NLAlib.LanczosReorthRun.exists_pure_backward_abs_quadForm_cfc_sub_le`: quadrature (F6, F7).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- **Ritz values interlace from above up to $e$** (F1): $\theta_i \le \lambda_i(\mathbf{H}) + e$
for $i < k$. [Simon1984b] in substance; [HornJohnson2013, Corollary 4.3.37] for the exact case.
Proof: `NLAlib.LanczosReorthRun.exists_backward` gives $\mathbf{T}_k = \mathbf{U}_k^{\mathsf{T}}
(\mathbf{H} + \mathbf{E})\mathbf{U}_k$ (multiply its identity by $\mathbf{U}_k^{\mathsf{T}}$ and use
orthonormality); `Matrix.IsHermitian.eigenvalue_conjTranspose_mul_mul_le` (Poincaré) for
$\mathbf{H} + \mathbf{E}$, then `Matrix.IsHermitian.abs_eigenvalue_sub_le` (Weyl) with
$\|\mathbf{E}\|_2 \le \|\mathbf{E}\|_{\mathsf F}$ (`specNorm_le_frobNorm`). S, about 30 lines. -/
theorem eigenvalue_tridiagonal_le_add (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.toLanczosData.tridiagonal i ≤ eigenvalue L.H i + L.backwardRadius := by
  sorry

/-- **Ritz values interlace from below up to $e$** (F1):
$\lambda_{i + n - k}(\mathbf{H}) - e \le \theta_i$ for $i < k$ (and $k \le n$ by
`NLAlib.LanczosReorthRun.succ_le_card`). [Simon1984b] in substance.
Proof: as `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add` with
`Matrix.IsHermitian.eigenvalue_le_eigenvalue_conjTranspose_mul_mul` ($d = n - k$). S, about 25
lines. -/
theorem eigenvalue_sub_le_eigenvalue_tridiagonal (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.H (i + (n - k)) - L.backwardRadius ≤ eigenvalue L.toLanczosData.tridiagonal i := by
  sorry

/-- **Converged Ritz values are not duplicated** (F2, S4a′): for $r$ orthonormal eigenvectors
$\mathbf{y}_i$ of $\mathbf{T}_k$ with eigenvalues $\theta_i \in [a, b]$ and residuals
$\beta_k|\mathbf{e}_{k-1}^{\mathsf{T}}\mathbf{y}_i| < (g - 2e)/\sqrt r$, $g > 2e$, the matrix
$\mathbf{H}$ has at least $r$ eigenvalues in $(a - g, b + g)$. With $[a, b]$ a window around a
simple isolated eigenvalue this forbids two converged copies; the residual condition cannot be
dropped (`docs/design/Krylov-LanczosReorth.md` §3.2, counterexample $\operatorname{diag}(1,0,-1)$).
The phenomenon: [Paige1971], [Parlett1998, Ch. 13]; this statement: no printed source.
Proof: `NLAlib.LanczosReorthRun.exists_backward`; $\mathbf{X} = \mathbf{U}_k\mathbf{Y}$ is
orthonormal and $(\mathbf{H} + \mathbf{E})\mathbf{x}_i - \theta_i\mathbf{x}_i = (\beta_k y_{k-1,i})
\mathbf{u}_{k+1}$ (norm $\beta_k|y_{k-1,i}|$). Apply
`NLAlib.card_le_card_eigenvalue_mem_of_hasOrthonormalCols`
to $\mathbf{H} + \mathbf{E}$ with $d = g - e$; every eigenvalue of $\mathbf{H} + \mathbf{E}$ in
$(a - g + e, b + g - e)$ matches an eigenvalue of $\mathbf{H}$ of the same index in
$(a - g, b + g)$ (`Matrix.IsHermitian.abs_eigenvalue_sub_le`), so the counts compare
(`Finset.card_le_card`). M, about 60 lines. -/
theorem card_le_card_eigenvalue_mem (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {r : ℕ} {Y : Matrix (Fin k) (Fin r) ℝ}
    (hY : HasOrthonormalCols Y) {θ : Fin r → ℝ}
    (hTY : ∀ i, L.toLanczosData.tridiagonal *ᵥ (fun c => Y c i) = θ i • fun c => Y c i)
    {a b g : ℝ} (hθ : ∀ i, θ i ∈ Set.Icc a b) (hg : 2 * L.backwardRadius < g)
    (hres : ∀ i, L.β k * |Y L.toLanczosData.lastIndex i| <
      (g - 2 * L.backwardRadius) / Real.sqrt r) :
    r ≤ ((Finset.range n).filter fun i => eigenvalue L.H i ∈ Set.Ioo (a - g) (b + g)).card := by
  sorry

/-- **Ritz-pair residuals** (F3, S4b): every unit eigenvector $\mathbf{y}$ of $\mathbf{T}_k$ with
eigenvalue $\theta$ gives an eigenvalue of $\mathbf{H}$ within $\beta_k|y_{k-1}| + e$.
[Paige1980] for plain Lanczos; standard.
Proof: with $\mathbf{x} = \mathbf{U}_k\mathbf{y}$ (unit), `NLAlib.LanczosReorthRun.exists_backward`
gives $(\mathbf{H} + \mathbf{E})\mathbf{x} - \theta\mathbf{x} = (\beta_k y_{k-1})\mathbf{u}_{k+1}$;
`Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le` for $\mathbf{H} + \mathbf{E}$, then
`Matrix.IsHermitian.abs_eigenvalue_sub_le`. S, about 25 lines. -/
theorem exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) [NeZero n] {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.toLanczosData.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ i < n, |eigenvalue L.H i - θ| ≤ L.β k * |y L.toLanczosData.lastIndex| +
      L.backwardRadius := by
  sorry

/-- **A small last coefficient makes the computed space nearly invariant** (F3, the
non-admissible stop): if $\beta_k \le \rho$, every Ritz value is within $\rho + e$ of an
eigenvalue of $\mathbf{H}$ (with $\rho = \tau\nu_{k+1}$-type bounds when the next step fails the
criterion). [Paige1970] (the stopping criterion).
Proof: for each $i < k$ take a unit eigenvector of $\mathbf{T}_k$ for its $i$-th eigenvalue
(`Matrix.IsHermitian.eigenvectorBasis`, `Matrix.IsHermitian.mulVec_eigenvectorBasis`), $|y_{k-1}|
\le 1$, and `NLAlib.LanczosReorthRun.exists_abs_eigenvalue_sub_le_of_mulVec_eq_smul`. S, about 25
lines. -/
theorem exists_abs_eigenvalue_sub_le_of_β_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) [NeZero n] {ρ : ℝ} (hρ : L.β k ≤ ρ)
    {i : ℕ} (hi : i < k) :
    ∃ l < n, |eigenvalue L.H l - eigenvalue L.toLanczosData.tridiagonal i| ≤
      ρ + L.backwardRadius := by
  sorry

/-- **Containment** (F4): every Ritz value lies in $[\lambda_{n-1}(\mathbf{H}) - e,
\lambda_0(\mathbf{H}) + e]$. [Paige1980] for plain Lanczos.
Proof: `NLAlib.LanczosReorthRun.eigenvalue_tridiagonal_le_add` at $i$ and
`Matrix.IsHermitian.eigenvalue_le_eigenvalue` (monotone in the index) for the upper end;
`NLAlib.LanczosReorthRun.eigenvalue_sub_le_eigenvalue_tridiagonal` and the same monotonicity for
the lower end ($i + n - k \le n - 1$). S, about 20 lines. -/
theorem eigenvalue_tridiagonal_mem_Icc (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {i : ℕ} (hi : i < k) :
    eigenvalue L.toLanczosData.tridiagonal i ∈
      Set.Icc (eigenvalue L.H (n - 1) - L.backwardRadius)
        (eigenvalue L.H 0 + L.backwardRadius) := by
  sorry

/-- **Kaniel–Paige–Saad for the backward model** (F5, S4c): the proved bound
`Matrix.IsHermitian.eigenvalue_sub_eigenvalue_conjTranspose_mul_mul_le` holds for
$(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$ with $\mathbf{T}_k$ in place of the compression, and
$\lambda_0(\mathbf{H} + \mathbf{E})$ is within $e$ of $\lambda_0(\mathbf{H})$. Stating the tangent
in
$\mathbf{H}$'s data needs Davis–Kahan (later). [Saad2011, Theorem 6.4] for the exact bound.
Proof: `NLAlib.LanczosReorthRun.exists_lanczosState_backward`; $\mathbf{T}_k =
\mathbf{U}_k^{\mathsf{T}}(\mathbf{H}+\mathbf{E})\mathbf{U}_k$ and the range of $\mathbf{U}_k$ is the
Krylov space $\mathcal K_k(\mathbf{H} + \mathbf{E}, \mathbf{u}_1)$ (the Lanczos basis spans it:
`Matrix.IsHermitian.lanczosMatrix_eq_arnoldiMatrix` and the range of the Arnoldi basis, with
$\beta_j > 0$ so the grade is at least $k$); apply the exact theorem with $q = k - 1$; Weyl for
the last conjunct. M, about 70 lines. -/
theorem exists_backward_kaniel_paige_saad (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ frobNorm E ≤ L.backwardRadius ∧
      |eigenvalue (L.H + E) 0 - eigenvalue L.H 0| ≤ L.backwardRadius ∧
      ∀ {a c : ℝ}, a < c → c < eigenvalue (L.H + E) 0 →
        spectrum ℝ (L.H + E) ⊆ Set.Icc a c ∪ {eigenvalue (L.H + E) 0} →
        0 < (spectralMeasure (L.H + E)
          (colSeq (polarFactor (basisOf L.v (k + 1))) 1)).real {eigenvalue (L.H + E) 0} →
        eigenvalue (L.H + E) 0 - eigenvalue L.toLanczosData.tridiagonal 0 ≤
          4 * (eigenvalue (L.H + E) 0 - a) *
            spectralTangentSq (L.H + E) (colSeq (polarFactor (basisOf L.v (k + 1))) 1)
              (eigenvalue (L.H + E) 0) *
            ((Real.sqrt (eigenvalue (L.H + E) 0 - a) - Real.sqrt (eigenvalue (L.H + E) 0 - c)) /
              (Real.sqrt (eigenvalue (L.H + E) 0 - a) +
                Real.sqrt (eigenvalue (L.H + E) 0 - c))) ^ (2 * (k - 1)) := by
  sorry

/-- **Gauss quadrature on the backward model** (F6, S4d): with $\mathbf{H}'$ from
`NLAlib.LanczosReorthRun.exists_pure_backward`, $\|\mathbf{b}\|^2\,[p(\mathbf{T}_k)]_{00} =
\mathbf{b}^{\mathsf{T}}p(\mathbf{H}')\mathbf{b}$ for every polynomial of degree at most $2k - 1$:
the computed tridiagonal is the Gauss rule of the spectral measure of $(\mathbf{H}', \mathbf{b})$.
[GolubMeurant2010, Theorem 6.6] (locator to verify).
Proof: `NLAlib.LanczosReorthRun.exists_pure_backward` gives $\mathbf{T}_k =$
`NLAlib.lanczosTridiagonal` $\mathbf{H}'\,\mathbf{b}\,k$; the exact moment matching for Hermitian
$\mathbf{H}'$ is `Matrix.IsHermitian.matchesMoments_lanczosQuadrature` (with the integral form of
the quadrature
in `NLAlib/Krylov/Functions/Quadrature.lean` to read off $[p(\mathbf{T}_k)]_{00}$; the grade is at
least
$k$ because $\beta_j > 0$). S, about 40 lines. -/
theorem exists_pure_backward_gauss (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      ∀ p : Polynomial ℝ, p.natDegree ≤ 2 * k - 1 →
        ‖WithLp.toLp 2 b‖ ^ 2 *
            (Polynomial.aeval L.toLanczosData.tridiagonal p) ⟨0, L.k_pos⟩ ⟨0, L.k_pos⟩ =
          b ⬝ᵥ (Polynomial.aeval H' p *ᵥ b) := by
  sorry

/-- **Transfer to $\mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}$** (F7, S4d): with $\mathbf{H}'$
as
in `NLAlib.LanczosReorthRun.exists_pure_backward_gauss`, for every $1$-Lipschitz $f$,
$|\mathbf{b}^{\mathsf{T}}f(\mathbf{H}')\mathbf{b} - \mathbf{b}^{\mathsf{T}}f(\mathbf{H})\mathbf{b}|
\le \|\mathbf{b}\|^2\|\mathbf{H}' - \mathbf{H}\|_{\mathsf F}$, so the exact quadrature error theory
for $(\mathbf{H}', \mathbf{b})$ transfers with that additive term. [Kittaneh1985].
Proof: `NLAlib.LanczosReorthRun.exists_pure_backward_gauss`; Cauchy–Schwarz and
$\|\mathbf{M}\mathbf{b}\| \le \|\mathbf{M}\|_{\mathsf F}\|\mathbf{b}\|$, then
`Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le`. S, about 20 lines. -/
theorem exists_pure_backward_abs_quadForm_cfc_sub_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {b : Fin n → ℝ} (hb : b ≠ 0) {δb : ℝ}
    (hδ : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖⁻¹ • b - L.v 1)‖ ≤ δb) :
    ∃ H' : Matrix (Fin n) (Fin n) ℝ, H'ᵀ = H' ∧
      frobNorm (H' - L.H) ≤ L.backwardRadius +
        3 * specNorm L.H * (δb + 2 * Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) ∧
      lanczosTridiagonal H' b k = L.toLanczosData.tridiagonal ∧
      ∀ f : ℝ → ℝ, LipschitzWith 1 f →
        |b ⬝ᵥ (cfc f H' *ᵥ b) - b ⬝ᵥ (cfc f L.H *ᵥ b)| ≤
          ‖WithLp.toLp 2 b‖ ^ 2 * frobNorm (H' - L.H) := by
  sorry

end LanczosReorthRun

end NLAlib
