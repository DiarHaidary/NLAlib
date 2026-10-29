/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.CGRun

/-!
# An a priori backward model for finite-precision conjugate gradients

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$, under the smallness hypothesis
$$\text{(H)}\qquad k^3\,\varepsilon\,\kappa^2 \le 10^{-5},$$
the run certificates are bounded a priori ($\|\mathbf{p}_j\|^2 \le 3.3\kappa\|\mathbf{r}_j\|^2$,
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le 1.05\kappa\|\mathbf{r}_j\|^2$, $\beta_{j+1},
\delta_j/\gamma_j \le 1.6a'$), and the backward model of the run satisfies
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
4 \cdot 10^4\,k^3\,\varepsilon\,\kappa\,a' \le a/2 .$$
Exact CG on $(\tilde{\mathbf{H}}, (\mathbf{b}, \mathbf{0}, \dots, \mathbf{0}))$ computes the
computed step lengths $\gamma_j$ exactly and residuals of exactly the computed norms
$\|\mathbf{r}_j\|$; its $\tilde{\mathbf{H}}$-norm error decreases by exactly
$\gamma_j\|\mathbf{r}_j\|^2$ per step, the estimator of [StrakosTichy2002, (4.9)]; and its
squared error at step $k$ is $\|\mathbf{x}_\star\|_{\mathbf{A}}^2 - \sum_{j<k}\gamma_j
\|\mathbf{r}_j\|^2$ up to $2\|\mathbf{b}\|^2c/a^2$, $c$ the model distance.

The proof is an induction on the number of steps through the backward model of the prefix
runs (`NLAlib.CGRun.take`): the model of the first $j$ steps is positive definite with condition
number at most $3\kappa$ by P(j); exact CG on it bounds the certificates of step $j$
(`Matrix.PosDef.norm_cgState_r_le`, `Matrix.PosDef.norm_cgState_p_sq_le`,
`Matrix.PosDef.norm_cgState_r_succ_sq_div_le`), and Lemmas A and B close P(j + 1).

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§6–§8).
Constants are unoptimised; see the note.

## Main definitions

* `NLAlib.CGRun.take`: the first $m$ steps of a run.

## Main results

* `NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`,
  `NLAlib.CGRun.lanczosβ_succ_le`, `NLAlib.CGRun.δ_le`, `NLAlib.CGRun.ρ_le`: a priori
  certificates.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le`: the a priori backward model.
* `NLAlib.CGRun.cgAlpha_backwardH`, `NLAlib.CGRun.norm_cgState_backwardH_r`: exact CG on the
  model reproduces the run.
* `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate`,
  `NLAlib.CGRun.abs_quadForm_backwardH_sub_cgIterate_sub_le`: the model's errors in terms of the
  computed coefficients.
* `NLAlib.CGRun.ρ_le_chebyshev`: the computed residual norms converge at the Chebyshev rate of
  $2\kappa + 1$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- **The first $m$ steps of a run**, $1 \le m \le k$: the same data, every hypothesis
restricted. -/
noncomputable def take (m : ℕ) (hm : 0 < m) (hmk : m ≤ k) : CGRun n m where
  A := C.A
  b := C.b
  x := C.x
  r := C.r
  p := C.p
  s := C.s
  ν := C.ν
  μ := C.μ
  γ := C.γ
  δ := C.δ
  es := C.es
  θ := C.θ
  eμ := C.eμ
  eγ := C.eγ
  ex := C.ex
  er := C.er
  eδ := C.eδ
  ep := C.ep
  ε := C.ε
  transpose_A := C.transpose_A
  ε_nonneg := C.ε_nonneg
  k_pos := hm
  k_mul_ε_le := by
    have h : (m : ℝ) ≤ k := by exact_mod_cast hmk
    nlinarith [C.k_mul_ε_le, C.ε_nonneg]
  x_zero := C.x_zero
  r_zero := C.r_zero
  p_zero := C.p_zero
  ν_eq := fun j hj => C.ν_eq j (hj.trans hmk)
  abs_θ_le := fun j hj => C.abs_θ_le j (hj.trans hmk)
  ν_pos := fun j hj => C.ν_pos j (hj.trans_le hmk)
  s_eq := fun j hj => C.s_eq j (hj.trans_le hmk)
  norm_es_le := fun j hj => C.norm_es_le j (hj.trans_le hmk)
  μ_eq := fun j hj => C.μ_eq j (hj.trans_le hmk)
  abs_eμ_le := fun j hj => C.abs_eμ_le j (hj.trans_le hmk)
  μ_pos := fun j hj => C.μ_pos j (hj.trans_le hmk)
  γ_eq := fun j hj => C.γ_eq j (hj.trans_le hmk)
  abs_eγ_le := fun j hj => C.abs_eγ_le j (hj.trans_le hmk)
  x_succ := fun j hj => C.x_succ j (hj.trans_le hmk)
  norm_ex_le := fun j hj => C.norm_ex_le j (hj.trans_le hmk)
  r_succ := fun j hj => C.r_succ j (hj.trans_le hmk)
  norm_er_le := fun j hj => C.norm_er_le j (hj.trans_le hmk)
  δ_eq := fun j hj => C.δ_eq j (hj.trans_le hmk)
  abs_eδ_le := fun j hj => C.abs_eδ_le j (hj.trans_le hmk)
  p_succ := fun j hj => C.p_succ j (hj.trans_le hmk)
  norm_ep_le := fun j hj => C.norm_ep_le j (hj.trans_le hmk)

/-! ### A priori certificates (the induction) -/

/-- **Directions against residuals, a priori**: under (H), $\|\mathbf{p}_j\|^2 \le
3.3\kappa\|\mathbf{r}_j\|^2$ for $j < k$, $\kappa = a'/a$. [StrakosTichy2002, (9.13)] has
$\|\mathbf{p}_j\|/\|\mathbf{r}_j\| \le 1 + j\kappa^{1/2}$ from an imported monotonicity.
Proof: the induction P(j) of the note (§7): the backward model of `C.take j` has spectrum in
$[a/2, a' + a/2]$ (`NLAlib.NormalizedLanczosData.spectrum_backwardH_subset_Icc` with the bound
of `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates` at the P(j) certificates),
exact CG on it reproduces the run (`NLAlib.CGRun.cgAlpha_backwardH` for the prefix), and
`Matrix.PosDef.norm_cgState_p_sq_le` on the model with the step-$j$ recursion
$\pi_j^2 \le (1 + O(\varepsilon))[1 + (\rho_j/\rho_{j-1})^2\pi_{j-1}^2 + 2\lvert\tau_{j-1}\rvert/
\rho_{j-1}^2]$ (`NLAlib.CGRun.abs_p_dotProduct_r_succ_le`). The other certificates of this
section are proved in the same induction. Difficulty: hard (the induction of the design). -/
theorem norm_p_sq_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ 33 / 10 * (a' / a) * C.ρ j ^ 2 := by
  sorry

/-- **The curvature certificate, a priori**: under (H),
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le 1.05\kappa\rho_j^2$, $j < k$.
Proof: $\gamma_j = \nu_j/\mu_j(1 + \eta)$ with
$\mu_j \ge (1 - 2.1\varepsilon\kappa)a\|\mathbf{p}_j\|^2$
(as in `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`), $\|\mathbf{A}\|_2 \le a'$. No model
needed. Difficulty: easy. -/
theorem specNorm_mul_γ_mul_norm_p_sq_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j < k) :
    specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ 21 / 20 * (a' / a) * C.ρ j ^ 2 := by
  sorry

/-- **The off-diagonal coefficients, a priori**: under (H), $\beta_{j+1} =
\rho_{j+1}/(\gamma_j\rho_j) \le 1.6a'$, $j < k$.
Proof: in the induction; $\beta_{j+1}$ is an entry of
$\hat{\mathbf{V}}_{j+2}^{\mathsf{T}}\tilde{\mathbf{H}}_{j+1}\hat{\mathbf{V}}_{j+1}$, hence at most
$\lambda_{\max}(\tilde{\mathbf{H}}_{j+1}) \le a' + a/2$ for the model of `C.take (j + 1)`.
Difficulty: moderate (inside the induction). -/
theorem lanczosβ_succ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    C.lanczosβ (j + 1) ≤ 8 / 5 * a' := by
  sorry

/-- **The coefficient ratio, a priori**: under (H), $\delta_j \le 1.6a'\gamma_j$, $j < k$.
Proof: in the induction; `Matrix.PosDef.norm_cgState_r_succ_sq_div_le` on the model of
`C.take (j + 1)`, which reproduces $\gamma_j$ and $\rho_j, \rho_{j+1}$, and
`NLAlib.CGRun.abs_δ_sub_le`. Difficulty: moderate (inside the induction). -/
theorem δ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    C.δ j ≤ 8 / 5 * a' * C.γ j := by
  sorry

/-! ### The backward model -/

/-- **The a priori backward model of finite-precision CG**: for spectrum in $[a, a']$, $a > 0$,
$\kappa = a'/a$, and (H) $k^3\varepsilon\kappa^2 \le 10^{-5}$,
$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le
4 \cdot 10^4\,k^3\,\varepsilon\,\kappa\,a' .$$
No printed source. [Greenbaum1989] states the model for perturbed recurrences, with a
perturbation of order $\varepsilon^{1/4}$, and does not bound the perturbation terms of CG in
terms of $\varepsilon$ [MeurantStrakos2006, §5.2]; [GreenbaumLiuChen2021] derive the terms and
check them numerically.
Proof: `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates` with
$1 + \Pi \le 1 + 1.82\sqrt{\kappa}$, $K \le 1.05\kappa$, $B \le 1.6a'$, $\|\mathbf{A}\|_2 \le a'$:
$f \le 89\varepsilon\kappa a'$, $p \le 322k\varepsilon\kappa a'$, and
$102 \cdot 89 + 96 \cdot 322 \le 4 \cdot 10^4$. Difficulty: easy given the certificates. -/
theorem frobNorm_backwardH_sub_dilatedH_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    frobNorm (C.backwardH - C.dilatedH) ≤ 40000 * k ^ 3 * C.ε * (a' / a) * a' := by
  sorry

/-- **The model is positive definite with condition number at most $2\kappa + 1$**: under (H)
its spectrum lies in $[a/2, a' + a/2]$.
Proof: `NLAlib.NormalizedLanczosData.spectrum_backwardH_subset_Icc` and
`NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le`, $4 \cdot 10^4k^3\varepsilon\kappa a' \le
0.4a$ by (H). Difficulty: easy. -/
theorem spectrum_backwardH_subset_Icc {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) :
    spectrum ℝ C.backwardH ⊆ Set.Icc (a / 2) (a' + a / 2) := by
  sorry

/-- **Exact Lanczos on the model computes the CG tridiagonal matrix** of the run, from the
dilated right-hand side (no hypothesis on $\varepsilon$).
Proof: `NLAlib.NormalizedLanczosData.lanczosTridiagonal_backwardH_dilatedStart`,
`NLAlib.CGRun.tridiagonal_toLanczosData`; `NLAlib.lanczosState` normalises its start and the
dilated start is $\mathbf{b}/\|\mathbf{b}\|$ in the first block. Difficulty: easy. -/
theorem lanczosTridiagonal_backwardH :
    lanczosTridiagonal C.backwardH C.dilatedRhs k = cgTridiagonal C.γ C.ρ k := by
  sorry

/-- **Exact CG on the model computes the computed step lengths**: under (H), for $j < k$,
the step length of `NLAlib.cgState` on $(\tilde{\mathbf{H}}, (\mathbf{b}, \mathbf{0}, \dots))$
from $\mathbf{0}$ is $\gamma_j$.
Proof: `Matrix.PosDef.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq` with
`NLAlib.CGRun.lanczosTridiagonal_backwardH`, the last coefficient from
`NLAlib.NormalizedLanczosData.lanczosState_backwardH_dilatedStart_beta`, positive definiteness
from `NLAlib.CGRun.spectrum_backwardH_subset_Icc`. Difficulty: easy. -/
theorem cgAlpha_backwardH {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    cgAlpha C.backwardH (cgState C.backwardH C.dilatedRhs 0 j) = C.γ j := by
  sorry

/-- **Exact CG on the model has the computed residual norms**: under (H), for $j \le k$,
$\|\tilde{\mathbf{r}}_j\| = \|\mathbf{r}_j\|$.
Proof: `Matrix.PosDef.norm_cgState_r_eq_of_lanczosTridiagonal_eq`, as
`NLAlib.CGRun.cgAlpha_backwardH`. Difficulty: easy. -/
theorem norm_cgState_backwardH_r {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (cgState C.backwardH C.dilatedRhs 0 j).r‖ = C.ρ j := by
  sorry

/-- **Residual ratios of the run, a priori**: under (H), $\|\mathbf{r}_j\| \le
\sqrt{3\kappa}\,\|\mathbf{r}_i\|$ for $i \le j \le k$ (the computed residual norms are those of
exact CG on a matrix of condition number at most $2\kappa + 1$). This is [StrakosTichy2002,
(7.20)] with the imported monotonicity replaced by the model.
Proof: `Matrix.PosDef.norm_cgState_r_le` on the model, `NLAlib.CGRun.norm_cgState_backwardH_r`,
$(a' + a/2)/(a/2) \le 3\kappa$. Difficulty: easy. -/
theorem ρ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ k) :
    C.ρ j ≤ Real.sqrt (3 * (a' / a)) * C.ρ i := by
  sorry

/-- **The computed residual norms converge at the Chebyshev rate** of the widened interval:
under (H), with $\kappa_c = 2\kappa + 1$, for $j \le k$,
$$\|\mathbf{r}_j\| \le 2\sqrt{\kappa_c}\Bigl(\frac{\sqrt{\kappa_c} - 1}{\sqrt{\kappa_c} + 1}\Bigr)^j
\|\mathbf{b}\| .$$
No printed source in this form; the qualitative statement is [Greenbaum1989] with
[MeurantStrakos2006, §5.2]. Valid for $k$ with (H), i.e. $k \lesssim (\varepsilon\kappa^2)^{-1/3}$.
Proof: `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow` on the model with
spectrum in $[a/2, a' + a/2]$,
$\|\tilde{\mathbf{r}}_j\|^2 \le (a' + a/2)\|\tilde{\mathbf{e}}_j\|^2$,
$\|\tilde{\mathbf{e}}_0\|^2 \le 2\|\mathbf{b}\|^2/a$, and `NLAlib.CGRun.norm_cgState_backwardH_r`.
Difficulty: easy. -/
theorem ρ_le_chebyshev {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j ≤ k) :
    C.ρ j ≤ 2 * Real.sqrt (2 * (a' / a) + 1) *
      ((Real.sqrt (2 * (a' / a) + 1) - 1) / (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ j *
        ‖WithLp.toLp 2 C.b‖ := by
  sorry

/-! ### Errors of exact CG on the model, in the computed quantities -/

/-- **The model's error decrements are the computed estimator**: under (H), for
$\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star = (\mathbf{b}, \mathbf{0}, \dots)$ and $j + d \le k$,
$$\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_j\|_{\tilde{\mathbf{H}}}^2 -
\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_{j+d}\|_{\tilde{\mathbf{H}}}^2 =
\sum_{i=j}^{j+d-1}\gamma_i\|\mathbf{r}_i\|^2,$$
exactly, with the computed $\gamma_i$ and the norms of the computed residuals: the estimator
$\nu_{j,d}$ of [StrakosTichy2002, (4.9), (10.7)] is exact for the model.
Proof: `Matrix.PosDef.re_quadForm_sub_cgIterate_sub_re_quadForm_sub_cgIterate_succ` on the
model, summed, with `NLAlib.CGRun.cgAlpha_backwardH` and `NLAlib.CGRun.norm_cgState_backwardH_r`.
Difficulty: easy. -/
theorem quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {j d : ℕ}
    (hjd : j + d ≤ k) :
    quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 j) -
        quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 (j + d)) =
      ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2 := by
  sorry

/-- **The model's error is a Gauss quadrature error of the computed tridiagonal matrix**:
under (H), $\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_k\|_{\tilde{\mathbf{H}}}^2 =
\|\tilde{\mathbf{x}}_\star\|_{\tilde{\mathbf{H}}}^2 - \sum_{j<k}\gamma_j\|\mathbf{r}_j\|^2$, and
the sum is $\|\mathbf{b}\|^2(\mathbf{T}_k^{-1})_{00}$ for $\mathbf{T}_k$ = `cgTridiagonal C.γ C.ρ k`
(`NLAlib.sq_mul_inv_cgTridiagonal_zero_zero`): the identity
$\|\mathbf{x} - \mathbf{x}_k\|_{\mathbf{A}}^2 = \|\mathbf{r}_0\|^2[(\mathbf{T}_n^{-1})_{11} -
(\mathbf{T}_k^{-1})_{11}]$ of [MeurantStrakos2006, (3.17)] holds for the model with the
computed $\mathbf{T}_k$ and
$\tilde{\mathbf{v}}^{\mathsf{T}}\tilde{\mathbf{H}}^{-1}\tilde{\mathbf{v}}$
in place of $(\mathbf{T}_n^{-1})_{11}$.
Proof: `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate` at
$j = 0$, $d = k$. Difficulty: easy. -/
theorem quadForm_backwardH_sub_cgIterate_eq {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) :
    quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 k) =
      quadForm C.backwardH xs - ∑ j ∈ Finset.range k, C.γ j * C.ρ j ^ 2 := by
  sorry

/-- **The model's initial error is the true one up to the model distance**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $\tilde{\mathbf{H}}\tilde{\mathbf{x}}_\star =
(\mathbf{b}, \mathbf{0}, \dots)$, with $c = 4 \cdot 10^4k^3\varepsilon\kappa a'$,
$$\bigl\lvert\|\tilde{\mathbf{x}}_\star\|_{\tilde{\mathbf{H}}}^2 -
\|\mathbf{x}_\star\|_{\mathbf{A}}^2\bigr\rvert \le 2\|\mathbf{b}\|^2c/a^2 .$$
The start of the model is exactly $\mathbf{b}/\|\mathbf{b}\|$ in the first block
($\mathbf{r}_0 = \mathbf{b}$ is not rounded), so the comparison is with the true problem.
Proof:
$\tilde{\mathbf{b}}^{\mathsf{T}}(\tilde{\mathbf{H}}^{-1} - \hat{\mathbf{H}}^{-1})\tilde{\mathbf{b}}$
and the resolvent identity, $\|\hat{\mathbf{H}}^{-1}\|_2 \le 1/a$,
$\|\tilde{\mathbf{H}}^{-1}\|_2 \le 2/a$, $\|\mathbf{\Delta}\|_2 \le c$. Difficulty: easy. -/
theorem abs_quadForm_backwardH_sub_quadForm_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {x : Fin n → ℝ}
    (hx : C.A *ᵥ x = C.b) :
    |quadForm C.backwardH xs - quadForm C.A x| ≤
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (40000 * k ^ 3 * C.ε * (a' / a) * a') / a ^ 2 := by
  sorry

/-- **The model's error at step $k$ in the computed quantities**: under (H),
$$\Bigl\lvert\|\tilde{\mathbf{x}}_\star - \tilde{\mathbf{x}}_k\|_{\tilde{\mathbf{H}}}^2 -
\Bigl(\|\mathbf{x}_\star\|_{\mathbf{A}}^2 - \sum_{j<k}\gamma_j\|\mathbf{r}_j\|^2\Bigr)\Bigr\rvert
\le 2\|\mathbf{b}\|^2c/a^2,\qquad c = 4 \cdot 10^4k^3\varepsilon\kappa a' .$$
The computed run's own error $\|\mathbf{x}_\star - \mathbf{x}_k\|_{\mathbf{A}}$ is not covered:
see the note (§9, next round).
Proof: `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_eq` and
`NLAlib.CGRun.abs_quadForm_backwardH_sub_quadForm_le`. Difficulty: easy. -/
theorem abs_quadForm_backwardH_sub_cgIterate_sub_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n × Fin (k + 1) → ℝ} (hxs : C.backwardH *ᵥ xs = C.dilatedRhs) {x : Fin n → ℝ}
    (hx : C.A *ᵥ x = C.b) :
    |quadForm C.backwardH (xs - cgIterate C.backwardH C.dilatedRhs 0 k) -
        (quadForm C.A x - ∑ j ∈ Finset.range k, C.γ j * C.ρ j ^ 2)| ≤
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (40000 * k ^ 3 * C.ε * (a' / a) * a') / a ^ 2 := by
  sorry

end CGRun

end NLAlib
