/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.Backward
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Matrix.Perturbation.Residual

/-!
# Spectral consequences of the backward model

From the backward model $\tilde{\mathbf{H}}$ of a run `L : NLAlib.LanczosRun n k`
(`NLAlib.LanczosRun.backwardH`), with <!-- value lanczosBackwardFactor k -->
$\delta = 2000k^4\varepsilon\|\mathbf{H}\|_2$:

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

The last rests on `Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le` (Kittaneh): a $1$-Lipschitz
function is $1$-Lipschitz in the Frobenius norm on symmetric matrices.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `rem:wasserstein`, `thm:stabilized`, `thm:containment`;
[Paige1980, Lemma 3.1, Theorem 3.1, (3.48)] for the classical forms.

## Main results

* `NLAlib.LanczosRun.exists_abs_eigenvalue_backwardH_sub_eigenvalue_le`: localization of the
  model's spectrum.
* `NLAlib.LanczosRun.exists_abs_sub_eigenvalue_le_of_mulVec_eq_smul`: stabilised Ritz values.
* `NLAlib.LanczosRun.eigenvalue_last_sub_le_of_mulVec_eq_smul`,
  `NLAlib.LanczosRun.sub_eigenvalue_zero_le_of_mulVec_eq_smul`: containment.
* `NLAlib.LanczosRun.abs_dotProduct_cfc_mulVec_sub_le`: closeness of the spectral measures.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- The squared norm of a vector on `Fin n × Fin m` is the sum over the blocks. -/
private theorem norm_toLp_sq_eq_sum_blocks {n m : ℕ} (x : Fin n × Fin m → ℝ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = ∑ r, ‖WithLp.toLp 2 (fun j => x (j, r))‖ ^ 2 := by
  simp only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, dotProduct, Fintype.sum_prod_type]
  exact Finset.sum_comm

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The dilated matrix is symmetric. -/
theorem isHermitian_dilatedH : L.dilatedH.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, dilatedH,
    Matrix.blockDiagonal_transpose, L.transpose_H]

/-- The matrix of the run is symmetric. -/
theorem isHermitian : L.H.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, L.transpose_H]

/-- The backward model is symmetric. -/
theorem isHermitian_backwardH : L.backwardH.IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, L.transpose_backwardH]

/-- The dilated matrix acts blockwise: block $r$ of $\hat{\mathbf{H}}\mathbf{x}$ is
$\mathbf{H}\mathbf{x}_r$. -/
theorem dilatedH_mulVec_apply (x : Fin n × Fin (k + 1) → ℝ) (i : Fin n) (r : Fin (k + 1)) :
    (L.dilatedH *ᵥ x) (i, r) = (L.H *ᵥ fun j => x (j, r)) i := by
  simp only [dilatedH, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.blockDiagonal_apply, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- The quadratic form of $\hat{\mathbf{H}}$ is the sum of those of $\mathbf{H}$ on the blocks. -/
private theorem dotProduct_dilatedH_mulVec_eq_sum (x : Fin n × Fin (k + 1) → ℝ) :
    x ⬝ᵥ (L.dilatedH *ᵥ x) = ∑ r, (fun j => x (j, r)) ⬝ᵥ (L.H *ᵥ fun j => x (j, r)) := by
  simp only [dotProduct, Fintype.sum_prod_type, L.dilatedH_mulVec_apply]
  exact Finset.sum_comm

/-- Every eigenvalue of $\hat{\mathbf{H}}$ is an eigenvalue of $\mathbf{H}$: if
$\hat{\mathbf{H}}\mathbf{u} = c\mathbf{u}$ with $\mathbf{u} \neq \mathbf{0}$, then
$c = \lambda_j(\mathbf{H})$ for some $j < n$. -/
theorem exists_eigenvalue_eq_of_dilatedH_mulVec_eq_smul {u : Fin n × Fin (k + 1) → ℝ} {c : ℝ}
    (hu : u ≠ 0) (h : L.dilatedH *ᵥ u = c • u) : ∃ j < n, eigenvalue L.H j = c := by
  obtain ⟨⟨i, r⟩, hir⟩ := Function.ne_iff.mp hu
  have hur : (fun j => u (j, r)) ≠ 0 := fun h0 => hir (congrFun h0 i)
  have hHu : L.H *ᵥ (fun j => u (j, r)) = c • fun j => u (j, r) := by
    funext j
    rw [← L.dilatedH_mulVec_apply, h]
    rfl
  obtain ⟨j, hj, hj'⟩ := L.isHermitian.exists_eigenvalue_eq_of_mulVec_eq_smul hur hHu
  exact ⟨j, by simpa using hj, hj'⟩

/-- There is at least one coordinate: $n \ge 1$ since $\mathbf{v}_1 \neq \mathbf{0}$. -/
theorem n_pos {n k : ℕ} (L : LanczosRun n k) : 0 < n := by
  by_contra h
  have hpos := L.norm_v_pos le_rfl L.k_pos
  have h0 : L.v 1 = 0 := funext fun i => absurd i.2 (by omega)
  rw [h0, WithLp.toLp_zero, norm_zero] at hpos
  exact lt_irrefl _ hpos

/-- **A residual bound for $\hat{\mathbf{H}}$ in the eigenvalues of $\mathbf{H}$**: for a unit
$\mathbf{x}$ and any $\mu$, some eigenvalue of $\mathbf{H}$ satisfies
$\lvert\lambda_j(\mathbf{H}) - \mu\rvert \le \|\hat{\mathbf{H}}\mathbf{x} - \mu\mathbf{x}\|$. -/
theorem exists_abs_eigenvalue_sub_le_norm_dilatedH_mulVec_sub {x : Fin n × Fin (k + 1) → ℝ}
    (hx1 : ‖WithLp.toLp 2 x‖ = 1) (μ : ℝ) :
    ∃ j < n, |eigenvalue L.H j - μ| ≤ ‖WithLp.toLp 2 (L.dilatedH *ᵥ x - μ • x)‖ := by
  have : Nonempty (Fin n × Fin (k + 1)) := ⟨(⟨0, L.n_pos⟩, 0)⟩
  obtain ⟨i, hi, hle⟩ := L.isHermitian_dilatedH.exists_abs_eigenvalue_sub_mul_norm_le x μ
  obtain ⟨u, hu1, hu⟩ := L.isHermitian_dilatedH.exists_norm_eq_one_and_mulVec_eq hi
  have hu0 : u ≠ 0 := fun h => by rw [h, WithLp.toLp_zero, norm_zero] at hu1; exact zero_ne_one hu1
  obtain ⟨j, hj, hj'⟩ := L.exists_eigenvalue_eq_of_dilatedH_mulVec_eq_smul hu0 hu
  rw [hx1, mul_one] at hle
  exact ⟨j, hj, hj' ▸ hle⟩

/-- The backward perturbation in the spectral norm: <!-- value lanczosBackwardFactor k -->
$\|\tilde{\mathbf{H}} - \hat{\mathbf{H}}\|_2 \le 2000k^4\varepsilon\|\mathbf{H}\|_2$. -/
theorem specNorm_backwardH_sub_dilatedH_le :
    specNorm (L.backwardH - L.dilatedH) ≤ lanczosBackwardFactor k * L.ε * specNorm L.H :=
  (specNorm_le_frobNorm _).trans L.frobNorm_backwardH_sub_dilatedH_le

/-- The backward perturbation on a unit vector. -/
private theorem norm_dilatedH_sub_backwardH_mulVec_le {x : Fin n × Fin (k + 1) → ℝ}
    (hx1 : ‖WithLp.toLp 2 x‖ = 1) :
    ‖WithLp.toLp 2 ((L.dilatedH - L.backwardH) *ᵥ x)‖ ≤
      lanczosBackwardFactor k * L.ε * specNorm L.H := by
  refine (norm_toLp_mulVec_le _ x).trans ?_
  rw [hx1, mul_one, specNorm_sub_comm]
  exact L.specNorm_backwardH_sub_dilatedH_le

/-- The Rayleigh bounds of $\hat{\mathbf{H}}$ are those of $\mathbf{H}$, above. -/
theorem dotProduct_dilatedH_mulVec_le (x : Fin n × Fin (k + 1) → ℝ) :
    x ⬝ᵥ (L.dilatedH *ᵥ x) ≤ eigenvalue L.H 0 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rw [L.dotProduct_dilatedH_mulVec_eq_sum, norm_toLp_sq_eq_sum_blocks, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  have h := L.isHermitian.re_quadForm_le_eigenvalue_zero_mul (fun j => x (j, r))
  simpa only [quadForm_def, star_trivial, RCLike.re_to_real] using h

/-- The Rayleigh bounds of $\hat{\mathbf{H}}$ are those of $\mathbf{H}$, below
($m + 1 = n$). -/
theorem eigenvalue_last_mul_le_dotProduct_dilatedH_mulVec {m : ℕ} (hm : m + 1 = n)
    (x : Fin n × Fin (k + 1) → ℝ) :
    eigenvalue L.H m * ‖WithLp.toLp 2 x‖ ^ 2 ≤ x ⬝ᵥ (L.dilatedH *ᵥ x) := by
  rw [L.dotProduct_dilatedH_mulVec_eq_sum, norm_toLp_sq_eq_sum_blocks, Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  have h := L.isHermitian.eigenvalue_last_mul_le_re_quadForm
    (by simpa using hm) (fun j => x (j, r))
  simpa only [quadForm_def, star_trivial, RCLike.re_to_real] using h

/-- **The spectrum of the backward model is near that of $\mathbf{H}$**: every eigenvalue of
$\tilde{\mathbf{H}}$ is within <!-- value lanczosBackwardFactor k -->
$2000k^4\varepsilon\|\mathbf{H}\|_2$ of an eigenvalue of
$\mathbf{H}$. No printed source; the maintainer's draft, `rem:wasserstein` (by Weyl's
inequality there). -/
theorem exists_abs_eigenvalue_backwardH_sub_eigenvalue_le {i : ℕ}
    (hi : i < Fintype.card (Fin n × Fin (k + 1))) :
    ∃ j < n, |eigenvalue L.backwardH i - eigenvalue L.H j| ≤
      lanczosBackwardFactor k * L.ε * specNorm L.H := by
  have : Nonempty (Fin n × Fin (k + 1)) := ⟨(⟨0, L.n_pos⟩, 0)⟩
  obtain ⟨x, hx1, hx⟩ := L.isHermitian_backwardH.exists_norm_eq_one_and_mulVec_eq hi
  obtain ⟨j, hj, hle⟩ := L.exists_abs_eigenvalue_sub_le_norm_dilatedH_mulVec_sub hx1
    (eigenvalue L.backwardH i)
  rw [← hx, ← Matrix.sub_mulVec] at hle
  exact ⟨j, hj, (abs_sub_comm _ _).trans_le
    (hle.trans (L.norm_dilatedH_sub_backwardH_mulVec_le hx1))⟩

/-- **Localization of stabilised Ritz values** (Paige): for a unit eigenpair
$\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$ of the computed tridiagonal matrix, some eigenvalue
$\lambda$ of $\mathbf{H}$ satisfies <!-- value lanczosBackwardFactor k -->
$$\lvert\theta - \lambda\rvert \le \beta_k\lvert y_{k-1}\rvert +
2000k^4\varepsilon\|\mathbf{H}\|_2 \,.$$
At a terminal last step ($\beta_k = 0$) this holds for every Ritz value.
No printed source; the maintainer's draft, `thm:stabilized`, states
$\lesssim_k \beta_k\lvert\mathbf{e}_k^{\mathsf{T}}\mathbf{y}\rvert + \varepsilon\|\mathbf{A}\|_2$;
[Paige1980, Theorem 3.1].
Result: paige-stabilized-ritz-values -/
theorem exists_abs_sub_eigenvalue_le_of_mulVec_eq_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ j < n, |θ - eigenvalue L.H j| ≤
      L.β k * |y L.lastIndex| + lanczosBackwardFactor k * L.ε * specNorm L.H := by
  set Q := L.dilatedBasis
  set x := Q *ᵥ y
  have hx1 : ‖WithLp.toLp 2 x‖ = 1 := by
    rw [L.hasOrthonormalCols_dilatedBasis.norm_toLp_mulVec, hy1]
  set w := L.dilatedBasisSucc.col (Fin.last k)
  have hAx : L.backwardH *ᵥ x = θ • x + (y L.lastIndex * L.β k) • w := by
    rw [Matrix.mulVec_mulVec, L.backwardH_mul_dilatedBasis, tridiagonalSucc,
      L.toLanczosData.mul_tridiagonalSucc, Matrix.add_mulVec, ← Matrix.mulVec_mulVec]
    change Q *ᵥ (L.tridiagonal *ᵥ y) + _ = _
    rw [hy, Matrix.mulVec_smul, Matrix.vecMulVec_mulVec, single_one_dotProduct, op_smul_eq_smul,
      smul_smul]
    rfl
  have hw : ‖WithLp.toLp 2 ((y L.lastIndex * L.β k) • w)‖ = L.β k * |y L.lastIndex| := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs,
      L.hasOrthonormalCols_dilatedBasisSucc.norm_toLp_col, mul_one, abs_mul,
      abs_of_nonneg (L.β_nonneg k le_rfl), mul_comm]
  obtain ⟨j, hj, hle⟩ := L.exists_abs_eigenvalue_sub_le_norm_dilatedH_mulVec_sub hx1 θ
  have hres : L.dilatedH *ᵥ x - θ • x =
      (L.dilatedH - L.backwardH) *ᵥ x + (y L.lastIndex * L.β k) • w := by
    rw [Matrix.sub_mulVec, hAx]
    abel
  rw [hres, WithLp.toLp_add] at hle
  refine ⟨j, hj, (abs_sub_comm _ _).trans_le (hle.trans ((norm_add_le _ _).trans ?_))⟩
  rw [hw]
  linarith [L.norm_dilatedH_sub_backwardH_mulVec_le hx1]

/-- A Ritz value is a Rayleigh quotient of $\hat{\mathbf{H}}$ up to the backward perturbation:
for a unit eigenpair $\mathbf{T}_k\mathbf{y} = \theta\mathbf{y}$ and
$\hat{\mathbf{x}} = \hat{\mathbf{V}}_k\mathbf{y}$, <!-- value lanczosBackwardFactor k -->
$$\lvert\hat{\mathbf{x}}^{\mathsf{T}}\hat{\mathbf{H}}\hat{\mathbf{x}} - \theta\rvert \le
2000k^4\varepsilon\|\mathbf{H}\|_2 \,.$$ -/
private theorem abs_dotProduct_dilatedH_mulVec_sub_le {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    |(L.dilatedBasis *ᵥ y) ⬝ᵥ (L.dilatedH *ᵥ (L.dilatedBasis *ᵥ y)) - θ| ≤
      lanczosBackwardFactor k * L.ε * specNorm L.H := by
  set Q := L.dilatedBasis
  set x := Q *ᵥ y
  have hx1 : ‖WithLp.toLp 2 x‖ = 1 := by
    rw [L.hasOrthonormalCols_dilatedBasis.norm_toLp_mulVec, hy1]
  have hθ : x ⬝ᵥ (L.backwardH *ᵥ x) = θ := by
    have hT : Qᵀ * (L.backwardH * Q) = L.tridiagonal := by
      rw [L.backwardH_mul_dilatedBasis, L.transpose_dilatedBasis_mul_dilatedBasisSucc_mul]
    have hyy : y ⬝ᵥ y = 1 := by
      rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, hy1, one_pow]
    calc x ⬝ᵥ (L.backwardH *ᵥ x) = y ⬝ᵥ ((Qᵀ * (L.backwardH * Q)) *ᵥ y) := by
          rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec y Qᵀ,
            Matrix.vecMul_transpose]
      _ = θ := by rw [hT, hy, dotProduct_smul, smul_eq_mul, hyy, mul_one]
  have h := norm_star_dotProduct_mulVec_le (L.dilatedH - L.backwardH) x x
  rw [star_trivial, Real.norm_eq_abs, hx1, one_mul, mul_one, Matrix.sub_mulVec, dotProduct_sub,
    hθ] at h
  exact h.trans ((specNorm_sub_comm _ _).trans_le L.specNorm_backwardH_sub_dilatedH_le)

/-- **Containment of the computed Ritz values, below** (Paige): every eigenvalue $\theta$ of the
computed tridiagonal matrix satisfies <!-- value lanczosBackwardFactor k -->
$\lambda_{\min}(\mathbf{H}) - \theta \le 2000k^4\varepsilon\|\mathbf{H}\|_2$, where
$\lambda_{\min}(\mathbf{H}) = \lambda_m(\mathbf{H})$, $m + 1 = n$.
No printed source; the maintainer's draft, `thm:containment`; [Paige1980, (3.48)].
Result: paige-ritz-containment -/
theorem eigenvalue_last_sub_le_of_mulVec_eq_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) {m : ℕ} (hm : m + 1 = n) :
    eigenvalue L.H m - θ ≤ lanczosBackwardFactor k * L.ε * specNorm L.H := by
  have hlow := L.eigenvalue_last_mul_le_dotProduct_dilatedH_mulVec hm (L.dilatedBasis *ᵥ y)
  rw [L.hasOrthonormalCols_dilatedBasis.norm_toLp_mulVec, hy1, one_pow, mul_one] at hlow
  linarith [(abs_le.mp (L.abs_dotProduct_dilatedH_mulVec_sub_le hy hy1)).2]

/-- **Containment of the computed Ritz values, above** (Paige): every eigenvalue $\theta$ of the
computed tridiagonal matrix satisfies <!-- value lanczosBackwardFactor k -->
$\theta - \lambda_{\max}(\mathbf{H}) \le 2000k^4\varepsilon\|\mathbf{H}\|_2$, where
$\lambda_{\max}(\mathbf{H}) = \lambda_0(\mathbf{H})$.
No printed source; the maintainer's draft, `thm:containment`; [Paige1980, (3.48)].
Result: paige-ritz-containment -/
theorem sub_eigenvalue_zero_le_of_mulVec_eq_smul {y : Fin k → ℝ} {θ : ℝ}
    (hy : L.tridiagonal *ᵥ y = θ • y) (hy1 : ‖WithLp.toLp 2 y‖ = 1) :
    θ - eigenvalue L.H 0 ≤ lanczosBackwardFactor k * L.ε * specNorm L.H := by
  have hup := L.dotProduct_dilatedH_mulVec_le (L.dilatedBasis *ᵥ y)
  rw [L.hasOrthonormalCols_dilatedBasis.norm_toLp_mulVec, hy1, one_pow, mul_one] at hup
  linarith [(abs_le.mp (L.abs_dotProduct_dilatedH_mulVec_sub_le hy hy1)).1]

/-- The quadratic forms of $f(\hat{\mathbf{H}})$ at the dilated start and of $f(\mathbf{H})$ at
$\bar{\mathbf{v}}_1$ agree: the spectral measure of $(\hat{\mathbf{H}}, \tilde{\mathbf{v}})$ is that
of $(\mathbf{H}, \bar{\mathbf{v}}_1)$. -/
theorem dotProduct_cfc_dilatedH_mulVec (f : ℝ → ℝ) :
    L.dilatedStart ⬝ᵥ (cfc f L.dilatedH *ᵥ L.dilatedStart) =
      L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) := by
  have hcfc' : cfc f L.dilatedH = Matrix.blockDiagonal fun _ => cfc f L.H :=
    cfc_blockDiagonal (fun _ => L.isHermitian) f
  rw [hcfc']
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Matrix.blockDiagonal_apply,
    dilatedStart, ite_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_comm, Fintype.sum_eq_single (0 : Fin (k + 1)) (fun r hr => by
    simp only [Fin.val_eq_zero_iff, if_neg hr, Finset.sum_const_zero])]
  simp only [Fin.val_zero, if_true]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Fintype.sum_eq_single (0 : Fin (k + 1)) (fun r hr => by
    simp only [Fin.val_eq_zero_iff, if_neg hr])]
  simp

/-- **The spectral measures are Wasserstein-close**: for every $1$-Lipschitz
$f$, <!-- value lanczosBackwardFactor k -->
$$\lvert\bar{\mathbf{v}}_1^{\mathsf{T}}f(\mathbf{H})\bar{\mathbf{v}}_1 -
\tilde{\mathbf{v}}^{\mathsf{T}}f(\tilde{\mathbf{H}})\tilde{\mathbf{v}}\rvert
\le 2000k^4\varepsilon\|\mathbf{H}\|_2 \,,$$
so the spectral measure of $(\mathbf{H}, \bar{\mathbf{v}}_1)$ and that of the backward model
$(\tilde{\mathbf{H}}, \tilde{\mathbf{v}})$, on which exact Lanczos computes $\mathbf{T}_k$, are
within that distance in $W_1$.
No printed source; the maintainer's draft, `rem:wasserstein`, bounds the difference by
$\sqrt{2k}\|\mathbf{\Delta}\|$ (through the rank of $\mathbf{\Delta}$); here directly by
$\|\mathbf{\Delta}\|_{\mathsf{F}}$.
Result: lanczos-spectral-measure-wasserstein -/
theorem abs_dotProduct_cfc_mulVec_sub_le {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    |L.normalizedV 1 ⬝ᵥ (cfc f L.H *ᵥ L.normalizedV 1) -
        L.dilatedStart ⬝ᵥ (cfc f L.backwardH *ᵥ L.dilatedStart)| ≤
      lanczosBackwardFactor k * L.ε * specNorm L.H := by
  have hs1 : ‖WithLp.toLp 2 L.dilatedStart‖ = 1 := by
    rw [← L.dilatedBasisSucc_col_zero]
    exact L.hasOrthonormalCols_dilatedBasisSucc.norm_toLp_col 0
  rw [← L.dotProduct_cfc_dilatedH_mulVec, ← dotProduct_sub, ← Matrix.sub_mulVec]
  have h := norm_star_dotProduct_mulVec_le (cfc f L.dilatedH - cfc f L.backwardH)
    L.dilatedStart L.dilatedStart
  rw [star_trivial, Real.norm_eq_abs, hs1, one_mul, mul_one] at h
  refine h.trans ((specNorm_le_frobNorm _).trans ?_)
  refine (L.isHermitian_dilatedH.frobNorm_cfc_sub_cfc_le L.isHermitian_backwardH hf).trans ?_
  rw [← frobNorm_neg, neg_sub]
  exact L.frobNorm_backwardH_sub_dilatedH_le

end LanczosRun

end NLAlib
