/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.BackwardSpectral

/-!
# The backward model of a normalised perturbed Lanczos recurrence

The Greenbaum-type backward model of `NLAlib/Krylov/FinitePrecision/Backward.lean` uses of a
finite-precision Lanczos run only its normalised data: a symmetric three-term datum
(`NLAlib.LanczosData`) whose vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$ are unit
vectors, with $\beta_j \ge 0$ and $\beta_j > 0$ before the last step, together with two numbers:
a bound $f$ on the recurrence residuals $\|\bar{\mathbf{f}}_j\|$ and a bound $p$ on the
adjacent inner products $\lvert\bar p_j\rvert$. This file states the model for that interface,
`NLAlib.NormalizedLanczosData`, with the bounds as hypotheses, so that it applies both to a
Lanczos run (`NLAlib.LanczosRun.toNormalizedLanczosData`) and to the Lanczos data of a
finite-precision conjugate gradient run (`NLAlib.CGRun.toNormalizedLanczosData`).

The bound is $22k^2 f + 17k\sqrt{k}\,p$, from
$\|\bar{\mathbf{F}}_k\|_{\mathsf{F}} \le \sqrt{k}f$ and the Frobenius Gram-commutator estimate
$\|\bar{\mathbf{M}}_k\|_{\mathsf{F}} \le 2\sqrt{k}p + 2kf$ (unit columns: no normalisation defect).
The shifted-stack estimate retains the orthonormality of the whole dilation. For a Lanczos run
with the additional horizon $k\varepsilon \le 1/100$
($f = 12k\varepsilon\|\mathbf{H}\|_2$, $p = 8k\varepsilon\|\mathbf{H}\|_2$), the model bound is
at most $400k^3\varepsilon\|\mathbf{H}\|_2$, within the registered factor $400k^3$.

## Main definitions

* `NLAlib.NormalizedLanczosData`: the interface.
* `NLAlib.normalizedBackwardBound`: the bound <!-- value normalizedBackwardBound k f p -->
  $22k^2f + 17k\sqrt{k} p$.
* `NLAlib.NormalizedLanczosData.backwardH`: the backward model.
* `NLAlib.LanczosRun.toNormalizedLanczosData`: a Lanczos run is an instance.

## Main results

* `NLAlib.NormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le`: the backward model.
* `NLAlib.NormalizedLanczosData.lanczosTridiagonal_backwardH_dilatedStart`: exact Lanczos on
  the model computes $\mathbf{T}_k$.
* `NLAlib.NormalizedLanczosData.spectrum_backwardH_subset_Icc`: Weyl localisation.
* `NLAlib.NormalizedLanczosData.spectrum_backwardH_subset_iUnion_Icc`: localization in a union
  of closed intervals about the input eigenvalues.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **Normalised Lanczos data**: a symmetric three-term datum (`NLAlib.LanczosData`) whose
vectors $\mathbf{v}_1, \dots, \mathbf{v}_{k+1}$ are unit vectors, with $\beta_j \ge 0$
($j \le k$) and $\beta_j > 0$ ($1 \le j < k$). The interface of the backward model: no relation
between vectors and coefficients is assumed, the residuals of the recurrence enter the theorems
as hypotheses. At a terminal last step ($\beta_k = 0$) $\mathbf{v}_{k+1}$ is any unit vector. -/
structure NormalizedLanczosData (n k : ℕ) extends LanczosData n k where
  /-- The vectors are unit vectors. -/
  norm_v : ∀ j, 1 ≤ j → j ≤ k + 1 → ‖WithLp.toLp 2 (v j)‖ = 1
  /-- The coefficients $\beta_j$ are nonnegative. -/
  β_nonneg : ∀ j ≤ k, 0 ≤ β j
  /-- No breakdown before the last step. -/
  β_pos : ∀ j, 1 ≤ j → j < k → 0 < β j

/-- **The bound of the normalised backward model**: <!-- value normalizedBackwardBound k f p -->
$22k^2f + 17k\sqrt{k} p$, for recurrence residuals at most $f$ and adjacent inner products at
most $p$ in absolute value. -/
noncomputable def normalizedBackwardBound (k : ℕ) (f p : ℝ) : ℝ :=
  22 * (k : ℝ) ^ 2 * f + 17 * k * Real.sqrt k * p

/-- The normalized backward bound is bounded by its former cubic estimate for nonnegative
residual and adjacent-inner-product bounds and at least one step. -/
theorem normalizedBackwardBound_le {k : ℕ} (hk : 1 ≤ k) {f p : ℝ}
    (hf : 0 ≤ f) (hp : 0 ≤ p) :
    normalizedBackwardBound k f p ≤ 102 * (k : ℝ) ^ 3 * f + 96 * (k : ℝ) ^ 2 * p := by
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsk : Real.sqrt (k : ℝ) ≤ k := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hk2 : (k : ℝ) ^ 2 ≤ k ^ 3 := by nlinarith
  unfold normalizedBackwardBound
  have h1 := mul_le_mul_of_nonneg_right hk2 hf
  have h2 := mul_le_mul_of_nonneg_right hsk (by positivity : 0 ≤ (k : ℝ) * p)
  nlinarith

namespace NormalizedLanczosData

variable {n k : ℕ} (D : NormalizedLanczosData n k)

/-- The **dilated matrix** $\mathbf{I}_{k+1} \otimes \mathbf{H}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => D.H

/-- The **dilated vectors** $\hat{\mathbf{V}}_{k+1}$: the orthonormal dilation of
$\mathbf{v}_1, \dots, \mathbf{v}_{k+1}$. -/
noncomputable def dilatedBasisSucc : Matrix (Fin n × Fin (k + 1)) (Fin (k + 1)) ℝ :=
  orthonormalDilation D.basisSucc

/-- The first $k$ dilated vectors $\hat{\mathbf{V}}_k$. -/
noncomputable def dilatedBasis : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  D.dilatedBasisSucc.submatrix id Fin.castSucc

/-- The **dilated start** $(\mathbf{v}_1, \mathbf{0}, \dots, \mathbf{0})$. -/
def dilatedStart : Fin n × Fin (k + 1) → ℝ :=
  fun x => if (x.2 : ℕ) = 0 then D.v 1 x.1 else 0

/-- The **residual of the dilated recurrence**
$\hat{\mathbf{E}} = \hat{\mathbf{H}}\hat{\mathbf{V}}_k - \hat{\mathbf{V}}_{k+1}
\underline{\mathbf{T}}_k$. -/
noncomputable def dilatedResidual : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  D.dilatedH * D.dilatedBasis - D.dilatedBasisSucc * D.tridiagonalSucc

/-- The **backward model** $\tilde{\mathbf{H}} = \hat{\mathbf{H}} + \mathbf{\Delta}$ with
$\mathbf{\Delta} = -\hat{\mathbf{E}}\hat{\mathbf{V}}_k^{\mathsf{T}} -
\hat{\mathbf{V}}_k\hat{\mathbf{E}}^{\mathsf{T}}(\mathbf{I} - \hat{\mathbf{V}}_k
\hat{\mathbf{V}}_k^{\mathsf{T}})$, the construction of `NLAlib.LanczosRun.backwardH`. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  D.dilatedH + (-(D.dilatedResidual * D.dilatedBasisᵀ) -
    D.dilatedBasis * D.dilatedResidualᵀ * (1 - D.dilatedBasis * D.dilatedBasisᵀ))

/-- The unit vectors as the hypothesis of the `NLAlib.LanczosData` backward model: the Gram
matrix of $\mathbf{V}_{k+1}$ has unit diagonal. -/
theorem transpose_basisSucc_mul_self_apply (j : Fin (k + 1)) :
    (D.basisSuccᵀ * D.basisSucc) j j = 1 :=
  D.toLanczosData.transpose_basisSucc_mul_self_apply_of_norm D.norm_v j

/-- The backward model is symmetric. -/
theorem transpose_backwardH : D.backwardHᵀ = D.backwardH := by
  exact D.toLanczosData.transpose_backwardH D.transpose_basisSucc_mul_self_apply

/-- The model recurrence: $\tilde{\mathbf{H}}\hat{\mathbf{V}}_k = \hat{\mathbf{V}}_{k+1}
\underline{\mathbf{T}}_k$. -/
theorem backwardH_mul_dilatedBasis :
    D.backwardH * D.dilatedBasis = D.dilatedBasisSucc * D.tridiagonalSucc := by
  exact D.toLanczosData.backwardH_mul_dilatedBasis D.transpose_basisSucc_mul_self_apply

/-- **The backward model of normalised Lanczos data**: if
$\|\bar{\mathbf{f}}_j\| \le f$ and $\lvert\bar p_j\rvert \le p$ for $j < k$, then

$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}
\le 22k^2 f + 17k\sqrt{k}p
\,.$$
No printed source. the maintainer's draft, `thm:greenbaum`, for Lanczos runs.
Result: lanczos-backward-model -/
theorem frobNorm_backwardH_sub_dilatedH_le {f p : ℝ}
    (hf : ∀ j < k, ‖WithLp.toLp 2 (D.recurrenceError j)‖ ≤ f)
    (hp : ∀ j < k, |D.adjacentInner j| ≤ p) :
    frobNorm (D.backwardH - D.dilatedH) ≤ normalizedBackwardBound k f p := by
  have hW := D.transpose_basisSucc_mul_self_apply
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hf0 : 0 ≤ f := (norm_nonneg _).trans (hf 0 D.k_pos)
  have hp0 : 0 ≤ p := (abs_nonneg _).trans (hp 0 D.k_pos)
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg _)
  have hV : frobNorm D.basis = Real.sqrt k := by
    have hcols : ∀ j : Fin k, ‖WithLp.toLp 2 (D.basis.col j)‖ = 1 := fun j =>
      D.norm_v ((j : ℕ) + 1) (by omega) (by omega)
    rw [← Real.sqrt_sq (frobNorm_nonneg _), frobNorm_sq_eq_sum_col]
    simp [hcols]
  have hF : frobNorm D.residual ≤ Real.sqrt k * f := by
    have hsq : frobNorm D.residual ^ 2 ≤ (Real.sqrt k * f) ^ 2 := by
      rw [frobNorm_sq_eq_sum_col, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
      calc ∑ j, ‖WithLp.toLp 2 (D.residual.col j)‖ ^ 2 ≤ ∑ _j : Fin k, f ^ 2 :=
            Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hf j j.2) 2
        _ = k * f ^ 2 := by simp
    exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq
  have hb : ∀ j < k, |D.β j| ≤ ∑ i ∈ Finset.range k, |D.β i| := fun j hj =>
    Finset.single_le_sum (f := fun i => |D.β i|) (fun i _ => abs_nonneg _) (Finset.mem_range.2 hj)
  have hg : ∀ i, |D.normSqDefect i| ≤ 0 := fun i => by
    simp [LanczosData.normSqDefect, D.norm_v ((i : ℕ) + 1) (by omega) (by omega)]
  have hG := D.frobNorm_gramCommutator_le hp hb hg
  rw [hV] at hG
  have hG' : frobNorm D.gramCommutator ≤ 2 * Real.sqrt k * p + 2 * k * f := by
    refine hG.trans ?_
    have := mul_le_mul_of_nonneg_left hF (Real.sqrt_nonneg (k : ℝ))
    nlinarith
  have hE := D.toLanczosData.frobNorm_dilatedResidual_le_of_frobNorm_gramCommutator_le hW hF hG'
  have h2 := D.toLanczosData.frobNorm_backwardH_sub_dilatedH_le_sqrt_two_mul hW
  change frobNorm (D.backwardH - D.dilatedH) ≤ Real.sqrt 2 * frobNorm D.dilatedResidual at h2
  change frobNorm D.dilatedResidual ≤ _ at hE
  have hss : Real.sqrt (k + 1) * Real.sqrt k ≤ 3 / 2 * k := by
    rw [← Real.sqrt_mul (by positivity), Real.sqrt_le_left (by positivity)]
    nlinarith
  refine h2.trans ?_
  rw [normalizedBackwardBound]
  have e1 : 2 * Real.sqrt (k + 1) * (Real.sqrt k * f) ≤ 2 * (3 / 2 * k) * f := by
    have := mul_le_mul_of_nonneg_right hss hf0
    nlinarith
  have hk2 : (k : ℝ) ≤ k ^ 2 := by nlinarith
  have hcoef : 4 * (k : ℝ) + 2 ≤ 6 * k := by linarith
  have e2 : (4 * (k : ℝ) + 2) * (2 * Real.sqrt k * p + 2 * k * f) ≤
      (6 * k) * (2 * Real.sqrt k * p + 2 * k * f) := by gcongr
  have e3 := mul_le_mul_of_nonneg_right hk2 hf0
  have hE' : frobNorm D.dilatedResidual ≤
      15 * (k : ℝ) ^ 2 * f + 12 * k * Real.sqrt k * p := by
    nlinarith only [hE, e1, e2, e3]
  have hs : Real.sqrt (2 : ℝ) ≤ 17 / 12 := by
    rw [Real.sqrt_le_left (by norm_num)]
    norm_num
  have hf' := mul_le_mul_of_nonneg_right (show Real.sqrt (2 : ℝ) * 15 ≤ 22 by linarith)
    (by positivity : 0 ≤ (k : ℝ) ^ 2 * f)
  have hp' := mul_le_mul_of_nonneg_right (show Real.sqrt (2 : ℝ) * 12 ≤ 17 by linarith)
    (by positivity : 0 ≤ (k : ℝ) * Real.sqrt k * p)
  have hE'' := mul_le_mul_of_nonneg_left hE' (Real.sqrt_nonneg 2)
  nlinarith only [hf', hp', hE'']

/-- **Exact Lanczos on the backward model computes the tridiagonal matrix**: $k$ steps of
`NLAlib.lanczosState` on $\tilde{\mathbf{H}}$ from $(\mathbf{v}_1, \mathbf{0}, \dots)$ give
$\mathbf{T}_k$. No hypothesis on the residuals. -/
theorem lanczosTridiagonal_backwardH_dilatedStart :
    lanczosTridiagonal D.backwardH D.dilatedStart k = D.tridiagonal := by
  exact LanczosData.lanczosTridiagonal_backwardH_dilatedStart
    D.transpose_basisSucc_mul_self_apply D.β_nonneg D.β_pos

/-- Exact Lanczos on the backward model computes the last coefficient $\beta_k$. -/
theorem lanczosState_backwardH_dilatedStart_beta :
    (lanczosState D.backwardH D.dilatedStart k).beta = D.β k := by
  exact LanczosData.lanczosState_backwardH_dilatedStart_beta
    D.transpose_basisSucc_mul_self_apply D.β_nonneg D.β_pos

/-- Exact Lanczos on the backward model computes the dilated vectors: `lanczosMatrix` of
$\tilde{\mathbf{H}}$ from the dilated start is $\hat{\mathbf{V}}_k$. -/
theorem lanczosMatrix_backwardH_dilatedStart :
    lanczosMatrix D.backwardH D.dilatedStart k = D.dilatedBasis := by
  exact LanczosData.lanczosMatrix_backwardH_dilatedStart
    D.transpose_basisSucc_mul_self_apply D.β_nonneg D.β_pos

/-- **Weyl localisation of the model**: if the spectrum of $\mathbf{H}$ lies in $[a, a']$ and
$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}} \le c$, the spectrum of
$\tilde{\mathbf{H}}$ lies in $[a - c, a' + c]$. The form the conjugate gradient analysis uses
(positive definiteness and the condition number of the model). -/
theorem spectrum_backwardH_subset_Icc {a a' c : ℝ} (hs : spectrum ℝ D.H ⊆ Set.Icc a a')
    (hc : frobNorm (D.backwardH - D.dilatedH) ≤ c) :
    spectrum ℝ D.backwardH ⊆ Set.Icc (a - c) (a' + c) := by
  exact D.toLanczosData.spectrum_backwardH_subset_Icc D.transpose_basisSucc_mul_self_apply hs hc

/-- The block dilation retains every set containing the input spectrum. -/
theorem spectrum_dilatedH_subset {S : Set ℝ} (hs : spectrum ℝ D.H ⊆ S) :
    spectrum ℝ D.dilatedH ⊆ S :=
  D.toLanczosData.spectrum_dilatedH_subset hs

/-- Every backward eigenvalue is within a certified Frobenius distance of an input
 eigenvalue, for normalized three-term data. -/
theorem exists_abs_eigenvalue_backwardH_sub_eigenvalue_le {δ : ℝ}
    (hgap : frobNorm (D.backwardH - D.dilatedH) ≤ δ) {i : ℕ}
    (hi : i < Fintype.card (Fin n × Fin (k + 1))) :
    ∃ j < n, |eigenvalue D.backwardH i - eigenvalue D.H j| ≤ δ :=
  D.toLanczosData.exists_abs_eigenvalue_backwardH_sub_eigenvalue_le
    D.transpose_basisSucc_mul_self_apply hgap hi

/-- The backward spectrum lies in the union of closed intervals of radius $\delta$ about
 the valid input eigenvalues when the Frobenius backward error is at most $\delta$. -/
theorem spectrum_backwardH_subset_iUnion_Icc {δ : ℝ}
    (hgap : frobNorm (D.backwardH - D.dilatedH) ≤ δ) :
    spectrum ℝ D.backwardH ⊆ ⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue D.H i - δ) (eigenvalue D.H i + δ) :=
  D.toLanczosData.spectrum_backwardH_subset_iUnion_Icc
    D.transpose_basisSucc_mul_self_apply hgap

/-- **The spectral measures are Wasserstein-close**: for every $1$-Lipschitz $f$,
$\lvert\mathbf{v}_1^{\mathsf{T}}f(\mathbf{H})\mathbf{v}_1 -
\tilde{\mathbf{v}}^{\mathsf{T}}f(\tilde{\mathbf{H}})\tilde{\mathbf{v}}\rvert \le
\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{H}\|_{\mathsf{F}}$. -/
theorem abs_dotProduct_cfc_mulVec_sub_le {f : ℝ → ℝ} (hf : LipschitzWith 1 f) :
    |D.v 1 ⬝ᵥ (cfc f D.H *ᵥ D.v 1) - D.dilatedStart ⬝ᵥ (cfc f D.backwardH *ᵥ D.dilatedStart)| ≤
      frobNorm (D.backwardH - D.dilatedH) := by
  exact D.toLanczosData.abs_dotProduct_cfc_mulVec_sub_le_frobNorm
    D.transpose_basisSucc_mul_self_apply hf

end NormalizedLanczosData

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- **A Lanczos run as normalised data**: the normalised run `NLAlib.LanczosRun.normalized`
(unit vectors, the terminal vector $\bar{\mathbf{v}}_{k+1} = \bar{\mathbf{v}}_1$). -/
noncomputable def toNormalizedLanczosData : NormalizedLanczosData n k :=
  { L.normalized with
    norm_v := fun _ h1 h2 => L.norm_normalizedV h1 h2
    β_nonneg := L.β_nonneg
    β_pos := L.β_pos }

/-- **The Lanczos backward model as an instance**
(assuming $k\varepsilon \le 1/100$): the model of the normalised data is
within <!-- value lanczosBackwardFactor k --> $400k^3\varepsilon\|\mathbf{H}\|_2$ of
$\mathbf{I}_{k+1} \otimes \mathbf{H}$, the statement of
`NLAlib.LanczosRun.frobNorm_backwardH_sub_dilatedH_le` recovered from the interface. -/
theorem frobNorm_toNormalizedLanczosData_backwardH_sub_dilatedH_le
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100) :
    frobNorm (L.toNormalizedLanczosData.backwardH - L.toNormalizedLanczosData.dilatedH) ≤
      lanczosBackwardFactor k * L.ε * specNorm L.H := by
  exact L.frobNorm_backwardH_sub_dilatedH_le hsmall

/-- The two constructions agree: the backward model of the run is that of its normalised
data. After the refactor `NLAlib.LanczosRun.backwardH` is defined this way and this is `rfl`. -/
theorem backwardH_eq_toNormalizedLanczosData_backwardH :
    L.backwardH = L.toNormalizedLanczosData.backwardH := by
  rfl

end LanczosRun

end NLAlib
