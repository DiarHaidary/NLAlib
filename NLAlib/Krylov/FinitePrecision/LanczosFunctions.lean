/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.BackwardSpectral
public import NLAlib.Krylov.Functions.LanczosFA
public import NLAlib.Polynomial.Approximation.Markov

/-!
# Physical matrix function vectors from finite precision Lanczos

Summing the blocks of the orthonormal backward dilation recovers the physical normalized
basis. This connects exact matrix function approximation on the backward model to the
physical computed vectors. The small matrix functional calculus and final multiplication
in the output definitions are exact postprocessing of a finite precision recurrence.

## Main results

* `NLAlib.LanczosRun.normalizedFunctionApprox_eq_blockSumMatrix_mulVec_lanczosFA`:
  the physical normalized output is the collapse of the exact backward output.
* `NLAlib.LanczosRun.norm_cfc_mulVec_sub_normalizedFunctionApprox_le_of_isUniformApproxOn`:
  physical vector approximation using polynomial stability on a common spectral interval.
* `NLAlib.LanczosRun.norm_cfc_mulVec_sub_functionApprox_le_of_precision`:
  a bounded-function guarantee under an explicit polynomial precision budget.
* `NLAlib.LanczosRun.norm_cfc_mulVec_sub_functionApprox_le_of_isUniformApproxOn`:
  a compositional physical basis bound with a scalar polynomial Lipschitz coefficient.
* `NLAlib.LanczosRun.norm_cfc_mulVec_sub_smul_functionApprox_le_of_precision`:
  the bounded-function approximation theorem for the scaled physical computed output.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix MatrixOrder NNReal
open Polynomial

/-- The approximation multiplier for bounded-function Lanczos is
currently <!-- value lanczosFunctionApproxFactor k --> $4k$.
This is the multiplier proved for the local recurrence model and its explicit precision budget;
[MuscoMuscoSidford2018, Theorem 2.1] uses $7k$ with a different implementation and budget. -/
noncomputable irreducible_def lanczosFunctionApproxFactor (k : ℕ) : ℝ := 4 * (k : ℝ)

/-- The finite precision function approximation multiplier is nonnegative. -/
theorem lanczosFunctionApproxFactor_nonneg (k : ℕ) :
    0 ≤ lanczosFunctionApproxFactor k := by
  rw [lanczosFunctionApproxFactor_def]
  positivity

/-- The function approximation multiplier is at most four times the iteration count. -/
theorem lanczosFunctionApproxFactor_le (k : ℕ) : lanczosFunctionApproxFactor k ≤ 4 * k := by
  rw [lanczosFunctionApproxFactor_def]

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The physical matrix function vector using the normalized computed basis:
$\mathsf{normalizedFunctionApprox}(L,f) := \bar{\mathbf{V}}_k f(\mathbf{T}_k)\mathbf{e}_0$.
The small matrix function and final multiplication are exact postprocessing.
Algorithm: lanczos (specification) -/
noncomputable def normalizedFunctionApprox (f : ℝ → ℝ) : Fin n → ℝ :=
  L.normalized.basis *ᵥ (cfc f L.tridiagonal *ᵥ Pi.single ⟨0, L.k_pos⟩ 1)

/-- The physical matrix function vector using the computed basis:
$\mathsf{functionApprox}(L,f) := \mathbf{V}_k f(\mathbf{T}_k)\mathbf{e}_0$.
The small matrix function and final multiplication are exact postprocessing.
Algorithm: lanczos (specification) -/
noncomputable def functionApprox (f : ℝ → ℝ) : Fin n → ℝ :=
  L.basis *ᵥ (cfc f L.tridiagonal *ᵥ Pi.single ⟨0, L.k_pos⟩ 1)

/-- Summing the blocks of the dilated basis recovers the normalized physical basis. -/
theorem blockSumMatrix_mul_dilatedBasis :
    blockSumMatrix (Fin n) (Fin (k + 1)) ℝ * L.dilatedBasis = L.normalized.basis := by
  have h := blockSumMatrix_mul_orthonormalDilation L.normalized.basisSucc
  ext i j
  exact congrFun (congrFun h i) j.castSucc

/-- The dilated start has unit norm. -/
theorem norm_dilatedStart : ‖WithLp.toLp 2 L.dilatedStart‖ = 1 := by
  rw [← L.dilatedBasisSucc_col_zero]
  exact L.hasOrthonormalCols_dilatedBasisSucc.norm_toLp_col 0

/-- The physical normalized output is the sum of the blocks of exact Lanczos on the
backward matrix. -/
theorem normalizedFunctionApprox_eq_blockSumMatrix_mulVec_lanczosFA (f : ℝ → ℝ) :
    L.normalizedFunctionApprox f = blockSumMatrix (Fin n) (Fin (k + 1)) ℝ *ᵥ
      lanczosFA L.backwardH f L.dilatedStart k := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero L.k_pos.ne'
  rw [L.isHermitian_backwardH.lanczosFA_eq_lanczosMatrix,
    L.lanczosTridiagonal_backwardH_dilatedStart, L.lanczosMatrix_backwardH_dilatedStart,
    L.norm_dilatedStart, RCLike.ofReal_one, one_smul, Matrix.mulVec_mulVec,
    L.blockSumMatrix_mul_dilatedBasis]
  rfl

/-- The physical normalized output is linear in the scalar function. -/
theorem normalizedFunctionApprox_sub (f g : ℝ → ℝ) :
    L.normalizedFunctionApprox (fun x => f x - g x) =
      L.normalizedFunctionApprox f - L.normalizedFunctionApprox g := by
  rw [L.normalizedFunctionApprox_eq_blockSumMatrix_mulVec_lanczosFA,
    lanczosFA_sub, Matrix.mulVec_sub,
    ← L.normalizedFunctionApprox_eq_blockSumMatrix_mulVec_lanczosFA,
    ← L.normalizedFunctionApprox_eq_blockSumMatrix_mulVec_lanczosFA]

/-- Collapsing the unperturbed dilated matrix function at the start gives the original
matrix function vector. -/
theorem blockSumMatrix_mulVec_cfc_dilatedH (f : ℝ → ℝ) :
    blockSumMatrix (Fin n) (Fin (k + 1)) ℝ *ᵥ
      (cfc f L.dilatedH *ᵥ L.dilatedStart) = cfc f L.H *ᵥ L.normalizedV 1 := by
  have hcf : cfc f L.dilatedH = Matrix.blockDiagonal fun _ : Fin (k + 1) => cfc f L.H :=
    cfc_blockDiagonal (fun _ => L.isHermitian) f
  have hstart : blockSumMatrix (Fin n) (Fin (k + 1)) ℝ *ᵥ L.dilatedStart =
      L.normalizedV 1 := by
    rw [blockSumMatrix_mulVec]
    ext i
    simp only [dilatedStart, Fin.val_eq_zero_iff, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  rw [hcf, Matrix.mulVec_mulVec, blockSumMatrix_mul_blockDiagonal,
    ← Matrix.mulVec_mulVec, hstart]

/-- The unperturbed dilated spectrum is contained in any set containing the original spectrum. -/
theorem spectrum_dilatedH_subset {s : Set ℝ} (hs : spectrum ℝ L.H ⊆ s) :
    spectrum ℝ L.dilatedH ⊆ s := by
  exact L.normalized.spectrum_dilatedH_subset hs

/-- The computed tridiagonal is the compression of the backward matrix to its dilated basis. -/
theorem conjTranspose_dilatedBasis_mul_backwardH_mul :
    L.dilatedBasisᴴ * L.backwardH * L.dilatedBasis = L.tridiagonal := by
  rw [Matrix.mul_assoc, L.backwardH_mul_dilatedBasis,
    Matrix.conjTranspose_eq_transpose_of_trivial,
    L.transpose_dilatedBasis_mul_dilatedBasisSucc_mul]

/-- The tridiagonal spectrum stays inside an interval containing the backward spectrum. -/
theorem spectrum_tridiagonal_subset_Icc {a a' : ℝ}
    (hs : spectrum ℝ L.backwardH ⊆ Set.Icc a a') :
    spectrum ℝ L.tridiagonal ⊆ Set.Icc a a' := by
  rw [← L.conjTranspose_dilatedBasis_mul_backwardH_mul]
  exact L.isHermitian_backwardH.spectrum_conjTranspose_mul_mul_subset_Icc hs
    L.hasOrthonormalCols_dilatedBasis

/-- A bounded scalar function gives a bounded physical normalized output. -/
theorem norm_normalizedFunctionApprox_le {a a' M : ℝ} {f : ℝ → ℝ}
    (hs : spectrum ℝ L.backwardH ⊆ Set.Icc a a') (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc a a', |f x| ≤ M) :
    ‖WithLp.toLp 2 (L.normalizedFunctionApprox f)‖ ≤ Real.sqrt (k + 1) * M := by
  have hP : specNorm (blockSumMatrix (Fin n) (Fin (k + 1)) ℝ) ≤ Real.sqrt (k + 1) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      (specNorm_blockSumMatrix_le (ι := Fin n) (κ := Fin (k + 1)) (𝕜 := ℝ))
  have hT : L.tridiagonal.IsHermitian := by
    rw [← L.conjTranspose_dilatedBasis_mul_backwardH_mul]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ L.isHermitian_backwardH
  have hsmall : ‖WithLp.toLp 2 (cfc f L.tridiagonal *ᵥ Pi.single ⟨0, L.k_pos⟩ 1)‖ ≤ M := by
    have h := norm_toLp_mulVec_le (cfc f L.tridiagonal) (Pi.single ⟨0, L.k_pos⟩ 1)
    rw [PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] at h
    exact h.trans (hT.specNorm_cfc_le hM fun x hx =>
      hf x (L.spectrum_tridiagonal_subset_Icc hs hx))
  unfold normalizedFunctionApprox
  rw [← L.blockSumMatrix_mul_dilatedBasis, ← Matrix.mulVec_mulVec]
  refine (norm_toLp_mulVec_le _ _).trans ?_
  rw [L.hasOrthonormalCols_dilatedBasis.norm_toLp_mulVec]
  exact mul_le_mul hP hsmall (norm_nonneg _) (Real.sqrt_nonneg _)

/-- For a polynomial of degree below the step count, the normalized physical output is
the collapse of the polynomial of the backward matrix at its starting vector. -/
theorem normalizedFunctionApprox_eval {p : ℝ[X]} (hp : p.degree < k) :
    L.normalizedFunctionApprox (fun x => p.eval x) =
      blockSumMatrix (Fin n) (Fin (k + 1)) ℝ *ᵥ
        (cfc (fun x => p.eval x) L.backwardH *ᵥ L.dilatedStart) := by
  rw [L.normalizedFunctionApprox_eq_blockSumMatrix_mulVec_lanczosFA,
    L.isHermitian_backwardH.lanczosFA_eval L.dilatedStart hp,
    L.isHermitian_backwardH.cfc_eq_aeval_of_forall_eval_eq (fun _ _ => rfl)]

/-- The Frobenius norm of the correction from computed to normalized physical columns is
at most the accuracy parameter times the square root of the number of columns. -/
theorem frobNorm_basis_sub_normalized_basis_le :
    frobNorm (L.basis - L.normalized.basis) ≤ Real.sqrt k * L.ε := by
  have hcol : ∀ j : Fin k,
      ‖WithLp.toLp 2 ((L.basis - L.normalized.basis).col j)‖ ≤ L.ε := by
    intro j
    exact L.norm_v_sub_normalizedV_le (by omega) (by omega)
  apply (sq_le_sq₀ (frobNorm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) L.ε_nonneg)).mp
  rw [frobNorm_sq_eq_sum_col, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
  calc _ ≤ ∑ _j : Fin k, L.ε ^ 2 :=
      Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcol j) 2
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Polynomial evaluation on the physical normalized basis is stable under the backward
perturbation, with its scalar Lipschitz coefficient on a common spectral set. -/
theorem norm_cfc_mulVec_sub_normalizedFunctionApprox_eval_le {s : Set ℝ}
    {p : ℝ[X]} (hp : p.degree < k) {ℓ : ℝ≥0}
    (hs : spectrum ℝ L.H ⊆ s) (hback : spectrum ℝ L.backwardH ⊆ s)
    (hpoly : LipschitzOnWith ℓ (fun x => p.eval x) s) :
    ‖WithLp.toLp 2 (cfc (fun x => p.eval x) L.H *ᵥ L.normalizedV 1 -
      L.normalizedFunctionApprox (fun x => p.eval x))‖ ≤
      Real.sqrt (k + 1) * ℓ * frobNorm (L.backwardH - L.dilatedH) := by
  have hP : specNorm (blockSumMatrix (Fin n) (Fin (k + 1)) ℝ) ≤ Real.sqrt (k + 1) := by
    simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] using
      (specNorm_blockSumMatrix_le (ι := Fin n) (κ := Fin (k + 1)) (𝕜 := ℝ))
  rw [L.normalizedFunctionApprox_eval hp, ← L.blockSumMatrix_mulVec_cfc_dilatedH,
    ← Matrix.mulVec_sub, ← Matrix.sub_mulVec]
  have hpΔ := L.isHermitian_dilatedH.frobNorm_cfc_sub_cfc_le_of_lipschitzOnWith
    L.isHermitian_backwardH (L.spectrum_dilatedH_subset hs) hback hpoly
  rw [frobNorm_sub_comm L.dilatedH L.backwardH] at hpΔ
  calc _ ≤ specNorm (blockSumMatrix (Fin n) (Fin (k + 1)) ℝ) *
        ‖WithLp.toLp 2 ((cfc (fun x => p.eval x) L.dilatedH -
          cfc (fun x => p.eval x) L.backwardH) *ᵥ L.dilatedStart)‖ := norm_toLp_mulVec_le _ _
    _ ≤ Real.sqrt (k + 1) *
        (specNorm (cfc (fun x => p.eval x) L.dilatedH -
          cfc (fun x => p.eval x) L.backwardH) * ‖WithLp.toLp 2 L.dilatedStart‖) :=
      mul_le_mul hP (norm_toLp_mulVec_le _ _)
        (norm_nonneg _) (Real.sqrt_nonneg _)
    _ ≤ _ := by
      rw [L.norm_dilatedStart, mul_one, mul_assoc]
      exact mul_le_mul_of_nonneg_left ((specNorm_le_frobNorm _).trans hpΔ)
        (Real.sqrt_nonneg _)

/-- **Physical Lanczos polynomial approximation bound.** A finite precision run with original
and backward spectra in $[a,a']$, and a polynomial $p$ of degree below $k$ approximating $f$
uniformly there to error $\delta$, satisfies
$$\|f(\mathbf{H})\bar{\mathbf{v}}_1 - \mathsf{normalizedFunctionApprox}(L,f)\| \le
(1+\sqrt{k+1})\delta + \sqrt{k+1}\ell
\|\widetilde{\mathbf{H}}-\widehat{\mathbf{H}}\|_{\mathsf{F}}\,,$$
where $\ell$ is any Lipschitz coefficient of $p$ on the interval. No regularity of $f$ is
assumed. The small matrix function and final multiplication are exact postprocessing.
No printed source; compared with [MuscoMuscoSidford2018, Theorem 2.1], this exposes the
polynomial stability term and uses the library's local recurrence model.
Result: lanczos-finite-precision-function-vector -/
theorem norm_cfc_mulVec_sub_normalizedFunctionApprox_le_of_isUniformApproxOn
    {a a' : ℝ} {f : ℝ → ℝ} {p : ℝ[X]} {δ : ℝ} {ℓ : ℝ≥0}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hback : spectrum ℝ L.backwardH ⊆ Set.Icc a a')
    (hp : p.degree < k)
    (hpoly : LipschitzOnWith ℓ (fun x => p.eval x) (Set.Icc a a'))
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') δ) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ L.normalizedV 1 - L.normalizedFunctionApprox f)‖ ≤
      (1 + Real.sqrt (k + 1)) * δ +
        Real.sqrt (k + 1) * ℓ * frobNorm (L.backwardH - L.dilatedH) := by
  let g : ℝ → ℝ := fun x => f x - p.eval x
  have hδ : 0 ≤ δ := by
    have hn : 0 < Fintype.card (Fin n) := by
      simpa only [Fintype.card_fin] using L.n_pos
    exact happ.nonneg ⟨_, hs (L.isHermitian.eigenvalue_mem_spectrum hn)⟩
  have hg : ∀ x ∈ Set.Icc a a', |g x| ≤ δ := fun x hx => by
    simpa only [g, Real.dist_eq, abs_sub_comm] using happ.apply hx
  have htail : ‖WithLp.toLp 2 (cfc g L.H *ᵥ L.normalizedV 1)‖ ≤ δ := by
    have h := norm_toLp_mulVec_le (cfc g L.H) (L.normalizedV 1)
    rw [L.norm_normalizedV (by omega) (by omega), mul_one] at h
    exact h.trans (L.isHermitian.specNorm_cfc_le hδ fun x hx => hg x (hs hx))
  have hphysical := L.norm_normalizedFunctionApprox_le hback hδ hg
  have hpolynomial := L.norm_cfc_mulVec_sub_normalizedFunctionApprox_eval_le hp hs hback hpoly
  have heq : cfc f L.H *ᵥ L.normalizedV 1 - L.normalizedFunctionApprox f =
      cfc g L.H *ᵥ L.normalizedV 1 +
        (cfc (fun x => p.eval x) L.H *ᵥ L.normalizedV 1 -
          L.normalizedFunctionApprox (fun x => p.eval x)) - L.normalizedFunctionApprox g := by
    rw [show g = (fun x => f x - p.eval x) from rfl,
      cfc_sub f (fun x => p.eval x) L.H (L.H.finite_real_spectrum.continuousOn _)
        (L.H.finite_real_spectrum.continuousOn _), Matrix.sub_mulVec,
      L.normalizedFunctionApprox_sub]
    abel
  rw [heq, WithLp.toLp_sub, WithLp.toLp_add]
  calc _ ≤ (‖WithLp.toLp 2 (cfc g L.H *ᵥ L.normalizedV 1)‖ +
        ‖WithLp.toLp 2 (cfc (fun x => p.eval x) L.H *ᵥ L.normalizedV 1 -
          L.normalizedFunctionApprox (fun x => p.eval x))‖) +
        ‖WithLp.toLp 2 (L.normalizedFunctionApprox g)‖ :=
      (norm_sub_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := by linarith

/-- Using the computed physical columns rather than their normalized versions changes the
matrix function vector by at most $\sqrt{k}\varepsilon M$ when the scalar function is bounded
by $M$ on an interval containing the backward spectrum. -/
theorem norm_normalizedFunctionApprox_sub_functionApprox_le {a a' M : ℝ} {f : ℝ → ℝ}
    (hs : spectrum ℝ L.backwardH ⊆ Set.Icc a a') (hM : 0 ≤ M)
    (hf : ∀ x ∈ Set.Icc a a', |f x| ≤ M) :
    ‖WithLp.toLp 2 (L.normalizedFunctionApprox f - L.functionApprox f)‖ ≤
      Real.sqrt k * L.ε * M := by
  have hT : L.tridiagonal.IsHermitian := by
    rw [← L.conjTranspose_dilatedBasis_mul_backwardH_mul]
    exact Matrix.isHermitian_conjTranspose_mul_mul _ L.isHermitian_backwardH
  have hsmall : ‖WithLp.toLp 2 (cfc f L.tridiagonal *ᵥ Pi.single ⟨0, L.k_pos⟩ 1)‖ ≤ M := by
    have h := norm_toLp_mulVec_le (cfc f L.tridiagonal) (Pi.single ⟨0, L.k_pos⟩ 1)
    rw [PiLp.toLp_single, PiLp.norm_single, norm_one, mul_one] at h
    exact h.trans (hT.specNorm_cfc_le hM fun x hx =>
      hf x (L.spectrum_tridiagonal_subset_Icc hs hx))
  unfold normalizedFunctionApprox functionApprox
  rw [← Matrix.sub_mulVec]
  refine (norm_toLp_mulVec_le _ _).trans ?_
  have hspec : specNorm (L.normalized.basis - L.basis) ≤ Real.sqrt k * L.ε := by
    exact (specNorm_le_frobNorm _).trans
      ((frobNorm_sub_comm _ _).trans_le L.frobNorm_basis_sub_normalized_basis_le)
  exact mul_le_mul hspec hsmall (norm_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) L.ε_nonneg)

/-- **Computed physical Lanczos polynomial approximation bound.** For original and backward
spectra in $[a,a']$, a degree-below-$k$ polynomial approximating $f$ to error $\delta$ there,
with scalar Lipschitz coefficient $\ell$, gives
$$\|f(\mathbf{H})\bar{\mathbf{v}}_1 - \mathsf{functionApprox}(L,f)\| \le
(1+\sqrt{k+1})\delta + \sqrt{k+1}\ell
\|\widetilde{\mathbf{H}}-\widehat{\mathbf{H}}\|_{\mathsf{F}} +
\sqrt{k}\varepsilon M\,,$$
where $\lvert f\rvert\le M$ on the interval. This uses the physical computed basis, with
exact small matrix functional calculus and final multiplication. No regularity of $f$ is assumed.
No printed source; the comparison with [MuscoMuscoSidford2018, Theorem 2.1] is at the level
of polynomial approximation and a polynomial precision coefficient, not its implementation.
Result: lanczos-finite-precision-computed-function-vector -/
theorem norm_cfc_mulVec_sub_functionApprox_le_of_isUniformApproxOn
    {a a' M : ℝ} {f : ℝ → ℝ} {p : ℝ[X]} {δ : ℝ} {ℓ : ℝ≥0}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hback : spectrum ℝ L.backwardH ⊆ Set.Icc a a')
    (hp : p.degree < k)
    (hpoly : LipschitzOnWith ℓ (fun x => p.eval x) (Set.Icc a a'))
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') δ)
    (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc a a', |f x| ≤ M) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ L.normalizedV 1 - L.functionApprox f)‖ ≤
      (1 + Real.sqrt (k + 1)) * δ +
        Real.sqrt (k + 1) * ℓ * frobNorm (L.backwardH - L.dilatedH) +
          Real.sqrt k * L.ε * M := by
  have h := L.norm_cfc_mulVec_sub_normalizedFunctionApprox_le_of_isUniformApproxOn
    hs hback hp hpoly happ
  have hraw := L.norm_normalizedFunctionApprox_sub_functionApprox_le hback hM hf
  have heq : cfc f L.H *ᵥ L.normalizedV 1 - L.functionApprox f =
      (cfc f L.H *ᵥ L.normalizedV 1 - L.normalizedFunctionApprox f) +
        (L.normalizedFunctionApprox f - L.functionApprox f) := by abel
  rw [heq, WithLp.toLp_add]
  exact (norm_add_le _ _).trans (add_le_add h hraw)

/-- Scaling the physical computed-basis bound by the norm of the starting vector gives
the usual Lanczos matrix function output. The initial direction is specified explicitly,
including the zero-vector case. -/
theorem norm_cfc_mulVec_sub_smul_functionApprox_le_of_isUniformApproxOn
    {a a' M : ℝ} {f : ℝ → ℝ} {p : ℝ[X]} {δ : ℝ} {ℓ : ℝ≥0}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hback : spectrum ℝ L.backwardH ⊆ Set.Icc a a')
    (hp : p.degree < k)
    (hpoly : LipschitzOnWith ℓ (fun x => p.eval x) (Set.Icc a a'))
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') δ)
    (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc a a', |f x| ≤ M)
    (b : Fin n → ℝ) (hb : b = ‖WithLp.toLp 2 b‖ • L.normalizedV 1) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ b - ‖WithLp.toLp 2 b‖ • L.functionApprox f)‖ ≤
      ((1 + Real.sqrt (k + 1)) * δ +
        Real.sqrt (k + 1) * ℓ * frobNorm (L.backwardH - L.dilatedH) +
          Real.sqrt k * L.ε * M) * ‖WithLp.toLp 2 b‖ := by
  have h := L.norm_cfc_mulVec_sub_functionApprox_le_of_isUniformApproxOn
    hs hback hp hpoly happ hM hf
  have hlin := congrArg (fun x => cfc f L.H *ᵥ x) hb
  rw [Matrix.mulVec_smul] at hlin
  rw [hlin, ← smul_sub, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

/-- A certified error in the final returned vector adds to the computed physical basis bound.
The residual is measured after the small matrix function, basis multiplication and scaling,
so it can account for all three postprocessing stages. -/
theorem norm_cfc_mulVec_sub_le_of_norm_sub_smul_functionApprox_le
    {a a' M : ℝ} {f : ℝ → ℝ} {p : ℝ[X]} {δ ζ : ℝ} {ℓ : ℝ≥0}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hback : spectrum ℝ L.backwardH ⊆ Set.Icc a a')
    (hp : p.degree < k)
    (hpoly : LipschitzOnWith ℓ (fun x => p.eval x) (Set.Icc a a'))
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') δ)
    (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc a a', |f x| ≤ M)
    (b : Fin n → ℝ) (hb : b = ‖WithLp.toLp 2 b‖ • L.normalizedV 1)
    (y : Fin n → ℝ)
    (hy : ‖WithLp.toLp 2 (‖WithLp.toLp 2 b‖ • L.functionApprox f - y)‖ ≤ ζ) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ b - y)‖ ≤
      ((1 + Real.sqrt (k + 1)) * δ +
        Real.sqrt (k + 1) * ℓ * frobNorm (L.backwardH - L.dilatedH) +
          Real.sqrt k * L.ε * M) * ‖WithLp.toLp 2 b‖ + ζ := by
  have h := L.norm_cfc_mulVec_sub_smul_functionApprox_le_of_isUniformApproxOn
    hs hback hp hpoly happ hM hf b hb
  have heq : cfc f L.H *ᵥ b - y =
      (cfc f L.H *ᵥ b - ‖WithLp.toLp 2 b‖ • L.functionApprox f) +
        (‖WithLp.toLp 2 b‖ • L.functionApprox f - y) := by abel
  rw [heq, WithLp.toLp_add]
  exact (norm_add_le _ _).trans (add_le_add h hy)

/-- **Finite precision Lanczos for bounded functions.** Let the spectrum of a run's matrix
lie in $[a,a']$, with $a<a'$, and let $p$ of degree below $k$ approximate $f$ to error
$\delta$ on $[a-\rho,a'+\rho]$, where $\lvert f\rvert\le M$. If the backward perturbation
fits in $\rho$, $k\varepsilon\le1/100$, and the explicit polynomial precision budget is at
most $\eta\le1$, then <!-- value lanczosFunctionApproxFactor k -->
$$\|f(\mathbf{H})\bar{\mathbf{v}}_1-\mathsf{functionApprox}(L,f)\|
\le4k\delta+\eta M\,.$$
The budget uses the degree factor <!-- value polynomialDerivativeFactor k --> $4k^2$
and backward factor <!-- value lanczosBackwardFactor k --> $400k^3$, so sufficient precision
has polynomial dependence on the step count. No continuity or Lipschitz assumption on $f$
is required. The small matrix function and final multiplication are exact postprocessing.
[MuscoMuscoSidford2018, Theorem 2.1] gives the same qualitative polynomial approximation and
additive precision structure for a specified floating point implementation; the local run
model, precision budget and constants here differ, and no runtime claim is made.
Result: lanczos-finite-precision-bounded-functions -/
theorem norm_cfc_mulVec_sub_functionApprox_le_of_precision
    {a a' ρ M δ η : ℝ} {f : ℝ → ℝ} {p : ℝ[X]}
    (hab : a < a') (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100)
    (hρ : lanczosBackwardFactor k * L.ε * specNorm L.H ≤ ρ)
    (hp : p.degree < k)
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc (a - ρ) (a' + ρ)) δ)
    (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc (a - ρ) (a' + ρ), |f x| ≤ M)
    (hη : η ≤ 1)
    (hprecision : Real.sqrt (k + 1) * polynomialDerivativeFactor k / (a' - a + 2 * ρ) *
      (lanczosBackwardFactor k * L.ε * specNorm L.H) + Real.sqrt k * L.ε ≤ η) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ L.normalizedV 1 - L.functionApprox f)‖ ≤
      lanczosFunctionApproxFactor k * δ + η * M := by
  let c := lanczosBackwardFactor k * L.ε * specNorm L.H
  have hgap : frobNorm (L.backwardH - L.dilatedH) ≤ c :=
    L.frobNorm_backwardH_sub_dilatedH_le hsmall
  have hc : 0 ≤ c := (frobNorm_nonneg _).trans hgap
  have hρ0 : 0 ≤ ρ := hc.trans hρ
  have hwidth : 0 < a' - a + 2 * ρ := by linarith
  have hsE : spectrum ℝ L.H ⊆ Set.Icc (a - ρ) (a' + ρ) :=
    fun x hx => ⟨by linarith [(hs hx).1], by linarith [(hs hx).2]⟩
  have hback : spectrum ℝ L.backwardH ⊆ Set.Icc (a - ρ) (a' + ρ) :=
    L.normalized.spectrum_backwardH_subset_Icc L.transpose_basisSucc_mul_self_apply
      hs (hgap.trans hρ)
  have hδ : 0 ≤ δ := happ.nonneg ⟨a - ρ, by constructor <;> linarith⟩
  have hbound : ∀ t ∈ Set.Icc (a - ρ) (a' + ρ), |p.eval t| ≤ M + δ := by
    intro t ht
    have htδ : |p.eval t - f t| ≤ δ := by simpa only [Real.dist_eq] using happ.apply ht
    calc |p.eval t| = |(p.eval t - f t) + f t| := by rw [sub_add_cancel]
      _ ≤ |p.eval t - f t| + |f t| := abs_add_le _ _
      _ ≤ M + δ := by linarith [hf t ht]
  have hdegree := polynomialDerivativeFactor_nonneg k
  let ℓ : ℝ≥0 := ⟨polynomialDerivativeFactor k * (M + δ) / (a' - a + 2 * ρ), by positivity⟩
  have hℓ : (ℓ : ℝ) = polynomialDerivativeFactor k * (M + δ) / (a' - a + 2 * ρ) := rfl
  have hpoly : LipschitzOnWith ℓ (fun x => p.eval x) (Set.Icc (a - ρ) (a' + ρ)) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have h := abs_eval_sub_eval_le_of_forall_abs_eval_le (le_of_lt hp)
      (by linarith : a - ρ < a' + ρ) (by positivity : 0 ≤ M + δ) hbound hx hy
    rw [Real.dist_eq, Real.dist_eq, hℓ]
    simpa only [show a' + ρ - (a - ρ) = a' - a + 2 * ρ by ring] using h
  have hcore := L.norm_cfc_mulVec_sub_functionApprox_le_of_isUniformApproxOn
    hsE hback hp hpoly happ hM hf
  let α := Real.sqrt (k + 1) * polynomialDerivativeFactor k / (a' - a + 2 * ρ) * c
  let β := Real.sqrt k * L.ε
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hβ : 0 ≤ β := by dsimp [β]; exact mul_nonneg (Real.sqrt_nonneg _) L.ε_nonneg
  have hbudget : α + β ≤ η := hprecision
  have hα1 : α ≤ 1 := (by linarith : α ≤ η).trans hη
  have hterm : Real.sqrt (k + 1) * (ℓ : ℝ) *
      frobNorm (L.backwardH - L.dilatedH) ≤ α * (M + δ) := by
    calc _ ≤ Real.sqrt (k + 1) * (ℓ : ℝ) * c :=
        mul_le_mul_of_nonneg_left hgap (by positivity)
      _ = _ := by rw [hℓ]; dsimp [α]; ring
  have hk : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  have hsqrt : Real.sqrt (k + 1) ≤ 2 * k := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hcoeff : 2 + Real.sqrt (k + 1) ≤ 4 * k := by linarith
  have hδmul := mul_le_mul_of_nonneg_right hα1 hδ
  have hMmul := mul_le_mul_of_nonneg_right hbudget hM
  have hlast := mul_le_mul_of_nonneg_right hcoeff hδ
  dsimp [β] at hMmul
  rw [lanczosFunctionApproxFactor_def]
  nlinarith

/-- The bounded-function precision theorem scaled to an arbitrary starting vector with the
run's initial direction. Its output is the norm of the input times the physical computed
basis applied to the small matrix function. -/
theorem norm_cfc_mulVec_sub_smul_functionApprox_le_of_precision
    {a a' ρ M δ η : ℝ} {f : ℝ → ℝ} {p : ℝ[X]}
    (hab : a < a') (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) * L.ε ≤ 1 / 100)
    (hρ : lanczosBackwardFactor k * L.ε * specNorm L.H ≤ ρ)
    (hp : p.degree < k)
    (happ : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc (a - ρ) (a' + ρ)) δ)
    (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc (a - ρ) (a' + ρ), |f x| ≤ M)
    (hη : η ≤ 1)
    (hprecision : Real.sqrt (k + 1) * polynomialDerivativeFactor k / (a' - a + 2 * ρ) *
      (lanczosBackwardFactor k * L.ε * specNorm L.H) + Real.sqrt k * L.ε ≤ η)
    (b : Fin n → ℝ) (hb : b = ‖WithLp.toLp 2 b‖ • L.normalizedV 1) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ b - ‖WithLp.toLp 2 b‖ • L.functionApprox f)‖ ≤
      (lanczosFunctionApproxFactor k * δ + η * M) * ‖WithLp.toLp 2 b‖ := by
  have h := L.norm_cfc_mulVec_sub_functionApprox_le_of_precision
    hab hs hsmall hρ hp happ hM hf hη hprecision
  have hlin := congrArg (fun x => cfc f L.H *ᵥ x) hb
  rw [Matrix.mulVec_smul] at hlin
  rw [hlin, ← smul_sub, WithLp.toLp_smul, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _), mul_comm]
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

end LanczosRun

end NLAlib
