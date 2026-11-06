/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthCoefficients

/-!
# The perturbed Lanczos relation of a reorthogonalized run

For a run `NLAlib.LanczosReorthRun`, the three-term relation
$\mathbf{H}\mathbf{V}_k = \mathbf{V}_k\mathbf{T}_k +
\beta_k\mathbf{v}_{k+1}\mathbf{e}_{k-1}^{\mathsf T} + \mathbf{F}_k$ (`NLAlib.LanczosData.mul_basis`)
has a residual with the discarded reorthogonalization coefficients in it, bounded by
$\|\mathbf{F}_k\|_{\mathsf F} \le 30(k+1)\,(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$,
and the computed tridiagonal is close to the projection
$\mathbf{V}_k^{\mathsf T}\mathbf{H}\mathbf{V}_k$. Hypotheses: $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$ and
$\tau \le 1$. [Paige1970]; [Paige1976] for the rounding part; [Simon1984b].

## Main results

* `NLAlib.LanczosReorthRun.frobNorm_residual_le`: the residual of the relation.
* `NLAlib.LanczosReorthRun.specNorm_transpose_mul_mul_sub_tridiagonal_le`: the projection form,
  $\|\mathbf{V}_k^{\mathsf T}\mathbf{H}\mathbf{V}_k - \mathbf{T}_k\|_2 \le
  50(k+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- A sum of $j + 1$ over $j < m$ is at most $(m+1)^2/2$. -/
private lemma sum_range_cast_add_one_le (m : ℕ) :
    ∑ i ∈ Finset.range m, ((i : ℝ) + 1) ≤ ((m : ℝ) + 1) ^ 2 / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ]
    push_cast
    nlinarith [ih, (Nat.cast_nonneg m : (0 : ℝ) ≤ m)]

/-- The Euclidean norm of a signed sum of six vectors, by the triangle inequality. -/
private lemma norm_toLp_six_le {n : ℕ} (a b c d e f : Fin n → ℝ) :
    ‖WithLp.toLp 2 (a + b - c - d - e - f)‖ ≤ ‖WithLp.toLp 2 a‖ + ‖WithLp.toLp 2 b‖ +
      ‖WithLp.toLp 2 c‖ + ‖WithLp.toLp 2 d‖ + ‖WithLp.toLp 2 e‖ + ‖WithLp.toLp 2 f‖ := by
  simp only [WithLp.toLp_sub, WithLp.toLp_add]
  have h1 := norm_sub_le (WithLp.toLp 2 a + WithLp.toLp 2 b - WithLp.toLp 2 c -
    WithLp.toLp 2 d - WithLp.toLp 2 e) (WithLp.toLp 2 f)
  have h2 := norm_sub_le (WithLp.toLp 2 a + WithLp.toLp 2 b - WithLp.toLp 2 c -
    WithLp.toLp 2 d) (WithLp.toLp 2 e)
  have h3 := norm_sub_le (WithLp.toLp 2 a + WithLp.toLp 2 b - WithLp.toLp 2 c)
    (WithLp.toLp 2 d)
  have h4 := norm_sub_le (WithLp.toLp 2 a + WithLp.toLp 2 b) (WithLp.toLp 2 c)
  have h5 := norm_add_le (WithLp.toLp 2 a) (WithLp.toLp 2 b)
  linarith

/-- The local errors of one column: $\|\mathbf{e}^w_{j+1}\| \le 2.57\,\varepsilon\|\mathbf{H}\|_2$
and $\|\mathbf{e}^z_{j+1}\| \le 4.3\,\varepsilon\|\mathbf{H}\|_2$. -/
private lemma norm_ew_ez_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.ew (j + 1))‖ ≤ 257 / 100 * (L.ε * specNorm L.H) ∧
      ‖WithLp.toLp 2 (L.ez (j + 1))‖ ≤ 43 / 10 * (L.ε * specNorm L.H) := by
  have hε := L.ε_nonneg
  have hεle := L.ε_le
  have hh := specNorm_nonneg L.H
  have hvj1 := L.norm_v_le (i := j + 1) (by omega)
  have hvj := L.norm_v_le (i := j) (by omega)
  have hβabs := L.abs_β_le hη hsmall hrec (i := j) hj.le
  have hu : ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤ 103 / 100 * specNorm L.H := by
    rw [L.u_eq j hj, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    have h1 := norm_toLp_mulVec_le L.H (L.v (j + 1))
    have h2 := L.norm_eu_le j hj
    have h3 := mul_le_mul_of_nonneg_left hvj1 hh
    have h4 := mul_le_mul_of_nonneg_left hvj1 (mul_nonneg hε hh)
    have h5 := mul_le_mul_of_nonneg_right hεle hh
    linarith
  have h2 := mul_le_mul hβabs hvj (norm_nonneg _) (by positivity)
  have hew : ‖WithLp.toLp 2 (L.ew (j + 1))‖ ≤ 257 / 100 * (L.ε * specNorm L.H) := by
    have h1 := L.norm_ew_le j hj
    have h3 := mul_le_mul_of_nonneg_left (add_le_add hu h2) hε
    linarith [mul_nonneg hε hh]
  have hw : ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 27 / 10 * specNorm L.H := by
    have hsub := norm_sub_le (WithLp.toLp 2 (L.u (j + 1))) (WithLp.toLp 2 (L.β j • L.v j))
    have hsm : ‖WithLp.toLp 2 (L.β j • L.v j)‖ = |L.β j| * ‖WithLp.toLp 2 (L.v j)‖ := by
      rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs]
    have hadd := norm_add_le (WithLp.toLp 2 (L.u (j + 1)) - WithLp.toLp 2 (L.β j • L.v j))
      (WithLp.toLp 2 (L.ew (j + 1)))
    have h3 := mul_le_mul_of_nonneg_right hεle hh
    rw [L.w_eq j hj, WithLp.toLp_add, WithLp.toLp_sub]
    linarith
  refine ⟨hew, ?_⟩
  have h1 := L.norm_ez_le j hj
  have hα := (L.coeff_le hη hsmall hrec j hj).1
  have h3 := mul_le_mul_of_nonneg_left
    (add_le_add hw (mul_le_mul hα hvj1 (norm_nonneg _) (by positivity))) hε
  linarith [mul_nonneg hε hh]

/-- One column of the residual is at most
$36\sqrt{j+1}\,(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$. -/
private lemma norm_residual_col_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (fun i => L.toLanczosData.residual i ⟨j, hj⟩)‖ ≤
      36 * Real.sqrt ((j : ℝ) + 1) * L.recLevel * specNorm L.H := by
  have hε := L.ε_nonneg
  have hε₂ := L.ε₂_nonneg
  have hr0 := L.recLevel_nonneg
  have hεr : L.ε ≤ L.recLevel := by
    linarith [L.orthLevel_nonneg, show L.recLevel = L.orthLevel + L.ε + L.ε₂ from rfl]
  have hε₂r : L.ε₂ ≤ L.recLevel := by
    linarith [L.orthLevel_nonneg, show L.recLevel = L.orthLevel + L.ε + L.ε₂ from rfl]
  have hh := specNorm_nonneg L.H
  have hVg := L.specNorm_transpose_mul_self_sub_one_le hη hsmall (m := j + 1) (by omega)
  have hVn : specNorm (basisOf L.v (j + 1)) ≤ 101 / 100 := by
    refine (specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le (hVg.trans hη)).trans ?_
    rw [Real.sqrt_le_iff]
    norm_num
  have hvj1 := L.norm_v_le (i := j + 1) (by omega)
  have hz' := (L.norm_z'_le hη hsmall hrec hj).trans
    (mul_le_mul_of_nonneg_right (by norm_num : (151 / 100 : ℝ) ≤ 152 / 100) hh)
  obtain ⟨hew, hez⟩ := norm_ew_ez_le L hη hsmall hrec hj
  have hcol : (fun i => L.toLanczosData.residual i ⟨j, hj⟩) =
      L.toLanczosData.recurrenceError j := by
    funext i
    rfl
  have hc := (L.orth_eq j hj).residual hVg
  have hz := (L.coeff_le hη hsmall hrec j hj).2.2
  have hzb := mul_le_mul_of_nonneg_left hz hε₂
  have hδ := mul_le_mul_of_nonneg_left hz' hε
  have hδ' := L.norm_δ_le j hj
  have hEu2 := mul_le_mul_of_nonneg_left hvj1 (mul_nonneg hε hh)
  have hEu := L.norm_eu_le j hj
  have hA1 : ‖WithLp.toLp 2 (basisOf L.v (j + 1) *ᵥ (fun i => L.h (j + 1) i))‖ ≤
      101 / 100 * (24 * Real.sqrt ((j : ℝ) + 1) * L.recLevel * specNorm L.H) :=
    (norm_toLp_mulVec_le _ _).trans
      (mul_le_mul hVn (norm_coef_le L hη hsmall hrec hτ j hj) (norm_nonneg _) (by norm_num))
  have hE1 := mul_le_mul_of_nonneg_right hεr hh
  have hE2 := mul_le_mul_of_nonneg_right hε₂r hh
  have hs1 : 1 ≤ Real.sqrt ((j : ℝ) + 1) := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (j : ℝ) + 1 by positivity),
      Real.sqrt_nonneg ((j : ℝ) + 1), (Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hE3 := mul_le_mul_of_nonneg_right hs1 (mul_nonneg hr0 hh)
  rw [hcol, recurrenceError_eq L hj]
  refine (norm_toLp_six_le _ _ _ _ _ _).trans ?_
  linarith [mul_nonneg (mul_nonneg (Real.sqrt_nonneg ((j : ℝ) + 1)) hr0) hh, mul_nonneg hε hh]

/-- **The perturbed Lanczos relation of a reorthogonalized run**: under $\eta_0 \le 1/100$, the
fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$
and $\tau \le 1$, with the discarded coefficients in the residual,
$\|\mathbf{F}_k\|_{\mathsf F} \le 30(k+1)\,(\mu + \varepsilon +
\varepsilon_2)\,\|\mathbf{H}\|_2$; the relation itself is `NLAlib.LanczosData.mul_basis`.
[Paige1971, §6.1, (6.8)] for the reorthogonalized relation; [Paige1976, §2, (15)–(19)] for
the rounding part. -/
theorem frobNorm_residual_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    frobNorm L.toLanczosData.residual ≤ 30 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := by
  have hr0 := L.recLevel_nonneg
  have hcolb : ∀ j : Fin k, ‖WithLp.toLp 2 (L.toLanczosData.residual.col j)‖ ^ 2 ≤
      36 ^ 2 * (L.recLevel * specNorm L.H) ^ 2 * (((j : ℕ) : ℝ) + 1) := by
    intro j
    have h1 := norm_residual_col_le L hη hsmall hrec hτ j.2
    have h2 := norm_nonneg (WithLp.toLp 2 (L.toLanczosData.residual.col j))
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ ((j : ℕ) : ℝ) + 1 by positivity)
    calc _ ≤ (36 * Real.sqrt (((j : ℕ) : ℝ) + 1) * L.recLevel * specNorm L.H) ^ 2 :=
          pow_le_pow_left₀ h2 h1 2
      _ = _ := by linear_combination (36 : ℝ) ^ 2 * (L.recLevel * specNorm L.H) ^ 2 * hs
  have hfin : frobNorm L.toLanczosData.residual ^ 2 ≤
      (30 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H) ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    calc ∑ j : Fin k, ‖WithLp.toLp 2 (L.toLanczosData.residual.col j)‖ ^ 2
        ≤ ∑ j : Fin k, 36 ^ 2 * (L.recLevel * specNorm L.H) ^ 2 * (((j : ℕ) : ℝ) + 1) :=
          Finset.sum_le_sum fun j _ => by simpa only [mul_assoc] using hcolb j
      _ = 36 ^ 2 * (L.recLevel * specNorm L.H) ^ 2 * ∑ i ∈ Finset.range k, ((i : ℝ) + 1) := by
          rw [Finset.mul_sum]
          exact Fin.sum_univ_eq_sum_range (fun i : ℕ => 36 ^ 2 * (L.recLevel * specNorm L.H) ^ 2 *
            ((i : ℝ) + 1)) k
      _ ≤ 36 ^ 2 * (L.recLevel * specNorm L.H) ^ 2 * (((k : ℝ) + 1) ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left (sum_range_cast_add_one_le k) (by positivity)
      _ ≤ (30 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H) ^ 2 := by
          nlinarith [sq_nonneg (((k : ℝ) + 1) * (L.recLevel * specNorm L.H))]
  have hX : 0 ≤ 30 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := by
    have := specNorm_nonneg L.H
    positivity
  nlinarith [frobNorm_nonneg L.toLanczosData.residual]

/-- Conjugation by a nearly orthonormal basis: $\|\mathbf{V}^{\mathsf T}\mathbf{H}\mathbf{V}\|_2
\le \tfrac{103}{100}\|\mathbf{H}\|_2$ when $\|\mathbf{V}\|_2 \le 101/100$. -/
private lemma specNorm_transpose_mul_mul_le_of_specNorm_le {m p : ℕ}
    (V : Matrix (Fin m) (Fin p) ℝ) (H : Matrix (Fin m) (Fin m) ℝ)
    (hVs : specNorm V ≤ 101 / 100) :
    specNorm (Vᵀ * H * V) ≤ 103 / 100 * specNorm H := by
  have h := (specNorm_mul_le (Vᵀ * H) V).trans (mul_le_mul_of_nonneg_right
    ((specNorm_mul_le Vᵀ H).trans_eq (by rw [specNorm_transpose])) (specNorm_nonneg V))
  have h6 := mul_self_le_mul_self (specNorm_nonneg _) hVs
  nlinarith [specNorm_nonneg H, mul_le_mul_of_nonneg_right h6 (specNorm_nonneg H)]

/-- The rank-one term of the relation: $\|\mathbf{V}_k^{\mathsf T}(\beta_k\mathbf{v}_{k+1})
\mathbf{e}^{\mathsf T}\|_2 \le \tfrac32\|\mathbf{H}\|_2\,(\mu + \varepsilon + \varepsilon_2)$. -/
private lemma specNorm_transpose_mul_vecMulVec_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100)
    (hG : specNorm (L.toLanczosData.basisᵀ * L.toLanczosData.basis - 1) ≤
      Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel) :
    specNorm (L.toLanczosData.basisᵀ * Matrix.vecMulVec (L.β k • L.v (k + 1))
      (Pi.single L.toLanczosData.lastIndex 1)) ≤ 3 / 2 * specNorm L.H * L.recLevel := by
  have hrμ := L.orthLevel_le_recLevel
  have hh := specNorm_nonneg L.H
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by have := L.k_pos; omega⟩
  have hμv := norm_transpose_mulVec_v_le L (j := j) (by omega) (hG.trans hsmall) hη
  have hβ := (L.coeff_le hη hsmall hrec j (by omega)).2.1
  have hβ0 := (L.β_succ_pos (j := j) (by omega)).le
  have he : ‖WithLp.toLp 2 (Pi.single L.toLanczosData.lastIndex (1 : ℝ) :
      Fin (j + 1) → ℝ)‖ = 1 := by
    simp
  rw [Matrix.mul_vecMulVec, specNorm_vecMulVec, Matrix.mulVec_smul, WithLp.toLp_smul,
    norm_smul, he, Real.norm_eq_abs, abs_of_nonneg hβ0]
  have hμv' : ‖WithLp.toLp 2 (L.toLanczosData.basisᵀ *ᵥ L.v (j + 1 + 1))‖ ≤ L.orthLevel := hμv
  have hq := mul_le_mul hβ hμv' (norm_nonneg _) (by positivity)
  nlinarith [mul_le_mul_of_nonneg_left hrμ hh]

/-- **The projection form of the perturbed Lanczos relation**: under $\eta_0 \le 1/100$, the
fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu + \varepsilon + \varepsilon_2 \le 1/100$
and $\tau \le 1$, $\|\mathbf{V}_k^{\mathsf{T}}\mathbf{H}\mathbf{V}_k -
\mathbf{T}_k\|_2 \le 50(k+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$.
[Simon1984b, Theorem 5] (semi-orthogonality suffices; locator from a secondary source). -/
theorem specNorm_transpose_mul_mul_sub_tridiagonal_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    specNorm (L.toLanczosData.basisᵀ * L.H * L.toLanczosData.basis -
      L.toLanczosData.tridiagonal) ≤ 50 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := by
  have hμ := L.orthLevel_nonneg
  have hr0 := L.recLevel_nonneg
  have hrμ := L.orthLevel_le_recLevel
  have hg1 : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ 1 / 100 := hsmall.trans hη
  have hs : Real.sqrt (3 * ((k : ℝ) + 1)) ≤ 2 * ((k : ℝ) + 1) :=
    Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]⟩
  have hG : specNorm (L.toLanczosData.basisᵀ * L.toLanczosData.basis - 1) ≤
      Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by
    refine (specNorm_le_frobNorm _).trans
      ((L.frobNorm_transpose_mul_self_sub_one_le hη hsmall k (by omega)).trans ?_)
    exact mul_le_mul_of_nonneg_right
      (Real.sqrt_le_sqrt (by linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)])) hμ
  have hVs : specNorm L.toLanczosData.basis ≤ 101 / 100 := by
    refine (specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le (hG.trans hg1)).trans ?_
    rw [Real.sqrt_le_iff]
    norm_num
  have hA := specNorm_transpose_mul_vecMulVec_le L hη hsmall hrec hG
  set V := L.toLanczosData.basis with hVd
  set T := L.toLanczosData.tridiagonal with hTd
  set F := L.toLanczosData.residual with hFd
  set E := Matrix.vecMulVec (L.β k • L.v (k + 1)) (Pi.single L.toLanczosData.lastIndex 1) with hEd
  have hmb : L.H * V = V * T + E + F := L.toLanczosData.mul_basis
  have hid : Vᵀ * L.H * V - T = (Vᵀ * V - 1) * T + Vᵀ * E + Vᵀ * F := by
    rw [Matrix.mul_assoc, hmb]
    simp only [Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc]
    abel
  have hM : specNorm (Vᵀ * L.H * V - T) ≤
      Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel * specNorm T + specNorm (Vᵀ * E) +
        specNorm (Vᵀ * F) := by
    rw [hid]
    have h1 := specNorm_add_le ((Vᵀ * V - 1) * T + Vᵀ * E) (Vᵀ * F)
    have h2 := specNorm_add_le ((Vᵀ * V - 1) * T) (Vᵀ * E)
    have h3 := specNorm_mul_le (Vᵀ * V - 1) T
    have h4 := mul_le_mul_of_nonneg_right hG (specNorm_nonneg T)
    linarith
  have hT : specNorm T ≤ specNorm (Vᵀ * L.H * V) + specNorm (Vᵀ * L.H * V - T) := by
    have := specNorm_sub_le (Vᵀ * L.H * V) (Vᵀ * L.H * V - T)
    rwa [sub_sub_cancel] at this
  have hVH := specNorm_transpose_mul_mul_le_of_specNorm_le L.toLanczosData.basis L.H hVs
  have hB : specNorm (Vᵀ * F) ≤ 101 / 100 * (30 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H) := by
    have h1 := specNorm_mul_le Vᵀ F
    rw [specNorm_transpose] at h1
    have h2 := specNorm_le_frobNorm F
    have h3 := frobNorm_residual_le L hη hsmall hrec hτ
    have h4 : specNorm F ≤ 30 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := h2.trans h3
    exact h1.trans (mul_le_mul hVs h4 (specNorm_nonneg _) (by norm_num))
  have hg0 : 0 ≤ Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel := by positivity
  have hg2 : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ 2 * ((k : ℝ) + 1) * L.recLevel := by
    calc _ ≤ 2 * ((k : ℝ) + 1) * L.orthLevel := mul_le_mul_of_nonneg_right hs hμ
      _ ≤ 2 * ((k : ℝ) + 1) * L.recLevel := mul_le_mul_of_nonneg_left hrμ (by positivity)
  have hK : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have p1 : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel * specNorm T ≤
      Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel * specNorm (Vᵀ * L.H * V) +
        Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel * specNorm (Vᵀ * L.H * V - T) := by
    rw [← mul_add]
    exact mul_le_mul_of_nonneg_left hT hg0
  have p2 : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel * specNorm (Vᵀ * L.H * V - T) ≤
      1 / 100 * specNorm (Vᵀ * L.H * V - T) :=
    mul_le_mul_of_nonneg_right hg1 (specNorm_nonneg _)
  have p3 : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel * specNorm (Vᵀ * L.H * V) ≤
      2 * ((k : ℝ) + 1) * L.recLevel * (103 / 100 * specNorm L.H) :=
    mul_le_mul hg2 hVH (specNorm_nonneg _) (by positivity)
  have p4 : specNorm L.H * L.recLevel ≤ ((k : ℝ) + 1) * (specNorm L.H * L.recLevel) :=
    le_mul_of_one_le_left (mul_nonneg (specNorm_nonneg _) hr0) hK
  nlinarith [specNorm_nonneg (Vᵀ * L.H * V - T), specNorm_nonneg L.H, hr0]

end LanczosReorthRun

end NLAlib
