/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthRun

/-!
# Coefficient bounds of a reorthogonalized Lanczos run

For a run `NLAlib.LanczosReorthRun` on its admissible prefix, under $\eta_0 \le 1/100$, the
fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$ on the orthogonality level $\mu$
(`NLAlib.LanczosReorthRun.orthLevel`) and $\mu + \varepsilon + \varepsilon_2 \le 1/100$
(`NLAlib.LanczosReorthRun.recLevel`): the Lanczos coefficients $\alpha_j$, $\beta_j$ and the
vectors $\mathbf{z}_j$ are bounded by $\tfrac32\|\mathbf{H}\|_2$ without growth in $j$, and the
reorthogonalization coefficients $\mathbf{h}_{j+1}$, which the program discards, are of the order
of the recurrence level. The second bound is the one place symmetry of $\mathbf{H}$ is used.
[Paige1970]; [Paige1976] for plain Lanczos.

## Main results

* `NLAlib.LanczosReorthRun.coeff_le`: $\lvert\alpha_{j+1}\rvert$, $\beta_{j+1}$,
  $\|\mathbf{z}_{j+1}\| \le \tfrac32\|\mathbf{H}\|_2$.
* `NLAlib.LanczosReorthRun.abs_β_le`, `NLAlib.LanczosReorthRun.norm_z'_le`: the same for
  $\lvert\beta_i\rvert$, $i \le k$, and a bound for $\|\mathbf{z}_{j+1}'\|$.
* `NLAlib.LanczosReorthRun.norm_coef_le`: the reorthogonalization coefficients,
  $\|\mathbf{h}_{j+1}\| \le 24\sqrt{j+1}\,(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- The parameter bounds that follow from $\mu + \varepsilon + \varepsilon_2 \le 1/100$. -/
private lemma levels_le_of_recLevel_le (hrec : L.recLevel ≤ 1 / 100) :
    0 ≤ L.ε₃ / L.τ ∧ L.ε ≤ 1 / 300 ∧ L.ε₂ ≤ 1 / 100 ∧ 0 ≤ L.orthLevel ∧
      L.orthLevel ≤ 1 / 100 ∧ L.ε₁ + L.ε₃ / L.τ ≤ 1 / 200 := by
  have hq : 0 ≤ L.ε₃ / L.τ := div_nonneg L.ε₃_nonneg L.τ_pos.le
  have h1 := L.ε₁_nonneg
  have h2 := L.ε₂_nonneg
  have h0 := L.ε_nonneg
  simp only [recLevel, orthLevel] at hrec ⊢
  refine ⟨hq, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- Component $c$ of $\mathbf{V}_m^{\mathsf{T}}\mathbf{x}$ is $\mathbf{v}_{c+1}^{\mathsf{T}}
\mathbf{x}$. -/
private lemma transpose_basisOf_mulVec_apply {m : ℕ} (x : Fin n → ℝ) (c : Fin m) :
    ((basisOf L.v m)ᵀ *ᵥ x) c = L.v ((c : ℕ) + 1) ⬝ᵥ x := by
  simp [basisOf, Matrix.mulVec, dotProduct]

/-- One component of $\mathbf{V}_m^{\mathsf{T}}\mathbf{x}$ is at most its norm. -/
private lemma abs_v_dotProduct_le {m : ℕ} (x : Fin n → ℝ) (c : ℕ)
    (hc : c < m) : |L.v (c + 1) ⬝ᵥ x| ≤ ‖WithLp.toLp 2 ((basisOf L.v m)ᵀ *ᵥ x)‖ := by
  rw [← transpose_basisOf_mulVec_apply L x ⟨c, hc⟩, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ _).trans (EuclideanSpace.norm_le_norm_toLp _)

/-- One orthogonalization step: $\|\mathbf{z}'\|$ and $\|\mathbf{h}\|$ against $\|\mathbf{z}\|$. -/
private lemma norm_z'_le_and_norm_coef_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {i : ℕ} (hi : i < k) :
    ‖WithLp.toLp 2 (L.z' (i + 1))‖ ≤ 103 / 100 * ‖WithLp.toLp 2 (L.z (i + 1))‖ ∧
      ‖WithLp.toLp 2 (fun c : Fin (i + 1) => L.h (i + 1) c)‖ ≤
        105 / 100 * ‖WithLp.toLp 2 (L.z (i + 1))‖ := by
  obtain ⟨hq, hε, hε₂, -, -, hε₁q⟩ := levels_le_of_recLevel_le L hrec
  have hV := L.specNorm_transpose_mul_self_sub_one_le hη hsmall (m := i + 1) (by omega)
  have hη0 : 0 ≤ L.η₀ := (specNorm_nonneg _).trans hV
  have hO := L.orth_eq i hi
  set V := basisOf L.v (i + 1)
  set z := L.z (i + 1)
  set z' := L.z' (i + 1)
  set hv : Fin (i + 1) → ℝ := fun c => L.h (i + 1) c
  set Z := ‖WithLp.toLp 2 z‖
  set Z' := ‖WithLp.toLp 2 z'‖
  set Hn := ‖WithLp.toLp 2 hv‖
  set T := ‖WithLp.toLp 2 (Vᵀ *ᵥ z')‖
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have hZ'0 : 0 ≤ Z' := norm_nonneg _
  have hHn0 : 0 ≤ Hn := norm_nonneg _
  have hsq : Real.sqrt (1 + L.η₀) ≤ 101 / 100 := Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hsq0 : 0 ≤ Real.sqrt (1 + L.η₀) := Real.sqrt_nonneg _
  have hA := hO.norm_coef_le hV (by linarith)
  have hVz : ‖WithLp.toLp 2 (Vᵀ *ᵥ z)‖ ≤ 101 / 100 * Z := by
    refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [specNorm_transpose]
    gcongr
    exact (specNorm_le_sqrt_of_specNorm_transpose_mul_self_sub_one_le hV).trans hsq
  have hT : T ≤ L.ε₁ * Z' + L.ε₃ * Z := hO.orth hV
  have hres : ‖WithLp.toLp 2 (z - V *ᵥ hv - z')‖ ≤ L.ε₂ * Z := hO.residual hV
  -- admissibility: `τ‖z‖ ≤ 1.01 ‖z'‖`
  have hν := L.abs_ν_sub_le i hi
  have hβ := L.abs_β_sub_le i hi
  have hadm := L.admissible i hi
  have hτ0 := L.τ_pos
  have hν' : (1 - L.ε) * Z ≤ L.ν (i + 1) := by
    linarith [neg_abs_le (L.ν (i + 1) - Z)]
  have hβ' : L.β (i + 1) ≤ (1 + L.ε) * Z' := by linarith [le_abs_self (L.β (i + 1) - Z')]
  have hτZ : L.τ * Z ≤ 101 / 100 * Z' := by
    nlinarith [mul_le_mul_of_nonneg_left hν' hτ0.le, mul_nonneg hτ0.le hZ0,
      mul_nonneg L.ε_nonneg (mul_nonneg hτ0.le hZ0)]
  have hε₃ : L.ε₃ * Z = L.ε₃ / L.τ * (L.τ * Z) := by field_simp
  have hT' : T ≤ 6 / 1000 * Z' := by
    nlinarith [mul_le_mul_of_nonneg_left hτZ hq, mul_nonneg L.ε₁_nonneg hZ'0,
      mul_nonneg hq hZ'0, mul_le_mul_of_nonneg_right hε₁q hZ'0]
  have hHn : Hn ≤ 1031 / 1000 * Z + 61 / 10000 * Z' := by
    rw [le_div_iff₀ (by linarith)] at hA
    nlinarith [mul_le_mul_of_nonneg_left hη hHn0, mul_le_mul hsq hε₂ L.ε₂_nonneg (by norm_num),
      mul_nonneg hsq0 L.ε₂_nonneg, mul_le_mul_of_nonneg_right
        (mul_le_mul hsq hε₂ L.ε₂_nonneg (by norm_num)) hZ0]
  -- `‖z'‖² = z' ⬝ (z - V h - r)`
  have hdot : z' ⬝ᵥ z' = z' ⬝ᵥ z - (Vᵀ *ᵥ z') ⬝ᵥ hv - z' ⬝ᵥ (z - V *ᵥ hv - z') := by
    rw [Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    simp only [dotProduct_sub]
    ring
  rw [← EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at hdot
  have h1 := le_abs_self (z' ⬝ᵥ z)
  have h2 := neg_abs_le ((Vᵀ *ᵥ z') ⬝ᵥ hv)
  have h3 := neg_abs_le (z' ⬝ᵥ (z - V *ᵥ hv - z'))
  have e1 := EuclideanSpace.abs_dotProduct_le_norm z' z
  have e2 := EuclideanSpace.abs_dotProduct_le_norm (Vᵀ *ᵥ z') hv
  have e3 := EuclideanSpace.abs_dotProduct_le_norm z' (z - V *ᵥ hv - z')
  have hZ'sq : Z' ^ 2 ≤ Z' * (101 / 100 * Z + 6 / 1000 * Hn) := by
    nlinarith [mul_le_mul_of_nonneg_left hres hZ'0, mul_le_mul_of_nonneg_right hT' hHn0,
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hε₂ hZ0) hZ'0,
      mul_nonneg L.ε₂_nonneg hZ0]
  have hZ' : Z' ≤ 101 / 100 * Z + 6 / 1000 * Hn := by
    rcases hZ'0.eq_or_lt with h | h
    · rw [← h]; positivity
    · exact le_of_mul_le_mul_left (by simpa [sq] using hZ'sq) h
  constructor <;> linarith

/-- The local errors of one step and the norm of $\mathbf{w}$. -/
private lemma norm_eu_ew_w_le (hrec : L.recLevel ≤ 1 / 100) {j : ℕ} (hj : j < k) {B : ℝ}
    (hB : |L.β j| ≤ B) :
    ‖WithLp.toLp 2 (L.eu (j + 1))‖ ≤ 101 / 100 * L.ε * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.ew (j + 1))‖ ≤ L.ε * (102 / 100 * specNorm L.H + 101 / 100 * B) ∧
      ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 103 / 100 * specNorm L.H + 102 / 100 * B := by
  have hε := (levels_le_of_recLevel_le L hrec).2.1
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hv := L.norm_v_le (i := j + 1) (by omega)
  have hv' := L.norm_v_le (i := j) (by omega)
  have heu : ‖WithLp.toLp 2 (L.eu (j + 1))‖ ≤ 101 / 100 * L.ε * specNorm L.H := by
    refine (L.norm_eu_le j hj).trans ?_
    nlinarith [mul_nonneg hε0 hs]
  have hu : ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤ 102 / 100 * specNorm L.H := by
    rw [L.u_eq j hj, WithLp.toLp_add]
    refine (norm_add_le _ _).trans ?_
    have := norm_toLp_mulVec_le L.H (L.v (j + 1))
    nlinarith [mul_le_mul_of_nonneg_left hv hs]
  have hbv : |L.β j| * ‖WithLp.toLp 2 (L.v j)‖ ≤ 101 / 100 * B :=
    (mul_le_mul hB hv' (norm_nonneg _) hB0).trans_eq (mul_comm _ _)
  have hew : ‖WithLp.toLp 2 (L.ew (j + 1))‖ ≤ L.ε * (102 / 100 * specNorm L.H + 101 / 100 * B) :=
    (L.norm_ew_le j hj).trans (by gcongr)
  refine ⟨heu, hew, ?_⟩
  rw [L.w_eq j hj, WithLp.toLp_add, WithLp.toLp_sub, WithLp.toLp_smul]
  refine (norm_add_le _ _).trans ?_
  have := norm_sub_le (WithLp.toLp 2 (L.u (j + 1))) (L.β j • WithLp.toLp 2 (L.v j))
  rw [norm_smul, Real.norm_eq_abs] at this
  nlinarith [mul_le_mul_of_nonneg_left (le_refl (102 / 100 * specNorm L.H + 101 / 100 * B)) hε0]

/-- The last update of a step: the coefficient bounds once
$\|\mathbf{w}\| \le 1.04\|\mathbf{H}\|_2$. -/
private lemma coeff_le_of_norm_w_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j : ℕ} (hj : j < k)
    (hw : ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 104 / 100 * specNorm L.H) :
    |L.α (j + 1)| ≤ 3 / 2 * specNorm L.H ∧ L.β (j + 1) ≤ 3 / 2 * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 3 / 2 * specNorm L.H := by
  have hε := (levels_le_of_recLevel_le L hrec).2.1
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  have hvsq := L.norm_v_sq_le (i := j + 1) (by omega)
  have hv := L.norm_v_le (i := j + 1) (by omega)
  have hvsq' : 1 - L.ε ≤ ‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 := by
    have := L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
    linarith [neg_abs_le (‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1)]
  have hsq : ‖WithLp.toLp 2 (L.w (j + 1) - L.α (j + 1) • L.v (j + 1))‖ ^ 2 =
      ‖WithLp.toLp 2 (L.w (j + 1))‖ ^ 2 - 2 * L.α (j + 1) * (L.v (j + 1) ⬝ᵥ L.w (j + 1)) +
        L.α (j + 1) ^ 2 * ‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 := by
    simp only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct_comm (L.w (j + 1)) (L.v (j + 1))]
    ring
  set v := L.v (j + 1)
  set w := L.w (j + 1)
  set a := L.α (j + 1)
  set e := L.eα (j + 1)
  have hW0 : 0 ≤ ‖WithLp.toLp 2 w‖ := norm_nonneg _
  have hv0 : 0 ≤ ‖WithLp.toLp 2 v‖ := norm_nonneg _
  have ha : a = v ⬝ᵥ w + e := L.α_eq j hj
  have he' : |e| ≤ 34 / 10000 * ‖WithLp.toLp 2 w‖ := by
    refine (L.abs_eα_le j hj).trans ?_
    nlinarith [mul_nonneg hε0 hW0, mul_le_mul_of_nonneg_left hv (mul_nonneg hε0 hW0)]
  have hvw : |v ⬝ᵥ w| ≤ 101 / 100 * ‖WithLp.toLp 2 w‖ :=
    (EuclideanSpace.abs_dotProduct_le_norm v w).trans (by gcongr)
  have haW : |a| ≤ 102 / 100 * ‖WithLp.toLp 2 w‖ := by
    rw [ha]; exact (abs_add_le _ _).trans (by linarith)
  have hwa : ‖WithLp.toLp 2 (w - a • v)‖ ≤ 101 / 100 * ‖WithLp.toLp 2 w‖ := by
    have hvw' : v ⬝ᵥ w = a - e := by rw [ha]; ring
    rw [hvw'] at hsq
    have h2 : ‖WithLp.toLp 2 (w - a • v)‖ ^ 2 ≤ (101 / 100 * ‖WithLp.toLp 2 w‖) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hvsq (sq_nonneg a), le_abs_self (a * e), abs_mul a e,
        sq_nonneg (99 / 100 * |a| - |e|), sq_abs a, abs_nonneg a, abs_nonneg e,
        mul_le_mul he' he' (abs_nonneg e) (by positivity)]
    nlinarith [norm_nonneg (WithLp.toLp 2 (w - a • v))]
  have hez : ‖WithLp.toLp 2 (L.ez (j + 1))‖ ≤ 7 / 1000 * ‖WithLp.toLp 2 w‖ := by
    refine (L.norm_ez_le j hj).trans ?_
    have : |a| * ‖WithLp.toLp 2 v‖ ≤ 102 / 100 * ‖WithLp.toLp 2 w‖ * (101 / 100) :=
      mul_le_mul haW hv hv0 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hε0, mul_nonneg hε0 hW0]
  have hz : ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 1017 / 1000 * ‖WithLp.toLp 2 w‖ := by
    rw [L.z_eq j hj, WithLp.toLp_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hz' := (norm_z'_le_and_norm_coef_le L hη hsmall hrec hj).1
  have hβ := L.abs_β_sub_le j hj
  have hβ' : L.β (j + 1) ≤ (1 + L.ε) * ‖WithLp.toLp 2 (L.z' (j + 1))‖ := by
    linarith [le_abs_self (L.β (j + 1) - ‖WithLp.toLp 2 (L.z' (j + 1))‖)]
  refine ⟨by linarith, ?_, by linarith⟩
  nlinarith [mul_le_mul_of_nonneg_left hz' hε0, norm_nonneg (WithLp.toLp 2 (L.z' (j + 1)))]

/-- The inner product $\mathbf{v}_{i+2}^{\mathsf{T}}\mathbf{H}\mathbf{v}_{i+1}$ is close to
$\beta_{i+1}\|\mathbf{v}_{i+2}\|^2$, from the relation at step $i + 1$. -/
private lemma abs_v_dotProduct_mulVec_sub_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {i : ℕ} (hik : i < k)
    (hα : |L.α (i + 1)| ≤ 3 / 2 * specNorm L.H) (hz : ‖WithLp.toLp 2 (L.z (i + 1))‖ ≤
      3 / 2 * specNorm L.H) (hβi : |L.β i| ≤ 3 / 2 * specNorm L.H) :
    |L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) - L.β (i + 1) * (L.v (i + 2) ⬝ᵥ L.v (i + 2))| ≤
      92 / 1000 * specNorm L.H := by
  obtain ⟨-, hε, hε₂, hμ0, hμ, -⟩ := levels_le_of_recLevel_le L hrec
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  obtain ⟨heu, hew, hw⟩ := norm_eu_ew_w_le L hrec hik hβi
  have hvn := L.norm_v_le (i := i + 2) (by omega)
  have hpn := L.norm_v_le (i := i + 1) (by omega)
  have hez : ‖WithLp.toLp 2 (L.ez (i + 1))‖ ≤
      L.ε * (103 / 100 * specNorm L.H + 102 / 100 * (3 / 2 * specNorm L.H) +
        3 / 2 * specNorm L.H * (101 / 100)) :=
    (L.norm_ez_le i hik).trans (by gcongr)
  obtain ⟨hz', hh⟩ := norm_z'_le_and_norm_coef_le L hη hsmall hrec hik
  have hV := L.specNorm_transpose_mul_self_sub_one_le hη hsmall (m := i + 1) (by omega)
  have hres := (L.orth_eq i hik).residual hV
  have hδ := L.norm_δ_le i hik
  have hG := (L.norm_transpose_mulVec_v_le hik hV hη).trans hμ
  have hHp : L.H *ᵥ L.v (i + 1) = basisOf L.v (i + 1) *ᵥ (fun c => L.h (i + 1) c) +
      (L.z (i + 1) - basisOf L.v (i + 1) *ᵥ (fun c => L.h (i + 1) c) - L.z' (i + 1)) +
      L.β (i + 1) • L.v (i + 2) - L.δ (i + 1) + L.α (i + 1) • L.v (i + 1) - L.ez (i + 1) +
      L.β i • L.v i - L.ew (i + 1) - L.eu (i + 1) := by
    rw [L.smul_v_eq i hik, L.z_eq i hik, L.w_eq i hik, L.u_eq i hik]
    abel
  generalize hr : L.z (i + 1) - basisOf L.v (i + 1) *ᵥ (fun c => L.h (i + 1) c) -
    L.z' (i + 1) = r at hHp hres
  have hdot : L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) - L.β (i + 1) * (L.v (i + 2) ⬝ᵥ L.v (i + 2)) =
      ((basisOf L.v (i + 1))ᵀ *ᵥ L.v (i + 2)) ⬝ᵥ (fun c => L.h (i + 1) c) +
      L.v (i + 2) ⬝ᵥ r - L.v (i + 2) ⬝ᵥ L.δ (i + 1) +
      L.α (i + 1) * (L.v (i + 2) ⬝ᵥ L.v (i + 1)) - L.v (i + 2) ⬝ᵥ L.ez (i + 1) +
      L.β i * (L.v (i + 2) ⬝ᵥ L.v i) - L.v (i + 2) ⬝ᵥ L.ew (i + 1) -
      L.v (i + 2) ⬝ᵥ L.eu (i + 1) := by
    rw [hHp, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    ring
  have hdv := EuclideanSpace.abs_dotProduct_le_norm (L.v (i + 2))
  have t1 : |((basisOf L.v (i + 1))ᵀ *ᵥ L.v (i + 2)) ⬝ᵥ (fun c => L.h (i + 1) c)| ≤
      1 / 100 * (105 / 100 * (3 / 2 * specNorm L.H)) :=
    (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
      (mul_le_mul hG (hh.trans (by gcongr)) (norm_nonneg _) (by norm_num))
  have t2 : |L.v (i + 2) ⬝ᵥ r| ≤ 101 / 100 * (1 / 100 * (3 / 2 * specNorm L.H)) :=
    (hdv _).trans (mul_le_mul hvn (hres.trans (mul_le_mul hε₂ hz (norm_nonneg _)
      (by norm_num))) (norm_nonneg _) (by norm_num))
  have t3 : |L.v (i + 2) ⬝ᵥ L.δ (i + 1)| ≤
      101 / 100 * (1 / 300 * (103 / 100 * (3 / 2 * specNorm L.H))) :=
    (hdv _).trans (mul_le_mul hvn (hδ.trans (mul_le_mul hε (hz'.trans (by gcongr))
      (norm_nonneg _) (by norm_num))) (norm_nonneg _) (by norm_num))
  have t4 : |L.α (i + 1) * (L.v (i + 2) ⬝ᵥ L.v (i + 1))| ≤ 3 / 2 * specNorm L.H * (1 / 100) := by
    rw [abs_mul, dotProduct_comm]
    exact mul_le_mul hα ((abs_v_dotProduct_le L _ i (by omega)).trans hG) (abs_nonneg _)
      (by positivity)
  have t5 : |L.v (i + 2) ⬝ᵥ L.ez (i + 1)| ≤ 101 / 100 * (1 / 300 *
      (103 / 100 * specNorm L.H + 102 / 100 * (3 / 2 * specNorm L.H) +
        3 / 2 * specNorm L.H * (101 / 100))) :=
    (hdv _).trans (mul_le_mul hvn (hez.trans (mul_le_mul_of_nonneg_right hε (by positivity)))
      (norm_nonneg _) (by norm_num))
  have t6 : |L.β i * (L.v (i + 2) ⬝ᵥ L.v i)| ≤ 3 / 2 * specNorm L.H * (1 / 100) := by
    rcases Nat.eq_zero_or_pos i with h0 | h0
    · subst h0
      simp only [L.β_zero, zero_mul, abs_zero]
      positivity
    · have := abs_v_dotProduct_le L (L.v (i + 2)) (i - 1) (show i - 1 < i + 1 by omega)
      rw [Nat.sub_add_cancel h0] at this
      rw [abs_mul, dotProduct_comm]
      exact mul_le_mul hβi (this.trans hG) (abs_nonneg _) (by positivity)
  have t7 : |L.v (i + 2) ⬝ᵥ L.ew (i + 1)| ≤
      101 / 100 * (1 / 300 * (102 / 100 * specNorm L.H + 101 / 100 * (3 / 2 * specNorm L.H))) :=
    (hdv _).trans (mul_le_mul hvn (hew.trans (mul_le_mul_of_nonneg_right hε (by positivity)))
      (norm_nonneg _) (by norm_num))
  have t8 : |L.v (i + 2) ⬝ᵥ L.eu (i + 1)| ≤ 101 / 100 * (101 / 100 * (1 / 300) * specNorm L.H) :=
    (hdv _).trans (mul_le_mul hvn (heu.trans (by gcongr)) (norm_nonneg _) (by norm_num))
  rw [hdot]
  rw [abs_le] at t1 t2 t3 t4 t5 t6 t7 t8 ⊢
  constructor <;> linarith [t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2, t5.1, t5.2, t6.1,
    t6.2, t7.1, t7.2, t8.1, t8.2]

/-- The first update of step $i + 2$ is bounded through symmetry of $\mathbf{H}$. -/
private lemma norm_w_succ_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {i : ℕ} (hi : i + 1 < k)
    (hIH : ∀ c ≤ i, |L.α (c + 1)| ≤ 3 / 2 * specNorm L.H ∧ L.β (c + 1) ≤ 3 / 2 * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.z (c + 1))‖ ≤ 3 / 2 * specNorm L.H) :
    ‖WithLp.toLp 2 (L.w (i + 1 + 1))‖ ≤ 104 / 100 * specNorm L.H := by
  obtain ⟨-, hε, -, -, -, -⟩ := levels_le_of_recLevel_le L hrec
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  have hik : i < k := by omega
  obtain ⟨hα, hb, hz⟩ := hIH i le_rfl
  have hb0 := (L.β_succ_pos hik).le
  have hβi : |L.β i| ≤ 3 / 2 * specNorm L.H := by
    rcases i with _ | c
    · simp only [L.β_zero, abs_zero]; positivity
    · rw [abs_of_pos (L.β_succ_pos (by omega))]; exact (hIH c (by omega)).2.1
  have hX0 := abs_v_dotProduct_mulVec_sub_le L hη hsmall hrec hik hα hz hβi
  obtain ⟨heu, hew, -⟩ := norm_eu_ew_w_le L hrec hi (B := 3 / 2 * specNorm L.H)
    (by rw [abs_of_nonneg hb0]; exact hb)
  have hv := L.norm_v_sq_le (i := i + 2) (by omega)
  have hp := L.norm_v_sq_le (i := i + 1) (by omega)
  have hv' := L.abs_norm_v_sq_sub_one_le (i + 2) (by omega) (by omega)
  have hp' := L.abs_norm_v_sq_sub_one_le (i + 1) (by omega) (by omega)
  rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at hv hp hv' hp'
  have hsym : L.v (i + 1) ⬝ᵥ (L.H *ᵥ L.v (i + 2)) = L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, L.transpose_H, dotProduct_comm]
  have hHv : ‖WithLp.toLp 2 (L.H *ᵥ L.v (i + 2))‖ ^ 2 ≤ specNorm L.H ^ 2 * (1 + L.ε) := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le L.H (L.v (i + 2))) 2
    rw [mul_pow, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self (L.v (i + 2))] at h1
    exact h1.trans (by gcongr)
  have hy2 : ‖WithLp.toLp 2 (L.H *ᵥ L.v (i + 2) - L.β (i + 1) • L.v (i + 1))‖ ^ 2 =
      ‖WithLp.toLp 2 (L.H *ᵥ L.v (i + 2))‖ ^ 2 -
        2 * L.β (i + 1) * (L.v (i + 1) ⬝ᵥ (L.H *ᵥ L.v (i + 2))) +
        L.β (i + 1) ^ 2 * (L.v (i + 1) ⬝ᵥ L.v (i + 1)) := by
    simp only [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul,
      dotProduct_comm (L.H *ᵥ L.v (i + 2)) (L.v (i + 1))]
    ring
  rw [hsym] at hy2
  have hX : |L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) - L.β (i + 1) * (L.v (i + 1) ⬝ᵥ L.v (i + 1))| ≤
      11 / 100 * specNorm L.H := by
    have hd : |L.v (i + 2) ⬝ᵥ L.v (i + 2) - L.v (i + 1) ⬝ᵥ L.v (i + 1)| ≤ 2 * L.ε := by
      rw [abs_le] at hv' hp' ⊢; constructor <;> linarith [hv'.1, hv'.2, hp'.1, hp'.2]
    have := mul_le_mul hb hd (abs_nonneg _) (by positivity)
    rw [← abs_of_nonneg hb0, ← abs_mul] at this
    have e : L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) -
        L.β (i + 1) * (L.v (i + 1) ⬝ᵥ L.v (i + 1)) =
        (L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) - L.β (i + 1) * (L.v (i + 2) ⬝ᵥ L.v (i + 2))) +
        L.β (i + 1) * (L.v (i + 2) ⬝ᵥ L.v (i + 2) - L.v (i + 1) ⬝ᵥ L.v (i + 1)) := by ring
    rw [e]
    refine (abs_add_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hε hs]
  have hy : ‖WithLp.toLp 2 (L.H *ᵥ L.v (i + 2) - L.β (i + 1) • L.v (i + 1))‖ ≤
      101 / 100 * specNorm L.H := by
    have hp1 : 1 - L.ε ≤ L.v (i + 1) ⬝ᵥ L.v (i + 1) := by
      linarith [neg_abs_le (L.v (i + 1) ⬝ᵥ L.v (i + 1) - 1)]
    have h2 : ‖WithLp.toLp 2 (L.H *ᵥ L.v (i + 2) - L.β (i + 1) • L.v (i + 1))‖ ^ 2 ≤
        (101 / 100 * specNorm L.H) ^ 2 := by
      rw [abs_le] at hX
      nlinarith [mul_le_mul_of_nonneg_left hp1 (sq_nonneg (L.β (i + 1))),
        mul_le_mul_of_nonneg_left hX.1 hb0, sq_nonneg (99 / 100 * L.β (i + 1) - 11 / 100 *
          specNorm L.H), mul_nonneg hε0 (sq_nonneg (specNorm L.H))]
    nlinarith [norm_nonneg (WithLp.toLp 2 (L.H *ᵥ L.v (i + 2) - L.β (i + 1) • L.v (i + 1)))]
  have hw : L.w (i + 1 + 1) = (L.H *ᵥ L.v (i + 2) - L.β (i + 1) • L.v (i + 1)) +
      L.eu (i + 1 + 1) + L.ew (i + 1 + 1) := by
    rw [L.w_eq (i + 1) hi, L.u_eq (i + 1) hi]
    abel
  rw [hw, WithLp.toLp_add, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  nlinarith [norm_add_le (WithLp.toLp 2 (L.H *ᵥ L.v (i + 2) - L.β (i + 1) • L.v (i + 1)))
    (WithLp.toLp 2 (L.eu (i + 1 + 1)))]

/-- **Coefficient bounds without growth in $j$**: under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$ and $\mu + \varepsilon + \varepsilon_2 \le 1/100$, for
$j < k$, $\lvert\alpha_{j+1}\rvert$, $\beta_{j+1}$ and $\|\mathbf{z}_{j+1}\|$ are at most
$\tfrac32\|\mathbf{H}\|_2$. [Paige1976, (28), (30), (34)] for plain Lanczos
(there with growth); here orthogonality is available first. -/
theorem coeff_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) :
    ∀ j < k, |L.α (j + 1)| ≤ 3 / 2 * specNorm L.H ∧ L.β (j + 1) ≤ 3 / 2 * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 3 / 2 * specNorm L.H := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    intro hj
    refine coeff_le_of_norm_w_le L hη hsmall hrec hj ?_
    rcases j with _ | i
    · have := (norm_eu_ew_w_le L hrec hj (B := 0) (by simp [L.β_zero])).2.2
      linarith [specNorm_nonneg L.H]
    · exact norm_w_succ_le L hη hsmall hrec hj fun c hc => IH c (by omega) (by omega)

/-- The coefficients $\beta_i$, $i \le k$, satisfy
$\lvert\beta_i\rvert \le \tfrac32\|\mathbf{H}\|_2$, under $\eta_0 \le 1/100$, the fixed-point
condition $\sqrt{3(k+1)}\,\mu \le \eta_0$ and $\mu + \varepsilon + \varepsilon_2 \le 1/100$; the
form of `NLAlib.LanczosReorthRun.coeff_le` used for the previous coefficient of a step. -/
theorem abs_β_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {i : ℕ} (hi : i ≤ k) : |L.β i| ≤ 3 / 2 * specNorm L.H := by
  rcases i with _ | i
  · simp only [L.β_zero, abs_zero]
    positivity
  · rw [abs_of_pos (L.β_succ_pos (by omega))]
    exact (L.coeff_le hη hsmall hrec i (by omega)).2.1

/-- The orthogonalized vectors satisfy $\|\mathbf{z}_{j+1}'\| \le \tfrac{151}{100}\|\mathbf{H}\|_2$
for $j < k$, under $\eta_0 \le 1/100$, the fixed-point condition
$\sqrt{3(k+1)}\,\mu \le \eta_0$ and $\mu + \varepsilon + \varepsilon_2 \le 1/100$. -/
theorem norm_z'_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.z' (j + 1))‖ ≤ 151 / 100 * specNorm L.H := by
  have hβ := (L.coeff_le hη hsmall hrec j hj).2.1
  have hε := (levels_le_of_recLevel_le L hrec).2.1
  have := L.abs_β_sub_le j hj
  nlinarith [neg_abs_le (L.β (j + 1) - ‖WithLp.toLp 2 (L.z' (j + 1))‖),
    norm_nonneg (WithLp.toLp 2 (L.z' (j + 1))),
    mul_le_mul_of_nonneg_right hε (norm_nonneg (WithLp.toLp 2 (L.z' (j + 1))))]

/-- Off-diagonal entries of the Gram matrix are at most $\mu$. -/
private lemma abs_v_dotProduct_v_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    {a b : ℕ} (hab : a < b) (hb : b ≤ k + 1) : |L.v a ⬝ᵥ L.v b| ≤ L.orthLevel := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp only [L.v_zero, zero_dotProduct, abs_zero]
    exact L.orthLevel_nonneg
  obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 2 := ⟨b - 2, by omega⟩
  have hV := L.specNorm_transpose_mul_self_sub_one_le hη hsmall (m := b' + 1) (by omega)
  exact (abs_v_dotProduct_le L _ a' (by omega)).trans
    (L.norm_transpose_mulVec_v_le (by omega) hV hη)

/-- The coefficients of the previous columns against $\mathbf{v}_{j+1}$ are at most $\mu$. -/
private lemma norm_transpose_basisOf_mulVec_v_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    {m j : ℕ} (hm : m ≤ j) (hj : 1 ≤ j) (hjk : j ≤ k) :
    ‖WithLp.toLp 2 ((basisOf L.v m)ᵀ *ᵥ L.v (j + 1))‖ ≤ L.orthLevel := by
  have he : (basisOf L.v m)ᵀ *ᵥ L.v (j + 1) =
      ((basisOf L.v j)ᵀ *ᵥ L.v (j + 1)) ∘ Fin.castLE hm := by
    ext d
    simp [basisOf, Matrix.mulVec, dotProduct]
  rw [he]
  refine (EuclideanSpace.norm_toLp_comp_le_of_injective (Fin.castLE_injective hm) _).trans ?_
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  exact L.norm_transpose_mulVec_v_le (by omega)
    (L.specNorm_transpose_mul_self_sub_one_le hη hsmall (m := j' + 1) (by omega)) hη

/-- The two neighbouring coefficients in component $c$ nearly cancel. -/
private lemma abs_β_mul_sub_β_mul_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j c : ℕ} (hj : j < k) (hc : c < j) :
    |L.β (c + 1) * (L.v (j + 1) ⬝ᵥ L.v (c + 2)) - L.β j * (L.v (c + 1) ⬝ᵥ L.v j)| ≤
      3 * (specNorm L.H * L.orthLevel) := by
  have hs := specNorm_nonneg L.H
  have hD3 := L.coeff_le hη hsmall hrec
  have hβle := fun i (hi : i ≤ j) => L.abs_β_le hη hsmall hrec (i := i) (by omega)
  have hεμ : L.ε ≤ L.orthLevel := by
    have := L.ε₁_nonneg
    have := (levels_le_of_recLevel_le L hrec).1
    have := L.ε_nonneg
    simp only [orthLevel]; linarith
  have hent := fun {a b : ℕ} (hab : a < b) (hb : b ≤ k + 1) =>
    abs_v_dotProduct_v_le L hη hsmall hab hb
  rcases Nat.lt_or_ge (c + 1) j with h1 | h1
  · have p1 : |L.β (c + 1) * (L.v (j + 1) ⬝ᵥ L.v (c + 2))| ≤ 3 / 2 * specNorm L.H *
        L.orthLevel := by
      rw [abs_mul, dotProduct_comm]
      exact mul_le_mul (hβle _ (by omega)) (hent (by omega) (by omega)) (abs_nonneg _)
        (by positivity)
    have p2 : |L.β j * (L.v (c + 1) ⬝ᵥ L.v j)| ≤ 3 / 2 * specNorm L.H * L.orthLevel := by
      rw [abs_mul]
      exact mul_le_mul (hβle _ le_rfl) (hent (by omega) (by omega)) (abs_nonneg _)
        (by positivity)
    rw [abs_le] at p1 p2 ⊢
    constructor <;> linarith [p1.1, p1.2, p2.1, p2.2]
  · obtain rfl : j = c + 1 := by omega
    have h2 := L.abs_norm_v_sq_sub_one_le (c + 2) (by omega) (by omega)
    have h3 := L.abs_norm_v_sq_sub_one_le (c + 1) (by omega) (by omega)
    rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at h2 h3
    have hd : |L.v (c + 2) ⬝ᵥ L.v (c + 2) - L.v (c + 1) ⬝ᵥ L.v (c + 1)| ≤ 2 * L.ε := by
      rw [abs_le] at h2 h3 ⊢; constructor <;> linarith [h2.1, h2.2, h3.1, h3.2]
    rw [show c + 1 + 1 = c + 2 from rfl, ← mul_sub, abs_mul]
    refine (mul_le_mul (hβle _ le_rfl) hd (abs_nonneg _) (by positivity)).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left hεμ hs]

/-- Component $c < j$ of $\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{z}_{j+1}$ expanded by the
relation at step $c$ and symmetry. -/
private lemma v_dotProduct_z_eq {j c : ℕ} (hj : j < k) (hc : c < j) :
    L.v (c + 1) ⬝ᵥ L.z (j + 1) =
      ((basisOf L.v (c + 1))ᵀ *ᵥ L.v (j + 1)) ⬝ᵥ (fun i => L.h (c + 1) i) +
      L.v (j + 1) ⬝ᵥ (L.z (c + 1) - basisOf L.v (c + 1) *ᵥ (fun i => L.h (c + 1) i) -
        L.z' (c + 1)) - L.v (j + 1) ⬝ᵥ L.δ (c + 1) +
      L.α (c + 1) * (L.v (j + 1) ⬝ᵥ L.v (c + 1)) - L.v (j + 1) ⬝ᵥ L.ez (c + 1) +
      L.β c * (L.v (j + 1) ⬝ᵥ L.v c) - L.v (j + 1) ⬝ᵥ L.ew (c + 1) -
      L.v (j + 1) ⬝ᵥ L.eu (c + 1) +
      (L.β (c + 1) * (L.v (j + 1) ⬝ᵥ L.v (c + 2)) - L.β j * (L.v (c + 1) ⬝ᵥ L.v j)) +
      L.v (c + 1) ⬝ᵥ L.eu (j + 1) + L.v (c + 1) ⬝ᵥ L.ew (j + 1) -
      L.α (j + 1) * (L.v (c + 1) ⬝ᵥ L.v (j + 1)) + L.v (c + 1) ⬝ᵥ L.ez (j + 1) := by
  have hck : c < k := by omega
  have hHq : L.H *ᵥ L.v (c + 1) = basisOf L.v (c + 1) *ᵥ (fun i => L.h (c + 1) i) +
      (L.z (c + 1) - basisOf L.v (c + 1) *ᵥ (fun i => L.h (c + 1) i) - L.z' (c + 1)) +
      L.β (c + 1) • L.v (c + 2) - L.δ (c + 1) + L.α (c + 1) • L.v (c + 1) - L.ez (c + 1) +
      L.β c • L.v c - L.ew (c + 1) - L.eu (c + 1) := by
    rw [L.smul_v_eq c hck, L.z_eq c hck, L.w_eq c hck, L.u_eq c hck]
    abel
  have hzexp : L.z (j + 1) = L.H *ᵥ L.v (j + 1) - L.β j • L.v j + L.eu (j + 1) + L.ew (j + 1) -
      L.α (j + 1) • L.v (j + 1) + L.ez (j + 1) := by
    rw [L.z_eq j hj, L.w_eq j hj, L.u_eq j hj]
    abel
  have hsym : L.v (c + 1) ⬝ᵥ (L.H *ᵥ L.v (j + 1)) = L.v (j + 1) ⬝ᵥ (L.H *ᵥ L.v (c + 1)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, L.transpose_H, dotProduct_comm]
  rw [hzexp]
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  rw [hsym, hHq, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec]
  simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  ring

/-- The reorthogonalization term of component $c$ is second order. -/
private lemma abs_transpose_mulVec_dotProduct_h_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j c : ℕ} (hj : j < k) (hc : c < j)
    (hh : ‖WithLp.toLp 2 (fun i : Fin (c + 1) => L.h (c + 1) i)‖ ≤
      24 * Real.sqrt ((c : ℝ) + 1) * L.recLevel * specNorm L.H) :
    |((basisOf L.v (c + 1))ᵀ *ᵥ L.v (j + 1)) ⬝ᵥ (fun i => L.h (c + 1) i)| ≤
      24 / 100 * (L.recLevel * specNorm L.H) := by
  obtain ⟨-, -, -, hμ0, -, -⟩ := levels_le_of_recLevel_le L hrec
  have hs := specNorm_nonneg L.H
  have hck : c < k := by omega
  have hR : L.recLevel = L.orthLevel + L.ε + L.ε₂ := rfl
  have hg := norm_transpose_basisOf_mulVec_v_le L hη hsmall (m := c + 1) (j := j) (by omega)
    (by omega) hj.le
  have hsq : Real.sqrt ((c : ℝ) + 1) * L.orthLevel ≤ 1 / 100 := by
    refine le_trans ?_ (hsmall.trans hη)
    have : (c : ℝ) < k := by exact_mod_cast hck
    gcongr
    linarith
  have hrec0 : 0 ≤ L.recLevel := by rw [hR]; linarith [L.ε₂_nonneg, L.ε_nonneg]
  refine (EuclideanSpace.abs_dotProduct_le_norm _ _).trans
    ((mul_le_mul hg hh (norm_nonneg _) hμ0).trans ?_)
  nlinarith [mul_le_mul_of_nonneg_right hsq (mul_nonneg hrec0 hs)]

/-- Component $c < j$ of $\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{z}_{j+1}$, through the relation at
step $c$ and symmetry. -/
private lemma abs_v_dotProduct_z_le_of_lt (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j c : ℕ} (hj : j < k) (hc : c < j)
    (hh : ‖WithLp.toLp 2 (fun i : Fin (c + 1) => L.h (c + 1) i)‖ ≤
      24 * Real.sqrt ((c : ℝ) + 1) * L.recLevel * specNorm L.H) :
    |L.v (c + 1) ⬝ᵥ L.z (j + 1)| ≤ 20 * L.recLevel * specNorm L.H := by
  obtain ⟨-, hε, hε₂, hμ0, hμ, -⟩ := levels_le_of_recLevel_le L hrec
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  have hck : c < k := by omega
  have hD3 := L.coeff_le hη hsmall hrec
  obtain ⟨hαc, hβc1, hzc⟩ := hD3 c hck
  obtain ⟨hαj, -, -⟩ := hD3 j hj
  have hβle := fun i (hi : i ≤ j) => L.abs_β_le hη hsmall hrec (i := i) (by omega)
  obtain ⟨heuc, hewc, hwc⟩ := norm_eu_ew_w_le L hrec hck (hβle c hc.le)
  obtain ⟨heuj, hewj, hwj⟩ := norm_eu_ew_w_le L hrec hj (hβle j le_rfl)
  have hv := fun i (hi : i ≤ k + 1) => L.norm_v_le hi
  have hezc : ‖WithLp.toLp 2 (L.ez (c + 1))‖ ≤ L.ε * (103 / 100 * specNorm L.H +
      102 / 100 * (3 / 2 * specNorm L.H) + 3 / 2 * specNorm L.H * (101 / 100)) :=
    (L.norm_ez_le c hck).trans (by gcongr; exact hv _ (by omega))
  have hezj : ‖WithLp.toLp 2 (L.ez (j + 1))‖ ≤ L.ε * (103 / 100 * specNorm L.H +
      102 / 100 * (3 / 2 * specNorm L.H) + 3 / 2 * specNorm L.H * (101 / 100)) :=
    (L.norm_ez_le j hj).trans (by gcongr; exact hv _ (by omega))
  have hres := (L.orth_eq c hck).residual 
    (L.specNorm_transpose_mul_self_sub_one_le hη hsmall (m := c + 1) (by omega))
  have hδ := L.norm_δ_le c hck
  have hz' := L.norm_z'_le hη hsmall hrec hck
  have hdot := v_dotProduct_z_eq L hj hc
  generalize hr : L.z (c + 1) - basisOf L.v (c + 1) *ᵥ (fun i => L.h (c + 1) i) -
    L.z' (c + 1) = r at hdot hres
  have hεμ : L.ε ≤ L.orthLevel := by
    have := L.ε₁_nonneg
    have := (levels_le_of_recLevel_le L hrec).1
    simp only [orthLevel]; linarith
  have hent := fun {a b : ℕ} (hab : a < b) (hb : b ≤ k + 1) =>
    abs_v_dotProduct_v_le L hη hsmall hab hb
  have hvj := hv (j + 1) (by omega)
  have hvc := hv (c + 1) (by omega)
  have hdv := EuclideanSpace.abs_dotProduct_le_norm (L.v (j + 1))
  have hdq := EuclideanSpace.abs_dotProduct_le_norm (L.v (c + 1))
  have hR : L.recLevel = L.orthLevel + L.ε + L.ε₂ := rfl
  have t1 := abs_transpose_mulVec_dotProduct_h_le L hη hsmall hrec hj hc hh
  have t2 : |L.v (j + 1) ⬝ᵥ r| ≤ 101 / 100 * (L.ε₂ * (3 / 2 * specNorm L.H)) :=
    (hdv r).trans (mul_le_mul hvj (hres.trans (mul_le_mul_of_nonneg_left hzc L.ε₂_nonneg))
      (norm_nonneg _) (by norm_num))
  have t3 : |L.v (j + 1) ⬝ᵥ L.δ (c + 1)| ≤ 101 / 100 * (L.ε * (151 / 100 * specNorm L.H)) :=
    (hdv _).trans (mul_le_mul hvj (hδ.trans (mul_le_mul_of_nonneg_left hz' hε0))
      (norm_nonneg _) (by norm_num))
  have t4 : |L.α (c + 1) * (L.v (j + 1) ⬝ᵥ L.v (c + 1))| ≤
      3 / 2 * specNorm L.H * L.orthLevel := by
    rw [abs_mul, dotProduct_comm]
    exact mul_le_mul hαc (hent (by omega) (by omega)) (abs_nonneg _) (by positivity)
  have t5 := (hdv (L.ez (c + 1))).trans (mul_le_mul hvj hezc (norm_nonneg _) (by norm_num))
  have t6 : |L.β c * (L.v (j + 1) ⬝ᵥ L.v c)| ≤ 3 / 2 * specNorm L.H * L.orthLevel := by
    rw [abs_mul, dotProduct_comm]
    exact mul_le_mul (hβle c hc.le) (hent (by omega) (by omega)) (abs_nonneg _) (by positivity)
  have t7 := (hdv (L.ew (c + 1))).trans (mul_le_mul hvj hewc (norm_nonneg _) (by norm_num))
  have t8 := (hdv (L.eu (c + 1))).trans (mul_le_mul hvj heuc (norm_nonneg _) (by norm_num))
  have t9 := abs_β_mul_sub_β_mul_le L hη hsmall hrec hj hc
  have t10 := (hdq (L.eu (j + 1))).trans (mul_le_mul hvc heuj (norm_nonneg _) (by norm_num))
  have t11 := (hdq (L.ew (j + 1))).trans (mul_le_mul hvc hewj (norm_nonneg _) (by norm_num))
  have t12 : |L.α (j + 1) * (L.v (c + 1) ⬝ᵥ L.v (j + 1))| ≤
      3 / 2 * specNorm L.H * L.orthLevel := by
    rw [abs_mul]
    exact mul_le_mul hαj (hent (by omega) (by omega)) (abs_nonneg _) (by positivity)
  have t13 := (hdq (L.ez (j + 1))).trans (mul_le_mul hvc hezj (norm_nonneg _) (by norm_num))
  rw [hdot, hR]
  rw [hR] at t1
  rw [abs_le] at t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 t12 t13 ⊢
  have p1 := mul_nonneg hμ0 hs
  have p2 := mul_nonneg L.ε₂_nonneg hs
  have p3 := mul_nonneg hε0 hs
  constructor <;> linarith only [p1, p2, p3, t1.1, t1.2, t2.1, t2.2, t3.1, t3.2, t4.1, t4.2,
    t5.1, t5.2, t6.1, t6.2, t7.1, t7.2, t8.1, t8.2, t9.1, t9.2, t10.1, t10.2, t11.1, t11.2,
    t12.1, t12.2, t13.1, t13.2]

/-- The current component $\mathbf{v}_{j+1}^{\mathsf{T}}\mathbf{z}_{j+1} = \alpha(1 -
\|\mathbf{v}\|^2) - e_\alpha + \mathbf{v}^{\mathsf{T}}\mathbf{e}^z$ is of order $\varepsilon$. -/
private lemma abs_v_dotProduct_z_self_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j : ℕ} (hj : j < k) :
    |L.v (j + 1) ⬝ᵥ L.z (j + 1)| ≤ 20 * L.recLevel * specNorm L.H := by
  obtain ⟨-, hε, -, hμ0, -, -⟩ := levels_le_of_recLevel_le L hrec
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  have hD3 := L.coeff_le hη hsmall hrec
  obtain ⟨hα, -, -⟩ := hD3 j hj
  have hβj := L.abs_β_le hη hsmall hrec (i := j) hj.le
  obtain ⟨-, -, hw⟩ := norm_eu_ew_w_le L hrec hj hβj
  have hv := L.norm_v_le (i := j + 1) (by omega)
  have hv1 := L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
  rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at hv1
  have hez : ‖WithLp.toLp 2 (L.ez (j + 1))‖ ≤ L.ε * (103 / 100 * specNorm L.H +
      102 / 100 * (3 / 2 * specNorm L.H) + 3 / 2 * specNorm L.H * (101 / 100)) :=
    (L.norm_ez_le j hj).trans (by gcongr)
  have heα : |L.eα (j + 1)| ≤ L.ε * (101 / 100) *
      (103 / 100 * specNorm L.H + 102 / 100 * (3 / 2 * specNorm L.H)) :=
    (L.abs_eα_le j hj).trans (by gcongr)
  have hdot : L.v (j + 1) ⬝ᵥ L.z (j + 1) =
      L.α (j + 1) * (1 - L.v (j + 1) ⬝ᵥ L.v (j + 1)) - L.eα (j + 1) +
        L.v (j + 1) ⬝ᵥ L.ez (j + 1) := by
    have ha := L.α_eq j hj
    rw [L.z_eq j hj]
    simp only [dotProduct_add, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    rw [ha]
    ring
  have t1 : |L.α (j + 1) * (1 - L.v (j + 1) ⬝ᵥ L.v (j + 1))| ≤ 3 / 2 * specNorm L.H * L.ε := by
    rw [abs_mul, abs_sub_comm]
    exact mul_le_mul hα hv1 (abs_nonneg _) (by positivity)
  have t3 := (EuclideanSpace.abs_dotProduct_le_norm (L.v (j + 1)) (L.ez (j + 1))).trans
    (mul_le_mul hv hez (norm_nonneg _) (by norm_num))
  have hR : L.recLevel = L.orthLevel + L.ε + L.ε₂ := rfl
  rw [hdot, hR]
  rw [abs_le] at t1 heα t3 ⊢
  have p1 := mul_nonneg hμ0 hs
  have p2 := mul_nonneg L.ε₂_nonneg hs
  have p3 := mul_nonneg hε0 hs
  constructor <;> linarith only [p1, p2, p3, t1.1, t1.2, heα.1, heα.2, t3.1, t3.2]

/-- **The discarded reorthogonalization coefficients are small**: for the symmetric $\mathbf{H}$ of
a run, under $\eta_0 \le 1/100$, the fixed-point condition $\sqrt{3(k+1)}\,\mu \le \eta_0$, $\mu +
\varepsilon + \varepsilon_2 \le 1/100$ and $\tau \le 1$, every $j < k$ has $\|\mathbf{h}_{j+1}\| \le
24\sqrt{j+1}\,(\mu + \varepsilon + \varepsilon_2) \|\mathbf{H}\|_2$. The one place symmetry is
needed: without it the coefficients are $O(1)$ (Arnoldi). [Paige1971, §6.1, (6.8)] in substance (the
coefficient matrix $\mathbf{B}$ there). -/
theorem norm_coef_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∀ j < k, ‖WithLp.toLp 2 (fun i : Fin (j + 1) => L.h (j + 1) i)‖ ≤
      24 * Real.sqrt ((j : ℝ) + 1) * L.recLevel * specNorm L.H := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    intro hj
    obtain ⟨hq, -, hε₂, hμ0, -, -⟩ := levels_le_of_recLevel_le L hrec
    have hs := specNorm_nonneg L.H
    have hR : L.recLevel = L.orthLevel + L.ε + L.ε₂ := rfl
    have hrec0 : 0 ≤ L.recLevel := by rw [hR]; linarith [L.ε_nonneg, L.ε₂_nonneg]
    have hV := L.specNorm_transpose_mul_self_sub_one_le hη hsmall (m := j + 1) (by omega)
    have hη0 : 0 ≤ L.η₀ := (specNorm_nonneg _).trans hV
    have hO := L.orth_eq j hj
    have hA := hO.norm_coef_le hV (by linarith)
    obtain ⟨-, hβ, hz⟩ := L.coeff_le hη hsmall hrec j hj
    have hsq1 : 1 ≤ Real.sqrt ((j : ℝ) + 1) := by
      exact Real.one_le_sqrt.mpr (by simp)
    -- the components of `Vᵀ z`
    have hVz : ‖WithLp.toLp 2 ((basisOf L.v (j + 1))ᵀ *ᵥ L.z (j + 1))‖ ≤
        Real.sqrt ((j : ℝ) + 1) * (20 * L.recLevel * specNorm L.H) := by
      refine (EuclideanSpace.norm_toLp_le_mul_add_of_forall_abs_le (le_refl (0 : ℝ))
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 20) hrec0) hs) (x := 0)
        fun c => ?_).trans ?_
      · rw [transpose_basisOf_mulVec_apply, Pi.zero_apply, abs_zero, mul_zero, zero_add]
        rcases Nat.lt_or_ge (c : ℕ) j with h | h
        · exact abs_v_dotProduct_z_le_of_lt L hη hsmall hrec hj h (IH c h (by omega))
        · rw [show (c : ℕ) = j by omega]
          exact abs_v_dotProduct_z_self_le L hη hsmall hrec hj
      · simp only [zero_mul, zero_add, Fintype.card_fin]
        push_cast
        rfl
    -- `Vᵀ z'`
    have hz' := L.norm_z'_le hη hsmall hrec hj
    have hε₃ : L.ε₃ ≤ L.ε₃ / L.τ := le_div_self L.ε₃_nonneg L.τ_pos hτ
    have hVz' : ‖WithLp.toLp 2 ((basisOf L.v (j + 1))ᵀ *ᵥ L.z' (j + 1))‖ ≤
        151 / 100 * (L.orthLevel * specNorm L.H) / 2 := by
      refine (hO.orth hV).trans ?_
      have h1 := mul_le_mul_of_nonneg_left hz' L.ε₁_nonneg
      have h2 := mul_le_mul hε₃ hz (norm_nonneg _) hq
      have h3 : L.ε₁ + L.ε₃ / L.τ ≤ L.orthLevel / 2 := by
        simp only [orthLevel]; linarith [L.ε_nonneg]
      nlinarith [mul_le_mul_of_nonneg_right h3 hs, mul_nonneg hq hs]
    have hsqη : Real.sqrt (1 + L.η₀) ≤ 101 / 100 :=
      Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
    have h3 : Real.sqrt (1 + L.η₀) * L.ε₂ * ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤
        101 / 100 * L.ε₂ * (3 / 2 * specNorm L.H) :=
      mul_le_mul (mul_le_mul_of_nonneg_right hsqη L.ε₂_nonneg) hz (norm_nonneg _)
        (mul_nonneg (by norm_num) L.ε₂_nonneg)
    have hRs : L.orthLevel * specNorm L.H + L.ε₂ * specNorm L.H ≤
        Real.sqrt ((j : ℝ) + 1) * (L.recLevel * specNorm L.H) := by
      have := mul_le_mul_of_nonneg_right hsq1 (mul_nonneg hrec0 hs)
      rw [hR] at this ⊢
      nlinarith [mul_nonneg L.ε_nonneg hs]
    rw [le_div_iff₀ (by linarith)] at hA
    have hHn0 := norm_nonneg (WithLp.toLp 2 (fun i : Fin (j + 1) => L.h (j + 1) i))
    nlinarith [mul_le_mul_of_nonneg_left hη hHn0, mul_nonneg hrec0 hs,
      mul_nonneg (Real.sqrt_nonneg ((j : ℝ) + 1)) (mul_nonneg hrec0 hs)]

end LanczosReorthRun

end NLAlib
