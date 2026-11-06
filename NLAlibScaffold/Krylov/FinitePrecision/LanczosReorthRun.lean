/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosReorthRun
public import NLAlibScaffold.Matrix.Perturbation.OrthErr

/-!
# Orthogonality, coefficients and the perturbed relation of a reorthogonalized run (scaffold)

Statements for `NLAlib/Krylov/FinitePrecision/LanczosReorthRun.lean` (stage LANCZOS-REORTH,
design note `docs/design/Krylov-LanczosReorth.md` §3.2–3.3, ids D2–D8 and the prefix
restriction), in the proof order D5 → D3 → D4 → D6 → D7: orthogonality of the computed basis on
the admissible prefix [Paige1970], the coefficient bounds, the reorthogonalization coefficients
(the one place symmetry is used), the perturbed three-term relation with the discarded
coefficients in its residual, the projection form [Simon1984b], and the dimension count.

Common hypotheses: `hη : L.η₀ ≤ 1 / 100` and the fixed-point condition
`hsmall : √(3(k+1)) * L.orthLevel ≤ L.η₀` of §1.2; for the coefficient and residual bounds also
`hrec : L.recLevel ≤ 1 / 100` and `hτ : L.τ ≤ 1`. The constants are generous proof-sketch values;
a proof giving other constants records them in `docs/constants.toml`.

## Main results

* `NLAlib.LanczosReorthRun.recurrenceError_eq`: the residual of the three-term relation.
* `NLAlib.LanczosReorthRun.norm_transpose_mulVec_v_le`: one column (D5a).
* `NLAlib.LanczosReorthRun.frobNorm_gram_sub_one_le`: S2 (D5).
* `NLAlib.LanczosReorthRun.coeff_le`: D3. `NLAlib.LanczosReorthRun.norm_coef_le`: D4.
* `NLAlib.LanczosReorthRun.frobNorm_residual_le`: S1 (D6).
* `NLAlib.LanczosReorthRun.specNorm_transpose_mul_mul_sub_tridiagonal_le`: S1′ (D7).
* `NLAlib.LanczosReorthRun.succ_le_card`: D8. `NLAlib.LanczosReorthRun.exists_ofLE`: prefixes.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace LanczosReorthRun

variable {n k : ℕ} (L : LanczosReorthRun n k)

/-- **The residual of the three-term relation** (D2): column $j$ of the residual of the
underlying data is the reorthogonalization correction plus the local errors,
$\mathbf{f}_j = \mathbf{V}_{j+1}\mathbf{h}_{j+1} + (\mathbf{z}_{j+1} - \mathbf{V}_{j+1}
\mathbf{h}_{j+1} - \mathbf{z}_{j+1}') - \boldsymbol\delta_{j+1} - \mathbf{e}^u_{j+1} -
\mathbf{e}^w_{j+1} - \mathbf{e}^z_{j+1}$. No printed source.
Proof: unfold `NLAlib.LanczosData.recurrenceError`, `NLAlib.LanczosReorthRun.toLanczosData`;
rewrite with the fields `u_eq`, `w_eq`, `z_eq`, `smul_v_eq` and `abel`. S, about 15 lines. -/
theorem recurrenceError_eq {j : ℕ} (hj : j < k) :
    L.toLanczosData.recurrenceError j =
      basisOf L.v (j + 1) *ᵥ (fun i => L.h (j + 1) i) +
        (L.z (j + 1) - basisOf L.v (j + 1) *ᵥ (fun i => L.h (j + 1) i) - L.z' (j + 1)) -
        L.δ (j + 1) - L.eu (j + 1) - L.ew (j + 1) - L.ez (j + 1) := by
  simp only [LanczosData.recurrenceError, toLanczosData]
  rw [L.smul_v_eq j hj, L.z_eq j hj, L.w_eq j hj, L.u_eq j hj]
  abel

/-- **One admissible column is nearly orthogonal to the previous ones** (D5a): if
$\|\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{V}_{j+1} - \mathbf{I}\|_2 \le \eta_0 \le 1/100$ then
$\|\mathbf{V}_{j+1}^{\mathsf{T}}\mathbf{v}_{j+2}\| \le \mu$ = `NLAlib.LanczosReorthRun.orthLevel`.
[Paige1970] (the criterion in substance).
Proof: $\beta\mathbf{v}_{j+2} = \mathbf{z}' + \boldsymbol\delta$ (`smul_v_eq`); `orth_eq`'s
`IsOrthErr.orth` gives $\|\mathbf{V}^{\mathsf{T}}\mathbf{z}'\| \le \varepsilon_1\|\mathbf{z}'\| +
\varepsilon_3\|\mathbf{z}\|$; admissibility with `abs_ν_sub_le`, `abs_β_sub_le` gives
$\|\mathbf{z}\| \le (1+\varepsilon)/((1-\varepsilon)\tau)\,\|\mathbf{z}'\|$ and $\beta \ge
(1-\varepsilon)\|\mathbf{z}'\| > 0$; $\|\mathbf{V}^{\mathsf{T}}\boldsymbol\delta\| \le
\sqrt{1+\eta_0}\,\varepsilon\|\mathbf{z}'\|$ by
`NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le`;
divide by $\beta$ and compare with $2(\varepsilon_1 + \varepsilon_3/\tau + \varepsilon)$
(`ε_le`). S, about 40 lines. -/
theorem norm_transpose_mulVec_v_le {j : ℕ} (hj : j < k)
    (hV : specNorm ((basisOf L.v (j + 1))ᵀ * basisOf L.v (j + 1) - 1) ≤ L.η₀)
    (hη : L.η₀ ≤ 1 / 100) :
    ‖WithLp.toLp 2 ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2))‖ ≤ L.orthLevel := by
  have hord := (L.orth_eq j hj).orth hV
  have hs : Real.sqrt (1 + L.η₀) ≤ 3 / 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> nlinarith
  have hsq : specNorm (basisOf L.v (j + 1))ᵀ ≤ Real.sqrt (1 + L.η₀) := by
    rw [specNorm_transpose]
    exact specNorm_le_sqrt_of_specNorm_gram_sub_one_le hV
  have hδ := (norm_toLp_mulVec_le (basisOf L.v (j + 1))ᵀ (L.δ (j + 1))).trans
    (mul_le_mul hsq (L.norm_δ_le j hj) (norm_nonneg _) (Real.sqrt_nonneg _))
  have hvec : L.β (j + 1) • ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2)) =
      (basisOf L.v (j + 1))ᵀ *ᵥ L.z' (j + 1) + (basisOf L.v (j + 1))ᵀ *ᵥ L.δ (j + 1) := by
    rw [← Matrix.mulVec_add, ← L.smul_v_eq j hj, Matrix.mulVec_smul]
  have hν := abs_le.mp (L.abs_ν_sub_le j hj)
  have hβ := abs_le.mp (L.abs_β_sub_le j hj)
  have hadm := L.admissible j hj
  have hτ := L.τ_pos
  have he0 := L.ε_nonneg
  have he1 := L.ε_le
  have hε₁ := L.ε₁_nonneg
  have hε₃ := L.ε₃_nonneg
  have hq0 := norm_nonneg (WithLp.toLp 2 (L.z (j + 1)))
  have hp0 := norm_nonneg (WithLp.toLp 2 (L.z' (j + 1)))
  set a := ‖WithLp.toLp 2 ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2))‖ with ha
  set p := ‖WithLp.toLp 2 (L.z' (j + 1))‖ with hp
  set q := ‖WithLp.toLp 2 (L.z (j + 1))‖ with hq
  set s := Real.sqrt (1 + L.η₀) with hsdef
  set ε := L.ε with hεdef
  set τ := L.τ with hτdef
  set β := L.β (j + 1) with hβdef
  set ε₁ := L.ε₁ with hε₁def
  set ε₃ := L.ε₃ with hε₃def
  set T := ε₃ / τ with hT
  have hτν : τ * ((1 - ε) * q) ≤ τ * L.ν (j + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hτ.le
  have hτq : 0 ≤ τ * ((1 - ε) * q) :=
    mul_nonneg hτ.le (mul_nonneg (by linarith) hq0)
  have hβpos : 0 < β := by linarith
  have hnorm : β * a = ‖WithLp.toLp 2 (β • ((basisOf L.v (j + 1))ᵀ *ᵥ L.v (j + 2)))‖ := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hβpos.le]
  have hb : β * a ≤ ε₁ * p + ε₃ * q + s * (ε * p) := by
    rw [hnorm, hvec, WithLp.toLp_add]
    exact (norm_add_le _ _).trans (by linarith)
  have hF2 : τ * ((1 - ε) * q) ≤ (1 + ε) * p := by linarith
  have hq2 : ε₃ * q * (1 - ε) ≤ T * (1 + ε) * p := by
    have h := mul_le_mul_of_nonneg_left hF2 (div_nonneg hε₃ hτ.le)
    calc ε₃ * q * (1 - ε) = T * (τ * ((1 - ε) * q)) := by
          rw [hT]; field_simp
      _ ≤ T * ((1 + ε) * p) := h
      _ = T * (1 + ε) * p := by ring
  have hT0 : 0 ≤ T := div_nonneg hε₃ hτ.le
  have hβlow : (1 - ε) * p ≤ β := by linarith [hβ.1]
  have h1 : a * β * (1 - ε) ≤ ((1 - ε) * (ε₁ + s * ε) + T * (1 + ε)) * p := by
    nlinarith [mul_le_mul_of_nonneg_right hb (by linarith : (0:ℝ) ≤ 1 - ε)]
  have hpoly : (1 - ε) * (ε₁ + s * ε) + T * (1 + ε) ≤ 2 * (ε₁ + T + ε) * (1 - ε) ^ 2 := by
    have c1 : 0 ≤ ε₁ * (1 - ε) * (1 - 2 * ε) :=
      mul_nonneg (mul_nonneg hε₁ (by linarith)) (by linarith)
    have c2 : 0 ≤ T * (1 - 5 * ε + 2 * ε ^ 2) :=
      mul_nonneg hT0 (by nlinarith)
    have c3 : 0 ≤ ε * (1 - ε) * (2 * (1 - ε) - s) :=
      mul_nonneg (mul_nonneg he0 (by linarith)) (by linarith)
    nlinarith [c1, c2, c3]
  have h2 : ((1 - ε) * (ε₁ + s * ε) + T * (1 + ε)) * p ≤ 2 * (ε₁ + T + ε) * (1 - ε) * β := by
    have hK : 0 ≤ 2 * (ε₁ + T + ε) * (1 - ε) := by
      have : 0 ≤ ε₁ + T + ε := by linarith
      have : 0 ≤ 1 - ε := by linarith
      positivity
    linarith [mul_le_mul_of_nonneg_right hpoly hp0, mul_le_mul_of_nonneg_left hβlow hK]
  have hpos : 0 < β * (1 - ε) := mul_pos hβpos (by linarith)
  unfold LanczosReorthRun.orthLevel
  by_contra hcon
  push_neg at hcon
  linarith [mul_lt_mul_of_pos_right hcon hpos]

/-- **Orthogonality of the computed basis on the admissible prefix** (D5, S2): under the
fixed-point condition, for every $m \le k + 1$,
$\|\mathbf{V}_m^{\mathsf{T}}\mathbf{V}_m - \mathbf{I}\|_{\mathsf F} \le \sqrt{3m}\,\mu$.
[Paige1970] for Lanczos with reorthogonalization; [GiraudLangouRozloznikVandenEshof2005,
Theorem 2] for the CGS2 kernel constants.
Proof: strong induction on $m$ with `NLAlib.frobNorm_gram_sub_one_le_of_columns`: the column
hypothesis at $c < m$ is `NLAlib.LanczosReorthRun.norm_transpose_mulVec_v_le` at $j = c - 1$
(for $c \ge 1$; $c = 0$ is the empty basis), whose precondition comes from the induction
hypothesis at $c$ ($\|\cdot\|_2 \le \|\cdot\|_{\mathsf F}$, `specNorm_le_frobNorm`, and
$\sqrt{3c}\,\mu \le \sqrt{3(k+1)}\,\mu \le \eta_0$); the norm hypothesis is
`abs_norm_v_sq_sub_one_le` with $\varepsilon \le \mu$. Note `basisOf` is the
`Matrix.of` of `NLAlib.frobNorm_gram_sub_one_le_of_columns`. M, about 50 lines. -/
theorem frobNorm_gram_sub_one_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) :
    ∀ m ≤ k + 1, frobNorm ((basisOf L.v m)ᵀ * basisOf L.v m - 1) ≤
      Real.sqrt (3 * m) * L.orthLevel := by
  have hμ : 0 ≤ L.orthLevel := by
    unfold LanczosReorthRun.orthLevel
    have := div_nonneg L.ε₃_nonneg L.τ_pos.le
    linarith [L.ε₁_nonneg, L.ε_nonneg]
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro hm
  apply frobNorm_gram_sub_one_le_of_columns L.v m hμ
  · intro c hc
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · simp [hμ, EuclideanSpace.norm_eq]
    · obtain ⟨j, rfl⟩ : ∃ j, c = j + 1 := ⟨c - 1, by omega⟩
      have hj : j < k := by omega
      have hIH := ih (j + 1) hc (by omega)
      have hc' : ((j + 1 : ℕ) : ℝ) ≤ (k : ℝ) + 1 := by
        have : j + 1 ≤ k + 1 := by omega
        exact_mod_cast this
      have h1 : Real.sqrt (3 * ((j + 1 : ℕ) : ℝ)) ≤ Real.sqrt (3 * ((k : ℝ) + 1)) :=
        Real.sqrt_le_sqrt (by linarith)
      have hV : specNorm ((basisOf L.v (j + 1))ᵀ * basisOf L.v (j + 1) - 1) ≤ L.η₀ :=
        (specNorm_le_frobNorm _).trans
          (hIH.trans ((mul_le_mul_of_nonneg_right h1 hμ).trans hsmall))
      exact norm_transpose_mulVec_v_le L hj hV hη
  · intro c hc
    have := L.abs_norm_v_sq_sub_one_le (c + 1) (by omega) (by omega)
    have hdiv := div_nonneg L.ε₃_nonneg L.τ_pos.le
    unfold LanczosReorthRun.orthLevel
    linarith [L.ε₁_nonneg, L.ε_nonneg]

private lemma coeff_params (hrec : L.recLevel ≤ 1 / 100) :
    0 ≤ L.ε₃ / L.τ ∧ L.ε ≤ 1 / 300 ∧ L.ε₂ ≤ 1 / 100 ∧ 0 ≤ L.orthLevel ∧
      L.orthLevel ≤ 1 / 100 ∧ L.ε₁ + L.ε₃ / L.τ ≤ 1 / 200 := by
  have hq : 0 ≤ L.ε₃ / L.τ := div_nonneg L.ε₃_nonneg L.τ_pos.le
  have h1 := L.ε₁_nonneg
  have h2 := L.ε₂_nonneg
  have h0 := L.ε_nonneg
  simp only [recLevel, orthLevel] at hrec ⊢
  refine ⟨hq, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

private lemma coeff_gram (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (m : ℕ) (hm : m ≤ k + 1) :
    specNorm ((basisOf L.v m)ᵀ * basisOf L.v m - 1) ≤ L.η₀ := by
  have hμ := (coeff_params L hrec).2.2.2.1
  refine (specNorm_le_frobNorm _).trans ((L.frobNorm_gram_sub_one_le hη hsmall m hm).trans ?_)
  refine le_trans ?_ hsmall
  gcongr
  exact_mod_cast hm

private lemma coeff_norm_v (hrec : L.recLevel ≤ 1 / 100) (i : ℕ) (hi : i ≤ k + 1) :
    ‖WithLp.toLp 2 (L.v i)‖ ^ 2 ≤ 1 + L.ε ∧ ‖WithLp.toLp 2 (L.v i)‖ ≤ 101 / 100 := by
  have hε := (coeff_params L hrec).2.1
  have hsq : ‖WithLp.toLp 2 (L.v i)‖ ^ 2 ≤ 1 + L.ε := by
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [L.v_zero, WithLp.toLp_zero, norm_zero]
      linarith [L.ε_nonneg]
    · have := L.abs_norm_v_sq_sub_one_le i hi0 hi
      linarith [le_abs_self (‖WithLp.toLp 2 (L.v i)‖ ^ 2 - 1)]
  exact ⟨hsq, by nlinarith [norm_nonneg (WithLp.toLp 2 (L.v i))]⟩

private lemma coeff_abs_dot_le {m : ℕ} (x : Fin n → ℝ) (c : ℕ) (hc : c < m) :
    |L.v (c + 1) ⬝ᵥ x| ≤ ‖WithLp.toLp 2 ((basisOf L.v m)ᵀ *ᵥ x)‖ := by
  have h : ((basisOf L.v m)ᵀ *ᵥ x) ⟨c, hc⟩ = L.v (c + 1) ⬝ᵥ x := by
    simp [basisOf, Matrix.mulVec, dotProduct]
  rw [← h, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ _).trans (EuclideanSpace.norm_le_norm_toLp _)

private lemma coeff_β_pos {j : ℕ} (hj : j < k) : 0 < L.β (j + 1) := by
  have hν := L.abs_ν_sub_le j hj
  have := L.ε_le
  have hν0 : 0 ≤ L.ν (j + 1) := by
    nlinarith [neg_abs_le (L.ν (j + 1) - ‖WithLp.toLp 2 (L.z (j + 1))‖),
      norm_nonneg (WithLp.toLp 2 (L.z (j + 1))),
      mul_nonneg L.ε_nonneg (norm_nonneg (WithLp.toLp 2 (L.z (j + 1))))]
  linarith [L.admissible j hj, mul_nonneg L.τ_pos.le hν0]

/-- One orthogonalization step: $\|\mathbf{z}'\|$ and $\|\mathbf{h}\|$ against $\|\mathbf{z}\|$. -/
private lemma coeff_step (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {i : ℕ} (hi : i < k) :
    ‖WithLp.toLp 2 (L.z' (i + 1))‖ ≤ 103 / 100 * ‖WithLp.toLp 2 (L.z (i + 1))‖ ∧
      ‖WithLp.toLp 2 (fun c : Fin (i + 1) => L.h (i + 1) c)‖ ≤
        105 / 100 * ‖WithLp.toLp 2 (L.z (i + 1))‖ := by
  obtain ⟨hq, hε, hε₂, -, -, hε₁q⟩ := coeff_params L hrec
  have hV := coeff_gram L hη hsmall hrec (i + 1) (by omega)
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
  have hA := hO.norm_coef_le hV (by linarith) L.ε₂_nonneg
  have hVz : ‖WithLp.toLp 2 (Vᵀ *ᵥ z)‖ ≤ 101 / 100 * Z := by
    refine (norm_toLp_mulVec_le _ _).trans ?_
    rw [specNorm_transpose]
    gcongr
    exact (specNorm_le_sqrt_of_specNorm_gram_sub_one_le hV).trans hsq
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
private lemma coeff_local (hrec : L.recLevel ≤ 1 / 100) {j : ℕ} (hj : j < k) {B : ℝ}
    (hB : |L.β j| ≤ B) :
    ‖WithLp.toLp 2 (L.eu (j + 1))‖ ≤ 101 / 100 * L.ε * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.ew (j + 1))‖ ≤ L.ε * (102 / 100 * specNorm L.H + 101 / 100 * B) ∧
      ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 103 / 100 * specNorm L.H + 102 / 100 * B := by
  have hε := (coeff_params L hrec).2.1
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hv := (coeff_norm_v L hrec (j + 1) (by omega)).2
  have hv' := (coeff_norm_v L hrec j (by omega)).2
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
$\|\mathbf{w}\| \le 1.04\|\mathbf{H}\|$. -/
private lemma coeff_of_norm_w_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {j : ℕ} (hj : j < k)
    (hw : ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 104 / 100 * specNorm L.H) :
    |L.α (j + 1)| ≤ 3 / 2 * specNorm L.H ∧ L.β (j + 1) ≤ 3 / 2 * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 3 / 2 * specNorm L.H := by
  have hε := (coeff_params L hrec).2.1
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  obtain ⟨hvsq, hv⟩ := coeff_norm_v L hrec (j + 1) (by omega)
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
  have hz' := (coeff_step L hη hsmall hrec hj).1
  have hβ := L.abs_β_sub_le j hj
  have hβ' : L.β (j + 1) ≤ (1 + L.ε) * ‖WithLp.toLp 2 (L.z' (j + 1))‖ := by
    linarith [le_abs_self (L.β (j + 1) - ‖WithLp.toLp 2 (L.z' (j + 1))‖)]
  refine ⟨by linarith, ?_, by linarith⟩
  nlinarith [mul_le_mul_of_nonneg_left hz' hε0, norm_nonneg (WithLp.toLp 2 (L.z' (j + 1)))]

/-- The inner product $\mathbf{v}_{i+2}^{\mathsf{T}}\mathbf{H}\mathbf{v}_{i+1}$ is close to
$\beta_{i+1}\|\mathbf{v}_{i+2}\|^2$, from the relation at step $i + 1$. -/
private lemma coeff_abs_dot_mulVec_sub_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {i : ℕ} (hik : i < k)
    (hα : |L.α (i + 1)| ≤ 3 / 2 * specNorm L.H) (hz : ‖WithLp.toLp 2 (L.z (i + 1))‖ ≤
      3 / 2 * specNorm L.H) (hβi : |L.β i| ≤ 3 / 2 * specNorm L.H) :
    |L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) - L.β (i + 1) * (L.v (i + 2) ⬝ᵥ L.v (i + 2))| ≤
      92 / 1000 * specNorm L.H := by
  obtain ⟨-, hε, hε₂, hμ0, hμ, -⟩ := coeff_params L hrec
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  obtain ⟨heu, hew, hw⟩ := coeff_local L hrec hik hβi
  have hvn := (coeff_norm_v L hrec (i + 2) (by omega)).2
  have hpn := (coeff_norm_v L hrec (i + 1) (by omega)).2
  have hez : ‖WithLp.toLp 2 (L.ez (i + 1))‖ ≤
      L.ε * (103 / 100 * specNorm L.H + 102 / 100 * (3 / 2 * specNorm L.H) +
        3 / 2 * specNorm L.H * (101 / 100)) :=
    (L.norm_ez_le i hik).trans (by gcongr)
  obtain ⟨hz', hh⟩ := coeff_step L hη hsmall hrec hik
  have hV := coeff_gram L hη hsmall hrec (i + 1) (by omega)
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
    exact mul_le_mul hα ((coeff_abs_dot_le L _ i (by omega)).trans hG) (abs_nonneg _)
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
    · have := coeff_abs_dot_le L (L.v (i + 2)) (i - 1) (show i - 1 < i + 1 by omega)
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
private lemma coeff_norm_w_succ (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) {i : ℕ} (hi : i + 1 < k)
    (hIH : ∀ c ≤ i, |L.α (c + 1)| ≤ 3 / 2 * specNorm L.H ∧ L.β (c + 1) ≤ 3 / 2 * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.z (c + 1))‖ ≤ 3 / 2 * specNorm L.H) :
    ‖WithLp.toLp 2 (L.w (i + 1 + 1))‖ ≤ 104 / 100 * specNorm L.H := by
  obtain ⟨-, hε, -, -, -, -⟩ := coeff_params L hrec
  have hε0 := L.ε_nonneg
  have hs := specNorm_nonneg L.H
  have hik : i < k := by omega
  obtain ⟨hα, hb, hz⟩ := hIH i le_rfl
  have hb0 := (coeff_β_pos L hik).le
  have hβi : |L.β i| ≤ 3 / 2 * specNorm L.H := by
    rcases i with _ | c
    · simp only [L.β_zero, abs_zero]; positivity
    · rw [abs_of_pos (coeff_β_pos L (by omega))]; exact (hIH c (by omega)).2.1
  have hX0 := coeff_abs_dot_mulVec_sub_le L hη hsmall hrec hik hα hz hβi
  obtain ⟨heu, hew, -⟩ := coeff_local L hrec hi (B := 3 / 2 * specNorm L.H)
    (by rw [abs_of_nonneg hb0]; exact hb)
  have hv := coeff_norm_v L hrec (i + 2) (by omega)
  have hp := coeff_norm_v L hrec (i + 1) (by omega)
  have hv' := L.abs_norm_v_sq_sub_one_le (i + 2) (by omega) (by omega)
  have hp' := L.abs_norm_v_sq_sub_one_le (i + 1) (by omega) (by omega)
  rw [EuclideanSpace.norm_toLp_sq_eq_dotProduct_self] at hv hp hv' hp'
  have hsym : L.v (i + 1) ⬝ᵥ (L.H *ᵥ L.v (i + 2)) = L.v (i + 2) ⬝ᵥ (L.H *ᵥ L.v (i + 1)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, L.transpose_H, dotProduct_comm]
  have hHv : ‖WithLp.toLp 2 (L.H *ᵥ L.v (i + 2))‖ ^ 2 ≤ specNorm L.H ^ 2 * (1 + L.ε) := by
    have h1 := pow_le_pow_left₀ (norm_nonneg _) (norm_toLp_mulVec_le L.H (L.v (i + 2))) 2
    rw [mul_pow, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self (L.v (i + 2))] at h1
    exact h1.trans (by gcongr; exact hv.1)
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


/-- **Coefficient bounds without growth in $j$** (D3): $|\alpha_{j+1}|$, $\beta_{j+1}$ and
$\|\mathbf{z}_{j+1}\|$ are at most $\tfrac32\|\mathbf{H}\|_2$. [Paige1976] for the plain case
(there with growth); here orthogonality is available first.
Proof: order D5 → D3. From `frobNorm_gram_sub_one_le` the basis is nearly orthonormal. Expand
$\|\mathbf{z}\|^2$ with $\mathbf{z} = \mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j -
\alpha_{j+1}\mathbf{v}_{j+1} + \mathbf{e}$ ($\mathbf{e}$ the three local errors): the cross terms
are $\le \mu$ times products of coefficients and $\|\mathbf{H}\|$, and $\mathbf{v}_j^{\mathsf{T}}
\mathbf{H}\mathbf{v}_{j+1} = \beta_j\|\mathbf{v}_{j+1}\|^2 + O((\mu + \varepsilon)\|\mathbf{H}\|)$
by symmetry and `recurrenceError_eq` at step $j - 1$ (the relation at step $j$). That relation
brings in $\mathbf{V}_j\mathbf{h}_j$: bound $\|\mathbf{h}_j\| \le 1.1\|\mathbf{z}_j\|$ crudely from
`NLAlib.IsOrthErr.norm_coef_le` with $\|\mathbf{V}_j^{\mathsf{T}}\mathbf{z}_j\| \le
\|\mathbf{V}_j\|_2\|\mathbf{z}_j\|$ (the sharp bound is D4, proved later), so
$|\mathbf{h}_j^{\mathsf{T}}\mathbf{V}_j^{\mathsf{T}}\mathbf{v}_{j+1}| \le 1.1\mu\|\mathbf{z}_j\|$.
Altogether $\|\mathbf{z}\|^2 \le (1 + \varepsilon)\|\mathbf{H}\|^2 + 30\,\mathrm{rec}\,
\|\mathbf{H}\|^2 \le 1.4\|\mathbf{H}\|^2$ under `hrec` (the $\beta_j^2$ and $\alpha^2$ terms enter
with negative signs), so $\|\mathbf{z}\| \le 1.3\|\mathbf{H}\|$; $|\alpha|$
from `α_eq`, `abs_eα_le`; $\beta \le (1+\varepsilon)\|\mathbf{z}'\|$ and $\|\mathbf{z}'\|^2 =
\mathbf{z}'^{\mathsf{T}}(\mathbf{z} - \mathbf{V}\mathbf{h} - \mathbf{r})$ with
`NLAlib.IsOrthErr.norm_coef_le` and $\|\mathbf{z}\| \le 1.03\|\mathbf{z}'\|/\tau$ (admissibility)
give $\|\mathbf{z}'\| \le (1 + \mathrm{rec})\|\mathbf{z}\|$.
Induction on $j$ closes with `hrec`. M, about 120 lines. -/
theorem coeff_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∀ j < k, |L.α (j + 1)| ≤ 3 / 2 * specNorm L.H ∧ L.β (j + 1) ≤ 3 / 2 * specNorm L.H ∧
      ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 3 / 2 * specNorm L.H := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j IH =>
    intro hj
    refine coeff_of_norm_w_le L hη hsmall hrec hj ?_
    rcases j with _ | i
    · have := (coeff_local L hrec hj (B := 0) (by simp [L.β_zero])).2.2
      linarith [specNorm_nonneg L.H]
    · exact coeff_norm_w_succ L hη hsmall hrec hj fun c hc => IH c (by omega) (by omega)

/-- **The discarded reorthogonalization coefficients are small** (D4): for symmetric
$\mathbf{H}$, $\|\mathbf{h}_{j+1}\| \le 24\sqrt{j+1}\,(\mu + \varepsilon + \varepsilon_2)
\|\mathbf{H}\|_2$. The one place symmetry is needed: without it the coefficients are $O(1)$
(Arnoldi). [Paige1970] in substance; [Simon1984b] for semi-orthogonal variants.
Proof: induction on $j$. By `NLAlib.IsOrthErr.norm_coef_le`, bound $\|\mathbf{V}_{j+1}^{\mathsf{T}}
\mathbf{z}_{j+1}\|$ with $\mathbf{z} = \mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j -
\alpha_{j+1}\mathbf{v}_{j+1} + \mathbf{e}$ ($\mathbf{e} = \mathbf{e}^u + \mathbf{e}^w +
\mathbf{e}^z$, $\|\mathbf{e}\| \le 8\varepsilon\|\mathbf{H}\|$ by `coeff_le`): keep
$\mathbf{V}^{\mathsf{T}}\mathbf{e}$ as one vector, $\|\mathbf{V}^{\mathsf{T}}\mathbf{e}\| \le
\|\mathbf{V}\|_2\|\mathbf{e}\|$ (not componentwise). For the rest go componentwise: for
$i \le j - 1$ (0-based columns before the previous one)
$\mathbf{v}_i^{\mathsf{T}}\mathbf{H}\mathbf{v}_{j+1} = (\mathbf{H}\mathbf{v}_i)^{\mathsf{T}}
\mathbf{v}_{j+1}$ (`transpose_H`, `Matrix.dotProduct_mulVec`); expand $\mathbf{H}\mathbf{v}_i$ by
`NLAlib.LanczosReorthRun.recurrenceError_eq` at $i$: off-diagonal Gram entries ($\le\mu$ by
`norm_transpose_mulVec_v_le`, times coefficients $\le \tfrac32\|\mathbf{H}\|$ from `coeff_le`;
as vectors these are five shifted copies of $\mathbf{g} = \mathbf{V}_j^{\mathsf{T}}\mathbf{v}_{j+1}$
and $\mathbf{V}_{j-1}^{\mathsf{T}}\mathbf{v}_j$, total $\le 7.5\mu\|\mathbf{H}\|$),
the term $\mathbf{h}_i^{\mathsf{T}}\mathbf{V}_i^{\mathsf{T}}\mathbf{v}_{j+1}$ ($\le\|\mathbf{h}_i\|
\mu$; by the induction hypothesis the sum of squares is $\le 24^2\mathrm{rec}^2\|\mathbf{H}\|^2
\mu^2 j(j+1)/2$ and $(j+1)\mu \le \sqrt{j+1}\,\eta_0/\sqrt3$ from `hsmall`, so this is
$\le 0.1\sqrt{j+1}\,\mathrm{rec}\,\|\mathbf{H}\|$, second order) and the local errors of step $i$
($\le 9.2(\varepsilon + \varepsilon_2)\|\mathbf{H}\|$ each, $\le 9.2\sqrt j\,\mathrm{rec}\,
\|\mathbf{H}\|$ in all: the only $\sqrt j$ term); the
previous column carries the same terms plus the cancellation
$\beta_j(\|\mathbf{v}_{j+1}\|^2 - \|\mathbf{v}_j\|^2) = O(\varepsilon\|\mathbf{H}\|)$; the current
column is $\alpha(1 - \|\mathbf{v}\|^2) - e_\alpha - \mathbf{v}^{\mathsf{T}}(\mathbf{e}^u +
\mathbf{e}^w) = O(\varepsilon\|\mathbf{H}\|)$. With $\varepsilon \le \mu/2$ and $\mu + \varepsilon
\le \mathrm{rec}$ this gives $\|\mathbf{V}^{\mathsf{T}}\mathbf{z}\| \le (14 + 9.2\sqrt j)\,
\mathrm{rec}\,\|\mathbf{H}\|$; $\|\mathbf{V}^{\mathsf{T}}\mathbf{z}'\| \le
\varepsilon_1\|\mathbf{z}'\|
+ \varepsilon_3\|\mathbf{z}\| \le (\varepsilon_1 + \varepsilon_3)\tfrac32\|\mathbf{H}\|
\le 0.8\mu\|\mathbf{H}\|$ with $\varepsilon_3 \le \varepsilon_3/\tau$; so $\|\mathbf{h}\| \le
(16 + 9.3\sqrt j)\,\mathrm{rec}\,\|\mathbf{H}\| \le 24\sqrt{j+1}\,\mathrm{rec}\,\|\mathbf{H}\|$.
L, about 200 lines; intermediate lemmas: the componentwise
bound for one earlier column, and the sum over columns. -/
theorem norm_coef_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    ∀ j < k, ‖WithLp.toLp 2 (fun i : Fin (j + 1) => L.h (j + 1) i)‖ ≤
      24 * Real.sqrt ((j : ℝ) + 1) * L.recLevel * specNorm L.H := by
  sorry

/-- **The perturbed Lanczos relation of a reorthogonalized run** (D6, S1): with the discarded
coefficients in the residual, $\|\mathbf{F}_k\|_{\mathsf F} \le 30(k+1)\,(\mu + \varepsilon +
\varepsilon_2)\,\|\mathbf{H}\|_2$; the relation itself is `NLAlib.LanczosData.mul_basis`.
[Paige1970] for the reorthogonalized relation; [Paige1976] for the rounding part.
Proof: column $j$ by `NLAlib.LanczosReorthRun.recurrenceError_eq`: $\|\mathbf{V}_{j+1}\mathbf{h}\|
\le \sqrt{1+\eta_0}\cdot 24\sqrt{j+1}\,\mathrm{rec}\,\|\mathbf{H}\|$ (`norm_coef_le`,
`NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le`), the orthogonalization residual $\le
\varepsilon_2\|\mathbf{z}\| \le 1.5\varepsilon_2\|\mathbf{H}\|$, and $\boldsymbol\delta$,
$\mathbf{e}^u$, $\mathbf{e}^w$, $\mathbf{e}^z$ together $\le 9.2\varepsilon\|\mathbf{H}\|$
(`coeff_le`, and $\|\mathbf{v}\| \le 1 + \varepsilon$ from `abs_norm_v_sq_sub_one_le`), so
$\|\mathbf{f}_j\| \le (24.2\sqrt{j+1} + 9.2)\,\mathrm{rec}\,\|\mathbf{H}\| \le 33.4\sqrt{j+1}\,
\mathrm{rec}\,\|\mathbf{H}\|$;
then $\|\mathbf{F}\|_{\mathsf F}^2 = \sum_j\|\mathbf{f}_j\|^2 \le 33.4^2\,
\mathrm{rec}^2\|\mathbf{H}\|^2 \sum_{j<k}(j+1)$ and $\sum_{j<k}(j+1) = k(k+1)/2 \le (k+1)^2/2$, so
$\|\mathbf{F}\|_{\mathsf F} \le 23.7(k+1)\,\mathrm{rec}\,\|\mathbf{H}\|$. M, about 60 lines. -/
theorem frobNorm_residual_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    frobNorm L.toLanczosData.residual ≤ 30 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := by
  sorry

/-- **The projection form** (D7, S1′): $\|\mathbf{V}_k^{\mathsf{T}}\mathbf{H}\mathbf{V}_k -
\mathbf{T}_k\|_2 \le 50(k+1)(\mu + \varepsilon + \varepsilon_2)\|\mathbf{H}\|_2$.
[Simon1984b] (semi-orthogonality suffices).
Proof: multiply `NLAlib.LanczosData.mul_basis` by $\mathbf{V}_k^{\mathsf{T}}$:
$\mathbf{V}_k^{\mathsf{T}}\mathbf{H}\mathbf{V}_k - \mathbf{T}_k = (\mathbf{G} - \mathbf{I})
\mathbf{T}_k + \mathbf{V}_k^{\mathsf{T}}(\beta_k\mathbf{v}_{k+1})\mathbf{e}^{\mathsf{T}} +
\mathbf{V}_k^{\mathsf{T}}\mathbf{F}_k$; bound with `frobNorm_gram_sub_one_le` ($\|\mathbf{G} -
\mathbf{I}\|_2 \le \sqrt{3k}\,\mu \le \sqrt3(k+1)\,\mathrm{rec}$), `coeff_le`
($\|\mathbf{T}_k\|_2 \le \tfrac92\|\mathbf{H}\|$, so the first term is $\le 7.8(k+1)\,\mathrm{rec}\,
\|\mathbf{H}\|$), `norm_transpose_mulVec_v_le` (second term $\le \tfrac32\mu\|\mathbf{H}\|$),
`frobNorm_residual_le` with `NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le` (third term
$\le 30.2(k+1)\,\mathrm{rec}\,\|\mathbf{H}\|$); total $\le 40(k+1)\,\mathrm{rec}\,\|\mathbf{H}\|$.
S, about 30 lines. -/
theorem specNorm_transpose_mul_mul_sub_tridiagonal_le (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀)
    (hrec : L.recLevel ≤ 1 / 100) (hτ : L.τ ≤ 1) :
    specNorm (L.toLanczosData.basisᵀ * L.H * L.toLanczosData.basis -
      L.toLanczosData.tridiagonal) ≤ 50 * ((k : ℝ) + 1) * L.recLevel * specNorm L.H := by
  sorry

/-- **Full reorthogonalization stops by step $n$** (D8): the admissible prefix has
$k + 1 \le n$ (strict admissibility makes $\mathbf{v}_{k+1}$ a genuine column). No printed
source.
Proof: `frobNorm_gram_sub_one_le` at $m = k + 1$ gives $\|\cdot\|_2 \le \eta_0 < 1$
(`specNorm_le_frobNorm`); apply `NLAlib.le_of_specNorm_gram_sub_one_lt_one`. S, about 8 lines. -/
theorem succ_le_card (hη : L.η₀ ≤ 1 / 100)
    (hsmall : Real.sqrt (3 * ((k : ℝ) + 1)) * L.orthLevel ≤ L.η₀) : k + 1 ≤ n := by
  have hfrob := frobNorm_gram_sub_one_le L hη hsmall (k + 1) le_rfl
  have hbound : Real.sqrt (3 * (((k + 1 : ℕ)) : ℝ)) * L.orthLevel ≤ L.η₀ := by
    push_cast
    exact hsmall
  have hspec : specNorm ((basisOf L.v (k + 1))ᵀ * basisOf L.v (k + 1) - 1) < 1 :=
    lt_of_le_of_lt (specNorm_le_frobNorm _ |>.trans (hfrob.trans hbound)) (by linarith)
  exact le_of_specNorm_gram_sub_one_lt_one hspec

/-- **Prefixes of a run are runs** (replaces E6, whose terminal case $\beta_k = 0$ cannot occur
under strict admissibility): for $0 < m \le k$ there is a run of $m$ steps with the same data and
parameters. Proof: build the structure field by field from `L`, restricting each `∀ j < k` field
to `j < m` (`lt_of_lt_of_le`); the norm field `abs_norm_v_sq_sub_one_le` restricts to
$j \le m + 1$. S, about 40 lines. -/
theorem exists_ofLE {m : ℕ} (hm : 0 < m) (hmk : m ≤ k) :
    ∃ L' : LanczosReorthRun n m, L'.H = L.H ∧ L'.v = L.v ∧ L'.α = L.α ∧ L'.β = L.β ∧
      L'.ν = L.ν ∧ L'.h = L.h ∧ L'.ε = L.ε ∧ L'.τ = L.τ ∧ L'.η₀ = L.η₀ ∧ L'.ε₁ = L.ε₁ ∧
      L'.ε₂ = L.ε₂ ∧ L'.ε₃ = L.ε₃ := by
  refine ⟨{
    H := L.H, v := L.v, u := L.u, w := L.w, z := L.z, z' := L.z', α := L.α, β := L.β,
    ν := L.ν, h := L.h, eu := L.eu, ew := L.ew, ez := L.ez, eα := L.eα, δ := L.δ, ε := L.ε,
    τ := L.τ, η₀ := L.η₀, ε₁ := L.ε₁, ε₂ := L.ε₂, ε₃ := L.ε₃,
    transpose_H := L.transpose_H, ε_nonneg := L.ε_nonneg, ε_le := L.ε_le,
    ε₁_nonneg := L.ε₁_nonneg, ε₂_nonneg := L.ε₂_nonneg, ε₃_nonneg := L.ε₃_nonneg,
    k_pos := hm, v_zero := L.v_zero, β_zero := L.β_zero,
    u_eq := fun j hj => L.u_eq j (by omega),
    norm_eu_le := fun j hj => L.norm_eu_le j (by omega),
    w_eq := fun j hj => L.w_eq j (by omega),
    norm_ew_le := fun j hj => L.norm_ew_le j (by omega),
    α_eq := fun j hj => L.α_eq j (by omega),
    abs_eα_le := fun j hj => L.abs_eα_le j (by omega),
    z_eq := fun j hj => L.z_eq j (by omega),
    norm_ez_le := fun j hj => L.norm_ez_le j (by omega),
    abs_ν_sub_le := fun j hj => L.abs_ν_sub_le j (by omega),
    orth_eq := fun j hj => L.orth_eq j (by omega),
    abs_β_sub_le := fun j hj => L.abs_β_sub_le j (by omega),
    smul_v_eq := fun j hj => L.smul_v_eq j (by omega),
    norm_δ_le := fun j hj => L.norm_δ_le j (by omega),
    abs_norm_v_sq_sub_one_le := fun j h1 h2 => L.abs_norm_v_sq_sub_one_le j h1 (by omega),
    admissible := fun j hj => L.admissible j (by omega),
    τ_pos := L.τ_pos
  },
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end LanczosReorthRun

end NLAlib
