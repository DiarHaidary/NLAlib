/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystromWindow
public import NLAlib.LowRank.Gaussian.RangeFinderMoments

/-!
# Relative error of truncated generalized Nyström with Gaussian sketches

Independent Gaussian sketches of widths $200k/\varepsilon$ and fourteen times the range width
suffice for relative expected squared Frobenius error $1+\varepsilon$.
The conditional window estimate is integrated against coupled range-finder moments.
Design: docs/design/research/Nystrom-Constants.md.

## Main results

* [Relative-error theorem](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_of_hasLaw_gaussianMatrix_of_truncatedGeneralizedNystromRangeDim_le).
-/

@[expose] public section

namespace NLAlib

private theorem late_noise_bundle {L T F S : ℝ} (hL : 200 ≤ L) (hT : 0 ≤ T)
    (hF : F ≤ 1.006 * T) (hS : S ≤ 10 / L * T) :
    7.3 * F + (1.574 * L + 2.3) * S ≤ 23.2 * T := by
  have hL0 : 0 < L := by linarith
  have h1 := mul_le_mul_of_nonneg_left hF (by norm_num : (0 : ℝ) ≤ 7.3)
  have h2 := mul_le_mul_of_nonneg_left hS (by linarith : 0 ≤ 1.574 * L + 2.3)
  have hc : 7.3 * 1.006 + (1.574 * L + 2.3) * (10 / L) ≤ 23.2 := by
    have hd : 23 / L ≤ 0.115 := (div_le_iff₀ hL0).2 (by linarith)
    have he : 7.3 * 1.006 + (1.574 * L + 2.3) * (10 / L) =
        23.0838 + 23 / L := by field_simp; ring
    rw [he]
    linarith
  have h3 := mul_le_mul_of_nonneg_right hc hT
  nlinarith only [h1, h2, h3]
private theorem late_window_coefficient {P L : ℝ} (hL : 0 < L) (hP : 14 * L ≤ P) :
    92 / √P * √(10 / L) ≤ 79 / L := by
  have hP0 : 0 < P := by linarith
  have hroot : (92 * √(10 / L) * L) ^ 2 ≤ (79 * √P) ^ 2 := by
    simp only [mul_pow, Real.sq_sqrt (by positivity : 0 ≤ 10 / L),
      Real.sq_sqrt hP0.le]
    have he : 10 / L * L ^ 2 = 10 * L := by field_simp
    nlinarith
  have hcross := (sq_le_sq₀ (by positivity : 0 ≤ 92 * √(10 / L) * L)
    (by positivity : 0 ≤ 79 * √P)).mp hroot
  rw [div_mul_eq_mul_div, div_le_div_iff₀ (Real.sqrt_pos.2 hP0) hL]
  nlinarith only [hcross]

private theorem late_moments_le {P L k T U F S : ℝ} (hL : 200 ≤ L)
    (hP : 14 * L ≤ P) (hk : 0 ≤ k) (hT : 0 ≤ T)
    (hU : U ≤ (1 + 2 * k / L) * T)
    (hF : F ≤ 1.006 * T) (hS : S ≤ 10 / L * T) :
    U + 69 * k / P * (7.3 * F + (1.574 * L + 2.3) * S) +
      92 * k / √P * (S / (2 * √(10 / L)) + √(10 / L) * T / 2) ≤
        (1 + 196 * k / L) * T := by
  have hL0 : 0 < L := by linarith
  have hP0 : 0 < P := by linarith
  have hu : 0 < √(10 / L) := Real.sqrt_pos.2 (by positivity)
  have hsdiv : S / (2 * √(10 / L)) ≤ √(10 / L) * T / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * √(10 / L))).2
    have hsqrt := Real.sq_sqrt (by positivity : 0 ≤ 10 / L)
    nlinarith only [hS, congrArg (fun x : ℝ => x * T) hsqrt]
  have hpart : S / (2 * √(10 / L)) + √(10 / L) * T / 2 ≤ √(10 / L) * T := by
    linarith
  have hN := late_noise_bundle hL hT hF hS
  have hcN : 69 / P * 23.2 ≤ 115 / L := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hP0 hL0]
    nlinarith
  have hcW := late_window_coefficient hL0 hP
  have h1 := mul_le_mul_of_nonneg_left hN
    (by positivity : 0 ≤ 69 * k / P)
  have h2 := mul_le_mul_of_nonneg_left hpart
    (by positivity : 0 ≤ 92 * k / √P)
  have h3 := mul_le_mul_of_nonneg_right hcN (mul_nonneg hk hT)
  have h4 := mul_le_mul_of_nonneg_right hcW (mul_nonneg hk hT)
  simp only [div_eq_mul_inv] at hU h1 h2 h3 h4 ⊢
  nlinarith only [hU, h1, h2, h3, h4]

private theorem gaussianProjectionFactor_le_decimal {k L : ℕ} (hk : 1 ≤ k)
    (hL : 200 * k ≤ L) : gaussianProjectionFactor k L ≤ 1.006 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL' : 200 * (k : ℝ) ≤ L := by exact_mod_cast hL
  have hd : (0 : ℝ) < (L : ℝ) - k - 1 := by linarith
  have hratio : (k : ℝ) / ((L : ℝ) - k - 1) ≤ 0.006 := by
    rw [div_le_iff₀ hd]
    linarith
  rw [gaussianProjectionFactor_def]
  linarith
private theorem gaussianProjectionFactor_le_one_add_div {k L : ℕ} (hk : 1 ≤ k)
    (hL : 200 * k ≤ L) : gaussianProjectionFactor k L ≤ 1 + 2 * (k : ℝ) / L := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hL' : 200 * (k : ℝ) ≤ L := by exact_mod_cast hL
  have hd : (0 : ℝ) < (L : ℝ) - k - 1 := by linarith
  have hL0 : (0 : ℝ) < L := by linarith
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_div_iff₀ hd hL0]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := ℝ) k)
    (show 0 ≤ (L : ℝ) - 2 * k - 2 by linarith)]

private theorem late_dim_le {k L : ℕ} {ε : ℝ} (hε1 : ε ≤ 1)
    (h : 200 * (k : ℝ) ≤ ε * L) : 200 * k ≤ L := by
  have hL := mul_le_mul_of_nonneg_right hε1 (Nat.cast_nonneg (α := ℝ) L)
  have hh : 200 * (k : ℝ) ≤ L := by linarith
  exact_mod_cast hh

private theorem late_factor_le {k L : ℕ} {ε : ℝ} (hk : 1 ≤ k) (hε1 : ε ≤ 1)
    (h : 200 * (k : ℝ) ≤ ε * L) : 1 + 196 * (k : ℝ) / L ≤ 1 + ε := by
  have hdim := late_dim_le hε1 h
  have hL : 0 < L := by omega
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  rw [add_le_add_iff_left, div_le_iff₀ hL']
  nlinarith [Nat.cast_nonneg (α := ℝ) k]

open MeasureTheory ProbabilityTheory
private theorem late_cross_majorant {e γ u T : ℝ} (he : 0 ≤ e) (hu : 0 < u)
    (hγ : γ ≤ T) :
    e * γ ≤ e ^ 2 / (2 * u) + u * T ^ 2 / 2 := by
  have h1 := mul_le_mul_of_nonneg_left hγ he
  have h2 := sq_nonneg (e - u * T)
  have heq : e ^ 2 / (2 * u) + u * T ^ 2 / 2 =
      (e ^ 2 + u ^ 2 * T ^ 2) / (2 * u) := by field_simp
  rw [heq, le_div_iff₀ (by positivity : 0 < 2 * u)]
  nlinarith [mul_le_mul_of_nonneg_right h1 hu.le]
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m n l p : Type*} [Fintype m] [Fintype n] [Fintype l] [Fintype p]
    {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}
private theorem late_integral_of_conditional
    (A : Matrix m n ℝ) (k : ℕ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hL : 200 ≤ Fintype.card l) (hP : 14 * Fintype.card l ≤ Fintype.card p)
    (hcond : ∀ x : Matrix n l ℝ,
      ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2
        ∂gaussianMatrix m p ≤
      frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
        69 * k / (Fintype.card p : ℝ) *
          (7.3 * frobNorm (A - rsvd A x) ^ 2 +
            (1.574 * Fintype.card l + 2.3) * specNorm (A - rsvd A x) ^ 2) +
        92 * k / √(Fintype.card p : ℝ) * specNorm (A - rsvd A x) *
          frobNorm (rsvd A x - truncatedSVD (rsvd A x) k)) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ) +
      69 * k / (Fintype.card p : ℝ) *
        (7.3 * (∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ) +
          (1.574 * Fintype.card l + 2.3) *
            (∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ)) +
      92 * k / √(Fintype.card p : ℝ) *
        ((∫ ω, specNorm (A - rsvd A (X ω)) ^ 2 ∂μ) /
          (2 * √(10 / (Fintype.card l : ℝ))) +
            √(10 / (Fintype.card l : ℝ)) *
              frobNorm (A - truncatedSVD A k) ^ 2 / 2) := by
  have := hX.isProbabilityMeasure
  let u : ℝ := √(10 / (Fintype.card l : ℝ))
  let c₁ : ℝ := 69 * k / (Fintype.card p : ℝ) * 7.3
  let c₂ : ℝ := 69 * k / (Fintype.card p : ℝ) * (1.574 * Fintype.card l + 2.3) +
    92 * k / √(Fintype.card p : ℝ) / (2 * u)
  let c₃ : ℝ := 92 * k / √(Fintype.card p : ℝ) * u / 2
  let H : Matrix n l ℝ → ℝ := fun x =>
    frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
      c₁ * frobNorm (A - rsvd A x) ^ 2 + c₂ * specNorm (A - rsvd A x) ^ 2 +
        c₃ * frobNorm (A - truncatedSVD A k) ^ 2
  have hu : 0 < u := Real.sqrt_pos.2 (div_pos (by norm_num)
    (by exact_mod_cast (show 0 < Fintype.card l by omega)))
  have hle (x : Matrix n l ℝ) :
      ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2
        ∂gaussianMatrix m p ≤ H x := by
    have hc := late_cross_majorant (specNorm_nonneg (A - rsvd A x)) hu
      (frobNorm_rsvd_sub_truncatedSVD_le A x k)
    have hm := mul_le_mul_of_nonneg_left hc
      (by positivity : 0 ≤ 92 * k / √(Fintype.card p : ℝ))
    have hh := hcond x
    dsimp only [H, c₁, c₂, c₃]
    simp only [div_eq_mul_inv] at hm hh ⊢
    nlinarith only [hm, hh]
  have hU := integrable_frobNorm_sub_truncatedSVD_rsvd_sq A hX.aemeasurable k
  have hF := (integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul c₁
  have hS := (integrable_specNorm_sub_rsvd_sq A hX.aemeasurable).const_mul c₂
  have hT : Integrable (fun _ : Ω => c₃ * frobNorm (A - truncatedSVD A k) ^ 2) μ :=
    integrable_const _
  have hUF : Integrable (fun ω =>
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        c₁ * frobNorm (A - rsvd A (X ω)) ^ 2) μ := hU.add hF
  have hUFS : Integrable (fun ω =>
      frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 +
        c₁ * frobNorm (A - rsvd A (X ω)) ^ 2 +
          c₂ * specNorm (A - rsvd A (X ω)) ^ 2) μ := hUF.add hS
  have hH := hUFS.add hT
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (gaussianMatrix m p) (gaussianMatrix m p) :=
    HasLaw.id
  have hint (x : Matrix n l ℝ) := 
    integrable_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_of_hasLaw_gaussianMatrix
      (X := fun _ => x) A aemeasurable_const hid (indepFun_const_left x _)
      (by omega : Fintype.card l + 2 ≤ Fintype.card p) k
  have hm : Measurable fun q : Matrix n l ℝ × Matrix m p ℝ =>
      frobNorm (A - truncatedSVD (generalizedNystrom A q.1 q.2) k) ^ 2 :=
    (continuous_frobNorm.measurable.comp (measurable_const.sub
      ((measurable_truncatedSVD k).comp (measurable_generalizedNystrom A)))).pow_const 2
  refine (hXΨ.integral_comp_le_of_integral_le hX.aemeasurable hΨ hm
    (fun _ => sq_nonneg _) (ae_of_all _ fun ω => hint (X ω))
    (ae_of_all _ fun ω => hle (X ω)) hH).trans_eq ?_
  simp only [H]
  rw [integral_add hUFS hT, integral_add hUF hS,
    integral_add hU hF, integral_const_mul, integral_const_mul,
    integral_const, probReal_univ, one_smul]
  dsimp only [c₁, c₂, c₃, u]
  ring
-- The residual theorem identifier alone exceeds 100 characters.
set_option linter.style.longLine false in
private theorem late_integral_le_of_conditional
    (A : Matrix m n ℝ) (k : ℕ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ)
    (hL : 200 ≤ Fintype.card l) (hP : 14 * Fintype.card l ≤ Fintype.card p)
    (hk : 1 ≤ k) (hkl : 200 * k ≤ Fintype.card l)
    (hcond : ∀ x : Matrix n l ℝ,
      ∫ ψ, frobNorm (A - truncatedSVD (generalizedNystrom A x ψ) k) ^ 2
        ∂gaussianMatrix m p ≤
      frobNorm (A - truncatedSVD (rsvd A x) k) ^ 2 +
        69 * k / (Fintype.card p : ℝ) *
          (7.3 * frobNorm (A - rsvd A x) ^ 2 +
            (1.574 * Fintype.card l + 2.3) * specNorm (A - rsvd A x) ^ 2) +
        92 * k / √(Fintype.card p : ℝ) * specNorm (A - rsvd A x) *
          frobNorm (rsvd A x - truncatedSVD (rsvd A x) k)) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (1 + 196 * (k : ℝ) / Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hk2 : k + 2 ≤ Fintype.card l := by omega
  have hu := integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk2
  have hf := integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hX hk2
  have hs :=
    integral_specNorm_sub_rsvd_sq_le_div_of_hasLaw_gaussianMatrix_of_gaussianRangeFinderResidualDim_le
      A hX hk (by rwa [gaussianRangeFinderResidualDim_def])
  rw [gaussianRangeFinderResidualConstant_def] at hs
  refine (late_integral_of_conditional A k hX hΨ hXΨ hL hP hcond).trans ?_
  apply late_moments_le
    (show (200 : ℝ) ≤ Fintype.card l by exact_mod_cast hL)
    (show 14 * (Fintype.card l : ℝ) ≤ Fintype.card p by exact_mod_cast hP)
    (Nat.cast_nonneg k) (sq_nonneg _)
  · exact hu.trans (mul_le_mul_of_nonneg_right
      (gaussianProjectionFactor_le_one_add_div hk hkl) (sq_nonneg _))
  · exact hf.trans (mul_le_mul_of_nonneg_right
      (gaussianProjectionFactor_le_decimal hk hkl) (sq_nonneg _))
  · exact hs


/-- The sufficient Gaussian range width for relative expected squared error is at
present <!-- value truncatedGeneralizedNystromRangeDim k \varepsilon -->
$200k/\varepsilon$.
The relative-error theorem assumes $0<\varepsilon\le1$; at $\varepsilon=0$ this total
expression equals $0$ by the inverse-of-zero convention. No printed source. -/
noncomputable irreducible_def truncatedGeneralizedNystromRangeDim (k : ℕ) (ε : ℝ) : ℝ :=
  200 * (k : ℝ) / ε

/-- The sufficient Gaussian co-range width, as a function of the range width, is at
present <!-- value truncatedGeneralizedNystromCorangeDim \ell --> $14\ell$.
No printed source. -/
irreducible_def truncatedGeneralizedNystromCorangeDim (l : ℕ) : ℕ := 14 * l

/-- The range-width bound is at
present <!-- value truncatedGeneralizedNystromRangeDim k \varepsilon -->
$200k/\varepsilon$. No printed source. -/
theorem truncatedGeneralizedNystromRangeDim_le (k : ℕ) (ε : ℝ) :
    truncatedGeneralizedNystromRangeDim k ε ≤ 200 * (k : ℝ) / ε := by
  rw [truncatedGeneralizedNystromRangeDim_def]

/-- The co-range-width bound is at
present <!-- value truncatedGeneralizedNystromCorangeDim \ell --> $14\ell$.
No printed source. -/
theorem truncatedGeneralizedNystromCorangeDim_le (l : ℕ) :
    truncatedGeneralizedNystromCorangeDim l ≤ 14 * l := by
  rw [truncatedGeneralizedNystromCorangeDim_def]

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Truncated generalized Nyström has relative expected squared Frobenius error**
for independent standard Gaussian range and co-range sketches of widths
$\ell\ge200k/\varepsilon$ and $p\ge14\ell$, with $0<\varepsilon\le1$:
$\mathbb E\|\mathbf A-\llbracket\mathsf{gn}(\mathbf A,\mathbf\Omega,\mathbf\Psi)
\rrbracket_k\|_{\mathsf F}^2
\le(1+\varepsilon)\|\mathbf A-\llbracket\mathbf A\rrbracket_k\|_{\mathsf F}^2\,.$
Every matrix rank and shape is allowed. No printed source.
Result: tgn-expected-error -/
theorem
    integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_of_hasLaw_gaussianMatrix_of_truncatedGeneralizedNystromRangeDim_le
    (A : Matrix m n ℝ) (k : ℕ) {ε : ℝ}
    (hX : HasLaw X (gaussianMatrix n l) μ) (hΨ : HasLaw Ψ (gaussianMatrix m p) μ)
    (hXΨ : IndepFun X Ψ μ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hl : truncatedGeneralizedNystromRangeDim k ε ≤ Fintype.card l)
    (hp : truncatedGeneralizedNystromCorangeDim (Fintype.card l) ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have := hX.isProbabilityMeasure
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [truncatedSVD_zero, sub_zero, integral_const, probReal_univ, one_smul]
    nlinarith [sq_nonneg (frobNorm A)]
  rw [truncatedGeneralizedNystromRangeDim_def] at hl
  rw [truncatedGeneralizedNystromCorangeDim_def] at hp
  have hwidth : 200 * (k : ℝ) ≤ ε * Fintype.card l := by
    have h := (div_le_iff₀ hε).1 hl
    nlinarith
  have hdim := late_dim_le hε1 hwidth
  have hL : 200 ≤ Fintype.card l := by omega
  have hb := late_integral_le_of_conditional A k hX hΨ hXΨ hL hp hk hdim
    (fun x => integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_fourteen_mul_le
      A x hk hL hp)
  exact hb.trans (mul_le_mul_of_nonneg_right (late_factor_le hk hε1 hwidth) (sq_nonneg _))

end NLAlib
