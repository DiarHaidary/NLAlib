/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.LanczosRun

/-!
# Constructing the existing Lanczos run from actual local defects

The record constructors in this file consume the vector values and bounds supplied by actual
rounded kernel execution. They introduce no numerical iteration interface. Whole-program
execution derives their premises from primitive scalar contracts separately.

## Main results

* `NLAlib.LanczosImplementation.exists_lanczosRun_one`: first executed step as an existing run.
-/

@[expose] public section

namespace NLAlib.LanczosImplementation

open scoped Matrix

private theorem one_nearly_unit {N : ℕ} (ε : ℝ) (v1 vn : Fin N → ℝ)
    (hv1 : |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ ε) :
    ∀ j, 1 ≤ j → j ≤ 1 →
      |‖WithLp.toLp 2
        ((Function.update (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) 2 vn) j)‖ ^ 2 - 1| ≤ ε := by
  intro j h1 h2
  have : j = 1 := by omega
  subst j
  simpa using hv1

private noncomputable def oneRoundedRun {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : Aᵀ = A) (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 100)
    (v1 uv wv zv vn : Fin N → ℝ) (an bn : ℝ)
    (hv1 : |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ ε)
    (hu : ‖WithLp.toLp 2 (A *ᵥ v1 - uv)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 v1‖)
    (hw : ‖WithLp.toLp 2 (uv - wv)‖ ≤ ε * ‖WithLp.toLp 2 uv‖)
    (ha : |v1 ⬝ᵥ wv - an| ≤ ε * ‖WithLp.toLp 2 v1‖ * ‖WithLp.toLp 2 wv‖)
    (hz : ‖WithLp.toLp 2 (wv - an • v1 - zv)‖ ≤
      ε * (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 v1‖))
    (hd : ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤ ε * ‖WithLp.toLp 2 zv‖)
    (hbn : 0 ≤ bn) (hvn : bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ ε) :
    LanczosRun N 1 where
  H := A
  v := Function.update (Function.update 0 1 v1) 2 vn
  u := Function.update 0 1 uv
  w := Function.update 0 1 wv
  z := Function.update 0 1 zv
  α := Function.update 0 1 an
  β := Function.update 0 1 bn
  eu := Function.update 0 1 (-(A *ᵥ v1 - uv))
  ew := Function.update 0 1 (-(uv - wv))
  eα := Function.update 0 1 (-(v1 ⬝ᵥ wv - an))
  ez := Function.update 0 1 (-(wv - an • v1 - zv))
  δ := Function.update 0 1 (-(zv - bn • vn))
  ε := ε
  transpose_H := hA
  ε_nonneg := hε
  k_pos := by norm_num
  ε_le := hsmall
  v_zero := by simp
  β_zero := by simp
  u_eq := by
    intro j hj
    have : j = 0 := by omega
    subst j; simp
  norm_eu_le := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa only [Nat.zero_add, Function.update_self,
      Function.update_of_ne (by omega : 1 ≠ 2), WithLp.toLp_neg, norm_neg] using hu
  w_eq := by
    intro j hj
    have : j = 0 := by omega
    subst j; simp
  norm_ew_le := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa only [Nat.zero_add, Function.update_self,
      Function.update_of_ne (by omega : 0 ≠ 1),
      WithLp.toLp_neg, norm_neg, Pi.zero_apply, abs_zero, zero_mul, add_zero] using hw
  α_eq := by
    intro j hj
    have : j = 0 := by omega
    subst j; simp
  abs_eα_le := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa only [Nat.zero_add, Function.update_self, abs_neg,
      Function.update_of_ne (by omega : 1 ≠ 2)] using ha
  z_eq := by
    intro j hj
    have : j = 0 := by omega
    subst j; simp
  norm_ez_le := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa only [Nat.zero_add, Function.update_self,
      Function.update_of_ne (by omega : 1 ≠ 2), WithLp.toLp_neg, norm_neg] using hz
  smul_v_eq := by
    intro j hj
    have : j = 0 := by omega
    subst j; simp
  norm_δ_le := by
    intro j hj
    have : j = 0 := by omega
    subst j
    simpa only [Nat.zero_add, Function.update_self, WithLp.toLp_neg, norm_neg] using hd
  abs_norm_v_sq_sub_one_le := one_nearly_unit ε v1 vn hv1
  abs_norm_v_succ_sq_sub_one_le := by simpa using hvn
  β_nonneg := by
    intro j hj
    have : j = 0 ∨ j = 1 := by omega
    rcases this with rfl | rfl
    · simp
    · simpa using hbn
  β_pos := by intro j h1 h2; omega

/-- The actual values and five bounded local defects of a first rounded Paige step give the
existing positive-length LanczosRun. The next coefficient may be zero; its next vector is
required nearly unit only when that coefficient is nonzero. This is a record constructor,
with no independent whole-program execution assertion. -/
theorem exists_lanczosRun_one {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ)
    (hA : Aᵀ = A) (ε : ℝ) (hε : 0 ≤ ε) (hsmall : ε ≤ 1 / 100)
    (v1 uv wv zv vn : Fin N → ℝ) (an bn : ℝ)
    (hv1 : |‖WithLp.toLp 2 v1‖ ^ 2 - 1| ≤ ε)
    (hu : ‖WithLp.toLp 2 (A *ᵥ v1 - uv)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 v1‖)
    (hw : ‖WithLp.toLp 2 (uv - wv)‖ ≤ ε * ‖WithLp.toLp 2 uv‖)
    (ha : |v1 ⬝ᵥ wv - an| ≤ ε * ‖WithLp.toLp 2 v1‖ * ‖WithLp.toLp 2 wv‖)
    (hz : ‖WithLp.toLp 2 (wv - an • v1 - zv)‖ ≤
      ε * (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 v1‖))
    (hd : ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤ ε * ‖WithLp.toLp 2 zv‖)
    (hbn : 0 ≤ bn) (hvn : bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ ε) :
    ∃ R : LanczosRun N 1, R.H = A ∧ R.ε = ε ∧
      R.v = Function.update (Function.update (0 : ℕ → Fin N → ℝ) 1 v1) 2 vn ∧
      R.α = Function.update (0 : ℕ → ℝ) 1 an ∧ R.β = Function.update (0 : ℕ → ℝ) 1 bn := by
  exact ⟨oneRoundedRun A hA ε hε hsmall v1 uv wv zv vn an bn hv1 hu hw ha hz hd hbn hvn,
    rfl, rfl, rfl, rfl, rfl⟩


private theorem append_equations {N k : ℕ} (R : LanczosRun N k)
    (uv wv zv vn : Fin N → ℝ) (an bn : ℝ) :
    (∀ j < k + 1, (Function.update R.u (k + 1) uv) (j + 1) = R.H *ᵥ (Function.update R.v (k + 2)
      vn) (j + 1) + (Function.update R.eu (k + 1) (-(R.H *ᵥ R.v (k + 1) - uv))) (j + 1)) ∧
    (∀ j < k + 1, (Function.update R.w (k + 1) wv) (j + 1) = (Function.update R.u (k + 1) uv) (j
      + 1) - (Function.update R.β (k + 1) bn) (j) • (Function.update R.v (k + 2) vn) (j) +
      (Function.update R.ew (k + 1) (-(uv - R.β k • R.v k - wv))) (j + 1)) ∧
    (∀ j < k + 1, (Function.update R.α (k + 1) an) (j + 1) = (Function.update R.v (k + 2) vn) (j
      + 1) ⬝ᵥ (Function.update R.w (k + 1) wv) (j + 1) + (Function.update R.eα (k + 1) (-(R.v (k
      + 1) ⬝ᵥ wv - an))) (j + 1)) ∧
    (∀ j < k + 1, (Function.update R.z (k + 1) zv) (j + 1) = (Function.update R.w (k + 1) wv) (j
      + 1) - (Function.update R.α (k + 1) an) (j + 1) • (Function.update R.v (k + 2) vn) (j + 1)
      + (Function.update R.ez (k + 1) (-(wv - an • R.v (k + 1) - zv))) (j + 1)) ∧
    (∀ j < k + 1, (Function.update R.β (k + 1) bn) (j + 1) • (Function.update R.v (k + 2) vn) (j
      + 2) = (Function.update R.z (k + 1) zv) (j + 1) + (Function.update R.δ (k + 1) (-(zv - bn •
      vn))) (j + 1)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.u_eq j hj), (by
      simp only [Function.update_self, Function.update_of_ne (show k + 1 ≠ k + 2 by omega), neg_sub]
      abel)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.w_eq j hj), (by
      simp only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        Function.update_of_ne (show k ≠ k + 2 by omega), neg_sub]
      abel)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.α_eq j hj), (by
      simp only [Function.update_self, Function.update_of_ne (show k + 1 ≠ k + 2 by omega), neg_sub]
      abel)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.z_eq j hj), (by
      simp only [Function.update_self, Function.update_of_ne (show k + 1 ≠ k + 2 by omega), neg_sub]
      abel)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.smul_v_eq j hj), (by
      simp only [Function.update_self, neg_sub]
      abel)⟩

private theorem append_bounds {N k : ℕ} (R : LanczosRun N k)
    (uv wv zv vn : Fin N → ℝ) (an bn : ℝ)
    (hu : ‖WithLp.toLp 2 (R.H *ᵥ R.v (k + 1) - uv)‖ ≤
      R.ε * specNorm R.H * ‖WithLp.toLp 2 (R.v (k + 1))‖)
    (hw : ‖WithLp.toLp 2 (uv - R.β k • R.v k - wv)‖ ≤
      R.ε * (‖WithLp.toLp 2 uv‖ + |R.β k| * ‖WithLp.toLp 2 (R.v k)‖))
    (ha : |R.v (k + 1) ⬝ᵥ wv - an| ≤
      R.ε * ‖WithLp.toLp 2 (R.v (k + 1))‖ * ‖WithLp.toLp 2 wv‖)
    (hz : ‖WithLp.toLp 2 (wv - an • R.v (k + 1) - zv)‖ ≤
      R.ε * (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 (R.v (k + 1))‖))
    (hd : ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤ R.ε * ‖WithLp.toLp 2 zv‖) :
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.eu (k + 1) (-(R.H *ᵥ R.v (k + 1) - uv))) (j
      + 1))‖ ≤ R.ε * specNorm R.H * ‖WithLp.toLp 2 ((Function.update R.v (k + 2) vn) (j + 1))‖) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.ew (k + 1) (-(uv - R.β k • R.v k - wv))) (j
      + 1))‖ ≤ R.ε * (‖WithLp.toLp 2 ((Function.update R.u (k + 1) uv) (j + 1))‖ +
      |(Function.update R.β (k + 1) bn) (j)| * ‖WithLp.toLp 2 ((Function.update R.v (k + 2) vn)
      (j))‖)) ∧
    (∀ j < k + 1, |(Function.update R.eα (k + 1) (-(R.v (k + 1) ⬝ᵥ wv - an))) (j + 1)| ≤ R.ε *
      ‖WithLp.toLp 2 ((Function.update R.v (k + 2) vn) (j + 1))‖ * ‖WithLp.toLp 2
      ((Function.update R.w (k + 1) wv) (j + 1))‖) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.ez (k + 1) (-(wv - an • R.v (k + 1) - zv)))
      (j + 1))‖ ≤ R.ε * (‖WithLp.toLp 2 ((Function.update R.w (k + 1) wv) (j + 1))‖ +
      |(Function.update R.α (k + 1) an) (j + 1)| * ‖WithLp.toLp 2 ((Function.update R.v (k + 2)
      vn) (j + 1))‖)) ∧
    (∀ j < k + 1, ‖WithLp.toLp 2 ((Function.update R.δ (k + 1) (-(zv - bn • vn))) (j + 1))‖ ≤ R.ε
      * ‖WithLp.toLp 2 ((Function.update R.z (k + 1) zv) (j + 1))‖) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.norm_eu_le j hj), (by
      simpa only [Function.update_self, Function.update_of_ne (show k + 1 ≠ k + 2 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hu)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.norm_ew_le j hj), (by
      simpa only [Function.update_self, Function.update_of_ne (show k ≠ k + 1 by omega),
        Function.update_of_ne (show k ≠ k + 2 by omega), WithLp.toLp_neg, norm_neg, abs_neg]
        using hw)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.abs_eα_le j hj), (by
      simpa only [Function.update_self, Function.update_of_ne (show k + 1 ≠ k + 2 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using ha)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.norm_ez_le j hj), (by
      simpa only [Function.update_self, Function.update_of_ne (show k + 1 ≠ k + 2 by omega),
        WithLp.toLp_neg, norm_neg, abs_neg]
        using hz)⟩
  · exact Nat.forall_lt_succ_right.mpr ⟨(fun j hj => by
        simpa only [Function.update_of_ne (show j + 1 ≠ k + 1 by omega),
          Function.update_of_ne (show j + 1 ≠ k + 2 by omega),
          Function.update_of_ne (show j + 2 ≠ k + 2 by omega),
          Function.update_of_ne (show j ≠ k + 1 by omega),
          Function.update_of_ne (show j ≠ k + 2 by omega)] using R.norm_δ_le j hj), (by
      simpa only [Function.update_self, WithLp.toLp_neg, norm_neg, abs_neg]
        using hd)⟩

private noncomputable def appendRoundedRun {N k : ℕ} (R : LanczosRun N k)
    (uv wv zv vn : Fin N → ℝ) (an bn : ℝ) (hk : R.β k ≠ 0)
    (hu : ‖WithLp.toLp 2 (R.H *ᵥ R.v (k + 1) - uv)‖ ≤
      R.ε * specNorm R.H * ‖WithLp.toLp 2 (R.v (k + 1))‖)
    (hw : ‖WithLp.toLp 2 (uv - R.β k • R.v k - wv)‖ ≤
      R.ε * (‖WithLp.toLp 2 uv‖ + |R.β k| * ‖WithLp.toLp 2 (R.v k)‖))
    (ha : |R.v (k + 1) ⬝ᵥ wv - an| ≤
      R.ε * ‖WithLp.toLp 2 (R.v (k + 1))‖ * ‖WithLp.toLp 2 wv‖)
    (hz : ‖WithLp.toLp 2 (wv - an • R.v (k + 1) - zv)‖ ≤
      R.ε * (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 (R.v (k + 1))‖))
    (hd : ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤ R.ε * ‖WithLp.toLp 2 zv‖)
    (hbn : 0 ≤ bn) (hvn : bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ R.ε) :
    LanczosRun N (k + 1) := by
  have he := append_equations R uv wv zv vn an bn
  have hb := append_bounds R uv wv zv vn an bn hu hw ha hz hd
  exact {
    H := R.H
    v := Function.update R.v (k + 2) vn
    u := Function.update R.u (k + 1) uv
    w := Function.update R.w (k + 1) wv
    z := Function.update R.z (k + 1) zv
    α := Function.update R.α (k + 1) an
    β := Function.update R.β (k + 1) bn
    eu := Function.update R.eu (k + 1) (-(R.H *ᵥ R.v (k + 1) - uv))
    ew := Function.update R.ew (k + 1) (-(uv - R.β k • R.v k - wv))
    eα := Function.update R.eα (k + 1) (-(R.v (k + 1) ⬝ᵥ wv - an))
    ez := Function.update R.ez (k + 1) (-(wv - an • R.v (k + 1) - zv))
    δ := Function.update R.δ (k + 1) (-(zv - bn • vn))
    ε := R.ε
    transpose_H := R.transpose_H
    ε_nonneg := R.ε_nonneg
    k_pos := by omega
    ε_le := R.ε_le
    v_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 2 by omega)] using R.v_zero
    β_zero := by simpa only [Function.update_of_ne (show 0 ≠ k + 1 by omega)] using R.β_zero
    u_eq := he.1
    w_eq := he.2.1
    α_eq := he.2.2.1
    z_eq := he.2.2.2.1
    smul_v_eq := he.2.2.2.2
    norm_eu_le := hb.1
    norm_ew_le := hb.2.1
    abs_eα_le := hb.2.2.1
    norm_ez_le := hb.2.2.2.1
    norm_δ_le := hb.2.2.2.2
    abs_norm_v_sq_sub_one_le := by
      intro j hj hle
      rw [Function.update_of_ne (show j ≠ k + 2 by omega)]
      rcases Nat.eq_or_lt_of_le hle with rfl | hlt
      · exact R.abs_norm_v_succ_sq_sub_one_le hk
      · exact R.abs_norm_v_sq_sub_one_le j hj (by omega)
    abs_norm_v_succ_sq_sub_one_le := by
      simpa only [show k + 1 + 1 = k + 2 by omega, Function.update_self] using hvn
    β_nonneg := by
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with rfl | hlt
      · simpa using hbn
      · simpa only [Function.update_of_ne (show j ≠ k + 1 by omega)] using
          R.β_nonneg j (by omega)
    β_pos := by
      intro j hj hlt
      rw [Function.update_of_ne (show j ≠ k + 1 by omega)]
      rcases Nat.eq_or_lt_of_le (show j ≤ k by omega) with rfl | hlt
      · exact lt_of_le_of_ne (R.β_nonneg _ le_rfl) (Ne.symm hk)
      · exact R.β_pos j hj hlt }

/-- Append the actual values and local defects of a nonterminal next step. This constructor
retains the existing run's prefix, including its error functions, and allows the new last
coefficient to be zero. Its hypotheses are derived from kernel execution by the program bridge. -/
theorem exists_lanczosRun_succ {N k : ℕ} (R : LanczosRun N k)
    (uv wv zv vn : Fin N → ℝ) (an bn : ℝ) (hk : R.β k ≠ 0)
    (hu : ‖WithLp.toLp 2 (R.H *ᵥ R.v (k + 1) - uv)‖ ≤
      R.ε * specNorm R.H * ‖WithLp.toLp 2 (R.v (k + 1))‖)
    (hw : ‖WithLp.toLp 2 (uv - R.β k • R.v k - wv)‖ ≤
      R.ε * (‖WithLp.toLp 2 uv‖ + |R.β k| * ‖WithLp.toLp 2 (R.v k)‖))
    (ha : |R.v (k + 1) ⬝ᵥ wv - an| ≤
      R.ε * ‖WithLp.toLp 2 (R.v (k + 1))‖ * ‖WithLp.toLp 2 wv‖)
    (hz : ‖WithLp.toLp 2 (wv - an • R.v (k + 1) - zv)‖ ≤
      R.ε * (‖WithLp.toLp 2 wv‖ + |an| * ‖WithLp.toLp 2 (R.v (k + 1))‖))
    (hd : ‖WithLp.toLp 2 (zv - bn • vn)‖ ≤ R.ε * ‖WithLp.toLp 2 zv‖)
    (hbn : 0 ≤ bn) (hvn : bn ≠ 0 → |‖WithLp.toLp 2 vn‖ ^ 2 - 1| ≤ R.ε) :
    ∃ S : LanczosRun N (k + 1), S.H = R.H ∧ S.ε = R.ε ∧
      S.v = Function.update R.v (k + 2) vn ∧
      S.α = Function.update R.α (k + 1) an ∧ S.β = Function.update R.β (k + 1) bn := by
  exact ⟨appendRoundedRun R uv wv zv vn an bn hk hu hw ha hz hd hbn hvn,
    rfl, rfl, rfl, rfl, rfl⟩

end NLAlib.LanczosImplementation
