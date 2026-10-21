/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-!
# Open Bernstein ellipses

The focal-distance description makes openness and inclusion of the whole real segment explicit.
A Joukowski annulus membership bridge supports contour estimates without boundary regularity.

## Main results

* `NLAlib.openBernsteinEllipse`: the open focal-distance ellipse.
* `NLAlib.isOpen_openBernsteinEllipse`: openness, including the two foci.
* `NLAlib.ofReal_mem_openBernsteinEllipse`: the closed segment lies inside when $\rho>1$.
* `NLAlib.joukowski_mem_openBernsteinEllipse`: the reciprocal annulus maps into the ellipse.
-/

@[expose] public section

namespace NLAlib

/-- The open Bernstein ellipse has foci $\pm1$ and focal-distance sum less than
$\rho+\rho^{-1}$. [Trefethen2019, Chapter 8]. The approximation regime is $\rho>1$.
The definition is total: for $\rho\le0$ or $\rho=1$ it is empty; for $0<\rho<1$ it is the
same ellipse as for the reciprocal parameter. No boundary extension is included. -/
noncomputable def openBernsteinEllipse (ρ : ℝ) : Set ℂ :=
  {z : ℂ | ‖z - 1‖ + ‖z + 1‖ < ρ + ρ⁻¹}

/-- The focal-distance ellipse is open for every parameter. -/
theorem isOpen_openBernsteinEllipse (ρ : ℝ) : IsOpen (openBernsteinEllipse ρ) :=
  isOpen_lt (by fun_prop) continuous_const

private lemma two_lt_radius_add_inv {ρ : ℝ} (hρ : 1 < ρ) : 2 < ρ + ρ⁻¹ := by
  have hp : 0 < ρ := zero_lt_one.trans hρ
  have hi : ρ * ρ⁻¹ = 1 := mul_inv_cancel₀ hp.ne'
  have hs : 0 < (ρ - 1) ^ 2 := sq_pos_of_pos (sub_pos.mpr hρ)
  nlinarith

/-- For $\rho>1$, the entire closed real segment $[-1,1]$ lies strictly inside the ellipse,
including both foci. [Trefethen2019, Chapter 8]. -/
theorem ofReal_mem_openBernsteinEllipse {ρ x : ℝ} (hρ : 1 < ρ)
    (hx : x ∈ Set.Icc (-1 : ℝ) 1) : (x : ℂ) ∈ openBernsteinEllipse ρ := by
  change ‖(x : ℂ) - 1‖ + ‖(x : ℂ) + 1‖ < ρ + ρ⁻¹
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, ← Complex.ofReal_add,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonpos (by linarith [hx.2] : x - 1 ≤ 0), abs_of_nonneg (by linarith [hx.1] : 0 ≤ x + 1)]
  linarith [two_lt_radius_add_inv hρ]

private lemma joukowski_focal_sum {w : ℂ} (hw : w ≠ 0) :
    ‖(w + w⁻¹) / 2 - 1‖ + ‖(w + w⁻¹) / 2 + 1‖ = ‖w‖ + ‖w‖⁻¹ := by
  have hm : (w + w⁻¹) / 2 - 1 = (w - 1) ^ 2 / (2 * w) := by
    field_simp
    ring
  have hp : (w + w⁻¹) / 2 + 1 = (w + 1) ^ 2 / (2 * w) := by
    field_simp
    ring
  have hs : ‖w - 1‖ ^ 2 + ‖w + 1‖ ^ 2 = 2 * (‖w‖ ^ 2 + 1) := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.one_re,
      Complex.sub_im,
      Complex.one_im, sub_zero, Complex.add_re, Complex.add_im, add_zero]
    ring
  rw [hm, hp, norm_div, norm_div, norm_pow, norm_pow, norm_mul,
    show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num,
    ← add_div, hs]
  field_simp

private lemma radius_add_inv_lt {ρ t : ℝ} (hρ : 1 < ρ)
    (ht : ρ⁻¹ < t) (htρ : t < ρ) : t + t⁻¹ < ρ + ρ⁻¹ := by
  have hp : 0 < ρ := zero_lt_one.trans hρ
  have htp : 0 < t := (inv_pos.mpr hp).trans ht
  have hprod : 1 < ρ * t := by
    have h := (mul_lt_mul_of_pos_left ht hp)
    rw [mul_inv_cancel₀ hp.ne'] at h
    exact h
  have hpos : 0 < (ρ - t) * (ρ * t - 1) := mul_pos (sub_pos.mpr htρ) (sub_pos.mpr hprod)
  have he : t + t⁻¹ = (t ^ 2 + 1) / t := by field_simp
  have heρ : ρ + ρ⁻¹ = (ρ ^ 2 + 1) / ρ := by field_simp
  rw [he, heρ, div_lt_div_iff₀ htp hp]
  nlinarith

/-- For $\rho>1$, the Joukowski image of every point with
$\rho^{-1}<\lVert w\rVert<\rho$ lies strictly inside the Bernstein ellipse.
[Trefethen2019, proof of Theorem 8.1]. No boundary continuity or noncritical-point assumption
is needed; this includes unit-circle points mapping to the foci. -/
theorem joukowski_mem_openBernsteinEllipse {ρ : ℝ} {w : ℂ} (hρ : 1 < ρ)
    (hw : ρ⁻¹ < ‖w‖ ∧ ‖w‖ < ρ) :
    (w + w⁻¹) / 2 ∈ openBernsteinEllipse ρ := by
  have hp : 0 < ‖w‖ := (inv_pos.mpr (zero_lt_one.trans hρ)).trans hw.1
  change ‖(w + w⁻¹) / 2 - 1‖ + ‖(w + w⁻¹) / 2 + 1‖ < ρ + ρ⁻¹
  rw [joukowski_focal_sum (norm_pos_iff.mp hp)]
  exact radius_add_inv_lt hρ hw.1 hw.2

end NLAlib
