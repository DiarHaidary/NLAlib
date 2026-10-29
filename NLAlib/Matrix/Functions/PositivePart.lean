/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Functions.GoldenThompson
public import NLAlib.Matrix.Spectral.HermitianPart

/-!
# Frobenius projection onto a spectral floor

Clipping the eigenvalues of the Hermitian part at a real floor gives the unique nearest matrix
above that floor in the Frobenius norm. The input may be non-Hermitian and the floor negative.
The projection is expressed with Mathlib's functional calculus; at floor zero it is the
positive part of the Hermitian part. These statements generalize [Higham1988, Theorem 2.1].

## Main results

* `Matrix.IsHermitian.smul_one_le_cfc_max`: feasibility of spectral clipping.
* `NLAlib.frobNorm_sub_cfc_max_hermitianPart_le`: nearest-matrix inequality.
* `NLAlib.frobNorm_sub_eq_frobNorm_sub_cfc_max_hermitianPart_iff`: uniqueness.
* `NLAlib.frobNorm_cfc_max_hermitianPart_sub_le`: nonexpansiveness.
* `NLAlib.frobNorm_sub_cfc_max_hermitianPart_sq`: exact squared distance.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Clipping a Hermitian matrix at a real floor $a$ gives a matrix above $a\mathbf{I}$.
This is the feasibility part of the nearest-matrix theorem. -/
theorem _root_.Matrix.IsHermitian.smul_one_le_cfc_max {H : Matrix n n 𝕜}
    (hH : H.IsHermitian) (a : ℝ) : a • (1 : Matrix n n 𝕜) ≤ cfc (max a) H := by
  have h := algebraMap_le_cfc (max a) a H (fun x _ => le_max_left a x)
    (H.finite_real_spectrum.continuousOn _) hH
  simpa only [Algebra.algebraMap_eq_smul_one] using h

/-- The clipping correction is positive semidefinite and complementary to the part above
the floor. This calculation is local to the projection proof. -/
private theorem cfc_max_sub_properties {H : Matrix n n 𝕜} (hH : H.IsHermitian) (a : ℝ) :
    (cfc (max a) H - H).PosSemidef ∧
      (cfc (max a) H - H) * (cfc (max a) H - a • 1) = 0 := by
  have hc (f : ℝ → ℝ) := H.finite_real_spectrum.continuousOn f
  have hid : cfc (fun x : ℝ => x) H = H := cfc_id' ℝ H hH
  have hconst : cfc (fun _ : ℝ => a) H = a • (1 : Matrix n n 𝕜) := by
    simpa only [Algebra.algebraMap_eq_smul_one] using (cfc_const (p := IsSelfAdjoint) a H hH)
  have hR : cfc (max a) H - H = cfc (fun x : ℝ => max a x - x) H := by
    rw [cfc_sub _ _ H (hc _) (hc _), hid]
  have hT : cfc (max a) H - a • 1 = cfc (fun x : ℝ => max a x - a) H := by
    rw [cfc_sub _ _ H (hc _) (hc _), hconst]
  constructor
  · rw [hR]
    exact Matrix.nonneg_iff_posSemidef.mp (cfc_nonneg fun x _ => sub_nonneg.mpr (le_max_right a x))
  · rw [hR, hT, ← cfc_mul _ _ H (hc _) (hc _)]
    have hzero : (fun x : ℝ => (max a x - x) * (max a x - a)) = fun _ => 0 := by
      funext x
      rcases le_total a x with h | h
      · rw [max_eq_right h, sub_self, zero_mul]
      · rw [max_eq_left h, sub_self, mul_zero]
    rw [hzero]
    exact cfc_const_zero ℝ H

/-- For any matrix $\mathbf{A}$ and real floor $a$, write
$\mathbf{P}=\max(a,\cdot)(\operatorname{hermitianPart}(\mathbf{A}))$.
Every $\mathbf{X}\succeq a\mathbf{I}$ satisfies the projection inequality
$\langle\mathbf{A}-\mathbf{P},\mathbf{X}-\mathbf{P}\rangle_{\mathsf{F}}\le0$.
Port of `NLAlib.frobInner_sub_nearestPSD_le_zero`. -/
theorem frobInner_sub_cfc_max_hermitianPart_le_zero
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobInner (A - cfc (max a) (hermitianPart A))
      (X - cfc (max a) (hermitianPart A)) ≤ 0 := by
  let H := hermitianPart A
  let P := cfc (max a) H
  have hH := isHermitian_hermitianPart A
  have hP : P.IsHermitian := cfc_predicate (max a) H
  have hR := (cfc_max_sub_properties hH a).1
  have hcomp := (cfc_max_sub_properties hH a).2
  have hfloor : (X - a • (1 : Matrix n n 𝕜)).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hX)
  have hXH : X.IsHermitian := by
    have h := hfloor.isHermitian.add (Matrix.isHermitian_one.smul (IsSelfAdjoint.all a))
    simpa only [sub_add_cancel] using h
  have htrace : 0 ≤ frobInner (P - H) (X - a • 1) := by
    rw [frobInner_eq_re_trace, hR.isHermitian.eq]
    exact hR.re_trace_mul_nonneg hfloor
  have hzero : frobInner (P - H) (P - a • 1) = 0 := by
    rw [frobInner_eq_re_trace, hR.isHermitian.eq, hcomp, Matrix.trace_zero, map_zero]
  have hskew : frobInner (A - H) (X - P) = 0 :=
    (hXH.sub hP).frobInner_sub_hermitianPart A
  change frobInner (A - P) (X - P) ≤ 0
  rw [show A - P = (A - H) - (P - H) by abel, frobInner_sub_left, hskew]
  have he : X - P = (X - a • 1) - (P - a • 1) := by abel
  rw [he, frobInner_sub_right, hzero]
  linarith

/-- **Nearest matrix above a spectral floor.** For any matrix $\mathbf{A}$ and real $a$,
let $\mathbf{H}=(\mathbf{A}+\mathbf{A}^{\mathsf{H}})/2$ and $\mathbf{P}=\max(a,\cdot)(\mathbf{H})$.
For every $\mathbf{X}\succeq a\mathbf{I}$,
$\|\mathbf{A}-\mathbf{P}\|_{\mathsf{F}}\le\|\mathbf{A}-\mathbf{X}\|_{\mathsf{F}}$.
[Higham1988, Theorem 2.1]; generalized from real matrices and floor zero.
Port of `NLAlib.nearestPSD_unique_minimizer`, with uniqueness stated separately.
Result: nearest-psd-frobenius -/
theorem frobNorm_sub_cfc_max_hermitianPart_le
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobNorm (A - cfc (max a) (hermitianPart A)) ≤ frobNorm (A - X) := by
  let P := cfc (max a) (hermitianPart A)
  have hv := frobInner_sub_cfc_max_hermitianPart_le_zero A a hX
  have he : A - X = (A - P) - (X - P) := by abel
  have hd := frobNorm_sub_sq (A - P) (X - P)
  rw [← he] at hd
  have hn := frobNorm_nonneg (A - P)
  have hm := frobNorm_nonneg (A - X)
  change frobNorm (A - P) ≤ _
  nlinarith [sq_nonneg (frobNorm (X - P))]

/-- Equality in the nearest-matrix inequality holds exactly at the clipped Hermitian part:
for any matrix $\mathbf{A}$, real floor $a$, and $\mathbf{X}\succeq a\mathbf{I}$, equality
of the two Frobenius distances implies $\mathbf{X}=\max(a,\cdot)(\mathbf{H})$, where
$\mathbf{H}=(\mathbf{A}+\mathbf{A}^{\mathsf{H}})/2$.
[Higham1988, Theorem 2.1]; generalized to either scalar field and any real floor.
Port of `NLAlib.nearestPSD_unique_minimizer`, the uniqueness clause. -/
theorem frobNorm_sub_eq_frobNorm_sub_cfc_max_hermitianPart_iff
    (A : Matrix n n 𝕜) (a : ℝ) {X : Matrix n n 𝕜}
    (hX : a • (1 : Matrix n n 𝕜) ≤ X) :
    frobNorm (A - X) = frobNorm (A - cfc (max a) (hermitianPart A)) ↔
      X = cfc (max a) (hermitianPart A) := by
  let P := cfc (max a) (hermitianPart A)
  refine ⟨fun heq => ?_, fun h => h ▸ rfl⟩
  have hv := frobInner_sub_cfc_max_hermitianPart_le_zero A a hX
  have he : A - X = (A - P) - (X - P) := by abel
  have hd := frobNorm_sub_sq (A - P) (X - P)
  rw [← he, heq] at hd
  have hz : frobNorm (X - P) = 0 := by nlinarith [sq_nonneg (frobNorm (X - P))]
  exact sub_eq_zero.mp (frobNorm_eq_zero_iff.mp hz)

/-- Projection above a fixed real spectral floor is nonexpansive in the Frobenius norm.
For arbitrary matrices $\mathbf{A},\mathbf{B}$, their projections $\mathbf{P},\mathbf{Q}$
obtained by clipping their Hermitian parts at that floor satisfy
$\|\mathbf{P}-\mathbf{Q}\|_{\mathsf{F}}\le\|\mathbf{A}-\mathbf{B}\|_{\mathsf{F}}$.
Port of `NLAlib.frobNorm_nearestPSD_sub_le`. -/
theorem frobNorm_cfc_max_hermitianPart_sub_le
    (A B : Matrix n n 𝕜) (a : ℝ) :
    frobNorm (cfc (max a) (hermitianPart A) -
      cfc (max a) (hermitianPart B)) ≤ frobNorm (A - B) := by
  let P := cfc (max a) (hermitianPart A)
  let Q := cfc (max a) (hermitianPart B)
  have hv1 := frobInner_sub_cfc_max_hermitianPart_le_zero A a
    ((isHermitian_hermitianPart B).smul_one_le_cfc_max a)
  have hv2 := frobInner_sub_cfc_max_hermitianPart_le_zero B a
    ((isHermitian_hermitianPart A).smul_one_le_cfc_max a)
  change frobInner (A - P) (Q - P) ≤ 0 at hv1
  change frobInner (B - Q) (P - Q) ≤ 0 at hv2
  rw [show Q - P = -(P - Q) by abel, frobInner_neg_right] at hv1
  have he : frobInner (A - B) (P - Q) - frobNorm (P - Q) ^ 2 =
      frobInner (A - P) (P - Q) - frobInner (B - Q) (P - Q) := by
    rw [← frobInner_self]
    simp only [frobInner_sub_left]
    ring
  have hCS := frobInner_le (A - B) (P - Q)
  have hn := frobNorm_nonneg (P - Q)
  have hm := frobNorm_nonneg (A - B)
  change frobNorm (P - Q) ≤ _
  nlinarith

/-- The squared distance to the projection above a real floor $a$ equals the squared
skew-Hermitian norm plus the squared eigenvalue deficits of the Hermitian part $\mathbf{H}$:
$$\|\mathbf{A}-\max(a,\cdot)(\mathbf{H})\|_{\mathsf{F}}^2
=\|\mathbf{A}-\mathbf{H}\|_{\mathsf{F}}^2+
\sum_{i=0}^{n-1}\max(a-\lambda_i(\mathbf{H}),0)^2\,.$$
[Higham1988, Theorem 2.1]; generalized to either scalar field and any real floor.
Port of `NLAlib.frobSq_sub_nearestPSD_eq`. -/
theorem frobNorm_sub_cfc_max_hermitianPart_sq
    (A : Matrix n n 𝕜) (a : ℝ) :
    frobNorm (A - cfc (max a) (hermitianPart A)) ^ 2 =
      frobNorm (A - hermitianPart A) ^ 2 +
        ∑ i ∈ Finset.range (Fintype.card n),
          max (a - eigenvalue (hermitianPart A) i) 0 ^ 2 := by
  let H := hermitianPart A
  let P := cfc (max a) H
  have hH := isHermitian_hermitianPart A
  have hP : P.IsHermitian := cfc_predicate (max a) H
  have hc (f : ℝ → ℝ) := H.finite_real_spectrum.continuousOn f
  have he : A - P = (A - H) - (P - H) := by abel
  have horth := (hP.sub hH).frobInner_sub_hermitianPart A
  rw [he, frobNorm_sub_sq_of_frobInner_eq_zero horth]
  congr 1
  have hR : P - H = cfc (fun x : ℝ => max a x - x) H := by
    have hid : cfc (fun x : ℝ => x) H = H := cfc_id' ℝ H hH
    rw [cfc_sub _ _ H (hc _) (hc _), hid]
  rw [frobNorm_sq_eq_re_trace, (hP.sub hH).eq, hR,
    ← cfc_mul _ _ H (hc _) (hc _), hH.re_trace_cfc]
  apply Finset.sum_congr rfl
  intro i hi
  have hx : max a (eigenvalue H i) - eigenvalue H i = max (a - eigenvalue H i) 0 := by
    rcases le_total a (eigenvalue H i) with h | h
    · rw [max_eq_right h, sub_self, max_eq_right (sub_nonpos.mpr h)]
    · rw [max_eq_left h, max_eq_left (sub_nonneg.mpr h)]
  rw [hx, pow_two]

end NLAlib
