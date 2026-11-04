/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Functions.Complexification

/-!
# Descent of similarity from $\mathbb{C}$ to $\mathbb{R}$

Real matrices that are similar over $\mathbb{C}$ are similar over $\mathbb{R}$, and real matrices
that are unitarily similar over $\mathbb{C}$ are orthogonally similar over $\mathbb{R}$; both
simultaneously for a family. If $\mathbf{S}$ intertwines the complexifications then so do its
real and imaginary parts $\mathbf{X}$ and $\mathbf{Y}$, and $\mathbf{X} + t\mathbf{Y}$ is
invertible for some real $t$ because its determinant is a nonzero polynomial in $t$. For a
unitary similarity the same real intertwiner also intertwines the adjoints, and its polar factor
is the orthogonal similarity.

## Main results

* `NLAlib.exists_real_similarity_of_complexify`: similarity.
* `NLAlib.HasOrthonormalCols.exists_real_orthogonal_of_complexify`: unitary similarity.
-/

@[expose] public section

open scoped Matrix Polynomial

namespace NLAlib

variable {ι n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The real and imaginary parts of a complex matrix intertwining two real matrices intertwine
them: if $\mathbf{A}\mathbf{S} = \mathbf{S}\mathbf{B}$ over $\mathbb{C}$, then
$\mathbf{A} \operatorname{Re}\mathbf{S} = (\operatorname{Re}\mathbf{S})\mathbf{B}$ and likewise for
the imaginary part. -/
private theorem mul_map_re_and_mul_map_im {A B : Matrix n n ℝ} {S : Matrix n n ℂ}
    (h : complexify A * S = S * complexify B) :
    A * S.map Complex.re = S.map Complex.re * B ∧ A * S.map Complex.im = S.map Complex.im * B := by
  constructor
  · ext i j
    have hij := congrArg Complex.re (congrFun (congrFun h i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, complexify_apply, Complex.re_sum,
      Complex.mul_re, RCLike.re_toComplex, RCLike.im_toComplex, RCLike.re_to_real,
      RCLike.im_to_real, zero_mul, mul_zero, sub_zero] using hij
  · ext i j
    have hij := congrArg Complex.im (congrFun (congrFun h i) j)
    simpa only [Matrix.mul_apply, Matrix.map_apply, complexify_apply, Complex.im_sum,
      Complex.mul_im, RCLike.re_toComplex, RCLike.im_toComplex, RCLike.re_to_real,
      RCLike.im_to_real, zero_mul, mul_zero, add_zero, zero_add] using hij

/-- If $\mathbf{X} + i\mathbf{Y}$ is invertible for real $\mathbf{X}$, $\mathbf{Y}$ then
$\mathbf{X} + t\mathbf{Y}$ is invertible for some real $t$: the determinant of
$\mathbf{X} + t\mathbf{Y}$ is a nonzero polynomial in $t$. -/
private theorem exists_isUnit_det_add_smul {X Y : Matrix n n ℝ}
    (h : IsUnit (X.map ((↑) : ℝ → ℂ) + Complex.I • Y.map ((↑) : ℝ → ℂ)).det) :
    ∃ t : ℝ, IsUnit (X + t • Y).det := by
  set M : Matrix n n ℝ[X] := X.map Polynomial.C + (Polynomial.X : ℝ[X]) • Y.map Polynomial.C
    with hM
  have hI : Polynomial.eval₂ Complex.ofRealHom Complex.I M.det =
      (X.map ((↑) : ℝ → ℂ) + Complex.I • Y.map ((↑) : ℝ → ℂ)).det := by
    change Polynomial.eval₂RingHom Complex.ofRealHom Complex.I M.det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [hM, RingHom.mapMatrix_apply, Polynomial.coe_eval₂RingHom, Matrix.map_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.eval₂_add, Polynomial.eval₂_C,
      Complex.ofRealHom_eq_coe, Polynomial.eval₂_mul, Polynomial.eval₂_X]
  have ht (t : ℝ) : Polynomial.eval t M.det = (X + t • Y).det := by
    change Polynomial.evalRingHom t M.det = _
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp only [hM, RingHom.mapMatrix_apply, Polynomial.coe_evalRingHom, Matrix.map_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
  have hne : M.det ≠ 0 := fun h0 => by
    rw [← hI, h0, Polynomial.eval₂_zero] at h
    exact not_isUnit_zero h
  by_contra hcon
  rw [not_exists] at hcon
  refine hne (Polynomial.funext fun t => ?_)
  rw [ht, Polynomial.eval_zero]
  exact not_not.mp fun h0 => hcon t (isUnit_iff_ne_zero.mpr h0)

/-- **Real matrices similar over $\mathbb{C}$ are similar over $\mathbb{R}$**, simultaneously for
a family: if $\mathbf{A}_i\mathbf{S} = \mathbf{S}\mathbf{B}_i$ for every $i$ with $\mathbf{S}$
complex invertible, there is a real invertible $\mathbf{T}$ with
$\mathbf{A}_i\mathbf{T} = \mathbf{T}\mathbf{B}_i$ for every $i$.
[HornJohnson2013, Theorem 1.3.29]. -/
theorem exists_real_similarity_of_complexify {A B : ι → Matrix n n ℝ} {S : Matrix n n ℂ}
    (hS : IsUnit S.det) (h : ∀ i, complexify (A i) * S = S * complexify (B i)) :
    ∃ T : Matrix n n ℝ, IsUnit T.det ∧ ∀ i, A i * T = T * B i := by
  have hsplit : S = (S.map Complex.re).map ((↑) : ℝ → ℂ) +
      Complex.I • (S.map Complex.im).map ((↑) : ℝ → ℂ) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [mul_comm, Complex.re_add_im]
  rw [hsplit] at hS
  obtain ⟨t, ht⟩ := exists_isUnit_det_add_smul hS
  refine ⟨_, ht, fun i => ?_⟩
  obtain ⟨h₁, h₂⟩ := mul_map_re_and_mul_map_im (h i)
  rw [Matrix.mul_add, Matrix.mul_smul, Matrix.add_mul, Matrix.smul_mul, h₁, h₂]

/-- **Real matrices unitarily similar over $\mathbb{C}$ are orthogonally similar over
$\mathbb{R}$**, simultaneously for a family: if
$\mathbf{A}_i = \mathbf{U}\mathbf{B}_i\mathbf{U}^{\mathsf{H}}$ for every $i$ with $\mathbf{U}$
unitary, there is a real orthogonal $\mathbf{Q}$ with
$\mathbf{A}_i = \mathbf{Q}\mathbf{B}_i\mathbf{Q}^{\mathsf{T}}$ for every $i$.
[HornJohnson2013, Theorem 2.5.21]. -/
theorem HasOrthonormalCols.exists_real_orthogonal_of_complexify {A B : ι → Matrix n n ℝ}
    {U : Matrix n n ℂ} (hU : HasOrthonormalCols U)
    (h : ∀ i, NLAlib.complexify (A i) = U * NLAlib.complexify (B i) * Uᴴ) :
    ∃ Q : Matrix n n ℝ, HasOrthonormalCols Q ∧ ∀ i, A i = Q * B i * Qᴴ := by
  have h₁ (i : ι) : NLAlib.complexify (A i) * U = U * NLAlib.complexify (B i) := by
    rw [h i, Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  have h₂ (i : ι) : NLAlib.complexify (A i)ᴴ * U = U * NLAlib.complexify (B i)ᴴ := by
    rw [complexify_conjTranspose, complexify_conjTranspose, h i, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
  obtain ⟨T, hT, hAT⟩ := exists_real_similarity_of_complexify
    (A := Sum.elim A fun i => (A i)ᴴ) (B := Sum.elim B fun i => (B i)ᴴ)
    ((Matrix.isUnit_iff_isUnit_det U).mp hU.isUnit) (fun i => i.casesOn h₁ h₂)
  have hQ : HasOrthonormalCols (polarFactor T) :=
    hasOrthonormalCols_polarFactor_iff.mpr
      (Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det T).mpr hT))
  refine ⟨polarFactor T, hQ, fun i => ?_⟩
  have hAQ : A i * polarFactor T = polarFactor T * B i :=
    mul_polarFactor_eq_polarFactor_mul (hAT (Sum.inl i)) (hAT (Sum.inr i))
  rw [← hAQ, Matrix.mul_assoc, hQ.mul_conjTranspose_self, Matrix.mul_one]

end NLAlib
