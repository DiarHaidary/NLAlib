/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Pseudoinverse.Pinv

/-!
# Galerkin approximation on a subspace

The Galerkin inverse of $\mathbf{A}$ on the column space of a matrix $\mathbf{X}$ is
$(\mathbf{P}_{\mathbf{X}}\mathbf{A}\mathbf{P}_{\mathbf{X}})^{+}$. It depends on the subspace only,
and in any orthonormal basis $\mathbf{Q}$ of it equals
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}$, which for
positive definite $\mathbf{A}$ is
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}$. Applied to
$\mathbf{b}$ it gives the vector of the subspace whose residual is orthogonal to the subspace, the
minimiser of the $\mathbf{A}$-norm error. The conjugate gradient iterate is the case of a Krylov
space (`NLAlib.cgIterate`); block CG, preconditioned CG and CGLS are other choices of
$\mathbf{X}$, and a matrix right-hand side needs no second definition.

Orthogonality of a residual to the subspace is always stated as
$\mathbf{X}^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbf{y}) = \mathbf{0}$;
`NLAlib.forall_mem_range_star_dotProduct_eq_zero_iff` converts it to the quantified form.

## Main definitions

* `NLAlib.galerkinInverse`: $(\mathbf{P}_{\mathbf{X}}\mathbf{A}\mathbf{P}_{\mathbf{X}})^{+}$.

## Main results

* `NLAlib.galerkinInverse_eq_of_range_eq`: it depends only on the column space.
* `NLAlib.HasOrthonormalCols.galerkinInverse_eq`, `Matrix.PosDef.galerkinInverse_eq`: the frame
  forms.
* `Matrix.PosDef.conjTranspose_mul_one_sub_mul_galerkinInverse`: the Galerkin condition.
* `Matrix.PosDef.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero`: the Galerkin
  condition determines the approximation.
* `Matrix.PosDef.isMinOn_galerkinInverse_mulVec`: $\mathbf{A}$-norm optimality.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n p r : Type*} [Fintype n] [Fintype p] [Fintype r]
  [DecidableEq r]

/-- The **Galerkin inverse** of $\mathbf{A}$ on the column space of $\mathbf{X}$:
$\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{X}) :=
(\mathbf{P}_{\mathbf{X}}\mathbf{A}\mathbf{P}_{\mathbf{X}})^{+}$. Its range and corange already lie
in the column space of $\mathbf{X}$, since the pseudoinverse of
$\mathbf{P}_{\mathbf{X}}\mathbf{A}\mathbf{P}_{\mathbf{X}}$ has the range of its adjoint. It depends
on $\mathbf{X}$ only through its column space (`galerkinInverse_eq_of_range_eq`), and for any
$\mathbf{Q}$ with orthonormal columns spanning that space it is
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}$
(`HasOrthonormalCols.galerkinInverse_eq`). For positive definite $\mathbf{A}$,
$\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$ is the Galerkin approximation to
$\mathbf{A}^{-1}\mathbf{b}$ from that space. Junk value: when
$\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}$ is singular, the pseudoinverse is returned, which is
not a Galerkin solution. [Saad2003, §5.2]. -/
noncomputable def galerkinInverse (A : Matrix n n 𝕜) (X : Matrix n p 𝕜) : Matrix n n 𝕜 :=
  pinv (rangeProjector X * A * rangeProjector X)

omit [DecidableEq r] in
/-- The Galerkin inverse depends only on the column space. -/
theorem galerkinInverse_eq_of_range_eq (A : Matrix n n 𝕜) {X : Matrix n p 𝕜}
    {Y : Matrix n r 𝕜} (h : LinearMap.range X.mulVecLin = LinearMap.range Y.mulVecLin) :
    galerkinInverse A X = galerkinInverse A Y := by
  rw [galerkinInverse, galerkinInverse, rangeProjector_inj.mpr h]

/-- **Frame form of the Galerkin inverse**, for every $\mathbf{A}$: for $\mathbf{Q}$ with
orthonormal columns and the column space of $\mathbf{X}$,
$\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{X}) =
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}$.
[Saad2003, §5.1]. -/
theorem HasOrthonormalCols.galerkinInverse_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {X : Matrix n p 𝕜} (h : LinearMap.range Q.mulVecLin = LinearMap.range X.mulVecLin)
    (A : Matrix n n 𝕜) : galerkinInverse A X = Q * pinv (Qᴴ * A * Q) * Qᴴ := by
  rw [galerkinInverse, ← rangeProjector_inj.mpr h, hQ.rangeProjector_eq,
    show Q * Qᴴ * A * (Q * Qᴴ) = Q * ((Qᴴ * A * Q) * Qᴴ) by simp only [Matrix.mul_assoc],
    hQ.pinv_mul_left, hQ.pinv_mul_conjTranspose_right, Matrix.mul_assoc]

/-- **Frame form for positive definite $\mathbf{A}$**:
$\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{X}) =
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}$ for every
$\mathbf{Q}$ with orthonormal columns spanning the column space of $\mathbf{X}$.
[Saad2003, §5.2]. -/
theorem _root_.Matrix.PosDef.galerkinInverse_eq {A : Matrix n n 𝕜} (hA : A.PosDef)
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) {X : Matrix n p 𝕜}
    (h : LinearMap.range Q.mulVecLin = LinearMap.range X.mulVecLin) :
    galerkinInverse A X = Q * (Qᴴ * A * Q)⁻¹ * Qᴴ := by
  rw [hQ.galerkinInverse_eq h A,
    pinv_of_isUnit (hA.conjTranspose_mul_mul_same hQ.mulVec_injective).isUnit]

omit [DecidableEq r] in
/-- The Galerkin approximation lies in the column space, for every $\mathbf{A}$. -/
theorem galerkinInverse_mulVec_mem (A : Matrix n n 𝕜) (X : Matrix n p 𝕜) (b : n → 𝕜) :
    galerkinInverse A X *ᵥ b ∈ LinearMap.range X.mulVecLin := by
  have hle : LinearMap.range (galerkinInverse A X).mulVecLin ≤ LinearMap.range X.mulVecLin := by
    rw [galerkinInverse, range_pinv, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      conjTranspose_rangeProjector, Matrix.mulVecLin_mul,
      ← range_rangeProjector X]
    exact LinearMap.range_comp_le_range _ _
  exact hle ⟨b, rfl⟩

omit [DecidableEq r] in
/-- **The Galerkin condition**, block form: for positive definite $\mathbf{A}$,
$\mathbf{X}^{\mathsf{H}}(\mathbf{I} - \mathbf{A}\,\mathsf{galerkinInverse}(\mathbf{A},
\mathbf{X})) = \mathbf{0}$, so the residual of every right-hand side is orthogonal to the column
space. [Saad2003, §5.2]. -/
theorem _root_.Matrix.PosDef.conjTranspose_mul_one_sub_mul_galerkinInverse [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosDef) (X : Matrix n p 𝕜) :
    Xᴴ * (1 - A * galerkinInverse A X) = 0 := by
  obtain ⟨Q, hQ, hQX⟩ :=
    exists_hasOrthonormalCols_range_eq (p := Fin X.rank) X (Fintype.card_fin _)
  have hT : IsUnit (Qᴴ * A * Q) := (hA.conjTranspose_mul_mul_same hQ.mulVec_injective).isUnit
  have hXP : Xᴴ = Xᴴ * Q * Qᴴ := by
    rw [Matrix.mul_assoc, ← hQ.rangeProjector_eq, rangeProjector_inj.mpr hQX,
      conjTranspose_mul_rangeProjector]
  have hQG : Qᴴ * (A * galerkinInverse A X) = Qᴴ := by
    rw [hA.galerkinInverse_eq hQ hQX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp hT), Matrix.one_mul]
  rw [hXP, Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hQG, sub_self, Matrix.mul_zero]

/-- The Galerkin condition applied to one right-hand side. -/
private lemma conjTranspose_mulVec_sub_mulVec_galerkinInverse_eq_zero {A : Matrix n n 𝕜}
    (hA : A.PosDef) {X : Matrix n p 𝕜} {b : n → 𝕜} :
    Xᴴ *ᵥ (b - A *ᵥ (galerkinInverse A X *ᵥ b)) = 0 := by
  classical
  have h := congrArg (· *ᵥ b) (hA.conjTranspose_mul_one_sub_mul_galerkinInverse X)
  simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.zero_mulVec, Matrix.mulVec_sub] using h

omit [DecidableEq r] in
/-- **The Galerkin condition determines the approximation**: for positive definite $\mathbf{A}$,
a vector $\mathbf{y}$ of the column space of $\mathbf{X}$ with
$\mathbf{X}^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\mathbf{y}) = \mathbf{0}$ is
$\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$.
[Saad2003, §5.2]. -/
theorem _root_.Matrix.PosDef.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero
    {A : Matrix n n 𝕜} (hA : A.PosDef) {X : Matrix n p 𝕜} {b y : n → 𝕜}
    (hy : y ∈ LinearMap.range X.mulVecLin) (h : Xᴴ *ᵥ (b - A *ᵥ y) = 0) :
    y = galerkinInverse A X *ᵥ b := by
  set z := galerkinInverse A X *ᵥ b
  have hd : y - z ∈ LinearMap.range X.mulVecLin :=
    Submodule.sub_mem _ hy (galerkinInverse_mulVec_mem A X b)
  have hAd : Xᴴ *ᵥ (A *ᵥ (y - z)) = 0 := by
    have : A *ᵥ (y - z) = (b - A *ᵥ z) - (b - A *ᵥ y) := by
      rw [Matrix.mulVec_sub]
      abel
    rw [this, Matrix.mulVec_sub, conjTranspose_mulVec_sub_mulVec_galerkinInverse_eq_zero hA, h,
      sub_zero]
  have h0 := forall_mem_range_star_dotProduct_eq_zero_iff.mpr hAd (y - z) hd
  by_contra hne
  exact (hA.dotProduct_mulVec_pos (sub_ne_zero.mpr hne)).ne' h0

omit [DecidableEq r] in
/-- **Galerkin approximations are $\mathbf{A}$-norm optimal**: for positive definite
$\mathbf{A}$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{X})\,\mathbf{b}$ minimises
$\|\mathbf{x}_\star - \mathbf{y}\|_{\mathbf{A}}^2 =
\operatorname{Re}\bigl((\mathbf{x}_\star - \mathbf{y})^{\mathsf{H}}\mathbf{A}
(\mathbf{x}_\star - \mathbf{y})\bigr)$ over the column space of $\mathbf{X}$.
[Saad2003, §5.2].
Result: galerkin-optimality -/
theorem _root_.Matrix.PosDef.isMinOn_galerkinInverse_mulVec {A : Matrix n n 𝕜} (hA : A.PosDef)
    (X : Matrix n p 𝕜) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) :
    IsMinOn (fun y => RCLike.re (quadForm A (xs - y)))
      (LinearMap.range X.mulVecLin : Set (n → 𝕜)) (galerkinInverse A X *ᵥ b) := by
  intro y hy
  set z := galerkinInverse A X *ᵥ b
  have hd : z - y ∈ LinearMap.range X.mulVecLin :=
    Submodule.sub_mem _ (galerkinInverse_mulVec_mem A X b) hy
  have hcross : star (z - y) ⬝ᵥ (A *ᵥ (xs - z)) = 0 := by
    rw [Matrix.mulVec_sub, hxs]
    exact forall_mem_range_star_dotProduct_eq_zero_iff.mpr
      (conjTranspose_mulVec_sub_mulVec_galerkinInverse_eq_zero hA) _ hd
  have hsplit : xs - y = (xs - z) + (z - y) := by abel
  change RCLike.re (quadForm A (xs - z)) ≤ RCLike.re (quadForm A (xs - y))
  rw [hsplit, hA.isHermitian.re_quadForm_add, hA.isHermitian.star_dotProduct_mulVec_comm, hcross,
    star_zero, map_zero, mul_zero, add_zero]
  exact le_add_of_nonneg_right (hA.posSemidef.re_quadForm_nonneg _)

omit [DecidableEq r] in
/-- **Exactness**: if the solution lies in the column space, the Galerkin approximation is the
solution. -/
theorem _root_.Matrix.PosDef.galerkinInverse_mulVec_eq_of_mem {A : Matrix n n 𝕜} (hA : A.PosDef)
    {X : Matrix n p 𝕜} {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (h : xs ∈ LinearMap.range X.mulVecLin) : galerkinInverse A X *ᵥ b = xs := by
  refine (hA.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero h ?_).symm
  rw [hxs, sub_self, Matrix.mulVec_zero]

end NLAlib
