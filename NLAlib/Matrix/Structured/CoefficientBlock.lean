/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Permutation
public import NLAlib.Matrix.Structured.Kronecker

/-!
# Coefficient block partial transpose

For Hermitian coefficients, the coefficient block matrix has block
$\mathbf{C}_{ij}=\mathbf{A}_j\mathbf{A}_i$. Finite coordinate swaps give the two spectral
norm bounds of [BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.3].

## Main results

* `NLAlib.isHermitian_coefficientBlock` and `NLAlib.eigenvalue_coefficientBlock_zero_nonneg`.
* `NLAlib.specNorm_coefficientBlock_le_specNorm_coefficientVariance` and
  `NLAlib.specNorm_coefficientBlock_le_specNorm_coefficientCovariance`.
* `NLAlib.coefficientBlockKappa_le_sqrt_specNorm_coefficientVariance` and
  `NLAlib.coefficientBlockKappa_le_sqrt_specNorm_coefficientCovariance`.
* `NLAlib.coefficientBlockKappa_eq_sqrt_specNorm_coefficientVariance_of_pairwise_commute`.
* `NLAlib.coefficientBlockKappa_kronecker_one`.
-/

@[expose] public section

open Matrix
open scoped Matrix ComplexOrder MatrixOrder Kronecker

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {ι d r : Type*} [Fintype ι] [Fintype d]

/-- The coefficient block matrix with block $\mathbf{C}_{ij} = \mathbf{A}_j\mathbf{A}_i$.
[BandeiraKuniskyNizicNikolacPesentiWang2026, equation (8)]. -/
def coefficientBlock (A : ι → Matrix d d 𝕜) : Matrix (ι × d) (ι × d) 𝕜 :=
  Matrix.of fun ia jb => (A jb.1 * A ia.1) ia.2 jb.2

/-- The matrix variance $\sum_i \mathbf{A}_i^2$ of a Hermitian coefficient family.
[BandeiraKuniskyNizicNikolacPesentiWang2026, definition of matrix variance in the introduction]. -/
def coefficientVariance (A : ι → Matrix d d 𝕜) : Matrix d d 𝕜 := ∑ i, A i * A i

/-- The sum of outer products of row-major vectorized coefficients.
[BandeiraKuniskyNizicNikolacPesentiWang2026, equation (2)]. -/
def coefficientCovariance (A : ι → Matrix d d 𝕜) : Matrix (d × d) (d × d) 𝕜 :=
  ∑ i, vecMulVec (Function.uncurry (A i)) (star (Function.uncurry (A i)))

/-- The coefficient block parameter $\sqrt{\lambda_0(\mathbf{C})}$. It is zero when the
block index is empty or the block matrix is not Hermitian, by the convention for `eigenvalue`.
[BandeiraKuniskyNizicNikolacPesentiWang2026, equation (7)]. -/
noncomputable def coefficientBlockKappa (A : ι → Matrix d d 𝕜) : ℝ :=
  Real.sqrt (eigenvalue (coefficientBlock A) 0)

/-- Exchange the first and third coordinates of the row-major covariance lift. -/
def coefficientCovarianceSwap : Equiv.Perm ((d × d) × d) where
  toFun x := ((x.2, x.1.2), x.1.1)
  invFun x := ((x.2, x.1.2), x.1.1)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The matrix with vectorized coefficients as columns, tensored with an identity.
This lift implements the coordinate calculation of
[BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.3]. -/
def coefficientCovarianceLift [DecidableEq d] (A : ι → Matrix d d 𝕜) :
    Matrix ((d × d) × d) (ι × d) 𝕜 :=
  (Matrix.of fun ab i => A i ab.1 ab.2) ⊗ₖ (1 : Matrix d d 𝕜)

omit [Fintype ι] in
/-- **Hermitian coefficient block.** If every coefficient $\mathbf{A}_i$ is Hermitian,
the matrix with block $\mathbf{C}_{ij}=\mathbf{A}_j\mathbf{A}_i$ is Hermitian.
[BandeiraKuniskyNizicNikolacPesentiWang2026, equation (8)].
Result: coefficient-block-partial-transpose -/
theorem isHermitian_coefficientBlock (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian) :
    (coefficientBlock A).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro ia jb
  have h : (A ia.1 * A jb.1)ᴴ = A jb.1 * A ia.1 := by
    rw [Matrix.conjTranspose_mul, (hA ia.1).eq, (hA jb.1).eq]
  exact congrFun (congrFun h ia.2) jb.2

/-- **Nonnegative largest coefficient block eigenvalue.** For a finite Hermitian coefficient
family, its coefficient block matrix satisfies $0 \le \lambda_0(\mathbf{C})$.
[BandeiraKuniskyNizicNikolacPesentiWang2026, equations (7)–(8)].
Result: coefficient-block-partial-transpose -/
theorem eigenvalue_coefficientBlock_zero_nonneg (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) : 0 ≤ eigenvalue (coefficientBlock A) 0 := by
  classical
  rcases isEmpty_or_nonempty (ι × d) with h | h
  · rw [eigenvalue_of_card_le _ (by simp)]
  let ia := Classical.choice h
  have hP : (A ia.1 * A ia.1).PosSemidef := by
    simpa only [(hA ia.1).eq] using Matrix.posSemidef_conjTranspose_mul_self (A ia.1)
  have h₀ : 0 ≤ RCLike.re (coefficientBlock A ia ia) :=
    (RCLike.nonneg_iff.mp (hP.diag_nonneg (i := ia.2))).1
  have h₁ := (Matrix.le_iff.mp
    (isHermitian_coefficientBlock A hA).le_eigenvalue_zero_smul_one).diag_nonneg (i := ia)
  apply h₀.trans
  exact sub_nonneg.mp (by
    simpa only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq,
      map_sub, RCLike.smul_re, RCLike.one_re, mul_one] using
      (RCLike.nonneg_iff.mp h₁).1)

omit [Fintype ι] in
/-- The coefficient block of a Hermitian family is the compression by the vectorized
coefficient lift of the permutation exchanging its first and third coordinates.
The finite factorization implements the covariance argument of
[BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.3]. -/
theorem coefficientBlock_eq_conjTranspose_coefficientCovarianceLift_mul_permMatrix_mul
    [DecidableEq d] (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlock A = (coefficientCovarianceLift A)ᴴ *
      coefficientCovarianceSwap.permMatrix 𝕜 * coefficientCovarianceLift A := by
  rw [Matrix.mul_assoc, PEquiv.toMatrix_toPEquiv_mul]
  ext ia jb
  simp [coefficientBlock, coefficientCovarianceLift, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, coefficientCovarianceSwap,
    apply_ite, (hA _).apply, mul_comm]

private def coefficientStack (A : ι → Matrix d d 𝕜) : Matrix (ι × d) d 𝕜 :=
  Matrix.of fun ia b => A ia.1 ia.2 b

private theorem coefficientStack_conjTranspose_mul_self (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    (coefficientStack A)ᴴ * coefficientStack A = coefficientVariance A := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientStack, Matrix.of_apply,
    Fintype.sum_prod_type, coefficientVariance, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun c _ => ?_
  rw [(hA i).apply]

private def coefficientVarianceSwap : Equiv.Perm (ι × (ι × d)) where
  toFun x := (x.2.1, (x.1, x.2.2))
  invFun x := (x.2.1, (x.1, x.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

private theorem coefficientBlock_eq_variance_compression [DecidableEq ι] [DecidableEq d]
    (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlock A = ((1 : Matrix ι ι 𝕜) ⊗ₖ coefficientStack A)ᴴ *
      coefficientVarianceSwap.permMatrix 𝕜 * ((1 : Matrix ι ι 𝕜) ⊗ₖ coefficientStack A) := by
  rw [Matrix.mul_assoc, PEquiv.toMatrix_toPEquiv_mul]
  ext ia jb
  simp [coefficientBlock, coefficientStack, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.one_apply, Fintype.sum_prod_type, coefficientVarianceSwap,
    apply_ite, ite_mul, (hA _).apply]

open scoped Matrix.Norms.L2Operator in
private theorem specNorm_conjTranspose_permMatrix_mul_le {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] (F : Matrix m n 𝕜) (σ : Equiv.Perm m) :
    specNorm (Fᴴ * σ.permMatrix 𝕜 * F) ≤ specNorm F ^ 2 := by
  have hP : specNorm (σ.permMatrix 𝕜) ≤ 1 := Matrix.permMatrix_l2_opNorm_le σ
  calc
    _ ≤ specNorm (Fᴴ * σ.permMatrix 𝕜) * specNorm F := specNorm_mul_le _ _
    _ ≤ (specNorm F * specNorm (σ.permMatrix 𝕜)) * specNorm F := by
      simpa only [specNorm_conjTranspose] using
        mul_le_mul_of_nonneg_right (specNorm_mul_le Fᴴ (σ.permMatrix 𝕜)) (specNorm_nonneg F)
    _ ≤ (specNorm F * 1) * specNorm F :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP (specNorm_nonneg F)) (specNorm_nonneg F)
    _ = _ := by rw [mul_one, sq]

/-- **Coefficient block variance bound.** For a finite Hermitian coefficient family,
the spectral norm of its coefficient block is at most $\|\sum_i \mathbf{A}_i^2\|_2$.
[BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.3].
Result: coefficient-block-partial-transpose -/
theorem specNorm_coefficientBlock_le_specNorm_coefficientVariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientBlock A) ≤ specNorm (coefficientVariance A) := by
  classical
  rw [coefficientBlock_eq_variance_compression A hA, ← coefficientStack_conjTranspose_mul_self A hA,
    specNorm_conjTranspose_mul_self]
  refine (specNorm_conjTranspose_permMatrix_mul_le _ _).trans ?_
  rw [specNorm_kronecker]
  exact pow_le_pow_left₀ (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
    (mul_le_of_le_one_left (specNorm_nonneg _) specNorm_one_le) 2

omit [Fintype d] in
private theorem coefficientCovariance_eq_mul_conjTranspose (A : ι → Matrix d d 𝕜) :
    coefficientCovariance A =
      (Matrix.of fun ab : d × d => fun i => A i ab.1 ab.2) *
        (Matrix.of fun ab : d × d => fun i => A i ab.1 ab.2)ᴴ := by
  ext ab ce
  simp [coefficientCovariance, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.sum_apply, Matrix.vecMulVec_apply, Pi.star_apply, Function.uncurry]

/-- **Coefficient block covariance bound.** For a finite Hermitian coefficient family,
the spectral norm of its coefficient block is at most the spectral norm of the sum of
outer products of its vectorized coefficients.
[BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.3].
Result: coefficient-block-partial-transpose -/
theorem specNorm_coefficientBlock_le_specNorm_coefficientCovariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    specNorm (coefficientBlock A) ≤ specNorm (coefficientCovariance A) := by
  classical
  rw [coefficientBlock_eq_conjTranspose_coefficientCovarianceLift_mul_permMatrix_mul A hA,
    coefficientCovariance_eq_mul_conjTranspose, specNorm_mul_conjTranspose_self]
  refine (specNorm_conjTranspose_permMatrix_mul_le _ _).trans ?_
  rw [coefficientCovarianceLift, specNorm_kronecker]
  exact pow_le_pow_left₀ (mul_nonneg (specNorm_nonneg _) (specNorm_nonneg _))
    (mul_le_of_le_one_right (specNorm_nonneg _) specNorm_one_le) 2

/-- **Coefficient block parameter versus variance.** For a finite Hermitian coefficient family,
$\sqrt{\lambda_0(\mathbf{C})} \le \sqrt{\|\sum_i \mathbf{A}_i^2\|_2}$.
[BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.3].
Result: coefficient-block-partial-transpose -/
theorem coefficientBlockKappa_le_sqrt_specNorm_coefficientVariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa A ≤ Real.sqrt (specNorm (coefficientVariance A)) :=
  Real.sqrt_le_sqrt ((le_abs_self _).trans
    (((isHermitian_coefficientBlock A hA).abs_eigenvalue_le_specNorm 0).trans
      (specNorm_coefficientBlock_le_specNorm_coefficientVariance A hA)))

/-- **Coefficient block parameter versus covariance.** For a finite Hermitian coefficient family,
the square root of its largest coefficient block eigenvalue is at most the square root of
the spectral norm of the sum of outer products of its vectorized coefficients.
[BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.3].
Result: coefficient-block-partial-transpose -/
theorem coefficientBlockKappa_le_sqrt_specNorm_coefficientCovariance (A : ι → Matrix d d 𝕜)
    (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa A ≤ Real.sqrt (specNorm (coefficientCovariance A)) :=
  Real.sqrt_le_sqrt ((le_abs_self _).trans
    (((isHermitian_coefficientBlock A hA).abs_eigenvalue_le_specNorm 0).trans
      (specNorm_coefficientBlock_le_specNorm_coefficientCovariance A hA)))

omit [Fintype ι] in
private theorem coefficientBlock_eq_mul_conjTranspose_of_pairwise_commute
    (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    coefficientBlock A = coefficientStack A * (coefficientStack A)ᴴ := by
  ext ia jb
  have hc : Commute (A jb.1) (A ia.1) := by
    rcases eq_or_ne jb.1 ia.1 with hij | hij
    · rw [hij]
    · exact hcomm hij
  change (A jb.1 * A ia.1) ia.2 jb.2 = _
  rw [hc.eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, coefficientStack, Matrix.of_apply]
  exact Finset.sum_congr rfl fun c _ => by rw [(hA jb.1).apply]

/-- **Attainment for commuting coefficients.** For a finite pairwise commuting Hermitian
family, $\sqrt{\lambda_0(\mathbf{C})} = \sqrt{\|\sum_i \mathbf{A}_i^2\|_2}$.
[BandeiraKuniskyNizicNikolacPesentiWang2026, discussion preceding Proposition 1.3].
Result: coefficient-block-partial-transpose -/
theorem coefficientBlockKappa_eq_sqrt_specNorm_coefficientVariance_of_pairwise_commute
    (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian)
    (hcomm : Pairwise fun i j => Commute (A i) (A j)) :
    coefficientBlockKappa A = Real.sqrt (specNorm (coefficientVariance A)) := by
  rw [coefficientBlockKappa, coefficientBlock_eq_mul_conjTranspose_of_pairwise_commute A hA hcomm,
    ← (Matrix.posSemidef_self_mul_conjTranspose _).specNorm_eq_eigenvalue_zero,
    specNorm_mul_conjTranspose_self, ← coefficientStack_conjTranspose_mul_self A hA,
    specNorm_conjTranspose_mul_self]

omit [Fintype ι] in
private theorem coefficientBlock_kronecker_one [Fintype r] [DecidableEq r]
    (A : ι → Matrix d d 𝕜) :
    coefficientBlock (fun i => A i ⊗ₖ (1 : Matrix r r 𝕜)) =
      (coefficientBlock A ⊗ₖ (1 : Matrix r r 𝕜)).submatrix
        (Equiv.prodAssoc ι d r).symm (Equiv.prodAssoc ι d r).symm := by
  ext ia jb
  simp only [coefficientBlock, Matrix.of_apply, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply, Matrix.kroneckerMap_apply]

/-- **Identity amplification invariance.** For a finite Hermitian coefficient family,
tensoring every coefficient with a nonempty finite identity preserves the coefficient block
parameter $\sqrt{\lambda_0(\mathbf{C})}$.
[BandeiraKuniskyNizicNikolacPesentiWang2026, Proposition 1.4].
Result: coefficient-block-partial-transpose -/
theorem coefficientBlockKappa_kronecker_one [Fintype r] [DecidableEq r] [Nonempty r]
    (A : ι → Matrix d d 𝕜) (hA : ∀ i, (A i).IsHermitian) :
    coefficientBlockKappa (fun i => A i ⊗ₖ (1 : Matrix r r 𝕜)) = coefficientBlockKappa A := by
  rw [coefficientBlockKappa, coefficientBlockKappa, coefficientBlock_kronecker_one,
    eigenvalue_submatrix_equiv, (isHermitian_coefficientBlock A hA).eigenvalue_zero_kronecker_one]

end NLAlib
