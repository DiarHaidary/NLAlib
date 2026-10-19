/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.EigenvalueTransform
import NLAlib.Matrix.Basic.Projector

/-!
# The Courant–Fischer variational characterisation of eigenvalues

The $k$-th eigenvalue of a Hermitian matrix is a max–min and a min–max of its quadratic form
over subspaces. The two one-sided subspace statements are the forms proofs use: a lower bound on
the quadratic form over a subspace of dimension $k + 1$ bounds $\lambda_k(\mathbf{A})$ from below,
and an upper bound over a subspace of codimension $k$ bounds it from above. Hypotheses are written
homogeneously, $c \|\mathbf{x}\|^2 \le
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$, with no restriction to nonzero or
unit vectors.

The extreme eigenvalues are also characterised in the Loewner order, which is how bounds on the
largest and smallest eigenvalue of a random matrix are stated and used.

## Main results

* `Matrix.IsHermitian.le_eigenvalue_of_forall_mem`,
  `Matrix.IsHermitian.eigenvalue_le_of_forall_mem`: the one-sided Courant–Fischer bounds.
* `Matrix.IsHermitian.eigenvalue_eq_iSup_iInf`, `Matrix.IsHermitian.eigenvalue_eq_iInf_iSup`:
  the Courant–Fischer theorem as equations.
* `Matrix.IsHermitian.le_smul_one_iff`, `Matrix.IsHermitian.smul_one_le_iff`: the largest and
  smallest eigenvalue in the Loewner order.
* `Matrix.IsHermitian.specNorm_eq_max`, `Matrix.PosSemidef.specNorm_eq_eigenvalue_zero`: the
  spectral norm of a Hermitian matrix;
  `IsStarProjection.exists_mulVec_eq_self_and_re_quadForm_eq_specNorm_mul_sq`:
  the spectral norm of $\mathbf{P}\mathbf{A}$ is attained in the range of $\mathbf{P}$.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-! ### Coordinates in an eigenbasis -/

/-- Coordinates in an orthonormal eigenbasis of a Hermitian matrix: a linear map $T$ to
`Fin (Fintype.card n) → 𝕜` that preserves the Euclidean norm, diagonalises the quadratic form
with the sorted eigenvalues as weights,
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) = \sum_j \lambda_j(\mathbf{A})
\lvert (T\mathbf{x})_j \rvert^2$, and for every set $s$ of coordinates has a subspace of
dimension $\lvert s \rvert$ on which the coordinates outside $s$ vanish. -/
private theorem exists_eigencoordinates {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    ∃ T : (n → 𝕜) →ₗ[𝕜] (Fin (Fintype.card n) → 𝕜),
      (∀ x, ‖WithLp.toLp 2 x‖ ^ 2 = ∑ j, ‖T x j‖ ^ 2) ∧
      (∀ x, RCLike.re (quadForm A x) = ∑ j : Fin (Fintype.card n), eigenvalue A j * ‖T x j‖ ^ 2) ∧
      ∀ s : Finset (Fin (Fintype.card n)), ∃ S : Submodule 𝕜 (n → 𝕜),
        Module.finrank 𝕜 S = s.card ∧ ∀ x ∈ S, ∀ j ∉ s, T x j = 0 := by
  classical
  obtain ⟨U, hU, hAU⟩ := hA.exists_eq_mul_diagonal_mul_conjTranspose
  have hU' : HasOrthonormalCols Uᴴ := hU.conjTranspose_of_card_eq (Fintype.card_fin _).symm
  refine ⟨Uᴴ.mulVecLin, fun x => ?_, fun x => ?_, fun s => ?_⟩
  · rw [Matrix.mulVecLin_apply, ← hU'.norm_toLp_mulVec x, EuclideanSpace.norm_sq_eq]
  · have hq : quadForm A x = quadForm
        (Matrix.diagonal fun i : Fin (Fintype.card n) => ((eigenvalue A i : ℝ) : 𝕜))
        (Uᴴ *ᵥ x) := by
      rw [← quadForm_conjTranspose_mul_mul, Matrix.conjTranspose_conjTranspose, ← hAU]
    rw [hq, quadForm_diagonal, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← RCLike.ofReal_mul, RCLike.ofReal_re, Matrix.mulVecLin_apply]
  · refine ⟨LinearMap.range
      (U.submatrix id (Subtype.val : s → Fin (Fintype.card n))).mulVecLin, ?_, ?_⟩
    · exact (hU.submatrix (Equiv.refl n) Subtype.val_injective).rank_eq.trans
        (Fintype.card_coe s)
    · rintro _ ⟨y, rfl⟩ j hj
      have hUs : Uᴴ * U.submatrix id (Subtype.val : s → Fin (Fintype.card n)) =
          (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜).submatrix id
            Subtype.val := by
        rw [← hU.conjTranspose_mul_self]
        rfl
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hUs]
      refine Finset.sum_eq_zero fun t _ => ?_
      change (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) 𝕜) j t.1 * y t = 0
      rw [Matrix.one_apply_ne fun h : j = t.1 => hj (h ▸ t.2), zero_mul]

/-- If the coordinates $\mathbf{y}_j$ with $j < k$ vanish, the weighted sum is at most
$\lambda_k(\mathbf{A})$ times the plain sum:
$\sum_j \lambda_j(\mathbf{A}) \lvert \mathbf{y}_j \rvert^2
\le \lambda_k(\mathbf{A}) \sum_j \lvert \mathbf{y}_j \rvert^2$. -/
private theorem sum_eigenvalue_mul_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    {y : Fin (Fintype.card n) → 𝕜} (hy : ∀ j : Fin (Fintype.card n), (j : ℕ) < k → y j = 0) :
    ∑ j : Fin (Fintype.card n), eigenvalue A j * ‖y j‖ ^ 2 ≤
      eigenvalue A k * ∑ j, ‖y j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge (j : ℕ) k with hjk | hjk
  · rw [hy j hjk, norm_zero, zero_pow two_ne_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalue_le_eigenvalue hjk j.isLt) (sq_nonneg _)

/-- If the coordinates $\mathbf{y}_j$ with $j > k$ vanish, $k < \lvert n \rvert$, the weighted
sum is at least $\lambda_k(\mathbf{A})$ times the plain sum:
$\lambda_k(\mathbf{A}) \sum_j \lvert \mathbf{y}_j \rvert^2
\le \sum_j \lambda_j(\mathbf{A}) \lvert \mathbf{y}_j \rvert^2$. -/
private theorem le_sum_eigenvalue_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k < Fintype.card n) {y : Fin (Fintype.card n) → 𝕜}
    (hy : ∀ j : Fin (Fintype.card n), k < (j : ℕ) → y j = 0) :
    eigenvalue A k * ∑ j, ‖y j‖ ^ 2 ≤
      ∑ j : Fin (Fintype.card n), eigenvalue A j * ‖y j‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rcases lt_or_ge k (j : ℕ) with hjk | hjk
  · rw [hy j hjk, norm_zero, zero_pow two_ne_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (hA.eigenvalue_le_eigenvalue hjk hk) (sq_nonneg _)

omit [Fintype n] in
/-- A subspace of dimension larger than $\lvert s \rvert$ has a nonzero vector whose coordinates in
$s$ vanish. -/
private theorem exists_mem_ne_zero_forall_eq_zero [Finite n] {N : ℕ} (T : (n → 𝕜) →ₗ[𝕜] (Fin N → 𝕜))
    (s : Finset (Fin N)) (S : Submodule 𝕜 (n → 𝕜)) (hS : s.card < Module.finrank 𝕜 S) :
    ∃ x ∈ S, x ≠ 0 ∧ ∀ j ∈ s, T x j = 0 := by
  have hker : LinearMap.ker
      ((LinearMap.funLeft 𝕜 𝕜 (Subtype.val : s → Fin N) ∘ₗ T).domRestrict S) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt
      (by rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_coe])
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  exact ⟨y, y.2, fun h => hy0 (Subtype.ext h),
    fun j hj => congrFun (LinearMap.mem_ker.mp hy) ⟨j, hj⟩⟩

private theorem norm_toLp_sq_pos {x : n → 𝕜} (hx : x ≠ 0) : 0 < ‖WithLp.toLp 2 x‖ ^ 2 :=
  pow_pos (norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hx)) 2

/-! ### Unit vectors -/

/-- A nonzero vector has a unit multiple, and the quadratic form scales with the squared norm. -/
private theorem exists_smul_norm_eq_one {x : n → 𝕜} (hx : x ≠ 0) :
    ∃ a : 𝕜, ‖WithLp.toLp 2 (a • x)‖ = 1 ∧ ∀ A : Matrix n n 𝕜,
      RCLike.re (quadForm A x) = RCLike.re (quadForm A (a • x)) * ‖WithLp.toLp 2 x‖ ^ 2 := by
  have hx' : ‖WithLp.toLp 2 x‖ ≠ 0 := norm_ne_zero_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr hx)
  have ha : ((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr (inv_ne_zero hx')
  have h1 : ‖WithLp.toLp 2 (((‖WithLp.toLp 2 x‖⁻¹ : ℝ) : 𝕜) • x)‖ = 1 := by
    rw [WithLp.toLp_smul, norm_smul, RCLike.norm_ofReal, abs_inv, abs_norm, inv_mul_cancel₀ hx']
  refine ⟨_, h1, fun A => ?_⟩
  rw [re_quadForm_eq_rayleighQuotient_mul A x, ← rayleighQuotient_smul A ha x,
    rayleighQuotient_of_norm_eq_one A h1]

/-- A lower bound on the quadratic form over the unit vectors of a subspace is a homogeneous
lower bound on the subspace. -/
private theorem mul_norm_sq_le_re_quadForm_of_forall_unit {A : Matrix n n 𝕜}
    {S : Submodule 𝕜 (n → 𝕜)} {c : ℝ}
    (h : ∀ x ∈ S, ‖WithLp.toLp 2 x‖ = 1 → c ≤ RCLike.re (quadForm A x)) (x : n → 𝕜)
    (hx : x ∈ S) : c * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [quadForm_zero_right, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero, mul_zero,
      map_zero]
  · obtain ⟨a, ha, hq⟩ := exists_smul_norm_eq_one hx0
    rw [hq A]
    exact mul_le_mul_of_nonneg_right (h _ (S.smul_mem a hx) ha) (sq_nonneg _)

/-- An upper bound on the quadratic form over the unit vectors of a subspace is a homogeneous
upper bound on the subspace. -/
private theorem re_quadForm_le_mul_norm_sq_of_forall_unit {A : Matrix n n 𝕜}
    {S : Submodule 𝕜 (n → 𝕜)} {c : ℝ}
    (h : ∀ x ∈ S, ‖WithLp.toLp 2 x‖ = 1 → RCLike.re (quadForm A x) ≤ c) (x : n → 𝕜)
    (hx : x ∈ S) : RCLike.re (quadForm A x) ≤ c * ‖WithLp.toLp 2 x‖ ^ 2 := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [quadForm_zero_right, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero, mul_zero,
      map_zero]
  · obtain ⟨a, ha, hq⟩ := exists_smul_norm_eq_one hx0
    rw [hq A]
    exact mul_le_mul_of_nonneg_right (h _ (S.smul_mem a hx) ha) (sq_nonneg _)

/-- A subspace of positive dimension has a unit vector. -/
private theorem exists_mem_norm_eq_one {S : Submodule 𝕜 (n → 𝕜)}
    (hS : 0 < Module.finrank 𝕜 S) : ∃ x ∈ S, ‖WithLp.toLp 2 x‖ = 1 := by
  obtain ⟨x, hx0⟩ := Module.finrank_pos_iff_exists_ne_zero.mp hS
  obtain ⟨a, ha, -⟩ := exists_smul_norm_eq_one (x := (x : n → 𝕜)) fun h => hx0 (Subtype.ext h)
  exact ⟨_, S.smul_mem a x.2, ha⟩

/-- On unit vectors the quadratic form is bounded by the spectral norm:
$\lvert \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \rvert \le
\|\mathbf{A}\|_2$ when $\|\mathbf{x}\| = 1$. -/
private theorem abs_re_quadForm_le_specNorm (A : Matrix n n 𝕜) {x : n → 𝕜}
    (hx : ‖WithLp.toLp 2 x‖ = 1) : |RCLike.re (quadForm A x)| ≤ specNorm A := by
  have h := abs_re_quadForm_le A x
  rwa [hx, one_pow, mul_one] at h

private theorem bddBelow_range_re_quadForm (A : Matrix n n 𝕜) (p : (n → 𝕜) → Prop) :
    BddBelow (Set.range fun x : {x : n → 𝕜 // p x ∧ ‖WithLp.toLp 2 x‖ = 1} =>
      RCLike.re (quadForm A x.1)) := by
  refine ⟨-specNorm A, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_le.mp (abs_re_quadForm_le_specNorm A x.2.2)).1

private theorem bddAbove_range_re_quadForm (A : Matrix n n 𝕜) (p : (n → 𝕜) → Prop) :
    BddAbove (Set.range fun x : {x : n → 𝕜 // p x ∧ ‖WithLp.toLp 2 x‖ = 1} =>
      RCLike.re (quadForm A x.1)) := by
  refine ⟨specNorm A, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (abs_le.mp (abs_re_quadForm_le_specNorm A x.2.2)).2

/-- The quadratic form of a matrix at a unit eigenvector with a real eigenvalue is the
eigenvalue: $\mathbf{A}\mathbf{u} = c\mathbf{u}$ and $\|\mathbf{u}\| = 1$ give
$\operatorname{Re}(\mathbf{u}^{\mathsf{H}}\mathbf{A}\mathbf{u}) = c$. -/
theorem re_quadForm_of_mulVec_eq_smul {A : Matrix n n 𝕜} {u : n → 𝕜} {c : ℝ}
    (hu : ‖WithLp.toLp 2 u‖ = 1) (h : A *ᵥ u = c • u) : RCLike.re (quadForm A u) = c := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)] at h
  rw [quadForm, h, dotProduct_smul, smul_eq_mul,
    EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, hu, one_pow, RCLike.ofReal_one, mul_one,
    RCLike.ofReal_re]

/-! ### One-sided subspace bounds -/

/-- **Courant–Fischer, lower bound.** If the quadratic form of a Hermitian $\mathbf{A}$ satisfies
$c \|\mathbf{x}\|^2 \le \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$ for every
$\mathbf{x}$ in a subspace of dimension at least $k + 1$, then $c \le \lambda_k(\mathbf{A})$.
[HornJohnson2013, Theorem 4.2.6]; stated there as an equation over $\mathbb{C}$ with eigenvalues
in increasing order, here as the inequality a proof applies, over any `RCLike` field,
non-increasing.
Port of `Matrix.IsHermitian.le_eigenvalues₀_of_forall_mem`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.le_eigenvalue_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (S : Submodule 𝕜 (n → 𝕜)) (hS : k + 1 ≤ Module.finrank 𝕜 S)
    {c : ℝ} (h : ∀ x ∈ S, c * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x)) :
    c ≤ eigenvalue A k := by
  have hk : k < Fintype.card n := by
    have h1 := S.finrank_le
    rw [Module.finrank_fintype_fun_eq_card] at h1
    omega
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  obtain ⟨x, hxS, hx0, hx⟩ := exists_mem_ne_zero_forall_eq_zero T (Finset.Iio ⟨k, hk⟩) S
    (by rw [Fin.card_Iio]; exact hS)
  have h1 : RCLike.re (quadForm A x) ≤ eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 := by
    rw [hT₁, hT₂]
    exact sum_eigenvalue_mul_le hA fun j hj => hx j (Finset.mem_Iio.mpr hj)
  exact le_of_mul_le_mul_right ((h x hxS).trans h1) (norm_toLp_sq_pos hx0)

/-- **Courant–Fischer, upper bound.** If the quadratic form of a Hermitian $\mathbf{A}$ satisfies
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \le c \|\mathbf{x}\|^2$ for every
$\mathbf{x}$ in a subspace of codimension at most $k$, for a valid index $k < \lvert n \rvert$,
then $\lambda_k(\mathbf{A}) \le c$. The index must be valid: beyond the size of $\mathbf{A}$ the
eigenvalue is $0$ by convention while the zero subspace satisfies the hypothesis for negative $c$.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_le_of_forall_mem`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_le_of_forall_mem {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) (W : Submodule 𝕜 (n → 𝕜))
    (hW : Fintype.card n ≤ Module.finrank 𝕜 W + k) {c : ℝ}
    (h : ∀ x ∈ W, RCLike.re (quadForm A x) ≤ c * ‖WithLp.toLp 2 x‖ ^ 2) :
    eigenvalue A k ≤ c := by
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  obtain ⟨x, hxW, hx0, hx⟩ := exists_mem_ne_zero_forall_eq_zero T (Finset.Ioi ⟨k, hk⟩) W
    (by rw [Fin.card_Ioi]; dsimp only; omega)
  have h1 : eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
    rw [hT₁, hT₂]
    exact le_sum_eigenvalue_mul hA hk fun j hj => hx j (Finset.mem_Ioi.mpr hj)
  exact le_of_mul_le_mul_right (h1.trans (h x hxW)) (norm_toLp_sq_pos hx0)

/-- The lower bound is attained: for $k < \lvert n \rvert$ there is a subspace of dimension
$k + 1$ on which
$\lambda_k(\mathbf{A}) \|\mathbf{x}\|^2 \le
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$ (the span of the first $k + 1$
eigenvectors).
Port of `Matrix.IsHermitian.exists_submodule_eigenvalues₀_mul_le`. -/
theorem _root_.Matrix.IsHermitian.exists_submodule_eigenvalue_mul_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ S : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 S = k + 1 ∧
      ∀ x ∈ S, eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := exists_eigencoordinates hA
  obtain ⟨S, hS, hST⟩ := hT₃ (Finset.Iic ⟨k, hk⟩)
  refine ⟨S, by rw [hS, Fin.card_Iic], fun x hx => ?_⟩
  rw [hT₁, hT₂]
  exact le_sum_eigenvalue_mul hA hk fun j hj =>
    hST x hx j fun hmem => absurd (Finset.mem_Iic.mp hmem) (not_le.mpr hj)

/-- The upper bound is attained: for $k < \lvert n \rvert$ there is a subspace of codimension $k$
on which
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \le \lambda_k(\mathbf{A})
\|\mathbf{x}\|^2$ (the span of the eigenvectors from the $k$-th on).
Port of `Matrix.IsHermitian.exists_submodule_le_eigenvalues₀_mul`. -/
theorem _root_.Matrix.IsHermitian.exists_submodule_le_eigenvalue_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    ∃ W : Submodule 𝕜 (n → 𝕜), Module.finrank 𝕜 W + k = Fintype.card n ∧
      ∀ x ∈ W, RCLike.re (quadForm A x) ≤ eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 := by
  obtain ⟨T, hT₁, hT₂, hT₃⟩ := exists_eigencoordinates hA
  obtain ⟨W, hW, hWT⟩ := hT₃ (Finset.Ici ⟨k, hk⟩)
  refine ⟨W, by rw [hW, Fin.card_Ici]; dsimp only; omega, fun x hx => ?_⟩
  rw [hT₁, hT₂]
  exact sum_eigenvalue_mul_le hA fun j hj =>
    hWT x hx j fun hmem => absurd (Finset.mem_Ici.mp hmem) (not_le.mpr hj)

/-! ### The Courant–Fischer equations -/

/-- **Courant–Fischer, max–min form.** For Hermitian $\mathbf{A}$ and $k < \lvert n \rvert$,
$$\lambda_k(\mathbf{A}) = \sup_{\dim S = k + 1} \;
  \inf_{\mathbf{x} \in S, \, \|\mathbf{x}\| = 1}
  \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}),$$
the supremum over subspaces $S$.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_eq_iSup_iInf`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_iSup_iInf {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k =
      ⨆ S : {S : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 S = k + 1},
        ⨅ x : {x : n → 𝕜 // x ∈ S.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  have hinner : ∀ S : {S : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 S = k + 1},
      (⨅ x : {x : n → 𝕜 // x ∈ S.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1)) ≤
        eigenvalue A k := fun S =>
    hA.le_eigenvalue_of_forall_mem S.1 S.2.ge <|
      mul_norm_sq_le_re_quadForm_of_forall_unit fun x hx hx1 =>
        ciInf_le (bddBelow_range_re_quadForm A (· ∈ S.1)) ⟨x, hx, hx1⟩
  obtain ⟨S, hS, hAS⟩ := hA.exists_submodule_eigenvalue_mul_le hk
  have : Nonempty {S : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 S = k + 1} := ⟨⟨S, hS⟩⟩
  refine le_antisymm ?_ (ciSup_le hinner)
  obtain ⟨u, huS, hu⟩ := exists_mem_norm_eq_one (S := S) (by omega)
  have : Nonempty {x : n → 𝕜 // x ∈ S ∧ ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, huS, hu⟩⟩
  refine le_ciSup_of_le ⟨eigenvalue A k, ?_⟩ ⟨S, hS⟩ (le_ciInf fun x => ?_)
  · rintro _ ⟨S', rfl⟩
    exact hinner S'
  · have h := hAS x.1 x.2.1
    rwa [x.2.2, one_pow, mul_one] at h

/-- **Courant–Fischer, min–max form.** For Hermitian $\mathbf{A}$ and $k < \lvert n \rvert$,
$$\lambda_k(\mathbf{A}) = \inf_{\dim W + k = \lvert n \rvert} \;
  \sup_{\mathbf{x} \in W, \, \|\mathbf{x}\| = 1}
  \operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}),$$
the infimum over subspaces $W$ of codimension $k$.
[HornJohnson2013, Theorem 4.2.6].
Port of `Matrix.IsHermitian.eigenvalues₀_eq_iInf_iSup`.
Result: courant-fischer -/
theorem _root_.Matrix.IsHermitian.eigenvalue_eq_iInf_iSup {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k < Fintype.card n) :
    eigenvalue A k =
      ⨅ W : {W : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 W + k = Fintype.card n},
        ⨆ x : {x : n → 𝕜 // x ∈ W.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  have hinner : ∀ W : {W : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 W + k = Fintype.card n},
      eigenvalue A k ≤
        ⨆ x : {x : n → 𝕜 // x ∈ W.1 ∧ ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) :=
    fun W => hA.eigenvalue_le_of_forall_mem hk W.1 W.2.ge <|
      re_quadForm_le_mul_norm_sq_of_forall_unit fun x hx hx1 =>
        le_ciSup (bddAbove_range_re_quadForm A (· ∈ W.1)) ⟨x, hx, hx1⟩
  obtain ⟨W, hW, hAW⟩ := hA.exists_submodule_le_eigenvalue_mul hk
  have : Nonempty {W : Submodule 𝕜 (n → 𝕜) // Module.finrank 𝕜 W + k = Fintype.card n} :=
    ⟨⟨W, hW⟩⟩
  refine le_antisymm (le_ciInf hinner) ?_
  obtain ⟨u, huW, hu⟩ := exists_mem_norm_eq_one (S := W) (by omega)
  have : Nonempty {x : n → 𝕜 // x ∈ W ∧ ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, huW, hu⟩⟩
  refine ciInf_le_of_le ⟨eigenvalue A k, ?_⟩ ⟨W, hW⟩ (ciSup_le fun x => ?_)
  · rintro _ ⟨W', rfl⟩
    exact hinner W'
  · have h := hAW x.1 x.2.1
    rwa [x.2.2, one_pow, mul_one] at h

/-! ### Extreme eigenvalues -/

/-- **Rayleigh bound, upper.** The quadratic form of a Hermitian matrix is at most its largest
eigenvalue times $\|\mathbf{x}\|^2$:
$\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \le \lambda_0(\mathbf{A})
\|\mathbf{x}\|^2$. [HornJohnson2013, Theorem 4.2.2]. -/
theorem _root_.Matrix.IsHermitian.re_quadForm_le_eigenvalue_zero_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (x : n → 𝕜) :
    RCLike.re (quadForm A x) ≤ eigenvalue A 0 * ‖WithLp.toLp 2 x‖ ^ 2 := by
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  rw [hT₁, hT₂]
  exact sum_eigenvalue_mul_le hA fun j hj => absurd hj (Nat.not_lt_zero _)

/-- **Rayleigh bound, lower.** The quadratic form of a Hermitian matrix is at least its smallest
eigenvalue times $\|\mathbf{x}\|^2$:
$\lambda_k(\mathbf{A}) \|\mathbf{x}\|^2 \le
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$, the last index given by the
equation $k + 1 = \lvert n \rvert$.
[HornJohnson2013, Theorem 4.2.2].
Port of `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`, there as an infimum. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_mul_le_re_quadForm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) (x : n → 𝕜) :
    eigenvalue A k * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) := by
  obtain ⟨T, hT₁, hT₂, -⟩ := exists_eigencoordinates hA
  rw [hT₁, hT₂]
  exact le_sum_eigenvalue_mul hA (by omega) fun j hj => absurd j.isLt (by omega)

/-- A Hermitian matrix is below its largest eigenvalue times the identity:
$\mathbf{A} \preceq \lambda_0(\mathbf{A}) \mathbf{I}$. -/
theorem _root_.Matrix.IsHermitian.le_eigenvalue_zero_smul_one [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) : A ≤ eigenvalue A 0 • (1 : Matrix n n 𝕜) := by
  rw [hA.le_iff_re_quadForm_le (isHermitian_real_smul_one _)]
  intro x
  rw [re_quadForm_real_smul_one]
  exact hA.re_quadForm_le_eigenvalue_zero_mul x

/-- A Hermitian matrix is above its smallest eigenvalue times the identity:
$\lambda_k(\mathbf{A}) \mathbf{I} \preceq \mathbf{A}$ for $k + 1 = \lvert n \rvert$. -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_smul_one_le [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    eigenvalue A k • (1 : Matrix n n 𝕜) ≤ A := by
  rw [(isHermitian_real_smul_one _).le_iff_re_quadForm_le hA]
  intro x
  rw [re_quadForm_real_smul_one]
  exact hA.eigenvalue_last_mul_le_re_quadForm hk x

/-- **The largest eigenvalue in the Loewner order.** For a Hermitian matrix on a nonempty index
type, $\mathbf{A} \preceq c\mathbf{I}$ exactly when $\lambda_0(\mathbf{A}) \le c$. This is the
form in which an upper bound on $\lambda_{\max}$ is used. -/
theorem _root_.Matrix.IsHermitian.le_smul_one_iff [DecidableEq n] [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ} :
    A ≤ c • (1 : Matrix n n 𝕜) ↔ eigenvalue A 0 ≤ c := by
  rw [hA.le_iff_re_quadForm_le (isHermitian_real_smul_one c)]
  simp only [re_quadForm_real_smul_one]
  refine ⟨fun h => ?_, fun h x => ?_⟩
  · refine hA.eigenvalue_le_of_forall_mem Fintype.card_pos ⊤ ?_ fun x _ => h x
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, add_zero]
  · exact (hA.re_quadForm_le_eigenvalue_zero_mul x).trans
      (mul_le_mul_of_nonneg_right h (sq_nonneg _))

/-- **The smallest eigenvalue in the Loewner order.** For a Hermitian matrix and
$k + 1 = \lvert n \rvert$, $c\mathbf{I} \preceq \mathbf{A}$ exactly when
$c \le \lambda_k(\mathbf{A})$. This is the form in which a lower bound on $\lambda_{\min}$ is
used. -/
theorem _root_.Matrix.IsHermitian.smul_one_le_iff [DecidableEq n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) {c : ℝ} :
    c • (1 : Matrix n n 𝕜) ≤ A ↔ c ≤ eigenvalue A k := by
  rw [(isHermitian_real_smul_one c).le_iff_re_quadForm_le hA]
  simp only [re_quadForm_real_smul_one]
  refine ⟨fun h => ?_, fun h x => ?_⟩
  · refine hA.le_eigenvalue_of_forall_mem ⊤ ?_ fun x _ => h x
    rw [finrank_top, Module.finrank_fintype_fun_eq_card, hk]
  · exact (mul_le_mul_of_nonneg_right h (sq_nonneg _)).trans
      (hA.eigenvalue_last_mul_le_re_quadForm hk x)

/-- **Rayleigh–Ritz theorem, largest eigenvalue.** The largest eigenvalue of a Hermitian matrix
on a nonempty index type is the supremum of its quadratic form over unit vectors:
$\lambda_0(\mathbf{A}) = \sup_{\|\mathbf{x}\| = 1}
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$. [HornJohnson2013, Theorem 4.2.2].
Result: rayleigh-ritz -/
theorem _root_.Matrix.IsHermitian.eigenvalue_zero_eq_iSup [Nonempty n] {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    eigenvalue A 0 = ⨆ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  obtain ⟨u, hu, hAu⟩ := hA.exists_norm_eq_one_and_mulVec_eq (k := 0) Fintype.card_pos
  have : Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, hu⟩⟩
  have hle : ∀ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1},
      RCLike.re (quadForm A x.1) ≤ eigenvalue A 0 := fun x => by
    have h := hA.re_quadForm_le_eigenvalue_zero_mul x.1
    rwa [x.2, one_pow, mul_one] at h
  refine le_antisymm ?_ (ciSup_le hle)
  rw [← re_quadForm_of_mulVec_eq_smul hu hAu]
  exact le_ciSup (f := fun x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} =>
    RCLike.re (quadForm A x.1)) ⟨eigenvalue A 0, by rintro _ ⟨x, rfl⟩; exact hle x⟩ ⟨u, hu⟩

/-- **Rayleigh–Ritz theorem, smallest eigenvalue.** The smallest eigenvalue of a Hermitian matrix
is the infimum of its quadratic form over unit vectors:
$\lambda_k(\mathbf{A}) = \inf_{\|\mathbf{x}\| = 1}
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x})$ for $k + 1 = \lvert n \rvert$.
[HornJohnson2013, Theorem 4.2.2].
Port of `Matrix.IsHermitian.eigenvalues₀_last_eq_iInf`.
Result: rayleigh-ritz -/
theorem _root_.Matrix.IsHermitian.eigenvalue_last_eq_iInf {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    eigenvalue A k = ⨅ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1}, RCLike.re (quadForm A x.1) := by
  obtain ⟨u, hu, hAu⟩ := hA.exists_norm_eq_one_and_mulVec_eq (k := k) (by omega)
  have : Nonempty {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} := ⟨⟨u, hu⟩⟩
  have hle : ∀ x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1},
      eigenvalue A k ≤ RCLike.re (quadForm A x.1) := fun x => by
    have h := hA.eigenvalue_last_mul_le_re_quadForm hk x.1
    rwa [x.2, one_pow, mul_one] at h
  refine le_antisymm (le_ciInf hle) ?_
  rw [← re_quadForm_of_mulVec_eq_smul hu hAu]
  exact ciInf_le (f := fun x : {x : n → 𝕜 // ‖WithLp.toLp 2 x‖ = 1} =>
    RCLike.re (quadForm A x.1)) ⟨eigenvalue A k, by rintro _ ⟨x, rfl⟩; exact hle x⟩ ⟨u, hu⟩

/-! ### The spectral norm of a Hermitian matrix -/

/-- Every eigenvalue of a Hermitian matrix is bounded in absolute value by the spectral norm:
$\lvert \lambda_k(\mathbf{A}) \rvert \le \|\mathbf{A}\|_2$. -/
theorem _root_.Matrix.IsHermitian.abs_eigenvalue_le_specNorm {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (k : ℕ) : |eigenvalue A k| ≤ specNorm A := by
  rcases lt_or_ge k (Fintype.card n) with hk | hk
  · obtain ⟨u, hu, hAu⟩ := hA.exists_norm_eq_one_and_mulVec_eq hk
    rw [← re_quadForm_of_mulVec_eq_smul hu hAu]
    exact abs_re_quadForm_le_specNorm A hu
  · rw [eigenvalue_of_card_le A hk, abs_zero]
    exact specNorm_nonneg A

/-- The spectral norm of a Hermitian matrix is the larger of the absolute values of its extreme
eigenvalues: $\|\mathbf{A}\|_2 = \max(\lvert \lambda_0(\mathbf{A}) \rvert,
\lvert \lambda_k(\mathbf{A}) \rvert)$ for $k + 1 = \lvert n \rvert$.
Port of `NLAlib.specNorm_eq_norm_eigenvalue`, there over $\mathbb{R}$ as a supremum over the
unsorted eigenvalues. -/
theorem _root_.Matrix.IsHermitian.specNorm_eq_max {A : Matrix n n 𝕜} (hA : A.IsHermitian) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    specNorm A = max |eigenvalue A 0| |eigenvalue A k| := by
  refine le_antisymm ?_
    (max_le (hA.abs_eigenvalue_le_specNorm 0) (hA.abs_eigenvalue_le_specNorm k))
  rw [hA.specNorm_le_iff_abs_re_quadForm_le (le_max_of_le_left (abs_nonneg _))]
  intro x
  have h0 := hA.re_quadForm_le_eigenvalue_zero_mul x
  have hk' := hA.eigenvalue_last_mul_le_re_quadForm hk x
  have hx := sq_nonneg ‖WithLp.toLp 2 x‖
  rw [abs_le]
  constructor
  · refine le_trans ?_ hk'
    rw [← neg_mul]
    exact mul_le_mul_of_nonneg_right
      ((neg_le_neg (le_max_right _ _)).trans (neg_abs_le _)) hx
  · exact h0.trans (mul_le_mul_of_nonneg_right ((le_abs_self _).trans (le_max_left _ _)) hx)

/-- The spectral norm of a positive semidefinite matrix is its largest eigenvalue:
$\|\mathbf{A}\|_2 = \lambda_0(\mathbf{A})$. -/
theorem _root_.Matrix.PosSemidef.specNorm_eq_eigenvalue_zero {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) : specNorm A = eigenvalue A 0 := by
  classical
  refine le_antisymm ?_
    ((le_abs_self _).trans (hA.isHermitian.abs_eigenvalue_le_specNorm 0))
  rw [hA.specNorm_le_iff (hA.eigenvalue_nonneg 0)]
  exact hA.isHermitian.le_eigenvalue_zero_smul_one

/-- A positive semidefinite matrix on a nonempty index type has a unit eigenvector for its
spectral norm: $\|\mathbf{u}\| = 1$ and $\mathbf{A}\mathbf{u} = \|\mathbf{A}\|_2 \mathbf{u}$.
Port of `NLAlib.exists_unit_mulVec_eq_specNorm_smul`, there over $\mathbb{R}$. -/
theorem _root_.Matrix.PosSemidef.exists_norm_eq_one_and_mulVec_eq_specNorm_smul [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) :
    ∃ u : n → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ A *ᵥ u = specNorm A • u := by
  rw [hA.specNorm_eq_eigenvalue_zero]
  exact hA.isHermitian.exists_norm_eq_one_and_mulVec_eq Fintype.card_pos

/-- **The spectral norm of a projected matrix is attained in the range of the projector**: for an
orthogonal projector $\mathbf{P}$ with $\|\mathbf{P}\mathbf{A}\|_2 > 0$ there is a unit vector
$\mathbf{u}$ with $\mathbf{P}\mathbf{u} = \mathbf{u}$ and
$\operatorname{Re}(\mathbf{u}^{\mathsf{H}}\mathbf{A}\mathbf{A}^{\mathsf{H}}\mathbf{u}) =
\|\mathbf{P}\mathbf{A}\|_2^2$: a top eigenvector of
$\mathbf{P}\mathbf{A}\mathbf{A}^{\mathsf{H}}\mathbf{P}$, which lies in the range of $\mathbf{P}$.
[TroppWebber2023, Lemma 9.4 (proof)], the step before (9.4). -/
theorem _root_.IsStarProjection.exists_mulVec_eq_self_and_re_quadForm_eq_specNorm_mul_sq
    {m : Type*} [Fintype m] {A : Matrix m n 𝕜} {P : Matrix m m 𝕜} (hP : IsStarProjection P)
    (h₀ : 0 < specNorm (P * A)) :
    ∃ u : m → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ P *ᵥ u = u ∧
      RCLike.re (quadForm (A * Aᴴ) u) = specNorm (P * A) ^ 2 := by
  have hne : Nonempty m := by
    by_contra h
    have : P * A = 0 := by
      have := not_nonempty_iff.mp h
      exact Subsingleton.elim _ _
    rw [this, specNorm_zero] at h₀
    exact lt_irrefl _ h₀
  have hM : (P * A * (P * A)ᴴ).PosSemidef := Matrix.posSemidef_self_mul_conjTranspose _
  obtain ⟨u, hu, hMu⟩ := hM.exists_norm_eq_one_and_mulVec_eq_specNorm_smul
  rw [specNorm_mul_conjTranspose_self] at hMu
  have hMe : P * A * (P * A)ᴴ = Pᴴ * (A * Aᴴ) * P := by
    rw [Matrix.conjTranspose_mul, hP.conjTranspose_eq]
    simp only [Matrix.mul_assoc]
  have hPM : P * (P * A * (P * A)ᴴ) = P * A * (P * A)ᴴ := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hP.mul_self]
  have hc : (specNorm (P * A) ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 h₀.ne'
  have hPu : P *ᵥ u = u := by
    have h := congrArg (fun M => M *ᵥ u) hPM
    simp only [← Matrix.mulVec_mulVec, hMu, Matrix.mulVec_smul] at h
    exact smul_right_injective _ hc h
  refine ⟨u, hu, hPu, ?_⟩
  rw [← re_quadForm_of_mulVec_eq_smul hu hMu, hMe, quadForm_conjTranspose_mul_mul, hPu]

end NLAlib
