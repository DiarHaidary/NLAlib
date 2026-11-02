/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.LeastSquares

/-!
# Regularized least squares

One objective and inverse operator cover identity and general matrix penalties.
Ordinary least squares for the augmented matrix supplies their normal equations.
Proof material adapted from `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`, `NLAlib/Matrix/Basic/GeneralTikhonov.lean`;
the present proofs instead reuse the existing least-squares interface.

## Main results

* `NLAlib.isMinOn_tikhonovObjective_iff_normal_equations`: the regularized normal equations.
* `NLAlib.isMinOn_tikhonovObjective`: the canonical inverse gives a minimizer.
* `NLAlib.isMinOn_tikhonovObjective_iff_exists`: all minimizers, including a common kernel.
* `NLAlib.existsUnique_isMinOn_tikhonovObjective_iff`: the exact uniqueness criterion.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p]

/-- Squared data residual plus a squared matrix penalty,
$\|\mathbf{b}-\mathbf{A}\mathbf{x}\|^2+\beta\|\mathbf{L}\mathbf{x}\|^2$.
The definition is total for every real parameter; minimization results assume nonnegativity.
The identity penalty gives standard Tikhonov regularization. -/
noncomputable def tikhonovObjective (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) (β : ℝ) (x : n → 𝕜) : ℝ :=
  ‖WithLp.toLp 2 (b - A *ᵥ x)‖ ^ 2 + β * ‖WithLp.toLp 2 (L *ᵥ x)‖ ^ 2

/-- The canonical regularized inverse
$(\mathbf{A}^{\mathsf{H}}\mathbf{A}+\beta\mathbf{L}^{\mathsf{H}}\mathbf{L})^+
\mathbf{A}^{\mathsf{H}}$. It is total at every rank and parameter. For nonnegative parameters
it returns the minimum-norm minimizer of the squared-residual objective. At zero it is
$\mathbf{A}^+$; for negative parameters no minimization interpretation is asserted. -/
noncomputable def tikhonovInverse (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (β : ℝ) : Matrix n m 𝕜 :=
  pinv (Aᴴ * A + β • (Lᴴ * L)) * Aᴴ

private theorem augmented_objective (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 ≤ β) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (Sum.elim b 0 - Matrix.fromRows A (Real.sqrt β • L) *ᵥ x)‖ ^ 2 =
      tikhonovObjective A L b β x := by
  have he : Sum.elim b 0 - Matrix.fromRows A (Real.sqrt β • L) *ᵥ x =
      Sum.elim (b - A *ᵥ x) (-(Real.sqrt β • (L *ᵥ x))) := by
    ext i
    cases i <;> simp [Matrix.fromRows_mulVec, Matrix.smul_mulVec]
  rw [he, EuclideanSpace.norm_toLp_sumElim_sq, WithLp.toLp_neg, norm_neg,
    WithLp.toLp_smul, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt hβ]
  rfl

omit [Fintype n] in
private theorem augmented_gram (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    {β : ℝ} (hβ : 0 ≤ β) :
    (Matrix.fromRows A (Real.sqrt β • L))ᴴ * Matrix.fromRows A (Real.sqrt β • L) =
      Aᴴ * A + β • (Lᴴ * L) := by
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mul_fromRows, Matrix.conjTranspose_smul, star_trivial,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two, Real.sq_sqrt hβ]

omit [Fintype n] in
private theorem augmented_rhs (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) (β : ℝ) :
    (Matrix.fromRows A (Real.sqrt β • L))ᴴ *ᵥ Sum.elim b 0 = Aᴴ *ᵥ b := by
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.fromCols_mulVec_sumElim, Matrix.mulVec_zero, add_zero]

/-- The regularized objective is ordinary least squares for the augmented data
$[\mathbf{A};\sqrt\beta\mathbf{L}]$ and $[\mathbf{b};\mathbf{0}]$, for $\beta\ge0$.
This bridge includes zero parameters and rank-deficient penalties. -/
theorem isMinOn_tikhonovObjective_iff_isLeastSquaresSolution
    (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) (b : m → 𝕜) {β : ℝ} (hβ : 0 ≤ β)
    {x : n → 𝕜} :
    IsMinOn (tikhonovObjective A L b β) Set.univ x ↔
      IsLeastSquaresSolution (Matrix.fromRows A (Real.sqrt β • L)) (Sum.elim b 0) x := by
  rw [isMinOn_univ_iff, isLeastSquaresSolution_iff]
  apply forall_congr'
  intro y
  rw [← augmented_objective A L b hβ x, ← augmented_objective A L b hβ y]
  exact sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)

/-- **Regularized normal equations.** For arbitrary real or complex rectangular data and
penalty matrices and $\beta\ge0$, a vector minimizes
$\|\mathbf{b}-\mathbf{A}\mathbf{x}\|^2+\beta\|\mathbf{L}\mathbf{x}\|^2$ exactly when
$$(\mathbf{A}^{\mathsf{H}}\mathbf{A}+\beta\mathbf{L}^{\mathsf{H}}\mathbf{L})\mathbf{x}
  =\mathbf{A}^{\mathsf{H}}\mathbf{b}\,.$$
No rank assumption is needed. Derived here from the ordinary least-squares normal equations;
no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem isMinOn_tikhonovObjective_iff_normal_equations
    (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) (b : m → 𝕜) {β : ℝ} (hβ : 0 ≤ β)
    {x : n → 𝕜} :
    IsMinOn (tikhonovObjective A L b β) Set.univ x ↔
      (Aᴴ * A + β • (Lᴴ * L)) *ᵥ x = Aᴴ *ᵥ b := by
  rw [isMinOn_tikhonovObjective_iff_isLeastSquaresSolution A L b hβ,
    isLeastSquaresSolution_iff_normal_equations, Matrix.mulVec_mulVec,
    augmented_gram A L hβ, augmented_rhs]

private theorem augmented_pinv (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 ≤ β) :
    pinv (Matrix.fromRows A (Real.sqrt β • L)) *ᵥ Sum.elim b 0 =
      tikhonovInverse A L β *ᵥ b := by
  rw [pinv_eq_pinv_conjTranspose_mul_self_mul, augmented_gram A L hβ,
    ← Matrix.mulVec_mulVec, augmented_rhs, Matrix.mulVec_mulVec]
  rfl

/-- **The canonical Tikhonov minimizer.** For any data matrix, penalty matrix and
$\beta\ge0$, applying the regularized inverse to the data minimizes the squared data residual
plus $\beta$ times the squared penalty. Empty dimensions and common kernels are allowed.
Derived here from the pseudoinverse solution of the augmented least-squares problem;
no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem isMinOn_tikhonovObjective (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 ≤ β) :
    IsMinOn (tikhonovObjective A L b β) Set.univ (tikhonovInverse A L β *ᵥ b) := by
  rw [isMinOn_tikhonovObjective_iff_isLeastSquaresSolution A L b hβ,
    ← augmented_pinv A L b hβ]
  exact isLeastSquaresSolution_pinv_mulVec _ _

/-- At parameter zero the regularized inverse is the Moore–Penrose inverse, independently
of the penalty. This is a value of the total definition, not an assertion about a general
penalty's limit from positive parameters. -/
theorem tikhonovInverse_zero (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) :
    tikhonovInverse A L 0 = pinv A := by
  simp only [tikhonovInverse, zero_smul, add_zero, ← pinv_eq_pinv_conjTranspose_mul_self_mul]

/-- The canonical regularized inverse selects the minimum-norm minimizer, even when data
and penalty matrices share a nontrivial kernel. -/
theorem norm_tikhonovInverse_mulVec_le (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 ≤ β) {x : n → 𝕜}
    (hx : IsMinOn (tikhonovObjective A L b β) Set.univ x) :
    ‖WithLp.toLp 2 (tikhonovInverse A L β *ᵥ b)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  rw [← augmented_pinv A L b hβ]
  exact ((isMinOn_tikhonovObjective_iff_isLeastSquaresSolution A L b hβ).mp hx).norm_pinv_mulVec_le

omit [Fintype m] [Fintype p] in
private theorem augmented_mulVec_eq_zero_iff (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    {β : ℝ} (hβ : 0 < β) (v : n → 𝕜) :
    Matrix.fromRows A (Real.sqrt β • L) *ᵥ v = 0 ↔ A *ᵥ v = 0 ∧ L *ᵥ v = 0 := by
  rw [Matrix.fromRows_mulVec, Matrix.smul_mulVec]
  constructor
  · intro hv
    refine ⟨funext fun i => congrFun hv (Sum.inl i), ?_⟩
    have hL : Real.sqrt β • (L *ᵥ v) = 0 := funext fun i => congrFun hv (Sum.inr i)
    exact (smul_eq_zero.mp hL).resolve_left (Real.sqrt_pos.mpr hβ).ne'
  · rintro ⟨hA, hL⟩
    ext i
    cases i <;> simp [hA, hL]

/-- **All general-form Tikhonov minimizers.** For real or complex rectangular matrices and
$\beta>0$, every minimizer is the canonical regularized inverse applied to the data plus
a vector in $\ker\mathbf{A}\cap\ker\mathbf{L}$, and every such vector is a minimizer.
Empty dimensions and deficient stacked rank are included. Derived here from augmented
least squares; no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem isMinOn_tikhonovObjective_iff_exists (A : Matrix m n 𝕜) (L : Matrix p n 𝕜)
    (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) {x : n → 𝕜} :
    IsMinOn (tikhonovObjective A L b β) Set.univ x ↔
      ∃ v, v ∈ LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin ∧
        x = tikhonovInverse A L β *ᵥ b + v := by
  have hmin := isMinOn_tikhonovObjective A L b hβ.le
  constructor
  · intro hx
    have he := ((isMinOn_tikhonovObjective_iff_isLeastSquaresSolution A L b hβ.le).mp hx).mulVec_eq
      ((isMinOn_tikhonovObjective_iff_isLeastSquaresSolution A L b hβ.le).mp hmin)
    have hz : Matrix.fromRows A (Real.sqrt β • L) *ᵥ
        (x - tikhonovInverse A L β *ᵥ b) = 0 := by
      rw [Matrix.mulVec_sub, he, sub_self]
    refine ⟨x - tikhonovInverse A L β *ᵥ b,
      (augmented_mulVec_eq_zero_iff A L hβ _).mp hz, ?_⟩
    exact (add_sub_cancel _ _).symm
  · rintro ⟨v, hv, rfl⟩
    rw [isMinOn_tikhonovObjective_iff_normal_equations A L b hβ.le] at hmin ⊢
    change A *ᵥ v = 0 ∧ L *ᵥ v = 0 at hv
    rw [Matrix.mulVec_add, hmin, Matrix.add_mulVec, Matrix.smul_mulVec,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hv.1, hv.2,
      Matrix.mulVec_zero, Matrix.mulVec_zero, smul_zero, add_zero, add_zero]

/-- **Uniqueness in general-form Tikhonov regularization.** For any data vector and
$\beta>0$, the squared-residual objective has exactly one minimizer if and only if
$\ker\mathbf{A}\cap\ker\mathbf{L}=\{\mathbf{0}\}$. Neither matrix individually needs
full column rank; empty dimensions are included. Derived here from augmented least squares;
no printed source for this formulation.
Result: general-form-tikhonov-gsvd -/
theorem existsUnique_isMinOn_tikhonovObjective_iff
    (A : Matrix m n 𝕜) (L : Matrix p n 𝕜) (b : m → 𝕜) {β : ℝ} (hβ : 0 < β) :
    (∃! x, IsMinOn (tikhonovObjective A L b β) Set.univ x) ↔
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥ := by
  simp_rw [isMinOn_tikhonovObjective_iff_isLeastSquaresSolution A L b hβ.le]
  rw [existsUnique_isLeastSquaresSolution_iff]
  have he : LinearMap.ker (Matrix.fromRows A (Real.sqrt β • L)).mulVecLin =
      LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin := by
    ext v
    exact augmented_mulVec_eq_zero_iff A L hβ v
  change Function.Injective (Matrix.fromRows A (Real.sqrt β • L)).mulVecLin ↔ _
  rw [← LinearMap.ker_eq_bot, he]

end NLAlib
