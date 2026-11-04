/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import NLAlib.Matrix.Spectral.LowRank

/-!
# Truncated-SVD regularization

The pseudoinverse of a retained positive block of any fixed SVD uniquely minimizes the
residual on the retained right singular space. The discarded bias and propagated noise are
orthogonal. The canonical `truncatedSVD` corollaries also include zero cutoff and zero rank.
No choice of a canonical subspace is asserted at a tied singular value.

## Main results

* `NLAlib.IsSVD.isMinOn_norm_sub_mulVec_pinv_mulVec`,
  `NLAlib.IsSVD.eq_pinv_mulVec_of_isMinOn`: constrained minimization and uniqueness.
* `NLAlib.IsSVD.norm_sub_pinv_mulVec_sq`: exact orthogonal bias/noise identity.
* `NLAlib.IsSVD.specNorm_pinv_of_fromCols`,
  `NLAlib.IsSVD.norm_sub_pinv_mulVec_sq_le_of_fromCols`: leading-block noise amplification.
* `NLAlib.isMinOn_norm_sub_mulVec_pinv_truncatedSVD_mulVec`,
  `NLAlib.eq_pinv_truncatedSVD_mulVec_of_isMinOn`,
  `NLAlib.norm_sub_pinv_truncatedSVD_mulVec_sq`: canonical truncation at every cutoff.
* `NLAlib.specNorm_pinv_truncatedSVD`,
  `NLAlib.norm_sub_pinv_truncatedSVD_mulVec_sq_le`: the sharp leading-cutoff bound.

The retained inverse formula and its arbitrary-family norm are already
`NLAlib.IsSVD.pinv_eq` and `NLAlib.IsSVD.specNorm_eq` applied to `NLAlib.IsSVD.pinv`.
Mathematical coverage follows `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730`,
`NLAlib/Matrix/Basic/TruncatedSVDRegularization.lean`, using the native SVD and pseudoinverse.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n r s : Type*}
  [Fintype m] [Fintype n] [Fintype r] [Fintype s]
  [DecidableEq r] [DecidableEq s]

private theorem pinv_mulVec_mem_range (B : Matrix m n 𝕜) (b : m → 𝕜) :
    NLAlib.pinv B *ᵥ b ∈ LinearMap.range Bᴴ.mulVecLin := by
  rw [← range_pinv]
  exact ⟨b, rfl⟩

private theorem mulVec_eq_of_mem_range {A B : Matrix m n 𝕜}
    (hAB : A * rangeProjector Bᴴ = B) {x : n → 𝕜}
    (hx : x ∈ LinearMap.range Bᴴ.mulVecLin) : A *ᵥ x = B *ᵥ x := by
  have hPx := rangeProjector_mulVec_eq_self_iff.mpr hx
  calc
    A *ᵥ x = A *ᵥ (rangeProjector Bᴴ *ᵥ x) := congrArg (A *ᵥ ·) hPx.symm
    _ = B *ᵥ x := by rw [Matrix.mulVec_mulVec, hAB]

private theorem isMinOn_norm_sub_mulVec_of_mul_rangeProjector {A B : Matrix m n 𝕜}
    (hAB : A * rangeProjector Bᴴ = B) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
      (LinearMap.range Bᴴ.mulVecLin) (NLAlib.pinv B *ᵥ b) := by
  rw [isMinOn_iff]
  intro x hx
  rw [mulVec_eq_of_mem_range hAB (pinv_mulVec_mem_range B b), mulVec_eq_of_mem_range hAB hx]
  exact isLeastSquaresSolution_pinv_mulVec B b x

private theorem eq_pinv_mulVec_of_isMinOn_range {A B : Matrix m n 𝕜}
    (hAB : A * rangeProjector Bᴴ = B) (b : m → 𝕜) {x : n → 𝕜}
    (hx : x ∈ LinearMap.range Bᴴ.mulVecLin)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.range Bᴴ.mulVecLin) x) : x = NLAlib.pinv B *ᵥ b := by
  have hls : IsLeastSquaresSolution B b x := by
    intro y
    have hy : rangeProjector Bᴴ *ᵥ y ∈ LinearMap.range Bᴴ.mulVecLin :=
      rangeProjector_mulVec_eq_self_iff.mp (by
        rw [Matrix.mulVec_mulVec, rangeProjector_mul_rangeProjector])
    have hh := isMinOn_iff.mp hmin _ hy
    rw [mulVec_eq_of_mem_range hAB hx, Matrix.mulVec_mulVec, hAB] at hh
    exact hh
  have he := hls.pinv_mulVec_mulVec
  rw [Matrix.mulVec_mulVec, pinv_mul, rangeProjector_mulVec_eq_self_iff.mpr hx] at he
  exact he

private theorem norm_sub_pinv_mulVec_sq_of_rangeProjector_mul [DecidableEq n]
    {A B : Matrix m n 𝕜}
    (hBA : rangeProjector B * A = B) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - NLAlib.pinv B *ᵥ (A *ᵥ x + e))‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - rangeProjector Bᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 (NLAlib.pinv B *ᵥ e)‖ ^ 2 := by
  have hPB : rangeProjector Bᴴ * NLAlib.pinv B = NLAlib.pinv B := by
    rw [← pinv_mul, pinv_mul_mul_pinv]
  have hBA' : NLAlib.pinv B * A = rangeProjector Bᴴ := by
    calc
      NLAlib.pinv B * A = NLAlib.pinv B * (rangeProjector B * A) := by
        rw [← mul_pinv]
        simp only [← Matrix.mul_assoc, pinv_mul_mul_pinv]
      _ = rangeProjector Bᴴ := by rw [hBA, pinv_mul]
  have hQ : (1 - rangeProjector Bᴴ) * NLAlib.pinv B = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPB, sub_self]
  have hP : rangeProjector Bᴴ *ᵥ (x - NLAlib.pinv B *ᵥ (A *ᵥ x + e)) =
      -(NLAlib.pinv B *ᵥ e) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hPB, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, hBA']
    abel
  have hQx : (1 - rangeProjector Bᴴ) *ᵥ (x - NLAlib.pinv B *ᵥ (A *ᵥ x + e)) =
      (1 - rangeProjector Bᴴ) *ᵥ x := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hQ, Matrix.zero_mulVec, sub_zero]
  rw [norm_toLp_sq_eq_add_one_sub_rangeProjector Bᴴ, hP, hQx,
    WithLp.toLp_neg, norm_neg, add_comm]

section Retained

variable {A : Matrix m n 𝕜} {U₁ : Matrix m r 𝕜} {U₂ : Matrix m s 𝕜}
  {V₁ : Matrix n r 𝕜} {V₂ : Matrix n s 𝕜} {σ₁ : r → ℝ} {σ₂ : s → ℝ}

private theorem IsSVD.mul_mul_conjTranspose_eq_left
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) :
    A * (V₁ * V₁ᴴ) = U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ := by
  have hV := hasOrthonormalCols_fromCols_iff.mp h.hasOrthonormalCols_right
  have h21 : V₂ᴴ * V₁ = 0 := by
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_zero] using congrArg Matrix.conjTranspose hV.2.2
  rw [h.eq_add, Matrix.add_mul, Matrix.mul_assoc _ V₁ᴴ, ← Matrix.mul_assoc V₁ᴴ,
    hV.1.conjTranspose_mul_self, Matrix.one_mul,
    Matrix.mul_assoc _ V₂ᴴ, ← Matrix.mul_assoc V₂ᴴ, h21,
    Matrix.zero_mul, Matrix.mul_zero, add_zero]

private theorem IsSVD.rangeProjector_left_mul
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i) :
    rangeProjector (U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ) * A =
      U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ := by
  have hB := h.fromCols_left
  have hp := hB.conjTranspose.rangeProjector_conjTranspose_eq hσ
  rw [Matrix.conjTranspose_conjTranspose] at hp
  rw [hp]
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_diagonal_ofReal, Matrix.mul_assoc] using
    congrArg Matrix.conjTranspose h.conjTranspose.mul_mul_conjTranspose_eq_left

private theorem IsSVD.range_left_conjTranspose
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i) :
    LinearMap.range (U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ)ᴴ.mulVecLin =
      LinearMap.range V₁.mulVecLin := by
  apply rangeProjector_inj.mp
  rw [h.fromCols_left.rangeProjector_conjTranspose_eq hσ,
    h.fromCols_left.hasOrthonormalCols_right.rangeProjector_eq]

/-- **Truncated-SVD regularization.** For a fixed SVD split into retained and discarded blocks,
with positive retained singular values, the retained pseudoinverse minimizes
$\|\mathbf{b}-\mathbf{A}\mathbf{x}\|$ on the range of the retained right factor
$\mathbf{V}_1$. The retained block may be empty and need not be leading or sorted.
[FesslerNadakuditi2024, §§5.6.1–5.6.4]; here for arbitrary retained positive coordinates.
Result: truncated-svd-regularization -/
theorem IsSVD.isMinOn_norm_sub_mulVec_pinv_mulVec
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
      (LinearMap.range V₁.mulVecLin)
      (NLAlib.pinv (U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ) *ᵥ b) := by
  rw [← h.range_left_conjTranspose hσ]
  apply isMinOn_norm_sub_mulVec_of_mul_rangeProjector
  rw [h.fromCols_left.rangeProjector_conjTranspose_eq hσ]
  exact h.mul_mul_conjTranspose_eq_left

/-- **Uniqueness of restricted least squares.** For a fixed split SVD whose retained singular
values are positive, every residual minimizer in the retained right singular space equals
the retained pseudoinverse solution. Empty retained spaces are included.
[FesslerNadakuditi2024, §§5.6.1–5.6.4].
Result: truncated-svd-regularization -/
theorem IsSVD.eq_pinv_mulVec_of_isMinOn
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i) (b : m → 𝕜)
    {x : n → 𝕜} (hx : x ∈ LinearMap.range V₁.mulVecLin)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.range V₁.mulVecLin) x) :
    x = NLAlib.pinv (U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ) *ᵥ b := by
  rw [← h.range_left_conjTranspose hσ] at hx hmin
  apply eq_pinv_mulVec_of_isMinOn_range _ b hx hmin
  rw [h.fromCols_left.rangeProjector_conjTranspose_eq hσ]
  exact h.mul_mul_conjTranspose_eq_left

/-- **Orthogonal bias and noise.** For a fixed split SVD with positive retained singular
values, put $\mathbf{B}=\mathbf{U}_1\mathbf{\Sigma}_1\mathbf{V}_1^{\mathsf{H}}$.
For arbitrary data $\mathbf{A}\mathbf{x}+\mathbf{e}$,
$$\|\mathbf{x}-\mathbf{B}^{+}(\mathbf{A}\mathbf{x}+\mathbf{e})\|^2 =
\|(\mathbf{I}-\mathbf{V}_1\mathbf{V}_1^{\mathsf{H}})\mathbf{x}\|^2+
\|\mathbf{B}^{+}\mathbf{e}\|^2.$$
The retained block may be empty or unsorted.
[FesslerNadakuditi2024, (5.42)]; the squared identity follows from orthogonality.
Result: truncated-svd-regularization -/
theorem IsSVD.norm_sub_pinv_mulVec_sq [DecidableEq n]
    (h : IsSVD A (Matrix.fromCols U₁ U₂) (Sum.elim σ₁ σ₂)
      (Matrix.fromCols V₁ V₂)) (hσ : ∀ i, 0 < σ₁ i) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - NLAlib.pinv (U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ) *ᵥ
      (A *ᵥ x + e))‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - V₁ * V₁ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2
          (NLAlib.pinv (U₁ * Matrix.diagonal (fun i => (σ₁ i : 𝕜)) * V₁ᴴ) *ᵥ e)‖ ^ 2 := by
  rw [norm_sub_pinv_mulVec_sq_of_rangeProjector_mul (h.rangeProjector_left_mul hσ),
    h.fromCols_left.rangeProjector_conjTranspose_eq hσ]

end Retained

section Leading

variable {k : ℕ} {A : Matrix m n 𝕜} {U₁ : Matrix m (Fin (k + 1)) 𝕜}
  {U₂ : Matrix m s 𝕜} {V₁ : Matrix n (Fin (k + 1)) 𝕜} {V₂ : Matrix n s 𝕜}
  {σ₂ : s → ℝ}

/-- **The retained inverse norm.** If the first block of a fixed SVD consists of the leading
$k+1$ positive singular values, its pseudoinverse has norm $\sigma_k(\mathbf{A})^{-1}$,
with singular values indexed from zero. Ties at the cutoff are allowed.
[FesslerNadakuditi2024, (5.43)].
Result: truncated-svd-regularization -/
theorem IsSVD.specNorm_pinv_of_fromCols
    (h : IsSVD A (Matrix.fromCols U₁ U₂)
      (Sum.elim (fun i : Fin (k + 1) => singularValues A i) σ₂)
      (Matrix.fromCols V₁ V₂)) (hk : k + 1 ≤ A.rank) :
    specNorm (NLAlib.pinv (U₁ * Matrix.diagonal
      (fun i : Fin (k + 1) => (singularValues A i : 𝕜)) * V₁ᴴ)) =
      (singularValues A k)⁻¹ := by
  rw [h.fromCols_left.pinv.specNorm_eq]
  have hpos : 0 < singularValues A k := (singularValues_pos_iff A).mpr (by omega)
  apply le_antisymm
  · apply (pi_norm_le_iff_of_nonneg (inv_nonneg.mpr hpos.le)).mpr
    intro i
    rw [Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (singularValues_nonneg A i))]
    exact inv_anti₀ hpos (singularValues_antitone A (by omega))
  · have hl := norm_le_pi_norm (fun i : Fin (k + 1) => (singularValues A i)⁻¹)
      (Fin.last k)
    simpa only [Fin.val_last, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos)] using hl

/-- **Deterministic TSVD error bound.** For a fixed SVD retaining its leading $k+1$ positive
singular values and $\mathbf{B}=\mathbf{U}_1\mathbf{\Sigma}_1\mathbf{V}_1^{\mathsf{H}}$,
$$\|\mathbf{x}-\mathbf{B}^{+}(\mathbf{A}\mathbf{x}+\mathbf{e})\|^2 \le
\|(\mathbf{I}-\mathbf{V}_1\mathbf{V}_1^{\mathsf{H}})\mathbf{x}\|^2+
\frac{\|\mathbf{e}\|^2}{\sigma_k(\mathbf{A})^2}.$$
Singular values are indexed from zero and ties are allowed.
[FesslerNadakuditi2024, (5.42)–(5.43)]; orthogonality yields the squared form.
Result: truncated-svd-regularization -/
theorem IsSVD.norm_sub_pinv_mulVec_sq_le_of_fromCols [DecidableEq n]
    (h : IsSVD A (Matrix.fromCols U₁ U₂)
      (Sum.elim (fun i : Fin (k + 1) => singularValues A i) σ₂)
      (Matrix.fromCols V₁ V₂)) (hk : k + 1 ≤ A.rank) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - NLAlib.pinv (U₁ * Matrix.diagonal
      (fun i : Fin (k + 1) => (singularValues A i : 𝕜)) * V₁ᴴ) *ᵥ
        (A *ᵥ x + e))‖ ^ 2 ≤
      ‖WithLp.toLp 2 ((1 - V₁ * V₁ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 e‖ ^ 2 / singularValues A k ^ 2 := by
  rw [h.norm_sub_pinv_mulVec_sq (fun i => (singularValues_pos_iff A).mpr (by omega))]
  apply add_le_add_right
  have hb := norm_toLp_mulVec_le
    (NLAlib.pinv (U₁ * Matrix.diagonal (fun i : Fin (k + 1) =>
      (singularValues A i : 𝕜)) * V₁ᴴ)) e
  rw [h.specNorm_pinv_of_fromCols hk] at hb
  simpa only [mul_pow, inv_pow, div_eq_mul_inv, mul_comm] using
    pow_le_pow_left₀ (norm_nonneg _) hb 2

end Leading

/-! ### The chosen truncation, including zero rank and zero cutoff -/

/-- **Canonical TSVD restricted least squares.** At every cutoff $k$, the pseudoinverse of
$\llbracket\mathbf{A}\rrbracket_k$ minimizes the original residual on the row space of that
truncation. Zero cutoff, zero rank and empty matrix dimensions are included.
[FesslerNadakuditi2024, §§5.6.1–5.6.4].
Result: truncated-svd-regularization -/
theorem isMinOn_norm_sub_mulVec_pinv_truncatedSVD_mulVec
    (A : Matrix m n 𝕜) (k : ℕ) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
      (LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin)
      (NLAlib.pinv (truncatedSVD A k) *ᵥ b) := by
  exact isMinOn_norm_sub_mulVec_of_mul_rangeProjector
    (mul_rangeProjector_conjTranspose_truncatedSVD A k) b

/-- **Canonical TSVD uniqueness.** At every cutoff, every residual minimizer in the row space
of $\llbracket\mathbf{A}\rrbracket_k$ is its pseudoinverse solution. At zero cutoff or zero
rank this space is zero, so uniqueness is retained.
[FesslerNadakuditi2024, §§5.6.1–5.6.4].
Result: truncated-svd-regularization -/
theorem eq_pinv_truncatedSVD_mulVec_of_isMinOn
    (A : Matrix m n 𝕜) (k : ℕ) (b : m → 𝕜) {x : n → 𝕜}
    (hx : x ∈ LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.range (truncatedSVD A k)ᴴ.mulVecLin) x) :
    x = NLAlib.pinv (truncatedSVD A k) *ᵥ b := by
  exact eq_pinv_mulVec_of_isMinOn_range
    (mul_rangeProjector_conjTranspose_truncatedSVD A k) b hx hmin

/-- **Canonical TSVD bias and noise.** At every cutoff, put
$\mathbf{B}=\llbracket\mathbf{A}\rrbracket_k$. For any signal and noise,
$$\|\mathbf{x}-\mathbf{B}^{+}(\mathbf{A}\mathbf{x}+\mathbf{e})\|^2 =
\|(\mathbf{I}-\mathbf{P}_{\mathbf{B}^{\mathsf{H}}})\mathbf{x}\|^2+
\|\mathbf{B}^{+}\mathbf{e}\|^2.$$
Zero rank, zero cutoff and empty dimensions are included.
[FesslerNadakuditi2024, (5.42)]; orthogonality yields the exact squared form.
Result: truncated-svd-regularization -/
theorem norm_sub_pinv_truncatedSVD_mulVec_sq [DecidableEq n]
    (A : Matrix m n 𝕜) (k : ℕ) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - NLAlib.pinv (truncatedSVD A k) *ᵥ (A *ᵥ x + e))‖ ^ 2 =
      ‖WithLp.toLp 2 ((1 - rangeProjector (truncatedSVD A k)ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 (NLAlib.pinv (truncatedSVD A k) *ᵥ e)‖ ^ 2 := by
  exact norm_sub_pinv_mulVec_sq_of_rangeProjector_mul
    (rangeProjector_truncatedSVD_mul A k) x e

/-- **Canonical TSVD inverse norm.** For $k+1\le\operatorname{rank}\mathbf{A}$,
$\|\llbracket\mathbf{A}\rrbracket_{k+1}^{+}\|_2=\sigma_k(\mathbf{A})^{-1}$,
singular values indexed from zero.
[FesslerNadakuditi2024, (5.43)].
Result: truncated-svd-regularization -/
theorem specNorm_pinv_truncatedSVD (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 ≤ A.rank) :
    specNorm (NLAlib.pinv (truncatedSVD A (k + 1))) = (singularValues A k)⁻¹ := by
  rw [specNorm_pinv _ (by rw [rank_truncatedSVD, min_eq_left hk]),
    singularValues_truncatedSVD, if_pos (by omega)]

/-- **Canonical deterministic TSVD error bound.** For $k+1\le\operatorname{rank}\mathbf{A}$,
put $\mathbf{B}=\llbracket\mathbf{A}\rrbracket_{k+1}$. Then
$$\|\mathbf{x}-\mathbf{B}^{+}(\mathbf{A}\mathbf{x}+\mathbf{e})\|^2 \le
\|(\mathbf{I}-\mathbf{P}_{\mathbf{B}^{\mathsf{H}}})\mathbf{x}\|^2+
\frac{\|\mathbf{e}\|^2}{\sigma_k(\mathbf{A})^2}.$$
Singular values are indexed from zero and ties at the cutoff are allowed.
[FesslerNadakuditi2024, (5.42)–(5.43)]; orthogonality gives the squared form.
Result: truncated-svd-regularization -/
theorem norm_sub_pinv_truncatedSVD_mulVec_sq_le [DecidableEq n]
    (A : Matrix m n 𝕜) {k : ℕ}
    (hk : k + 1 ≤ A.rank) (x : n → 𝕜) (e : m → 𝕜) :
    ‖WithLp.toLp 2 (x - NLAlib.pinv (truncatedSVD A (k + 1)) *ᵥ (A *ᵥ x + e))‖ ^ 2 ≤
      ‖WithLp.toLp 2 ((1 - rangeProjector (truncatedSVD A (k + 1))ᴴ) *ᵥ x)‖ ^ 2 +
        ‖WithLp.toLp 2 e‖ ^ 2 / singularValues A k ^ 2 := by
  rw [norm_sub_pinv_truncatedSVD_mulVec_sq]
  apply add_le_add_right
  have hb := norm_toLp_mulVec_le (NLAlib.pinv (truncatedSVD A (k + 1))) e
  rw [specNorm_pinv_truncatedSVD A hk] at hb
  simpa only [mul_pow, inv_pow, div_eq_mul_inv, mul_comm] using
    pow_le_pow_left₀ (norm_nonneg _) hb 2

end NLAlib
