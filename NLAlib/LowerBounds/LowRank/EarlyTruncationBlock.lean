/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.SketchedLowRank
public import NLAlib.Matrix.Norms.Nuclear

/-!
# The early-truncated randomized SVD on the block instance: the deterministic step

For $\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, s\mathbf{I}_k)$ with $0 \le s \le 1$ and a test
matrix $\mathbf{\Omega} = [\mathbf{\Omega}_1; \mathbf{\Omega}_2]$, the error of the early-truncated
randomized SVD $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$
(`NLAlib.earlyTruncatedRSVD`) is controlled by the tail content $T$ of the dominant $k$-frame of
the sketch: it is at least $ks^2 + (1 - s^2)T$, and a variational inequality (Ky Fan maximality of
the truncated SVD against a rotated competitor frame) bounds $T$ from below by the blocks of
$\mathbf{\Omega}$. Deterministic.

This is the linear-algebra step of the general-$k$ lower bound; the Gaussian concentration and the
expectation bound are in `NLAlib.LowerBounds.LowRank.EarlyTruncationBlockGaussian`, the
$k = 1$ instance in `NLAlib.LowerBounds.LowRank.EarlyTruncation`. New (research note
`reports/OP1-EarlyTruncatedRSVD.md` of the NLAlib workflow, 2026-10-25). Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.1. Real throughout.

## Main results

* `NLAlib.frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational`: the error bound by
  the tail content, and the variational inequality.
-/

@[expose] public section

open Matrix
open scoped Matrix

namespace NLAlib

variable {l : Type*} [Fintype l]

/-- A real Frobenius norm squared is the trace of $\mathbf{A}\mathbf{A}^{\mathsf{T}}$. -/
private theorem frobNorm_sq_eq_trace_mul_conjTranspose {m n : Type*} [Fintype m] [Fintype n]
    (A : Matrix m n ℝ) : frobNorm A ^ 2 = (A * Aᴴ).trace := by
  rw [frobNorm_sq_eq_re_trace, RCLike.re_to_real, Matrix.trace_mul_comm]

/-- The two frame blocks carry the trace of the frame:
$\operatorname{tr}\mathbf{U}_h\mathbf{U}_h^{\mathsf{H}} +
\operatorname{tr}\mathbf{U}_t\mathbf{U}_t^{\mathsf{H}} = k$ for orthonormal $k$ columns. -/
private theorem trace_toRows_mul_conjTranspose_add {k : ℕ} {U : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ}
    (hU : HasOrthonormalCols U) :
    (U.toRows₁ * U.toRows₁ᴴ).trace + (U.toRows₂ * U.toRows₂ᴴ).trace = k := by
  have h1 : (U * Uᴴ).trace = k := by
    rw [Matrix.trace_mul_comm, HasOrthonormalCols.conjTranspose_mul_self hU, Matrix.trace_one,
      Fintype.card_fin]
  have h2 : (U * Uᴴ).trace =
      (U.toRows₁ * U.toRows₁ᴴ).trace + (U.toRows₂ * U.toRows₂ᴴ).trace := by
    simp [Matrix.trace, Fintype.sum_sum_type, Matrix.mul_apply, Matrix.toRows₁, Matrix.toRows₂]
  rw [← h2, h1]

/-- The tail of the head block of a frame:
$\|\mathbf{U}_h^{\mathsf{T}}\mathbf{\Omega}_1\|_{\mathsf{F}}^2
\le \|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2 T$ when
$\operatorname{tr}\mathbf{U}_h\mathbf{U}_h^{\mathsf{T}} = k - T$, from
$\mathbf{I} - \mathbf{U}_h\mathbf{U}_h^{\mathsf{T}} \succeq 0$ and
$\mathbf{\Omega}_1\mathbf{\Omega}_1^{\mathsf{T}} \succeq \sigma_{k-1}^2 \mathbf{I}$. -/
private theorem frobNorm_conjTranspose_mul_sq_le_of_posSemidef {k : ℕ} {l : Type*} [Fintype l]
    (Ω : Matrix (Fin k) l ℝ) (Uh : Matrix (Fin k) (Fin k) ℝ)
    (hPSD : (1 - Uh * Uhᴴ).PosSemidef) (T : ℝ) (hT : (Uh * Uhᴴ).trace = k - T) :
    frobNorm (Uhᴴ * Ω) ^ 2 ≤ frobNorm Ω ^ 2 - singularValues Ω (k - 1) ^ 2 * T := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hT0 : T = 0 := by simpa using hT.symm
    rw [hT0, mul_zero, sub_zero, frobNorm_sq_eq_sum]
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    exact (sq_nonneg _).trans_eq' (by simp) |>.trans_eq' rfl
  have hG : (Ω * Ωᴴ - singularValues Ω (k - 1) ^ 2 • (1 : Matrix (Fin k) (Fin k) ℝ)).PosSemidef :=
    by
    have h := (Matrix.isHermitian_mul_conjTranspose_self Ω).eigenvalue_last_smul_one_le
      (k := k - 1) (by simp; omega)
    rw [singularValues_sq_eq_eigenvalue_mul_conjTranspose_self]
    exact Matrix.le_iff.mp h
  have htr := hPSD.trace_mul_nonneg hG
  have e1 : frobNorm (Uhᴴ * Ω) ^ 2 = ((Uh * Uhᴴ) * (Ω * Ωᴴ)).trace := by
    rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [Matrix.trace_mul_comm]
    simp only [← Matrix.mul_assoc, RCLike.re_to_real]
  have e2 := frobNorm_sq_eq_trace_mul_conjTranspose Ω
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, smul_eq_mul, hT, Fintype.card_fin]
    at htr e1 e2 ⊢
  have h3 : singularValues Ω (k - 1) ^ 2 * ((k : ℝ) - ((k : ℝ) - T)) =
      singularValues Ω (k - 1) ^ 2 * T := by ring
  linarith

/-- A frame of the dominant $k$-dimensional range: $\mathbf{P}_{\llbracket \mathbf{Y}\rrbracket_k} =
\mathbf{U}\mathbf{U}^{\mathsf{H}}$ with $\mathbf{U}$ having orthonormal columns, when
$\operatorname{rank}\mathbf{Y} \ge k$. -/
private theorem exists_hasOrthonormalCols_rangeProjector_truncatedSVD_eq {n l : Type*}
    [Fintype n] [Fintype l] (Y : Matrix n l ℝ) (k : ℕ) (hr : k ≤ Y.rank) :
    ∃ U : Matrix n (Fin k) ℝ, HasOrthonormalCols U ∧
      rangeProjector (truncatedSVD Y k) = U * Uᴴ := by
  obtain ⟨U, hU, hrange⟩ := exists_hasOrthonormalCols_range_eq (truncatedSVD Y k) (p := Fin k)
    (by rw [rank_truncatedSVD, min_eq_left hr]; simp)
  refine ⟨U, hU, ?_⟩
  rw [← hU.rangeProjector_eq]
  exact rangeProjector_inj.mpr hrange.symm

/-- The block form of $\mathbf{V}^{\mathsf{H}}\mathbf{D}\mathbf{\Omega}$ for the diagonal weight
$\mathbf{D} = \operatorname{diag}(\mathbf{I}, s\mathbf{I})$:
$\mathbf{V}^{\mathsf{H}}\mathbf{D}\mathbf{\Omega} = \mathbf{V}_1^{\mathsf{H}}\mathbf{\Omega}_1 +
s\,\mathbf{V}_2^{\mathsf{H}}\mathbf{\Omega}_2$. -/
private theorem conjTranspose_mul_diagonal_mul_eq_toRows {k : ℕ} {l : Type*} (s : ℝ)
    (V : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) (Ω : Matrix (Fin k ⊕ Fin k) l ℝ) :
    Vᴴ * (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω) =
      V.toRows₁ᴴ * Ω.toRows₁ + s • (V.toRows₂ᴴ * Ω.toRows₂) := by
  ext i j
  rw [← Matrix.mul_assoc, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal]
  simp only [Fintype.sum_sum_type, Matrix.mul_apply, Matrix.add_apply,
    Matrix.smul_apply, Matrix.toRows₁, Matrix.toRows₂, Matrix.conjTranspose_apply,
    Sum.elim_inl, Sum.elim_inr, smul_eq_mul, Matrix.of_apply, Finset.mul_sum]
  congr 1 <;> refine Finset.sum_congr rfl fun x _ => ?_ <;> ring

/-- An orthogonal matrix that realises the nuclear norm against the second block:
$\langle \mathbf{R}\mathbf{\Omega}_1, \mathbf{\Omega}_2\rangle_{\mathsf{F}} =
\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_*$, from an SVD of
$\mathbf{\Omega}_2\mathbf{\Omega}_1^{\mathsf{T}}$. -/
private theorem exists_orthogonal_frobInner_eq_nuclearNorm {k : ℕ} {l : Type*} [Fintype l]
    (Ω₁ Ω₂ : Matrix (Fin k) l ℝ) :
    ∃ R : Matrix (Fin k) (Fin k) ℝ, Rᴴ * R = 1 ∧
      frobInner Ω₁ (Rᴴ * Ω₂) = nuclearNorm (Ω₁ * Ω₂ᴴ) := by
  obtain ⟨Us, Vs, hS⟩ := exists_isSVD (Ω₂ * Ω₁ᴴ) (k := k)
    (by simpa using (Ω₂ * Ω₁ᴴ).rank_le_card_height) (by simp) (by simp)
  have hUU : Usᴴ * Us = 1 := hS.hasOrthonormalCols_left
  have hVV : Vsᴴ * Vs = 1 := hS.hasOrthonormalCols_right
  have hVV' : Vs * Vsᴴ = 1 := mul_eq_one_comm.mp hVV
  refine ⟨Us * Vsᴴ, ?_, ?_⟩
  · simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Usᴴ, hUU, Matrix.one_mul, hVV']
  · have hN : nuclearNorm (Ω₁ * Ω₂ᴴ) = ∑ i : Fin k, singularValues (Ω₂ * Ω₁ᴴ) (i : ℕ) := by
      rw [← nuclearNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      exact hS.nuclearNorm_eq_sum
    rw [hN, ← frobInner_mul_left, frobInner_eq_re_trace, RCLike.re_to_real]
    have t1 : ((Us * Vsᴴ * Ω₁)ᴴ * Ω₂).trace = (Vs * (Usᴴ * (Ω₂ * Ω₁ᴴ))).trace := by
      simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      rw [Matrix.trace_mul_comm]
      simp only [Matrix.mul_assoc]
    have t2 : Usᴴ * (Ω₂ * Ω₁ᴴ) =
        Matrix.diagonal (fun i : Fin k => singularValues (Ω₂ * Ω₁ᴴ) (i : ℕ)) * Vsᴴ := by
      conv_lhs => rw [hS.eq]
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Usᴴ Us, hUU, Matrix.one_mul]
      rfl
    rw [t1, t2, Matrix.trace_mul_comm, Matrix.mul_assoc, hVV, Matrix.mul_one, Matrix.trace_diagonal]

/-- The cross term of two frame blocks: $|\langle \mathbf{U}_h^{\mathsf{T}}\mathbf{\Omega}_1,
\mathbf{U}_t^{\mathsf{T}}\mathbf{\Omega}_2\rangle_{\mathsf{F}}| \le
\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{k\|\mathbf{U}_t\|_{\mathsf{F}}^2}$
when $\|\mathbf{U}_h\|_{\mathsf{F}}^2 \le k$. -/
private theorem abs_frobInner_conjTranspose_mul_le {k : ℕ} {l : Type*} [Fintype l]
    (Ω₁ Ω₂ : Matrix (Fin k) l ℝ) (Uh Ut : Matrix (Fin k) (Fin k) ℝ)
    (hUh : frobNorm Uh ^ 2 ≤ k) :
    |frobInner (Uhᴴ * Ω₁) (Utᴴ * Ω₂)| ≤ specNorm (Ω₁ * Ω₂ᴴ) * √(k * frobNorm Ut ^ 2) := by
  have e : frobInner (Uhᴴ * Ω₁) (Utᴴ * Ω₂) = frobInner (Uh * Utᴴ) (Ω₁ * Ω₂ᴴ) := by
    rw [frobInner_mul_left, Matrix.conjTranspose_conjTranspose, ← Matrix.mul_assoc]
    rw [frobInner_eq_re_trace_mul_conjTranspose, frobInner_eq_re_trace_mul_conjTranspose]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    have h := Matrix.trace_conjTranspose (Ω₁ * (Ω₂ᴴ * (Ut * Uhᴴ)))
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      star_trivial] at h
    rw [h]
  have hnuc : nuclearNorm (Uh * Utᴴ) ≤ frobNorm Uh * frobNorm Ut := by
    have := nuclearNorm_mul_le_frobNorm_mul_frobNorm Uh Utᴴ
    rwa [frobNorm_conjTranspose] at this
  have hfr : frobNorm Uh * frobNorm Ut ≤ √(k * frobNorm Ut ^ 2) := by
    calc frobNorm Uh * frobNorm Ut = √((frobNorm Uh * frobNorm Ut) ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(k * frobNorm Ut ^ 2) :=
          Real.sqrt_le_sqrt (by rw [mul_pow]; exact mul_le_mul_of_nonneg_right hUh (sq_nonneg _))
  rw [e]
  refine (abs_frobInner_le_nuclearNorm_mul_specNorm _ _).trans ?_
  exact (mul_le_mul_of_nonneg_right (hnuc.trans hfr) (specNorm_nonneg _)).trans_eq (mul_comm _ _)

/-- The residual of a projector on a diagonal matrix:
$\|\mathbf{D} - \mathbf{P}\mathbf{D}\|_{\mathsf{F}}^2 =
\sum_j d_j^2 - \sum_j d_j^2 \mathbf{P}_{jj}$. -/
private theorem frobNorm_diagonal_sub_mul_diagonal_sq {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) (d : n → ℝ) :
    frobNorm (Matrix.diagonal d - P * Matrix.diagonal d) ^ 2 =
      ∑ j, d j ^ 2 - ∑ j, d j ^ 2 * P j j := by
  rw [hP.frobNorm_sub_mul_sq_eq_sub_frobInner, frobNorm_diagonal_sq, frobInner_eq_sum_mul,
    Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  simp only [Real.norm_eq_abs, sq_abs, Matrix.diagonal_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.star_apply, star_trivial]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Ky Fan maximality of the truncated SVD, in the Frobenius norm: a projection onto $k$
orthonormal columns captures at most the energy of the dominant $k$-frame of $\mathbf{Y}$. -/
private theorem frobNorm_conjTranspose_mul_le_rangeProjector_truncatedSVD {n l : Type*}
    [Fintype n] [Fintype l] (Y : Matrix n l ℝ) (k : ℕ)
    {V : Matrix n (Fin k) ℝ} (hV : HasOrthonormalCols V) :
    frobNorm (Vᴴ * Y) ^ 2 ≤ frobNorm (rangeProjector (truncatedSVD Y k) * Y) ^ 2 := by
  classical
  have hB : (V * (Vᴴ * Y)).rank ≤ k :=
    (Matrix.rank_mul_le_right _ _).trans ((Matrix.rank_mul_le_left _ _).trans
      (by simpa using Matrix.rank_le_card_height Vᴴ))
  have h1 := frobNorm_sub_truncatedSVD_le_of_rank_le Y hB
  have e1 : Y - rangeProjector (truncatedSVD Y k) * Y =
      (1 - rangeProjector (truncatedSVD Y k)) * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul]
  have e2 : Y - V * (Vᴴ * Y) = (1 - V * Vᴴ) * Y := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]
  rw [← rangeProjector_truncatedSVD_mul Y k, e1, e2] at h1
  have hP := (isStarProjection_rangeProjector (truncatedSVD Y k)).frobNorm_sq_eq_add Y
  have hV' := (hV.isStarProjection_mul_conjTranspose).frobNorm_sq_eq_add Y
  rw [Matrix.mul_assoc, hV.frobNorm_mul_left] at hV'
  have h2 := pow_le_pow_left₀ (frobNorm_nonneg _) h1 2
  linarith

/-- The competitor frame $\mathbf{V} = [\cos\theta\,\mathbf{I}; \sin\theta\,\mathbf{R}]$ has
orthonormal columns when $\mathbf{R}$ does. -/
private theorem hasOrthonormalCols_fromRows_cos_sin {k : ℕ} {θ : ℝ}
    {R : Matrix (Fin k) (Fin k) ℝ} (hR : HasOrthonormalCols R) :
    HasOrthonormalCols
      (Matrix.fromRows (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ)) (Real.sin θ • R)) := by
  unfold HasOrthonormalCols at hR ⊢
  rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
  simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, hR, ← add_smul]
  have h : Real.cos θ * Real.cos θ + Real.sin θ * Real.sin θ = 1 := by
    linear_combination Real.cos_sq_add_sin_sq θ
  rw [h, one_smul]

/-- The Frobenius norm of the competitor's projected sketch:
$\|\mathbf{V}^{\mathsf{T}}\mathbf{D}\mathbf{\Omega}\|_{\mathsf{F}}^2 = \cos^2\theta\,
\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 + 2\cos\theta\, s\sin\theta\,
\langle\mathbf{\Omega}_1, \mathbf{R}^{\mathsf{T}}\mathbf{\Omega}_2\rangle_{\mathsf{F}} +
s^2\sin^2\theta\,\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_fromRows_cos_sin_mul_diagonal_sq {k : ℕ} {l : Type*} [Fintype l] {s : ℝ}
    (θ : ℝ) {R : Matrix (Fin k) (Fin k) ℝ} (hR : HasOrthonormalCols R)
    (Ω : Matrix (Fin k ⊕ Fin k) l ℝ) :
    frobNorm ((Matrix.fromRows (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ)) (Real.sin θ • R))ᴴ *
        (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω)) ^ 2 =
      Real.cos θ ^ 2 * frobNorm Ω.toRows₁ ^ 2 +
        2 * (Real.cos θ * (s * Real.sin θ)) * frobInner Ω.toRows₁ (Rᴴ * Ω.toRows₂) +
        (s * Real.sin θ) ^ 2 * frobNorm Ω.toRows₂ ^ 2 := by
  rw [conjTranspose_mul_diagonal_mul_eq_toRows, Matrix.toRows₁_fromRows, Matrix.toRows₂_fromRows]
  have e : (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ))ᴴ * Ω.toRows₁ +
      s • ((Real.sin θ • R)ᴴ * Ω.toRows₂) =
      Real.cos θ • Ω.toRows₁ + (s * Real.sin θ) • (Rᴴ * Ω.toRows₂) := by
    simp only [Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial, Matrix.smul_mul,
      Matrix.one_mul, smul_smul]
  rw [e, frobNorm_add_sq, frobInner_smul_left, frobInner_smul_right, frobNorm_real_smul,
    frobNorm_real_smul, hR.conjTranspose.frobNorm_mul_left, mul_pow, mul_pow, sq_abs, sq_abs]
  ring

/-- The upper bound on the frame energy: with $\mathbf{U}_h, \mathbf{U}_t$ the two blocks of a
frame,
$\|\mathbf{U}_h^{\mathsf{T}}\mathbf{\Omega}_1 +
s\mathbf{U}_t^{\mathsf{T}}\mathbf{\Omega}_2\|_{\mathsf{F}}^2
\le \|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2 T +
2s\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{kT} + s^2\|\mathbf{\Omega}_2\|_2^2 T$
where $T = \|\mathbf{U}_t\|_{\mathsf{F}}^2$. -/
private theorem frobNorm_add_smul_conjTranspose_mul_sq_le {k : ℕ} {l : Type*} [Fintype l] {s : ℝ}
    (hs : 0 ≤ s) (Ω₁ Ω₂ : Matrix (Fin k) l ℝ) (Uh Ut : Matrix (Fin k) (Fin k) ℝ)
    (hPSD : (1 - Uh * Uhᴴ).PosSemidef) {T : ℝ} (hT : (Uh * Uhᴴ).trace = k - T)
    (hTt : frobNorm Ut ^ 2 = T) :
    frobNorm (Uhᴴ * Ω₁ + s • (Utᴴ * Ω₂)) ^ 2 ≤
      frobNorm Ω₁ ^ 2 - singularValues Ω₁ (k - 1) ^ 2 * T +
        2 * s * specNorm (Ω₁ * Ω₂ᴴ) * √(k * T) + s ^ 2 * specNorm Ω₂ ^ 2 * T := by
  have hT0 : 0 ≤ T := by rw [← hTt]; positivity
  have hUh : frobNorm Uh ^ 2 ≤ k := by
    rw [frobNorm_sq_eq_trace_mul_conjTranspose, hT]
    linarith
  have h1 := frobNorm_conjTranspose_mul_sq_le_of_posSemidef Ω₁ Uh hPSD T hT
  have h2 := abs_frobInner_conjTranspose_mul_le Ω₁ Ω₂ Uh Ut hUh
  rw [hTt] at h2
  have h3 : frobNorm (Utᴴ * Ω₂) ^ 2 ≤ T * specNorm Ω₂ ^ 2 := by
    have h := frobNorm_mul_le_frobNorm_mul_specNorm Utᴴ Ω₂
    rw [frobNorm_conjTranspose] at h
    have h' := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
    rw [mul_pow, hTt] at h'
    exact h'
  rw [frobNorm_add_sq, frobInner_smul_right, frobNorm_real_smul, mul_pow, sq_abs]
  have hcross : s * frobInner (Uhᴴ * Ω₁) (Utᴴ * Ω₂) ≤ s * (specNorm (Ω₁ * Ω₂ᴴ) * √(k * T)) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans h2) hs
  have htail : s ^ 2 * frobNorm (Utᴴ * Ω₂) ^ 2 ≤ s ^ 2 * (T * specNorm Ω₂ ^ 2) :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg s)
  linarith

/-- The first conjunct, in the frame: the error is $k s^2 + (1 - s^2) T$ up to the inequality. -/
private theorem k_mul_sq_add_le_frobNorm_sub_diagonal {k : ℕ} {s : ℝ}
    {U : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ} (hU : HasOrthonormalCols U) {T : ℝ}
    (hT : T = (U.toRows₂ * U.toRows₂ᴴ).trace) :
    (k : ℝ) * s ^ 2 + (1 - s ^ 2) * T ≤
      frobNorm (Matrix.diagonal (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s)) -
        (U * Uᴴ) * Matrix.diagonal
          (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s))) ^ 2 := by
  rw [frobNorm_diagonal_sub_mul_diagonal_sq hU.isStarProjection_mul_conjTranspose]
  have htr := trace_toRows_mul_conjTranspose_add hU
  have hd1 : ∑ j : Fin k ⊕ Fin k, (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s) j) ^ 2
      = k + k * s ^ 2 := by
    simp [Fintype.sum_sum_type]
  have hd2 : ∑ j : Fin k ⊕ Fin k,
      (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s) j) ^ 2 * (U * Uᴴ) j j =
      (U.toRows₁ * U.toRows₁ᴴ).trace + s ^ 2 * (U.toRows₂ * U.toRows₂ᴴ).trace := by
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, one_pow, one_mul]
    rw [← Finset.mul_sum]
    rfl
  rw [hd1, hd2, hT]
  linarith

/-- The second conjunct, in the frame: the competitor $\mathbf{V}_\theta$ is beaten by the frame
and the frame energy is bounded by its blocks. -/
private theorem sin_mul_cos_mul_nuclearNorm_sub_le_of_frobNorm_sq_le {k : ℕ} {l : Type*}
    [Fintype l] {s θ : ℝ} (hs : 0 ≤ s) (Ω : Matrix (Fin k ⊕ Fin k) l ℝ)
    {U : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ}
    (hU : HasOrthonormalCols U) (hPSD : (1 - U.toRows₁ * U.toRows₁ᴴ).PosSemidef) {T : ℝ}
    (hTU : T = (U.toRows₂ * U.toRows₂ᴴ).trace) {R : Matrix (Fin k) (Fin k) ℝ}
    (hR : HasOrthonormalCols R)
    (hcross : frobInner Ω.toRows₁ (Rᴴ * Ω.toRows₂) = nuclearNorm (Ω.toRows₁ * Ω.toRows₂ᴴ))
    (hKF : frobNorm ((Matrix.fromRows (Real.cos θ • (1 : Matrix (Fin k) (Fin k) ℝ))
        (Real.sin θ • R))ᴴ * (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω)) ^ 2 ≤
      frobNorm (Uᴴ * (Matrix.diagonal (Sum.elim (fun _ => (1 : ℝ)) (fun _ => s)) * Ω)) ^ 2) :
    2 * s * Real.sin θ * Real.cos θ * nuclearNorm (Ω.toRows₁ * Ω.toRows₂ᴴ) -
        Real.sin θ ^ 2 * (frobNorm Ω.toRows₁ ^ 2 - s ^ 2 * frobNorm Ω.toRows₂ ^ 2) ≤
      T * (s ^ 2 * specNorm Ω.toRows₂ ^ 2 - singularValues Ω.toRows₁ (k - 1) ^ 2) +
        2 * s * specNorm (Ω.toRows₁ * Ω.toRows₂ᴴ) * √(k * T) := by
  rw [frobNorm_fromRows_cos_sin_mul_diagonal_sq θ hR Ω, hcross] at hKF
  rw [conjTranspose_mul_diagonal_mul_eq_toRows] at hKF
  have hT_Uh := trace_toRows_mul_conjTranspose_add hU
  have hT' : (U.toRows₁ * U.toRows₁ᴴ).trace = k - T := by linarith
  have hTt : frobNorm U.toRows₂ ^ 2 = T := by
    rw [frobNorm_sq_eq_trace_mul_conjTranspose, hTU]
  have hup := frobNorm_add_smul_conjTranspose_mul_sq_le hs Ω.toRows₁ Ω.toRows₂ U.toRows₁
    U.toRows₂ hPSD hT' hTt
  have hca : Real.cos θ ^ 2 * frobNorm Ω.toRows₁ ^ 2 =
      frobNorm Ω.toRows₁ ^ 2 - Real.sin θ ^ 2 * frobNorm Ω.toRows₁ ^ 2 := by
    linear_combination frobNorm Ω.toRows₁ ^ 2 * Real.cos_sq_add_sin_sq θ
  linarith [hKF, hup, hca]

/-- The tail content of the sketch's dominant frame controls the error, deterministic: for
$\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, s\mathbf{I}_k)$ with $s \ge 0$, any
$\mathbf{\Omega} = [\mathbf{\Omega}_1; \mathbf{\Omega}_2] \in \mathbb{R}^{2k \times \ell}$ with
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \ge k$, $\mathbf{P}$ the range projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$, $T = \operatorname{tr}\mathbf{P}_{22}$ its tail
content, and any $\theta$: the error is at least $ks^2 + (1 - s^2)T$, and
$$\begin{aligned}
&T\bigl(s^2\|\mathbf{\Omega}_2\|_2^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2\bigr) +
2s\,\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{kT} \\
&\quad\ge 2s\sin\theta\cos\theta\,\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_* -
\sin^2\theta\,\bigl(\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 -
s^2\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2\bigr)\,.
\end{aligned}$$
No printed source. New (research note OP1, §4 steps 1–3). -/
theorem frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational {k : ℕ} {s : ℝ}
    (hs0 : 0 ≤ s) {A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ}
    (hA : A = Matrix.fromBlocks 1 0 0 (s • 1)) {Ω' : Matrix (Fin k ⊕ Fin k) l ℝ}
    (hr : k ≤ (A * Ω').rank) (θ : ℝ) {T : ℝ}
    (hT : T = ∑ i : Fin k, rangeProjector (truncatedSVD (A * Ω') k) (Sum.inr i) (Sum.inr i)) :
    k * s ^ 2 + (1 - s ^ 2) * T ≤ frobNorm (A - earlyTruncatedRSVD A Ω' k) ^ 2 ∧
      2 * s * Real.sin θ * Real.cos θ * nuclearNorm (Ω'.toRows₁ * Ω'.toRows₂ᵀ) -
          Real.sin θ ^ 2 * (frobNorm Ω'.toRows₁ ^ 2 - s ^ 2 * frobNorm Ω'.toRows₂ ^ 2) ≤
        T * (s ^ 2 * specNorm Ω'.toRows₂ ^ 2 - singularValues Ω'.toRows₁ (k - 1) ^ 2) +
          2 * s * specNorm (Ω'.toRows₁ * Ω'.toRows₂ᵀ) * √(k * T) := by
  classical
  subst hA
  have hD : (Matrix.fromBlocks (1 : Matrix (Fin k) (Fin k) ℝ) 0 0 (s • 1)) =
      Matrix.diagonal (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s)) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.one_apply, Matrix.diagonal]
  rw [hD] at hr hT ⊢
  obtain ⟨U, hU, hPU⟩ := exists_hasOrthonormalCols_rangeProjector_truncatedSVD_eq _ k hr
  have hPSD : (1 - U.toRows₁ * U.toRows₁ᴴ).PosSemidef := by
    have hQ : IsStarProjection (1 - U * Uᴴ) := by
      rw [← hPU]
      exact isStarProjection_one_sub_rangeProjector _
    have e : (1 - U * Uᴴ).submatrix Sum.inl Sum.inl = 1 - U.toRows₁ * U.toRows₁ᴴ := by
      ext i j
      simp [Matrix.mul_apply, Matrix.toRows₁, Matrix.one_apply]
    rw [← e]
    exact hQ.posSemidef.submatrix Sum.inl
  have hTU : T = (U.toRows₂ * U.toRows₂ᴴ).trace := by
    rw [hT, hPU]
    rfl
  constructor
  · rw [earlyTruncatedRSVD, hPU]
    exact k_mul_sq_add_le_frobNorm_sub_diagonal hU hTU
  · simp only [← Matrix.conjTranspose_eq_transpose_of_trivial]
    obtain ⟨R, hR, hcross⟩ := exists_orthogonal_frobInner_eq_nuclearNorm Ω'.toRows₁ Ω'.toRows₂
    have hKF := frobNorm_conjTranspose_mul_le_rangeProjector_truncatedSVD
      (Matrix.diagonal (Sum.elim (fun _ : Fin k => (1 : ℝ)) (fun _ : Fin k => s)) * Ω') k
      (hasOrthonormalCols_fromRows_cos_sin (θ := θ) hR)
    rw [hPU, Matrix.mul_assoc U, hU.frobNorm_mul_left] at hKF
    exact sin_mul_cos_mul_nuclearNorm_sub_le_of_frobNorm_sq_le hs0 Ω' hU hPSD hTU hR hcross hKF

end NLAlib
