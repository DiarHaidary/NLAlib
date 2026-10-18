/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.RangeFinder
public import NLAlib.Matrix.Functions.HermitianCalculus

/-!
# The filtered range finder

The randomized SVD at a filtered test matrix $g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega}$,
for a real function $g$ through the functional calculus, here deterministic. Polynomial filters
(randomized subspace iteration, $g(x) = x^p$; the Chebyshev filters inside randomized block Krylov
iteration) are the case $g = f.\mathrm{eval}$, by
`Matrix.IsHermitian.cfc_eq_aeval_of_forall_eval_eq`.

The filter enters through two frames. $\mathbf{W}$ is an invariant frame of
$\mathbf{A}^{\mathsf{H}}\mathbf{A}$ for the head that the filter amplifies,
$\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{W} = \mathbf{W}\operatorname{diag}(\mathbf{d})$ with
$c \le \lvert g(\mathbf{d}_i) \rvert$; $\mathbf{Z}$ is a frame whose range contains that of
$\mathbf{W}$ and with $\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank. With
$\mathbf{B} = \mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})$ the sketch residual is
$$\mathbf{M} = (\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\,,$$
which is small when $g$ is small on the tail. The head of $\mathbf{A}$ is captured up to
$c^{-1}\mathbf{M}$, and the error of the randomized SVD is the tail of $\mathbf{A}$ plus
$c^{-2}\mathbf{M}^{\mathsf{H}}\mathbf{M}$, in every quadratic unitarily invariant norm.

## Main results

* `NLAlib.HasOrthonormalCols.singularValues_one_sub_rangeProjector_mul_mul_le`,
  `NLAlib.HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le`: head capture, singular
  value by singular value and in every unitarily invariant norm.
* `NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le`: the filtered structural
  bound, Gram form, every unitarily invariant norm.
* `NLAlib.HasOrthonormalCols.specNorm_sub_rsvd_cfc_sq_le`,
  `NLAlib.HasOrthonormalCols.frobNorm_sub_rsvd_cfc_sq_le`: its spectral and Frobenius forms.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n r s : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype r] [Fintype s] [DecidableEq m] [DecidableEq n] [DecidableEq r] [DecidableEq s]

-- Stage B4

/-- **Head capture by a filtered sketch, singular value by singular value**: under the hypotheses
of `NLAlib.HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le`, for every $i$,
$$\sigma_i\bigl((\mathbf{I} - \mathbf{P}_{\mathbf{B}\mathbf{\Omega}})
\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}\bigr) \le
c^{-1}\,\sigma_i\bigl((\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})
\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\bigr)\,,\qquad
\mathbf{B} = \mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\,.$$
The pointwise form survives squaring, which the Gram form of the filtered structural bound needs.
Proof: $\mathbf{A}\mathbf{W} = \mathbf{B}\mathbf{W}g(\mathbf{D})^{-1}$ and
$\mathbf{W} = \mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{W}$, and the competitor identity gives
$(\mathbf{I} - \mathbf{P}_{\mathbf{B}\mathbf{\Omega}})\mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
-(\mathbf{I} - \mathbf{P}_{\mathbf{B}\mathbf{\Omega}})\mathbf{M}\mathbf{Z}^{\mathsf{H}}$.
[TroppWebber2023, Lemma 9.5 (proof, (9.6))]. -/
theorem HasOrthonormalCols.singularValues_one_sub_rangeProjector_mul_mul_le {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {W : Matrix n r 𝕜} (hW : HasOrthonormalCols W) {d : r → ℝ}
    (hAW : Aᴴ * A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank)
    (hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin) {c : ℝ} (hc : 0 < c)
    (hg : ∀ i, c ≤ |g (d i)|) (i : ℕ) :
    singularValues ((1 - rangeProjector (A * cfc g (Aᴴ * A) * Ω)) * (A * W * Wᴴ)) i ≤
      c⁻¹ * singularValues
        ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) i := by
  set B := A * cfc g (Aᴴ * A) with hB
  set P := rangeProjector (B * Ω)
  set M := (B - B * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)
  set Dinv : Matrix r r 𝕜 := Matrix.diagonal fun j => (((g (d j))⁻¹ : ℝ) : 𝕜)
  have hgd (j : r) : g (d j) ≠ 0 := fun h0 => by
    have h := hg j
    rw [h0, abs_zero] at h
    linarith
  have hD : (Matrix.diagonal fun j => (g (d j) : 𝕜)) * Dinv = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    rw [← RCLike.ofReal_mul, mul_inv_cancel₀ (hgd j), RCLike.ofReal_one]
  have hGW := (Matrix.isHermitian_conjTranspose_mul_self A).cfc_mul_eq_mul_diagonal_of_mul_eq
    hAW g
  have hAW' : A * W = B * W * Dinv := by
    rw [hB, Matrix.mul_assoc A (cfc g (Aᴴ * A)) W, hGW, ← Matrix.mul_assoc,
      Matrix.mul_assoc (A * W), hD, Matrix.mul_one]
  have hZW : Z * Zᴴ * W = W := by
    rw [← hZ.rangeProjector_eq]
    exact rangeProjector_mul_eq_self_iff.mpr hWZ
  have hBW : B * W = B * Z * Zᴴ * W := by
    rw [Matrix.mul_assoc (B * Z), Matrix.mul_assoc B, ← Matrix.mul_assoc Z, hZW]
  have hC : B * Z * Zᴴ = B * Ω * pinv (Zᴴ * Ω) * Zᴴ - M * Zᴴ := by
    have h := hZ.sub_mul_mul_pinv_mul_conjTranspose_eq hΩ B
    rw [sub_sub, sub_right_inj] at h
    exact eq_sub_of_add_eq h.symm
  have hPC : (1 - P) * (B * Ω * pinv (Zᴴ * Ω) * Zᴴ) = 0 := by
    have h0 : (1 - P) * (B * Ω) = 0 := by
      rw [Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]
    rw [Matrix.mul_assoc (B * Ω), ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  have hPB : (1 - P) * (B * Z * Zᴴ) = -((1 - P) * M * Zᴴ) := by
    rw [hC, Matrix.mul_sub, hPC, zero_sub, Matrix.mul_assoc (1 - P) M Zᴴ]
  have hN : (1 - P) * (A * W * Wᴴ) = -((1 - P) * M) * (Zᴴ * (W * Dinv)) * Wᴴ := by
    calc (1 - P) * (A * W * Wᴴ) = (1 - P) * (B * Z * Zᴴ) * (W * Dinv * Wᴴ) := by
          rw [hAW', hBW]
          simp only [Matrix.mul_assoc]
      _ = -((1 - P) * M) * (Zᴴ * (W * Dinv)) * Wᴴ := by
          rw [hPB]
          simp only [Matrix.neg_mul, Matrix.mul_assoc]
  rw [hN, hW.singularValues_mul_conjTranspose_right]
  calc singularValues (-((1 - P) * M) * (Zᴴ * (W * Dinv))) i
      ≤ singularValues (-((1 - P) * M)) i * specNorm (Zᴴ * (W * Dinv)) :=
        singularValues_mul_le_mul_specNorm _ _ i
    _ ≤ singularValues M i * c⁻¹ := by
        rw [singularValues_neg]
        refine mul_le_mul (singularValues_one_sub_rangeProjector_mul_le _ M i) ?_
          (specNorm_nonneg _) (singularValues_nonneg M i)
        calc specNorm (Zᴴ * (W * Dinv)) ≤ specNorm (W * Dinv) :=
              hZ.specNorm_conjTranspose_mul_le _
          _ = specNorm Dinv := hW.specNorm_mul_left _
          _ ≤ c⁻¹ := specNorm_diagonal_le (inv_nonneg.mpr hc.le) fun j => by
              rw [RCLike.norm_ofReal, abs_inv]
              exact inv_anti₀ hc (hg j)
    _ = c⁻¹ * singularValues M i := mul_comm _ _

/-- **Head capture by a filtered sketch**: for an invariant frame $\mathbf{W}$ of
$\mathbf{A}^{\mathsf{H}}\mathbf{A}$ with eigenvalues $\mathbf{d}$ on which
$\lvert g \rvert \ge c > 0$, a frame $\mathbf{Z}$ whose range contains that of $\mathbf{W}$, and
$\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$ of full row rank, in every unitarily invariant norm,
$$\|(\mathbf{I} - \mathbf{P}_{\mathbf{B}\mathbf{\Omega}})\mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}
\|_{\Phi} \le c^{-1}\,\bigl\|(\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})
\mathbf{\Omega}(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}\bigr\|_{\Phi}\,,\qquad
\mathbf{B} = \mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\,.$$
The truncated outputs use it alone (with Gu's projected form).
[TroppWebber2023, Lemma 9.5 (proof, (9.6))]; [MuscoMusco2015, Lemma 9, property 1]; there for a
diagonal matrix and the top singular frame, here any matrix and frames. -/
theorem HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le (Φ : SymmetricGauge)
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {W : Matrix n r 𝕜}
    (hW : HasOrthonormalCols W) {d : r → ℝ}
    (hAW : Aᴴ * A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank)
    (hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin) {c : ℝ} (hc : 0 < c)
    (hg : ∀ i, c ≤ |g (d i)|) :
    Φ.matrixNorm ((1 - rangeProjector (A * cfc g (Aᴴ * A) * Ω)) * (A * W * Wᴴ)) ≤
      c⁻¹ * Φ.matrixNorm
        ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) := by
  have h := Φ.matrixNorm_le_of_singularValues_le
    (A := (1 - rangeProjector (A * cfc g (Aᴴ * A) * Ω)) * (A * W * Wᴴ))
    (B := ((c⁻¹ : ℝ) : 𝕜) •
      ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))) fun i => by
      rw [singularValues_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hc)]
      exact hW.singularValues_one_sub_rangeProjector_mul_mul_le g hAW hZ hΩ hWZ hc hg i
  rwa [Φ.matrixNorm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hc)] at h

omit [DecidableEq m] in
/-- **The filtered structural bound, Gram form**: under the hypotheses of the head-capture lemma
(`NLAlib.HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le`), in every unitarily
invariant norm,
$$\bigl\|\mathbf{E}_g^{\mathsf{H}}\mathbf{E}_g\bigr\|_{\Phi} \le
\bigl\|(\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}})^{\mathsf{H}}
(\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}})\bigr\|_{\Phi} +
c^{-2}\,\|\mathbf{M}^{\mathsf{H}}\mathbf{M}\|_{\Phi}\,,$$
with $\mathbf{E}_g = \mathbf{A} - \mathsf{rsvd}(\mathbf{A},
g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})$,
$\mathbf{B} = \mathbf{A}g(\mathbf{A}^{\mathsf{H}}\mathbf{A})$ and
$\mathbf{M} = (\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{\Omega}
(\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega})^{+}$: a bound on every quadratic unitarily invariant norm,
squared Schatten norms $\|\cdot\|_{S_p}^2$ for $p \ge 2$ included. At $g = 1$ and $\mathbf{W} =
\mathbf{Z}$ it is the structural bound of the range finder
(`NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_le`).
[TroppWebber2023, Lemma 9.5]; there for a diagonal positive semidefinite matrix, the top frames and
Schatten norms, with $\|\mathbf{A}_3\varphi(\mathbf{A}_3)\|_p$ in the printed statement where the
proof (and Theorem 9.2) uses the Frobenius norm; here any matrix and frames, and the Gram form of
the proof.
Result: filtered-range-finder-bound -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le (Φ : SymmetricGauge)
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} (g : ℝ → ℝ) {W : Matrix n r 𝕜}
    (hW : HasOrthonormalCols W) {d : r → ℝ}
    (hAW : Aᴴ * A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank)
    (hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin) {c : ℝ} (hc : 0 < c)
    (hg : ∀ i, c ≤ |g (d i)|) :
    Φ.matrixNorm ((A - rsvd A (cfc g (Aᴴ * A) * Ω))ᴴ * (A - rsvd A (cfc g (Aᴴ * A) * Ω))) ≤
      Φ.matrixNorm ((A - A * W * Wᴴ)ᴴ * (A - A * W * Wᴴ)) +
        c⁻¹ ^ 2 * Φ.matrixNorm
          (((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))ᴴ *
            ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω))) := by
  classical
  have hcap := hW.singularValues_one_sub_rangeProjector_mul_mul_le g hAW hZ hΩ hWZ hc hg
  set G := cfc g (Aᴴ * A)
  set P := rangeProjector (A * G * Ω)
  set M := (A * G - A * G * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)
  have hsub : A - rsvd A (G * Ω) =
      (1 - P) * (A - A * W * Wᴴ) + (1 - P) * (A * W * Wᴴ) := by
    rw [sub_rsvd, ← Matrix.mul_assoc, ← Matrix.mul_add, sub_add_cancel]
  have hEW : (A - A * W * Wᴴ) * W = 0 := by
    rw [Matrix.sub_mul, hW.mul_conjTranspose_mul_cancel_right, sub_self]
  have hcross : (1 - P) * (A - A * W * Wᴴ) * ((1 - P) * (A * W * Wᴴ))ᴴ = 0 := by
    have hEW' : (A - A * (W * Wᴴ)) * W = 0 := by
      rw [← Matrix.mul_assoc]
      exact hEW
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (A - A * (W * Wᴴ)) W, hEW', Matrix.zero_mul, Matrix.mul_zero]
  have hcross' : (1 - P) * (A * W * Wᴴ) * ((1 - P) * (A - A * W * Wᴴ))ᴴ = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose ((1 - P) * (A * W * Wᴴ)),
      ← Matrix.conjTranspose_mul, hcross, Matrix.conjTranspose_zero]
  have hgram : (A - rsvd A (G * Ω)) * (A - rsvd A (G * Ω))ᴴ =
      (1 - P) * (A - A * W * Wᴴ) * ((1 - P) * (A - A * W * Wᴴ))ᴴ +
        (1 - P) * (A * W * Wᴴ) * ((1 - P) * (A * W * Wᴴ))ᴴ := by
    rw [hsub, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hcross,
      hcross', add_zero, zero_add]
  have hE : Φ.matrixNorm (((1 - P) * (A - A * W * Wᴴ))ᴴ * ((1 - P) * (A - A * W * Wᴴ))) ≤
      Φ.matrixNorm ((A - A * W * Wᴴ)ᴴ * (A - A * W * Wᴴ)) := by
    refine Φ.matrixNorm_le_of_singularValues_le fun i => ?_
    rw [singularValues_conjTranspose_mul_self, singularValues_conjTranspose_mul_self]
    exact pow_le_pow_left₀ (singularValues_nonneg _ _)
      (singularValues_one_sub_rangeProjector_mul_le _ _ i) 2
  have hN : Φ.matrixNorm (((1 - P) * (A * W * Wᴴ))ᴴ * ((1 - P) * (A * W * Wᴴ))) ≤
      c⁻¹ ^ 2 * Φ.matrixNorm (Mᴴ * M) := by
    have hc2 : ‖((c⁻¹ ^ 2 : ℝ) : 𝕜)‖ = c⁻¹ ^ 2 := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (by positivity)]
    have h := Φ.matrixNorm_le_of_singularValues_le
      (A := ((1 - P) * (A * W * Wᴴ))ᴴ * ((1 - P) * (A * W * Wᴴ)))
      (B := ((c⁻¹ ^ 2 : ℝ) : 𝕜) • (Mᴴ * M)) fun i => by
        rw [singularValues_smul, hc2, singularValues_conjTranspose_mul_self,
          singularValues_conjTranspose_mul_self, ← mul_pow]
        exact pow_le_pow_left₀ (singularValues_nonneg _ _) (hcap i) 2
    rwa [Φ.matrixNorm_smul, hc2] at h
  rw [← Φ.matrixNorm_mul_conjTranspose_self, hgram]
  refine (Φ.matrixNorm_add_le _ _).trans ?_
  rw [Φ.matrixNorm_mul_conjTranspose_self, Φ.matrixNorm_mul_conjTranspose_self]
  exact add_le_add hE hN

omit [DecidableEq m] in
/-- **The filtered structural bound, spectral form**: under the hypotheses of the head-capture
lemma,
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})\|_2^2 \le
\|\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}\|_2^2 + c^{-2}\|\mathbf{M}\|_2^2\,,$$
with $\mathbf{M}$ the sketch residual of
`NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le`.
[TroppWebber2023, Lemma 9.5], at $p = \infty$.
Result: filtered-range-finder-bound -/
theorem HasOrthonormalCols.specNorm_sub_rsvd_cfc_sq_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    (g : ℝ → ℝ) {W : Matrix n r 𝕜} (hW : HasOrthonormalCols W) {d : r → ℝ}
    (hAW : Aᴴ * A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank)
    (hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin) {c : ℝ} (hc : 0 < c)
    (hg : ∀ i, c ≤ |g (d i)|) :
    specNorm (A - rsvd A (cfc g (Aᴴ * A) * Ω)) ^ 2 ≤
      specNorm (A - A * W * Wᴴ) ^ 2 +
        c⁻¹ ^ 2 * specNorm
          ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 := by
  have h := (lpGauge ⊤ le_top).matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le g hW hAW hZ hΩ
    hWZ hc hg
  simpa only [lpGauge_top_matrixNorm, specNorm_conjTranspose_mul_self] using h

omit [DecidableEq m] in
/-- **The filtered structural bound, Frobenius form**: under the hypotheses of the head-capture
lemma,
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A},
g(\mathbf{A}^{\mathsf{H}}\mathbf{A})\mathbf{\Omega})\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathbf{A}\mathbf{W}\mathbf{W}^{\mathsf{H}}\|_{\mathsf{F}}^2 +
c^{-2}\|\mathbf{M}\|_{\mathsf{F}}^2\,,$$
with $\mathbf{M}$ the sketch residual of
`NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le`.
[TroppWebber2023, Lemma 9.5], at $p = 2$.
Result: filtered-range-finder-bound -/
theorem HasOrthonormalCols.frobNorm_sub_rsvd_cfc_sq_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    (g : ℝ → ℝ) {W : Matrix n r 𝕜} (hW : HasOrthonormalCols W) {d : r → ℝ}
    (hAW : Aᴴ * A * W = W * Matrix.diagonal fun i => (d i : 𝕜)) {Z : Matrix n s 𝕜}
    (hZ : HasOrthonormalCols Z) (hΩ : (Ωᴴ * Z).rank = Z.rank)
    (hWZ : LinearMap.range W.mulVecLin ≤ LinearMap.range Z.mulVecLin) {c : ℝ} (hc : 0 < c)
    (hg : ∀ i, c ≤ |g (d i)|) :
    frobNorm (A - rsvd A (cfc g (Aᴴ * A) * Ω)) ^ 2 ≤
      frobNorm (A - A * W * Wᴴ) ^ 2 +
        c⁻¹ ^ 2 * frobNorm
          ((A * cfc g (Aᴴ * A) - A * cfc g (Aᴴ * A) * Z * Zᴴ) * Ω * pinv (Zᴴ * Ω)) ^ 2 := by
  have h := (lpGauge 1 le_rfl).matrixNorm_conjTranspose_mul_self_sub_rsvd_cfc_le g hW hAW hZ hΩ
    hWZ hc hg
  simpa only [lpGauge_one_matrixNorm, nuclearNorm_conjTranspose_mul_self] using h

end NLAlib
