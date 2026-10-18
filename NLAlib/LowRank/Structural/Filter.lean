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

* `NLAlib.HasOrthonormalCols.matrixNorm_one_sub_rangeProjector_mul_mul_le`: head capture.
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
  sorry

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
  sorry

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
  sorry

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
  sorry

end NLAlib
