/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Factorizations.NystromOrder
public import NLAlib.Matrix.Factorizations.SketchedLowRank
public import NLAlib.Matrix.Spectral.BestRankApprox

/-!
# Late truncation of sketched low-rank approximations

Late truncation computes an approximation and then keeps its best rank-$k$ part:
$\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k$ for the randomized SVD,
$\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\rrbracket_k$ for Nyström and
$\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k$ for generalized
Nyström. They have no names: they are spelled `truncatedSVD (rsvd A Ω) k`,
`truncatedSVD (nystrom H Ω) k` and `truncatedSVD (generalizedNystrom A Ω Ψ) k`, and their errors
`A - truncatedSVD (rsvd A Ω) k` and so on. The algorithm's own form
$\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$ is bridged by
`NLAlib.HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd`.

The deterministic bounds here are instances of the truncation lemmas of
`NLAlib/Matrix/Spectral/BestRankApprox.lean`: constant one for the randomized SVD and for Nyström of
a positive semidefinite matrix (both are dominated by the input), an exact Pythagorean split for the
randomized SVD in the Frobenius norm, the Gram correspondence between truncated Nyström and the
truncated randomized SVD of a factor, and perturbed truncation for generalized Nyström. Every
statement holds for every choice of the truncation. Design: `docs/design/LowRank-S2a.md`.

## Main results

* `NLAlib.SymmetricGauge.matrixNorm_sub_truncatedSVD_rsvd_le`: HMT Theorem 9.3, every gauge.
* `NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`, `NLAlib.frobNorm_rsvd_sub_truncatedSVD_le`,
  `NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add`: the Frobenius split.
* `NLAlib.HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd`: the algorithm's factored form.
* `NLAlib.IsBestRankApprox.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le`: reverse
  Eckart–Young for a truncation of the randomized SVD.
* `NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`: Gu's projected
  form.
* `NLAlib.SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le`,
  `NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`,
  `Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom`,
  `Matrix.PosSemidef.nuclearNorm_sub_le_nuclearNorm_sub_truncatedSVD_nystrom_of_isBestRankApprox`:
  truncated Nyström, the last for any best approximation in place of the truncation; it lies
  below the matrix by `Matrix.PosSemidef.truncatedSVD_nystrom_le`
  (`NLAlib.Matrix.Factorizations.NystromOrder`).
* `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD`,
  `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm`: truncated generalized
  Nyström.
* `NLAlib.truncatedSVD_rsvd_eq_rangeProjector_mul`,
  `NLAlib.singularValues_sub_truncatedSVD_rsvd_le_of_le`: the truncated randomized SVD is a
  projection of $\mathbf{A}$, and its error decreases with the rank.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p q : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p] [Fintype q]

/-! ### Truncated randomized SVD -/

/-- **The truncated randomized SVD in every unitarily invariant norm**:
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\Phi} \le
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\Phi} +
\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\Phi}\,.$$
[HalkoMartinssonTropp2011, Theorem 9.3]; there in the spectral norm, here every unitarily
invariant norm.
Result: truncation-lemma -/
theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_rsvd_le (Φ : SymmetricGauge)
    (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    Φ.matrixNorm (A - truncatedSVD (rsvd A Ω) k) ≤
      Φ.matrixNorm (A - truncatedSVD A k) + Φ.matrixNorm (A - rsvd A Ω) :=
  (isBestRankApprox_truncatedSVD (rsvd A Ω) k).matrixNorm_sub_le_add_of_singularValues_le
    (fun i => (isStarProjection_rangeProjector (A * Ω)).singularValues_mul_le A i) Φ

/-- The optimal error of the projected matrix is at most that of the matrix:
$$\|\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}) -
\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}
\le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\,.$$
[HalkoMartinssonTropp2011, Theorem 9.3 (proof)]; [Woodruff2014, Lemma 44]. -/
theorem frobNorm_rsvd_sub_truncatedSVD_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) ≤ frobNorm (A - truncatedSVD A k) := by
  have h := (lpGauge 2 one_le_two).matrixNorm_sub_truncatedSVD_le_of_singularValues_le
    (A := A) (Â := rsvd A Ω)
    (fun i => (isStarProjection_rangeProjector (A * Ω)).singularValues_mul_le A i) k
  rwa [lpGauge_two_matrixNorm, lpGauge_two_matrixNorm] at h

/-- For any best rank-$k$ approximation $\mathbf{Y}$ of the randomized SVD
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, the error splits exactly:
$$\|\mathbf{A} - \mathbf{Y}\|_{\mathsf{F}}^2
= \|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 +
\|\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}) - \mathbf{Y}\|_{\mathsf{F}}^2\,.$$
The hypothesis form of `NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`, for a measurable selector or an
algorithm's $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$.
[Woodruff2014, Lemma 44]. -/
theorem IsBestRankApprox.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {k : ℕ} {Y : Matrix m n 𝕜} (hY : IsBestRankApprox (rsvd A Ω) k Y) :
    frobNorm (A - Y) ^ 2 = frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (rsvd A Ω - Y) ^ 2 := by
  classical
  have hPY : rangeProjector (A * Ω) * Y = Y := rangeProjector_mul_eq_self_iff.mpr
    ((rangeProjector_mul_eq_self_iff.mp hY.rangeProjector_mul).trans (range_rsvd_le A Ω))
  have h := frobNorm_sub_mul_sq (rangeProjector (A * Ω)) A Y
  rw [(isStarProjection_rangeProjector _).rangeProjector_eq, hPY, ← sub_rsvd] at h
  exact h

/-- **The truncated randomized SVD error splits exactly**:
$$\|\mathbf{A} -
\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
= \|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 +
\|\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}) -
\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every choice of the truncation.
[Woodruff2014, Lemma 44]; there the optimality of a truncation inside a row space, here the exact
split for the named output. Port of `NLAlib.frobSq_truncatedRsvdOutput_eq`, there for the
algorithm's factored form. -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 =
      frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) ^ 2 :=
  (isBestRankApprox_truncatedSVD (rsvd A Ω) k).frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add

/-- **The truncation lemma, Frobenius-squared form**:
$$\|\mathbf{A} -
\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 +
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
sharper than squaring the gauge form. Dominated by
`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add`, kept because
consumers cite this simpler form.
[HalkoMartinssonTropp2011, Theorem 9.3]; [Woodruff2014, Lemma 44]; there in the spectral norm.
Port of `NLAlib.frobSq_sub_truncatedRsvdOutput_le_bestRankFrobSq_add_frobSq_residual`.
Result: truncation-lemma -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 ≤
      frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2 := by
  rw [frobNorm_sub_truncatedSVD_rsvd_sq]
  have := pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_rsvd_sub_truncatedSVD_le A Ω k) 2
  linarith

/-- **Reverse Eckart–Young for the truncated randomized SVD**: for a best rank-$k$ approximation
$\mathbf{Y}$ of $\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$$\|\mathbf{A} - \mathbf{Y}\|_2^2 + \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \sigma_k(\mathbf{A})^2 + \|\mathbf{A} -
\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2\,:$$
a Frobenius bound for the truncated output becomes a spectral one at no cost. The right side does
not depend on the choice of the truncation (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`).
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a remark on truncated outputs, here subtraction-free, indices
from $0$. -/
theorem IsBestRankApprox.specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {k : ℕ} {Y : Matrix m n 𝕜} (hY : IsBestRankApprox (rsvd A Ω) k Y) :
    specNorm (A - Y) ^ 2 + frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 := by
  have h := specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_rank_le A hY.rank_le
  rwa [hY.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add, hY.frobNorm_sub,
    ← frobNorm_sub_truncatedSVD_rsvd_sq] at h

/-- **The truncated randomized SVD through a basis**: for any $\mathbf{Q}$ with orthonormal
columns spanning $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, the algorithm's
$\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}\mathbf{A}\rrbracket_k$ has the Frobenius error of
$\llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k$, whatever the two
truncations choose.
[TroppYurtseverUdellCevher2017, §6.2, (6.3)]. -/
theorem HasOrthonormalCols.frobNorm_sub_truncatedSVD_rsvd [DecidableEq q] {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q)
    (hQY : LinearMap.range Q.mulVecLin = LinearMap.range (A * Ω).mulVecLin) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) = frobNorm (A - Q * truncatedSVD (Qᴴ * A) k) := by
  have hP : rangeProjector (A * Ω) = Q * Qᴴ := by
    rw [← rangeProjector_inj.mpr hQY, hQ.rangeProjector_eq]
  have hr : rsvd A Ω = Q * (Qᴴ * A) := by
    change rangeProjector (A * Ω) * A = _
    rw [hP, Matrix.mul_assoc]
  have h1 : IsBestRankApprox (rsvd A Ω) k (Q * truncatedSVD (Qᴴ * A) k) := by
    rw [hr]
    exact hQ.isBestRankApprox_mul_iff.mpr (isBestRankApprox_truncatedSVD _ _)
  refine (sq_eq_sq₀ (frobNorm_nonneg _) (frobNorm_nonneg _)).mp ?_
  rw [frobNorm_sub_truncatedSVD_rsvd_sq, h1.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add,
    h1.frobNorm_sub]

/-- **Gu's projected form**: with $\mathbf{T} = \llbracket\mathbf{A}\rrbracket_k$ and
$\mathbf{P} = \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$,
$$\|\mathbf{A} - \llbracket\mathbf{P}\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathbf{T}\|_{\mathsf{F}}^2 +
\|\mathbf{T} - \mathbf{P}\mathbf{T}\|_{\mathsf{F}}^2\,,$$
for every test matrix (no rank hypothesis). Since
$\mathbf{T} = \mathbf{A}\mathbf{P}_{\mathbf{T}^{\mathsf{H}}}$,
$$\|\mathbf{T} - \mathbf{P}\mathbf{T}\|_{\mathsf{F}} \le
\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}\,,$$
so for every test matrix this is at least as sharp as the Frobenius-squared truncation lemma
(`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_rsvd_sq_add`) and, under the rank
hypothesis of the range finder, as truncation for free
(`NLAlib.HasOrthonormalCols.frobNorm_sub_mul_truncatedSVD_sq_le`).
[TroppYurtseverUdellCevher2017a, App. A.5]; [Gu2015, Theorem 3.5] as applied there; there for
$\mathbf{A}^{1/2}$, here any matrix and test matrix. -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_sq_add
    (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 ≤
      frobNorm (A - truncatedSVD A k) ^ 2 +
        frobNorm (truncatedSVD A k - rangeProjector (A * Ω) * truncatedSVD A k) ^ 2 := by
  classical
  have hP := isStarProjection_rangeProjector (A * Ω)
  rw [frobNorm_sub_truncatedSVD_rsvd_sq]
  have hEY : frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) ≤
      frobNorm (rsvd A Ω - rangeProjector (A * Ω) * truncatedSVD A k) :=
    frobNorm_sub_truncatedSVD_le_of_rank_le _
      ((Matrix.rank_mul_le_right _ _).trans (rank_truncatedSVD_le A k))
  have hsplit : frobNorm (A - rangeProjector (A * Ω) * truncatedSVD A k) ^ 2 =
      frobNorm (A - rsvd A Ω) ^ 2 +
        frobNorm (rsvd A Ω - rangeProjector (A * Ω) * truncatedSVD A k) ^ 2 := by
    have h := frobNorm_sub_mul_sq (rangeProjector (A * Ω)) A (truncatedSVD A k)
    rw [hP.rangeProjector_eq, ← sub_rsvd] at h
    exact h
  have hR := mul_rangeProjector_conjTranspose_truncatedSVD A k
  have hTR : truncatedSVD A k * rangeProjector (truncatedSVD A k)ᴴ = truncatedSVD A k := by
    have h := congrArg Matrix.conjTranspose (rangeProjector_mul_self (truncatedSVD A k)ᴴ)
    rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector,
      Matrix.conjTranspose_conjTranspose] at h
  have hcross : frobInner (A - truncatedSVD A k)
      (truncatedSVD A k - rangeProjector (A * Ω) * truncatedSVD A k) = 0 := by
    have e : truncatedSVD A k - rangeProjector (A * Ω) * truncatedSVD A k =
        (1 - rangeProjector (A * Ω)) * A * rangeProjector (truncatedSVD A k)ᴴ := by
      rw [Matrix.mul_assoc, hR, Matrix.sub_mul, Matrix.one_mul]
    rw [e, frobInner_comm, frobInner_mul_right, conjTranspose_rangeProjector,
      Matrix.sub_mul A (truncatedSVD A k), hR, hTR, sub_self, frobInner_zero_right]
  have hpy := frobNorm_add_sq_of_frobInner_eq_zero hcross
  rw [show A - truncatedSVD A k + (truncatedSVD A k - rangeProjector (A * Ω) * truncatedSVD A k) =
    A - rangeProjector (A * Ω) * truncatedSVD A k by abel] at hpy
  have := pow_le_pow_left₀ (frobNorm_nonneg _) hEY 2
  linarith

/-! ### Truncated Nyström -/

/-- **Truncated Nyström in every unitarily invariant norm**: for positive semidefinite
$\mathbf{H}$,
$$\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\rrbracket_k\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} +
\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_{\Phi}\,.$$
[MartinssonTropp2020, §14.3]; [TroppYurtseverUdellCevher2017a, Theorem 4.2 (proof)]; there inside an
expectation with constant two, here constant one by domination.
Result: truncation-lemma -/
theorem SymmetricGauge.matrixNorm_sub_truncatedSVD_nystrom_le (Φ : SymmetricGauge)
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (k : ℕ) :
    Φ.matrixNorm (H - truncatedSVD (nystrom H Ω) k) ≤
      Φ.matrixNorm (H - truncatedSVD H k) + Φ.matrixNorm (H - nystrom H Ω) :=
  (isBestRankApprox_truncatedSVD (nystrom H Ω) k).matrixNorm_sub_le_add_of_singularValues_le
    (hH.singularValues_nystrom_le Ω) Φ

/-- **Truncation under the Gram correspondence**: the trace error of truncated Nyström of
$\mathbf{F}^{\mathsf{H}}\mathbf{F}$ is the squared Frobenius error of the truncated randomized SVD
of $\mathbf{F}$,
$$\|\mathbf{F}^{\mathsf{H}}\mathbf{F} -
\llbracket\mathsf{nystrom}(\mathbf{F}^{\mathsf{H}}\mathbf{F}, \mathbf{\Omega})\rrbracket_k\|_*
= \|\mathbf{F} -
\llbracket\mathsf{rsvd}(\mathbf{F}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every factor, test matrix, rank and choice of truncation.
[TroppYurtseverUdellCevher2017a, App. A.5]; [MartinssonTropp2020, §14.2]; there in the proof of a
Nyström bound for $\mathbf{A}^{1/2}$ and a Gaussian test matrix, here any factor, deterministic.
Result: truncated-gram-correspondence -/
theorem nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom (F : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    nuclearNorm (Fᴴ * F - truncatedSVD (nystrom (Fᴴ * F) Ω) k) =
      frobNorm (F - truncatedSVD (rsvd F Ω) k) ^ 2 := by
  have h1 : (Fᴴ * F - (rsvd F Ω)ᴴ * rsvd F Ω).PosSemidef := by
    rw [← nystrom_conjTranspose_mul_self, conjTranspose_mul_self_sub_nystrom]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have h2 : ((rsvd F Ω)ᴴ * rsvd F Ω - truncatedSVD ((rsvd F Ω)ᴴ * rsvd F Ω) k).PosSemidef :=
    Matrix.le_iff.mp ((Matrix.posSemidef_conjTranspose_mul_self _).truncatedSVD_le k)
  have h3 := nuclearNorm_conjTranspose_mul_self_sub_nystrom F Ω
  rw [nystrom_conjTranspose_mul_self] at h3
  rw [nystrom_conjTranspose_mul_self,
    show Fᴴ * F - truncatedSVD ((rsvd F Ω)ᴴ * rsvd F Ω) k =
      (Fᴴ * F - (rsvd F Ω)ᴴ * rsvd F Ω) +
        ((rsvd F Ω)ᴴ * rsvd F Ω - truncatedSVD ((rsvd F Ω)ᴴ * rsvd F Ω) k) by abel,
    (h1.add h2).nuclearNorm_eq_re_trace, Matrix.trace_add, map_add,
    ← h1.nuclearNorm_eq_re_trace, ← h2.nuclearNorm_eq_re_trace, h3,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD, frobNorm_sub_truncatedSVD_rsvd_sq]

open scoped Classical in
/-- **Truncation under the Gram correspondence**, positive semidefinite form: with
$\mathbf{F} = \mathbf{H}^{1/2}$,
$$\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\rrbracket_k\|_*
= \|\mathbf{H}^{1/2} -
\llbracket\mathsf{rsvd}(\mathbf{H}^{1/2}, \mathbf{\Omega})\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
[TroppYurtseverUdellCevher2017a, App. A.5]; [MartinssonTropp2020, §14.2].
Result: truncated-gram-correspondence -/
theorem _root_.Matrix.PosSemidef.nuclearNorm_sub_truncatedSVD_nystrom {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (k : ℕ) :
    nuclearNorm (H - truncatedSVD (nystrom H Ω) k) =
      frobNorm (CFC.sqrt H - truncatedSVD (rsvd (CFC.sqrt H) Ω) k) ^ 2 := by
  have hR : (CFC.sqrt H)ᴴ = CFC.sqrt H :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian.eq
  have hHF : (CFC.sqrt H)ᴴ * CFC.sqrt H = H := by rw [hR, CFC.sqrt_mul_sqrt_self H hH.nonneg]
  have h := nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom (CFC.sqrt H) Ω k
  rwa [hHF] at h

/-- **The trace error of truncated Nyström under any choice of the truncation**: for positive
semidefinite $\mathbf{H}$ and any best rank-$k$ approximation $\mathbf{Y}$ of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$,
$$\|\mathbf{H} - \mathbf{Y}\|_* \le
\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\rrbracket_k\|_*\,,$$
the right side being choice-free
(`NLAlib.nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom`). With reverse Eckart–Young
(`NLAlib.specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_rank_le`) it turns a trace bound for
truncated Nyström into a spectral bound for every choice of the truncation. -/
theorem
_root_.Matrix.PosSemidef.nuclearNorm_sub_le_nuclearNorm_sub_truncatedSVD_nystrom_of_isBestRankApprox
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) {Ω : Matrix n l 𝕜} {k : ℕ} {Y : Matrix n n 𝕜}
    (hY : IsBestRankApprox (nystrom H Ω) k Y) :
    nuclearNorm (H - Y) ≤ nuclearNorm (H - truncatedSVD (nystrom H Ω) k) := by
  have h1 : (H - nystrom H Ω).PosSemidef := Matrix.le_iff.mp (hH.nystrom_le Ω)
  have h2 : (nystrom H Ω - truncatedSVD (nystrom H Ω) k).PosSemidef :=
    Matrix.le_iff.mp ((hH.nystrom Ω).truncatedSVD_le k)
  have hY' : nuclearNorm (nystrom H Ω - Y) =
      nuclearNorm (nystrom H Ω - truncatedSVD (nystrom H Ω) k) := by
    simpa only [lpGauge_one_matrixNorm] using hY.matrixNorm_sub (lpGauge 1 le_rfl)
  calc nuclearNorm (H - Y) = nuclearNorm ((H - nystrom H Ω) + (nystrom H Ω - Y)) := by
        rw [sub_add_sub_cancel]
    _ ≤ nuclearNorm (H - nystrom H Ω) + nuclearNorm (nystrom H Ω - Y) := nuclearNorm_add_le _ _
    _ = nuclearNorm (H - truncatedSVD (nystrom H Ω) k) := by
      rw [hY', h1.nuclearNorm_eq_re_trace, h2.nuclearNorm_eq_re_trace, ← map_add,
        ← Matrix.trace_add, sub_add_sub_cancel,
        (Matrix.le_iff.mp (hH.truncatedSVD_nystrom_le Ω k)).nuclearNorm_eq_re_trace]

/-! ### Truncated generalized Nyström -/

/-- The core form of truncated generalized Nyström: in a basis $\mathbf{Q}$ of
$\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, the truncation is $\mathbf{Q}\mathbf{Y}$ with
$\mathbf{Y}$ a best approximation of $\mathbf{Q}^{\mathsf{H}}\mathbf{A} + \mathbf{N}_0$, the error
splits off $\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2$, and the core quantities have the
basis-free values. -/
private theorem exists_core_generalizedNystrom {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Ψ : Matrix m p 𝕜} (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    ∃ C E Y : Matrix (Fin (A * Ω).rank) n 𝕜, IsBestRankApprox (C + E) k Y ∧
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 =
        frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (C - Y) ^ 2 ∧
      frobNorm (C - truncatedSVD C k) = frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) ∧
      singularValues E = singularValues (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) := by
  classical
  obtain ⟨Q, hQ, hQY⟩ := exists_hasOrthonormalCols_range_eq (p := Fin (A * Ω).rank) (A * Ω)
    (Fintype.card_fin _)
  have hΨQ : (Ψᴴ * Q).rank = Q.rank := by
    rw [Matrix.rank_mul_eq_iff_injOn, hQY]
    exact Matrix.rank_mul_eq_iff_injOn.mp h
  have hP : rangeProjector (A * Ω) = Q * Qᴴ := by
    rw [← rangeProjector_inj.mpr hQY, hQ.rangeProjector_eq]
  have hG : generalizedNystrom A Ω Ψ = Q * sketchAndSolve Q Ψᴴ A :=
    generalizedNystrom_eq_mul_sketchAndSolve hQY h
  have hX := hQ.sketchAndSolve_eq_add hΨQ A
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, N₀ = sketchAndSolve Q Ψᴴ ((1 - Q * Qᴴ) * A) := ⟨_, rfl⟩
  rw [← hN₀] at hX
  refine ⟨Qᴴ * A, N₀, Qᴴ * truncatedSVD (Q * (Qᴴ * A + N₀)) k,
    hQ.isBestRankApprox_conjTranspose_mul_truncatedSVD _ k, ?_, ?_, ?_⟩
  · have hT := (hQ.mul_conjTranspose_mul_truncatedSVD (Qᴴ * A + N₀) k).symm
    rw [hG, hX]
    conv_lhs => rw [hT]
    rw [hQ.frobNorm_sub_mul_sq, sub_rsvd, hP]
  · have hr : rsvd A Ω = Q * (Qᴴ * A) := by
      change rangeProjector (A * Ω) * A = _
      rw [hP, Matrix.mul_assoc]
    rw [hr, ← lpGauge_two_matrixNorm, ← lpGauge_two_matrixNorm]
    exact SymmetricGauge.matrixNorm_congr _ (funext fun i => by
      rw [singularValues_sub_truncatedSVD, singularValues_sub_truncatedSVD,
        hQ.singularValues_mul_left])
  · rw [sub_rsvd, hP, ← obliqueProjector_eq_of_range_eq hΨQ hQY, ← mul_sketchAndSolve,
      hQ.singularValues_mul_left, hN₀]

/-- **The truncated generalized Nyström error, deterministic form.** For
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
and any $k$, with $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and the core noise
$$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})\,,$$
$\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}$ the oblique projector
`obliqueProjector (A * Ω) Ψᴴ`,
$$\|\mathbf{A} -
\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 + \bigl(\|\mathbf{R} -
\llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}} +
2\,\|\llbracket\mathbf{N}\rrbracket_{2k}\|_{\mathsf{F}}\bigr)^2\,,$$
for every choice of the truncations. The rank hypothesis is necessary.
Proved without a literature source; the input is von Neumann's trace inequality
[HornJohnson2013, Theorem 7.4.1.1]. Related: [TroppYurtseverUdellCevher2017, Proposition 6.1].
Result: perturbed-truncation -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - rsvd A Ω) ^ 2 +
        (frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) +
          2 * frobNorm
            (truncatedSVD (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) (2 * k))) ^ 2 := by
  obtain ⟨C, E, Y, hY, hsplit, hC, hE⟩ := exists_core_generalizedNystrom h k
  have hb := hY.frobNorm_sub_le_add_frobNorm_truncatedSVD
  have hEq : frobNorm (truncatedSVD E (2 * k)) =
      frobNorm (truncatedSVD (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) (2 * k)) := by
    rw [← lpGauge_two_matrixNorm, ← lpGauge_two_matrixNorm]
    exact SymmetricGauge.matrixNorm_congr _ (funext fun i => by
      rw [singularValues_truncatedSVD, singularValues_truncatedSVD, hE])
  rw [hsplit, ← hC, ← hEq]
  have := pow_le_pow_left₀ (frobNorm_nonneg _) hb 2
  linarith

/-- **The truncated generalized Nyström error, spectral form.** For
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
and any $k$, with $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and the core noise
$$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})\,,$$
$\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}$ the oblique projector
`obliqueProjector (A * Ω) Ψᴴ`,
$$\|\mathbf{A} -
\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2
\le \|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 + \bigl(\|\mathbf{R} -
\llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}} +
2\sqrt{2k}\,\|\mathbf{N}\|_2\bigr)^2\,,$$
the form of `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_frobNorm_truncatedSVD`
with the spectral norm of the core noise, the shape truncated generalized Nyström in expectation
consumes.
Proved without a literature source. Related: [TroppYurtseverUdellCevher2017, Proposition 6.1].
Result: perturbed-truncation -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - rsvd A Ω) ^ 2 +
        (frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) +
          2 * √(2 * (k : ℝ)) * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω))) ^ 2 := by
  obtain ⟨C, E, Y, hY, hsplit, hC, hE⟩ := exists_core_generalizedNystrom h k
  have hb := hY.frobNorm_sub_le_add_specNorm
  have hEq : specNorm E = specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) := by
    rw [← singularValues_zero_eq_specNorm, ← singularValues_zero_eq_specNorm, hE]
  rw [hsplit, ← hC, ← hEq]
  have := pow_le_pow_left₀ (frobNorm_nonneg _) hb 2
  linarith

/-! ### Truncation as a projection -/

-- Stage B4

/-- **The truncated randomized SVD is a projection of $\mathbf{A}$**: with
$\mathbf{T} = \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k$,
$$\mathbf{T} = \mathbf{P}_{\mathbf{T}}\mathbf{A}\,,$$
since the leading left singular vectors of $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$ lie in
the range of $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$. Its error
$\mathbf{A} - \mathbf{T} = (\mathbf{I} - \mathbf{P}_{\mathbf{T}})\mathbf{A}$ is therefore a
projection residual. [MuscoMusco2015, Lemma 2 (proof)]. -/
theorem truncatedSVD_rsvd_eq_rangeProjector_mul (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    truncatedSVD (rsvd A Ω) k = rangeProjector (truncatedSVD (rsvd A Ω) k) * A := by
  have hle : LinearMap.range (truncatedSVD (rsvd A Ω) k).mulVecLin ≤
      LinearMap.range (A * Ω).mulVecLin :=
    (range_truncatedSVD_le _ k).trans (range_rsvd_le A Ω)
  calc truncatedSVD (rsvd A Ω) k
      = rangeProjector (truncatedSVD (rsvd A Ω) k) * rsvd A Ω :=
        (rangeProjector_truncatedSVD_mul _ k).symm
    _ = rangeProjector (truncatedSVD (rsvd A Ω) k) * (rangeProjector (A * Ω) * A) := rfl
    _ = rangeProjector (truncatedSVD (rsvd A Ω) k) * A := by
        rw [← Matrix.mul_assoc, rangeProjector_mul_rangeProjector_of_range_le' hle]

/-- **The truncated randomized SVD improves with the rank**: for $k \le k'$ and every $i$,
$$\sigma_i(\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_{k'}) \le
\sigma_i(\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k)\,,$$
so in every unitarily invariant norm. Stated for the chosen truncation: with ties among the
singular values of $\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ two arbitrary best approximations
need not be nested. [MuscoMusco2015, Theorem 10 (proof)]. -/
theorem singularValues_sub_truncatedSVD_rsvd_le_of_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    {k k' : ℕ} (h : k ≤ k') (i : ℕ) :
    singularValues (A - truncatedSVD (rsvd A Ω) k') i ≤
      singularValues (A - truncatedSVD (rsvd A Ω) k) i := by
  classical
  have hsub (j : ℕ) : A - truncatedSVD (rsvd A Ω) j =
      (1 - rangeProjector (truncatedSVD (rsvd A Ω) j)) * A := by
    conv_lhs => rw [truncatedSVD_rsvd_eq_rangeProjector_mul A Ω j]
    rw [Matrix.sub_mul, Matrix.one_mul]
  rw [hsub k', hsub k]
  exact singularValues_one_sub_rangeProjector_mul_le_of_range_le
    (range_truncatedSVD_mono _ h) A i

end NLAlib
