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
  Nyström, from its core form `NLAlib.exists_core_generalizedNystrom`.
* `NLAlib.truncatedSVD_rsvd_eq_rangeProjector_mul`,
  `NLAlib.singularValues_sub_truncatedSVD_rsvd_le_of_le`: the truncated randomized SVD is a
  projection of $\mathbf{A}$, and its error decreases with the rank.
* `NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq`:
  truncated generalized Nyström never beats the truncated randomized SVD.
* `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm`: the
  perturbed truncation with the next-$k$ tail in the cross term.
* `NLAlib.le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq`: the reverse perturbed truncation,
  under a gap. The last two are new (research note OP2 of the NLAlib workflow, and
  `docs/design/LowRank-EstimatorLowerBounds.md` §3.2).
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
  have h := (lpGauge 2).matrixNorm_sub_truncatedSVD_le_of_singularValues_le
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
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
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

/-- The trace error of truncated Nyström under any choice of the truncation: for positive
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
    simpa only [lpGauge_one_matrixNorm] using hY.matrixNorm_sub (lpGauge 1)
  calc nuclearNorm (H - Y) = nuclearNorm ((H - nystrom H Ω) + (nystrom H Ω - Y)) := by
        rw [sub_add_sub_cancel]
    _ ≤ nuclearNorm (H - nystrom H Ω) + nuclearNorm (nystrom H Ω - Y) := nuclearNorm_add_le _ _
    _ = nuclearNorm (H - truncatedSVD (nystrom H Ω) k) := by
      rw [hY', h1.nuclearNorm_eq_re_trace, h2.nuclearNorm_eq_re_trace, ← map_add,
        ← Matrix.trace_add, sub_add_sub_cancel,
        (Matrix.le_iff.mp (hH.truncatedSVD_nystrom_le Ω k)).nuclearNorm_eq_re_trace]

/-! ### Truncated generalized Nyström -/

/-- The core form of truncated generalized Nyström: for $\mathbf{A} \in \Bbbk^{m \times n}$,
$\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and $\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
and any $k$, there are an orthonormal basis $\mathbf{Q}$ of
$\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, a core noise $\mathbf{E}$ with
$\mathbf{Q}\mathbf{E} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, and a best
rank-$k$ approximation $\mathbf{Y}$ of $\mathbf{Q}^{\mathsf{H}}\mathbf{A} + \mathbf{E}$ with
$$\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k =
\mathbf{Q}\mathbf{Y}\,,\qquad
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 = \|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 +
\|\mathbf{Q}^{\mathsf{H}}\mathbf{A} - \mathbf{Y}\|_{\mathsf{F}}^2\,;$$
the core $\mathbf{Q}^{\mathsf{H}}\mathbf{A}$ has the truncation error of $\mathbf{R}$ and
$\mathbf{E}$ the singular values of the core noise. For the choice `truncatedSVD` makes.
Proved without a literature source. -/
theorem exists_core_generalizedNystrom {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Ψ : Matrix m p 𝕜} (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    ∃ (Q : Matrix m (Fin (A * Ω).rank) 𝕜) (E Y : Matrix (Fin (A * Ω).rank) n 𝕜),
      HasOrthonormalCols Q ∧ rangeProjector (A * Ω) = Q * Qᴴ ∧
      Q * E = obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω) ∧
      IsBestRankApprox (Qᴴ * A + E) k Y ∧
      truncatedSVD (generalizedNystrom A Ω Ψ) k = Q * Y ∧
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 =
        frobNorm (A - rsvd A Ω) ^ 2 + frobNorm (Qᴴ * A - Y) ^ 2 ∧
      frobNorm (Qᴴ * A - truncatedSVD (Qᴴ * A) k) =
        frobNorm (rsvd A Ω - truncatedSVD (rsvd A Ω) k) ∧
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
  have hQN : Q * N₀ = obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω) := by
    rw [sub_rsvd, hP, ← obliqueProjector_eq_of_range_eq hΨQ hQY, ← mul_sketchAndSolve, hN₀]
  have hT := (hQ.mul_conjTranspose_mul_truncatedSVD (Qᴴ * A + N₀) k).symm
  refine ⟨Q, N₀, Qᴴ * truncatedSVD (Q * (Qᴴ * A + N₀)) k, hQ, hP, hQN,
    hQ.isBestRankApprox_conjTranspose_mul_truncatedSVD _ k, ?_, ?_, ?_, ?_⟩
  · rw [hG, hX]
    exact hT
  · rw [hG, hX]
    conv_lhs => rw [hT]
    rw [hQ.frobNorm_sub_mul_sq, sub_rsvd, hP]
  · have hr : rsvd A Ω = Q * (Qᴴ * A) := by
      change rangeProjector (A * Ω) * A = _
      rw [hP, Matrix.mul_assoc]
    rw [hr, ← lpGauge_two_matrixNorm, ← lpGauge_two_matrixNorm]
    exact SymmetricGauge.matrixNorm_congr _ (funext fun i => by
      rw [singularValues_sub_truncatedSVD, singularValues_sub_truncatedSVD,
        hQ.singularValues_mul_left])
  · rw [← hQN, hQ.singularValues_mul_left]

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
  obtain ⟨Q, E, Y, -, -, -, hY, -, hsplit, hC, hE⟩ := exists_core_generalizedNystrom h k
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
  obtain ⟨Q, E, Y, -, -, -, hY, -, hsplit, hC, hE⟩ := exists_core_generalizedNystrom h k
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

/-! ### Sharpened and reverse perturbed truncation -/

section NextK

/-- Truncated generalized Nyström never beats the truncated randomized SVD: for
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$
has the rank of $\mathbf{A}\mathbf{\Omega}$, and any $k$,
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
\le
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2\,:$$
both outputs lie in $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, and the truncated randomized
SVD
is the best rank-$k$ approximation there. For the choice `truncatedSVD` makes. -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 := by
  obtain ⟨Q, E, Y, -, -, -, hY, -, hsplit, hC, -⟩ := exists_core_generalizedNystrom h k
  have hEY : frobNorm (Qᴴ * A - truncatedSVD (Qᴴ * A) k) ≤ frobNorm (Qᴴ * A - Y) :=
    frobNorm_sub_truncatedSVD_le_of_rank_le _ hY.rank_le
  rw [hsplit, frobNorm_sub_truncatedSVD_rsvd_sq, ← hC]
  have := pow_le_pow_left₀ (frobNorm_nonneg _) hEY 2
  linarith

/-- A best approximation is the projection of the target onto its own column space:
$\mathbf{P}_{\mathbf{Y}}\mathbf{M} = \mathbf{Y}$. -/
private theorem IsBestRankApprox.rangeProjector_self_mul {M Y : Matrix m n 𝕜} {k : ℕ}
    (hY : IsBestRankApprox M k Y) : rangeProjector Y * M = Y := by
  classical
  have hsplit := (isStarProjection_rangeProjector Y).frobNorm_sq_eq_add (M - Y)
  have e1 : rangeProjector Y * (M - Y) = rangeProjector Y * M - Y := by
    rw [Matrix.mul_sub, rangeProjector_mul_self]
  have e2 : (1 - rangeProjector Y) * (M - Y) = M - rangeProjector Y * M := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.one_mul,
      rangeProjector_mul_self, sub_self, sub_zero]
  rw [e1, e2] at hsplit
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _) (hY.frobNorm_sub_le _
    ((Matrix.rank_mul_le_left (rangeProjector Y) M).trans
      (by rw [rank_rangeProjector]; exact hY.rank_le))) 2
  have hsq : frobNorm (rangeProjector Y * M - Y) ^ 2 = 0 :=
    le_antisymm (by linarith) (sq_nonneg _)
  exact sub_eq_zero.mp (frobNorm_eq_zero_iff.mp (pow_eq_zero_iff two_ne_zero |>.mp hsq))

/-- The scalar step of the next-$k$ perturbed truncation. -/
private theorem le_add_mul_of_le_two_mul {S a w u q γ s r e : ℝ} (hs : 0 ≤ s) (he : 0 ≤ e)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hr2 : r ^ 2 = 2) (hqγ : q ≤ γ)
    (h1 : S ≤ 2 * (r * s * u * e + w)) (h2 : S = a - q ^ 2 + w) (h3 : u ^ 2 = a + q ^ 2)
    (hw : w ≤ s ^ 2 * e ^ 2) :
    S ≤ 4 * s * e * γ + 12 * s ^ 2 * e ^ 2 := by
  have hr3 : r ≤ 3 / 2 := by nlinarith
  have hsq : (u - r * s * e) ^ 2 ≤ (2 * s * e + r * q) ^ 2 := by
    have e1 : (u - r * s * e) ^ 2 = u ^ 2 - 2 * (r * s * u * e) + r ^ 2 * (s * e) ^ 2 := by ring
    have e2 : (2 * s * e + r * q) ^ 2 =
        4 * (s * e) ^ 2 + 4 * (r * s * e * q) + r ^ 2 * q ^ 2 := by ring
    rw [e1, e2, hr2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hr hs) he) hq]
  have hu' : u ≤ (r + 2) * s * e + r * q := by
    nlinarith [(abs_le_of_sq_le_sq' hsq (by positivity)).2]
  have hse : 0 ≤ r * s * e := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hu' hse, mul_le_mul_of_nonneg_left hqγ (mul_nonneg hs he),
    mul_le_mul_of_nonneg_right hr3 (sq_nonneg (s * e))]

/-- The optimality step of perturbed truncation: for any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 -
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 \le
2\langle\mathbf{Y} - \llbracket\mathbf{C}\rrbracket_k, \mathbf{E}\rangle_{\mathsf{F}}\,.$$ -/
private theorem IsBestRankApprox.frobNorm_sub_sq_sub_le_two_mul_frobInner
    {C E Y : Matrix m n 𝕜} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ^ 2 - frobNorm (C - truncatedSVD C k) ^ 2 ≤
      2 * frobInner (Y - truncatedSVD C k) E := by
  have hopt := pow_le_pow_left₀ (frobNorm_nonneg _)
    (hY.frobNorm_sub_le (truncatedSVD C k) (rank_truncatedSVD_le C k)) 2
  have e1 : frobNorm (C - Y) ^ 2 =
      frobNorm (C + E - Y) ^ 2 - 2 * frobInner (C + E - Y) E + frobNorm E ^ 2 := by
    rw [← frobNorm_sub_sq, show C + E - Y - E = C - Y by abel]
  have e2 : frobNorm (C + E - truncatedSVD C k) ^ 2 =
      frobNorm (C - truncatedSVD C k) ^ 2 + 2 * frobInner (C - truncatedSVD C k) E +
        frobNorm E ^ 2 := by
    rw [← frobNorm_add_sq, show C - truncatedSVD C k + E = C + E - truncatedSVD C k by abel]
  have e3 : frobInner (C - truncatedSVD C k) E - frobInner (C + E - Y) E =
      frobInner (Y - truncatedSVD C k) E - frobNorm E ^ 2 := by
    rw [← frobInner_self, ← frobInner_sub_left, ← frobInner_sub_left]
    congr 1
    abel
  linarith

/-- The next-$k$ perturbed truncation in core coordinates: for any best rank-$k$ approximation
$\mathbf{Y}$ of $\mathbf{C} + \mathbf{E}$, with $\gamma_k =
\|\llbracket\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$,
$$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2 \le
\|\mathbf{C} - \llbracket\mathbf{C}\rrbracket_k\|_{\mathsf{F}}^2 +
4\sqrt{k}\,\|\mathbf{E}\|_2\,\gamma_k + 12k\,\|\mathbf{E}\|_2^2\,.$$ -/
private theorem IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm
    {C E Y : Matrix m n 𝕜} {k : ℕ} (hY : IsBestRankApprox (C + E) k Y) :
    frobNorm (C - Y) ^ 2 ≤ frobNorm (C - truncatedSVD C k) ^ 2 +
      4 * √(k : ℝ) * specNorm E * frobNorm (truncatedSVD (C - truncatedSVD C k) k) +
      12 * k * specNorm E ^ 2 := by
  classical
  set T := truncatedSVD C k with hT
  set B₂ := C - T with hB₂
  set P := rangeProjector Y with hPdef
  have hP : IsStarProjection P := isStarProjection_rangeProjector Y
  have hPY : P * (C + E) = Y := hY.rangeProjector_self_mul
  have hY' : Y = P * C + P * E := by rw [← hPY, Matrix.mul_add]
  have hrP : P.rank ≤ k := by rw [hPdef, rank_rangeProjector]; exact hY.rank_le
  have hrT : T.rank ≤ k := rank_truncatedSVD_le C k
  -- (D1) the optimality of `Y` against `T`
  have hS : frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2 ≤ 2 * frobInner (Y - T) E :=
    hY.frobNorm_sub_sq_sub_le_two_mul_frobInner
  -- (D2) the row spaces of `T` and `B₂` are orthogonal
  have hTPB : frobInner T (P * B₂) = 0 := by
    have hCQ : C * rangeProjector Tᴴ = T := mul_rangeProjector_conjTranspose_truncatedSVD C k
    have hTQ : T * rangeProjector Tᴴ = T :=
      calc T * rangeProjector Tᴴ = C * rangeProjector Tᴴ * rangeProjector Tᴴ := by
            rw [hCQ]
        _ = T := by rw [Matrix.mul_assoc, rangeProjector_mul_rangeProjector, hCQ]
    have hBQ : B₂ * rangeProjector Tᴴ = 0 := by rw [hB₂, Matrix.sub_mul, hCQ, hTQ, sub_self]
    nth_rw 1 [← hTQ]
    rw [frobInner_mul_right, conjTranspose_rangeProjector, Matrix.mul_assoc, hBQ, Matrix.mul_zero,
      frobInner_zero_right]
  have hCY : frobNorm (C - Y) ^ 2 = frobNorm (T - P * T) ^ 2 +
      (frobNorm B₂ ^ 2 - frobNorm (P * B₂) ^ 2) + frobNorm (P * E) ^ 2 := by
    have h1 : C - Y = (C - P * C) - P * E := by rw [hY']; abel
    have h0 : frobInner (C - P * C) (P * E) = 0 := by
      rw [frobInner_comm, frobInner_mul_left, hP.conjTranspose_eq, Matrix.mul_sub,
        ← Matrix.mul_assoc, hP.mul_self, sub_self, frobInner_zero_right]
    have h2 : C - P * C = (T - P * T) + (B₂ - P * B₂) := by rw [hB₂, Matrix.mul_sub]; abel
    have h3 : frobInner (T - P * T) (B₂ - P * B₂) = 0 := by
      rw [hP.frobInner_sub_mul_sub_mul, frobInner_sub_left, frobInner_mul_left,
        hP.conjTranspose_eq, hTPB, frobInner_truncatedSVD_sub C k, sub_zero]
    have h4 := hP.frobNorm_sq_eq_add B₂
    rw [Matrix.sub_mul, Matrix.one_mul] at h4
    rw [h1, frobNorm_sub_sq_of_frobInner_eq_zero h0, h2, frobNorm_add_sq_of_frobInner_eq_zero h3]
    linarith
  have hD : frobNorm (P * C - T) ^ 2 = frobNorm (T - P * T) ^ 2 + frobNorm (P * B₂) ^ 2 := by
    have h1 : P * C - T = P * B₂ - (T - P * T) := by rw [hB₂, Matrix.mul_sub]; abel
    have h0 : frobInner (P * B₂) (T - P * T) = 0 := by
      rw [frobInner_sub_right, frobInner_mul_left, frobInner_mul_left, hP.conjTranspose_eq,
        ← Matrix.mul_assoc, hP.mul_self, sub_self]
    rw [h1, frobNorm_sub_sq_of_frobInner_eq_zero h0]
    ring
  have hYT : frobInner (Y - T) E = frobInner (P * C - T) E + frobNorm (P * E) ^ 2 := by
    rw [hY', show P * C + P * E - T = (P * C - T) + P * E by abel, frobInner_add_left,
      ← frobInner_self, frobInner_mul_left P E (P * E), hP.conjTranspose_eq, ← Matrix.mul_assoc,
      hP.mul_self, frobInner_comm (P * E) E]
  -- the cross term sees rank `2k`, the noise term rank `k`
  have hDE : frobInner (P * C - T) E ≤
      √2 * √(k : ℝ) * frobNorm (P * C - T) * specNorm E := by
    have hrank : (P * C - T).rank ≤ 2 * k := (Matrix.rank_sub_le _ _).trans
      (by have := (Matrix.rank_mul_le_left P C).trans hrP; omega)
    have h := frobInner_le_sqrt_mul_frobNorm_mul_specNorm_of_rank_le hrank E
    rwa [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul zero_le_two] at h
  have hw : frobNorm (P * E) ^ 2 ≤ √(k : ℝ) ^ 2 * specNorm E ^ 2 := by
    rw [Real.sq_sqrt (Nat.cast_nonneg k)]
    exact (frobNorm_sq_le_rank_mul_specNorm_sq _).trans (mul_le_mul
      (by exact_mod_cast (Matrix.rank_mul_le_left P E).trans hrP)
      (pow_le_pow_left₀ (specNorm_nonneg _) (hP.specNorm_mul_le E) 2) (sq_nonneg _)
      (Nat.cast_nonneg k))
  -- Ky Fan for the rank-`k` projector `P`
  have hg : frobNorm (P * B₂) ≤ frobNorm (truncatedSVD B₂ k) := by
    have h1 := frobInner_le_frobNorm_mul_frobNorm_truncatedSVD_of_rank_le
      ((Matrix.rank_mul_le_left P B₂).trans hrP) B₂
    have h2 : frobInner (P * B₂) B₂ = frobNorm (P * B₂) ^ 2 := by
      rw [← frobInner_self, frobInner_mul_left P B₂ (P * B₂), frobInner_mul_left P B₂ B₂,
        hP.conjTranspose_eq, ← Matrix.mul_assoc, hP.mul_self]
    nlinarith [frobNorm_nonneg (P * B₂), frobNorm_nonneg (truncatedSVD B₂ k)]
  have h := le_add_mul_of_le_two_mul (S := frobNorm (C - Y) ^ 2 - frobNorm B₂ ^ 2)
    (a := frobNorm (T - P * T) ^ 2) (w := frobNorm (P * E) ^ 2) (Real.sqrt_nonneg (k : ℝ))
    (specNorm_nonneg E) (frobNorm_nonneg _) (Real.sqrt_nonneg 2) (Real.sq_sqrt zero_le_two)
    hg (by linarith) (by linarith) hD hw
  rw [Real.sq_sqrt (Nat.cast_nonneg k)] at h
  linarith

/-- The perturbed truncation with the next-$k$ tail: for
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$
has the rank of $\mathbf{A}\mathbf{\Omega}$, any $k$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})$,
the core noise $\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})$ and
$\gamma_k = \|\llbracket\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}
= (\sum_{k \le i < 2k}\sigma_i(\mathbf{R})^2)^{1/2}$,
$$\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
4\sqrt{k}\,\|\mathbf{N}\|_2\,\gamma_k + 12k\,\|\mathbf{N}\|_2^2\,.$$
Since $\gamma_k \le \min(\|\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}},
\sqrt{k}\,\sigma_k(\mathbf{R}))$, it sharpens the cross term $4\sqrt{2k}\,\gamma\,\|\mathbf{N}\|_2$
of `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm` (expanded), at the
price of $12k$ for $8k$ in the noise term. For the choice `truncatedSVD` makes.
No printed source. New (research note OP2, §2, D2, with the constants recomputed here). -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 +
        4 * √(k : ℝ) * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) *
          frobNorm (truncatedSVD (rsvd A Ω - truncatedSVD (rsvd A Ω) k) k) +
        12 * k * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 2 := by
  obtain ⟨Q, E, Y, hQ, hP, -, hY, -, hsplit, hC, hE⟩ := exists_core_generalizedNystrom h k
  have hEq : specNorm E = specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) := by
    rw [← singularValues_zero_eq_specNorm, ← singularValues_zero_eq_specNorm, hE]
  have hr : rsvd A Ω = Q * (Qᴴ * A) := by
    change rangeProjector (A * Ω) * A = _
    rw [hP, Matrix.mul_assoc]
  have hγ : frobNorm (truncatedSVD (Qᴴ * A - truncatedSVD (Qᴴ * A) k) k) =
      frobNorm (truncatedSVD (rsvd A Ω - truncatedSVD (rsvd A Ω) k) k) := by
    rw [hr, ← lpGauge_two_matrixNorm, ← lpGauge_two_matrixNorm]
    exact SymmetricGauge.matrixNorm_congr _ (funext fun i => by
      rw [singularValues_truncatedSVD, singularValues_truncatedSVD,
        singularValues_sub_truncatedSVD, singularValues_sub_truncatedSVD,
        hQ.singularValues_mul_left])
  have hb := hY.frobNorm_sub_sq_le_add_specNorm_mul_frobNorm
  rw [hsplit, frobNorm_sub_truncatedSVD_rsvd_sq, ← hγ, ← hC, ← hEq]
  linarith

/-- The error of $\mathbf{P}(\mathbf{R} + \mathbf{N})$, for an orthogonal projector
$\mathbf{P}$, splits into three orthogonal pieces along
$\mathbf{R} = \llbracket\mathbf{R}\rrbracket_k +
(\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k)$. -/
private theorem frobNorm_sub_mul_add_sq_eq_add [DecidableEq m] {R : Matrix m n 𝕜}
    (N : Matrix m n 𝕜) {P : Matrix m m 𝕜} (hP : IsStarProjection P) (k : ℕ) :
    frobNorm (R - P * (R + N)) ^ 2 = frobNorm ((1 - P) * truncatedSVD R k) ^ 2 +
      frobNorm ((1 - P) * (R - truncatedSVD R k)) ^ 2 + frobNorm (P * N) ^ 2 := by
  set T := truncatedSVD R k
  have hTS : T * (R - T)ᴴ = 0 := by
    have hV := isStarProjection_rangeProjector Tᴴ
    have hRV : R * rangeProjector Tᴴ = T := mul_rangeProjector_conjTranspose_truncatedSVD R k
    rw [← hRV, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hV.conjTranspose_eq,
      Matrix.mul_sub]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (rangeProjector Tᴴ) (rangeProjector Tᴴ), hV.mul_self, sub_self]
  have e : R - P * (R + N) = ((1 - P) * T + (1 - P) * (R - T)) - P * N := by
    rw [← Matrix.mul_add, add_sub_cancel, Matrix.mul_add, Matrix.sub_mul, Matrix.one_mul]
    abel
  have h0 : frobInner ((1 - P) * T + (1 - P) * (R - T)) (P * N) = 0 := by
    rw [← Matrix.mul_add, add_sub_cancel, frobInner_comm]
    exact hP.frobInner_mul_one_sub_mul N R
  rw [e, frobNorm_sub_sq_of_frobInner_eq_zero h0, frobNorm_add_sq_of_mul_conjTranspose_eq_zero]
  rw [Matrix.conjTranspose_mul, ← Matrix.mul_assoc, Matrix.mul_assoc _ T, hTS,
    Matrix.mul_zero, Matrix.zero_mul]

/-- The reverse perturbed truncation for an arbitrary orthogonal projector $\mathbf{P}$ of rank
at most $k$ applied to $\mathbf{R} + \mathbf{N}$. -/
private theorem le_frobNorm_sub_mul_add_sq {R N : Matrix m n 𝕜} {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k) (hk : 0 < k)
    (hgap : singularValues R k ^ 2 < singularValues R (k - 1) ^ 2) :
    frobNorm (R - truncatedSVD R k) ^ 2 + frobNorm (rangeProjector (truncatedSVD R k) * N) ^ 2 -
        frobNorm N ^ 4 / (singularValues R (k - 1) ^ 2 - singularValues R k ^ 2) ≤
      frobNorm (R - P * (R + N)) ^ 2 := by
  classical
  set T := truncatedSVD R k with hT
  set Pt := rangeProjector T
  set a := singularValues R (k - 1)
  set b := singularValues R k
  have hPt := isStarProjection_rangeProjector T
  have ha : 0 < a := by
    by_contra h0
    nlinarith [singularValues_nonneg R (k - 1), sq_nonneg b]
  have hrankT : T.rank = k := by
    rw [hT, rank_truncatedSVD, min_eq_left]
    have := (singularValues_pos_iff R).mp ha
    omega
  have hrankPt : Pt.rank = k := (rank_rangeProjector T).trans hrankT
  have hPtS : Pt * (R - T) = 0 := by
    rw [Matrix.mul_sub, rangeProjector_truncatedSVD_mul, rangeProjector_mul_self, sub_self]
  -- the right side splits into three orthogonal pieces
  have hrhs := frobNorm_sub_mul_add_sq_eq_add (R := R) N hP k
  have hS2 := hP.frobNorm_sq_eq_add (R - T)
  -- the leading block loses at least `a ^ 2 * t`
  have h4 : a ^ 2 * frobNorm ((1 - P) * Pt) ^ 2 ≤ frobNorm ((1 - P) * T) ^ 2 := by
    have hpinv : specNorm (pinv T) = a⁻¹ := by
      rw [specNorm_pinv T (k := k - 1) (by omega), hT, singularValues_truncatedSVD,
        if_pos (by omega)]
    have h := frobNorm_mul_le_frobNorm_mul_specNorm ((1 - P) * T) (pinv T)
    rw [Matrix.mul_assoc, mul_pinv, hpinv] at h
    have h' := (le_mul_inv_iff₀ ha).mp h
    rw [← mul_pow, mul_comm]
    exact pow_le_pow_left₀ (by positivity) h' 2
  have hflip : frobNorm (P * (1 - Pt)) = frobNorm ((1 - Pt) * P) := by
    rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, hP.conjTranspose_eq,
      hPt.one_sub.conjTranspose_eq]
  -- the trailing block gains at most `b ^ 2 * u`
  have h5 : frobNorm (P * (R - T)) ^ 2 ≤ b ^ 2 * frobNorm ((1 - Pt) * P) ^ 2 := by
    have e : P * (R - T) = P * (1 - Pt) * (R - T) := by
      rw [Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul, hPtS, sub_zero]
    have h := frobNorm_mul_le_frobNorm_mul_specNorm (P * (1 - Pt)) (R - T)
    rw [← e, hflip, hT, specNorm_sub_truncatedSVD, ← hT] at h
    have := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
    rw [mul_pow] at this
    linarith
  have hu : frobNorm ((1 - Pt) * P) ^ 2 ≤ frobNorm ((1 - P) * Pt) ^ 2 := by
    have h1 := hP.frobNorm_sq_eq_add Pt
    have h2 := hPt.frobNorm_sq_eq_add P
    have hflip' : frobNorm (Pt * P) = frobNorm (P * Pt) := by
      rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, hP.conjTranspose_eq,
        hPt.conjTranspose_eq]
    rw [hPt.frobNorm_sq_eq_rank, hrankPt] at h1
    rw [hP.frobNorm_sq_eq_rank, hflip'] at h2
    have : (P.rank : ℝ) ≤ k := by exact_mod_cast hPk
    linarith
  have hd : frobNorm (Pt - P) ^ 2 =
      frobNorm ((1 - P) * Pt) ^ 2 + frobNorm ((1 - Pt) * P) ^ 2 := by
    have e : Pt - P = (1 - P) * Pt - P * (1 - Pt) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
      abel
    have h0 : frobInner ((1 - P) * Pt) (P * (1 - Pt)) = 0 := by
      rw [frobInner_mul_left, hP.one_sub.conjTranspose_eq, ← Matrix.mul_assoc, Matrix.sub_mul,
        Matrix.one_mul, hP.mul_self, sub_self, Matrix.zero_mul, frobInner_zero_right]
    rw [e, frobNorm_sub_sq_of_frobInner_eq_zero h0, hflip]
  have h8 : frobNorm (Pt * N) ^ 2 - frobNorm (P * N) ^ 2 ≤ frobNorm (Pt - P) * frobNorm N ^ 2 := by
    have hq : ∀ X : Matrix m m 𝕜, IsStarProjection X →
        frobNorm (X * N) ^ 2 = frobInner N (X * N) := fun X hX => by
      rw [← frobInner_self, frobInner_mul_left, hX.conjTranspose_eq, ← Matrix.mul_assoc,
        hX.mul_self]
    rw [hq Pt hPt, hq P hP, ← frobInner_sub_right, ← Matrix.sub_mul]
    refine (frobInner_le _ _).trans ?_
    nlinarith [mul_le_mul_of_nonneg_left (frobNorm_mul_le (Pt - P) N) (frobNorm_nonneg N)]
  have hg : 0 < a ^ 2 - b ^ 2 := by linarith
  have hw : frobNorm N ^ 4 / (a ^ 2 - b ^ 2) * (a ^ 2 - b ^ 2) = frobNorm N ^ 4 :=
    div_mul_cancel₀ _ hg.ne'
  have hde : 2 * frobNorm (Pt - P) * frobNorm N ^ 2 ≤
      (a ^ 2 - b ^ 2) * frobNorm (Pt - P) ^ 2 + frobNorm N ^ 4 / (a ^ 2 - b ^ 2) := by
    refine le_of_mul_le_mul_left ?_ hg
    nlinarith [sq_nonneg ((a ^ 2 - b ^ 2) * frobNorm (Pt - P) - frobNorm N ^ 2)]
  have hw0 : 0 ≤ frobNorm N ^ 4 / (a ^ 2 - b ^ 2) := by positivity
  rw [hrhs]
  nlinarith [mul_le_mul_of_nonneg_left hu (by positivity : (0 : ℝ) ≤ a ^ 2 + b ^ 2)]

/-- The reverse perturbed truncation: for $\mathbf{A} \in \Bbbk^{m \times n}$,
$\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and $\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
$k \ge 1$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ with a gap
$g = \sigma_{k-1}(\mathbf{R})^2 - \sigma_k(\mathbf{R})^2 > 0$, and the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$,
$$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2 -
\frac{\|\mathbf{N}\|_{\mathsf{F}}^4}{g} \le
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
Truncated generalized Nyström keeps the noise that falls in the dominant subspace of
$\mathbf{R}$, up to a perturbation that vanishes as the gap grows. For the choice
`truncatedSVD` makes (the left side is choice-free under the gap).
No printed source. New (this design, §3.2, after research note OP2, §1). -/
theorem le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) {k : ℕ} (hk : 0 < k)
    (hgap : singularValues (rsvd A Ω) k ^ 2 < singularValues (rsvd A Ω) (k - 1) ^ 2) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 +
        frobNorm (rangeProjector (truncatedSVD (rsvd A Ω) k) *
          (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω))) ^ 2 -
        frobNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 4 /
          (singularValues (rsvd A Ω) (k - 1) ^ 2 - singularValues (rsvd A Ω) k ^ 2) ≤
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 := by
  classical
  obtain ⟨Q, E, Y, hQ, hP, hQE, hY, hZ, hsplit, -, -⟩ := exists_core_generalizedNystrom h k
  have hR : rsvd A Ω = Q * (Qᴴ * A) := by
    change rangeProjector (A * Ω) * A = _
    rw [hP, Matrix.mul_assoc]
  have hPZ : rangeProjector (Q * Y) * (rsvd A Ω + Q * E) = Q * Y := by
    rw [hQ.rangeProjector_mul, hR, ← Matrix.mul_add, Matrix.mul_assoc, Matrix.mul_assoc,
      ← Matrix.mul_assoc Qᴴ, hQ.conjTranspose_mul_self, Matrix.one_mul,
      hY.rangeProjector_self_mul]
  have hYk : (rangeProjector (Q * Y)).rank ≤ k := by
    rw [rank_rangeProjector, hQ.rank_mul]
    exact hY.rank_le
  have key := le_frobNorm_sub_mul_add_sq (N := Q * E) (isStarProjection_rangeProjector (Q * Y))
    hYk hk hgap
  rw [hPZ, hR, ← Matrix.mul_sub, ← hR] at key
  simp only [hQ.frobNorm_mul_left] at key
  rw [hsplit, frobNorm_sub_truncatedSVD_rsvd_sq, ← hQE, hQ.frobNorm_mul_left]
  linarith

end NextK

end NLAlib
