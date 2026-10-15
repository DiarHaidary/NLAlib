/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Gaussian.RangeFinderTail
public import NLAlib.RandomMatrix.Haar.Transfer

/-!
# The randomized SVD with a rotation-invariant test matrix

A random test matrix $\mathbf{X}$ of size $n \times \ell$ is rotation invariant when its law
$\nu$ is a left unitarily invariant probability measure (`NLAlib.IsLeftUnitarilyInvariant`:
$\mathbf{U}\mathbf{X}$ has the law of $\mathbf{X}$ for every orthogonal $\mathbf{U}$); with full
column rank almost surely this is the full-rank rotation-invariant embedding of Epperly and
Webber. The standard Gaussian and the Haar frame (for $\ell \le n$) are instances. For such a
test matrix the range projector $\mathbf{P}_{\mathbf{A}\mathbf{X}}$ has the law of
$\mathbf{P}_{\mathbf{A}\mathbf{G}}$ for a standard Gaussian $\mathbf{G}$
(`NLAlib.hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant`), and every error of the
randomized SVD is a measurable function of that projector. So the Gaussian expectations of
`NLAlib.LowRank.Gaussian.RangeFinder` and the Gaussian tails of
`NLAlib.LowRank.Gaussian.RangeFinderTail` hold verbatim.

The hypotheses are `HasLaw X ν μ` with `[IsProbabilityMeasure ν] [IsLeftUnitarilyInvariant ν]`
and `∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec`. The second is unsatisfiable for $\ell > n$; a Haar
frame of that shape has orthonormal rows and recovers the matrix almost surely
(`NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame`). The late-truncated Frobenius error is
transferred through its choice-free form (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`). Design:
`docs/design/LowRank-S3.md` §3.6, §8 items 6 and 8.

## Main results

* `NLAlib.ae_rsvd_eq_self_of_isLeftUnitarilyInvariant`: exact recovery at
  $\operatorname{rank}\mathbf{A} \le \ell$.
* the Gram form, in the `NLAlib.SymmetricGauge` namespace:
  `integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_isLeftUnitarilyInvariant`.
* `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`,
  `NLAlib.integral_frobNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant`: HMT Theorem 10.5 and
  Epperly and Webber's Theorem 3.1, squared and as printed.
* `NLAlib.integral_specNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant`: HMT Theorem 10.6.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant`: the
  truncated output.
* the Gram-form tail (TW Theorem 8.1 (RSVD1)), in the `NLAlib.SymmetricGauge` namespace:
  `measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_isLeftUnitarilyInvariant`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

omit [Fintype n] in
/-- $\mathbf{P} \mapsto \mathbf{A} - \mathbf{P}\mathbf{A}$ is measurable. -/
private theorem measurable_sub_mul (A : Matrix m n ℝ) :
    Measurable fun P : Matrix m m ℝ => A - P * A :=
  measurable_const.matrix_sub (measurable_id.matrix_mul measurable_const)

variable [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
  [IsLeftUnitarilyInvariant ν]

/-! ### Exact recovery -/

/-- **A rotation-invariant sketch at least as wide as the rank recovers the matrix**: if
$\operatorname{rank}\mathbf{A} \le \ell$, then $\mathsf{rsvd}(\mathbf{A}, \mathbf{X}) =
\mathbf{A}$ almost surely, for a test matrix $\mathbf{X}$ with a left unitarily invariant law
and full column rank almost surely. -/
theorem ae_rsvd_eq_self_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ)
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hA : A.rank ≤ Fintype.card l) : ∀ᵐ ω ∂μ, rsvd A (X ω) = A := by
  filter_upwards [ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant A hX hXr] with ω hω
  exact rsvd_eq_self_of_rank_eq (hω.trans (min_eq_left hA))

/-! ### Expectations -/

namespace SymmetricGauge

/-- **The expected error of the randomized SVD, Gram form, rotation-invariant test matrices**:
for a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost
surely (Gaussian, Haar, ...), $k + 2 \le \ell$ and every unitarily invariant norm,
$$\mathbb{E}\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{k}{\ell - k - 1}\,
\|\mathbf{E}\|_{\mathsf{F}}^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
the bound of the Gaussian test matrix (in this namespace,
`integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix`).
[TroppWebber2023, Theorem 8.1 (RSVD2)]; [EpperlyWebber2026, Theorem 3.1]; there for Gaussian test
matrices and Schatten $p \ge 2$ (TW), or rotation-invariant ones and the Frobenius norm (EW).
Result: randomized-svd-expected-error -/
theorem integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ∂μ ≤
      Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hg : Measurable fun P : Matrix m m ℝ => Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A)) :=
    Φ.measurable_matrixNorm.comp ((Measurable.matrix_conjTranspose continuous_star.measurable
      (measurable_sub_mul A)).matrix_mul (measurable_sub_mul A))
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω))) hg fun _ => rfl).trans_le ?_
  exact integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_hasLaw_gaussianMatrix Φ A
    HasLaw.id hk

end SymmetricGauge

/-- **The expected error of the randomized SVD, Frobenius norm, rotation-invariant test
matrices**: for a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column
rank almost surely and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
the factor being `gaussianProjectionFactor k ℓ`.
[EpperlyWebber2026, Theorem 3.1]; [HalkoMartinssonTropp2011, Theorem 10.5]; there (EW) over
$\mathbb{R}$ and $\mathbb{C}$ with a minimum over the number $q$ of directions, here over
$\mathbb{R}$ at $q = k$.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ)
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => frobNorm (A - rsvd A Ω) ^ 2)
    ((measurable_frobNorm.comp (measurable_sub_mul A)).pow_const 2) fun _ => rfl).trans_le ?_
  exact integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A HasLaw.id hk

/-- **The expected error of the randomized SVD, Frobenius norm, as printed, rotation-invariant
test matrices**: for a test matrix $\mathbf{X}$ with a left unitarily invariant law and full
column rank almost surely and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}} \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)^{1/2}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}\,.$$
[EpperlyWebber2026, Theorem 3.1]; [HalkoMartinssonTropp2011, Theorem 10.5]; there (EW) with a
minimum over the number $q$ of directions, here at $q = k$.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ)
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - rsvd A (X ω)) ∂μ ≤
      √(gaussianProjectionFactor k (Fintype.card l)) * frobNorm (A - truncatedSVD A k) := by
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => frobNorm (A - rsvd A Ω)) (measurable_frobNorm.comp (measurable_sub_mul A))
    fun _ => rfl).trans_le ?_
  exact integral_frobNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix A HasLaw.id hk

/-- **The average spectral error of the randomized SVD, rotation-invariant test matrices**: for a
test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely
and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2 \le
\Bigl(1 + \sqrt{\tfrac{k}{\ell - k - 1}}\Bigr)\sigma_k(\mathbf{A}) +
C\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\,,$$
with $C$ = `gaussianPinvSpecNormBound k ℓ`, the bound of the Gaussian test matrix
(`NLAlib.integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`).
[HalkoMartinssonTropp2011, Theorem 10.6]; [MartinssonTropp2020, Theorem 11.5]; there for Gaussian
test matrices, with $e\sqrt{k + p}/p$ in place of $C$.
Result: randomized-svd-average-spectral-error -/
theorem integral_specNorm_sub_rsvd_le_of_isLeftUnitarilyInvariant (A : Matrix m n ℝ)
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - rsvd A (X ω)) ∂μ ≤
      (1 + √((k : ℝ) / ((Fintype.card l : ℝ) - k - 1))) * singularValues A k +
        gaussianPinvSpecNormBound k (Fintype.card l) * frobNorm (A - truncatedSVD A k) := by
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => specNorm (A - rsvd A Ω)) (measurable_specNorm.comp (measurable_sub_mul A))
    fun _ => rfl).trans_le ?_
  exact integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix A HasLaw.id hk

/-- **The expected error of the truncated randomized SVD, Frobenius norm, rotation-invariant test
matrices**: for a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column
rank almost surely and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k
\|_{\mathsf{F}}^2 \le \Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
for every choice of the truncation. The error is transferred to the Gaussian through its
choice-free form, the squared error of the untruncated output plus the tail sum of squared
singular values of $\mathsf{rsvd}(\mathbf{A}, \mathbf{X})$.
[HalkoMartinssonTropp2011, Theorem 10.5]; [Woodruff2014, Lemma 48]; there for Gaussian test
matrices and the untruncated output, with Woodruff's truncation for free.
Result: randomized-svd-expected-error -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant
    (A : Matrix m n ℝ) (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  have hg : Measurable fun P : Matrix m m ℝ => frobNorm (A - P * A) ^ 2 +
      ∑ i ∈ Finset.Ico k (min (Fintype.card m) (Fintype.card n)), singularValues (P * A) i ^ 2 :=
    ((measurable_frobNorm.comp (measurable_sub_mul A)).pow_const 2).add
      (Finset.measurable_sum _ fun i _ => ((measurable_singularValues i).comp
        (measurable_id.matrix_mul measurable_const)).pow_const 2)
  refine (integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2) hg fun Ω => ?_).trans_le ?_
  · rw [frobNorm_sub_truncatedSVD_rsvd_sq, frobNorm_sub_truncatedSVD_sq]
    rfl
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix A HasLaw.id hk

/-! ### Tails -/

namespace SymmetricGauge

/-- **The tail of the randomized SVD, Gram form, rotation-invariant test matrices**: for a test
matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
$d = \ell - k + 1$, every unitarily invariant norm, any $u$ and $t > 0$,
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{utk}{d}\,
\|\mathbf{E}\|_{\mathsf{F}}^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
outside probability $e^{-(u-2)/4}$ + `gaussianPinvFrobTail k d t`, the tail of the Gaussian test
matrix (in this namespace,
`measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_gaussianMatrix`).
[TroppWebber2023, Theorem 8.1 (RSVD1)]; there for Gaussian test matrices and Schatten norms
$p \ge 2$, with second failure term $\sqrt{\pi k}\,(t/e)^{-d/2}$, which the library's is below.
Result: randomized-svd-tail -/
theorem measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω))) ≤
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * frobNorm (A - truncatedSVD A k) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  have hg : Measurable fun P : Matrix m m ℝ => Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A)) :=
    Φ.measurable_matrixNorm.comp ((Measurable.matrix_conjTranspose continuous_star.measurable
      (measurable_sub_mul A)).matrix_mul (measurable_sub_mul A))
  refine (measureReal_eq_measureReal_gaussianMatrix_of_isLeftUnitarilyInvariant A hX hXr
    (f := fun Ω => Φ.matrixNorm ((A - rsvd A Ω)ᴴ * (A - rsvd A Ω))) hg (fun _ => rfl) _).trans_le ?_
  exact measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_hasLaw_gaussianMatrix Φ
    A HasLaw.id hd u ht

end SymmetricGauge

end NLAlib
