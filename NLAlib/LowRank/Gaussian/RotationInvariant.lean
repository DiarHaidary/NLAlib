/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinder
public import NLAlib.LowRank.Gaussian.RangeFinderTail
public import NLAlib.LowRank.Random.Nystrom
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
transferred through its choice-free form (`NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq`).

**Nyström.** For positive semidefinite $\mathbf{H}$, $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$ has
the law of $\mathsf{nystrom}(\mathbf{H}, \mathbf{G})$ for a standard Gaussian $\mathbf{G}$, and the
Nyström expectations and tails hold with the Gaussian constants. Each is the rotation-invariant
statement for the randomized SVD at a factor $\mathbf{F}$ with
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$, through the Gram correspondence
(`NLAlib.conjTranspose_mul_self_sub_nystrom`); the spectral error of truncated Nyström adds reverse
Eckart–Young (`NLAlib.LowRank.Random.Nystrom`) and is stated for a measurable selector and,
directly, for `truncatedSVD`, which is Borel measurable (`NLAlib.measurable_truncatedSVD`). Design:
`docs/design/LowRank-S3.md` §3.6, §8 items 6 and 8; `docs/design/LowRank-S5.md` §3.5, §8;
`docs/design/LowRank-S2c.md` §8 item 8.

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
* Nyström, in the `Matrix.PosSemidef` namespace: `hasLaw_nystrom_of_isLeftUnitarilyInvariant`
  (the law of the output), `integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant`,
  `integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`,
  `integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant` (MT Theorem
  14.1, for a measurable selector) and its direct form
  `integral_specNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`,
  `ae_nystrom_eq_self_of_isLeftUnitarilyInvariant`; in the
  `NLAlib.SymmetricGauge` namespace,
  `integral_matrixNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant` and
  `measureReal_not_matrixNorm_sub_nystrom_le_le_of_isLeftUnitarilyInvariant`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder MatrixOrder

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
and $k + 2 \le \ell$, <!-- value gaussianPinvSpecNormBound k \ell -->
$$\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_2 \le
\Bigl(1 + \sqrt{\tfrac{k}{\ell - k - 1}}\Bigr)\sigma_k(\mathbf{A}) +
\frac{e}{\ell - k}\sqrt{(\ell + k - 1)/2}\,
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\,,$$
the bound of the Gaussian test matrix
(`NLAlib.integral_specNorm_sub_rsvd_le_of_hasLaw_gaussianMatrix`); the constant is
`gaussianPinvSpecNormBound k ℓ`.
[HalkoMartinssonTropp2011, Theorem 10.6]; [MartinssonTropp2020, Theorem 11.5]; there for Gaussian
test matrices, with the constant $e\sqrt{k + p}/p$, $p = \ell - k$.
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
outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-(u-2)/4} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$ (the second term is
`gaussianPinvFrobTail k d t`), the tail of the Gaussian test matrix (in this namespace,
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

/-! ### Nyström -/

/-- **Nyström with a rotation-invariant test matrix has the Gaussian law**: for positive
semidefinite $\mathbf{H}$ and a test matrix $\mathbf{X}$ with a left unitarily invariant law and
full column rank almost surely, $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$ has the law of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{G})$ for a standard Gaussian $\mathbf{G}$. Nyström depends
on the test matrix only through the range projector $\mathbf{P}_{\mathbf{H}^{1/2}\mathbf{X}}$
(`Matrix.PosSemidef.nystrom_eq`), whose law is the Gaussian one
(`NLAlib.hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant`). Every rotation-invariant
Nyström statement is a consequence.
[TroppYurtseverUdellCevher2017a, Proposition A.2 and proof of Theorem A.1];
[EpperlyWebber2026, Fact 6.1(b)]; there as "we may assume the test matrix is Gaussian", here as
a law statement for every full-rank rotation-invariant law.
Result: gaussian-haar-range-transfer -/
theorem _root_.Matrix.PosSemidef.hasLaw_nystrom_of_isLeftUnitarilyInvariant {H : Matrix n n ℝ}
    (hH : H.PosSemidef) (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) :
    HasLaw (fun ω => nystrom H (X ω)) ((gaussianMatrix n l).map (nystrom H)) μ := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℝ,
      ∀ G : Matrix n l ℝ, nystrom H G = S * rangeProjector (S * G) * S :=
    ⟨_, hH.nystrom_eq⟩
  have hg : Measurable fun P : Matrix n n ℝ => S * P * S :=
    (measurable_const.matrix_mul measurable_id).matrix_mul measurable_const
  have hm : Measurable fun G : Matrix n l ℝ => rangeProjector (S * G) :=
    measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id)
  have h := HasLaw.fun_comp (Y := fun P : Matrix n n ℝ => S * P * S) ⟨hg.aemeasurable, rfl⟩
    (hasLaw_rangeProjector_mul_of_isLeftUnitarilyInvariant S hX hXr)
  rw [Measure.map_map hg hm] at h
  have e1 : (fun ω => nystrom H (X ω)) = fun ω => S * rangeProjector (S * X ω) * S :=
    funext fun ω => hS (X ω)
  have e2 : nystrom H = (fun P : Matrix n n ℝ => S * P * S) ∘ fun G => rangeProjector (S * G) :=
    funext hS
  rw [e1, e2]
  exact h

namespace SymmetricGauge

/-- **The expected error of randomized Nyström, every unitarily invariant norm, rotation-invariant
test matrices**: for positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely (Gaussian, Haar, ...) and
$k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,
\frac{k}{\ell - k - 1}\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
the bound of the Gaussian test matrix (in this namespace,
`integral_matrixNorm_sub_nystrom_le_of_hasLaw_gaussianMatrix`); the rotation-invariant Gram form
of the randomized SVD at a factor of $\mathbf{H}$.
[TroppWebber2023, Corollary 8.2 (NysSVD2)]; [TroppYurtseverUdellCevher2017a, Theorem A.1];
[EpperlyWebber2026, Theorem 3.1 and Fact 3.5]; there for Gaussian test matrices and Schatten
norms (TW), or the trace (TYUC, EW).
Result: randomized-nystrom-expected-error -/
theorem integral_matrixNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant (Φ : SymmetricGauge)
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, Φ.matrixNorm (H - nystrom H (X ω)) ∂μ ≤
      Φ.matrixNorm (H - truncatedSVD H k) +
        Φ (Finsupp.single 0 1) * ((k : ℝ) / ((Fintype.card l : ℝ) - k - 1)) *
          nuclearNorm (H - truncatedSVD H k) := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom,
    Φ.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact Φ.integral_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_of_isLeftUnitarilyInvariant F hX
    hXr hk

end SymmetricGauge

/-- **The expected trace error of randomized Nyström, rotation-invariant test matrices**: for
positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left unitarily invariant law
and full column rank almost surely and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_* \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
the factor being `gaussianProjectionFactor k ℓ`: the squared Frobenius error of the randomized
SVD of a factor (`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant`). A Haar
frame (`NLAlib.haarFrame`) is an instance: its law is left unitarily invariant
(`NLAlib.isLeftUnitarilyInvariant_haarFrame`), and for $\ell \le n$ it has full column rank
almost surely (`NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{I}$).
[EpperlyWebber2026, Theorem 3.1 and Fact 3.5]; [TroppYurtseverUdellCevher2017a, Theorem A.1];
there with a minimum over the comparison rank, for orthonormal test matrices (TYUC) or
rotation-invariant ones (EW, the Nyström twin of their Theorem 3.1); here at one rank.
Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k) := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, nuclearNorm_conjTranspose_mul_self_sub_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant F hX hXr hk

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected trace error of truncated Nyström, rotation-invariant test matrices**: for
positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left unitarily invariant law
and full column rank almost surely, $k + 2 \le \ell$ and every choice of the truncation,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_*
\le \Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,:$$
the squared Frobenius error of the truncated randomized SVD of a factor
(`NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant`). A Haar
frame is an instance (`NLAlib.isLeftUnitarilyInvariant_haarFrame`, and
`NLAlib.ae_rank_mul_eq_min_of_hasLaw_haarFrame` at $\mathbf{A} = \mathbf{I}$ for $\ell \le n$).
[TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.1)]; there for Gaussian or orthonormal test
matrices, with $1 \le k$ and $\ell \le n$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) * nuclearNorm (H - truncatedSVD H k) := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD_nystrom,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_isLeftUnitarilyInvariant F hX hXr hk

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected spectral error of truncated Nyström, rotation-invariant test matrices**
(Martinsson and Tropp's Theorem 14.1): for positive semidefinite $\mathbf{H}$, a test matrix
$\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
$k + 2 \le \ell$ and a measurable choice $\mathbf{Y}$ of best rank-$k$ approximations of
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$,
$$\mathbb{E}\|\mathbf{H} - \mathbf{Y}\|_2 \le \lambda_k(\mathbf{H}) + \frac{k}{\ell - k - 1}
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
eigenvalues indexed from $0$.
Direct form at `truncatedSVD`:
`Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`.
[MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]; there
for Gaussian (MT, TYUC) or orthonormal (TYUC) test matrices, with $1 \le k < \ell \le n$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l)
    {Y : Ω → Matrix n n ℝ} (hY : ∀ ω, IsBestRankApprox (nystrom H (X ω)) k (Y ω))
    (hYm : AEStronglyMeasurable Y μ) :
    ∫ ω, specNorm (H - Y ω) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) := by
  have := hX.isProbabilityMeasure
  have h1 :=
    hH.integral_specNorm_sub_add_nuclearNorm_sub_truncatedSVD_le_of_isBestRankApprox_nystrom
      hX.aemeasurable hY hYm
  have h2 :=
    hH.integral_nuclearNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant hX hXr hk
  rw [gaussianProjectionFactor_def] at h2
  linarith

-- The declaration name alone, with its `_root_.Matrix.PosSemidef` prefix, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The expected spectral error of truncated Nyström, rotation-invariant test matrices**
(Martinsson and Tropp's Theorem 14.1): for positive semidefinite $\mathbf{H}$, a test matrix
$\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely and
$k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{H} - \llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{X})\rrbracket_k\|_2 \le
\lambda_k(\mathbf{H}) + \frac{k}{\ell - k - 1}\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*\,,$$
eigenvalues indexed from $0$. The direct form of
`Matrix.PosSemidef.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant`,
which covers any other measurable choice of the truncation.
[MartinssonTropp2020, Theorem 14.1]; [TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]; there
for Gaussian (MT, TYUC) or orthonormal (TYUC) test matrices, with $1 \le k < \ell \le n$.
Result: randomized-nystrom-expected-error -/
theorem
_root_.Matrix.PosSemidef.integral_specNorm_sub_truncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k : ℕ} (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k) :=
  hH.integral_specNorm_sub_le_of_isBestRankApprox_nystrom_of_isLeftUnitarilyInvariant hX hXr hk
    (fun _ => isBestRankApprox_truncatedSVD _ k)
    (((measurable_nystrom H).comp_aemeasurable hX.aemeasurable).truncatedSVD k).aestronglyMeasurable

namespace SymmetricGauge

/-- **The tail of randomized Nyström, every unitarily invariant norm, rotation-invariant test
matrices**: for positive semidefinite $\mathbf{H}$, a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely, $d = \ell - k + 1$, any $u$ and
$t > 0$,
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_{\Phi} \le
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{utk}{d}\,
\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_k\|_*$$
outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-(u-2)/4} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$ (the second term is
`gaussianPinvFrobTail k d t`), the tail of the Gaussian test matrix (in this namespace,
`measureReal_not_matrixNorm_sub_nystrom_le_le_of_hasLaw_gaussianMatrix`).
[TroppWebber2023, Corollary 8.2 (NysSVD1)]; there for Gaussian test matrices and Schatten norms,
with a larger second failure term.
Result: randomized-nystrom-tail -/
theorem measureReal_not_matrixNorm_sub_nystrom_le_le_of_isLeftUnitarilyInvariant
    (Φ : SymmetricGauge) {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {k d : ℕ}
    (hd : k + d = Fintype.card l + 1) (u : ℝ) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | ¬ Φ.matrixNorm (H - nystrom H (X ω)) ≤
        Φ.matrixNorm (H - truncatedSVD H k) +
          Φ (Finsupp.single 0 1) * (u * t * k / d) * nuclearNorm (H - truncatedSVD H k)} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail k d t := by
  obtain ⟨F, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.nonneg
  simp only [Matrix.star_eq_conjTranspose, conjTranspose_mul_self_sub_nystrom,
    Φ.matrixNorm_conjTranspose_mul_self_sub_truncatedSVD,
    nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
  exact
    Φ.measureReal_not_matrixNorm_conjTranspose_mul_self_sub_rsvd_le_le_of_isLeftUnitarilyInvariant
      F hX hXr hd u ht

end SymmetricGauge

/-- **A rotation-invariant sketch at least as wide as the rank makes Nyström exact**: for
positive semidefinite $\mathbf{H}$ with $\operatorname{rank}\mathbf{H} \le \ell$ and a test matrix
$\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
$\mathsf{nystrom}(\mathbf{H}, \mathbf{X}) = \mathbf{H}$ almost surely. -/
theorem _root_.Matrix.PosSemidef.ae_nystrom_eq_self_of_isLeftUnitarilyInvariant
    {H : Matrix n n ℝ} (hH : H.PosSemidef) (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) (hHl : H.rank ≤ Fintype.card l) :
    ∀ᵐ ω ∂μ, nystrom H (X ω) = H := by
  filter_upwards [ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant H hX hXr] with ω hω
  exact hH.nystrom_eq_self_of_rank_eq (hω.trans (min_eq_left hHl))

end NLAlib
