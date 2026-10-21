/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.RangeFinderTail
public import NLAlib.RandomMatrix.Haar.Transfer

/-!
# The tail of the randomized SVD with a Haar test matrix

For an $n \times \ell$ Haar frame $\mathbf{\Omega}$ (`NLAlib.haarFrame`), the randomized SVD
$\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ has the tail of Tropp and Webber's (RSVD1) verbatim:
the error is a function of the range projector $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$, whose law
is that of $\mathbf{P}_{\mathbf{A}\mathbf{G}}$ for a standard Gaussian $\mathbf{G}$ of the same
shape (`NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`), so the Gaussian tail of
`NLAlib.LowRank.Gaussian.RangeFinderTail` transfers. Every shape: no $\ell \le n$. Real
throughout.

The Gram form is stated, for every unitarily invariant norm; the Schatten, Frobenius and spectral
forms are its corollaries at the gauges, as in the Gaussian file. This is the Haar case of the
randomized SVD tail by range transfer, the twin of the expectation transfers of
`NLAlib.LowRank.Gaussian.EarlyTruncationHaar`. Design: `docs/design/LowRank-S7.md` §3.5, §8
item 3.

## Main results

* The Gram form, every unitarily invariant norm, in the namespace `NLAlib.SymmetricGauge`:
  `measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l : Type*} [Fintype m]
  [Fintype n] [Fintype l] {X : Ω → Matrix n l ℝ}

namespace SymmetricGauge

/-- **The tail of the randomized SVD with a Haar test matrix, Gram form**: for an $n \times \ell$
Haar frame $\mathbf{\Omega}$, $d = \ell - k + 1$, every unitarily invariant norm, $s \ge 0$ and
$t > 0$,
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\bigr\|_{\Phi} \le
\|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} + \Phi(\mathbf{e}_0)\,\frac{tk}{d}\,
\bigl(\|\mathbf{E}\|_{\mathsf{F}} + s\,\sigma_k(\mathbf{A})\bigr)^2\,,\qquad
\mathbf{E} = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\,,$$
outside probability <!-- value gaussianPinvFrobTail k d t -->
$e^{-s^2/2} + 2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1)$ (the second term is
`gaussianPinvFrobTail k d t`), with $\mathbf{e}_0$ the first unit coordinate sequence: the bound
of the Gaussian statement
`measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix`
(in this namespace) verbatim, since the range of $\mathbf{A}\mathbf{\Omega}$ has the same law for
both (`NLAlib.hasLaw_rangeProjector_mul_of_hasLaw_haarFrame`).
[TroppWebber2023, Theorem 8.1 (RSVD1)]; there for Gaussian test matrices and squared Schatten norms,
with the noise term $(utk/d)\|\mathbf{E}\|_{\mathsf{F}}^2$ and the failure probability
$e^{-(u-2)/4} + \sqrt{\pi k}\,(t/e)^{-d/2}$, which follow from this bound at $s = \sqrt{u} - 1$.
Result: randomized-svd-tail -/
theorem measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_haarFrame
    [DecidableEq l] (Φ : SymmetricGauge) (A : Matrix m n ℝ) (hX : HasLaw X (haarFrame n l) μ)
    {k d : ℕ} (hd : k + d = Fintype.card l + 1) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) :
    μ.real {ω | Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
        Φ (Finsupp.single 0 1) * (t * k / d) *
          (frobNorm (A - truncatedSVD A k) + s * singularValues A k) ^ 2 <
        Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤
      Real.exp (-s ^ 2 / 2) + gaussianPinvFrobTail k d t := by
  classical
  set c := Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) +
    Φ (Finsupp.single 0 1) * (t * k / d) *
      (frobNorm (A - truncatedSVD A k) + s * singularValues A k) ^ 2
  have hf : Measurable fun P : Matrix m m ℝ => Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A)) := by
    have h1 : Measurable fun P : Matrix m m ℝ => A - P * A :=
      measurable_const.matrix_sub (measurable_id.matrix_mul measurable_const)
    exact Φ.measurable_matrixNorm.comp
      ((Measurable.matrix_conjTranspose continuous_star.measurable h1).matrix_mul h1)
  have hS : MeasurableSet
      {P : Matrix m m ℝ | c < Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A))} :=
    measurableSet_lt measurable_const hf
  have hT := hasLaw_rangeProjector_mul_of_hasLaw_haarFrame A hX
  have hg : Measurable fun G : Matrix n l ℝ => rangeProjector (A * G) :=
    measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id)
  have hG :=
    measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_gaussianMatrix Φ A
      (HasLaw.id (μ := gaussianMatrix n l)) hd hs ht
  calc μ.real {ω | c < Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))}
      = μ.real ((fun ω => rangeProjector (A * X ω)) ⁻¹'
          {P : Matrix m m ℝ | c < Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A))}) := rfl
    _ = (gaussianMatrix n l).real ((fun G => rangeProjector (A * G)) ⁻¹'
          {P : Matrix m m ℝ | c < Φ.matrixNorm ((A - P * A)ᴴ * (A - P * A))}) := by
        rw [← map_measureReal_apply_of_aemeasurable hT.aemeasurable hS, hT.map_eq,
          map_measureReal_apply hg hS]
    _ ≤ Real.exp (-s ^ 2 / 2) + gaussianPinvFrobTail k d t := hG

end SymmetricGauge

end NLAlib
