/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.TruncatedGeneralizedNystrom

/-!
# Truncated generalized Nyström: exact Gaussian identities (stage S10)

For independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($m \times p$), $p \ge \ell + 2$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})$
and the core noise $\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})$, the part of the noise in the dominant rank-$k$ subspace of
$\mathbf{R}$ has the exact mean
$\mathbb{E}\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2 =
\tfrac{k}{p - \ell - 1}\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2$ (against
$\tfrac{\ell}{p - \ell - 1}$ for all of $\mathbf{N}$, Epperly and Webber's identity), and the
oracle truncation $\llbracket\mathbf{R}\rrbracket_k +
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$
has an exact expected error. They join `NLAlib/LowRank/Gaussian/TruncatedGeneralizedNystrom.lean`.
New (research note `reports/OP2-TruncatedGN.md` of the NLAlib workflow, §3, I2–I3). Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.2. Real. Proofs deferred.

## Main results

* `NLAlib.integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix`: I2.
* `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix`:
  I3, and its bound
  `NLAlib.integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_le_of_hasLaw_gaussianMatrix`
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}

/-- **The core noise in the dominant subspace**: for independent standard Gaussian test
matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$), $k \le \ell$,
$\ell + 2 \le p$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$,
$$\mathbb{E}\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2 =
\frac{k}{p - \ell - 1}\,\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2\,.$$
Every rank of $\mathbf{A}$: if $\operatorname{rank}\mathbf{A} < \ell$ both sides vanish
($\mathbf{R} = \mathbf{A}$ almost surely). For the choice `truncatedSVD` makes.
No printed source. New (research note OP2, §3, I2).
Proof: M, about 80 lines. Condition on $\mathbf{\Omega}$ (`IndepFun`, the fixed-$\mathbf{\Omega}$
pattern of `integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix`). If
$\operatorname{rank}\mathbf{A} < \ell$: `ae_rsvd_eq_self_of_hasLaw_gaussianMatrix`. Otherwise
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) = \ell$ a.s.
(`ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`); take $\mathbf{Q}$ an orthonormal basis of the
range and $\mathbf{Q}_\perp$ its complement; $\mathbf{G}_1 = \mathbf{\Psi}^{\mathsf{T}}\mathbf{Q}$,
$\mathbf{G}_2 = \mathbf{\Psi}^{\mathsf{T}}\mathbf{Q}_\perp$ are independent standard Gaussian
(rotation invariance, `Invariance.lean`), $\mathbf{N} =
\mathbf{Q}\mathbf{G}_1^{+}\mathbf{G}_2\mathbf{C}$
with $\mathbf{C} = \mathbf{Q}_\perp^{\mathsf{T}}\mathbf{A}$, and
$\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k} = \mathbf{Q}\mathbf{P}_B\mathbf{Q}^{\mathsf{T}}$ with
$\mathbf{P}_B$ of rank $k$ and fixed given $\mathbf{\Omega}$. Then
$\mathbb{E}_{\mathbf{G}_2}\|\mathbf{P}_B\mathbf{G}_1^{+}\mathbf{G}_2\mathbf{C}\|_{\mathsf{F}}^2 =
\|\mathbf{C}\|_{\mathsf{F}}^2
\operatorname{tr}(\mathbf{P}_B(\mathbf{G}_1^{\mathsf{T}}\mathbf{G}_1)^{-1})$
and the inverse Wishart mean (`integral_mul_conjTranspose_inv_of_hasLaw_gaussianMatrix`) gives
$\operatorname{tr}\mathbf{P}_B/(p - \ell - 1)$; $\|\mathbf{C}\|_{\mathsf{F}} = \|\mathbf{A} -
\mathbf{R}\|_{\mathsf{F}}$. -/
theorem integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
        (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ =
      k / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  sorry

/-- **The oracle-truncated generalized Nyström error, exactly**: for independent standard Gaussian
test matrices $\mathbf{\Omega}$ ($n \times \ell$) and $\mathbf{\Psi}$ ($m \times p$), $k \le \ell$,
$\ell + 2 \le p$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$
and the oracle truncation $\widehat{\mathbf{A}} = \llbracket\mathbf{R}\rrbracket_k +
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$ (truncation in the dominant subspace of
$\mathbf{R}$ instead of that of $\mathsf{gn}$; not computable from the sketches),
$$\mathbb{E}\|\mathbf{A} - \widehat{\mathbf{A}}\|_{\mathsf{F}}^2 =
\mathbb{E}\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
\frac{k}{p - \ell - 1}\,\mathbb{E}\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2\,.$$
The noise costs $k/(p - \ell - 1)$, not $\ell/(p - \ell - 1)$: what truncated generalized Nyström
loses beyond this is the misalignment of its truncation subspace.
No printed source. New (research note OP2, §3, I3).
Proof: S, about 30 lines. $\mathbf{A} - \widehat{\mathbf{A}} = (\mathbf{A} -
\llbracket\mathbf{R}\rrbracket_k) -
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$; expand the square. The cross term
$\mathbb{E}\langle\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k,
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\rangle_{\mathsf{F}}$ vanishes: conditionally
on $\mathbf{\Omega}$ the core noise is linear in $\mathbf{G}_2$ of mean zero and independent of
$\mathbf{G}_1$ (`integrable_sketchAndSolve_of_hasLaw_gaussianMatrix`-type unbiasedness of Gaussian
sketch-and-solve, or the decomposition in the proof of I2); the square term is
`integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix`. -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
        rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ =
      ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ +
        k / ((Fintype.card p : ℝ) - Fintype.card l - 1) *
          ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  sorry

/-- **The expected error of the oracle truncation**: for
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($m \times p$), $k + 2 \le \ell$, $\ell + 2 \le p$,
$\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$
and $\widehat{\mathbf{A}} = \llbracket\mathbf{R}\rrbracket_k +
\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}$,
so <!-- value gaussianProjectionFactor k \ell -->
$$\mathbb{E}\|\mathbf{A} - \widehat{\mathbf{A}}\|_{\mathsf{F}}^2 \le
\Bigl(1 + \frac{k}{\ell - k - 1}\Bigr)\Bigl(1 + \frac{k}{p - \ell - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
A statement about an analysis device, not an algorithm: the dominant subspace of $\mathbf{R}$
is not available from the two sketches, so this says nothing about what an estimator built from
them can reach. It separates the two losses of truncated generalized Nyström: the noise in a
fixed rank-$k$ subspace costs $k/(p - \ell - 1)$; the rest is the misalignment of the data-driven
truncation subspace (design note §3.2).
No printed source. New (research note OP2, §3, I3).
Proof: S, about 15 lines. The identity
`integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_of_hasLaw_gaussianMatrix`,
$\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}} \le \|\mathbf{A} -
\llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}$
pointwise (`frobNorm_sub_truncatedSVD_rsvd_sq`, or Pythagoras with
`truncatedSVD_rsvd_eq_rangeProjector_mul`), and
`integral_frobNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix`. -/
theorem integral_frobNorm_sub_truncatedSVD_rsvd_sub_rangeProjector_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {k : ℕ}
    (hkl : k + 2 ≤ Fintype.card l) (hlp : Fintype.card l + 2 ≤ Fintype.card p) :
    ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k -
        rangeProjector (truncatedSVD (rsvd A (X ω)) k) *
          (obliqueProjector (A * X ω) (Ψ ω)ᴴ * (A - rsvd A (X ω)))) ^ 2 ∂μ ≤
      gaussianProjectionFactor k (Fintype.card l) *
        (1 + k / ((Fintype.card p : ℝ) - Fintype.card l - 1)) *
          frobNorm (A - truncatedSVD A k) ^ 2 := by
  sorry

end NLAlib
