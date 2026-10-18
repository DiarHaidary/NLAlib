/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.GirardHutchinson
public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowRank.Gaussian.RotationInvariant
public import NLAlib.Matrix.Spectral.BestRankApprox
public import NLAlib.Sketching.Gaussian.Rademacher

/-!
# Hutch++: the definition, unbiasedness and the exact variance

For a square $\mathbf{A}$, a sketch test matrix $\mathbf{S}$ with $\lvert s \rvert$ columns and a
residual test matrix $\mathbf{G}$ with $\ell = \lvert t \rvert$ columns, **Hutch++** computes the
trace of the randomized SVD of $\mathbf{A}$ exactly and estimates the trace of the compressed
residual with the Girard–Hutchinson estimator:
$$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) :=
\operatorname{tr}\mathsf{rsvd}(\mathbf{A}, \mathbf{S}) +
\mathsf{girardHutchinson}\bigl((\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{A}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}}), \mathbf{G}\bigr)\,,$$
with $2\lvert s \rvert + \ell$ products with $\mathbf{A}$. Its error is the Girard–Hutchinson error
on the compressed residual (`NLAlib.hutchpp_sub_trace`), so it is unbiased whenever the residual
probes are isotropic and independent of the sketch, whatever the sketch's law, and its
mean-square error is the average over the sketch of the Girard–Hutchinson mean-square error.

With a standard Gaussian residual test matrix the variance is computed exactly,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] = \frac{2}{\ell}\,
\mathbb{E}\,\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{H}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\|_{\mathsf{F}}^2\,,$$
$\mathbf{H} = \tfrac12(\mathbf{A} + \mathbf{A}^{\mathsf{T}})$, for every sketch law; with a
Gaussian sketch too, the bounds of Meyer, Musco, Musco and Woodruff and of Epperly, Tropp and
Webber follow. The high-probability bounds are in `NLAlib.Estimation.Trace.HutchPlusPlusTail`.
Probabilistic statements are over $\mathbb{R}$, where the Gaussian law and Hanson–Wright live; the
definition, the error identity and unbiasedness are over any `RCLike` field. Design:
`docs/design/Estimation-HutchPP.md`.

## Main definitions

* `NLAlib.hutchpp`.

## Main results

* `NLAlib.HasOrthonormalCols.hutchpp_eq`: the papers' form with an orthonormal basis of the sketch.
* `NLAlib.hutchpp_sub_trace`: the error identity; `NLAlib.hutchpp_eq_trace_of_rank_eq`: exactness
  when the sketch captures the range.
* `NLAlib.integral_hutchpp`: unbiasedness.
* `NLAlib.integral_norm_hutchpp_sub_trace_sq`: the mean-square error as an average over the sketch.
* `NLAlib.variance_hutchpp_of_hasLaw_gaussianMatrix`,
  `NLAlib.variance_hutchpp_of_hasLaw_rademacherMatrix`,
  `Matrix.IsHermitian.variance_hutchpp_of_hasLaw_gaussianMatrix`: the exact variances.
* `NLAlib.ae_hutchpp_eq_trace_of_hasLaw_gaussianMatrix`: exactness at low rank.
* `NLAlib.variance_hutchpp_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.variance_hutchpp_le_of_hasLaw_gaussianMatrix_of_rank_le`,
  `NLAlib.variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix`,
  `Matrix.PosSemidef.variance_hutchpp_le_trace_sq_of_hasLaw_gaussianMatrix`: the variance bounds,
  and the asymptotic form `NLAlib.exists_forall_variance_hutchpp_le_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n s t : Type*} [Fintype n] [Fintype s] [Fintype t] [DecidableEq n]

-- Stage TE-2

/-- **Hutch++**: for a square $\mathbf{A}$, a sketch test matrix $\mathbf{S}$ and a residual test
matrix $\mathbf{G}$,
$$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) :=
\operatorname{tr}\mathsf{rsvd}(\mathbf{A}, \mathbf{S}) +
\mathsf{girardHutchinson}\bigl((\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{A}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}}), \mathbf{G}\bigr)\,,$$
the exact trace of the randomized SVD of $\mathbf{A}$ with sketch $\mathbf{S}$ plus the
Girard–Hutchinson estimate, with the columns of $\mathbf{G}$ as probes, of the trace of the
compressed residual. It uses $\lvert s \rvert$ products to form $\mathbf{A}\mathbf{S}$, at most
$\lvert s \rvert$ more for $\mathbf{A}\mathbf{Q}$ with $\mathbf{Q}$ a basis of its range, and
$\lvert t \rvert$ for the residual. Junk value: with no residual probes ($t$ empty) the estimate
of the residual is $0$ and the output is $\operatorname{tr}\mathsf{rsvd}(\mathbf{A}, \mathbf{S})$.
The basis form of the papers is `NLAlib.HasOrthonormalCols.hutchpp_eq`.
[MeyerMuscoMuscoWoodruff2021, Algorithm 1 and Algorithm 3]; [EpperlyTroppWebber2024, (1.3)];
there with an orthonormal basis $\mathbf{Q}$ of the range of $\mathbf{A}\mathbf{S}$ and
$\mathbf{S}$, $\mathbf{G}$ random (sign or Gaussian entries). -/
noncomputable def hutchpp (A : Matrix n n 𝕜) (S : Matrix n s 𝕜) (G : Matrix n t 𝕜) : 𝕜 :=
  (rsvd A S).trace +
    girardHutchinson ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))) G

/-- **Hutch++ with an orthonormal basis of the sketch**: if $\mathbf{Q}$ has orthonormal columns
and $\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}\mathbf{S}}$, then
$$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) =
\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) +
\mathsf{girardHutchinson}\bigl((\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}
(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}), \mathbf{G}\bigr)\,,$$
the form in which the papers state the algorithm. A bridge to `NLAlib.hutchpp`; such a
$\mathbf{Q}$ exists for every sketch (`NLAlib.HasOrthonormalCols.rangeProjector_eq`). -/
theorem HasOrthonormalCols.hutchpp_eq {q : Type*} [Fintype q] [DecidableEq q] {Q : Matrix n q 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} {S : Matrix n s 𝕜}
    (hQS : Q * Qᴴ = rangeProjector (A * S)) (G : Matrix n t 𝕜) :
    hutchpp A S G =
      (Qᴴ * A * Q).trace + girardHutchinson ((1 - Q * Qᴴ) * A * (1 - Q * Qᴴ)) G := by
  sorry

/-- **The error of Hutch++ is the error of Girard–Hutchinson on the compressed residual**: for
every square $\mathbf{A}$ and all test matrices $\mathbf{S}$, $\mathbf{G}$, with
$\mathbf{\Delta} = (\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{A}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})$,
$$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) - \operatorname{tr}\mathbf{A} =
\mathsf{girardHutchinson}(\mathbf{\Delta}, \mathbf{G}) - \operatorname{tr}\mathbf{\Delta}\,.$$
Deterministic; from the trace split
`IsIdempotentElem.trace_mul_add_trace_one_sub_mul_mul_one_sub`.
[MeyerMuscoMuscoWoodruff2021, §3, proof of Theorem 1]; [EpperlyTroppWebber2024, §1.1.2]. -/
theorem hutchpp_sub_trace (A : Matrix n n 𝕜) (S : Matrix n s 𝕜) (G : Matrix n t 𝕜) :
    hutchpp A S G - A.trace =
      girardHutchinson ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))) G -
        ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))).trace := by
  sorry

/-- **Hutch++ is exact when the sketch captures the range**: if
$\operatorname{rank}(\mathbf{A}\mathbf{S}) = \operatorname{rank}\mathbf{A}$, then
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) = \operatorname{tr}\mathbf{A}$ for every
residual test matrix $\mathbf{G}$: the randomized SVD recovers $\mathbf{A}$
(`NLAlib.rsvd_eq_self_of_rank_eq`) and the compressed residual is $\mathbf{0}$. -/
theorem hutchpp_eq_trace_of_rank_eq {A : Matrix n n 𝕜} {S : Matrix n s 𝕜}
    (h : (A * S).rank = A.rank) (G : Matrix n t 𝕜) : hutchpp A S G = A.trace := by
  sorry

/-- Hutch++ is a Borel measurable function of the pair of test matrices
$(\mathbf{S}, \mathbf{G})$, from `NLAlib.measurable_rangeProjector`. -/
theorem measurable_hutchpp (A : Matrix n n 𝕜) :
    Measurable fun p : Matrix n s 𝕜 × Matrix n t 𝕜 => hutchpp A p.1 p.2 := by
  sorry

/-- **Hutch++ is unbiased**: if the sketch test matrix $\mathbf{S}$ is almost everywhere
measurable, the residual test matrix $\mathbf{G}$ is independent of it and has at least one
column, and every column $\mathbf{g}$ of $\mathbf{G}$ is isotropic
($\mathbb{E}\,\mathbf{g}\mathbf{g}^{\mathsf{H}} = \mathbf{I}$, square integrable), then for
every square $\mathbf{A}$,
$$\mathbb{E}\,\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) =
\operatorname{tr}\mathbf{A}\,.$$
The sketch may have any law and the columns of $\mathbf{G}$ need not be independent. Conditionally
on $\mathbf{S}$, the residual estimate is unbiased for the trace of the compressed residual
(`NLAlib.integral_girardHutchinson`), and the trace split adds the exact part back.
[MeyerMuscoMuscoWoodruff2021, Theorem 10 and Lemma 14]; [EpperlyTroppWebber2024, Proposition 5.2];
there with Gaussian $\mathbf{S}$ and real Gaussian or sign $\mathbf{G}$.
Result: hutchpp-unbiased -/
theorem integral_hutchpp [IsProbabilityMeasure μ] [Nonempty t] (A : Matrix n n 𝕜)
    {S : Ω → Matrix n s 𝕜} {G : Ω → Matrix n t 𝕜} (hS : AEMeasurable S μ)
    (hSG : IndepFun S G μ) (hG : ∀ j, IsIsotropic (fun ω i => G ω i j) μ) :
    ∫ ω, hutchpp A (S ω) (G ω) ∂μ = A.trace := by
  sorry

/-- **The mean-square error of Hutch++ is an average over the sketch**: if the sketch test matrix
$\mathbf{S}$ is almost everywhere measurable, the residual test matrix $\mathbf{G}$ is independent
of it and every entry of $\mathbf{G}$ has a finite fourth moment, then for every square
$\mathbf{A}$, with $\mathbf{\Delta}(\mathbf{S}) = (\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})
\mathbf{A}(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})$ and $\mathbf{G}'$ an independent copy
of $\mathbf{G}$ (the inner integral),
$$\mathbb{E}\,\lvert \mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) -
\operatorname{tr}\mathbf{A} \rvert^2 = \mathbb{E}_{\mathbf{S}}\,\mathbb{E}_{\mathbf{G}'}
\lvert \mathsf{girardHutchinson}(\mathbf{\Delta}(\mathbf{S}), \mathbf{G}') -
\operatorname{tr}\mathbf{\Delta}(\mathbf{S}) \rvert^2\,.$$
No isotropy, no independence of the columns and no column is needed; the per-law formulas of
`NLAlib.integral_norm_girardHutchinson_sub_trace_sq` evaluate the inner integral.
[MeyerMuscoMuscoWoodruff2021, proof of Theorem 10, (2)]; there as the law of total variance with
Gaussian test matrices. -/
theorem integral_norm_hutchpp_sub_trace_sq [IsProbabilityMeasure μ] (A : Matrix n n 𝕜)
    {S : Ω → Matrix n s 𝕜} {G : Ω → Matrix n t 𝕜} (hS : AEMeasurable S μ)
    (hG : ∀ i j, MemLp (fun ω => G ω i j) 4 μ) (hSG : IndepFun S G μ) :
    ∫ ω, ‖hutchpp A (S ω) (G ω) - A.trace‖ ^ 2 ∂μ =
      ∫ ω, ∫ ω', ‖girardHutchinson ((1 - rangeProjector (A * S ω)) * A *
          (1 - rangeProjector (A * S ω))) (G ω') -
        ((1 - rangeProjector (A * S ω)) * A * (1 - rangeProjector (A * S ω))).trace‖ ^ 2 ∂μ ∂μ := by
  sorry

/-- **The exact variance of Hutch++ with a Gaussian residual test matrix**: if the sketch test
matrix $\mathbf{S}$ is almost everywhere measurable and the $n \times \ell$ residual test matrix
$\mathbf{G}$, $\ell \ge 1$, is standard Gaussian and independent of $\mathbf{S}$, then for every
real square $\mathbf{A}$, with $\mathbf{H} = \tfrac12(\mathbf{A} + \mathbf{A}^{\mathsf{T}})$ its
symmetric part,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] = \frac{2}{\ell}\,
\mathbb{E}\,\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{H}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\|_{\mathsf{F}}^2\,.$$
Exact for every law of the sketch; Gaussianity of $\mathbf{S}$ enters only the bounds
(`NLAlib.variance_hutchpp_le_of_hasLaw_gaussianMatrix`). With $\ell = 0$ the right side would be
$0$ while the output $\operatorname{tr}\mathsf{rsvd}(\mathbf{A}, \mathbf{S})$ is random, hence
$\ell \ge 1$. The sign-probe identity is `NLAlib.variance_hutchpp_of_hasLaw_rademacherMatrix`.
[MeyerMuscoMuscoWoodruff2021, proof of Theorem 10, Imported Lemma 11];
[EpperlyTroppWebber2024, Proposition 5.2]; there for symmetric (MMMW: positive semidefinite)
$\mathbf{A}$ and Gaussian $\mathbf{S}$, as the first line of a bound. MMMW's Algorithm 3 samples
$\mathbf{G}$ with sign entries while applying the Gaussian Lemma 11; their bound survives because
the sign variance is at most the Gaussian one.
Result: hutchpp-variance -/
theorem variance_hutchpp_of_hasLaw_gaussianMatrix [Nonempty t] (A : Matrix n n ℝ)
    {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} (hS : AEMeasurable S μ)
    (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ =
      2 / Fintype.card t * ∫ ω, frobNorm ((1 - rangeProjector (A * S ω)) * hermitianPart A *
        (1 - rangeProjector (A * S ω))) ^ 2 ∂μ := by
  sorry

/-- **The exact variance of Hutch++ with a sign residual test matrix**: if the sketch test matrix
$\mathbf{S}$ is almost everywhere measurable and the $n \times \ell$ residual test matrix
$\mathbf{G}$, $\ell \ge 1$, has independent uniformly random signs as entries and is independent of
$\mathbf{S}$, then for every real square $\mathbf{A}$, with
$\mathbf{H} = \tfrac12(\mathbf{A} + \mathbf{A}^{\mathsf{T}})$ and
$\mathbf{\Delta}_{\mathbf{H}} = (\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{H}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})$,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] = \frac{2}{\ell}\,
\mathbb{E}\Bigl[\|\mathbf{\Delta}_{\mathbf{H}}\|_{\mathsf{F}}^2 -
\sum_i (\mathbf{\Delta}_{\mathbf{H}})_{i,i}^2\Bigr]\,.$$
At most the Gaussian variance `NLAlib.variance_hutchpp_of_hasLaw_gaussianMatrix`; with a Gaussian
$\mathbf{S}$ it is the exact variance of [MeyerMuscoMuscoWoodruff2021, Algorithm 3] as printed.
The sign law is stated on the rows of $\mathbf{G}^{\mathsf{H}}$, the columns of $\mathbf{G}$.
[Epperly2023, Real-Valued Test Vectors]; there for Girard–Hutchinson alone.
Result: hutchpp-variance -/
theorem variance_hutchpp_of_hasLaw_rademacherMatrix [Nonempty t] (A : Matrix n n ℝ)
    {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} (hS : AEMeasurable S μ)
    (hG : HasLaw (fun ω => (G ω)ᴴ) (rademacherMatrix t n) μ) (hSG : IndepFun S G μ) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ =
      2 / Fintype.card t * ∫ ω, (frobNorm ((1 - rangeProjector (A * S ω)) * hermitianPart A *
          (1 - rangeProjector (A * S ω))) ^ 2 -
        ∑ i, ((1 - rangeProjector (A * S ω)) * hermitianPart A *
          (1 - rangeProjector (A * S ω))) i i ^ 2) ∂μ := by
  sorry

/-- **The exact variance of Hutch++ for a symmetric matrix, Pythagorean form**: for real symmetric
$\mathbf{A}$, an almost everywhere measurable sketch test matrix $\mathbf{S}$ and a standard
Gaussian $n \times \ell$ residual test matrix $\mathbf{G}$, $\ell \ge 1$, independent of
$\mathbf{S}$, with $\mathbf{P} = \mathbf{P}_{\mathbf{A}\mathbf{S}}$,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] = \frac{2}{\ell}\Bigl(
\mathbb{E}\,\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}^2 -
\mathbb{E}\,\|(\mathbf{I} - \mathbf{P})\mathbf{A}\mathbf{P}\|_{\mathsf{F}}^2\Bigr)\,:$$
the randomized-SVD error less the part of it that leaves the range of the sketch on the right,
by `NLAlib.frobNorm_one_sub_rangeProjector_mul_sq_eq_add`. Dropping the second term is the
submultiplicativity step of [MeyerMuscoMuscoWoodruff2021, proof of Theorem 10]. -/
theorem _root_.Matrix.IsHermitian.variance_hutchpp_of_hasLaw_gaussianMatrix [Nonempty t]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ}
    (hS : AEMeasurable S μ) (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ =
      2 / Fintype.card t * (∫ ω, frobNorm (A - rsvd A (S ω)) ^ 2 ∂μ -
        ∫ ω, frobNorm ((1 - rangeProjector (A * S ω)) * A * rangeProjector (A * S ω)) ^ 2 ∂μ) := by
  sorry

/-- **Hutch++ is exact at low rank with a Gaussian sketch**: if the $n \times \lvert s \rvert$
sketch test matrix $\mathbf{S}$ is standard Gaussian and
$\operatorname{rank}\mathbf{A} \le \lvert s \rvert$, then for every residual test matrix
$\mathbf{G}$ (of any law, dependent or not),
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) = \operatorname{tr}\mathbf{A}$ almost
surely; in particular its variance is $0$. From
`NLAlib.ae_rsvd_eq_self_of_hasLaw_gaussianMatrix` and `NLAlib.hutchpp_eq_trace_of_rank_eq`. -/
theorem ae_hutchpp_eq_trace_of_hasLaw_gaussianMatrix (A : Matrix n n ℝ) {S : Ω → Matrix n s ℝ}
    (hS : HasLaw S (gaussianMatrix n s) μ) (hA : A.rank ≤ Fintype.card s)
    (G : Ω → Matrix n t ℝ) :
    ∀ᵐ ω ∂μ, hutchpp A (S ω) (G ω) = A.trace := by
  sorry

-- Stage TE-3

/-- **The variance of Gaussian Hutch++, Halko–Martinsson–Tropp form**: if the
$n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$ and the $n \times \ell$ residual test
matrix $\mathbf{G}$, $\ell \ge 1$, are independent and standard Gaussian, then for every real
square $\mathbf{A}$ and every
$r$ with $r + 2 \le \lvert s \rvert$, <!-- value gaussianProjectionFactor r {\lvert s \rvert} -->
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] \le \frac{2}{\ell}
\Bigl(1 + \frac{r}{\lvert s \rvert - r - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2\,;$$
the factor is `gaussianProjectionFactor r (Fintype.card s)`. From the exact variance
`NLAlib.variance_hutchpp_of_hasLaw_gaussianMatrix`, the bound
$\|(\mathbf{I} - \mathbf{P})\mathbf{H}(\mathbf{I} - \mathbf{P})\|_{\mathsf{F}} \le
\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}$ (no symmetry of $\mathbf{A}$
needed) and `NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix`. The sharper
Epperly–Webber factor is `NLAlib.variance_hutchpp_le_of_hasLaw_gaussianMatrix_of_rank_le`; the
nuclear form is `NLAlib.variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix`.
[EpperlyTroppWebber2024, Theorem 1.1 (Hutch++ line) and Proposition 5.2];
[MeyerMuscoMuscoWoodruff2021, proof of Theorem 10 and Lemma 14]; there for symmetric
(MMMW: positive semidefinite) $\mathbf{A}$ and, in MMMW, $r \ge 2$.
Result: hutchpp-variance -/
theorem variance_hutchpp_le_of_hasLaw_gaussianMatrix [Nonempty t] (A : Matrix n n ℝ)
    {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} (hS : HasLaw S (gaussianMatrix n s) μ)
    (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) {r : ℕ}
    (hr : r + 2 ≤ Fintype.card s) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ ≤
      2 / Fintype.card t * gaussianProjectionFactor r (Fintype.card s) *
        frobNorm (A - truncatedSVD A r) ^ 2 := by
  sorry

/-- **The variance of Gaussian Hutch++, Epperly–Webber form**: if the $n \times \lvert s \rvert$
sketch test matrix $\mathbf{S}$ and the $n \times \ell$ residual test matrix $\mathbf{G}$,
$\ell \ge 1$, are independent and standard Gaussian, then for every real square $\mathbf{A}$ with
$\operatorname{rank}\mathbf{A} \le r$, $\lvert s \rvert \le r$ and
$q + 2 \le \lvert s \rvert$, <!-- value rotationInvariantFactor r {\lvert s \rvert} q -->
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] \le \frac{2}{\ell}\,
\frac{r - \lvert s \rvert}{r - q}\Bigl(1 + \frac{q}{\lvert s \rvert - q - 1}\Bigr)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2\,;$$
the factor is `rotationInvariantFactor r (Fintype.card s) q`, below the Halko–Martinsson–Tropp
factor of `NLAlib.variance_hutchpp_le_of_hasLaw_gaussianMatrix` and better when the rank $r$ is
close to $\lvert s \rvert$. From the exact variance and
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le`.
[EpperlyWebber2026]; there for the randomized SVD alone.
Result: hutchpp-variance -/
theorem variance_hutchpp_le_of_hasLaw_gaussianMatrix_of_rank_le [Nonempty t] (A : Matrix n n ℝ)
    {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} (hS : HasLaw S (gaussianMatrix n s) μ)
    (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) {r q : ℕ} (hr : A.rank ≤ r)
    (hsr : Fintype.card s ≤ r) (hq : q + 2 ≤ Fintype.card s) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ ≤
      2 / Fintype.card t * rotationInvariantFactor r (Fintype.card s) q *
        frobNorm (A - truncatedSVD A q) ^ 2 := by
  sorry

/-- **The variance of Gaussian Hutch++, nuclear form**: if the $n \times \lvert s \rvert$ sketch
test matrix $\mathbf{S}$ and the $n \times \ell$ residual test matrix $\mathbf{G}$, $\ell \ge 1$,
are independent and standard Gaussian, then for every real square $\mathbf{A}$ and every $r \ge 1$
with $2r + 1 \le \lvert s \rvert$,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] \le
\frac{\|\mathbf{A}\|_*^2}{\ell\, r}\,.$$
The Halko–Martinsson–Tropp factor is at most $2$ when $\lvert s \rvert \ge 2r + 1$, and
$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_r\|_{\mathsf{F}}^2 \le \|\mathbf{A}\|_*^2/(4r)$
(`NLAlib.frobNorm_sub_truncatedSVD_le_nuclearNorm_div`). With MMMW's parameters
$r = (m - 2)/8$, $\lvert s \rvert = (m + 2)/4 = 2r + 1$ and $\ell = (m - 2)/2$, so that
$m = 2\lvert s \rvert + \ell$, it is their $16\|\mathbf{A}\|_*^2/(m - 2)^2$. Asymptotic form:
`NLAlib.exists_forall_variance_hutchpp_le_of_hasLaw_gaussianMatrix`.
[MeyerMuscoMuscoWoodruff2021, Theorem 10 and Lemma 14]; [EpperlyTroppWebber2024, Theorem 1.1
(Hutch++ line)]; MMMW for $m$ products with the parameters above, Theorem 10 for positive
semidefinite $\mathbf{A}$ with $\operatorname{tr}^2\mathbf{A}$ (here
`Matrix.PosSemidef.variance_hutchpp_le_trace_sq_of_hasLaw_gaussianMatrix`).
Result: hutchpp-variance -/
theorem variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix [Nonempty t] (A : Matrix n n ℝ)
    {S : Ω → Matrix n s ℝ} {G : Ω → Matrix n t ℝ} (hS : HasLaw S (gaussianMatrix n s) μ)
    (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) {r : ℕ} (hr0 : 0 < r)
    (hr : 2 * r + 1 ≤ Fintype.card s) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ ≤
      nuclearNorm A ^ 2 / (Fintype.card t * r) := by
  sorry

/-- **The variance of Gaussian Hutch++ for a positive semidefinite matrix**: if the
$n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$ and the $n \times \ell$ residual test
matrix $\mathbf{G}$, $\ell \ge 1$, are independent and standard Gaussian, then for every real
positive semidefinite $\mathbf{A}$ and every $r \ge 1$ with $2r + 1 \le \lvert s \rvert$,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] \le
\frac{(\operatorname{tr}\mathbf{A})^2}{\ell\, r}\,,$$
`NLAlib.variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix` with
$\|\mathbf{A}\|_* = \operatorname{tr}\mathbf{A}$. With $r = (m - 2)/8$,
$\lvert s \rvert = (m + 2)/4$ and $\ell = (m - 2)/2$ it is
$16(\operatorname{tr}\mathbf{A})^2/(m - 2)^2$ for $m = 2\lvert s \rvert + \ell$ products.
[MeyerMuscoMuscoWoodruff2021, Theorem 10]; there with sign residual probes (see
`NLAlib.variance_hutchpp_of_hasLaw_rademacherMatrix`).
Result: hutchpp-variance -/
theorem _root_.Matrix.PosSemidef.variance_hutchpp_le_trace_sq_of_hasLaw_gaussianMatrix
    [Nonempty t] {A : Matrix n n ℝ} (hA : A.PosSemidef) {S : Ω → Matrix n s ℝ}
    {G : Ω → Matrix n t ℝ} (hS : HasLaw S (gaussianMatrix n s) μ)
    (hG : HasLaw G (gaussianMatrix n t) μ) (hSG : IndepFun S G μ) {r : ℕ} (hr0 : 0 < r)
    (hr : 2 * r + 1 ≤ Fintype.card s) :
    variance (fun ω => hutchpp A (S ω) (G ω)) μ ≤ A.trace ^ 2 / (Fintype.card t * r) := by
  sorry

/-- **$O(\eta^{-1/2})$ products suffice for Gaussian Hutch++ to reach variance
$\eta\|\mathbf{A}\|_*^2$**: there is an absolute constant $C > 0$ such that if the
$n \times \lvert s \rvert$ sketch test matrix $\mathbf{S}$ and the $n \times \lvert t \rvert$
residual test matrix $\mathbf{G}$ are independent and standard Gaussian, $0 < \eta \le 1$,
$\lvert s \rvert \ge C/\sqrt{\eta}$ and $\lvert t \rvert \ge C/\sqrt{\eta}$, then for every real
square $\mathbf{A}$,
$$\operatorname{Var}[\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})] \le
\eta\,\|\mathbf{A}\|_*^2\,,$$
with $m = 2\lvert s \rvert + \lvert t \rvert$ products in all. The asymptotic form of
`NLAlib.variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix`, proved from it with $C = 4$ and
$r = \lfloor (\lvert s \rvert - 1)/2 \rfloor$; the cap $\eta \le 1$ keeps $r \ge 1$.
[EpperlyTroppWebber2024, (1.10)]; [MeyerMuscoMuscoWoodruff2021, Theorem 10].
Asymptotic: NLAlib.variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix
Result: hutchpp-variance -/
theorem exists_forall_variance_hutchpp_le_of_hasLaw_gaussianMatrix :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n s t : Type} [MeasurableSpace Ω] [Fintype n] [Fintype s] [Fintype t]
      [DecidableEq n] (μ : Measure Ω) (A : Matrix n n ℝ) (S : Ω → Matrix n s ℝ)
      (G : Ω → Matrix n t ℝ) (η : ℝ),
      HasLaw S (gaussianMatrix n s) μ → HasLaw G (gaussianMatrix n t) μ → IndepFun S G μ →
      0 < η → η ≤ 1 → C / √η ≤ Fintype.card s → C / √η ≤ Fintype.card t →
      variance (fun ω => hutchpp A (S ω) (G ω)) μ ≤ η * nuclearNorm A ^ 2 := by
  sorry

end NLAlib
