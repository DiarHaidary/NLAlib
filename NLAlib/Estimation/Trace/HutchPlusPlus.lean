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
on the compressed residual (`NLAlib.trace_sub_hutchpp`), so it is unbiased whenever the residual
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
* `NLAlib.trace_sub_hutchpp`: the error identity; `NLAlib.hutchpp_eq_trace_of_rsvd_eq`,
  `NLAlib.hutchpp_eq_trace_of_rank_eq`: exactness when the sketch captures $\mathbf{A}$.
* `NLAlib.integral_hutchpp`: unbiasedness.
* `NLAlib.integral_norm_trace_sub_hutchpp_sq`: the mean-square error as an average over the sketch.
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
open scoped Matrix ENNReal

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

/-! #### Deterministic helpers -/

/-- The compression of $\mathbf{B}$ by the residual projector of the sketch of $\mathbf{A}$ is
no larger than $\mathbf{B}$ in the Frobenius norm. -/
private theorem frobNorm_compress_le (A B : Matrix n n 𝕜) (S : Matrix n s 𝕜) :
    frobNorm ((1 - rangeProjector (A * S)) * B * (1 - rangeProjector (A * S))) ≤ frobNorm B :=
  ((isStarProjection_one_sub_rangeProjector (A * S)).frobNorm_mul_right_le _).trans
    (frobNorm_one_sub_rangeProjector_mul_le (A * S) B)

/-- Compression by a residual projector commutes with taking the Hermitian part. -/
private theorem hermitianPart_compress (A : Matrix n n 𝕜) (S : Matrix n s 𝕜) :
    (1 - rangeProjector (A * S)) * hermitianPart A * (1 - rangeProjector (A * S)) =
      hermitianPart ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))) := by
  have h := hermitianPart_mul_mul_conjTranspose (1 - rangeProjector (A * S)) A
  rw [(isStarProjection_one_sub_rangeProjector (A * S)).conjTranspose_eq] at h
  exact h.symm

/-- The compressed Hermitian part is no larger than the error of the randomized SVD:
$\|(\mathbf{I} - \mathbf{P})\mathbf{H}(\mathbf{I} - \mathbf{P})\|_{\mathsf{F}} \le
\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}}$. -/
private theorem frobNorm_compress_hermitianPart_le (A : Matrix n n 𝕜) (S : Matrix n s 𝕜) :
    frobNorm ((1 - rangeProjector (A * S)) * hermitianPart A * (1 - rangeProjector (A * S))) ≤
      frobNorm (A - rsvd A S) := by
  rw [hermitianPart_compress, sub_rsvd]
  exact (frobNorm_hermitianPart_le _).trans
    ((isStarProjection_one_sub_rangeProjector (A * S)).frobNorm_mul_right_le _)

omit [DecidableEq n] in
/-- The Girard–Hutchinson estimate is at most
$\|\mathbf{B}\|_{\mathsf{F}}\|\mathbf{G}\|_{\mathsf{F}}^2$ in modulus. -/
private theorem norm_girardHutchinson_le (B : Matrix n n 𝕜) (g : Matrix n t 𝕜) :
    ‖girardHutchinson B g‖ ≤ frobNorm B * frobNorm g ^ 2 := by
  have h1 : ‖(gᴴ * B * g).trace‖ ≤ frobNorm B * frobNorm g ^ 2 := by
    refine (norm_trace_le_nuclearNorm _).trans ?_
    rw [Matrix.mul_assoc]
    refine (nuclearNorm_mul_le_frobNorm_mul_frobNorm _ _).trans ?_
    rw [frobNorm_conjTranspose]
    calc frobNorm g * frobNorm (B * g) ≤ frobNorm g * (frobNorm B * frobNorm g) :=
          mul_le_mul_of_nonneg_left (frobNorm_mul_le B g) (frobNorm_nonneg g)
      _ = frobNorm B * frobNorm g ^ 2 := by ring
  rw [girardHutchinson, norm_div, RCLike.norm_natCast]
  rcases Nat.eq_zero_or_pos (Fintype.card t) with h | h
  · rw [h, Nat.cast_zero, div_zero]
    exact mul_nonneg (frobNorm_nonneg _) (sq_nonneg _)
  · exact (div_le_self (norm_nonneg _) (by exact_mod_cast h)).trans h1

omit [DecidableEq n] in
/-- The trace is at most $\lvert n \rvert \|\mathbf{B}\|_{\mathsf{F}}$ in modulus. -/
private theorem norm_trace_le_card_mul_frobNorm (B : Matrix n n 𝕜) :
    ‖B.trace‖ ≤ Fintype.card n * frobNorm B := by
  rw [Matrix.trace]
  refine (norm_sum_le _ _).trans ?_
  simpa only [Matrix.diag_apply, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
    Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => norm_apply_le_frobNorm B i i

/-- The residual error is bounded by
$\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{G}\|_{\mathsf{F}}^2 +
\lvert n \rvert \|\mathbf{A}\|_{\mathsf{F}}$, uniformly in the sketch. -/
private theorem norm_girardHutchinson_compress_sub_trace_le (A : Matrix n n 𝕜)
    (S : Matrix n s 𝕜) (g : Matrix n t 𝕜) :
    ‖girardHutchinson ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))) g -
        ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))).trace‖ ≤
      frobNorm A * frobNorm g ^ 2 + Fintype.card n * frobNorm A := by
  have hΔ := frobNorm_compress_le A A S
  refine (norm_sub_le _ _).trans (add_le_add ?_ ?_)
  · exact (norm_girardHutchinson_le _ g).trans (mul_le_mul_of_nonneg_right hΔ (sq_nonneg _))
  · exact (norm_trace_le_card_mul_frobNorm _).trans
      (mul_le_mul_of_nonneg_left hΔ (Nat.cast_nonneg _))

omit [DecidableEq n] in
/-- Over $\mathbb{R}$ the Girard–Hutchinson estimate sees only the symmetric part. -/
private theorem girardHutchinson_hermitianPart (B : Matrix n n ℝ) (g : Matrix n t ℝ) :
    girardHutchinson (hermitianPart B) g = girardHutchinson B g := by
  rw [girardHutchinson, girardHutchinson, trace_conjTranspose_mul_hermitianPart_mul]

omit [DecidableEq n] in
/-- Over $\mathbb{R}$ the trace sees only the symmetric part. -/
private theorem trace_hermitianPart (B : Matrix n n ℝ) : (hermitianPart B).trace = B.trace := by
  classical
  simpa only [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] using
    trace_conjTranspose_mul_hermitianPart_mul (1 : Matrix n n ℝ) B

/-! #### Measurability and integrability helpers -/

private theorem measurable_one_sub_rangeProjector_mul (A : Matrix n n 𝕜) :
    Measurable fun S : Matrix n s 𝕜 => 1 - rangeProjector (A * S) :=
  measurable_const.matrix_sub
    (measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id))

private theorem measurable_compress (A B : Matrix n n 𝕜) :
    Measurable fun S : Matrix n s 𝕜 =>
      (1 - rangeProjector (A * S)) * B * (1 - rangeProjector (A * S)) :=
  ((measurable_one_sub_rangeProjector_mul A).matrix_mul measurable_const).matrix_mul
    (measurable_one_sub_rangeProjector_mul A)

omit [DecidableEq n] in
private theorem measurable_girardHutchinson :
    Measurable fun p : Matrix n n 𝕜 × Matrix n t 𝕜 => girardHutchinson p.1 p.2 := by
  unfold girardHutchinson
  exact (((Measurable.matrix_conjTranspose continuous_star.measurable measurable_snd).matrix_mul
    measurable_fst).matrix_mul measurable_snd).matrix_trace.div_const _

/-- The residual error as a function of the pair of test matrices is measurable. -/
private theorem measurable_girardHutchinson_compress_sub_trace (A : Matrix n n 𝕜) :
    Measurable fun p : Matrix n s 𝕜 × Matrix n t 𝕜 =>
      girardHutchinson ((1 - rangeProjector (A * p.1)) * A * (1 - rangeProjector (A * p.1))) p.2 -
        ((1 - rangeProjector (A * p.1)) * A * (1 - rangeProjector (A * p.1))).trace :=
  (measurable_girardHutchinson.comp
    (((measurable_compress A A).comp measurable_fst).prodMk measurable_snd)).sub
    ((measurable_compress A A).comp measurable_fst).matrix_trace

private theorem aemeasurable_of_memLp_apply {a b : Type*} [Countable a] [Countable b]
    {G : Ω → Matrix a b 𝕜} {p : ℝ≥0∞} (hG : ∀ i j, MemLp (fun ω => G ω i j) p μ) :
    AEMeasurable G μ :=
  aemeasurable_pi_lambda _ fun i => aemeasurable_pi_lambda _ fun j =>
    (hG i j).aestronglyMeasurable.aemeasurable

omit [Fintype s] [DecidableEq n] in
private theorem integrable_frobNorm_sq_of_memLp [IsFiniteMeasure μ] {G : Ω → Matrix n t 𝕜}
    (hG : ∀ i j, MemLp (fun ω => G ω i j) 2 μ) :
    Integrable (fun ω => frobNorm (G ω) ^ 2) μ := by
  simp only [frobNorm_sq_eq_sum]
  exact integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
    (hG i j).integrable_norm_pow' (p := 2)

omit [Fintype s] [DecidableEq n] in
private theorem integrable_frobNorm_pow_four_of_memLp [IsFiniteMeasure μ]
    {G : Ω → Matrix n t 𝕜} (hG : ∀ i j, MemLp (fun ω => G ω i j) 4 μ) :
    Integrable (fun ω => frobNorm (G ω) ^ 4) μ := by
  have hm : AEMeasurable G μ := aemeasurable_of_memLp_apply hG
  have hb : Integrable (fun ω => ((Fintype.card n * Fintype.card t : ℕ) : ℝ) *
      ∑ i, ∑ j, ‖G ω i j‖ ^ 4) μ :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
      (hG i j).integrable_norm_pow' (p := 4)).const_mul _
  refine hb.mono'
    ((continuous_frobNorm.measurable.comp_aemeasurable hm).pow_const 4).aestronglyMeasurable
    (ae_of_all _ fun ω => ?_)
  have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (n × t)))
    (f := fun p => ‖G ω p.1 p.2‖ ^ 2)
  rw [Real.norm_of_nonneg (by positivity), show frobNorm (G ω) ^ 4 = (frobNorm (G ω) ^ 2) ^ 2 by
    ring, frobNorm_sq_eq_sum]
  simpa only [Fintype.sum_prod_type, Finset.card_univ, Fintype.card_prod, ← pow_mul] using h

/-- **Conditioning on the sketch**: for independent $\mathbf{S}$, $\mathbf{G}$ and a measurable
$f$ dominated by an integrable function of $\mathbf{G}$,
$\mathbb{E} f(\mathbf{S}, \mathbf{G}) = \mathbb{E}_{\mathbf{S}}\mathbb{E}_{\mathbf{G}'}
f(\mathbf{S}, \mathbf{G}')$. -/
private theorem integral_comp_eq_integral_integral_of_norm_le [IsProbabilityMeasure μ]
    {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [NormedSpace ℝ E] {S : Ω → α} {G : Ω → β} (hS : AEMeasurable S μ) (hG : AEMeasurable G μ)
    (hSG : IndepFun S G μ) {f : α × β → E} (hf : StronglyMeasurable f) {b : β → ℝ}
    (hb : Integrable (fun ω => b (G ω)) μ) (hfb : ∀ x, ‖f x‖ ≤ b x.2) :
    ∫ ω, f (S ω, G ω) ∂μ = ∫ ω, ∫ ω', f (S ω, G ω') ∂μ ∂μ := by
  have hint : Integrable f ((μ.map S).prod (μ.map G)) := by
    rw [← (indepFun_iff_map_prod_eq_prod_map_map hS hG).1 hSG,
      integrable_map_measure hf.aestronglyMeasurable (hS.prodMk hG)]
    exact hb.mono' (hf.aestronglyMeasurable.comp_aemeasurable (hS.prodMk hG))
      (ae_of_all _ fun ω => hfb _)
  rw [IndepFun.integral_comp_eq_integral_integral hSG hS hG hint,
    integral_map hS hf.integral_prod_right'.aestronglyMeasurable]
  exact integral_congr_ae (ae_of_all _ fun ω =>
    integral_map hG (hf.comp_measurable measurable_prodMk_left).aestronglyMeasurable)

omit [DecidableEq n] in
private theorem integrable_girardHutchinson [IsFiniteMeasure μ] (B : Matrix n n 𝕜)
    {G : Ω → Matrix n t 𝕜} (hG : ∀ i j, MemLp (fun ω => G ω i j) 2 μ) :
    Integrable (fun ω => girardHutchinson B (G ω)) μ := by
  have hm : Measurable fun g : Matrix n t 𝕜 => girardHutchinson B g := by
    unfold girardHutchinson
    exact (((Measurable.matrix_conjTranspose continuous_star.measurable measurable_id).matrix_mul
      measurable_const).matrix_mul measurable_id).matrix_trace.div_const _
  exact ((integrable_frobNorm_sq_of_memLp hG).const_mul (frobNorm B)).mono'
    (hm.comp_aemeasurable (aemeasurable_of_memLp_apply hG)).aestronglyMeasurable
    (ae_of_all _ fun ω => norm_girardHutchinson_le B (G ω))

/-- A bounded measurable function of the sketch is integrable. -/
private theorem integrable_comp_of_norm_le [IsFiniteMeasure μ] {α : Type*} [MeasurableSpace α]
    {S : Ω → α} (hS : AEMeasurable S μ) {F : α → ℝ} (hF : Measurable F) {C : ℝ}
    (hC : ∀ x, ‖F x‖ ≤ C) : Integrable (fun ω => F (S ω)) μ :=
  (integrable_const C).mono' (hF.comp_aemeasurable hS).aestronglyMeasurable
    (ae_of_all _ fun _ => hC _)

omit [Fintype t] in
private theorem integrable_frobNorm_compress_hermitianPart_sq [IsFiniteMeasure μ]
    (A : Matrix n n 𝕜) {S : Ω → Matrix n s 𝕜} (hS : AEMeasurable S μ) :
    Integrable (fun ω => frobNorm ((1 - rangeProjector (A * S ω)) * hermitianPart A *
      (1 - rangeProjector (A * S ω))) ^ 2) μ :=
  integrable_comp_of_norm_le hS
    ((continuous_frobNorm.measurable.comp (measurable_compress A (hermitianPart A))).pow_const 2)
    (C := frobNorm (hermitianPart A) ^ 2) fun x => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_compress_le _ _ _) 2

/-- **Hutch++ with an orthonormal basis of the sketch**: if $\mathbf{Q}$ has orthonormal columns
and $\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}\mathbf{S}}$, then
$$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) =
\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) +
\mathsf{girardHutchinson}\bigl((\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{A}
(\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}}), \mathbf{G}\bigr)\,,$$
the form in which the papers state the algorithm. A bridge to `NLAlib.hutchpp`; such a
$\mathbf{Q}$ exists for every sketch (`NLAlib.HasOrthonormalCols.rangeProjector_eq`). The proof
uses only $\mathbf{Q}\mathbf{Q}^{\mathsf{H}} = \mathbf{P}_{\mathbf{A}\mathbf{S}}$ and cyclicity of
the trace; orthonormality is kept for the reading. -/
theorem HasOrthonormalCols.hutchpp_eq {q : Type*} [Fintype q] [DecidableEq q] {Q : Matrix n q 𝕜}
    (_hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} {S : Matrix n s 𝕜}
    (hQS : Q * Qᴴ = rangeProjector (A * S)) (G : Matrix n t 𝕜) :
    hutchpp A S G =
      (Qᴴ * A * Q).trace + girardHutchinson ((1 - Q * Qᴴ) * A * (1 - Q * Qᴴ)) G := by
  rw [hutchpp, rsvd, ← hQS, Matrix.mul_assoc Q Qᴴ A, Matrix.trace_mul_comm Q (Qᴴ * A)]

/-- **The error of Hutch++ is the error of Girard–Hutchinson on the compressed residual**: for
every square $\mathbf{A}$ and all test matrices $\mathbf{S}$, $\mathbf{G}$, with
$\mathbf{\Delta} = (\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})\mathbf{A}
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})$,
$$\operatorname{tr}\mathbf{A} - \mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) =
\operatorname{tr}\mathbf{\Delta} - \mathsf{girardHutchinson}(\mathbf{\Delta}, \mathbf{G})\,.$$
Deterministic; from the trace split
`IsIdempotentElem.trace_mul_add_trace_one_sub_mul_mul_one_sub`.
[MeyerMuscoMuscoWoodruff2021, §3, proof of Theorem 1]; [EpperlyTroppWebber2024, §1.1.2]. -/
theorem trace_sub_hutchpp (A : Matrix n n 𝕜) (S : Matrix n s 𝕜) (G : Matrix n t 𝕜) :
    A.trace - hutchpp A S G =
      ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))).trace -
        girardHutchinson ((1 - rangeProjector (A * S)) * A * (1 - rangeProjector (A * S))) G := by
  have h := (isStarProjection_rangeProjector (A * S)).isIdempotentElem
    |>.trace_mul_add_trace_one_sub_mul_mul_one_sub A
  rw [hutchpp, rsvd]
  linear_combination -h

/-- **Hutch++ is exact when the randomized SVD is**: if
$\mathsf{rsvd}(\mathbf{A}, \mathbf{S}) = \mathbf{A}$, then
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) = \operatorname{tr}\mathbf{A}$ for every
residual test matrix $\mathbf{G}$: the residual $(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})
\mathbf{A} = \mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})$ vanishes, hence so does the
compressed residual and its Girard–Hutchinson estimate. In particular Hutch++ is exact when
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{S})\|_{\mathsf{F}} = 0$. -/
theorem hutchpp_eq_trace_of_rsvd_eq {A : Matrix n n 𝕜} {S : Matrix n s 𝕜} (h : rsvd A S = A)
    (G : Matrix n t 𝕜) : hutchpp A S G = A.trace := by
  have h0 : (1 - rangeProjector (A * S)) * A = 0 := by rw [← sub_rsvd, h, sub_self]
  rw [hutchpp, h, h0, Matrix.zero_mul, girardHutchinson, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.trace_zero, zero_div, add_zero]

/-- **Hutch++ is exact when the sketch captures the range**: if
$\operatorname{rank}(\mathbf{A}\mathbf{S}) = \operatorname{rank}\mathbf{A}$, then
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) = \operatorname{tr}\mathbf{A}$ for every
residual test matrix $\mathbf{G}$: the randomized SVD recovers $\mathbf{A}$
(`NLAlib.rsvd_eq_self_of_rank_eq`) and the compressed residual is $\mathbf{0}$. -/
theorem hutchpp_eq_trace_of_rank_eq {A : Matrix n n 𝕜} {S : Matrix n s 𝕜}
    (h : (A * S).rank = A.rank) (G : Matrix n t 𝕜) : hutchpp A S G = A.trace :=
  hutchpp_eq_trace_of_rsvd_eq (rsvd_eq_self_of_rank_eq h) G

/-- Hutch++ is a Borel measurable function of the pair of test matrices
$(\mathbf{S}, \mathbf{G})$, from `NLAlib.measurable_rangeProjector`. -/
theorem measurable_hutchpp (A : Matrix n n 𝕜) :
    Measurable fun p : Matrix n s 𝕜 × Matrix n t 𝕜 => hutchpp A p.1 p.2 := by
  have h := ((measurable_rsvd (l := s) A).comp
    (measurable_fst (β := Matrix n t 𝕜))).matrix_trace.add
    ((measurable_girardHutchinson (n := n) (t := t) (𝕜 := 𝕜)).comp
      (((measurable_compress A A).comp measurable_fst).prodMk measurable_snd))
  unfold hutchpp
  exact h

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
  have hL2 (i : n) (j : t) : MemLp (fun ω => G ω i j) 2 μ := (hG j).memLp i
  have hGm := aemeasurable_of_memLp_apply hL2
  have hb : Integrable (fun ω => frobNorm A * frobNorm (G ω) ^ 2 + Fintype.card n * frobNorm A) μ :=
    ((integrable_frobNorm_sq_of_memLp hL2).const_mul _).add (integrable_const _)
  have hm := measurable_girardHutchinson_compress_sub_trace (s := s) (t := t) A
  have hint : Integrable (fun ω =>
      girardHutchinson ((1 - rangeProjector (A * S ω)) * A * (1 - rangeProjector (A * S ω))) (G ω) -
        ((1 - rangeProjector (A * S ω)) * A * (1 - rangeProjector (A * S ω))).trace) μ :=
    hb.mono' (hm.comp_aemeasurable (hS.prodMk hGm)).aestronglyMeasurable
      (ae_of_all _ fun ω => norm_girardHutchinson_compress_sub_trace_le A (S ω) (G ω))
  have he (ω : Ω) : hutchpp A (S ω) (G ω) = A.trace +
      (girardHutchinson ((1 - rangeProjector (A * S ω)) * A * (1 - rangeProjector (A * S ω)))
        (G ω) - ((1 - rangeProjector (A * S ω)) * A * (1 - rangeProjector (A * S ω))).trace) := by
    linear_combination -(trace_sub_hutchpp A (S ω) (G ω))
  simp only [he]
  rw [integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul,
    integral_comp_eq_integral_integral_of_norm_le hS hGm hSG hm.stronglyMeasurable
      (b := fun g => frobNorm A * frobNorm g ^ 2 + Fintype.card n * frobNorm A) hb
      fun x => norm_girardHutchinson_compress_sub_trace_le A x.1 x.2]
  have hinner (u : Matrix n s 𝕜) : ∫ ω', (girardHutchinson ((1 - rangeProjector (A * u)) * A *
      (1 - rangeProjector (A * u))) (G ω') -
        ((1 - rangeProjector (A * u)) * A * (1 - rangeProjector (A * u))).trace) ∂μ = 0 := by
    rw [integral_sub (integrable_girardHutchinson _ hL2) (integrable_const _),
      integral_girardHutchinson hG, integral_const, probReal_univ, one_smul, sub_self]
  simp only [hinner, integral_zero, add_zero]

/-- **The mean-square error of Hutch++ is an average over the sketch**: if the sketch test matrix
$\mathbf{S}$ is almost everywhere measurable, the residual test matrix $\mathbf{G}$ is independent
of it and every entry of $\mathbf{G}$ has a finite fourth moment, then for every square
$\mathbf{A}$, with $\mathbf{\Delta}(\mathbf{S}) = (\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})
\mathbf{A}(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{S}})$ and $\mathbf{G}'$ an independent copy
of $\mathbf{G}$ (the inner integral),
$$\mathbb{E}\,\lvert \operatorname{tr}\mathbf{A} -
\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G}) \rvert^2 =
\mathbb{E}_{\mathbf{S}}\,\mathbb{E}_{\mathbf{G}'}
\lvert \operatorname{tr}\mathbf{\Delta}(\mathbf{S}) -
\mathsf{girardHutchinson}(\mathbf{\Delta}(\mathbf{S}), \mathbf{G}') \rvert^2\,.$$
No isotropy, no independence of the columns and no column is needed; the per-law formulas of
`NLAlib.integral_norm_trace_sub_girardHutchinson_sq` evaluate the inner integral.
[MeyerMuscoMuscoWoodruff2021, proof of Theorem 10, (2)]; there as the law of total variance with
Gaussian test matrices. -/
theorem integral_norm_trace_sub_hutchpp_sq [IsProbabilityMeasure μ] (A : Matrix n n 𝕜)
    {S : Ω → Matrix n s 𝕜} {G : Ω → Matrix n t 𝕜} (hS : AEMeasurable S μ)
    (hG : ∀ i j, MemLp (fun ω => G ω i j) 4 μ) (hSG : IndepFun S G μ) :
    ∫ ω, ‖A.trace - hutchpp A (S ω) (G ω)‖ ^ 2 ∂μ =
      ∫ ω, ∫ ω', ‖((1 - rangeProjector (A * S ω)) * A * (1 - rangeProjector (A * S ω))).trace -
        girardHutchinson ((1 - rangeProjector (A * S ω)) * A *
          (1 - rangeProjector (A * S ω))) (G ω')‖ ^ 2 ∂μ ∂μ := by
  have hGm := aemeasurable_of_memLp_apply hG
  have hL2 (i : n) (j : t) : MemLp (fun ω => G ω i j) 2 μ :=
    (hG i j).mono_exponent (by norm_num)
  have hb : Integrable (fun ω => 2 * (frobNorm A ^ 2 * frobNorm (G ω) ^ 4) +
      2 * (Fintype.card n * frobNorm A) ^ 2) μ :=
    (((integrable_frobNorm_pow_four_of_memLp hG).const_mul _).const_mul _).add (integrable_const _)
  simp only [trace_sub_hutchpp, norm_sub_rev (Matrix.trace _)]
  refine integral_comp_eq_integral_integral_of_norm_le hS hGm hSG
    ((measurable_girardHutchinson_compress_sub_trace A).norm.pow_const 2).stronglyMeasurable
    (b := fun g => 2 * (frobNorm A ^ 2 * frobNorm g ^ 4) + 2 * (Fintype.card n * frobNorm A) ^ 2)
    hb fun x => ?_
  have h := norm_girardHutchinson_compress_sub_trace_le A x.1 x.2
  have h0 := norm_nonneg (girardHutchinson ((1 - rangeProjector (A * x.1)) * A *
    (1 - rangeProjector (A * x.1))) x.2 -
      ((1 - rangeProjector (A * x.1)) * A * (1 - rangeProjector (A * x.1))).trace)
  rw [norm_pow, norm_norm]
  nlinarith [sq_nonneg (frobNorm A * frobNorm x.2 ^ 2 - Fintype.card n * frobNorm A),
    mul_le_mul h h h0 (h0.trans h)]

omit [DecidableEq n] in
/-- The mean-square error of Girard–Hutchinson with a standard Gaussian test matrix, for a fixed
real $\mathbf{B}$: $(2/\ell)\|\mathbf{H}\|_{\mathsf{F}}^2$ with $\mathbf{H}$ the symmetric
part of $\mathbf{B}$. -/
private theorem integral_girardHutchinson_sub_trace_sq_of_hasLaw_gaussianMatrix [Nonempty t]
    {G : Ω → Matrix n t ℝ} (hG : HasLaw G (gaussianMatrix n t) μ) (B : Matrix n n ℝ) :
    ∫ ω, (girardHutchinson B (G ω) - B.trace) ^ 2 ∂μ =
      2 / Fintype.card t * frobNorm (hermitianPart B) ^ 2 := by
  classical
  have := hG.isProbabilityMeasure_iff.2 inferInstance
  have hcol := hasLaw_col_of_hasLaw_gaussianMatrix hG
  have hX (j : t) := isIsotropic_of_hasLaw_gaussianVector (hcol j)
  have hL4 (j : t) (i : n) : MemLp (fun ω => G ω i j) 4 μ :=
    (((hcol j).eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
      (memLp_id_gaussianReal' 4 (by simp))
  have e (ω : Ω) : girardHutchinson B (G ω) - B.trace =
      girardHutchinson (hermitianPart B) (G ω) - (hermitianPart B).trace := by
    rw [girardHutchinson_hermitianPart, trace_hermitianPart]
  have hH := isHermitian_hermitianPart B
  have h := integral_norm_trace_sub_girardHutchinson_sq (iIndepFun_col_of_hasLaw_gaussianMatrix hG)
    hX (A := hermitianPart B) (fun j => memLp_quadForm (hL4 j) _)
    (v := 2 * frobNorm (hermitianPart B) ^ 2) fun j => by
      rw [← variance_quadForm_of_hasLaw_gaussianVector (hcol j) hH,
        variance_eq_integral (memLp_quadForm (hL4 j) _).aestronglyMeasurable.aemeasurable,
        (hX j).integral_quadForm]
      simp only [Real.norm_eq_abs, sq_abs]
  simp only [norm_sub_rev (Matrix.trace _), Real.norm_eq_abs, sq_abs] at h
  simp only [e, h]
  ring

omit [DecidableEq n] in
/-- The columns of $\mathbf{G}$ are the rows of $\mathbf{G}^{\mathsf{H}}$: a sign law on the rows
of $\mathbf{G}^{\mathsf{H}}$ gives independent sign columns of $\mathbf{G}$. -/
private theorem hasLaw_col_of_hasLaw_conjTranspose_rademacherMatrix {G : Ω → Matrix n t ℝ}
    (hG : HasLaw (fun ω => (G ω)ᴴ) (rademacherMatrix t n) μ) :
    (∀ j, HasLaw (fun ω i => G ω i j) (rademacherVector n) μ) ∧
      iIndepFun (fun j ω i => G ω i j) μ := by
  have e (j : t) : (fun ω => (G ω)ᴴ j) = fun ω i => G ω i j := by
    funext ω i
    simp only [Matrix.conjTranspose_apply, star_trivial]
  refine ⟨fun j => ?_, ?_⟩
  · convert hG.eval j using 1
    exact (e j).symm
  · convert hG.iIndepFun_eval using 1
    exact (funext e).symm

omit [DecidableEq n] in
/-- The mean-square error of Girard–Hutchinson with sign probes, for a fixed real $\mathbf{B}$:
$(2/\ell)(\|\mathbf{H}\|_{\mathsf{F}}^2 - \sum_i \mathbf{H}_{i,i}^2)$ with $\mathbf{H}$
the symmetric part of $\mathbf{B}$. -/
private theorem integral_girardHutchinson_sub_trace_sq_of_hasLaw_rademacherMatrix [Nonempty t]
    {G : Ω → Matrix n t ℝ} (hG : HasLaw (fun ω => (G ω)ᴴ) (rademacherMatrix t n) μ)
    (B : Matrix n n ℝ) :
    ∫ ω, (girardHutchinson B (G ω) - B.trace) ^ 2 ∂μ =
      2 / Fintype.card t * (frobNorm (hermitianPart B) ^ 2 - ∑ i, hermitianPart B i i ^ 2) := by
  classical
  have := hG.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨hcol, hind⟩ := hasLaw_col_of_hasLaw_conjTranspose_rademacherMatrix hG
  have hX (j : t) := isIsotropic_of_hasLaw_rademacherVector (hcol j)
  have hL4 (j : t) (i : n) : MemLp (fun ω => G ω i j) 4 μ :=
    memLp_of_hasLaw_rademacherVector (hcol j) 4 i
  have e (ω : Ω) : girardHutchinson B (G ω) - B.trace =
      girardHutchinson (hermitianPart B) (G ω) - (hermitianPart B).trace := by
    rw [girardHutchinson_hermitianPart, trace_hermitianPart]
  have hH := isHermitian_hermitianPart B
  have h := integral_norm_trace_sub_girardHutchinson_sq hind hX (A := hermitianPart B)
    (fun j => memLp_quadForm (hL4 j) _)
    (v := 2 * (frobNorm (hermitianPart B) ^ 2 - ∑ i, hermitianPart B i i ^ 2)) fun j => by
      rw [← variance_quadForm_of_hasLaw_rademacherVector (hcol j) hH,
        variance_eq_integral (memLp_quadForm (hL4 j) _).aestronglyMeasurable.aemeasurable,
        (hX j).integral_quadForm]
      simp only [Real.norm_eq_abs, sq_abs]
  simp only [norm_sub_rev (Matrix.trace _), Real.norm_eq_abs, sq_abs] at h
  simp only [e, h]
  ring

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
  have := hG.isProbabilityMeasure_iff.2 inferInstance
  have hcol := hasLaw_col_of_hasLaw_gaussianMatrix hG
  have hL4 (i : n) (j : t) : MemLp (fun ω => G ω i j) 4 μ :=
    ((((hcol j).eval i).memLp_comp_iff (f := id) aestronglyMeasurable_id).2
      (memLp_id_gaussianReal' 4 (by simp)))
  have hm' := (measurable_hutchpp (s := s) (t := t) A).comp_aemeasurable
    (hS.prodMk (aemeasurable_of_memLp_apply hL4))
  have hm : AEMeasurable (fun ω => hutchpp A (S ω) (G ω)) μ := hm'
  have hmean := integral_hutchpp A hS hSG fun j => isIsotropic_of_hasLaw_gaussianVector (hcol j)
  have h3 := integral_norm_trace_sub_hutchpp_sq A hS hL4 hSG
  simp only [norm_sub_rev (Matrix.trace _), Real.norm_eq_abs, sq_abs] at h3
  rw [variance_eq_integral hm]
  simp only [hmean]
  rw [h3, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [hermitianPart_compress]
  exact integral_girardHutchinson_sub_trace_sq_of_hasLaw_gaussianMatrix hG _

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
  have := hG.isProbabilityMeasure_iff.2 inferInstance
  obtain ⟨hcol, -⟩ := hasLaw_col_of_hasLaw_conjTranspose_rademacherMatrix hG
  have hL4 (i : n) (j : t) : MemLp (fun ω => G ω i j) 4 μ :=
    memLp_of_hasLaw_rademacherVector (hcol j) 4 i
  have hm' := (measurable_hutchpp (s := s) (t := t) A).comp_aemeasurable
    (hS.prodMk (aemeasurable_of_memLp_apply hL4))
  have hm : AEMeasurable (fun ω => hutchpp A (S ω) (G ω)) μ := hm'
  have hmean := integral_hutchpp A hS hSG fun j => isIsotropic_of_hasLaw_rademacherVector (hcol j)
  have h3 := integral_norm_trace_sub_hutchpp_sq A hS hL4 hSG
  simp only [norm_sub_rev (Matrix.trace _), Real.norm_eq_abs, sq_abs] at h3
  rw [variance_eq_integral hm]
  simp only [hmean]
  rw [h3, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  simp only [hermitianPart_compress]
  exact integral_girardHutchinson_sub_trace_sq_of_hasLaw_rademacherMatrix hG _

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
  have := hG.isProbabilityMeasure_iff.2 inferInstance
  have hint : Integrable (fun ω =>
      frobNorm ((1 - rangeProjector (A * S ω)) * A * rangeProjector (A * S ω)) ^ 2) μ :=
    integrable_comp_of_norm_le hS ((continuous_frobNorm.measurable.comp
      (((measurable_one_sub_rangeProjector_mul A).matrix_mul measurable_const).matrix_mul
        (measurable_rangeProjector.comp (measurable_const.matrix_mul measurable_id)))).pow_const 2)
      (C := frobNorm A ^ 2) fun x => by
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        exact pow_le_pow_left₀ (frobNorm_nonneg _)
          (((isStarProjection_rangeProjector _).frobNorm_mul_right_le _).trans
            (frobNorm_one_sub_rangeProjector_mul_le _ _)) 2
  rw [NLAlib.variance_hutchpp_of_hasLaw_gaussianMatrix A hS hG hSG, hA.hermitianPart_eq,
    ← integral_sub (integrable_frobNorm_sub_rsvd_sq A hS) hint]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have h := frobNorm_one_sub_rangeProjector_mul_sq_eq_add (A * S ω) A
  simp only [sub_rsvd]
  linarith

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
  filter_upwards [ae_rsvd_eq_self_of_hasLaw_gaussianMatrix A hS hA] with ω hω
  exact hutchpp_eq_trace_of_rsvd_eq hω (G ω)

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
  have := hS.isProbabilityMeasure_iff.2 inferInstance
  rw [variance_hutchpp_of_hasLaw_gaussianMatrix A hS.aemeasurable hG hSG, mul_assoc]
  refine mul_le_mul_of_nonneg_left (le_trans ?_
    (integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix A hS hr)) (by positivity)
  exact integral_mono (integrable_frobNorm_compress_hermitianPart_sq A hS.aemeasurable)
    (integrable_frobNorm_sub_rsvd_sq A hS.aemeasurable) fun ω =>
      pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_compress_hermitianPart_le A (S ω)) 2

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
  have := hS.isProbabilityMeasure_iff.2 inferInstance
  rw [variance_hutchpp_of_hasLaw_gaussianMatrix A hS.aemeasurable hG hSG, mul_assoc]
  refine mul_le_mul_of_nonneg_left (le_trans ?_
    (integral_frobNorm_sub_rsvd_sq_le_of_hasLaw_gaussianMatrix_of_rank_le A hS hr hsr hq))
    (by positivity)
  exact integral_mono (integrable_frobNorm_compress_hermitianPart_sq A hS.aemeasurable)
    (integrable_frobNorm_sub_rsvd_sq A hS.aemeasurable) fun ω =>
      pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_compress_hermitianPart_le A (S ω)) 2

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
  refine (variance_hutchpp_le_of_hasLaw_gaussianMatrix A hS hG hSG (r := r) (by omega)).trans ?_
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr0
  have hℓ : (0 : ℝ) < Fintype.card t := by exact_mod_cast Fintype.card_pos
  have hq : (2 * r + 1 : ℝ) ≤ Fintype.card s := by exact_mod_cast hr
  have hfac : gaussianProjectionFactor r (Fintype.card s) ≤ 2 := by
    rw [gaussianProjectionFactor_def]
    have hpos : (0 : ℝ) < Fintype.card s - r - 1 := by linarith
    have := (div_le_one hpos).2 (show (r : ℝ) ≤ Fintype.card s - r - 1 by linarith)
    linarith
  have hsq : frobNorm (A - truncatedSVD A r) ^ 2 ≤ nuclearNorm A ^ 2 / (4 * r) := by
    have h := pow_le_pow_left₀ (frobNorm_nonneg _)
      (frobNorm_sub_truncatedSVD_le_nuclearNorm_div A hr0) 2
    rwa [div_pow, mul_pow, Real.sq_sqrt hr'.le, show (2 : ℝ) ^ 2 = 4 by norm_num] at h
  calc 2 / (Fintype.card t : ℝ) * gaussianProjectionFactor r (Fintype.card s) *
        frobNorm (A - truncatedSVD A r) ^ 2
      ≤ 2 / (Fintype.card t : ℝ) * 2 * (nuclearNorm A ^ 2 / (4 * r)) := by gcongr
    _ = nuclearNorm A ^ 2 / (Fintype.card t * r) := by
        field_simp
        ring

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
  have h := variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix A hS hG hSG hr0 hr
  rwa [hA.nuclearNorm_eq_re_trace, RCLike.re_to_real] at h

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
  refine ⟨4, by norm_num, ?_⟩
  intro Ω n s t _ _ _ _ _ μ A S G η hS hG hSG hη hη1 hs ht
  have hsη : 0 < √η := Real.sqrt_pos.2 hη
  set x := 1 / √η with hx
  have hx1 : 1 ≤ x := by
    rw [hx, le_div_iff₀ hsη, one_mul]
    exact Real.sqrt_le_one.mpr hη1
  have hxx : x * x = 1 / η := by
    rw [hx, div_mul_div_comm, one_mul, Real.mul_self_sqrt hη.le]
  have h4 : 4 / √η = 4 * x := by rw [hx, mul_one_div]
  rw [h4] at hs ht
  have hq4 : 4 ≤ Fintype.card s := by exact_mod_cast (show (4 : ℝ) ≤ Fintype.card s by linarith)
  have hℓ : 0 < Fintype.card t := by exact_mod_cast (show (0 : ℝ) < Fintype.card t by linarith)
  have : Nonempty t := Fintype.card_pos_iff.mp hℓ
  set r := (Fintype.card s - 1) / 2 with hr
  have hr0 : 0 < r := by omega
  have hr1 : 2 * r + 1 ≤ Fintype.card s := by omega
  refine (variance_hutchpp_le_nuclearNorm_of_hasLaw_gaussianMatrix A hS hG hSG hr0 hr1).trans ?_
  have hr2 : (Fintype.card s : ℝ) ≤ 2 * r + 2 := by
    exact_mod_cast (show Fintype.card s ≤ 2 * r + 2 by omega)
  have hrx : x ≤ r := by linarith
  have hℓx : x ≤ Fintype.card t := by linarith
  have hprod : 1 / η ≤ Fintype.card t * r := by
    rw [← hxx]
    exact mul_le_mul hℓx hrx (by linarith) (by linarith)
  have hpos : (0 : ℝ) < Fintype.card t * r := by
    have : (0 : ℝ) < 1 / η := by positivity
    linarith
  have h1 : 1 ≤ η * (Fintype.card t * r) := by
    have := mul_le_mul_of_nonneg_left hprod hη.le
    rwa [mul_one_div_cancel hη.ne'] at this
  rw [div_le_iff₀ hpos]
  nlinarith [sq_nonneg (nuclearNorm A)]

end NLAlib
