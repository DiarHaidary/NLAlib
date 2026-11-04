/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.EarlyTruncation
public import NLAlib.LowRank.Oblivious.RangeFinder
public import NLAlib.Sketching.Structured.SRHTMultiplication

/-!
# The randomized SVD with an SRHT test matrix

The SRHT instances of `NLAlib.LowRank.Oblivious.RangeFinder`, for the family of
`NLAlib.Sketching.Structured.SRHT`: a test matrix $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$
whose sketch $\mathbf{\Omega}^{\mathsf{H}}$ is a subsampled randomized transform of a bounded
orthonormal $\mathbf{F}$ with bound $\beta$ (`NLAlib.IsBoundedOrthonormal`), without replacement
(`NLAlib.srht`, $\ell \le n$) or with replacement (`NLAlib.srhtWithReplacement`). Two routes, both
at a constant factor: the injection route, factor $1 + 2t$ at failure probability
$\delta + 1/t$, in both models; and, without replacement only, the bounded-sketch route, factor
$1 + 2n/\ell$ at failure probability $\delta$ in every quadratic unitarily invariant norm, since
there $\|\mathbf{\Omega}\|_2 = \sqrt{n/\ell}$ almost surely
(`NLAlib.HasOrthonormalCols.ae_specNorm_eq_of_hasLaw_srht`;
with replacement, repeated rows break it). Both use the family's injection at constant $1/2$. Any
`RCLike` field.

The constant-factor statements have no accuracy parameter and no asymptotic form; in $O(\cdot)$
form their size is the family's injection size,
`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_srht` and its with-replacement twin.
The $(1 + \varepsilon)$ forms, randomized SVD and early truncation, go through the JL moment of a
real SRHT at $p = 2$ (`NLAlib.hasJLMoment_of_hasLaw_srht`), hence $1/\delta$ in their second size;
a $\log(1/\delta)$ form
through spectral approximate multiplication is quadratic in $k$ and is not stated (§5.5 there).

**Statements with no per-family form.** Nyström, generalized Nyström and the truncations apply
through the family's OSI:
```
isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionDim_le hF hX hln k hε hδ hl
isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionDim_le hF hX k
  hε hδ hl
```
with `hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ` (respectively `srhtWithReplacement`).

## Main results

* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`,
  `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srhtWithReplacement`: the injection
  route.
* `SymmetricGauge.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_srht`:
  the bounded-sketch route, HMT's SRFT theorem.
* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht_of_le_card`,
  `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht`: the
  $(1 + \varepsilon)$ forms, real, with their asymptotic forms
  `exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht` and
  `exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l 𝕜}

/-- **The randomized SVD with an SRHT test matrix**: if the sketch $\mathbf{\Omega}^{\mathsf{H}}$
is the SRHT without replacement of a bounded orthonormal $\mathbf{F}$ with bound $\beta$,
$\ell$ nonempty, $\ell \le n$, $\delta, t > 0$ and $\ell$ is at
least <!-- value samplingInjectionDim k L (1/2) (\delta/2) -->
$$\frac{2 L \log(k/(\delta/2))}{(1/2)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/2) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 2)` and the size is
`samplingInjectionDim k L (1 / 2) (δ / 2)`, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 2t)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. Its bounded-sketch neighbour, failure probability
$\delta$ and factor $1 + 2n/\ell$ in every quadratic unitarily invariant norm, is
`NLAlib.SymmetricGauge.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_srht`;
this one is better when $t < n/\ell$. In $O(\cdot)$ form the size is the family's injection size,
$O(\beta(k + \log(n/\delta))\log(k/\delta))$
(`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_srht`); a constant-factor result
has no asymptotic form of its own.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2]; there an OSI and $C/\alpha$ at probability $9/10$.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht [Nonempty l] {F : Matrix n n 𝕜}
    {β : ℝ} (hF : IsBoundedOrthonormal F β) (A : Matrix m n 𝕜)
    (hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ) (hln : Fintype.card l ≤ Fintype.card n) {k : ℕ}
    {δ t : ℝ} (hδ : 0 < δ) (ht : 0 < t)
    (hl : samplingInjectionDim k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hln)
  have h := (isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionDim_le hF hX hln k
    (by norm_num) hδ hl).measureReal_frobNorm_sub_rsvd_sq_gt_le (A := A) (by norm_num) ht
  rwa [show (1 : ℝ) + t / (1 - 1 / 2) = 1 + 2 * t by ring] at h

/-- **The randomized SVD with an SRHT test matrix, with replacement**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ is the SRHT with i.i.d. uniform row indices of a bounded
orthonormal $\mathbf{F}$ with bound $\beta$, $\ell$ and $n$ nonempty, $\delta, t > 0$ and
$\ell$ is at
least <!-- value samplingInjectionDim k L (1/2) (\delta/2) -->
$$\frac{2 L \log(k/(\delta/2))}{(1/2)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/2) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 2)` and the size is
`samplingInjectionDim k L (1 / 2) (δ / 2)`, then
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + 2t)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + 1/t$. No $\ell \le n$, and no bounded-sketch twin: with
replacement $\|\mathbf{\Omega}\|_2$ is not constant. The without-replacement form is
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`. In $O(\cdot)$ form the size is
the family's injection size
(`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement`); a
constant-factor result has no asymptotic form of its own.
[CamanoEpperlyMeyerTropp2025, Theorem 2.2]; there an OSI and $C/\alpha$ at probability $9/10$.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srhtWithReplacement [Nonempty l]
    [Nonempty n] {F : Matrix n n 𝕜} {β : ℝ} (hF : IsBoundedOrthonormal F β) (A : Matrix m n 𝕜)
    (hX : HasLaw (fun ω => (X ω)ᴴ) (srhtWithReplacement l F) μ) {k : ℕ} {δ t : ℝ} (hδ : 0 < δ)
    (ht : 0 < t)
    (hl : samplingInjectionDim k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  have : IsProbabilityMeasure μ :=
    hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srhtWithReplacement F)
  have h := (isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionDim_le
    hF hX k (by norm_num) hδ hl).measureReal_frobNorm_sub_rsvd_sq_gt_le (A := A) (by norm_num) ht
  rwa [show (1 : ℝ) + t / (1 - 1 / 2) = 1 + 2 * t by ring] at h

/-- **The randomized SVD with an SRHT test matrix, bounded-sketch form** (HMT's SRFT theorem): if
the sketch $\mathbf{\Omega}^{\mathsf{H}}$ is the SRHT without replacement of a bounded
orthonormal $\mathbf{F}$ with bound $\beta$, $\ell \ge 1$, $\ell \le n$, $\delta > 0$ and $\ell$
is at least <!-- value samplingInjectionDim k L (1/2) (\delta/2) -->
$$\frac{2 L \log(k/(\delta/2))}{(1/2)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/2) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 2)` and the size is
`samplingInjectionDim k L (1 / 2) (δ / 2)`, then for every unitarily invariant norm
$$\bigl\|(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))^{\mathsf{H}}
(\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega}))\bigr\|_{\Phi} \le
\Bigl(1 + \frac{2n}{\ell}\Bigr)\bigl\|(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)^{\mathsf{H}}
(\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k)\bigr\|_{\Phi}$$
except with probability $\delta$: in spectral norm
$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_2^2 \le
(1 + 2n/\ell)\,\sigma_k(\mathbf{A})^2$, in Frobenius norm the same factor against
$\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$. The injection-route neighbour,
factor $1 + 2t$ at failure probability $\delta + 1/t$, is
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`; this one is better when
$n/\ell < t$, and needs no Markov step. In $O(\cdot)$ form the size is the family's injection size
(`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_srht`).
[HalkoMartinssonTropp2011, Theorem 11.2]; there the spectral and Frobenius norms, factor
$1 + 7n/\ell$, failure probability $O(k^{-1})$ and $\ell$ of order
$(k + \log n)\log k$; here a sharper factor ($1 + 2n/\ell$ against $1 + 7n/\ell$), an explicit
failure probability and an incomparable size condition.
Result: randomized-svd-tail -/
theorem SymmetricGauge.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_srht
    [Nonempty l] (Φ : SymmetricGauge) {F : Matrix n n 𝕜} {β : ℝ} (hF : IsBoundedOrthonormal F β)
    (A : Matrix m n 𝕜) (hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ)
    (hln : Fintype.card l ≤ Fintype.card n) {k : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hl : samplingInjectionDim k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * Fintype.card n / Fintype.card l) *
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤ δ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hln)
  have hinj := (isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionDim_le hF hX hln k
    (by norm_num) hδ hl).hasSubspaceInjection (U := (truncatedSVD A k)ᴴ)
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)
  have hL : ∀ᵐ ω ∂μ, specNorm (X ω) ≤ √(Fintype.card n / Fintype.card l : ℝ) := by
    filter_upwards [HasOrthonormalCols.ae_specNorm_eq_of_hasLaw_srht hF.hasOrthonormalCols hX] with
      ω hω
    rw [← specNorm_conjTranspose, hω]
  have h := hinj.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_specNorm_le
    (by norm_num) hL Φ
  rwa [Real.sq_sqrt (by positivity),
    show (1 : ℝ) + Fintype.card n / Fintype.card l / (1 - 1 / 2) =
      1 + 2 * Fintype.card n / Fintype.card l by ring] at h

/-! ### The $(1 + \varepsilon)$ forms -/

omit [Fintype n] [Fintype l] [DecidableEq n] in
/-- The test matrix is measurable when its sketch is. -/
private theorem aemeasurable_of_conjTranspose [Finite n] [Finite l] {X : Ω → Matrix n l ℝ}
    (hX : AEMeasurable (fun ω => (X ω)ᴴ) μ) : AEMeasurable X μ := by
  have := Fintype.ofFinite n
  have := Fintype.ofFinite l
  exact (continuous_id.matrix_conjTranspose.measurable.comp_aemeasurable hX).congr
    (ae_of_all _ fun ω => Matrix.conjTranspose_conjTranspose (X ω))

omit [DecidableEq n] in
/-- The events of the $(1 + \varepsilon)$ forms are empty without columns, or null at $k = 0$. -/
private theorem measureReal_one_add_mul_frobNorm_lt_le [IsFiniteMeasure μ] {Y : Ω → Matrix m n ℝ}
    (A B : Matrix m n ℝ) {ε δ : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ)
    (h : ∀ ω, frobNorm (A - Y ω) ≤ frobNorm (A - B)) :
    μ.real {ω | (1 + ε) * frobNorm (A - B) ^ 2 < frobNorm (A - Y ω) ^ 2} ≤ δ := by
  refine le_of_eq_of_le ((measureReal_eq_zero_iff (measure_ne_top _ _)).2 ?_) hδ
  refine measure_mono_null (fun ω hω => ?_) measure_empty
  have hω' : (1 + ε) * frobNorm (A - B) ^ 2 < frobNorm (A - Y ω) ^ 2 := hω
  have := pow_le_pow_left₀ (frobNorm_nonneg _) (h ω) 2
  nlinarith [sq_nonneg (frobNorm (A - B))]

/-- **The randomized SVD with an SRHT test matrix, relative error**: for a real bounded
orthonormal $\mathbf{F}$ with constant $\beta$, a test matrix $\mathbf{\Omega}$ whose sketch
$\mathbf{\Omega}^{\mathsf{H}}$ is the SRHT of $\mathbf{F}$ without replacement, $\ell$ nonempty,
$\ell \le n$, $\varepsilon, \delta > 0$, at
least <!-- value samplingInjectionDim k L (1/2) (\delta/4) -->
$$\ell \ge \frac{2 L \log(k/(\delta/4))}{(1/2)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/4) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/4))} +
2 \log(\lvert n \rvert/(\delta/4))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 4)` (the size is
`samplingInjectionDim k L (1 / 2) (δ / 4)`, the injection at constant $1/2$ and failure
$\delta/2$), and $\ell \ge 8(3\beta^2 - 1)k/(\varepsilon\delta)$,
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$. The route of
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_isSubgaussianVector`, with the SRHT JL moment
`NLAlib.hasJLMoment_of_hasLaw_srht` at $\sqrt{\varepsilon/(4k)}$; the name carries `_of_le_card`
to tell it apart from the constant-factor
`NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`.
Asymptotic form: `NLAlib.exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`.
[Woodruff2014, Lemma 45 and Remark 46]; there for dense sketches, constants unspecified.
Result: randomized-svd-tail -/
theorem measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht_of_le_card [Nonempty l]
    {X : Ω → Matrix n l ℝ} {F : Matrix n n ℝ} {β : ℝ} (hF : IsBoundedOrthonormal F β)
    (A : Matrix m n ℝ) (hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ)
    (hln : Fintype.card l ≤ Fintype.card n) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hl : samplingInjectionDim k (β * srhtRowBound (Fintype.card n) k (δ / 4)) (1 / 2) (δ / 4) ≤
      Fintype.card l)
    (hl' : 8 * (3 * β ^ 2 - 1) * k ≤ ε * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hln)
  have : Nonempty n := Fintype.card_pos_iff.1 (Fintype.card_pos.trans_le hln)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine measureReal_one_add_mul_frobNorm_lt_le _ _ hε.le hδ.le fun ω => ?_
    rw [truncatedSVD_zero, sub_zero, sub_rsvd]
    exact frobNorm_one_sub_rangeProjector_mul_le _ A
  have hβ := hF.one_le
  have hv : 0 < 3 * β ^ 2 - 1 := by nlinarith
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 Fintype.card_pos
  have hεJ : 0 < √(ε / (4 * k)) := Real.sqrt_pos.2 (by positivity)
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionDim_le hF hX hln k
    (ε := 1 / 2) (by norm_num) (half_pos hδ) (by rw [show δ / 2 / 2 = δ / 4 by ring]; exact hl)
  have h := (hasJLMoment_of_hasLaw_srht hF hX hεJ).measureReal_frobNorm_sub_rsvd_sq_gt_le (A := A)
    (hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    (aemeasurable_of_conjTranspose hX.aemeasurable) (by norm_num) hεJ le_rfl
    (div_nonneg hv.le (by positivity))
  have hsq : √(ε / (4 * k)) ^ 2 = ε / (4 * k) := Real.sq_sqrt (by positivity)
  refine (measureReal_mono fun ω hω => ?_).trans (h.trans ?_)
  · have hω' : (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 < frobNorm (A - rsvd A (X ω)) ^ 2 :=
      hω
    rw [Set.mem_ofPred_eq, hsq]
    refine lt_of_eq_of_lt ?_ hω'
    field_simp
    ring
  · rw [hsq]
    have e : (3 * β ^ 2 - 1) / (Fintype.card l * (ε / (4 * k))) =
        4 * (3 * β ^ 2 - 1) * k / (Fintype.card l * ε) := by
      field_simp
    have h2 : 4 * (3 * β ^ 2 - 1) * k / (Fintype.card l * ε) ≤ δ / 2 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [e]
    linarith

/-- **$O(\beta(k + \log(n/\delta))\log(k/\delta) + \beta^2 k/(\varepsilon\delta))$ SRHT columns
suffice for the randomized SVD**: there are absolute constants $C, \varepsilon_0 > 0$ such that
for a real bounded orthonormal $\mathbf{F}$ with constant $\beta$ and a test matrix
$\mathbf{\Omega}$ whose sketch $\mathbf{\Omega}^{\mathsf{H}}$ is its SRHT without replacement,
$\ell$ nonempty, $\ell \le n$, $0 < \varepsilon \le \varepsilon_0$, $0 < \delta \le 1/2$ and $\ell$
at least $C$ times that threshold,
$$\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the constants come before every dimension and before $\beta$.
Proved from `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht_of_le_card` with
$\varepsilon_0 = 1$. [Woodruff2014, Lemma 45 and Remark 46].
Asymptotic: NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht_of_le_card
Result: randomized-svd-tail -/
theorem exists_forall_measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] [Nonempty l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (F : Matrix n n ℝ) (β : ℝ) (k : ℕ) (ε δ : ℝ),
      IsBoundedOrthonormal F β → HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ →
      Fintype.card l ≤ Fintype.card n → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (β * (k + Real.log (Fintype.card n / δ)) * Real.log (k / δ) +
        β ^ 2 * (k : ℝ) / (ε * δ)) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ := by
  refine ⟨1152, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ _ μ A X F β k ε δ hF hX hln hε hε1 hδ hδ2 hk
  have : Nonempty n := Fintype.card_pos_iff.1 (Fintype.card_pos.trans_le hln)
  have hβ : 1 ≤ β := hF.one_le
  have hN : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.2 Fintype.card_pos
  have h2N : Real.log 2 ≤ Real.log (Fintype.card n / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hT2 : 0 ≤ β ^ 2 * (k : ℝ) / (ε * δ) := by positivity
  have hT1 : 0 ≤ β * (k + Real.log (Fintype.card n / δ)) * Real.log (k / δ) := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have hd1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk0
    have : 0 ≤ Real.log (k / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; nlinarith)
    have : 0 ≤ (k : ℝ) + Real.log (Fintype.card n / δ) := by linarith
    positivity
  refine measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht_of_le_card hF A hX hln hε hδ ?_ ?_
  · have h := samplingInjectionDim_srhtRowBound_le (n := n) hβ k (half_pos hδ) (by linarith)
      (1 / 2)
    rw [show δ / 2 / 2 = δ / 4 by ring] at h
    refine h.trans ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [CharP.cast_eq_zero, zero_div, Real.log_zero, mul_zero, zero_add] at hk ⊢
      linarith
    have hd1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk0
    have h2d : Real.log 2 ≤ Real.log (k / δ) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
    have e (x : ℝ) (hx : 0 < x) : Real.log (x / (δ / 2)) = Real.log 2 + Real.log (x / δ) := by
      rw [show x / (δ / 2) = 2 * (x / δ) by ring, Real.log_mul (by norm_num) (by positivity)]
    rw [e _ (by positivity), e _ (by positivity)]
    have hA : (k : ℝ) + (Real.log 2 + Real.log (Fintype.card n / δ)) ≤
        2 * (k + Real.log (Fintype.card n / δ)) := by linarith
    have hB : Real.log 2 + Real.log (k / δ) ≤ 2 * Real.log (k / δ) := by linarith
    have hAB := mul_le_mul hA hB (by linarith) (by linarith)
    have : 32 * (β * (k + (Real.log 2 + Real.log (Fintype.card n / δ))) *
        (Real.log 2 + Real.log (k / δ)) / (1 / 2) ^ 2) ≤
        1152 * (β * (k + Real.log (Fintype.card n / δ)) * Real.log (k / δ)) := by
      rw [show ∀ x : ℝ, x / (1 / 2) ^ 2 = 4 * x from fun x => by ring]
      nlinarith [mul_le_mul_of_nonneg_left hAB (by linarith : (0 : ℝ) ≤ β)]
    linarith
  · have h : 8 * (3 * β ^ 2 - 1) * k ≤ 1152 * (β ^ 2 * (k : ℝ) / (ε * δ)) * (ε * δ) := by
      rw [mul_assoc 1152, div_mul_cancel₀ _ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hk' : 1152 * (β ^ 2 * (k : ℝ) / (ε * δ)) ≤ Fintype.card l := by nlinarith
    calc 8 * (3 * β ^ 2 - 1) * k ≤ 1152 * (β ^ 2 * (k : ℝ) / (ε * δ)) * (ε * δ) := h
      _ ≤ Fintype.card l * (ε * δ) := mul_le_mul_of_nonneg_right hk' (by positivity)
      _ = ε * δ * Fintype.card l := by ring

/-- **Early-truncated randomized SVD with an SRHT test matrix, tail**: for a real bounded
orthonormal $\mathbf{F}$ with constant $\beta$, a test matrix $\mathbf{\Omega}$ whose sketch
$\mathbf{\Omega}^{\mathsf{H}}$ is the SRHT of $\mathbf{F}$ without replacement, $\ell$ nonempty,
$\ell \le n$, $0 < \varepsilon \le 1$, $\delta > 0$, at
least <!-- value samplingInjectionDim k L (\varepsilon/6) (\delta/6) -->
$$\ell \ge \frac{2 L \log(k/(\delta/6))}{(\varepsilon/6)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/6) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/6))} +
2 \log(\lvert n \rvert/(\delta/6))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 6)` (the size is
`samplingInjectionDim k L (ε / 6) (δ / 6)`, the injection at constant $1 - \varepsilon/6$ and
failure $\delta/3$), and $\ell \ge 108(3\beta^2 - 1)k/(\varepsilon^2\delta)$,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$. The route of
`NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_gaussianMatrix`, with the
SRHT JL moment `NLAlib.hasJLMoment_of_hasLaw_srht` at $\varepsilon/(6\sqrt{k})$ for the two
multiplication tails. Asymptotic form:
`NLAlib.exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht`.
[CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3]; there for dense random sign matrices,
with unspecified constants.
Result: etrsvd -/
theorem measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht [Nonempty l]
    {X : Ω → Matrix n l ℝ} {F : Matrix n n ℝ} {β : ℝ} (hF : IsBoundedOrthonormal F β)
    (A : Matrix m n ℝ) (hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ)
    (hln : Fintype.card l ≤ Fintype.card n) {k : ℕ} {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ)
    (hl : samplingInjectionDim k (β * srhtRowBound (Fintype.card n) k (δ / 6)) (ε / 6) (δ / 6) ≤
      Fintype.card l)
    (hl' : 108 * (3 * β ^ 2 - 1) * k ≤ ε ^ 2 * δ * Fintype.card l) :
    μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hln)
  have : Nonempty n := Fintype.card_pos_iff.1 (Fintype.card_pos.trans_le hln)
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine measureReal_one_add_mul_frobNorm_lt_le _ _ hε.le hδ.le fun ω => ?_
    rw [sub_earlyTruncatedRSVD, truncatedSVD_zero, truncatedSVD_zero, rangeProjector_zero,
      sub_zero, sub_zero, Matrix.one_mul]
  have hβ := hF.one_le
  have hv : 0 < 3 * β ^ 2 - 1 := by nlinarith
  have hL : (0 : ℝ) < Fintype.card l := Nat.cast_pos.2 Fintype.card_pos
  have hXm := aemeasurable_of_conjTranspose hX.aemeasurable
  have hk0 : (0 : ℝ) < √(k : ℝ) := Real.sqrt_pos.2 (Nat.cast_pos.2 hk)
  have hεJ : 0 < ε / (6 * √(k : ℝ)) := by positivity
  have hOSI := isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionDim_le hF hX hln k
    (ε := ε / 6) (by positivity) (by positivity : (0 : ℝ) < δ / 3)
    (by rw [show δ / 3 / 2 = δ / 6 by ring]; exact hl)
  have hJL := hasJLMoment_of_hasLaw_srht hF hX hεJ
  have h1 : (fun ω => ((1 : ℝ) • X ω)ᴴ) = fun ω => (X ω)ᴴ := by simp only [one_smul]
  rw [← h1] at hOSI hJL
  refine (hJL.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_one_add_mul_le
    (hOSI.hasSubspaceInjection (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k))
    ((continuous_const_smul _).measurable.comp_aemeasurable hXm)
    hε hε1 le_rfl (div_nonneg hv.le (by positivity))).trans ?_
  have e : (3 * β ^ 2 - 1) / (Fintype.card l * (ε / (6 * √(k : ℝ))) ^ 2) =
      36 * (3 * β ^ 2 - 1) * k / (Fintype.card l * ε ^ 2) := by
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg k)]
    field_simp
    ring
  have h3 : 36 * (3 * β ^ 2 - 1) * k / (Fintype.card l * ε ^ 2) ≤ δ / 3 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  rw [e]
  linarith

/-- **$O(\beta(k + \log(n/\delta))\log(k/\delta)/\varepsilon^2 + \beta^2k/(\varepsilon^2\delta))$
SRHT columns suffice for early truncation**: there are absolute constants
$C, \varepsilon_0 > 0$ such that for a real bounded orthonormal $\mathbf{F}$ with constant $\beta$
and a test matrix $\mathbf{\Omega}$ whose sketch $\mathbf{\Omega}^{\mathsf{H}}$ is its SRHT
without replacement, $\ell$ nonempty, $\ell \le n$, $0 < \varepsilon \le \varepsilon_0$,
$0 < \delta \le 1/2$ and $\ell$ at least $C$ times that threshold,
$$\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
(1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$; the constants come before every dimension and before $\beta$.
Proved from `NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht` with
$\varepsilon_0 = 1$. [CohenElderMuscoMuscoPersu2015, Theorem 12 and Lemma 3].
Asymptotic: NLAlib.measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht
Result: etrsvd -/
theorem exists_forall_measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
      [Fintype l] [DecidableEq n] [Nonempty l] (μ : Measure Ω) (A : Matrix m n ℝ)
      (X : Ω → Matrix n l ℝ) (F : Matrix n n ℝ) (β : ℝ) (k : ℕ) (ε δ : ℝ),
      IsBoundedOrthonormal F β → HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ →
      Fintype.card l ≤ Fintype.card n → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (β * (k + Real.log (Fintype.card n / δ)) * Real.log (k / δ) / ε ^ 2 +
        β ^ 2 * (k : ℝ) / (ε ^ 2 * δ)) ≤ Fintype.card l →
      μ.real {ω | (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 <
        frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ := by
  refine ⟨10368, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n l _ _ _ _ _ _ μ A X F β k ε δ hF hX hln hε hε1 hδ hδ2 hk
  have : Nonempty n := Fintype.card_pos_iff.1 (Fintype.card_pos.trans_le hln)
  have hβ : 1 ≤ β := hF.one_le
  have hN : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.2 Fintype.card_pos
  have h2N : Real.log 2 ≤ Real.log (Fintype.card n / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl3 : Real.log 3 ≤ 2 * Real.log 2 := by
    rw [← Real.log_rpow (by norm_num)]
    exact Real.log_le_log (by norm_num) (by norm_num)
  have hl30 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  have hT2 : 0 ≤ β ^ 2 * (k : ℝ) / (ε ^ 2 * δ) := by positivity
  have hT1 : 0 ≤ β * (k + Real.log (Fintype.card n / δ)) * Real.log (k / δ) / ε ^ 2 := by
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp
    have hd1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk0
    have : 0 ≤ Real.log (k / δ) := Real.log_nonneg (by rw [le_div_iff₀ hδ]; nlinarith)
    have : 0 ≤ (k : ℝ) + Real.log (Fintype.card n / δ) := by linarith
    positivity
  refine measureReal_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le_of_hasLaw_srht hF A hX hln hε hε1 hδ
    ?_ ?_
  · have h := samplingInjectionDim_srhtRowBound_le (n := n) hβ k (by positivity : 0 < δ / 3)
      (by linarith) (ε / 6)
    rw [show δ / 3 / 2 = δ / 6 by ring] at h
    refine h.trans ?_
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp only [CharP.cast_eq_zero, zero_div, Real.log_zero, mul_zero, zero_add] at hk ⊢
      linarith
    have hd1 : (1 : ℝ) ≤ k := Nat.one_le_cast.2 hk0
    have h2d : Real.log 2 ≤ Real.log (k / δ) :=
      Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
    have e (x : ℝ) (hx : 0 < x) : Real.log (x / (δ / 3)) = Real.log 3 + Real.log (x / δ) := by
      rw [show x / (δ / 3) = 3 * (x / δ) by ring, Real.log_mul (by norm_num) (by positivity)]
    rw [e _ (by positivity), e _ (by positivity)]
    have hA : (k : ℝ) + (Real.log 3 + Real.log (Fintype.card n / δ)) ≤
        3 * (k + Real.log (Fintype.card n / δ)) := by linarith
    have hB : Real.log 3 + Real.log (k / δ) ≤ 3 * Real.log (k / δ) := by linarith
    have hAB := mul_le_mul hA hB (by linarith) (by linarith)
    have : 32 * (β * (k + (Real.log 3 + Real.log (Fintype.card n / δ))) *
        (Real.log 3 + Real.log (k / δ)) / (ε / 6) ^ 2) ≤
        10368 * (β * (k + Real.log (Fintype.card n / δ)) * Real.log (k / δ) / ε ^ 2) := by
      rw [div_pow, div_div_eq_mul_div, mul_div_assoc', mul_div_assoc']
      refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
      nlinarith [mul_le_mul_of_nonneg_left hAB (by linarith : (0 : ℝ) ≤ β)]
    linarith
  · have hε2 : 0 < ε ^ 2 := by positivity
    have h : 108 * (3 * β ^ 2 - 1) * k ≤
        10368 * (β ^ 2 * (k : ℝ) / (ε ^ 2 * δ)) * (ε ^ 2 * δ) := by
      rw [mul_assoc 10368, div_mul_cancel₀ _ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    have hk' : 10368 * (β ^ 2 * (k : ℝ) / (ε ^ 2 * δ)) ≤ Fintype.card l := by nlinarith
    calc 108 * (3 * β ^ 2 - 1) * k ≤ 10368 * (β ^ 2 * (k : ℝ) / (ε ^ 2 * δ)) * (ε ^ 2 * δ) := h
      _ ≤ Fintype.card l * (ε ^ 2 * δ) := mul_le_mul_of_nonneg_right hk' (by positivity)
      _ = ε ^ 2 * δ * Fintype.card l := by ring

end NLAlib
