/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Oblivious.RangeFinder
public import NLAlib.Sketching.Structured.SRHT

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
there $\|\mathbf{\Omega}\|_2 = \sqrt{n/\ell}$ almost surely (`NLAlib.ae_specNorm_eq_of_hasLaw_srht`;
with replacement, repeated rows break it). Both use the family's injection at constant $1/2$. Any
`RCLike` field.

There is no approximate-multiplication route and so no $(1 + \varepsilon)$ form: the SRHT has no
approximate-multiplication tail in the library yet (`docs/design/LowRank-S7.md` §0.2, D6). The
constant-factor statements have no accuracy parameter and no asymptotic form; in $O(\cdot)$ form
their size is the family's injection size,
`NLAlib.exists_forall_isObliviousSubspaceInjection_of_hasLaw_srht` and its with-replacement twin.

**Statements with no per-family form.** Nyström, generalized Nyström and the truncations apply
through the family's OSI:
```
isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le hF hX hln k hε hδ hl
isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionSize_le hF hX k
  hε hδ hl
```
with `hX : HasLaw (fun ω => (X ω)ᴴ) (srht l F) μ` (respectively `srhtWithReplacement`). Design:
`docs/design/LowRank-S7.md` §3.5, §8.

## Main results

* `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srht`,
  `NLAlib.measureReal_frobNorm_sub_rsvd_sq_gt_le_of_hasLaw_srhtWithReplacement`: the injection
  route.
* `SymmetricGauge.measureReal_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_hasLaw_srht`:
  the bounded-sketch route, HMT's SRFT theorem.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {m n l : Type*} [Fintype m] [Fintype n] [Fintype l] [DecidableEq n] {X : Ω → Matrix n l 𝕜}

/-- **The randomized SVD with an SRHT test matrix**: if the sketch $\mathbf{\Omega}^{\mathsf{H}}$
is the SRHT without replacement of a bounded orthonormal $\mathbf{F}$ with bound $\beta$,
$\ell \le n$, $\delta, t > 0$ and $\ell$ is at
least <!-- value samplingInjectionSize k L (1/2) (\delta/2) -->
$$\frac{2 L \log(k/(\delta/2))}{(1/2)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/2) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 2)` and the size is
`samplingInjectionSize k L (1 / 2) (δ / 2)`, then
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
    (hl : samplingInjectionSize k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hln)
  have h := (isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le hF hX hln k
    (by norm_num) hδ hl).measure_frobNorm_sub_rsvd_sq_gt_le (A := A) (by norm_num) ht
  rwa [show (1 : ℝ) + t / (1 - 1 / 2) = 1 + 2 * t by ring] at h

/-- **The randomized SVD with an SRHT test matrix, with replacement**: if the sketch
$\mathbf{\Omega}^{\mathsf{H}}$ is the SRHT with i.i.d. uniform row indices of a bounded
orthonormal $\mathbf{F}$ with bound $\beta$, $\delta, t > 0$ and $\ell$ is at
least <!-- value samplingInjectionSize k L (1/2) (\delta/2) -->
$$\frac{2 L \log(k/(\delta/2))}{(1/2)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/2) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 2)` and the size is
`samplingInjectionSize k L (1 / 2) (δ / 2)`, then
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
    (hl : samplingInjectionSize k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * t) * frobNorm (A - truncatedSVD A k) ^ 2 <
      frobNorm (A - rsvd A (X ω)) ^ 2} ≤ δ + 1 / t := by
  have : IsProbabilityMeasure μ :=
    hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srhtWithReplacement F)
  have h := (isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionSize_le
    hF hX k (by norm_num) hδ hl).measure_frobNorm_sub_rsvd_sq_gt_le (A := A) (by norm_num) ht
  rwa [show (1 : ℝ) + t / (1 - 1 / 2) = 1 + 2 * t by ring] at h

/-- **The randomized SVD with an SRHT test matrix, bounded-sketch form** (HMT's SRFT theorem): if
the sketch $\mathbf{\Omega}^{\mathsf{H}}$ is the SRHT without replacement of a bounded
orthonormal $\mathbf{F}$ with bound $\beta$, $\ell \le n$, $\delta > 0$ and $\ell$ is at
least <!-- value samplingInjectionSize k L (1/2) (\delta/2) -->
$$\frac{2 L \log(k/(\delta/2))}{(1/2)^2}\,,$$
where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} k (\delta/2) -->
$$L = \beta\,\bigl(k + 2\sqrt{k \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `srhtRowBound (Fintype.card n) k (δ / 2)` and the size is
`samplingInjectionSize k L (1 / 2) (δ / 2)`, then for every unitarily invariant norm
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
    (hl : samplingInjectionSize k (β * srhtRowBound (Fintype.card n) k (δ / 2)) (1 / 2) (δ / 2) ≤
      Fintype.card l) :
    μ.real {ω | (1 + 2 * Fintype.card n / Fintype.card l) *
        Φ.matrixNorm ((A - truncatedSVD A k)ᴴ * (A - truncatedSVD A k)) <
      Φ.matrixNorm ((A - rsvd A (X ω))ᴴ * (A - rsvd A (X ω)))} ≤ δ := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hln)
  have hinj := (isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le hF hX hln k
    (by norm_num) hδ hl).hasSubspaceInjection (U := (truncatedSVD A k)ᴴ)
    (by rw [Matrix.rank_conjTranspose]; exact rank_truncatedSVD_le A k)
  have hL : ∀ᵐ ω ∂μ, specNorm (X ω) ≤ √(Fintype.card n / Fintype.card l : ℝ) := by
    filter_upwards [ae_specNorm_eq_of_hasLaw_srht hF.hasOrthonormalCols hX] with ω hω
    rw [← specNorm_conjTranspose, hω]
  have h := hinj.measure_matrixNorm_conjTranspose_mul_self_sub_rsvd_gt_le_of_specNorm_le
    (by norm_num) hL Φ
  rwa [Real.sq_sqrt (by positivity),
    show (1 : ℝ) + Fintype.card n / Fintype.card l / (1 - 1 / 2) =
      1 + 2 * Fintype.card n / Fintype.card l by ring] at h

end NLAlib
