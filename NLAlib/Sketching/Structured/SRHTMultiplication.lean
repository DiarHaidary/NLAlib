/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.ProjectionCost
public import NLAlib.Sketching.Sampling.MatrixMultiplication
public import NLAlib.Sketching.Structured.SRHT

/-!
# The SRHT as a Johnson–Lindenstrauss and multiplication sketch

The subsampled randomized trigonometric transform of `NLAlib.Sketching.Structured.SRHT`, for a
bounded orthonormal $\mathbf{F}$ with constant $\beta$, in both sampling models.

* **Distributional JL.** An oblivious subspace embedding for dimension $1$ with constants strictly
  inside $1 \mp \varepsilon$ has the JL property
  (`NLAlib.IsObliviousSubspaceEmbedding.hasJLProperty`), so the SRHT OSE at $d = 1$, by
  continuity in the distortion, gives the JL tail
  $$2\exp\Bigl(-\frac{\varepsilon^2\lvert k\rvert}{3\beta(1 + 2\sqrt{t} + 2t)}\Bigr)
  + \lvert n\rvert e^{-t}$$
  and its size form at $O(\beta\log(\lvert n\rvert/\delta)\log(1/\delta)/\varepsilon^2)$ rows;
  any field. The JL lemma for $N$ points follows by
  `NLAlib.HasJLProperty.measureReal_exists_abs_norm_mulVec_sq_sub_ge_le`.
* **The JL moment at $p = 2$**, directly: with $\mathbf{z} = \mathbf{F}\mathbf{D}\mathbf{x}$ the
  squared sketch norm is the mean of $\lvert k\rvert$ draws of $\lvert n\rvert\lvert z_i\rvert^2$,
  whose variance without replacement is at most the one with replacement, and the fourth moment
  of a Rademacher sum bounds $\mathbb{E}\lvert z_i\rvert^4$ by $3\beta^2/\lvert n\rvert^2$, so
  $\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - 1)^2 \le (3\beta^2 - 1)/\lvert k\rvert$, with no
  $\log\lvert n\rvert$. The JL moment does not follow usefully from the tail, whose flattening
  floor $\lvert n\rvert e^{-t}$ costs a $\log^2(1/\delta)$. Real $\mathbf{F}$.
* **Projection-cost preservation** through
  `NLAlib.IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment`, at the size
  of the SRHT OSE plus <!-- value projectionCostTailDim {(3\beta^2 - 1)} d \varepsilon \delta -->
  $384 \cdot (3\beta^2 - 1) (d + 1)/(\varepsilon^2 \delta)$ rows; real.
* **Spectral approximate multiplication**: condition on the signs, flatten the rows of
  $\mathbf{F}\mathbf{D}\mathbf{A}$ and $\mathbf{F}\mathbf{D}\mathbf{B}$
  (`NLAlib.measureReal_exists_norm_mul_diagonal_mul_apply_sq_gt_le_of_hasLaw_rademacherVector`),
  then sample (`NLAlib.Sketching.Sampling.MatrixMultiplication`); any field.

The relative-error sketch-and-solve, randomized SVD and early truncation through the JL moment
are in `NLAlib.Regression.SRHT` and `NLAlib.LowRank.Oblivious.SRHT`. Design:
`docs/design/Sketching-Moments.md` §3, §5.4.

## Main results

* `NLAlib.hasJLProperty_of_hasLaw_srht`,
  `NLAlib.hasJLProperty_of_hasLaw_srht_of_samplingEmbeddingDim_le`,
  `NLAlib.exists_forall_hasJLProperty_of_hasLaw_srht` and their with-replacement forms.
* `NLAlib.hasJLMoment_of_hasLaw_srht`, `NLAlib.hasJLMoment_of_hasLaw_srhtWithReplacement`.
* `NLAlib.hasProjectionCostPreserving_of_hasLaw_srht_of_le_card` and its asymptotic form
  `NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_srht`.
* `NLAlib.measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_srht` and its
  with-replacement form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n : Type*} [Fintype k] [Fintype n] [DecidableEq n] {β ε t δ : ℝ}

/-! ### Distributional JL -/

section JL

variable {S : Ω → Matrix k n 𝕜} {F : Matrix n n 𝕜}

/-- **Distributional JL for the SRHT**: for a bounded orthonormal $\mathbf{F}$ with constant
$\beta$, the SRHT $\mathbf{S}$ built from it (independent random signs and an independent uniform
choice of $\lvert k\rvert$ distinct rows), $0 \le \varepsilon \le 1$ and $t \ge 0$, $\mathbf{S}$
has the JL property with distortion $\varepsilon$ and failure probability
$$2\exp\Bigl(-\frac{\varepsilon^2\lvert k\rvert}{3\beta(1 + 2\sqrt{t} + 2t)}\Bigr)
+ \lvert n\rvert e^{-t}\,,$$
the OSE bound of `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` at $d = 1$, through
`NLAlib.IsObliviousSubspaceEmbedding.hasJLProperty` at every $\varepsilon' < \varepsilon$ and
continuity of the bound. [Woodruff2014, Theorem 7] and [Tropp2011a, Theorems 1.3 and 3.1] for the
SRHT as an embedding; the fast JL transform of Ailon and Chazelle (not in hand). Any field.
Result: jl-srht -/
theorem hasJLProperty_of_hasLaw_srht (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    HasJLProperty S ε
      (2 * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (1 + 2 * √t + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  sorry

/-- **Distributional JL for the SRHT, sample-size form**: for $0 < \varepsilon \le 1$,
$\delta > 0$ and at least <!-- value samplingEmbeddingDim {\cdot 1} L \varepsilon (\delta/2) -->
$$\lvert k \rvert \ge \frac{3 L \log(2\cdot 1/(\delta/2))}{\varepsilon^2}$$
rows (`NLAlib.samplingEmbeddingDim 1 L ε (δ/2)`), where the flattened
coherence <!-- value srhtRowBound {\lvert n \rvert} 1 (\delta/2) -->
$$L = \beta\,\bigl(1 + 2\sqrt{1 \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `NLAlib.srhtRowBound (Fintype.card n) 1 (δ / 2)`, the SRHT has the JL property
with distortion $\varepsilon$ and failure probability $\delta$: the OSE size at $d = 1$.
[Woodruff2014, Theorem 7]; [Tropp2011a, Theorem 3.1]. Asymptotic form:
`NLAlib.exists_forall_hasJLProperty_of_hasLaw_srht`.
Result: jl-srht -/
theorem hasJLProperty_of_hasLaw_srht_of_samplingEmbeddingDim_le (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingEmbeddingDim 1 (β * srhtRowBound (Fintype.card n) 1 (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    HasJLProperty S ε δ μ := by
  sorry

/-- **Distributional JL for the SRHT, asymptotic form**:
$O(\beta(1 + \log(\lvert n\rvert/\delta))\log(1/\delta)/\varepsilon^2)$ rows suffice for the SRHT
of a bounded orthonormal $\mathbf{F}$ with constant $\beta$ to have the JL property with distortion
$\varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below absolute
constants; the constants come before every dimension and before $\beta$, and the
$\log\lvert n\rvert$ of the flattening stays in the threshold. Proved from
`NLAlib.hasJLProperty_of_hasLaw_srht_of_samplingEmbeddingDim_le` with $\varepsilon_0 = 1$ and
$\delta \le 1/2$. [Woodruff2014, Theorem 7].
Asymptotic: NLAlib.hasJLProperty_of_hasLaw_srht_of_samplingEmbeddingDim_le
Result: jl-srht -/
theorem exists_forall_hasJLProperty_of_hasLaw_srht :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k]
      [Fintype n] [DecidableEq n] (μ : Measure Ω) (S : Ω → Matrix k n 𝕜) (F : Matrix n n 𝕜)
      (β ε δ : ℝ),
      IsBoundedOrthonormal F β → HasLaw S (srht k F) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (β * (1 + Real.log (Fintype.card n / δ)) * Real.log (1 / δ) / ε ^ 2) ≤
        Fintype.card k →
      HasJLProperty S ε δ μ := by
  sorry

/-- **Distributional JL for the SRHT with replacement**: for a bounded orthonormal $\mathbf{F}$
with constant $\beta$, the SRHT $\mathbf{S}$ built from it with $\lvert k\rvert$ i.i.d. uniform
row indices, $0 \le \varepsilon \le 1$ and $t \ge 0$, $\mathbf{S}$ has the JL property with
distortion $\varepsilon$ and failure probability
$$2\exp\Bigl(-\frac{\varepsilon^2\lvert k\rvert}{3\beta(1 + 2\sqrt{t} + 2t)}\Bigr)
+ \lvert n\rvert e^{-t}\,,$$
the OSE bound of `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement` at $d = 1$.
[MartinssonTropp2020, §9.3]. Any field.
Result: jl-srht -/
theorem hasJLProperty_of_hasLaw_srhtWithReplacement (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srhtWithReplacement k F) μ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    HasJLProperty S ε
      (2 * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (1 + 2 * √t + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  sorry

/-- **Distributional JL for the SRHT with replacement, sample-size form**: for
$0 < \varepsilon \le 1$, $\delta > 0$ and at
least <!-- value samplingEmbeddingDim {\cdot 1} L \varepsilon (\delta/2) -->
$$\lvert k \rvert \ge \frac{3 L \log(2\cdot 1/(\delta/2))}{\varepsilon^2}$$
rows (`NLAlib.samplingEmbeddingDim 1 L ε (δ/2)`), where the flattened
coherence <!-- value srhtRowBound {\lvert n \rvert} 1 (\delta/2) -->
$$L = \beta\,\bigl(1 + 2\sqrt{1 \log(\lvert n \rvert/(\delta/2))} +
2 \log(\lvert n \rvert/(\delta/2))\bigr)$$
is $\beta$ times `NLAlib.srhtRowBound (Fintype.card n) 1 (δ / 2)`, the SRHT with i.i.d. uniform
row indices has the JL property with distortion $\varepsilon$ and failure probability $\delta$.
[MartinssonTropp2020, §9.3]. Asymptotic form:
`NLAlib.exists_forall_hasJLProperty_of_hasLaw_srhtWithReplacement`.
Result: jl-srht -/
theorem hasJLProperty_of_hasLaw_srhtWithReplacement_of_samplingEmbeddingDim_le
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingEmbeddingDim 1 (β * srhtRowBound (Fintype.card n) 1 (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    HasJLProperty S ε δ μ := by
  sorry

/-- **Distributional JL for the SRHT with replacement, asymptotic form**:
$O(\beta(1 + \log(\lvert n\rvert/\delta))\log(1/\delta)/\varepsilon^2)$ rows suffice for the SRHT
with i.i.d. uniform row indices of a bounded orthonormal $\mathbf{F}$ with constant $\beta$ to
have the JL property with distortion $\varepsilon$ and failure probability $\delta$, for
$\varepsilon$ and $\delta$ below absolute constants; the constants come before every dimension and
before $\beta$. Proved from
`NLAlib.hasJLProperty_of_hasLaw_srhtWithReplacement_of_samplingEmbeddingDim_le` with
$\varepsilon_0 = 1$ and $\delta \le 1/2$. [MartinssonTropp2020, §9.3].
Asymptotic: NLAlib.hasJLProperty_of_hasLaw_srhtWithReplacement_of_samplingEmbeddingDim_le
Result: jl-srht -/
theorem exists_forall_hasJLProperty_of_hasLaw_srhtWithReplacement :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype k]
      [Fintype n] [DecidableEq n] (μ : Measure Ω) (S : Ω → Matrix k n 𝕜) (F : Matrix n n 𝕜)
      (β ε δ : ℝ),
      IsBoundedOrthonormal F β → HasLaw S (srhtWithReplacement k F) μ →
      0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (β * (1 + Real.log (Fintype.card n / δ)) * Real.log (1 / δ) / ε ^ 2) ≤
        Fintype.card k →
      HasJLProperty S ε δ μ := by
  sorry

end JL

/-! ### The JL moment at $p = 2$ and projection-cost preservation -/

section Moment

variable {S : Ω → Matrix k n ℝ} {F : Matrix n n ℝ}

/-- **The JL moment of the SRHT** at $p = 2$: for a real bounded orthonormal $\mathbf{F}$ with
constant $\beta$, the SRHT $\mathbf{S}$ built from it (independent random signs and an independent
uniform choice of $\lvert k\rvert$ distinct rows), $k$ nonempty and $\varepsilon > 0$, the JL
moment property holds with exponent $2$ and failure probability
$$\delta = \frac{3\beta^2 - 1}{\lvert k\rvert\varepsilon^2}\,;$$
the Gaussian sketch's $2/(\lvert k\rvert\varepsilon^2)$ at $\beta = 1$ (Walsh–Hadamard). No
$\log\lvert n\rvert$: the flattening is not used. [Woodruff2014, Definition 12] for the property;
the bound is this proof's (no printed source in hand). -/
theorem hasJLMoment_of_hasLaw_srht [Nonempty k] (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hε : 0 < ε) :
    HasJLMoment S ε ((3 * β ^ 2 - 1) / (Fintype.card k * ε ^ 2)) 2 μ := by
  sorry

/-- **The JL moment of the SRHT with replacement** at $p = 2$: for a real bounded orthonormal
$\mathbf{F}$ with constant $\beta$, the SRHT $\mathbf{S}$ built from it with $\lvert k\rvert$
i.i.d. uniform row indices, $k$ and $n$ nonempty and $\varepsilon > 0$, the JL moment property
holds with exponent $2$ and failure probability
$$\delta = \frac{3\beta^2 - 1}{\lvert k\rvert\varepsilon^2}\,,$$
the bound without replacement (`NLAlib.hasJLMoment_of_hasLaw_srht`), here with equality in the
variance step. [Woodruff2014, Definition 12] for the property; the bound is this proof's. -/
theorem hasJLMoment_of_hasLaw_srhtWithReplacement [Nonempty k] [Nonempty n]
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (hε : 0 < ε) :
    HasJLMoment S ε ((3 * β ^ 2 - 1) / (Fintype.card k * ε ^ 2)) 2 μ := by
  sorry

/-- **The SRHT is a projection-cost-preserving sketch**, size form: for a real bounded orthonormal
$\mathbf{F}$ with constant $\beta$, the SRHT $\mathbf{S}$ built from it (independent random signs
and an independent uniform choice of $\lvert k\rvert$ distinct rows), $0 < \varepsilon \le 2$,
$\delta > 0$, at least <!-- value samplingEmbeddingDim d L (\varepsilon/2) (\delta/4) -->
$$\lvert k\rvert \ge \frac{3L\log(2d/(\delta/4))}{(\varepsilon/2)^2}$$
rows, where the flattened coherence <!-- value srhtRowBound {\lvert n \rvert} d (\delta/4) -->
$$L = \beta\,\bigl(d + 2\sqrt{d \log(\lvert n \rvert/(\delta/4))} +
2 \log(\lvert n \rvert/(\delta/4))\bigr)$$
is $\beta$ times `NLAlib.srhtRowBound (Fintype.card n) d (δ / 4)` (the size is
`NLAlib.samplingEmbeddingDim d L (ε / 2) (δ / 4)`, the OSE at $(\varepsilon/2, \delta/2)$), and at
least <!-- value projectionCostTailDim {(3\beta^2 - 1)} d \varepsilon \delta -->
$384 \cdot (3\beta^2 - 1) (d + 1)/(\varepsilon^2 \delta)$ rows
(`projectionCostTailDim (3 * β ^ 2 - 1) d ε δ`), $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ is a rank-$d$
projection-cost-preserving sketch of $\mathbf{A}$ with constants $1 \mp \varepsilon$, for every
$\mathbf{A}$, except with probability $\delta$. The tail is the JL moment
`NLAlib.hasJLMoment_of_hasLaw_srht` at $\varepsilon/(8\sqrt{d+1})$. [CohenElderMuscoMuscoPersu2015,
proof of Theorem 12]; there the SRHT at dimension $O(k)$ through stable-rank spectral approximate
multiplication; here the JL moment at $p = 2$, so $1/\delta$ in the second size. Asymptotic form:
`NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_srht`.
Result: srht-pcp -/
theorem hasProjectionCostPreserving_of_hasLaw_srht_of_le_card (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) {m : Type*} [Fintype m] (A : Matrix m n ℝ) (d : ℕ)
    (hε : 0 < ε) (hε2 : ε ≤ 2) (hδ : 0 < δ)
    (hk₁ : samplingEmbeddingDim d (β * srhtRowBound (Fintype.card n) d (δ / 4)) (ε / 2) (δ / 4) ≤
      Fintype.card k)
    (hk₂ : projectionCostTailDim (3 * β ^ 2 - 1) d ε δ ≤ Fintype.card k) :
    HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ := by
  sorry

/-- **$O(\beta(d + \log(\lvert n\rvert/\delta))\log(d/\delta)/\varepsilon^2 +
\beta^2(d+1)/(\varepsilon^2\delta))$ SRHT rows suffice for a rank-$d$ projection-cost-preserving
sketch**: for a real bounded orthonormal $\mathbf{F}$ with constant $\beta$ and its SRHT
$\mathbf{S}$, $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ is a rank-$d$ projection-cost-preserving sketch
of $\mathbf{A}$ with constants $1 \mp \varepsilon$ and failure probability $\delta$, for
$\varepsilon$ and $\delta$ below absolute constants; the constants come before every dimension
and before $\beta$. Proved from `NLAlib.hasProjectionCostPreserving_of_hasLaw_srht_of_le_card`
with $\varepsilon_0 = 1$ and $\delta \le 1/2$. [CohenElderMuscoMuscoPersu2015, proof of
Theorem 12].
Asymptotic: NLAlib.hasProjectionCostPreserving_of_hasLaw_srht_of_le_card
Result: srht-pcp -/
theorem exists_forall_hasProjectionCostPreserving_of_hasLaw_srht :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m]
      [Fintype n] [DecidableEq n] (μ : Measure Ω) (S : Ω → Matrix k n ℝ) (F : Matrix n n ℝ)
      (β : ℝ) (A : Matrix m n ℝ) (d : ℕ) (ε δ : ℝ),
      IsBoundedOrthonormal F β → HasLaw S (srht k F) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (β * (d + Real.log (Fintype.card n / δ)) * Real.log (d / δ) / ε ^ 2 +
        β ^ 2 * ((d : ℝ) + 1) / (ε ^ 2 * δ)) ≤ Fintype.card k →
      HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ := by
  sorry

end Moment

/-! ### Spectral approximate multiplication -/

section Spectral

variable {q r : Type*} [Fintype q] [Fintype r] {S : Ω → Matrix k n 𝕜} {F : Matrix n n 𝕜}

/-- **Approximate matrix multiplication in the spectral norm by the SRHT**: for a bounded
orthonormal $\mathbf{F}$ with constant $\beta$, the SRHT $\mathbf{S}$ built from it (independent
random signs and an independent uniform choice of $\lvert k\rvert$ distinct rows), $r$ nonempty,
$\mathbf{A} \in \Bbbk^{n \times q}$, $\mathbf{B} \in \Bbbk^{n \times r}$ and $s, t \ge 0$,
$$\mathbb{P}\bigl[t \le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B}
- \mathbf{A}^{\mathsf{H}}\mathbf{B}\|_2\bigr] \le (\lvert q\rvert + \lvert r\rvert)
\exp\Bigl(-\frac{\lvert k\rvert t^2/2}{\max(\beta R_{\mathbf{B}}\|\mathbf{A}\|_2^2,
\beta R_{\mathbf{A}}\|\mathbf{B}\|_2^2) + 2\beta\sqrt{R_{\mathbf{A}}R_{\mathbf{B}}}\,t/3}\Bigr)
+ 2\lvert n\rvert e^{-s}\,,$$
with the flattened row-norm bounds <!-- value srhtRowNormBound \mathbf{A} s -->
$$R_{\mathbf{A}} = \|\mathbf{A}\|_{\mathsf{F}}^2
+ 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{s} + 2\|\mathbf{A}\|_2^2 s$$
(`NLAlib.srhtRowNormBound A s`) and $R_{\mathbf{B}}$ likewise
(<!-- mention srhtRowNormBound -->`srhtRowNormBound B s`): condition on the signs, flatten both
factors, then sample without replacement
(`measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketchWithoutReplacement`).
For $\mathbf{A} = \mathbf{B}$ with $\|\mathbf{A}\|_2 = 1$ and stable rank $r_s$ this is
$\lvert k\rvert = O(\beta(r_s + \log(n/\delta))\log((q + r)/\delta)/\varepsilon^2)$.
[Tropp2011a, Lemma 3.3] for flattening; the bound is this proof's (no printed source in hand).
Any field.
Result: amm-srht-spectral -/
theorem measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_srht [Nonempty r]
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ) (A : Matrix n q 𝕜)
    (B : Matrix n r 𝕜) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) /
        (max (β * srhtRowNormBound B s * specNorm A ^ 2)
            (β * srhtRowNormBound A s * specNorm B ^ 2) +
          2 * β * √(srhtRowNormBound A s * srhtRowNormBound B s) * t / 3)) +
      2 * Fintype.card n * Real.exp (-s) := by
  sorry

/-- **Approximate matrix multiplication in the spectral norm by the SRHT with replacement**: for a
bounded orthonormal $\mathbf{F}$ with constant $\beta$, the SRHT $\mathbf{S}$ built from it with
$\lvert k\rvert$ i.i.d. uniform row indices, $k$ and $r$ nonempty,
$\mathbf{A} \in \Bbbk^{n \times q}$, $\mathbf{B} \in \Bbbk^{n \times r}$ and $s, t \ge 0$,
$$\mathbb{P}\bigl[t \le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B}
- \mathbf{A}^{\mathsf{H}}\mathbf{B}\|_2\bigr] \le (\lvert q\rvert + \lvert r\rvert)
\exp\Bigl(-\frac{\lvert k\rvert t^2/2}{\max(\beta R_{\mathbf{B}}\|\mathbf{A}\|_2^2,
\beta R_{\mathbf{A}}\|\mathbf{B}\|_2^2) + 2\beta\sqrt{R_{\mathbf{A}}R_{\mathbf{B}}}\,t/3}\Bigr)
+ 2\lvert n\rvert e^{-s}\,,$$
with the flattened row-norm bounds <!-- value srhtRowNormBound \mathbf{A} s -->
$$R_{\mathbf{A}} = \|\mathbf{A}\|_{\mathsf{F}}^2
+ 2\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}\|_2\sqrt{s} + 2\|\mathbf{A}\|_2^2 s$$
(`NLAlib.srhtRowNormBound A s`) and $R_{\mathbf{B}}$ likewise: flatten, then sample with
replacement (`NLAlib.measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch` at
uniform weights). [Tropp2011a, Lemma 3.3] for flattening; the bound is this proof's. Any
field.
Result: amm-srht-spectral -/
theorem measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_srhtWithReplacement [Nonempty k]
    [Nonempty r] (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) /
        (max (β * srhtRowNormBound B s * specNorm A ^ 2)
            (β * srhtRowNormBound A s * specNorm B ^ 2) +
          2 * β * √(srhtRowNormBound A s * srhtRowNormBound B s) * t / 3)) +
      2 * Fintype.card n * Real.exp (-s) := by
  sorry

end Spectral

end NLAlib
