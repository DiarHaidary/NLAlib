/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.QuadraticForm.Moments
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

omit [Fintype k] in
/-- A unitary times a diagonal of signs is unitary. -/
private theorem hasOrthonormalCols_mul_diagonal {F : Matrix n n 𝕜} (hF : HasOrthonormalCols F)
    {y : n → ℝ} (hy : ∀ i, y i ^ 2 = 1) : HasOrthonormalCols (F * Matrix.diagonal fun i => (y i : 𝕜)) := by
  rw [HasOrthonormalCols, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Fᴴ,
    hF.conjTranspose_mul_self, Matrix.one_mul, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← sq, hy i,
    RCLike.ofReal_one]

/-! ### Distributional JL -/

section JL

variable {S : Ω → Matrix k n 𝕜} {F : Matrix n n 𝕜}

omit [DecidableEq n] in
/-- The JL property at $\varepsilon > 0$ from the JL property at $\varepsilon$ with every failure
bound $g(e)$, $0 < e < \varepsilon$, when $g$ is continuous at $\varepsilon$. -/
private theorem hasJLProperty_of_forall_mem_Ioo {g : ℝ → ℝ} (hg : ContinuousAt g ε)
    (hε : 0 < ε) (h : ∀ e ∈ Set.Ioo 0 ε, HasJLProperty S ε (g e) μ) :
    HasJLProperty S ε (g ε) μ := by
  intro x hx
  refine ge_of_tendsto (hg.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Iio ε))) ?_
  filter_upwards [Ioo_mem_nhdsLT hε] with e he
  exact h e he x hx

omit [DecidableEq n] in
/-- The OSE tail at $d = 1$ gives the JL tail: through
`NLAlib.IsObliviousSubspaceEmbedding.hasJLProperty` at every $e < \varepsilon$ and continuity. -/
private theorem hasJLProperty_of_forall_isObliviousSubspaceEmbedding [IsFiniteMeasure μ]
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (h1 : ∀ s : Set Ω, μ.real s ≤ 1) {c : ℝ}
    (hose : ∀ e, 0 ≤ e → e ≤ 1 → IsObliviousSubspaceEmbedding S 1 (1 - e) (1 + e)
      (2 * 1 * Real.exp (-e ^ 2 * Fintype.card k / (3 * c)) + Fintype.card n * Real.exp (-t)) μ) :
    HasJLProperty S ε
      (2 * Real.exp (-ε ^ 2 * Fintype.card k / (3 * c)) + Fintype.card n * Real.exp (-t)) μ := by
  rcases hε.eq_or_lt with rfl | hε0
  · intro x _
    refine (h1 _).trans ?_
    have : (0 : ℝ) ≤ Fintype.card n * Real.exp (-t) := by positivity
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, neg_zero, zero_mul,
      zero_div, Real.exp_zero, mul_one]
    linarith
  refine hasJLProperty_of_forall_mem_Ioo (g := fun e =>
    2 * Real.exp (-e ^ 2 * Fintype.card k / (3 * c)) + Fintype.card n * Real.exp (-t))
    (by fun_prop) hε0 fun e he => ?_
  have h := hose e he.1.le (he.2.le.trans hε1)
  rw [mul_one] at h
  exact h.hasJLProperty (by linarith [he.2]) (by linarith [he.2])

/-- The sample-size step of the two JL size forms: the JL tail at
$t = \log(\lvert n\rvert/(\delta/2))$ and the size `samplingEmbeddingDim 1 L ε (δ / 2)`. -/
private theorem hasJLProperty_of_samplingEmbeddingDim_le [IsFiniteMeasure μ] [Nonempty n]
    (hF : IsBoundedOrthonormal F β) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hk : samplingEmbeddingDim 1 (β * srhtRowBound (Fintype.card n) 1 (δ / 2)) ε (δ / 2) ≤
      Fintype.card k)
    (htail : ∀ t : ℝ, 0 ≤ t → HasJLProperty S ε
      (2 * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (1 + 2 * √t + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ) :
    HasJLProperty S ε δ μ := by
  have hn : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.2 Fintype.card_pos
  have hpos : 0 < (Fintype.card n : ℝ) / (δ / 2) := by positivity
  have hlog : 0 < Real.log (Fintype.card n / (δ / 2)) :=
    Real.log_pos ((one_lt_div (by positivity)).2 (by linarith))
  have hexp : Fintype.card n * Real.exp (-Real.log (Fintype.card n / (δ / 2))) = δ / 2 := by
    rw [Real.exp_neg, Real.exp_log hpos, inv_div, mul_div_cancel₀ _ (by positivity)]
  have hL : β * (1 + 2 * √(Real.log (Fintype.card n / (δ / 2))) +
      2 * Real.log (Fintype.card n / (δ / 2))) = β * srhtRowBound (Fintype.card n) 1 (δ / 2) := by
    rw [srhtRowBound_def, Nat.cast_one, one_mul]
  have hLpos : 0 < β * srhtRowBound (Fintype.card n) 1 (δ / 2) := by
    rw [← hL]
    exact mul_pos (one_pos.trans_le hF.one_le) (by positivity)
  refine (htail _ hlog.le).mono le_rfl ?_
  rw [hL, hexp]
  have h := two_mul_mul_exp_le_of_samplingEmbeddingDim_le hLpos hε (half_pos hδ) hk
  rw [Nat.cast_one, mul_one] at h
  linarith

omit [DecidableEq n] in
/-- The arithmetic of the two JL asymptotic forms: for $\beta \ge 1$, nonempty `n` and
$0 < \delta \le 1/2$, the size `samplingEmbeddingDim 1 L ε (δ / 2)` at the flattened coherence is
at most $72\beta(1 + \log(\lvert n\rvert/\delta))\log(1/\delta)/\varepsilon^2$. -/
private theorem samplingEmbeddingDim_one_le [Nonempty n] (hβ : 1 ≤ β) (hδ : 0 < δ)
    (hδ2 : δ ≤ 1 / 2) :
    samplingEmbeddingDim 1 (β * srhtRowBound (Fintype.card n) 1 (δ / 2)) ε (δ / 2) ≤
      72 * (β * (1 + Real.log (Fintype.card n / δ)) * Real.log (1 / δ) / ε ^ 2) := by
  refine (samplingEmbeddingDim_le _ _ ε _).trans ?_
  have hN : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.2 Fintype.card_pos
  have h2N : Real.log 2 ≤ Real.log (Fintype.card n / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
  have h2d : Real.log 2 ≤ Real.log (1 / δ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hδ]; nlinarith)
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlN : Real.log (Fintype.card n / (δ / 2)) = Real.log 2 + Real.log (Fintype.card n / δ) := by
    rw [show (Fintype.card n : ℝ) / (δ / 2) = 2 * (Fintype.card n / δ) by ring,
      Real.log_mul (by norm_num) (by positivity)]
  have hR : srhtRowBound (Fintype.card n) 1 (δ / 2) ≤
      8 * (1 + Real.log (Fintype.card n / δ)) := by
    have h := srhtRowBound_le (Fintype.card n) 1 (δ / 2)
    have hb := Real.sq_sqrt (by linarith : 0 ≤ 2 * Real.log (Fintype.card n / (δ / 2)))
    rw [Nat.cast_one, Real.sqrt_one] at h
    nlinarith [sq_nonneg (1 - √(2 * Real.log (Fintype.card n / (δ / 2))))]
  have hl : Real.log (2 * ((1 : ℕ) : ℝ) / (δ / 2)) = 2 * Real.log 2 + Real.log (1 / δ) := by
    rw [Nat.cast_one, show 2 * (1 : ℝ) / (δ / 2) = 2 * 2 * (1 / δ) by field_simp,
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by norm_num) (by norm_num)]
    ring
  rw [mul_div_assoc']
  refine div_le_div_of_nonneg_right ?_ (sq_nonneg ε)
  calc 3 * (β * srhtRowBound (Fintype.card n) 1 (δ / 2)) * Real.log (2 * ((1 : ℕ) : ℝ) / (δ / 2))
      ≤ 3 * (β * (8 * (1 + Real.log (Fintype.card n / δ)))) *
          Real.log (2 * ((1 : ℕ) : ℝ) / (δ / 2)) :=
        mul_le_mul_of_nonneg_right
          (by nlinarith [mul_le_mul_of_nonneg_left hR (by linarith : (0 : ℝ) ≤ β)])
          (by rw [hl]; linarith)
    _ ≤ 3 * (β * (8 * (1 + Real.log (Fintype.card n / δ)))) * (3 * Real.log (1 / δ)) :=
        mul_le_mul_of_nonneg_left (by rw [hl]; linarith) (by nlinarith)
    _ = 72 * (β * (1 + Real.log (Fintype.card n / δ)) * Real.log (1 / δ)) := by ring

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
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  refine hasJLProperty_of_forall_isObliviousSubspaceEmbedding hε hε1
    (measureReal_le_one_of_hasLaw_srht hS) fun e he he1 => ?_
  have h := isObliviousSubspaceEmbedding_of_hasLaw_srht hF hS 1 he he1 ht
  simp only [Nat.cast_one, one_mul] at h
  exact h

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
  rcases isEmpty_or_nonempty n with hn | hn
  · intro x hx
    simp [Subsingleton.elim x 0] at hx
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact fun x _ => (measureReal_le_one_of_hasLaw_srht hS _).trans hδ1
  exact hasJLProperty_of_samplingEmbeddingDim_le hF hε hδ hδ1 hk fun t ht =>
    hasJLProperty_of_hasLaw_srht hF hS hε.le hε1 ht

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
  refine ⟨72, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 k n _ _ _ _ _ μ S F β ε δ hF hS hε hε1 hδ hδ2 hk
  rcases isEmpty_or_nonempty n with hn | hn
  · intro x hx
    simp [Subsingleton.elim x 0] at hx
  exact hasJLProperty_of_hasLaw_srht_of_samplingEmbeddingDim_le hF hS hε hε1 hδ
    ((samplingEmbeddingDim_one_le hF.one_le hδ hδ2).trans hk)

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
  rcases isEmpty_or_nonempty n with hn | hn
  · intro x hx
    simp [Subsingleton.elim x 0] at hx
  have := hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srhtWithReplacement F)
  refine hasJLProperty_of_forall_isObliviousSubspaceEmbedding hε hε1
    (fun _ => measureReal_le_one) fun e he he1 => ?_
  have h := isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement hF hS 1 he he1 ht
  simp only [Nat.cast_one, one_mul] at h
  exact h

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
  rcases isEmpty_or_nonempty n with hn | hn
  · intro x hx
    simp [Subsingleton.elim x 0] at hx
  have := hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srhtWithReplacement F)
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact fun x _ => measureReal_le_one.trans hδ1
  exact hasJLProperty_of_samplingEmbeddingDim_le hF hε hδ hδ1 hk fun t ht =>
    hasJLProperty_of_hasLaw_srhtWithReplacement hF hS hε.le hε1 ht

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
  refine ⟨72, 1, by norm_num, one_pos, ?_⟩
  intro Ω 𝕜 k n _ _ _ _ _ μ S F β ε δ hF hS hε hε1 hδ hδ2 hk
  rcases isEmpty_or_nonempty n with hn | hn
  · intro x hx
    simp [Subsingleton.elim x 0] at hx
  exact hasJLProperty_of_hasLaw_srhtWithReplacement_of_samplingEmbeddingDim_le hF hS hε hε1 hδ
    ((samplingEmbeddingDim_one_le hF.one_le hδ hδ2).trans hk)

end JL

/-! ### The JL moment at $p = 2$ and projection-cost preservation -/

section Moment

variable {S : Ω → Matrix k n ℝ} {F : Matrix n n ℝ}

omit [Fintype k] [DecidableEq n] in
/-- **The fourth moment of a Rademacher sum**:
$\mathbb{E}(\sum_j a_j\xi_j)^4 \le 3(\sum_j a_j^2)^2$, through the variance of the quadratic form
of $\mathbf{a}\mathbf{a}^{\mathsf{T}}$. -/
private theorem integral_sum_mul_pow_four_le {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {ν : Measure Ω'} {ξ : Ω' → n → ℝ} (hξ : HasLaw ξ (rademacherVector n) ν) (a : n → ℝ) :
    ∫ ω, (∑ j, a j * ξ ω j) ^ 4 ∂ν ≤ 3 * (∑ j, a j ^ 2) ^ 2 := by
  classical
  have := hξ.isProbabilityMeasure_iff.2 inferInstance
  set A : Matrix n n ℝ := Matrix.vecMulVec a a with hAdef
  have hA : A.IsHermitian := by
    rw [Matrix.IsHermitian, hAdef, Matrix.conjTranspose_vecMulVec, star_trivial]
  have hq (x : n → ℝ) : quadForm A x = (∑ j, a j * x j) ^ 2 := by
    simp only [quadForm, hAdef, star_trivial, dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply,
      sq, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hvar := variance_quadForm_of_hasLaw_rademacherVector hξ hA
  have hmean := (isIsotropic_of_hasLaw_rademacherVector hξ).integral_quadForm A
  have htr : A.trace = ∑ j, a j ^ 2 := by
    simp only [Matrix.trace, Matrix.diag, hAdef, Matrix.vecMulVec_apply, sq]
  have hF : frobNorm A ^ 2 = (∑ j, a j ^ 2) ^ 2 := by
    rw [hAdef, frobNorm_vecMulVec, ← sq, ← pow_mul, show 2 * 2 = 2 * 2 from rfl, pow_mul,
      EuclideanSpace.norm_sq_eq]
    simp only [Real.norm_eq_abs, sq_abs]
  have hL2 : MemLp (fun ω => quadForm A (ξ ω)) 2 ν :=
    memLp_quadForm (memLp_of_hasLaw_rademacherVector hξ 4) A
  rw [variance_eq_sub hL2, hmean, htr, hF] at hvar
  have h4 : ∫ ω, (∑ j, a j * ξ ω j) ^ 4 ∂ν = ∫ ω, ((fun ω => quadForm A (ξ ω)) ^ 2) ω ∂ν := by
    refine integral_congr_ae (ae_of_all _ fun ω => ?_)
    simp only [Pi.pow_apply, hq]
    ring
  have hd : 0 ≤ ∑ i, A i i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [h4]
  nlinarith

omit [DecidableEq n] in
/-- **The second moment of an i.i.d. uniform sample sum**: for a centred population
$a : n \to \mathbb{R}$ and $\lvert k\rvert$ i.i.d. uniform indices,
$\mathbb{E}(\sum_j a_{J_j})^2 = (\lvert k\rvert/\lvert n\rvert)\sum_i a_i^2$. -/
private theorem integral_sum_sq_pi_samplingMeasure [Nonempty n] [MeasurableSpace n]
    [MeasurableSingletonClass n] (a : n → ℝ) (ha : ∑ i, a i = 0) :
    ∫ J, (∑ j, a (J j)) ^ 2
        ∂(Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : NNReal)⁻¹) =
      Fintype.card k / Fintype.card n * ∑ i, a i ^ 2 := by
  set P := Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : NNReal)⁻¹
  have := isProbabilityMeasure_samplingMeasure _ (NNReal.sum_const_inv_card (ι := n))
  have hind : iIndepFun (fun j (J : k → n) => a (J j)) P :=
    iIndepFun_pi (X := fun (_ : k) (i : n) => a i) fun _ => (measurable_of_finite _).aemeasurable
  have hmem (j : k) : MemLp (fun J : k → n => a (J j)) 2 P := .of_discrete
  have hc : (((Fintype.card n : NNReal)⁻¹ : NNReal) : ℝ) = (Fintype.card n : ℝ)⁻¹ := by
    rw [NNReal.coe_inv, NNReal.coe_natCast]
  have hev (f : n → ℝ) (j : k) : ∫ J, f (J j) ∂P = (Fintype.card n : ℝ)⁻¹ * ∑ i, f i := by
    have h := (HasLaw.id (μ := P)).eval j
    rw [show ∫ J, f (J j) ∂P = ∫ i, f i ∂(samplingMeasure fun _ : n =>
      (Fintype.card n : NNReal)⁻¹) from
      h.integral_comp (StronglyMeasurable.of_discrete).aestronglyMeasurable,
      integral_samplingMeasure, Finset.mul_sum]
    simp only [hc, smul_eq_mul]
  have hvar := IndepFun.variance_sum (s := Finset.univ) (X := fun j (J : k → n) => a (J j))
    (fun j _ => hmem j) (fun i _ j _ hij => hind.indepFun hij)
  have hsum : MemLp (∑ j ∈ Finset.univ, fun J : k → n => a (J j)) 2 P :=
    memLp_finsetSum' _ fun j _ => hmem j
  rw [variance_eq_sub hsum] at hvar
  simp only [fun j => variance_eq_sub (hmem j)] at hvar
  have hm : ∫ J, (∑ j ∈ Finset.univ, fun J : k → n => a (J j)) J ∂P = 0 := by
    simp only [Finset.sum_apply]
    rw [integral_finsetSum _ fun j _ => (hmem j).integrable one_le_two]
    simp only [hev a, ha, mul_zero, Finset.sum_const_zero]
  rw [hm] at hvar
  simp only [Pi.pow_apply, Finset.sum_apply, hev (fun i => a i ^ 2), hev a, ha, mul_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero] at hvar
  rw [hvar, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The squared norm of a sampled unit vector at uniform weights, minus one, as a sum over the
samples of the centred population $(\lvert n\rvert z_i^2 - 1)/\lvert k\rvert$. -/
private theorem norm_samplingSketchMatrix_mulVec_sq_sub_one [Nonempty k] (ι : k → n)
    {z : n → ℝ} :
    ‖WithLp.toLp 2 ((samplingSketchMatrix (fun _ : n => (Fintype.card n : NNReal)⁻¹) ι :
        Matrix k n ℝ) *ᵥ z)‖ ^ 2 - 1 =
      ∑ j, (Fintype.card n * z (ι j) ^ 2 - 1) / Fintype.card k := by
  have hK : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hrow (j : k) : ((samplingSketchMatrix (fun _ : n => (Fintype.card n : NNReal)⁻¹) ι :
      Matrix k n ℝ) *ᵥ z) j =
      (√((Fintype.card k : ℝ) * (Fintype.card n : ℝ)⁻¹))⁻¹ * z (ι j) := by
    simp only [samplingSketchMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, ite_mul,
      zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, NNReal.coe_inv, NNReal.coe_natCast]
    rfl
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, hrow, mul_pow, inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (Fintype.card k : ℝ) * (Fintype.card n : ℝ)⁻¹),
    sub_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_one_div_cancel hK]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_inv, inv_inv]
  ring

omit [DecidableEq n] in
/-- The centred population of the squared norm sums to zero at a unit vector, and its squares
give the variance $(\lvert n\rvert\sum_i z_i^4 - 1)/\lvert k\rvert$ after the factor
$\lvert k\rvert/\lvert n\rvert$. -/
private theorem sum_sq_sub_one_div_card [Nonempty k] [Nonempty n] {z : n → ℝ}
    (hz : ‖WithLp.toLp 2 z‖ = 1) :
    ∑ i, (Fintype.card n * z i ^ 2 - 1) / (Fintype.card k : ℝ) = 0 ∧
      Fintype.card k / Fintype.card n *
        ∑ i, ((Fintype.card n * z i ^ 2 - 1) / (Fintype.card k : ℝ)) ^ 2 =
      (Fintype.card n * ∑ i, z i ^ 4 - 1) / Fintype.card k := by
  have hK : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  have hz2 : ∑ i, z i ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hz
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] at h
    exact h
  have e1 (i : n) : ((Fintype.card n * z i ^ 2 - 1) / (Fintype.card k : ℝ)) ^ 2 =
      ((Fintype.card n : ℝ) ^ 2 * z i ^ 4 - 2 * Fintype.card n * z i ^ 2 + 1) /
        (Fintype.card k : ℝ) ^ 2 := by
    field_simp
    ring
  refine ⟨?_, ?_⟩
  · rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.mul_sum, hz2, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, mul_one, sub_self, zero_div]
  · simp only [e1, ← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, hz2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    field_simp
    ring

/-- **The JL second moment of row sampling without replacement** at a unit vector:
$\mathbb{E}(\|\mathbf{P}\mathbf{z}\|^2 - 1)^2 \le (\lvert n\rvert\sum_i z_i^4 - 1)/\lvert k\rvert$,
the i.i.d. value through Hoeffding's comparison. -/
private theorem integral_sq_le_of_samplingSketchWithoutReplacement [Nonempty k]
    (hk : Fintype.card k ≤ Fintype.card n) {z : n → ℝ} (hz : ‖WithLp.toLp 2 z‖ = 1) :
    ∫ P, (‖WithLp.toLp 2 (P *ᵥ z)‖ ^ 2 - 1) ^ 2 ∂(samplingSketchWithoutReplacement (𝕜 := ℝ) k n) ≤
      (Fintype.card n * ∑ i, z i ^ 4 - 1) / Fintype.card k := by
  let _ : MeasurableSpace n := ⊤
  obtain ⟨j₀⟩ := ‹Nonempty k›
  have : Nonempty n := ⟨(Function.Embedding.nonempty_of_card_le hk).some j₀⟩
  obtain ⟨ha, hv⟩ := sum_sq_sub_one_div_card (k := k) hz
  rw [samplingSketchWithoutReplacement_eq_map, integral_map (measurable_of_countable _).aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [norm_samplingSketchMatrix_mulVec_sq_sub_one]
  have h2 := integral_uniformOn_injective_le_integral_pi (Even.convexOn_pow (𝕜 := ℝ) even_two)
    (continuous_pow 2).continuousOn isClosed_univ hk
    (fun i => (Fintype.card n * z i ^ 2 - 1) / (Fintype.card k : ℝ)) fun _ => Set.mem_univ _
  rw [← samplingMeasure_const_inv_card, integral_sum_sq_pi_samplingMeasure _ ha, hv] at h2
  exact h2

/-- **The JL second moment of row sampling with replacement** at a unit vector, uniform weights:
$\mathbb{E}(\|\mathbf{P}\mathbf{z}\|^2 - 1)^2 = (\lvert n\rvert\sum_i z_i^4 - 1)/\lvert k\rvert$. -/
private theorem integral_sq_le_of_samplingSketch [Nonempty k] [Nonempty n] {z : n → ℝ}
    (hz : ‖WithLp.toLp 2 z‖ = 1) :
    ∫ P, (‖WithLp.toLp 2 (P *ᵥ z)‖ ^ 2 - 1) ^ 2
        ∂(samplingSketch (𝕜 := ℝ) k fun _ : n => (Fintype.card n : NNReal)⁻¹) ≤
      (Fintype.card n * ∑ i, z i ^ 4 - 1) / Fintype.card k := by
  let _ : MeasurableSpace n := ⊤
  obtain ⟨ha, hv⟩ := sum_sq_sub_one_div_card (k := k) hz
  rw [samplingSketch_eq_map, integral_map (measurable_of_finite _).aemeasurable
    (Continuous.aestronglyMeasurable (by fun_prop))]
  simp only [norm_samplingSketchMatrix_mulVec_sq_sub_one]
  rw [integral_sum_sq_pi_samplingMeasure _ ha, hv]

omit [Fintype k] in
/-- The mean of the fourth-power bound of the conditioned JL moment over the signs: for a unit
$\mathbf{v}$, $\lvert n\rvert\,\mathbb{E}\sum_i (\mathbf{F}\mathbf{D}\mathbf{v})_i^4 \le 3\beta^2$,
and the fourth powers are integrable. -/
private theorem integral_sum_mulVec_pow_four_le {Ω' : Type*} {mΩ' : MeasurableSpace Ω'}
    {ν : Measure Ω'} {ξ : Ω' → n → ℝ} (hξ : HasLaw ξ (rademacherVector n) ν)
    (hF : IsBoundedOrthonormal F β) {v : n → ℝ} (hv : ‖WithLp.toLp 2 v‖ = 1) :
    (∀ i, Integrable (fun ω => ((F * Matrix.diagonal (ξ ω)) *ᵥ v) i ^ 4) ν) ∧
      Fintype.card n * ∑ i, ∫ ω, ((F * Matrix.diagonal (ξ ω)) *ᵥ v) i ^ 4 ∂ν ≤ 3 * β ^ 2 := by
  have hz (ω : Ω') (i : n) : ((F * Matrix.diagonal (ξ ω)) *ᵥ v) i =
      ∑ j, (F i j * v j) * ξ ω j := by
    simp only [Matrix.mulVec, dotProduct, Matrix.mul_diagonal]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hv2 : ∑ j, v j ^ 2 = 1 := by
    have h := congrArg (· ^ 2) hv
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs, one_pow] at h
    exact h
  refine ⟨fun i => ?_, ?_⟩
  · have hm : MemLp (fun ω => ∑ j, (F i j * v j) * ξ ω j) 4 ν :=
      memLp_finsetSum _ fun j _ => (memLp_of_hasLaw_rademacherVector hξ 4 j).const_mul _
    have h := hm.integrable_norm_pow (by norm_num)
    simp only [Real.norm_eq_abs, Even.pow_abs ⟨2, rfl⟩] at h
    simpa only [hz] using h
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Finset.univ_eq_empty, Finset.sum_empty, mul_zero]
    positivity
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.2 Fintype.card_pos
  have hrow (i : n) : ∑ j, (F i j * v j) ^ 2 ≤ β / Fintype.card n := by
    calc ∑ j, (F i j * v j) ^ 2 ≤ ∑ j, β / Fintype.card n * v j ^ 2 := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [mul_pow]
          refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
          rw [le_div_iff₀ hN, mul_comm]
          simpa only [Real.norm_eq_abs, sq_abs] using hF.card_mul_norm_sq_le i j
      _ = β / Fintype.card n := by rw [← Finset.mul_sum, hv2, mul_one]
  have hi (i : n) : ∫ ω, ((F * Matrix.diagonal (ξ ω)) *ᵥ v) i ^ 4 ∂ν ≤
      3 * (β / Fintype.card n) ^ 2 := by
    simp only [hz]
    exact (integral_sum_mul_pow_four_le hξ _).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (Finset.sum_nonneg fun j _ => sq_nonneg _) (hrow i) 2) (by norm_num))
  calc Fintype.card n * ∑ i, ∫ ω, ((F * Matrix.diagonal (ξ ω)) *ᵥ v) i ^ 4 ∂ν
      ≤ Fintype.card n * ∑ _i : n, 3 * (β / Fintype.card n) ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hi i) hN.le
    _ = 3 * β ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp

/-- **Condition on the signs** for the JL moment: on the product of the signs and an independent
sampling law `ρ` whose JL second moment at every unit vector $\mathbf{z}$ is at most
$(\lvert n\rvert\sum_i z_i^4 - 1)/\lvert k\rvert$, the pushforward
$\mathbf{P}\mathbf{F}\mathbf{D}$ has the JL moment at exponent $2$ with failure
$(3\beta^2 - 1)/(\lvert k\rvert\varepsilon^2)$. -/
private theorem hasJLMoment_map_prod {ρ : Measure (Matrix k n ℝ)} [IsProbabilityMeasure ρ]
    (hF : IsBoundedOrthonormal F β) (hε : 0 < ε)
    (hint : ∀ z : n → ℝ,
      Integrable (fun P : Matrix k n ℝ => (‖WithLp.toLp 2 (P *ᵥ z)‖ ^ 2 - 1) ^ 2) ρ)
    (hρ : ∀ z : n → ℝ, ‖WithLp.toLp 2 z‖ = 1 →
      ∫ P, (‖WithLp.toLp 2 (P *ᵥ z)‖ ^ 2 - 1) ^ 2 ∂ρ ≤
        (Fintype.card n * ∑ i, z i ^ 4 - 1) / Fintype.card k) :
    HasJLMoment (fun x : (n → ℝ) × Matrix k n ℝ => x.2 * F * Matrix.diagonal x.1) ε
      ((3 * β ^ 2 - 1) / (Fintype.card k * ε ^ 2)) 2 ((rademacherVector n).prod ρ) := by
  have hfst := (measurePreserving_fst (μ := rademacherVector n) (ν := ρ)).hasLaw
  have hsnd := (measurePreserving_snd (μ := rademacherVector n) (ν := ρ)).hasLaw
  have hind : IndepFun (fun x : (n → ℝ) × Matrix k n ℝ => x.1) (fun x => x.2)
      ((rademacherVector n).prod ρ) :=
    indepFun_prod (μ := rademacherVector n) (ν := ρ) (X := id) (Y := id) measurable_id
      measurable_id
  have key (v : n → ℝ) (hv : ‖WithLp.toLp 2 v‖ = 1) :
      Integrable (fun x : (n → ℝ) × Matrix k n ℝ =>
        (‖WithLp.toLp 2 (x.2 *ᵥ ((F * Matrix.diagonal x.1) *ᵥ v))‖ ^ 2 - 1) ^ 2)
          ((rademacherVector n).prod ρ) ∧
      ∫ x, (‖WithLp.toLp 2 (x.2 *ᵥ ((F * Matrix.diagonal x.1) *ᵥ v))‖ ^ 2 - 1) ^ 2
          ∂((rademacherVector n).prod ρ) ≤ (3 * β ^ 2 - 1) / Fintype.card k := by
    obtain ⟨h4, h4le⟩ := integral_sum_mulVec_pow_four_le hfst hF hv
    set G : (n → ℝ) × Matrix k n ℝ → ℝ := fun p =>
      (‖WithLp.toLp 2 (p.2 *ᵥ ((F * Matrix.diagonal p.1) *ᵥ v))‖ ^ 2 - 1) ^ 2 with hGdef
    set H : (n → ℝ) × Matrix k n ℝ → ℝ := fun x =>
      (Fintype.card n * ∑ i, ((F * Matrix.diagonal x.1) *ᵥ v) i ^ 4 - 1) / Fintype.card k
      with hHdef
    have hG : Measurable G := (by fun_prop : Continuous _).measurable
    have hG0 : ∀ p, 0 ≤ G p := fun _ => sq_nonneg _
    have hH : Integrable H ((rademacherVector n).prod ρ) :=
      (((integrable_finsetSum _ fun i _ => h4 i).const_mul _).sub (integrable_const _)).div_const _
    have hint' : ∀ᵐ x ∂((rademacherVector n).prod ρ), Integrable (fun P => G (x.1, P)) ρ :=
      ae_of_all _ fun x => hint ((F * Matrix.diagonal x.1) *ᵥ v)
    have hle : ∀ᵐ x ∂((rademacherVector n).prod ρ), ∫ P, G (x.1, P) ∂ρ ≤ H x := by
      filter_upwards [ae_sq_eq_one_of_hasLaw_rademacherVector hfst] with x hx
      have hT : HasOrthonormalCols (F * Matrix.diagonal x.1) :=
        hasOrthonormalCols_mul_diagonal (𝕜 := ℝ) hF.hasOrthonormalCols hx
      exact hρ ((F * Matrix.diagonal x.1) *ᵥ v) (by rw [hT.norm_toLp_mulVec, hv])
    have hI := hind.integrable_comp_of_integral_le (F := G) (H := H) hfst.aemeasurable hsnd hG hG0
      hint' hle hH
    have hL := hind.integral_comp_le_of_integral_le (F := G) (H := H) hfst.aemeasurable hsnd hG
      hG0 hint' hle hH
    refine ⟨hI, hL.trans ?_⟩
    rw [hHdef, integral_div, integral_sub ((integrable_finsetSum _ fun i _ => h4 i).const_mul _)
      (integrable_const _), integral_const_mul, integral_finsetSum _ fun i _ => h4 i,
      integral_const, probReal_univ, one_smul]
    exact div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _)
  have hrw (v : n → ℝ) (x : (n → ℝ) × Matrix k n ℝ) :
      |‖WithLp.toLp 2 ((x.2 * F * Matrix.diagonal x.1) *ᵥ v)‖ ^ 2 - 1| ^ (2 : ℝ) =
        (‖WithLp.toLp 2 (x.2 *ᵥ ((F * Matrix.diagonal x.1) *ᵥ v))‖ ^ 2 - 1) ^ 2 := by
    rw [Real.rpow_two, sq_abs, Matrix.mul_assoc, Matrix.mulVec_mulVec]
  refine ⟨fun v hv => ?_, fun v hv => ?_⟩
  · simp only [hrw]
    exact (key v hv).1
  · simp only [hrw]
    refine (key v hv).2.trans_eq ?_
    rw [Real.rpow_two]
    field_simp

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
  rcases isEmpty_or_nonempty n with hn | hn
  · refine ⟨fun x hx => ?_, fun x hx => ?_⟩ <;> simp [Subsingleton.elim x 0] at hx
  let _ : MeasurableSpace n := ⊤
  rw [hS.hasJLMoment_iff, srht_eq_map_prod]
  simp only [RCLike.ofReal_real_eq_id, id]
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [samplingSketchWithoutReplacement_eq_map, uniformOn_injective_of_card_lt hk,
      Measure.map_zero, Measure.prod_zero, Measure.map_zero]
    have hβ : 0 ≤ 3 * β ^ 2 - 1 := by nlinarith [hF.one_le]
    refine ⟨fun _ _ => integrable_zero_measure, fun _ _ => ?_⟩
    rw [integral_zero_measure]
    positivity
  have := isProbabilityMeasure_samplingSketchWithoutReplacement (𝕜 := ℝ) hk
  refine (HasLaw.hasJLMoment_iff ⟨(by fun_prop : Continuous _).measurable.aemeasurable, rfl⟩).1
    (hasJLMoment_map_prod hF hε (fun z => ?_)
      fun z hz => integral_sq_le_of_samplingSketchWithoutReplacement hk hz)
  rw [samplingSketchWithoutReplacement_eq_map, integrable_map_measure
    (Continuous.aestronglyMeasurable (by fun_prop)) (measurable_of_countable _).aemeasurable]
  exact .of_finite

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
  let _ : MeasurableSpace n := ⊤
  rw [hS.hasJLMoment_iff, srhtWithReplacement_eq_map_prod]
  simp only [RCLike.ofReal_real_eq_id, id]
  have := isProbabilityMeasure_samplingSketch (𝕜 := ℝ) (k := k)
    (NNReal.sum_const_inv_card (ι := n))
  refine (HasLaw.hasJLMoment_iff ⟨(by fun_prop : Continuous _).measurable.aemeasurable, rfl⟩).1
    (hasJLMoment_map_prod hF hε (fun z => ?_) fun z hz => integral_sq_le_of_samplingSketch hz)
  rw [samplingSketch_eq_map, integrable_map_measure
    (Continuous.aestronglyMeasurable (by fun_prop)) (measurable_of_finite _).aemeasurable]
  exact .of_finite

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

omit [Fintype q] [Fintype r] in
/-- The sampled product through a unitary $\mathbf{T}$:
$\mathbf{A}^{\mathsf{H}}(\mathbf{P}\mathbf{T})^{\mathsf{H}}\mathbf{P}\mathbf{T}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}$ is the sampled product of $\mathbf{T}\mathbf{A}$ and
$\mathbf{T}\mathbf{B}$. -/
private theorem conjTranspose_mul_mul_sub_of_hasOrthonormalCols {T : Matrix n n 𝕜}
    (hT : HasOrthonormalCols T) (P : Matrix k n 𝕜) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Aᴴ * (P * T)ᴴ * (P * T) * B - Aᴴ * B =
      (T * A)ᴴ * Pᴴ * P * (T * B) - (T * A)ᴴ * (T * B) := by
  have h : (T * A)ᴴ * (T * B) = Aᴴ * B := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ,
      hT.conjTranspose_mul_self, Matrix.one_mul]
  rw [h, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

omit [Fintype k] in
/-- The flattening event of both factors fails with probability at most
$2\lvert n\rvert e^{-s}$. -/
private theorem measureReal_not_mem_flat_le {ν : Measure ((n → ℝ) × Matrix k n 𝕜)}
    {ξ : (n → ℝ) × Matrix k n 𝕜 → n → ℝ} (hξ : HasLaw ξ (rademacherVector n) ν)
    (hF : IsBoundedOrthonormal F β) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) {s : ℝ} (hs : 0 ≤ s) :
    ν.real {x | ¬ ((∀ i, ξ x i ^ 2 = 1) ∧
      (∀ i, ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ x l : 𝕜)) * A) i)‖ ^ 2 ≤
        β * srhtRowNormBound A s * (Fintype.card n : ℝ)⁻¹) ∧
      ∀ i, ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ x l : 𝕜)) * B) i)‖ ^ 2 ≤
        β * srhtRowNormBound B s * (Fintype.card n : ℝ)⁻¹)} ≤
      2 * Fintype.card n * Real.exp (-s) := by
  have : IsProbabilityMeasure ν := hξ.isProbabilityMeasure_iff.2 inferInstance
  have h1 : ν.real {x | ¬ ∀ i, ξ x i ^ 2 = 1} = 0 :=
    (measureReal_eq_zero_iff (measure_ne_top _ _)).2
      (ae_iff.1 (ae_sq_eq_one_of_hasLaw_rademacherVector hξ))
  have h2 := measureReal_exists_norm_mul_diagonal_mul_apply_sq_gt_le_of_hasLaw_rademacherVector
    hF hξ A hs
  have h3 := measureReal_exists_norm_mul_diagonal_mul_apply_sq_gt_le_of_hasLaw_rademacherVector
    hF hξ B hs
  set EA := {x | ∃ i, β * srhtRowNormBound A s * (Fintype.card n : ℝ)⁻¹ <
    ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ x l : 𝕜)) * A) i)‖ ^ 2}
  set EB := {x | ∃ i, β * srhtRowNormBound B s * (Fintype.card n : ℝ)⁻¹ <
    ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (ξ x l : 𝕜)) * B) i)‖ ^ 2}
  calc _ ≤ ν.real ({x | ¬ ∀ i, ξ x i ^ 2 = 1} ∪ (EA ∪ EB)) := by
        refine measureReal_mono (fun x hx => ?_) (measure_ne_top _ _)
        simp only [Set.mem_ofPred_eq, not_and_or, not_forall, not_le] at hx
        simp only [EA, EB, Set.mem_union, Set.mem_ofPred_eq, not_forall]
        exact hx
    _ ≤ ν.real {x | ¬ ∀ i, ξ x i ^ 2 = 1} + (ν.real EA + ν.real EB) :=
        (measureReal_union_le _ _).trans (add_le_add le_rfl (measureReal_union_le _ _))
    _ ≤ 2 * Fintype.card n * Real.exp (-s) := by
        rw [h1]
        linarith

/-- **Flatten, then sample** for approximate multiplication, on the product of the signs and an
independent sampling law `ρ`: if `ρ` multiplies every pair of fixed factors with the norms of
$\mathbf{A}$, $\mathbf{B}$ and flattened rows to within $t$ outside probability $\delta_1$, the
pushforward does outside probability $\delta_1 + 2\lvert n\rvert e^{-s}$. -/
private theorem measureReal_specNorm_map_prod_le {ρ : Measure (Matrix k n 𝕜)}
    [IsProbabilityMeasure ρ] (hF : IsBoundedOrthonormal F β) (A : Matrix n q 𝕜)
    (B : Matrix n r 𝕜) {s t δ₁ : ℝ} (hs : 0 ≤ s) (hδ₁ : 0 ≤ δ₁)
    (hsample : ∀ (A' : Matrix n q 𝕜) (B' : Matrix n r 𝕜), specNorm A' = specNorm A →
      specNorm B' = specNorm B →
      (∀ i, ‖WithLp.toLp 2 (A' i)‖ ^ 2 ≤ β * srhtRowNormBound A s * (Fintype.card n : ℝ)⁻¹) →
      (∀ i, ‖WithLp.toLp 2 (B' i)‖ ^ 2 ≤ β * srhtRowNormBound B s * (Fintype.card n : ℝ)⁻¹) →
      ρ.real {P | t ≤ specNorm (A'ᴴ * Pᴴ * P * B' - A'ᴴ * B')} ≤ δ₁) :
    (((rademacherVector n).prod ρ).map
        fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)).real
      {M | t ≤ specNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B)} ≤
      δ₁ + 2 * Fintype.card n * Real.exp (-s) := by
  have hmap : Measurable fun x : (n → ℝ) × Matrix k n 𝕜 =>
      x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜) := (by fun_prop : Continuous _).measurable
  have hE : MeasurableSet {M : Matrix k n 𝕜 | t ≤ specNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B)} :=
    measurableSet_le measurable_const (continuous_specNorm.comp (by fun_prop)).measurable
  rw [map_measureReal_apply hmap hE]
  have hfst := (measurePreserving_fst (μ := rademacherVector n) (ν := ρ)).hasLaw
  have hsnd := (measurePreserving_snd (μ := rademacherVector n) (ν := ρ)).hasLaw
  have hind : IndepFun (fun x : (n → ℝ) × Matrix k n 𝕜 => x.2) (fun x => x.1)
      ((rademacherVector n).prod ρ) :=
    (indepFun_prod (μ := rademacherVector n) (ν := ρ) (X := id) (Y := id) measurable_id
      measurable_id).symm
  have hG : MeasurableSet {y : n → ℝ | (∀ i, y i ^ 2 = 1) ∧
      (∀ i, ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (y l : 𝕜)) * A) i)‖ ^ 2 ≤
        β * srhtRowNormBound A s * (Fintype.card n : ℝ)⁻¹) ∧
      ∀ i, ‖WithLp.toLp 2 ((F * Matrix.diagonal (fun l => (y l : 𝕜)) * B) i)‖ ^ 2 ≤
        β * srhtRowNormBound B s * (Fintype.card n : ℝ)⁻¹} := by
    simp only [Set.ofPred_and, Set.ofPred_forall]
    refine (MeasurableSet.iInter fun i => ?_).inter
      ((MeasurableSet.iInter fun i => ?_).inter (MeasurableSet.iInter fun i => ?_))
    · exact measurableSet_eq_fun (by fun_prop) measurable_const
    · exact measurableSet_le (Continuous.measurable (by fun_prop)) measurable_const
    · exact measurableSet_le (Continuous.measurable (by fun_prop)) measurable_const
  refine hind.measureReal_mem_le_add (E := {p : Matrix k n 𝕜 × (n → ℝ) |
      t ≤ specNorm (Aᴴ * (p.1 * F * Matrix.diagonal fun i => (p.2 i : 𝕜))ᴴ *
        (p.1 * F * Matrix.diagonal fun i => (p.2 i : 𝕜)) * B - Aᴴ * B)})
    measurable_snd.aemeasurable measurable_fst.aemeasurable
    (measurableSet_le measurable_const (continuous_specNorm.comp (by fun_prop)).measurable)
    hG hδ₁ (fun y hy => ?_) (measureReal_not_mem_flat_le hfst hF A B hs)
  obtain ⟨hy1, hyA, hyB⟩ := hy
  have hT := hasOrthonormalCols_mul_diagonal (𝕜 := 𝕜) hF.hasOrthonormalCols hy1
  set T := F * Matrix.diagonal fun i => (y i : 𝕜) with hTdef
  have hset : {x : (n → ℝ) × Matrix k n 𝕜 | (x.2, y) ∈ {p : Matrix k n 𝕜 × (n → ℝ) |
      t ≤ specNorm (Aᴴ * (p.1 * F * Matrix.diagonal fun i => (p.2 i : 𝕜))ᴴ *
        (p.1 * F * Matrix.diagonal fun i => (p.2 i : 𝕜)) * B - Aᴴ * B)}} =
      {x | t ≤ specNorm ((T * A)ᴴ * x.2ᴴ * x.2 * (T * B) - (T * A)ᴴ * (T * B))} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [Matrix.mul_assoc x.2 F, ← hTdef, conjTranspose_mul_mul_sub_of_hasOrthonormalCols hT]
  rw [hset, hsnd.measureReal_eq (p := fun P : Matrix k n 𝕜 =>
    t ≤ specNorm ((T * A)ᴴ * Pᴴ * P * (T * B) - (T * A)ᴴ * (T * B)))
    (measurableSet_le measurable_const (continuous_specNorm.comp (by fun_prop)).measurable)]
  exact hsample _ _ (hT.specNorm_mul_left A) (hT.specNorm_mul_left B) hyA hyB

omit [DecidableEq n] in
/-- The degenerate case of the SRHT spectral tails, empty `n`: both factors vanish. -/
private theorem measureReal_specNorm_ge_le_of_isEmpty [IsEmpty n] [Nonempty r]
    (h1 : ∀ s : Set Ω, μ.real s ≤ 1) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) {t : ℝ} (ht : 0 ≤ t)
    (x : ℝ) {y : ℝ} (hy : 0 ≤ y) :
    μ.real {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(Fintype.card k * t ^ 2 / 2) / x) + y := by
  have hA : A = 0 := Matrix.ext fun i => isEmptyElim i
  have hr : (1 : ℝ) ≤ Fintype.card q + Fintype.card r := by
    have : (1 : ℝ) ≤ Fintype.card r := by exact_mod_cast Fintype.card_pos
    linarith [(Nat.cast_nonneg (α := ℝ) (Fintype.card q))]
  rcases ht.eq_or_lt with rfl | ht'
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_div,
      neg_zero, Real.exp_zero, mul_one]
    linarith [h1 {ω | 0 ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)}]
  have hE : {ω | t ≤ specNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} = ∅ := by
    ext ω
    simp [hA, specNorm_zero, not_le.2 ht']
  rw [hE, measureReal_empty]
  positivity

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
  rcases isEmpty_or_nonempty n with hn | hn
  · exact measureReal_specNorm_ge_le_of_isEmpty (S := S) (measureReal_le_one_of_hasLaw_srht hS)
      A B ht _ (by positivity)
  let _ : MeasurableSpace n := ⊤
  have hE : MeasurableSet {M : Matrix k n 𝕜 | t ≤ specNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B)} :=
    measurableSet_le measurable_const (continuous_specNorm.comp (by fun_prop)).measurable
  rw [hS.measureReal_eq hE, srht_eq_map_prod]
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [samplingSketchWithoutReplacement_eq_map, uniformOn_injective_of_card_lt hk,
      Measure.map_zero, Measure.prod_zero, Measure.map_zero, measureReal_zero_apply]
    positivity
  have := isProbabilityMeasure_samplingSketchWithoutReplacement (𝕜 := 𝕜) hk
  have hβ : 0 ≤ β := zero_le_one.trans hF.one_le
  have hRA := srhtRowNormBound_nonneg A hs
  have hRB := srhtRowNormBound_nonneg B hs
  refine measureReal_specNorm_map_prod_le hF A B hs (by positivity)
    fun A' B' hA' hB' hrA hrB => ?_
  rcases isEmpty_or_nonempty k with hk0 | hk0
  · refine measureReal_le_one.trans ?_
    have : (1 : ℝ) ≤ Fintype.card r := by exact_mod_cast Fintype.card_pos
    rw [Fintype.card_eq_zero (α := k), Nat.cast_zero, zero_mul, zero_div, neg_zero, zero_div,
      Real.exp_zero, mul_one]
    linarith [(Nat.cast_nonneg (α := ℝ) (Fintype.card q))]
  have h :=
    measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketchWithoutReplacement
      (HasLaw.id (μ := samplingSketchWithoutReplacement k n)) A' B' (mul_nonneg hβ hRA)
      (mul_nonneg hβ hRB) hrA hrB ht
  rw [hA', hB', show β * srhtRowNormBound A s * (β * srhtRowNormBound B s) =
    β ^ 2 * (srhtRowNormBound A s * srhtRowNormBound B s) by ring,
    Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ, ← mul_assoc] at h
  exact h

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
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : srhtWithReplacement k F = 0 := by
      let _ : MeasurableSpace n := ⊤
      have hpi : (Measure.pi fun _ : k =>
          samplingMeasure fun _ : n => (Fintype.card n : NNReal)⁻¹) = 0 := by
        rw [← Measure.measure_univ_eq_zero, Measure.pi_univ]
        exact Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary k))
          (by simp [samplingMeasure])
      rw [srhtWithReplacement_eq_map_prod, samplingSketch_eq_map, hpi, Measure.map_zero,
        Measure.prod_zero, Measure.map_zero]
    have hμ : μ = 0 := (Measure.map_eq_zero_iff hS.aemeasurable).1 (hS.map_eq.trans h0)
    exact measureReal_specNorm_ge_le_of_isEmpty (S := S)
      (fun s => by rw [hμ, measureReal_zero_apply]; exact zero_le_one) A B ht _ (by positivity)
  let _ : MeasurableSpace n := ⊤
  have hE : MeasurableSet {M : Matrix k n 𝕜 | t ≤ specNorm (Aᴴ * Mᴴ * M * B - Aᴴ * B)} :=
    measurableSet_le measurable_const (continuous_specNorm.comp (by fun_prop)).measurable
  rw [hS.measureReal_eq hE, srhtWithReplacement_eq_map_prod]
  have := isProbabilityMeasure_samplingSketch (𝕜 := 𝕜) (k := k)
    (NNReal.sum_const_inv_card (ι := n))
  have hβ : 0 ≤ β := zero_le_one.trans hF.one_le
  have hRA := srhtRowNormBound_nonneg A hs
  have hRB := srhtRowNormBound_nonneg B hs
  have hc : ((((Fintype.card n : NNReal)⁻¹ : NNReal)) : ℝ) = (Fintype.card n : ℝ)⁻¹ := by
    rw [NNReal.coe_inv, NNReal.coe_natCast]
  refine measureReal_specNorm_map_prod_le hF A B hs (by positivity)
    fun A' B' hA' hB' hrA hrB => ?_
  have h := measureReal_specNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_samplingSketch
    (HasLaw.id (μ := samplingSketch k fun _ : n => (Fintype.card n : NNReal)⁻¹))
    NNReal.sum_const_inv_card A' B' (mul_nonneg hβ hRA) (mul_nonneg hβ hRB)
    (fun i => by rw [hc]; exact hrA i) (fun i => by rw [hc]; exact hrB i) ht
  rw [hA', hB', show β * srhtRowNormBound A s * (β * srhtRowNormBound B s) =
    β ^ 2 * (srhtRowNormBound A s * srhtRowNormBound B s) by ring,
    Real.sqrt_mul (sq_nonneg β), Real.sqrt_sq hβ, ← mul_assoc] at h
  exact h

end Spectral

end NLAlib
