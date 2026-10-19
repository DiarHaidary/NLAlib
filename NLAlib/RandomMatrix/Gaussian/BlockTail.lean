/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlib.Probability.Tail
public import NLAlib.RandomMatrix.Gaussian.BlockMoments
public import NLAlib.RandomMatrix.Gaussian.Concentration

/-!
# Tails of the Gaussian block of the randomized range finder

For a standard Gaussian $r \times k$ matrix $\mathbf{G}$ with $d = \lvert k \rvert - \lvert r
\rvert + 1$, the diagonal entries of $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$ are
$1/\chi^2_d$, so the exact small ball of $\chi^2$ bounds their upper tails, and their sum, the
trace $\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$, has the
tail <!-- value gaussianPinvFrobTail {\lvert r\rvert} d t -->
$$\mathbb{P}\Bigl\{\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 > \frac{t\lvert r\rvert}{d}\Bigr\} \le
\frac{2\sqrt{\lvert r\rvert}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}$$
for $t > 0$, the right side being `NLAlib.gaussianPinvFrobTail` (Tropp and Webber's (B.3), with a
smaller constant, by Markov's inequality on a truncated $d$-th power and the layer-cake formula in
place of their parallel sum). Markov's inequality on the spectral moments gives the spectral tail
of $\mathbf{G}^{+}$.

For frames $\mathbf{V}_1$, $\mathbf{V}_2$ with $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$
and a fixed $\mathbf{S}$, the blocks $\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{G}$ are
independent standard Gaussian matrices; conditioning on $\mathbf{G}_1$ through the
independent-factor concentration
`NLAlib.measureReal_gt_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun` gives the tails of
$\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|$ that the range finder's tail bounds consume: Tropp and
Webber's Proposition 8.6 (8.9) in the Frobenius norm, and the shapes of Halko, Martinsson and
Tropp's proofs of Theorems 10.7 and 10.8.

## Main definitions

* `NLAlib.gaussianPinvFrobTail k d t`: the tail of $\|\mathbf{G}^{+}\|_{\mathsf{F}}^2$.

## Main results

* `NLAlib.gaussianPinvFrobTail_nonneg`, `NLAlib.gaussianPinvFrobTail_le`,
  `NLAlib.one_le_gaussianPinvFrobTail_zero`: the API of the named tail.
* `NLAlib.measureReal_inv_mul_conjTranspose_apply_self_ge_le_of_hasLaw_gaussianMatrix`.
* `NLAlib.measureReal_frobNorm_pinv_sq_gt_le_of_hasLaw_gaussianMatrix`: the trace tail of an
  inverse Wishart matrix.
* `NLAlib.measureReal_specNorm_pinv_gt_le_of_hasLaw_gaussianMatrix`.
* `NLAlib.measureReal_frobNorm_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix`: the block
  tail.
* `NLAlib.measureReal_specNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix`,
  `NLAlib.measureReal_frobNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix`: the block tails
  in the shape of Halko, Martinsson and Tropp.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k r s a : Type*} [Fintype n]
  [Fintype k] [Fintype r] [Fintype s] [Fintype a]

/-! ### The named tail -/

/-- **The tail of the Frobenius norm of a Gaussian pseudoinverse**, the right side of
the bound <!-- value gaussianPinvFrobTail k d t -->
$$\mathbb{P}\Bigl\{\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 > \frac{tk}{d}\Bigr\} \le
\frac{2\sqrt{k}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}$$
for a real $k \times (k + d - 1)$ standard Gaussian $\mathbf{G}$ and $t > 0$
(`NLAlib.measureReal_frobNorm_pinv_sq_gt_le_of_hasLaw_gaussianMatrix`). Source value
$\sqrt{\pi k/d}\,(e/t)^{d/2}$ [TroppWebber2023, Lemma B.2 (B.3)], printed as
$\sqrt{\pi k}\,(e/t)^{d/2}$ in [TroppWebber2023, Theorem 8.1]. The proved value is smaller for every
$d \ge 1$: by $\Gamma(x + 1) \ge \sqrt{2\pi x}\,(x/e)^x$ it is at most $2/\pi$ times (B.3)'s and
$2/(\pi\sqrt{d})$ times Theorem 8.1's, and asymptotically $2/\pi$ times (B.3)'s. The displayed
comparison with (B.3) needs Stirling's lower bound for $\Gamma$ at half-integers, which Mathlib
does not have; the comparison lemma is `NLAlib.gaussianPinvFrobTail_le`. Values: $0$ at $k = 0$,
$2\sqrt{k} \ge 2$ at $d = 0$; meaningful for $t > 0$. Consumers use its API. -/
noncomputable irreducible_def gaussianPinvFrobTail (k d : ℕ) (t : ℝ) : ℝ :=
  2 * √(k : ℝ) * ((d : ℝ) / (2 * t)) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1)

/-- The named tail is nonnegative: for $t > 0$, <!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1) \ge 0$ (`gaussianPinvFrobTail k d t`); for
$t \le 0$ the real power of a negative base is not sign-controlled. -/
theorem gaussianPinvFrobTail_nonneg (k d : ℕ) {t : ℝ} (ht : 0 < t) :
    0 ≤ gaussianPinvFrobTail k d t := by
  rw [gaussianPinvFrobTail_def]
  have := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 + 1 by positivity)
  positivity

/-- At $d = 0$ the named tail is $2\sqrt{k}$, at least $1$ for $k \ge 1$: a bound with this
failure probability says nothing. -/
theorem one_le_gaussianPinvFrobTail_zero {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    1 ≤ gaussianPinvFrobTail k 0 t := by
  rw [gaussianPinvFrobTail_def]
  simp only [Nat.cast_zero, zero_div, Real.rpow_zero, mul_one, zero_add, Real.Gamma_one, div_one]
  have : (1 : ℝ) ≤ √(k : ℝ) := Real.one_le_sqrt.2 (by exact_mod_cast hk)
  linarith

/-- The explicit comparison: for $t > 0$, <!-- value gaussianPinvFrobTail k d t -->
$2\sqrt{k}\,(d/(2t))^{d/2}/\Gamma(d/2 + 1) \le 2\sqrt{k}\,(e/t)^{d/2}$, the left side being
`gaussianPinvFrobTail k d t`, by $\Gamma(x + 1) \ge (x/e)^x$
(`Real.rpow_mul_exp_neg_le_Gamma_add_one`). The right side is $2/\sqrt{\pi}$ times the failure
term $\sqrt{\pi k}\,(e/t)^{d/2}$ of [TroppWebber2023, Theorem 8.1]. -/
theorem gaussianPinvFrobTail_le (k d : ℕ) {t : ℝ} (ht : 0 < t) :
    gaussianPinvFrobTail k d t ≤ 2 * √(k : ℝ) * (Real.exp 1 / t) ^ ((d : ℝ) / 2) := by
  rw [gaussianPinvFrobTail_def, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp
  set x : ℝ := (d : ℝ) / 2
  have hx : 0 < x := by positivity
  have hΓ := Real.rpow_mul_exp_neg_le_Gamma_add_one hx.le
  refine (div_le_div_of_nonneg_left (by positivity) (by positivity) hΓ).trans (le_of_eq ?_)
  rw [show (d : ℝ) / (2 * t) = x / t by simp only [x]; field_simp,
    Real.div_rpow hx.le ht.le, Real.div_rpow (Real.exp_pos 1).le ht.le, Real.exp_one_rpow,
    Real.exp_neg]
  have : 0 < x ^ x := Real.rpow_pos_of_pos hx x
  have : 0 < t ^ x := Real.rpow_pos_of_pos ht x
  field_simp

/-! ### Tails of the pseudoinverse -/

omit [Fintype r] in
/-- The diagonal entries of $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}$ are measurable in
$\mathbf{G}$. -/
private theorem measurable_inv_mul_conjTranspose_apply [Fintype r] [DecidableEq r] (i : r) :
    Measurable fun G : Matrix r k ℝ => (G * Gᴴ)⁻¹ i i :=
  (Matrix.measurable_apply i i).comp measurable_mul_conjTranspose_inv

omit [Fintype k] in
private theorem inv_mul_conjTranspose_apply_self_nonneg [Fintype k] [DecidableEq r]
    (G : Matrix r k ℝ) (i : r) : 0 ≤ (G * Gᴴ)⁻¹ i i :=
  (Matrix.posSemidef_self_mul_conjTranspose G).inv.diag_nonneg

/-- **The upper tail of a diagonal entry of an inverse Wishart matrix**: for an $r \times k$
standard Gaussian $\mathbf{G}$, $d = \lvert k \rvert - \lvert r \rvert + 1$ and $s > 0$,
$$\mathbb{P}\{s \le (\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}_{ii}\} \le
\frac{(1/(2s))^{d/2}}{\Gamma(d/2 + 1)}\,,$$
the exact small ball of $\chi^2_d$
(`NLAlib.measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector`) at $u = 1/s$, since
the entry is $1/\chi^2_d$
(`NLAlib.hasLaw_inv_mul_conjTranspose_apply_self_of_hasLaw_gaussianMatrix`). The input of
[TroppWebber2023, Lemma B.2]. -/
theorem measureReal_inv_mul_conjTranspose_apply_self_ge_le_of_hasLaw_gaussianMatrix
    [DecidableEq r] {X : Ω → Matrix r k ℝ} (hX : HasLaw X (gaussianMatrix r k) μ) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (i : r) {s : ℝ} (hs : 0 < s) :
    μ.real {ω | s ≤ (X ω * (X ω)ᴴ)⁻¹ i i} ≤
      (1 / (2 * s)) ^ ((d : ℝ) / 2) / Real.Gamma ((d : ℝ) / 2 + 1) := by
  have hY := hasLaw_inv_mul_conjTranspose_apply_self_of_hasLaw_gaussianMatrix hX hd i
  have hm : Measurable fun z : Fin d → ℝ => (‖WithLp.toLp 2 z‖ ^ 2)⁻¹ := by fun_prop
  have hI : MeasurableSet {y : ℝ | s ≤ y} := measurableSet_Ici
  rw [hY.measureReal_eq (p := fun y => s ≤ y) hI, measureReal_def, Measure.map_apply hm hI,
    ← measureReal_def]
  have hsub : (fun z : Fin d → ℝ => (‖WithLp.toLp 2 z‖ ^ 2)⁻¹) ⁻¹' {y | s ≤ y} ⊆
      {z | ‖WithLp.toLp 2 z‖ ^ 2 ≤ 1 / s} := by
    intro z (hz : s ≤ (‖WithLp.toLp 2 z‖ ^ 2)⁻¹)
    change ‖WithLp.toLp 2 z‖ ^ 2 ≤ 1 / s
    rcases (sq_nonneg ‖WithLp.toLp 2 z‖).eq_or_lt with h0 | hpos
    · rw [← h0]; positivity
    · rw [le_div_iff₀ hs]
      rw [le_inv_comm₀ hs hpos] at hz
      calc ‖WithLp.toLp 2 z‖ ^ 2 * s ≤ s⁻¹ * s := by gcongr
        _ = 1 := inv_mul_cancel₀ hs.ne'
  refine (measureReal_mono hsub).trans ?_
  have h := measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector
    (HasLaw.id (μ := gaussianVector (Fin d))) (u := 1 / s) (by positivity)
  simp only [id, Fintype.card_fin] at h
  rwa [show 1 / s / 2 = 1 / (2 * s) by field_simp] at h

/-- **Truncated mean by the layer cake**: if $Z \ge 0$ has $\mathbb{P}\{Z > s\} \le K s^{-1/2}$
for every $s > 0$, then $\mathbb{E}\min(a, Z) \le 2K\sqrt{a}$. -/
private theorem integral_min_le_two_mul_sqrt {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {Z : α → ℝ} (hZ : Measurable Z) (hZ0 : ∀ x, 0 ≤ Z x) {c K : ℝ}
    (hc : 0 ≤ c)
    (htail : ∀ s : ℝ, 0 < s → ν.real {x | s < Z x} ≤ K * s ^ (-(1 / 2 : ℝ))) :
    ∫ x, min c (Z x) ∂ν ≤ 2 * K * √c := by
  have hint : Integrable (fun x => min c (Z x)) ν := by
    refine Integrable.of_bound (C := c) ((measurable_const.min hZ).aestronglyMeasurable)
      (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (le_min hc (hZ0 x))]
    exact min_le_left _ _
  rw [hint.integral_eq_integral_meas_lt (ae_of_all _ fun x => le_min hc (hZ0 x))]
  have hset : ∀ t : ℝ, ν.real {x | t < min c (Z x)} =
      (Set.Iio c).indicator (fun t => ν.real {x | t < Z x}) t := by
    intro t
    by_cases ht : t < c
    · rw [Set.indicator_of_mem (show t ∈ Set.Iio c from ht)]
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq, lt_min_iff, ht, true_and]
    · rw [Set.indicator_of_notMem (show t ∉ Set.Iio c from ht)]
      convert measureReal_empty (μ := ν)
      ext x
      simp only [Set.mem_ofPred_eq, lt_min_iff, ht, false_and, Set.mem_empty_iff_false]
  simp only [hset]
  rw [setIntegral_indicator measurableSet_Iio, Set.Ioi_inter_Iio]
  have hmeas : Measurable fun t : ℝ => ν.real {x | t < Z x} :=
    Antitone.measurable fun t₁ t₂ h12 =>
      measureReal_mono fun x (hx : t₂ < Z x) => lt_of_le_of_lt h12 hx
  have hrp : IntegrableOn (fun t : ℝ => K * t ^ (-(1 / 2 : ℝ))) (Set.Ioc 0 c) :=
    ((intervalIntegral.intervalIntegrable_rpow' (by norm_num)).const_mul K).1
  calc ∫ t in Set.Ioo 0 c, ν.real {x | t < Z x}
      ≤ ∫ t in Set.Ioo 0 c, K * t ^ (-(1 / 2 : ℝ)) := by
        refine setIntegral_mono_on ?_ (hrp.mono_set Set.Ioo_subset_Ioc_self) measurableSet_Ioo
          fun t ht => htail t ht.1
        refine Measure.integrableOn_of_bounded (M := 1) (by simp) hmeas.aestronglyMeasurable
          (ae_of_all _ fun t => ?_)
        rw [Real.norm_of_nonneg measureReal_nonneg]
        exact measureReal_le_one
    _ = 2 * K * √c := by
        rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hc,
          intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num)),
          Real.zero_rpow (by norm_num), sub_zero, Real.sqrt_eq_rpow]
        norm_num
        ring

/-- **The sum of variables with polynomial tails**: if $D_i \ge 0$, $i \in r$, $R = \lvert r \rvert
\ge 1$, have $\mathbb{P}\{u \le D_i\} \le K u^{-d/2}$ for every $u > 0$, with $d \ge 1$, then
$\mathbb{P}\{v < \sum_i D_i\} \le 2KR\sqrt{R^{d-1}}\,v^{-d/2}$, by Markov's inequality on
$\min(v^d, (\sum_i D_i)^d) \le R^{d-1}\sum_i \min(v^d/R^{d-1}, D_i^d)$ and the layer cake. -/
private theorem measureReal_lt_sum_le {α : Type*} [MeasurableSpace α] {ν : Measure α}
    [IsProbabilityMeasure ν] {D : r → α → ℝ} (hD : ∀ i, Measurable (D i))
    (hD0 : ∀ i x, 0 ≤ D i x) (hr : 0 < Fintype.card r) {d : ℕ} (hd : 0 < d) {K : ℝ}
    (htail : ∀ i, ∀ u : ℝ, 0 < u → ν.real {x | u ≤ D i x} ≤ K * u ^ (-((d : ℝ) / 2)))
    {v : ℝ} (hv : 0 < v) :
    ν.real {x | v < ∑ i, D i x} ≤
      2 * K * Fintype.card r * √((Fintype.card r : ℝ) ^ (d - 1)) / v ^ ((d : ℝ) / 2) := by
  set R : ℝ := (Fintype.card r : ℝ) with hR_def
  have hR : 0 < R := Nat.cast_pos.2 hr
  set N : ℝ := R ^ (d - 1) with hN_def
  have hN : 0 < N := by positivity
  set w : ℝ := v ^ ((d : ℝ) / 2) with hw_def
  have hw : 0 < w := Real.rpow_pos_of_pos hv _
  have hvd : v ^ d = w ^ 2 := by
    rw [hw_def, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hv.le]
    congr 1
    push_cast
    ring
  set c : ℝ := v ^ d / N with hc_def
  have hc : 0 ≤ c := by positivity
  -- the tail of `D i ^ d`
  have htail' : ∀ i, ∀ s : ℝ, 0 < s → ν.real {x | s < D i x ^ d} ≤ K * s ^ (-(1 / 2 : ℝ)) := by
    intro i s hs
    have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    refine (measureReal_mono fun x (hx : s < D i x ^ d) => ?_).trans
      ((htail i (s ^ ((d : ℝ)⁻¹)) (Real.rpow_pos_of_pos hs _)).trans (le_of_eq ?_))
    · change s ^ ((d : ℝ)⁻¹) ≤ D i x
      have h := Real.rpow_le_rpow hs.le hx.le (inv_nonneg.2 (Nat.cast_nonneg d))
      rwa [← Real.rpow_natCast, ← Real.rpow_mul (hD0 i x), mul_inv_cancel₀ hdr,
        Real.rpow_one] at h
    · rw [← Real.rpow_mul hs.le]
      congr 2
      field_simp
  -- the pointwise bound
  have hpt : ∀ x, min (v ^ d) ((∑ i, D i x) ^ d) ≤ N * ∑ i, min c (D i x ^ d) := by
    intro x
    have hpow : (∑ i, D i x) ^ d ≤ N * ∑ i, D i x ^ d := by
      obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
      have h := pow_sum_div_card_le_sum_pow (s := Finset.univ) (fun i _ => hD0 i x) e
      rw [div_le_iff₀' (by positivity), Finset.card_univ] at h
      simpa only [hN_def, Nat.add_sub_cancel] using h
    have hmin : min c (∑ i, D i x ^ d) ≤ ∑ i, min c (D i x ^ d) := by
      by_cases h : ∃ i, c ≤ D i x ^ d
      · obtain ⟨i, hi⟩ := h
        calc min c (∑ i, D i x ^ d) ≤ c := min_le_left _ _
          _ = min c (D i x ^ d) := (min_eq_left hi).symm
          _ ≤ ∑ j, min c (D j x ^ d) :=
            Finset.single_le_sum (f := fun j => min c (D j x ^ d))
              (fun j _ => le_min hc (pow_nonneg (hD0 j x) d)) (Finset.mem_univ i)
      · push Not at h
        refine (min_le_right _ _).trans (le_of_eq ?_)
        exact Finset.sum_congr rfl fun i _ => (min_eq_right (h i).le).symm
    calc min (v ^ d) ((∑ i, D i x) ^ d) ≤ min (v ^ d) (N * ∑ i, D i x ^ d) :=
          min_le_min le_rfl hpow
      _ = N * min c (∑ i, D i x ^ d) := by
          rw [mul_min_of_nonneg _ _ hN.le, hc_def, mul_div_cancel₀ _ hN.ne']
      _ ≤ N * ∑ i, min c (D i x ^ d) := mul_le_mul_of_nonneg_left hmin hN.le
  have hWm : Measurable fun x => min (v ^ d) ((∑ i, D i x) ^ d) :=
    measurable_const.min ((Finset.measurable_sum _ fun i _ => hD i).pow_const d)
  have hWint : Integrable (fun x => min (v ^ d) ((∑ i, D i x) ^ d)) ν := by
    refine Integrable.of_bound (C := v ^ d) hWm.aestronglyMeasurable (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (le_min (by positivity)
      (pow_nonneg (Finset.sum_nonneg fun i _ => hD0 i x) d))]
    exact min_le_left _ _
  have hint_i : ∀ i, Integrable (fun x => min c (D i x ^ d)) ν := fun i => by
    refine Integrable.of_bound (C := c)
      ((measurable_const.min ((hD i).pow_const d)).aestronglyMeasurable) (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (le_min hc (pow_nonneg (hD0 i x) d))]
    exact min_le_left _ _
  have hE : ∫ x, min (v ^ d) ((∑ i, D i x) ^ d) ∂ν ≤ N * (R * (2 * K * √c)) := by
    calc ∫ x, min (v ^ d) ((∑ i, D i x) ^ d) ∂ν
        ≤ ∫ x, N * ∑ i, min c (D i x ^ d) ∂ν :=
          integral_mono hWint ((integrable_finsetSum _ fun i _ => hint_i i).const_mul N) hpt
      _ = N * ∑ i, ∫ x, min c (D i x ^ d) ∂ν := by
          rw [integral_const_mul, integral_finsetSum _ fun i _ => hint_i i]
      _ ≤ N * ∑ _i : r, 2 * K * √c := by
          gcongr with i
          exact integral_min_le_two_mul_sqrt ((hD i).pow_const d)
            (fun x => pow_nonneg (hD0 i x) d) hc (htail' i)
      _ = N * (R * (2 * K * √c)) := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hsub : {x | v < ∑ i, D i x} ⊆ {x | v ^ d ≤ min (v ^ d) ((∑ i, D i x) ^ d)} := by
    intro x (hx : v < ∑ i, D i x)
    change v ^ d ≤ min (v ^ d) ((∑ i, D i x) ^ d)
    exact le_min le_rfl (pow_le_pow_left₀ hv.le hx.le d)
  refine (measureReal_mono hsub).trans ((measureReal_ge_le_integral_div
    (ae_of_all _ fun x => le_min (by positivity)
      (pow_nonneg (Finset.sum_nonneg fun i _ => hD0 i x) d)) hWint (by positivity)).trans ?_)
  refine (div_le_div_of_nonneg_right hE (by positivity)).trans (le_of_eq ?_)
  have hsq : √c = w / √N := by
    rw [hc_def, hvd, Real.sqrt_div' _ hN.le, Real.sqrt_sq hw.le]
  have hsN : 0 < √N := Real.sqrt_pos.2 hN
  rw [hsq, hvd]
  field_simp
  rw [Real.sq_sqrt hN.le]
  ring

/-- On the law: the trace tail at a positive number of rows and degrees of freedom. -/
private theorem gaussianMatrix_real_lt_sum_le [DecidableEq r]
    (hr : 0 < Fintype.card r) {d : ℕ} (hd0 : 0 < d)
    (hd : Fintype.card r + d = Fintype.card k + 1) {t : ℝ} (ht : 0 < t) :
    (gaussianMatrix r k).real {G | t * Fintype.card r / d < ∑ i, (G * Gᴴ)⁻¹ i i} ≤
      gaussianPinvFrobTail (Fintype.card r) d t := by
  set x : ℝ := (d : ℝ) / 2
  set Γ := Real.Gamma (x + 1)
  have hΓ : 0 < Γ := Real.Gamma_pos_of_pos (by positivity)
  have hR : (0 : ℝ) < Fintype.card r := Nat.cast_pos.2 hr
  have hdr : (0 : ℝ) < d := Nat.cast_pos.2 hd0
  have htail : ∀ i : r, ∀ u : ℝ, 0 < u →
      (gaussianMatrix r k).real {G | u ≤ (G * Gᴴ)⁻¹ i i} ≤ ((1 / 2) ^ x / Γ) * u ^ (-x) := by
    intro i u hu
    refine (measureReal_inv_mul_conjTranspose_apply_self_ge_le_of_hasLaw_gaussianMatrix
      (HasLaw.id (μ := gaussianMatrix r k)) hd i hu).trans (le_of_eq ?_)
    rw [show 1 / (2 * u) = 1 / 2 * u⁻¹ by field_simp, Real.mul_rpow (by norm_num)
      (inv_nonneg.2 hu.le), Real.inv_rpow hu.le, Real.rpow_neg hu.le]
    ring
  refine (measureReal_lt_sum_le (fun i => measurable_inv_mul_conjTranspose_apply i)
    (fun i G => inv_mul_conjTranspose_apply_self_nonneg G i) hr hd0 htail
    (by positivity)).trans (le_of_eq ?_)
  rw [gaussianPinvFrobTail_def]
  set R : ℝ := (Fintype.card r : ℝ)
  -- `R * √(R ^ (d - 1)) = √R * R ^ x`
  have hRR : R * √(R ^ (d - 1)) = √R * R ^ x := by
    have h1 : R ^ x = √(R ^ d) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hR.le]
      congr 1
      simp only [x]
      ring
    have e1 : R * √(R ^ (d - 1)) = √(R ^ 2 * R ^ (d - 1)) := by
      rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hR.le]
    rw [e1, h1, ← Real.sqrt_mul hR.le, ← pow_succ', ← pow_add]
    congr 2
    omega
  rw [show Real.Gamma ((d : ℝ) / 2 + 1) = Γ from rfl, show ((d : ℝ) / 2) = x from rfl,
    show (2 * ((1 / 2) ^ x / Γ) * R * √(R ^ (d - 1))) =
      2 * ((1 / 2) ^ x / Γ) * (R * √(R ^ (d - 1))) by ring, hRR,
    Real.div_rpow (by positivity) hdr.le, Real.mul_rpow ht.le hR.le,
    Real.div_rpow hdr.le (by positivity), Real.mul_rpow (by norm_num) ht.le, Real.div_rpow
    (by norm_num) (by norm_num), Real.one_rpow]
  have : 0 < R ^ x := Real.rpow_pos_of_pos hR x
  have : 0 < t ^ x := Real.rpow_pos_of_pos ht x
  have : 0 < (2 : ℝ) ^ x := Real.rpow_pos_of_pos two_pos x
  have : 0 < (d : ℝ) ^ x := Real.rpow_pos_of_pos hdr x
  clear_value x Γ
  field_simp

/-- **The trace tail of an inverse Wishart matrix**: for an $r \times k$ standard Gaussian
$\mathbf{G}$, $d = \lvert k\rvert - \lvert r\rvert + 1$ and
$t > 0$, <!-- value gaussianPinvFrobTail {\lvert r\rvert} d t -->
$$\mathbb{P}\Bigl\{\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 > \frac{t\lvert r\rvert}{d}\Bigr\} \le
\frac{2\sqrt{\lvert r\rvert}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}\,,$$
the right side being `gaussianPinvFrobTail |r| d t`. Off a null set
$\|\mathbf{G}^{+}\|_{\mathsf{F}}^2 = \sum_i D_i$ with
$D_i = (\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1}_{ii} \sim 1/\chi^2_d$; Markov's inequality on
$\min(v^d, (\sum_i D_i)^d)$, the power-mean inequality and the layer cake for
$\mathbb{E}\min(a, D_i^d)$ replace the parallel sum of the source.
[TroppWebber2023, Lemma B.2 (B.3)], there $\sqrt{\pi\lvert r\rvert/d}\,(e/t)^{d/2}$, which this
bound is below for every $d \ge 1$. Compare [HalkoMartinssonTropp2011, Proposition 10.4 (10.5)]:
in their notation ($k = \lvert r\rvert$, $p = d - 1$), $4t^{-p}$ at $\sqrt{12k/p}\,t$, which this
bound is below unless $k > 4(12/e)^{p+1}t^2$. For
$d = 0$ the bound is at least $2$; for empty $r$ the event is empty.
Result: inverse-wishart-trace-tail -/
theorem measureReal_frobNorm_pinv_sq_gt_le_of_hasLaw_gaussianMatrix
    {X : Ω → Matrix r k ℝ} (hX : HasLaw X (gaussianMatrix r k) μ) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t * Fintype.card r / d < frobNorm (pinv (X ω)) ^ 2} ≤
      gaussianPinvFrobTail (Fintype.card r) d t := by
  simp only [← not_le]
  classical
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have h0 := gaussianPinvFrobTail_nonneg (Fintype.card r) d ht
  rcases Nat.eq_zero_or_pos (Fintype.card r) with hr | hr
  · have : IsEmpty r := Fintype.card_eq_zero_iff.mp hr
    have hempty : {ω | ¬ frobNorm (pinv (X ω)) ^ 2 ≤ t * Fintype.card r / d} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [Subsingleton.elim (pinv (X ω)) 0, frobNorm_zero, hr]
      simp
    rw [hempty, measureReal_empty]
    exact h0
  rcases Nat.eq_zero_or_pos d with hd0 | hd0
  · refine measureReal_le_one.trans ?_
    rw [hd0]
    exact one_le_gaussianPinvFrobTail_zero hr t
  have hset :
      MeasurableSet {G : Matrix r k ℝ | ¬ frobNorm (pinv G) ^ 2 ≤ t * Fintype.card r / d} :=
    (measurableSet_le ((measurable_frobNorm.comp measurable_pinv).pow_const 2)
      measurable_const).compl
  rw [hX.measureReal_eq (p := fun G => ¬ frobNorm (pinv G) ^ 2 ≤ t * Fintype.card r / d) hset]
  refine le_trans (le_of_eq (measureReal_congr ?_)) (gaussianMatrix_real_lt_sum_le hr hd0 hd ht)
  have hrk : Fintype.card r ≤ Fintype.card k := by omega
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix r k))]
    with G hG
  rw [id, min_eq_left hrk] at hG
  have hinj : Function.Injective Gᴴ.mulVec := by
    rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose, hG]
  have he := frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose hinj
  rw [RCLike.re_to_real, Matrix.trace] at he
  change (¬ frobNorm (pinv G) ^ 2 ≤ t * Fintype.card r / d) =
    (t * Fintype.card r / d < ∑ i, (G * Gᴴ)⁻¹ i i)
  rw [he, not_le]
  rfl

/-- **The spectral tail of a Gaussian pseudoinverse**: for an $r \times k$ standard Gaussian
$\mathbf{G}$ with $\lvert r\rvert < \lvert k\rvert$ and
$t > 0$, <!-- value gaussianPinvSpecNormBound {\lvert r\rvert} {\lvert k\rvert} -->
$$\mathbb{P}\Bigl\{\|\mathbf{G}^{+}\|_2 > t\,\frac{e}{\lvert k\rvert - \lvert r\rvert}
\sqrt{(\lvert k\rvert + \lvert r\rvert - 1)/2}\Bigr\} \le
t^{-(\lvert k\rvert - \lvert r\rvert)}\,,$$
the constant being `gaussianPinvSpecNormBound |r| |k|`, by Markov's inequality at the spectral
moment of order $\lvert k\rvert - \lvert r\rvert$
(`NLAlib.integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix`).
HMT's (10.6) has $t^{-(p+1)}$ at $e\sqrt{k+p}/(p+1)$, through the smallest-singular-value density,
not reached by moments [HalkoMartinssonTropp2011, Proposition 10.4]. -/
theorem measureReal_specNorm_pinv_gt_le_of_hasLaw_gaussianMatrix
    {X : Ω → Matrix r k ℝ} (hX : HasLaw X (gaussianMatrix r k) μ)
    (hrk : Fintype.card r < Fintype.card k) {t : ℝ} (ht : 0 < t) :
    μ.real {ω | t * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) <
        specNorm (pinv (X ω))} ≤
      t ^ (-((Fintype.card k : ℝ) - Fintype.card r)) := by
  simp only [← not_le]
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have hq : (0 : ℝ) < (Fintype.card k : ℝ) - Fintype.card r := by
    have : (Fintype.card r : ℝ) < Fintype.card k := by exact_mod_cast hrk
    linarith
  set q : ℝ := (Fintype.card k : ℝ) - Fintype.card r
  set C := gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)
  rcases isEmpty_or_nonempty r with hr | hr
  · have hempty : {ω | ¬ specNorm (pinv (X ω)) ≤ t * C} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
      rw [Subsingleton.elim (pinv (X ω)) 0, specNorm_zero]
      exact mul_nonneg ht.le (gaussianPinvSpecNormBound_nonneg hrk)
    rw [hempty, measureReal_empty]
    positivity
  have hC : 0 < C := by
    have hR : (1 : ℝ) ≤ Fintype.card r := by exact_mod_cast Fintype.card_pos
    have hK : (Fintype.card r : ℝ) + 1 ≤ Fintype.card k := by exact_mod_cast hrk
    simp only [C, gaussianPinvSpecNormBound_def]
    exact mul_pos (div_pos (Real.exp_pos 1) hq) (Real.sqrt_pos.2 (by linarith))
  have hint := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hX hq le_rfl
  have hmom : ∫ ω, specNorm (pinv (X ω)) ^ q ∂μ ≤ C ^ q := by
    have h := integral_specNorm_pinv_rpow_le_of_hasLaw_gaussianMatrix hX hq le_rfl
    rwa [← gaussianPinvSpecNormBound_def] at h
  have hsub : {ω | ¬ specNorm (pinv (X ω)) ≤ t * C} ⊆
      {ω | (t * C) ^ q ≤ specNorm (pinv (X ω)) ^ q} := by
    intro ω (hω : ¬ specNorm (pinv (X ω)) ≤ t * C)
    exact Real.rpow_le_rpow (by positivity) (not_le.1 hω).le hq.le
  refine (measureReal_mono hsub).trans ((measureReal_ge_le_integral_div
    (ae_of_all _ fun ω => Real.rpow_nonneg (specNorm_nonneg _) q) hint
    (Real.rpow_pos_of_pos (by positivity) q)).trans ?_)
  refine (div_le_div_of_nonneg_right hmom (by positivity)).trans (le_of_eq ?_)
  rw [Real.mul_rpow ht.le hC.le, Real.rpow_neg ht.le]
  have : 0 < C ^ q := Real.rpow_pos_of_pos hC q
  have : 0 < t ^ q := Real.rpow_pos_of_pos ht q
  field_simp

/-! ### The block tails -/

section Block

variable [DecidableEq r] [DecidableEq s] {X : Ω → Matrix n k ℝ} {V₁ : Matrix n r ℝ}
  {V₂ : Matrix n s ℝ}

omit [Fintype a] in
/-- The common skeleton of the spectral and Frobenius block tails: outside the two bad events of
$\mathbf{T} = \mathbf{G}_1^{+}$ (spectral and Frobenius tails) and the concentration event of
$f(\mathbf{T}, \mathbf{G}_2)$ about $c(\mathbf{T})$ with deviation $L(\mathbf{T})u$, the
statistic is at most any $b$ that dominates $c + Lu$ on the good event. -/
private theorem measureReal_block_le_of_good (hX : HasLaw X (gaussianMatrix n k) μ)
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (hrk : Fintype.card r < Fintype.card k)
    {f : Matrix k r ℝ → Matrix s k ℝ → ℝ} (hf : Measurable (Function.uncurry f))
    {L c : Matrix k r ℝ → ℝ} (hL : Measurable L) (hL0 : ∀ T, 0 ≤ L T) (hc : Measurable c)
    (hlip : ∀ T A B, |f T A - f T B| ≤ L T * frobNorm (A - B))
    (hmean : ∀ T, ∫ A, f T A ∂(gaussianMatrix s k) ≤ c T) {u t b : ℝ} (hu : 0 ≤ u)
    (ht : 0 < t)
    (hgood : ∀ T : Matrix k r ℝ,
      specNorm T ≤ t * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) →
      frobNorm T ^ 2 ≤ t ^ 2 * Fintype.card r / d → c T + L T * u ≤ b) :
    μ.real {ω | ¬ f (pinv (V₁ᴴ * X ω)) (V₂ᴴ * X ω) ≤ b} ≤
      t ^ (-((Fintype.card k : ℝ) - Fintype.card r)) +
        gaussianPinvFrobTail (Fintype.card r) d (t ^ 2) + Real.exp (-u ^ 2 / 2) := by
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have hG₁ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
  have hG₂ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂
  set A₁ := {ω | ¬ specNorm (pinv (V₁ᴴ * X ω)) ≤
    t * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)}
  set A₂ := {ω | ¬ frobNorm (pinv (V₁ᴴ * X ω)) ^ 2 ≤ t ^ 2 * Fintype.card r / d}
  set B := {ω | ¬ f (pinv (V₁ᴴ * X ω)) (V₂ᴴ * X ω) ≤
    c (pinv (V₁ᴴ * X ω)) + L (pinv (V₁ᴴ * X ω)) * u}
  have hsub : {ω | ¬ f (pinv (V₁ᴴ * X ω)) (V₂ᴴ * X ω) ≤ b} ⊆ A₁ ∪ A₂ ∪ B := by
    intro ω hω
    by_contra hn
    simp only [A₁, A₂, B, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn hω
    exact hω (hn.2.trans (hgood _ hn.1.1 hn.1.2))
  have h₁ := measureReal_specNorm_pinv_gt_le_of_hasLaw_gaussianMatrix hG₁ hrk ht
  have h₂ := measureReal_frobNorm_pinv_sq_gt_le_of_hasLaw_gaussianMatrix hG₁ hd
    (pow_pos ht 2)
  have h₃ := measureReal_gt_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun hG₂
    (measurable_pinv.comp_aemeasurable hG₁.aemeasurable)
    ((indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂).comp measurable_pinv
      measurable_id) hf hL hL0 hc hlip hmean hu
  simp only [← not_le] at h₁ h₂ h₃
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  exact add_le_add ((measureReal_union_le _ _).trans (add_le_add h₁ h₂)) h₃

/-- **The range finder's block tail** [TroppWebber2023, Proposition 8.6 (8.9)]: for a standard
Gaussian $n \times k$ matrix $\mathbf{G}$, frames $\mathbf{V}_1$ ($n \times r$) and
$\mathbf{V}_2$ ($n \times s$) with $\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, the blocks
$\mathbf{G}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{G}$, $d = \lvert k\rvert - \lvert r\rvert + 1$, any
$u$ and $t > 0$, <!-- value gaussianPinvFrobTail {\lvert r\rvert} d t -->
$$\mathbb{P}\Bigl\{\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_{\mathsf{F}}^2 >
\frac{ut\lvert r\rvert}{d}\|\mathbf{S}\|_{\mathsf{F}}^2\Bigr\} \le e^{-(u-2)/4} +
\frac{2\sqrt{\lvert r\rvert}\,(d/(2t))^{d/2}}{\Gamma(d/2 + 1)}\,.$$
Conditionally on $\mathbf{T} = \mathbf{G}_1^{+}$, $\mathbf{G} \mapsto
\|\mathbf{S}\mathbf{G}\mathbf{T}\|_{\mathsf{F}}$ is
$\|\mathbf{S}\|_{\mathsf{F}}\|\mathbf{T}\|_{\mathsf{F}}$-Lipschitz with mean at most that constant;
concentration at deviation $\sqrt{u} - 1$ and $e^{-(\sqrt{u}-1)^2/2} \le e^{-(u-2)/4}$, plus the
trace tail `NLAlib.measureReal_frobNorm_pinv_sq_gt_le_of_hasLaw_gaussianMatrix`. The second
failure term, `gaussianPinvFrobTail |r| d t`, is smaller than TW's
$\sqrt{\pi\lvert r\rvert}\,(e/t)^{d/2}$. For $u \le 2$ the bound is at least $1$. -/
theorem measureReal_frobNorm_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix n k) μ) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (S : Matrix a s ℝ) (u : ℝ) {t : ℝ}
    (ht : 0 < t) :
    μ.real {ω | u * t * Fintype.card r / d * frobNorm S ^ 2 <
        frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2} ≤
      Real.exp (-(u - 2) / 4) + gaussianPinvFrobTail (Fintype.card r) d t := by
  simp only [← not_le]
  have : IsProbabilityMeasure μ := hX.isProbabilityMeasure_iff.2 inferInstance
  have h0 := gaussianPinvFrobTail_nonneg (Fintype.card r) d ht
  rcases le_or_gt u 2 with hu | hu
  · refine measureReal_le_one.trans ?_
    have : 1 ≤ Real.exp (-(u - 2) / 4) := Real.one_le_exp (by linarith)
    linarith
  have hG₁ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁
  have hG₂ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₂
  have hsu : 1 ≤ √u := Real.one_le_sqrt.2 (by linarith)
  set A := {ω | ¬ frobNorm (pinv (V₁ᴴ * X ω)) ^ 2 ≤ t * Fintype.card r / d}
  set B := {ω | ¬ frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ≤
    frobNorm S * frobNorm (pinv (V₁ᴴ * X ω)) +
      frobNorm S * frobNorm (pinv (V₁ᴴ * X ω)) * (√u - 1)}
  have hsub : {ω | ¬ frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ^ 2 ≤
      u * t * Fintype.card r / d * frobNorm S ^ 2} ⊆ B ∪ A := by
    intro ω hω
    by_contra hn
    simp only [A, B, Set.mem_union, Set.mem_ofPred_eq, not_or, not_not] at hn hω
    obtain ⟨hB, hA⟩ := hn
    have hB' : frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω)) ≤
        √u * (frobNorm S * frobNorm (pinv (V₁ᴴ * X ω))) := by linarith
    have hsq := pow_le_pow_left₀ (frobNorm_nonneg _) hB' 2
    rw [mul_pow, Real.sq_sqrt (by linarith), mul_pow] at hsq
    refine hω (hsq.trans ?_)
    calc u * (frobNorm S ^ 2 * frobNorm (pinv (V₁ᴴ * X ω)) ^ 2)
        ≤ u * (frobNorm S ^ 2 * (t * Fintype.card r / d)) := by gcongr
      _ = u * t * Fintype.card r / d * frobNorm S ^ 2 := by ring
  have hA := measureReal_frobNorm_pinv_sq_gt_le_of_hasLaw_gaussianMatrix hG₁ hd ht
  have hf : Measurable (Function.uncurry fun (T : Matrix k r ℝ) (M : Matrix s k ℝ) =>
      frobNorm (S * M * T)) :=
    (continuous_frobNorm.comp ((continuous_const.matrix_mul continuous_snd).matrix_mul
      continuous_fst)).measurable
  have hB := measureReal_gt_add_mul_le_of_hasLaw_gaussianMatrix_of_indepFun hG₂
    (measurable_pinv.comp_aemeasurable hG₁.aemeasurable)
    ((indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX hV₁ hV₂ h₁₂).comp measurable_pinv
      measurable_id) hf
    (L := fun T => frobNorm S * frobNorm T) (c := fun T => frobNorm S * frobNorm T)
    (measurable_const.mul measurable_frobNorm) (fun T => by positivity)
    (measurable_const.mul measurable_frobNorm)
    (fun T A B => by
      refine (abs_frobNorm_sub_frobNorm_le _ _).trans ?_
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      calc frobNorm (S * (A - B) * T) ≤ frobNorm (S * (A - B)) * frobNorm T := frobNorm_mul_le _ _
        _ ≤ frobNorm S * frobNorm (A - B) * frobNorm T := by
            gcongr
            exact frobNorm_mul_le _ _
        _ = frobNorm S * frobNorm T * frobNorm (A - B) := by ring)
    (fun T => integral_frobNorm_mul_mul_le_of_hasLaw_gaussianMatrix
      (HasLaw.id (μ := gaussianMatrix s k)) S T)
    (t := √u - 1) (by linarith)
  have hexp : Real.exp (-(√u - 1) ^ 2 / 2) ≤ Real.exp (-(u - 2) / 4) := by
    rw [Real.exp_le_exp]
    have h2 := Real.sq_sqrt (show 0 ≤ u by linarith)
    nlinarith [sq_nonneg (√u - 2)]
  simp only [← not_le] at hA hB
  refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans ?_)
  exact add_le_add (hB.trans hexp) hA

/-- **The spectral block tail**, in the shape of [HalkoMartinssonTropp2011, proof of Theorem 10.8]:
with the hypotheses of
`NLAlib.measureReal_frobNorm_mul_mul_pinv_sq_gt_le_of_hasLaw_gaussianMatrix`, $u \ge 0$ and
$t > 0$, <!-- value gaussianPinvSpecNormBound {\lvert r\rvert} {\lvert k\rvert} -->
$$\begin{aligned}\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_2 \le{}&
t\Bigl(\|\mathbf{S}\|_2\sqrt{\lvert r\rvert/d} + \frac{e}{\lvert k\rvert - \lvert r\rvert}
\sqrt{(\lvert k\rvert + \lvert r\rvert - 1)/2}\,\|\mathbf{S}\|_{\mathsf{F}}\Bigr) \\
&+ ut\,\frac{e}{\lvert k\rvert - \lvert r\rvert}\sqrt{(\lvert k\rvert + \lvert r\rvert - 1)/2}\,
\|\mathbf{S}\|_2\end{aligned}$$
outside probability <!-- value gaussianPinvFrobTail {\lvert r\rvert} d t^2 -->
$$t^{-(\lvert k\rvert - \lvert r\rvert)} +
\frac{2\sqrt{\lvert r\rvert}\,(d/(2t^2))^{d/2}}{\Gamma(d/2 + 1)} + e^{-u^2/2}\,;$$
the constant is `gaussianPinvSpecNormBound |r| |k|`, the second failure term
`gaussianPinvFrobTail |r| d (t ^ 2)`. On the good event of $\mathbf{G}_1^{+}$
(`NLAlib.measureReal_specNorm_pinv_gt_le_of_hasLaw_gaussianMatrix`, and the trace tail at
$t^2$), concentration of the $\|\mathbf{S}\|_2\|\mathbf{G}_1^{+}\|_2$-Lipschitz map about
Chevet's mean bound. Given `hd`, `hrk` is $d \ge 2$. -/
theorem measureReal_specNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix n k) μ) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (hrk : Fintype.card r < Fintype.card k)
    (S : Matrix a s ℝ) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | t * (specNorm S * √((Fintype.card r : ℝ) / d) +
          frobNorm S * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)) +
        u * t * gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) * specNorm S <
        specNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω))} ≤
      t ^ (-((Fintype.card k : ℝ) - Fintype.card r)) +
        gaussianPinvFrobTail (Fintype.card r) d (t ^ 2) + Real.exp (-u ^ 2 / 2) := by
  simp only [← not_le]
  set C := gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k)
  have hf : Measurable (Function.uncurry fun (T : Matrix k r ℝ) (M : Matrix s k ℝ) =>
      specNorm (S * M * T)) :=
    (continuous_specNorm.comp ((continuous_const.matrix_mul continuous_snd).matrix_mul
      continuous_fst)).measurable
  refine measureReal_block_le_of_good hX hV₁ hV₂ h₁₂ hd hrk hf
    (L := fun T => specNorm S * specNorm T)
    (c := fun T => specNorm S * frobNorm T + frobNorm S * specNorm T)
    (measurable_const.mul measurable_specNorm) (fun T => by positivity)
    ((measurable_const.mul measurable_frobNorm).add (measurable_const.mul measurable_specNorm))
    (fun T A B => ?_) (fun T => integral_specNorm_mul_mul_le_of_hasLaw_gaussianMatrix
      (HasLaw.id (μ := gaussianMatrix s k)) S T) hu ht (fun T hT₁ hT₂ => ?_)
  · refine (abs_specNorm_sub_specNorm_le _ _).trans ?_
    rw [← Matrix.sub_mul, ← Matrix.mul_sub]
    calc specNorm (S * (A - B) * T) ≤ specNorm (S * (A - B)) * specNorm T := specNorm_mul_le _ _
      _ ≤ specNorm S * frobNorm (A - B) * specNorm T := by
          gcongr
          exact (specNorm_mul_le _ _).trans (by gcongr; exact specNorm_le_frobNorm _)
      _ = specNorm S * specNorm T * frobNorm (A - B) := by ring
  · have hF : frobNorm T ≤ t * √((Fintype.card r : ℝ) / d) := by
      rw [← Real.sqrt_sq (frobNorm_nonneg T), ← Real.sqrt_sq ht.le, ← Real.sqrt_mul (sq_nonneg t)]
      exact Real.sqrt_le_sqrt (by rw [mul_div_assoc] at hT₂; exact hT₂)
    have h1 := mul_le_mul_of_nonneg_left hF (specNorm_nonneg S)
    have h2 := mul_le_mul_of_nonneg_left hT₁ (frobNorm_nonneg S)
    have h3 := mul_le_mul_of_nonneg_left hT₁ (mul_nonneg (specNorm_nonneg S) hu)
    nlinarith

/-- **The Frobenius block tail**, in the shape of [HalkoMartinssonTropp2011, proof of
Theorem 10.7]: with the hypotheses of
`NLAlib.measureReal_specNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix`, the block
satisfies <!-- value gaussianPinvSpecNormBound {\lvert r\rvert} {\lvert k\rvert} -->
$$\|\mathbf{S}\mathbf{G}_2\mathbf{G}_1^{+}\|_{\mathsf{F}} \le t\sqrt{\lvert r\rvert/d}\,
\|\mathbf{S}\|_{\mathsf{F}} + ut\,\frac{e}{\lvert k\rvert - \lvert r\rvert}
\sqrt{(\lvert k\rvert + \lvert r\rvert - 1)/2}\,\|\mathbf{S}\|_2$$
outside probability <!-- value gaussianPinvFrobTail {\lvert r\rvert} d t^2 -->
$$t^{-(\lvert k\rvert - \lvert r\rvert)} +
\frac{2\sqrt{\lvert r\rvert}\,(d/(2t^2))^{d/2}}{\Gamma(d/2 + 1)} + e^{-u^2/2}\,;$$
the constant is `gaussianPinvSpecNormBound |r| |k|`, the second failure term
`gaussianPinvFrobTail |r| d (t ^ 2)`. The proof: concentration of the
$\|\mathbf{S}\|_2\|\mathbf{G}_1^{+}\|_2$-Lipschitz map about the Frobenius mean
`NLAlib.integral_frobNorm_mul_mul_le_of_hasLaw_gaussianMatrix`. Given `hd`, `hrk` is $d \ge 2$. -/
theorem measureReal_frobNorm_mul_mul_pinv_gt_le_of_hasLaw_gaussianMatrix
    (hX : HasLaw X (gaussianMatrix n k) μ) (hV₁ : HasOrthonormalCols V₁)
    (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0) {d : ℕ}
    (hd : Fintype.card r + d = Fintype.card k + 1) (hrk : Fintype.card r < Fintype.card k)
    (S : Matrix a s ℝ) {u t : ℝ} (hu : 0 ≤ u) (ht : 0 < t) :
    μ.real {ω | t * √((Fintype.card r : ℝ) / d) * frobNorm S + u * t *
        gaussianPinvSpecNormBound (Fintype.card r) (Fintype.card k) * specNorm S <
        frobNorm (S * (V₂ᴴ * X ω) * pinv (V₁ᴴ * X ω))} ≤
      t ^ (-((Fintype.card k : ℝ) - Fintype.card r)) +
        gaussianPinvFrobTail (Fintype.card r) d (t ^ 2) + Real.exp (-u ^ 2 / 2) := by
  simp only [← not_le]
  have hf : Measurable (Function.uncurry fun (T : Matrix k r ℝ) (M : Matrix s k ℝ) =>
      frobNorm (S * M * T)) :=
    (continuous_frobNorm.comp ((continuous_const.matrix_mul continuous_snd).matrix_mul
      continuous_fst)).measurable
  refine measureReal_block_le_of_good hX hV₁ hV₂ h₁₂ hd hrk hf
    (L := fun T => specNorm S * specNorm T) (c := fun T => frobNorm S * frobNorm T)
    (measurable_const.mul measurable_specNorm) (fun T => by positivity)
    (measurable_const.mul measurable_frobNorm)
    (fun T A B => ?_) (fun T => integral_frobNorm_mul_mul_le_of_hasLaw_gaussianMatrix
      (HasLaw.id (μ := gaussianMatrix s k)) S T) hu ht (fun T hT₁ hT₂ => ?_)
  · refine (abs_frobNorm_sub_frobNorm_le _ _).trans ?_
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, Matrix.mul_assoc]
    calc frobNorm (S * ((A - B) * T)) ≤ specNorm S * frobNorm ((A - B) * T) :=
          frobNorm_mul_le_specNorm_mul_frobNorm _ _
      _ ≤ specNorm S * (frobNorm (A - B) * specNorm T) := by
          gcongr
          exact frobNorm_mul_le_frobNorm_mul_specNorm _ _
      _ = specNorm S * specNorm T * frobNorm (A - B) := by ring
  · have hF : frobNorm T ≤ t * √((Fintype.card r : ℝ) / d) := by
      rw [← Real.sqrt_sq (frobNorm_nonneg T), ← Real.sqrt_sq ht.le, ← Real.sqrt_mul (sq_nonneg t)]
      exact Real.sqrt_le_sqrt (by rw [mul_div_assoc] at hT₂; exact hT₂)
    have h1 := mul_le_mul_of_nonneg_left hF (frobNorm_nonneg S)
    have h3 := mul_le_mul_of_nonneg_left hT₁ (mul_nonneg (specNorm_nonneg S) hu)
    nlinarith

end Block

end NLAlib
