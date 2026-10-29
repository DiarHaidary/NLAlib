/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Gamma
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Gamma.Basic
public import NLAlib.ForMathlib.Probability.Distributions.ChiSquared
public import NLAlib.Probability.Distributions.Gaussian

/-!
# Real moments of the chi-square law

For a standard Gaussian vector $\mathbf{g}$ in $\mathbb{R}^n$ (with $d = \lvert n \rvert$),
$\|\mathbf{g}\|^2$ has the $\chi^2_d$ law, and
$\mathbb{E}(\|\mathbf{g}\|^2)^s = 2^s \Gamma(d/2 + s) / \Gamma(d/2)$ for every real $s > -d/2$, the
integrability threshold. The negative moments are what the inverse moments of Gaussian matrices
rest on; in particular $\mathbb{E}[1 / \|\mathbf{g}\|^2] = 1 / (d - 2)$ for $d \ge 3$. At
$\mathbf{g} = \mathbf{0}$ (probability zero) $0^s$ is Lean's junk value for $s < 0$; the integrals
are unaffected. The case $s = 1/2$ gives $\mathbb{E}\|\mathbf{g}\|$, whose growth in the
dimension ($\sqrt{m} - \sqrt{n} \le \mathbb{E}\|\mathbf{g}_m\| - \mathbb{E}\|\mathbf{g}_n\|$ for
standard Gaussian vectors $\mathbf{g}_k$ of dimension $k$) is the step of Gordon's lower bound for
the smallest singular value of a Gaussian matrix.

## Main results

* `NLAlib.integral_norm_sq_rpow_of_hasLaw_gaussianVector`.
* `NLAlib.integral_comp_norm_of_hasLaw_gaussianVector`: polar coordinates, the $\chi_d$ density.
* `NLAlib.integral_norm_sq_inv_of_hasLaw_gaussianVector`.
* `NLAlib.integral_norm_sq_rpow_lt_of_five_le_card_of_hasLaw_gaussianVector`: the strict
  uniform inverse-moment bound from HMT, including positive exponents below two.
* `NLAlib.integral_norm_sq_rpow_le_of_hasLaw_gaussianVector`: a uniform inverse-moment bound
  in all admissible dimensions, with `chiSquareInverseMomentFactor` currently
  equal to <!-- value chiSquareInverseMomentFactor -->$4$.
* `NLAlib.le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector`:
  $\sqrt{m} - \sqrt{n} \le \mathbb{E}\|\mathbf{g}_m\| - \mathbb{E}\|\mathbf{g}_n\|$ for
  $1 \le n \le m$.
* `NLAlib.integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector`,
  `NLAlib.integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector`: for independent
  $\mathbf{g}, \mathbf{h}$ and $X = \|\mathbf{g}\|^2 - \|\mathbf{h}\|^2$, $\mathbb{E}X^2 = 4d$
  and $\mathbb{E}X^4 = 48d^2 + 96d$ (the Paley–Zygmund step of the early-truncation lower bound).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real Set

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n : Type*} [Fintype n]
  {g : Ω → n → ℝ}

/-- The radial integral
$\int_0^\infty y^{d-1} e^{-y^2/2} (y^2)^s \, dy = 2^{d/2 + s} \Gamma(d/2 + s) / 2$ for $d \ge 1$
and $s > -d/2$. -/
private theorem integral_pow_mul_exp_mul_rpow {d : ℕ} (hd : 1 ≤ d) {s : ℝ}
    (hs : -((d : ℝ) / 2) < s) :
    ∫ y in Ioi (0 : ℝ), y ^ (d - 1) * (rexp (-y ^ 2 / 2) * (y ^ 2) ^ s) =
      2 ^ ((d : ℝ) / 2 + s) * (1 / 2) * Real.Gamma ((d : ℝ) / 2 + s) := by
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by rw [Nat.cast_sub hd, Nat.cast_one]
  have h := integral_rpow_mul_exp_neg_sq_div_two (q := (d : ℝ) - 1 + 2 * s) (by linarith)
  rw [show ((d : ℝ) - 1 + 2 * s + 1) / 2 = (d : ℝ) / 2 + s by ring] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi fun y (hy : 0 < y) => ?_
  rw [← Real.rpow_natCast, hcast, ← Real.rpow_two, ← Real.rpow_mul hy.le, mul_left_comm,
    ← Real.rpow_add hy]
  ring_nf

/-- The real moments of $\chi^2_d$ under the law itself. -/
private theorem integral_norm_sq_rpow_gaussianVector {s : ℝ}
    (hs : -((Fintype.card n : ℝ) / 2) < s) :
    ∫ x, (‖WithLp.toLp 2 x‖ ^ 2) ^ s ∂(gaussianVector n) =
      2 ^ s * Real.Gamma ((Fintype.card n : ℝ) / 2 + s) /
        Real.Gamma ((Fintype.card n : ℝ) / 2) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hs0 : 0 < s := by simpa [Fintype.card_eq_zero] using hs
    simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, zero_div, Real.Gamma_zero, div_zero]
    have h0 (x : n → ℝ) : (‖WithLp.toLp 2 x‖ ^ 2) ^ s = 0 := by
      rw [Subsingleton.elim (WithLp.toLp 2 x) 0, norm_zero, zero_pow two_ne_zero,
        Real.zero_rpow hs0.ne']
    simp only [h0, integral_zero]
  have h := integral_comp_norm_pi_gaussianReal (ι := n) fun y => (y ^ 2) ^ s
  set d := Fintype.card n with hd_def
  have hd : 1 ≤ d := Fintype.card_pos
  rw [h, integral_pow_mul_exp_mul_rpow hd hs, Real.rpow_add (by norm_num),
    Real.rpow_sub (by norm_num), Real.rpow_one]
  have hG : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by positivity)
  field_simp

/-- Polar coordinates for a standard Gaussian vector, the $\chi_d$ density: for a standard
Gaussian vector $\mathbf{g}$ of dimension $d = \lvert n \rvert \ge 1$ and measurable $\varphi$,
$$\mathbb{E}\,\varphi(\|\mathbf{g}\|) = \frac{1}{2^{d/2 - 1}\,\Gamma(d/2)}
\int_0^\infty y^{d-1} e^{-y^2/2} \varphi(y)\,dy\,.$$
Both sides are Bochner integrals, so the identity also holds (as $0 = 0$) when either side is not
integrable. This is the density-level fact behind the exact small ball of $\chi^2$
(`NLAlib.measureReal_norm_sq_le_le_rpow_div_Gamma_of_hasLaw_gaussianVector`). -/
theorem integral_comp_norm_of_hasLaw_gaussianVector (hg : HasLaw g (gaussianVector n) μ)
    (hn : 0 < Fintype.card n) {φ : ℝ → ℝ} (hφ : Measurable φ) :
    ∫ ω, φ ‖WithLp.toLp 2 (g ω)‖ ∂μ =
      (∫ y in Ioi (0 : ℝ), y ^ (Fintype.card n - 1) * (rexp (-y ^ 2 / 2) * φ y)) /
        (2 ^ ((Fintype.card n : ℝ) / 2 - 1) * Real.Gamma ((Fintype.card n : ℝ) / 2)) := by
  have : Nonempty n := Fintype.card_pos_iff.mp hn
  have hf : Measurable fun x : n → ℝ => φ ‖WithLp.toLp 2 x‖ := hφ.comp (by fun_prop)
  rw [show (∫ ω, φ ‖WithLp.toLp 2 (g ω)‖ ∂μ) = ∫ x, φ ‖WithLp.toLp 2 x‖ ∂(gaussianVector n) from
    hg.integral_comp hf.aestronglyMeasurable]
  exact integral_comp_norm_pi_gaussianReal φ

/-- $(\|\mathbf{g}\|^2)^s$ is integrable for a standard Gaussian vector $\mathbf{g}$ when
$s > -d/2$, with $d = \lvert n \rvert$ (the range is sharp; only this direction is stated). -/
theorem integrable_norm_sq_rpow_of_hasLaw_gaussianVector (hg : HasLaw g (gaussianVector n) μ)
    {s : ℝ} (hs : -((Fintype.card n : ℝ) / 2) < s) :
    Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ s) μ := by
  have hf : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ s := by fun_prop
  refine (integrable_map_measure hf.aestronglyMeasurable hg.aemeasurable).1 ?_
  rw [hg.map_eq]
  rcases isEmpty_or_nonempty n with hn | hn
  · have hs0 : 0 < s := by simpa [Fintype.card_eq_zero] using hs
    have h0 : (fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ s) = fun _ => 0 := by
      funext x
      rw [Subsingleton.elim (WithLp.toLp 2 x) 0, norm_zero, zero_pow two_ne_zero,
        Real.zero_rpow hs0.ne']
    rw [h0]
    exact integrable_zero _ _ _
  refine Integrable.of_integral_ne_zero ?_
  rw [integral_norm_sq_rpow_gaussianVector hs]
  have h1 : 0 < Real.Gamma ((Fintype.card n : ℝ) / 2 + s) :=
    Real.Gamma_pos_of_pos (by linarith)
  have h2 : 0 < Real.Gamma ((Fintype.card n : ℝ) / 2) :=
    Real.Gamma_pos_of_pos (by have : 0 < Fintype.card n := Fintype.card_pos; positivity)
  positivity

/-- The real moments of $\chi^2_d$: for a standard Gaussian vector $\mathbf{g}$ of dimension
$d = \lvert n \rvert$ and real $s > -d/2$,
$$\mathbb{E}(\|\mathbf{g}\|^2)^s = \frac{2^s \Gamma(d/2 + s)}{\Gamma(d/2)}\,.$$ -/
theorem integral_norm_sq_rpow_of_hasLaw_gaussianVector (hg : HasLaw g (gaussianVector n) μ)
    {s : ℝ} (hs : -((Fintype.card n : ℝ) / 2) < s) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ s ∂μ =
      2 ^ s * Real.Gamma ((Fintype.card n : ℝ) / 2 + s) /
        Real.Gamma ((Fintype.card n : ℝ) / 2) := by
  rw [← integral_norm_sq_rpow_gaussianVector hs]
  have hf : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ s := by fun_prop
  exact hg.integral_comp hf.aestronglyMeasurable

/-- $\mathbb{E}[1 / \|\mathbf{g}\|^2] = 1 / (d - 2)$ for a standard Gaussian vector $\mathbf{g}$
of dimension $d = \lvert n \rvert \ge 3$. -/
theorem integral_norm_sq_inv_of_hasLaw_gaussianVector (hg : HasLaw g (gaussianVector n) μ)
    (hn : 3 ≤ Fintype.card n) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2)⁻¹ ∂μ = 1 / ((Fintype.card n : ℝ) - 2) := by
  have hd : (3 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
  simp only [← Real.rpow_neg_one]
  rw [integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (by linarith),
    show (Fintype.card n : ℝ) / 2 = ((Fintype.card n : ℝ) / 2 + -1) + 1 by ring,
    Real.Gamma_add_one (by linarith), add_neg_cancel_right, Real.rpow_neg_one]
  have hG : 0 < Real.Gamma ((Fintype.card n : ℝ) / 2 + -1) := Real.Gamma_pos_of_pos (by linarith)
  have hb : (Fintype.card n : ℝ) - 2 ≠ 0 := by linarith
  rw [mul_div_assoc, mul_comm ((Fintype.card n : ℝ) / 2 + -1), ← div_div, div_self hG.ne',
    show (Fintype.card n : ℝ) / 2 + -1 = ((Fintype.card n : ℝ) - 2) / 2 by ring]
  field_simp

/-! ### Uniform inverse moments -/

/-- The absolute factor in the uniform inverse chi-square moment bound in all admissible
dimensions. Its value is <!-- value chiSquareInverseMomentFactor -->$4$; dimension at least
five admits the stronger factor three from [HalkoMartinssonTropp2011, Lemma A.10]. -/
noncomputable irreducible_def chiSquareInverseMomentFactor : ℝ := 4

/-- The uniform inverse chi-square moment factor is positive. -/
theorem chiSquareInverseMomentFactor_pos : 0 < chiSquareInverseMomentFactor := by
  rw [chiSquareInverseMomentFactor_def]
  norm_num

/-- The uniform inverse chi-square moment factor is at most four; its current value
is <!-- value chiSquareInverseMomentFactor -->$4$. -/
theorem chiSquareInverseMomentFactor_le_four : chiSquareInverseMomentFactor ≤ 4 := by
  rw [chiSquareInverseMomentFactor_def]

/-- The exact negative moment, written with a positive power in the denominator. -/
private theorem integral_norm_sq_rpow_neg_eq (hg : HasLaw g (gaussianVector n) μ)
    {q : ℝ} (hqd : q < (Fintype.card n : ℝ) / 2) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ =
      Gamma ((Fintype.card n : ℝ) / 2 - q) /
        (2 ^ q * Gamma ((Fintype.card n : ℝ) / 2)) := by
  rw [integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (by linarith),
    rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [sub_eq_add_neg, div_eq_mul_inv, mul_inv_rev]
  ring

/-- Probability-space moment comparison, specialized to the reciprocal Gaussian squared norm. -/
private theorem integral_norm_sq_rpow_neg_root_mono (hg : HasLaw g (gaussianVector n) μ)
    {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (hqd : q < (Fintype.card n : ℝ) / 2) :
    (∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-p) ∂μ) ^ p⁻¹ ≤
      (∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ) ^ q⁻¹ := by
  have := hg.isProbabilityMeasure
  let f : Ω → ℝ := fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2)⁻¹
  have hf : AEStronglyMeasurable f μ :=
    ((by fun_prop : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2)⁻¹).comp_aemeasurable
      hg.aemeasurable).aestronglyMeasurable
  have he (ω : Ω) (t : ℝ) : ‖f ω‖ ^ t = (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-t) := by
    dsimp [f]
    rw [abs_of_nonneg (by positivity), ← rpow_neg_eq_inv_rpow]
  have hq : 0 < q := hp.trans_le hpq
  have hMp : MemLp f (ENNReal.ofReal p) μ :=
    (integrable_norm_rpow_iff hf (by simp [hp]) (by simp)).1 (by
      simpa only [ENNReal.toReal_ofReal hp.le, he] using
        integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := -p) (by linarith))
  have hMq : MemLp f (ENNReal.ofReal q) μ :=
    (integrable_norm_rpow_iff hf (by simp [hq]) (by simp)).1 (by
      simpa only [ENNReal.toReal_ofReal hq.le, he] using
        integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := -q) (by linarith))
  have hmono := eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.ofReal_le_ofReal hpq) hf (μ := μ)
  rw [hMp.eLpNorm_eq_integral_rpow_norm (by simp [hp]) (by simp),
    hMq.eLpNorm_eq_integral_rpow_norm (by simp [hq]) (by simp)] at hmono
  simp only [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le, he] at hmono
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmono

/-- For a standard Gaussian vector of dimension $d\ge5$ and $0<q\le(d-1)/2$,
$\mathbb{E}\|\mathbf{g}\|^{-2q} < (3/d)^q$.
Integrability is `integrable_norm_sq_rpow_of_hasLaw_gaussianVector` with exponent $-q$.
[HalkoMartinssonTropp2011, Lemma A.10] states the rooted bound for $2\le q\le(d-1)/2$;
probability-space moment comparison extends its endpoint to every positive $q$ in this range.
Port of `NLAlib.integral_rpow_inv_sum_sq_gaussianVector_root_le_three_div` and the strict
endpoint `NLAlib.integral_rpow_inv_sum_sq_gaussianVector_lt`. -/
theorem integral_norm_sq_rpow_lt_of_five_le_card_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hn : 5 ≤ Fintype.card n)
    {q : ℝ} (hq : 0 < q) (hqd : 2 * q + 1 ≤ (Fintype.card n : ℝ)) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ <
      (3 / (Fintype.card n : ℝ)) ^ q := by
  have hd : (5 : ℝ) ≤ Fintype.card n := by exact_mod_cast hn
  let r : ℝ := ((Fintype.card n : ℝ) - 1) / 2
  have hr : 0 < r := by dsimp [r]; linarith
  have hend : ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-r) ∂μ <
      (3 / (Fintype.card n : ℝ)) ^ r := by
    rw [integral_norm_sq_rpow_neg_eq hg (by dsimp [r]; linarith),
      show (Fintype.card n : ℝ) / 2 - r = 1 / 2 by dsimp [r]; ring, Gamma_one_half_eq]
    exact sqrt_pi_div_rpow_mul_Gamma_lt_rpow hn
  have hmono := integral_norm_sq_rpow_neg_root_mono hg hq (q := r)
    (by dsimp [r]; linarith) (by dsimp [r]; linarith)
  have hroot : (∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ) ^ q⁻¹ <
      3 / (Fintype.card n : ℝ) := by
    refine hmono.trans_lt ?_
    have h := rpow_lt_rpow (by positivity) hend (by positivity : 0 < r⁻¹)
    rwa [rpow_rpow_inv (by positivity) hr.ne'] at h
  have h := rpow_lt_rpow (by positivity) hroot hq
  rwa [rpow_inv_rpow (by positivity) hq.ne'] at h

/-- The two-dimensional endpoint, after taking the square. -/
private theorem integral_norm_sq_rpow_neg_half_sq_le_two
    (hg : HasLaw g (gaussianVector n) μ) (hn : Fintype.card n = 2) :
    (∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-(1 / 2 : ℝ)) ∂μ) ^ 2 ≤ 2 := by
  rw [integral_norm_sq_rpow_neg_eq hg (by norm_num [hn]), hn]
  norm_num [Gamma_one_half_eq, Gamma_one, ← sqrt_eq_rpow]
  have hs := sq_sqrt pi_nonneg
  have ht := sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hp := pi_le_four
  rw [div_pow]
  exact (div_le_iff₀ (by positivity : 0 < sqrt 2 ^ 2)).mpr (by nlinarith)

/-- The four-dimensional endpoint is at most one. -/
private theorem integral_norm_sq_rpow_neg_three_halves_le_one
    (hg : HasLaw g (gaussianVector n) μ) (hn : Fintype.card n = 4) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-(3 / 2 : ℝ)) ∂μ ≤ 1 := by
  rw [integral_norm_sq_rpow_neg_eq hg (by norm_num [hn]), hn]
  norm_num [Gamma_one_half_eq, Gamma_two]
  have hs : sqrt π ≤ 2 := by nlinarith [sq_sqrt pi_nonneg, sqrt_nonneg π, pi_le_four]
  have ht : (2 : ℝ) ≤ 2 ^ (3 / 2 : ℝ) := by
    simpa using rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1 : ℝ) ≤ 3 / 2)
  exact (div_le_one (by positivity : (0 : ℝ) < 2 ^ (3 / 2 : ℝ))).mpr (hs.trans ht)

/-- The small-dimension cases of the rooted inverse-moment bound. -/
private theorem integral_norm_sq_rpow_neg_root_le_four_div_of_card_lt_five
    (hg : HasLaw g (gaussianVector n) μ) (hn : Fintype.card n < 5)
    {q : ℝ} (hq : 0 < q) (hqd : 2 * q + 1 ≤ (Fintype.card n : ℝ)) :
    (∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ) ^ q⁻¹ ≤
      4 / (Fintype.card n : ℝ) := by
  have hd2 : 2 ≤ Fintype.card n := by
    have : (1 : ℝ) < Fintype.card n := by linarith
    have : 1 < Fintype.card n := by exact_mod_cast this
    omega
  have hcases : Fintype.card n = 2 ∨ Fintype.card n = 3 ∨ Fintype.card n = 4 := by omega
  rcases hcases with hd | hd | hd
  · have h := integral_norm_sq_rpow_neg_root_mono hg hq (q := 1 / 2)
      (by norm_num [hd] at hqd ⊢; linarith) (by norm_num [hd])
    have hb := integral_norm_sq_rpow_neg_half_sq_le_two hg hd
    norm_num [hd] at h ⊢
    exact h.trans hb
  · have h := integral_norm_sq_rpow_neg_root_mono hg hq (q := 1)
      (by norm_num [hd] at hqd ⊢; linarith) (by norm_num [hd])
    have he := integral_norm_sq_inv_of_hasLaw_gaussianVector hg (by omega)
    norm_num [hd, rpow_neg_one] at he h ⊢
    rw [he] at h
    exact h.trans (by norm_num)
  · have h := integral_norm_sq_rpow_neg_root_mono hg hq (q := 3 / 2)
      (by norm_num [hd] at hqd ⊢; linarith) (by norm_num [hd])
    have hb := rpow_le_one (by positivity)
      (integral_norm_sq_rpow_neg_three_halves_le_one hg hd)
      (by norm_num : 0 ≤ (3 / 2 : ℝ)⁻¹)
    exact h.trans (by simpa [hd] using hb)

/-- For a standard Gaussian vector of dimension $d$ and $0\le q\le(d-1)/2$,
we have <!-- value chiSquareInverseMomentFactor -->$\mathbb{E}\|\mathbf{g}\|^{-2q} \le (4/d)^q$.
The Lean bound uses `chiSquareInverseMomentFactor`. Integrability is
`integrable_norm_sq_rpow_of_hasLaw_gaussianVector` with exponent $-q$.
This extends the dimension-at-least-five estimate of [HalkoMartinssonTropp2011, Lemma A.10]
to dimensions two, three, and four using the exact Gamma formula; exponent zero is immediate.
Port of `NLAlib.integral_rpow_inv_sum_sq_gaussianVector_root_le_four_div` and
`NLAlib.integral_rpow_inv_sum_sq_root_le_four_div_of_hasLaw`. -/
theorem integral_norm_sq_rpow_le_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ)
    {q : ℝ} (hq : 0 ≤ q) (hqd : 2 * q + 1 ≤ (Fintype.card n : ℝ)) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (-q) ∂μ ≤
      (chiSquareInverseMomentFactor / (Fintype.card n : ℝ)) ^ q := by
  have := hg.isProbabilityMeasure
  rcases eq_or_lt_of_le hq with rfl | hq
  · simp
  rw [chiSquareInverseMomentFactor_def]
  by_cases hn : 5 ≤ Fintype.card n
  · exact (integral_norm_sq_rpow_lt_of_five_le_card_of_hasLaw_gaussianVector hg hn hq hqd).le.trans
      (rpow_le_rpow (by positivity) (by gcongr; norm_num) hq.le)
  have hroot := integral_norm_sq_rpow_neg_root_le_four_div_of_card_lt_five hg
    (by omega) hq hqd
  have h := rpow_le_rpow (by positivity) hroot hq.le
  rwa [rpow_inv_rpow (by positivity) hq.ne'] at h

/-! ### The growth of $\mathbb{E}\|\mathbf{g}_d\|$ -/

/-- The expected norm of a standard Gaussian vector in dimension $d$:
$a_d = \sqrt{2}\, \Gamma(d/2 + 1/2) / \Gamma(d/2)$. -/
private noncomputable def gaussNormMean (d : ℕ) : ℝ :=
  √2 * Real.Gamma ((d : ℝ) / 2 + 1 / 2) / Real.Gamma ((d : ℝ) / 2)

private theorem integral_norm_eq_gaussNormMean (hg : HasLaw g (gaussianVector n) μ) :
    ∫ ω, ‖WithLp.toLp 2 (g ω)‖ ∂μ = gaussNormMean (Fintype.card n) := by
  have h := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg (s := 1 / 2)
    (by have := (Nat.cast_nonneg (Fintype.card n) : (0 : ℝ) ≤ _); linarith)
  have e (ω : Ω) : (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ (1 / 2 : ℝ) = ‖WithLp.toLp 2 (g ω)‖ := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_sq (norm_nonneg _)]
  simp only [e] at h
  rw [h, gaussNormMean, ← Real.sqrt_eq_rpow]

private theorem gaussNormMean_pos {d : ℕ} (hd : 1 ≤ d) : 0 < gaussNormMean d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 + 1 / 2 by positivity)
  have h2 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  unfold gaussNormMean
  positivity

private theorem gaussNormMean_mul_succ {d : ℕ} (hd : 1 ≤ d) :
    gaussNormMean d * gaussNormMean (d + 1) = d := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have h1 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 + 1 / 2 by positivity)
  have h2 := Real.Gamma_pos_of_pos (show 0 < (d : ℝ) / 2 by positivity)
  unfold gaussNormMean
  rw [Nat.cast_succ, show ((d : ℝ) + 1) / 2 = (d : ℝ) / 2 + 1 / 2 by ring,
    show (d : ℝ) / 2 + 1 / 2 + 1 / 2 = (d : ℝ) / 2 + 1 by ring,
    Real.Gamma_add_one (show (d : ℝ) / 2 ≠ 0 by positivity)]
  have hs : √2 * √2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [show √2 * Real.Gamma ((d : ℝ) / 2 + 1 / 2) / Real.Gamma ((d : ℝ) / 2) *
      (√2 * ((d : ℝ) / 2 * Real.Gamma ((d : ℝ) / 2)) / Real.Gamma ((d : ℝ) / 2 + 1 / 2)) =
      (√2 * √2) * (d / 2) by field_simp, hs]
  ring

/-- $a_d^2 \le d$, by Jensen (`IsIsotropic.integral_norm_mulVec_le` with
$\mathbf{A} = \mathbf{I}$). -/
private theorem gaussNormMean_sq_le (d : ℕ) : gaussNormMean d ^ 2 ≤ d := by
  have hg : HasLaw (id : (Fin d → ℝ) → Fin d → ℝ) (gaussianVector (Fin d))
      (gaussianVector (Fin d)) := HasLaw.id
  have h := (isIsotropic_of_hasLaw_gaussianVector hg).integral_norm_mulVec_le
    (1 : Matrix (Fin d) (Fin d) ℝ)
  have h0 : 0 ≤ ∫ x, ‖WithLp.toLp 2 (id x : Fin d → ℝ)‖ ∂(gaussianVector (Fin d)) :=
    integral_nonneg fun _ => norm_nonneg _
  simp only [Matrix.one_mulVec] at h
  rw [integral_norm_eq_gaussNormMean hg, Fintype.card_fin] at h h0
  calc gaussNormMean d ^ 2 ≤ frobNorm (1 : Matrix (Fin d) (Fin d) ℝ) ^ 2 :=
        pow_le_pow_left₀ h0 h 2
    _ = d := by rw [frobNorm_one_sq, Fintype.card_fin]

/-! ### The sequence argument -/
/-- Comparison sequence $B_m = m - 1/2 + 3/(20 m)$. -/
private noncomputable def enB (m : ℝ) : ℝ := m - 1 / 2 + 3 / (20 * m)

private theorem enB_pos {m : ℝ} (hm : 1 ≤ m) : 0 < enB m := by
  unfold enB
  have : 0 < 3 / (20 * m) := by positivity
  linarith

private theorem enB_mono_step {m : ℝ} (hm : 1 ≤ m) : m ^ 2 * enB (m + 2) ≤ (m + 1) ^ 2 * enB m := by
  unfold enB
  have hm0 : 0 < m := by linarith
  rw [← sub_nonneg]
  have e : (m + 1) ^ 2 * (m - 1 / 2 + 3 / (20 * m)) - m ^ 2 * (m + 2 - 1 / 2 + 3 / (20 * (m + 2)))
      = (2 * m ^ 2 - 5 * m + 6) / (20 * m * (m + 2)) := by
    field_simp
    ring
  rw [e]
  apply div_nonneg _ (by positivity)
  nlinarith [sq_nonneg (m - 5 / 4)]

private theorem enB_le_div {M : ℝ} (hM : 1 ≤ M) : M / enB M ≤ 1 + 1 / M := by
  have hB := enB_pos hM
  rw [div_le_iff₀ hB]
  unfold enB
  have hM0 : 0 < M := by linarith
  have e : (1 + 1 / M) * (M - 1 / 2 + 3 / (20 * M)) - M
      = (1 / 2) - 1 / (2 * M) + 3 / (20 * M) + 3 / (20 * M ^ 2) := by
    field_simp; ring
  have h1 : 1 / (2 * M) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
  have : 0 ≤ 3 / (20 * M) := by positivity
  have : 0 ≤ 3 / (20 * M ^ 2) := by positivity
  nlinarith

/-- Abstract sequence argument: if $a_m a_{m+1} = m$, $a_m > 0$ and $a_m^2 \le m$ for $m \ge 1$,
then $a_m^2 \le m - 1/2 + 3/(20m)$. -/
private theorem en_seq_sq_le (a : ℕ → ℝ) (hpos : ∀ m, 1 ≤ m → 0 < a m)
    (hrec : ∀ m, 1 ≤ m → a m * a (m + 1) = m) (hsq : ∀ m, 1 ≤ m → a m ^ 2 ≤ m)
    (m : ℕ) (hm : 1 ≤ m) : a m ^ 2 ≤ enB m := by
  have hstep : ∀ k, 1 ≤ k → a (k + 2) = ((k : ℝ) + 1) / k * a k := by
    intro k hk
    have h1 := hrec k hk
    have h2 := hrec (k + 1) (by omega)
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have ha1 := hpos (k + 1) (by omega)
    push_cast at h2
    rw [show k + 1 + 1 = k + 2 by ring] at h2
    field_simp
    nlinarith
  -- ratio `ρ k = a k² / B k` is nondecreasing along steps of two
  have hmono : ∀ k, 1 ≤ k → a k ^ 2 / enB k ≤ a (k + 2) ^ 2 / enB ((k + 2 : ℕ)) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hk0 : (0 : ℝ) < k := by linarith
    have hB := enB_pos hk1
    have hB2 := enB_pos (show (1 : ℝ) ≤ ((k + 2 : ℕ) : ℝ) by push_cast; linarith)
    rw [hstep k hk, div_le_div_iff₀ hB hB2]
    have hms := enB_mono_step hk1
    push_cast
    have e : (((k : ℝ) + 1) / k * a k) ^ 2 = ((k : ℝ) + 1) ^ 2 * a k ^ 2 / k ^ 2 := by
      field_simp
    rw [e]
    rw [show ((k : ℝ) + 1) ^ 2 * a k ^ 2 / k ^ 2 * enB k
        = a k ^ 2 * (((k : ℝ) + 1) ^ 2 * enB k) / k ^ 2 by ring]
    rw [le_div_iff₀ (by positivity)]
    have : a k ^ 2 * (k ^ 2 * enB (k + 2)) ≤ a k ^ 2 * ((k + 1) ^ 2 * enB k) :=
      mul_le_mul_of_nonneg_left hms (sq_nonneg _)
    nlinarith
  have hiter : ∀ j : ℕ, a m ^ 2 / enB m ≤ a (m + 2 * j) ^ 2 / enB ((m + 2 * j : ℕ)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine ih.trans ?_
      have := hmono (m + 2 * j) (by omega)
      rwa [show m + 2 * j + 2 = m + 2 * (j + 1) by ring] at this
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hB := enB_pos hm1
  by_contra hcon
  push Not at hcon
  set ρ := a m ^ 2 / enB m with hρ
  have hρ1 : 1 < ρ := by rw [hρ, lt_div_iff₀ hB]; linarith
  obtain ⟨j, hj⟩ := exists_nat_gt (1 / (ρ - 1))
  set M : ℕ := m + 2 * j with hM
  have hM1 : (1 : ℝ) ≤ M := by rw [hM]; push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  have hBM := enB_pos hM1
  have h1 := hiter j
  rw [← hM] at h1
  have h2 : a M ^ 2 / enB M ≤ M / enB M :=
    div_le_div_of_nonneg_right (hsq M (by omega)) hBM.le
  have h3 := enB_le_div hM1
  have hj0 : (0 : ℝ) < j := lt_trans (by positivity) hj
  have hjM : (j : ℝ) ≤ M := by rw [hM]; push_cast; linarith
  have h4 : 1 / (M : ℝ) < ρ - 1 := by
    have : 1 / (M : ℝ) ≤ 1 / j := one_div_le_one_div_of_le hj0 hjM
    have : 1 / (j : ℝ) < ρ - 1 := by
      rw [div_lt_iff₀ hj0]
      rw [div_lt_iff₀ (by linarith)] at hj
      linarith
    linarith
  linarith

/-- $\sqrt{m(m+1)} \ge m + 1/2 - 1/(8m)$ for $m \ge 1$. -/
private theorem en_sqrt_mul_ge {m : ℝ} (hm : 1 ≤ m) :
    m + 1 / 2 - 1 / (8 * m) ≤ Real.sqrt m * Real.sqrt (m + 1) := by
  rw [← Real.sqrt_mul (by linarith)]
  apply Real.le_sqrt_of_sq_le
  have hm0 : 0 < m := by linarith
  have e : (m + 1 / 2 - 1 / (8 * m)) ^ 2 = m * (m + 1) - 1 / (8 * m) + 1 / (64 * m ^ 2) := by
    field_simp; ring
  rw [e]
  have : 1 / (64 * m ^ 2) ≤ 1 / (8 * m) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]; nlinarith
  linarith

/-- One step: if $0 < a \le \sqrt{B_m}$ and $a b = m$ then $b - a \ge \sqrt{m+1} - \sqrt{m}$. -/
private theorem en_step {m a b : ℝ} (hm : 1 ≤ m) (ha : 0 < a) (hab : a * b = m)
    (hB : a ^ 2 ≤ enB m) :
    Real.sqrt (m + 1) - Real.sqrt m ≤ b - a := by
  have hm0 : 0 < m := by linarith
  have hb : b = m / a := by field_simp; linarith
  rw [hb]
  set s := Real.sqrt m with hs
  set t := Real.sqrt (m + 1) with ht
  have hs0 : 0 < s := Real.sqrt_pos.2 hm0
  have ht0 : 0 < t := Real.sqrt_pos.2 (by linarith)
  have hs2 : s ^ 2 = m := Real.sq_sqrt hm0.le
  have ht2 : t ^ 2 = m + 1 := Real.sq_sqrt (by linarith)
  have hst := en_sqrt_mul_ge hm
  rw [← hs, ← ht] at hst
  have hd : t - s = 1 / (t + s) := by
    field_simp
    nlinarith
  have hts : 0 < t + s := by linarith
  have hc : 0 < 1 / 2 - 3 / (20 * m) := by
    have : 3 / (20 * m) ≤ 3 / 20 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    linarith
  have hma : 1 / 2 - 3 / (20 * m) ≤ m - a ^ 2 := by unfold enB at hB; linarith
  have hsq : 4 * m + 2 - 1 / (4 * m) ≤ (t + s) ^ 2 := by
    have : (t + s) ^ 2 = t ^ 2 + s ^ 2 + 2 * (s * t) := by ring
    rw [this, ht2, hs2]
    have : 2 * (m + 1 / 2 - 1 / (8 * m)) = 2 * m + 1 - 1 / (4 * m) := by field_simp; ring
    linarith
  have hpoly : enB m ≤ (1 / 2 - 3 / (20 * m)) ^ 2 * (4 * m + 2 - 1 / (4 * m)) := by
    unfold enB
    rw [← sub_nonneg]
    have e : (1 / 2 - 3 / (20 * m)) ^ 2 * (4 * m + 2 - 1 / (4 * m)) - (m - 1 / 2 + 3 / (20 * m))
        = (640 * m ^ 3 - 676 * m ^ 2 + 132 * m - 9) / (1600 * m ^ 3) := by
      field_simp; ring
    rw [e]
    apply div_nonneg _ (by positivity)
    nlinarith [sq_nonneg (m - 1), mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hm)]
  have h5 : a ^ 2 ≤ ((1 / 2 - 3 / (20 * m)) * (t + s)) ^ 2 := by
    rw [mul_pow]
    refine hB.trans (hpoly.trans ?_)
    exact mul_le_mul_of_nonneg_left hsq (sq_nonneg _)
  have h6 : a ≤ (1 / 2 - 3 / (20 * m)) * (t + s) :=
    (pow_le_pow_iff_left₀ ha.le (by positivity) (by norm_num)).1 h5
  have hkey : a ≤ (m - a ^ 2) * (t + s) :=
    h6.trans (mul_le_mul_of_nonneg_right hma hts.le)
  have e2 : m / a - a = (m - a ^ 2) / a := by field_simp
  rw [hd, e2, div_le_div_iff₀ hts ha]
  linarith

/-- Telescoping: $a_N - a_n \ge \sqrt{N} - \sqrt{n}$ for $N \ge n \ge 1$. -/
private theorem en_seq_diff (a : ℕ → ℝ) (hpos : ∀ m, 1 ≤ m → 0 < a m)
    (hrec : ∀ m, 1 ≤ m → a m * a (m + 1) = m) (hsq : ∀ m, 1 ≤ m → a m ^ 2 ≤ m)
    {N n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    Real.sqrt N - Real.sqrt n ≤ a N - a n := by
  induction N, hnN using Nat.le_induction with
  | base => simp
  | succ k hk ih =>
    have hk1 : 1 ≤ k := le_trans hn hk
    have hst := en_step (m := (k : ℝ)) (by exact_mod_cast hk1) (hpos k hk1) (hrec k hk1)
      (en_seq_sq_le a hpos hrec hsq k hk1)
    push_cast
    linarith

/-- **Growth of $\mathbb{E}\|\mathbf{g}_d\|$**: for standard Gaussian vectors $\mathbf{g}$ in
$\mathbb{R}^n$ and $\mathbf{g}'$ in $\mathbb{R}^m$ (possibly on different probability spaces) with
$1 \le \lvert n \rvert \le \lvert m \rvert$,
$$\sqrt{\lvert m \rvert} - \sqrt{\lvert n \rvert}
\le \mathbb{E}\|\mathbf{g}'\| - \mathbb{E}\|\mathbf{g}\|\,.$$
[DavidsonSzarek2001, proof of Theorem II.13]; the step of Gordon's lower bound for the smallest
singular value of a Gaussian matrix. Both hypotheses are needed: for $\lvert n \rvert = 0$ it would
claim $\sqrt{\lvert m \rvert} \le \mathbb{E}\|\mathbf{g}'\|$, false for $\lvert m \rvert \ge 1$, and
for $\lvert n \rvert > \lvert m \rvert$ the inequality reverses. -/
theorem le_integral_norm_sub_integral_norm_of_hasLaw_gaussianVector {Ω' : Type*}
    {mΩ' : MeasurableSpace Ω'} {ν : Measure Ω'} {m : Type*} [Fintype m] {g' : Ω' → m → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) (hg' : HasLaw g' (gaussianVector m) ν)
    (hn : 0 < Fintype.card n) (hnm : Fintype.card n ≤ Fintype.card m) :
    √(Fintype.card m : ℝ) - √(Fintype.card n : ℝ) ≤
      ∫ ω, ‖WithLp.toLp 2 (g' ω)‖ ∂ν - ∫ ω, ‖WithLp.toLp 2 (g ω)‖ ∂μ := by
  rw [integral_norm_eq_gaussNormMean hg, integral_norm_eq_gaussNormMean hg']
  exact en_seq_diff gaussNormMean (fun _ hd => gaussNormMean_pos hd)
    (fun _ hd => gaussNormMean_mul_succ hd) (fun d _ => gaussNormMean_sq_le d) hn hnm

/-! ### Differences of two independent chi-square variables -/

section ChiSquareDifference

variable {h : Ω → n → ℝ}

/-- The powers of $\|\mathbf{g}\|^2$ are integrable (helper). -/
private theorem integrable_norm_sq_pow (hg : HasLaw g (gaussianVector n) μ)
    (hn : 0 < Fintype.card n) (k : ℕ) :
    Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ k) μ := by
  have hs : -((Fintype.card n : ℝ) / 2) < (k : ℝ) := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    have : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
    linarith
  simpa only [Real.rpow_natCast] using integrable_norm_sq_rpow_of_hasLaw_gaussianVector hg hs

/-- Moments of $\|\mathbf{g}\|^2$ (helper): $\mathbb{E}(\|\mathbf{g}\|^2)^k
= \prod_{i<k}(d+2i)$ for $d = \lvert n \rvert > 0$. -/
private theorem integral_norm_sq_pow_eq_prod (hg : HasLaw g (gaussianVector n) μ)
    (hn : 0 < Fintype.card n) (k : ℕ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ k ∂μ =
      ∏ i ∈ Finset.range k, ((Fintype.card n : ℝ) + 2 * i) := by
  have hd : (0 : ℝ) < Fintype.card n := by exact_mod_cast hn
  have hs : -((Fintype.card n : ℝ) / 2) < (k : ℝ) := by
    have := (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
    linarith
  have h := integral_norm_sq_rpow_of_hasLaw_gaussianVector hg hs
  simp only [Real.rpow_natCast] at h
  have hpos : ∀ m : ℕ, (0 : ℝ) < (Fintype.card n : ℝ) / 2 + m := fun m => by
    have := (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    linarith
  have hG : ∀ m : ℕ, Real.Gamma ((Fintype.card n : ℝ) / 2 + m) =
      Real.Gamma ((Fintype.card n : ℝ) / 2) *
        ∏ i ∈ Finset.range m, ((Fintype.card n : ℝ) / 2 + i) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Nat.cast_succ, show (Fintype.card n : ℝ) / 2 + (m + 1) =
          ((Fintype.card n : ℝ) / 2 + m) + 1 by ring,
        Real.Gamma_add_one (hpos m).ne', ih, Finset.prod_range_succ]
      ring
  have hΓ : Real.Gamma ((Fintype.card n : ℝ) / 2) ≠ 0 :=
    (Real.Gamma_pos_of_pos (by linarith)).ne'
  have hp : ∏ i ∈ Finset.range k, ((Fintype.card n : ℝ) + 2 * i) =
      2 ^ k * ∏ i ∈ Finset.range k, ((Fintype.card n : ℝ) / 2 + i) := by
    rw [show (2 : ℝ) ^ k = ∏ _i ∈ Finset.range k, (2 : ℝ) by simp, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [h, hG k, hp]
  field_simp

/-- For independent $\mathbf{g}, \mathbf{h}$, the mixed powers of $\|\mathbf{g}\|^2$ and
$\|\mathbf{h}\|^2$ are integrable and their integrals factor (helper). -/
private theorem integrable_and_integral_norm_sq_pow_mul (hg : HasLaw g (gaussianVector n) μ)
    (hh : HasLaw h (gaussianVector n) μ) (hgh : IndepFun g h μ) (hn : 0 < Fintype.card n)
    (a b : ℕ) :
    Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ a * (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ b) μ ∧
      ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ a * (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ b ∂μ =
        (∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ a ∂μ) * ∫ ω, (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ b ∂μ := by
  have hf : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ a := by fun_prop
  have hk : Measurable fun x : n → ℝ => (‖WithLp.toLp 2 x‖ ^ 2) ^ b := by fun_prop
  exact ⟨(hgh.comp hf hk).integrable_mul (integrable_norm_sq_pow hg hn a)
      (integrable_norm_sq_pow hh hn b),
    (hgh.comp hf hk).integral_mul_eq_mul_integral
      (hf.comp_aemeasurable hg.aemeasurable).aestronglyMeasurable
      (hk.comp_aemeasurable hh.aemeasurable).aestronglyMeasurable⟩

/-- The variance of a difference of two independent $\chi^2_d$ variables: for independent
standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension $d = \lvert n \rvert$,
$$\mathbb{E}\bigl(\|\mathbf{g}\|^2 - \|\mathbf{h}\|^2\bigr)^2 = 4d\,.$$ -/
theorem integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hh : HasLaw h (gaussianVector n) μ)
    (hgh : IndepFun g h μ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2 ∂μ =
      4 * Fintype.card n := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hd0 | hd
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hd0
    simp [Subsingleton.elim (WithLp.toLp 2 (g _)) 0, Subsingleton.elim (WithLp.toLp 2 (h _)) 0]
  obtain ⟨hmix, hmixI⟩ := integrable_and_integral_norm_sq_pow_mul hg hh hgh hd 1 1
  have e : ∀ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2 =
      ((‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 + (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) -
        2 * ((‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 1 * (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 1) :=
    fun ω => by ring
  have hI : Integrable (fun ω => (‖WithLp.toLp 2 (g ω)‖ ^ 2) ^ 2 +
      (‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 2) μ :=
    (integrable_norm_sq_pow hg hd 2).add (integrable_norm_sq_pow hh hd 2)
  simp only [e]
  rw [integral_sub hI (hmix.const_mul 2), integral_add (integrable_norm_sq_pow hg hd 2)
      (integrable_norm_sq_pow hh hd 2), integral_const_mul, hmixI]
  simp only [integral_norm_sq_pow_eq_prod hg hd, integral_norm_sq_pow_eq_prod hh hd,
    Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

/-- Expansion of $\mathbb{E}(A - B)^4$ for integrable powers and factorised mixed terms
(helper). -/
private theorem integral_sub_pow_four_eq {A B : Ω → ℝ}
    (hA : ∀ k : ℕ, Integrable (fun ω => A ω ^ k) μ)
    (hB : ∀ k : ℕ, Integrable (fun ω => B ω ^ k) μ)
    (hAB : ∀ a b : ℕ, Integrable (fun ω => A ω ^ a * B ω ^ b) μ)
    (hI : ∀ a b : ℕ, ∫ ω, A ω ^ a * B ω ^ b ∂μ = (∫ ω, A ω ^ a ∂μ) * ∫ ω, B ω ^ b ∂μ) :
    ∫ ω, (A ω - B ω) ^ 4 ∂μ = ∫ ω, A ω ^ 4 ∂μ + ∫ ω, B ω ^ 4 ∂μ
      - 4 * ((∫ ω, A ω ^ 3 ∂μ) * ∫ ω, B ω ^ 1 ∂μ)
      - 4 * ((∫ ω, A ω ^ 1 ∂μ) * ∫ ω, B ω ^ 3 ∂μ)
      + 6 * ((∫ ω, A ω ^ 2 ∂μ) * ∫ ω, B ω ^ 2 ∂μ) := by
  have e : ∀ ω, (A ω - B ω) ^ 4 = A ω ^ 4 + B ω ^ 4 - 4 * (A ω ^ 3 * B ω ^ 1)
      - 4 * (A ω ^ 1 * B ω ^ 3) + 6 * (A ω ^ 2 * B ω ^ 2) := fun ω => by ring
  simp only [e]
  have i1 : Integrable (fun ω => A ω ^ 4 + B ω ^ 4) μ := (hA 4).add (hB 4)
  have i2 : Integrable (fun ω => A ω ^ 4 + B ω ^ 4 - 4 * (A ω ^ 3 * B ω ^ 1)) μ :=
    i1.sub ((hAB 3 1).const_mul 4)
  have i3 : Integrable (fun ω => A ω ^ 4 + B ω ^ 4 - 4 * (A ω ^ 3 * B ω ^ 1)
      - 4 * (A ω ^ 1 * B ω ^ 3)) μ := i2.sub ((hAB 1 3).const_mul 4)
  have i4 : Integrable (fun ω => 6 * (A ω ^ 2 * B ω ^ 2)) μ := (hAB 2 2).const_mul 6
  rw [integral_add i3 i4, integral_sub i2 ((hAB 1 3).const_mul 4),
    integral_sub i1 ((hAB 3 1).const_mul 4), integral_add (hA 4) (hB 4),
    integral_const_mul, integral_const_mul, integral_const_mul, hI 3 1, hI 1 3, hI 2 2]

/-- The fourth moment of a difference of two independent $\chi^2_d$ variables: for
independent standard Gaussian vectors $\mathbf{g}, \mathbf{h}$ of dimension
$d = \lvert n \rvert$,
$$\mathbb{E}\bigl(\|\mathbf{g}\|^2 - \|\mathbf{h}\|^2\bigr)^4 = 48 d^2 + 96 d\,.$$ -/
theorem integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector
    (hg : HasLaw g (gaussianVector n) μ) (hh : HasLaw h (gaussianVector n) μ)
    (hgh : IndepFun g h μ) :
    ∫ ω, (‖WithLp.toLp 2 (g ω)‖ ^ 2 - ‖WithLp.toLp 2 (h ω)‖ ^ 2) ^ 4 ∂μ =
      48 * (Fintype.card n : ℝ) ^ 2 + 96 * Fintype.card n := by
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hd0 | hd
  · have : IsEmpty n := Fintype.card_eq_zero_iff.mp hd0
    simp [Subsingleton.elim (WithLp.toLp 2 (g _)) 0, Subsingleton.elim (WithLp.toLp 2 (h _)) 0]
  rw [integral_sub_pow_four_eq (A := fun ω => ‖WithLp.toLp 2 (g ω)‖ ^ 2)
      (B := fun ω => ‖WithLp.toLp 2 (h ω)‖ ^ 2) (integrable_norm_sq_pow hg hd)
      (integrable_norm_sq_pow hh hd)
      (fun a b => (integrable_and_integral_norm_sq_pow_mul hg hh hgh hd a b).1)
      (fun a b => (integrable_and_integral_norm_sq_pow_mul hg hh hgh hd a b).2)]
  simp only [integral_norm_sq_pow_eq_prod hg hd, integral_norm_sq_pow_eq_prod hh hd,
    Finset.prod_range_succ, Finset.prod_range_zero]
  push_cast
  ring

end ChiSquareDifference

end NLAlib
