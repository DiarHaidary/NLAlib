/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.MeasureTheory.Measure.WithDensity
public import NLAlib.Polynomial.Approximation.Stieltjes

/-!
# Interpolating Stieltjes functions

The error of polynomial interpolation of a Stieltjes function at positive nodes
$\theta_1, \dots, \theta_k$ factors as the nodal polynomial
$\pi(z) = \prod_j (z - \theta_j)$ times another Stieltjes function:
$$f(z) - q(z) = (-1)^k\,\pi(z) \int \frac{1}{z + t}\,
\frac{d\mu(t)}{\prod_j (\theta_j + t)} \,,$$
where $q$ interpolates $f$ at the nodes. If instead $f(z)/z$ is Stieltjes with measure $\mu$
and $k \ge 1$, the same holds with the sign $(-1)^{k+1}$ and the measure
$t\,d\mu(t)/\prod_j(\theta_j + t)$. Both come from one identity for each kernel, integrated
against $\mu$; the interpolant of the integral is the integral of the interpolants because
Lagrange interpolation is a finite combination of values.

Nodes are a `Finset ℝ` with `id` as the node map, the interpolant is Mathlib's
`Lagrange.interpolate s id f` and the nodal polynomial `Lagrange.nodal s id`.

## Main results

* `NLAlib.inv_add_sub_eval_interpolate`, `NLAlib.div_add_sub_eval_interpolate`: the identity
  for one kernel, $(z + t)^{-1}$ and $z/(z + t)$.
* `NLAlib.HasStieltjesMeasure.sub_eval_interpolate_eq`,
  `NLAlib.HasStieltjesMeasure.exists_sub_eval_interpolate_eq`: Stieltjes $f$.
* `NLAlib.HasStieltjesMeasure.sub_eval_interpolate_eq_of_div`,
  `NLAlib.HasStieltjesMeasure.exists_sub_eval_interpolate_eq_of_div`: Stieltjes $f(z)/z$.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped ENNReal NNReal

namespace NLAlib

variable {f : ℝ → ℝ} {μ : Measure ℝ} {s : Finset ℝ}

/-- The degree bound behind the kernel identity: for $\deg q < \lvert s \rvert$,
$\deg\bigl(1 - (X + t)\,q - c\,\pi_s\bigr) < \lvert s \rvert + 1$. -/
private theorem degree_one_sub_mul_sub_lt {q : ℝ[X]} (hq : q.degree < s.card) (t c : ℝ) :
    (1 - (X + C t) * q - C c * Lagrange.nodal s id).degree < ↑(s.card + 1) := by
  have h1 : ((X + C t) * q).degree < ↑(s.card + 1) := by
    rw [degree_mul, degree_X_add_C]
    calc 1 + q.degree < 1 + (s.card : WithBot ℕ) := WithBot.add_lt_add_left WithBot.one_ne_bot hq
      _ = ↑(s.card + 1) := by push_cast; ring
  have h2 : (C c * Lagrange.nodal s id).degree < ↑(s.card + 1) := by
    refine (degree_mul_le _ _).trans_lt ?_
    rw [Lagrange.degree_nodal]
    refine (add_le_add_left degree_C_le _).trans_lt ?_
    rw [zero_add]
    exact_mod_cast Nat.lt_succ_self _
  have h0 : (1 : ℝ[X]).degree < ↑(s.card + 1) := by
    rw [degree_one]
    exact_mod_cast Nat.succ_pos _
  exact (degree_sub_le _ _).trans_lt (max_lt ((degree_sub_le _ _).trans_lt (max_lt h0 h1)) h2)

/-- **Interpolation error of one resolvent kernel**: for nodes $s$ and $t$ with
$\theta + t \ne 0$ for every node and $z + t \ne 0$,
$$\frac{1}{z + t} - q_t(z) = (-1)^{\lvert s \rvert}\,
\frac{\pi(z)}{(z + t)\prod_{\theta \in s}(\theta + t)} \,,$$
where $q_t$ interpolates $\theta \mapsto (\theta + t)^{-1}$ on $s$ and $\pi$ is the nodal
polynomial. The numerator $1 - (z + t)q_t(z)$ has degree at most $\lvert s \rvert$ and
vanishes on $s$, so it is a multiple of $\pi$, fixed by its value $1$ at $z = -t$.
[FrommerGuttelSchweitzer2014, (3.9)]; [ChenPersson2026, Lemma 4]. -/
theorem inv_add_sub_eval_interpolate {t z : ℝ} (hs : ∀ θ ∈ s, θ + t ≠ 0) (hz : z + t ≠ 0) :
    (z + t)⁻¹ - (Lagrange.interpolate s id fun θ => (θ + t)⁻¹).eval z =
      (-1) ^ s.card * (Lagrange.nodal s id).eval z / ((z + t) * ∏ θ ∈ s, (θ + t)) := by
  set q := Lagrange.interpolate s id fun θ => (θ + t)⁻¹
  have hq : q.degree < s.card := Lagrange.degree_interpolate_lt _ (Set.injOn_id _)
  have hP : ∀ θ ∈ s, (θ + t) ⁻¹ = q.eval θ := fun θ hθ =>
    (Lagrange.eval_interpolate_at_node (v := id) (fun θ => (θ + t)⁻¹) (Set.injOn_id _) hθ).symm
  have hprod : ∏ θ ∈ s, (-t - θ) = (-1) ^ s.card * ∏ θ ∈ s, (θ + t) := by
    rw [← Finset.prod_neg]
    exact Finset.prod_congr rfl fun θ _ => by ring
  have hprod0 : ∏ θ ∈ s, (θ + t) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
  have hπt : (Lagrange.nodal s id).eval (-t) = (-1) ^ s.card * ∏ θ ∈ s, (θ + t) := by
    rw [Lagrange.eval_nodal, ← hprod]
    rfl
  set c := ((-1) ^ s.card * ∏ θ ∈ s, (θ + t))⁻¹
  have hts : -t ∉ s := fun h => hs _ h (by ring)
  -- $1 - (X + t)q = c\,\pi_s$: both sides have degree at most $\lvert s \rvert$ and agree on
  -- $s \cup \{-t\}$
  have hkey : 1 - (X + C t) * q - C c * Lagrange.nodal s id = 0 := by
    refine Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero (insert (-t) s) ?_ ?_
    · rw [Finset.card_insert_of_notMem hts]
      exact degree_one_sub_mul_sub_lt hq t c
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · simp only [eval_sub, eval_one, eval_mul, eval_add, eval_X, eval_C, neg_add_cancel,
          zero_mul, sub_zero, hπt, c]
        rw [inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ (by norm_num)) hprod0), sub_self]
      · have hx0 : (Lagrange.nodal s id).eval x = 0 := Lagrange.eval_nodal_at_node (v := id) hx
        simp only [eval_sub, eval_one, eval_mul, eval_add, eval_X, eval_C, ← hP x hx, hx0,
          mul_zero, sub_zero]
        rw [mul_inv_cancel₀ (hs x hx), sub_self]
  have hz' : 1 - (z + t) * q.eval z = c * (Lagrange.nodal s id).eval z := by
    have := congrArg (eval z) hkey
    simp only [eval_sub, eval_one, eval_mul, eval_add, eval_X, eval_C, eval_zero] at this
    linarith
  have hc : c = (-1) ^ s.card * (∏ θ ∈ s, (θ + t))⁻¹ := by
    simp only [c, mul_inv, ← inv_pow, inv_neg, inv_one]
  rw [eq_div_iff (mul_ne_zero hz hprod0)]
  calc ((z + t)⁻¹ - q.eval z) * ((z + t) * ∏ θ ∈ s, (θ + t))
      = (1 - (z + t) * q.eval z) * ∏ θ ∈ s, (θ + t) := by field_simp
    _ = _ := by rw [hz', hc]; field_simp

/-- **Interpolation error of the kernel $z/(z + t)$**: for nonempty nodes $s$, $t$ with
$\theta + t \ne 0$ on $s$ and $z + t \ne 0$,
$$\frac{z}{z + t} - q_t(z) = (-1)^{\lvert s \rvert + 1}\,
\frac{t\,\pi(z)}{(z + t)\prod_{\theta \in s}(\theta + t)} \,,$$
where $q_t$ interpolates $\theta \mapsto \theta/(\theta + t)$. The numerator
$z - (z + t)q_t(z)$ has degree at most $\lvert s \rvert$ because $s$ is nonempty.
[ChenPersson2026, Lemma 4]. -/
theorem div_add_sub_eval_interpolate {t z : ℝ} (hne : s.Nonempty) (hs : ∀ θ ∈ s, θ + t ≠ 0)
    (hz : z + t ≠ 0) :
    z / (z + t) - (Lagrange.interpolate s id fun θ => θ / (θ + t)).eval z =
      (-1) ^ (s.card + 1) * t * (Lagrange.nodal s id).eval z /
        ((z + t) * ∏ θ ∈ s, (θ + t)) := by
  have hfun : Lagrange.interpolate s id (fun θ => θ / (θ + t)) =
      Lagrange.interpolate s id (1 - t • fun θ => (θ + t)⁻¹) :=
    Lagrange.interpolate_eq_of_values_eq_on _ _ fun θ hθ => by
      simp only [Pi.sub_apply, Pi.one_apply, Pi.smul_apply, smul_eq_mul]
      field_simp [hs θ hθ]
      ring
  rw [hfun, map_sub, map_smul, Lagrange.interpolate_one (Set.injOn_id _) hne, eval_sub, eval_one,
    eval_smul, smul_eq_mul]
  have h := inv_add_sub_eval_interpolate hs hz
  have hprod0 : ∏ θ ∈ s, (θ + t) ≠ 0 := Finset.prod_ne_zero_iff.mpr hs
  have e : z / (z + t) - (1 - t * (Lagrange.interpolate s id fun θ => (θ + t)⁻¹).eval z) =
      -t * ((z + t)⁻¹ - (Lagrange.interpolate s id fun θ => (θ + t)⁻¹).eval z) := by
    field_simp
    ring
  rw [e, h, pow_succ]
  ring

/-- The interpolant of an integral of kernels is the integral of the interpolants of the
kernels, for integrable kernels. -/
private theorem eval_interpolate_eq_integral {k : ℝ → ℝ → ℝ}
    (hk : ∀ θ ∈ s, f θ = ∫ t, k θ t ∂μ) (hi : ∀ θ ∈ s, Integrable (k θ) μ) (z : ℝ) :
    (Lagrange.interpolate s id f).eval z =
        ∫ t, (Lagrange.interpolate s id fun θ => k θ t).eval z ∂μ ∧
      Integrable (fun t => (Lagrange.interpolate s id fun θ => k θ t).eval z) μ := by
  simp only [Lagrange.interpolate_apply, eval_finsetSum, eval_mul, eval_C]
  refine ⟨?_, integrable_finsetSum _ fun θ hθ => (hi θ hθ).mul_const _⟩
  rw [integral_finsetSum _ fun θ hθ => (hi θ hθ).mul_const _]
  exact Finset.sum_congr rfl fun θ hθ => by rw [hk θ hθ, integral_mul_const]

/-- **Interpolation error of a Stieltjes function**: for $f$ represented by $\mu$, positive
nodes $s$ and $z > 0$,
$$f(z) - q(z) = (-1)^{\lvert s \rvert}\,\pi(z)\int \frac{1}{z + t}\,
\frac{d\mu(t)}{\prod_{\theta \in s}(\theta + t)} \,,$$
with $q$ the interpolant of $f$ on $s$ and $\pi$ the nodal polynomial. The integral is again a
Stieltjes function of $z$ (`HasStieltjesMeasure.exists_sub_eval_interpolate_eq`).
[FrommerGuttelSchweitzer2014, (3.9)]; [ChenPersson2026, Lemma 4, part 1]; there for the Ritz
values, here for any positive nodes. -/
theorem HasStieltjesMeasure.sub_eval_interpolate_eq (hf : HasStieltjesMeasure f μ)
    (hs : ∀ θ ∈ s, 0 < θ) {z : ℝ} (hz : 0 < z) :
    f z - (Lagrange.interpolate s id f).eval z =
      (-1) ^ s.card * (Lagrange.nodal s id).eval z *
        ∫ t, (z + t)⁻¹ * (∏ θ ∈ s, (θ + t))⁻¹ ∂μ := by
  obtain ⟨he, hi⟩ := eval_interpolate_eq_integral (k := fun θ t => (θ + t)⁻¹)
    (fun θ hθ => hf.eq_integral θ (hs θ hθ)) (fun θ hθ => hf.integrable_inv_add (hs θ hθ)) z
  rw [he, hf.eq_integral z hz, ← integral_sub (hf.integrable_inv_add hz) hi,
    ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_nonneg] with t ht
  rw [inv_add_sub_eval_interpolate (fun θ hθ => by linarith [hs θ hθ]) (by linarith)]
  field_simp

/-- **Interpolation error when $f(z)/z$ is Stieltjes**: for $z \mapsto f(z)/z$ represented by
$\mu$, nonempty positive nodes $s$ and $z > 0$,
$$f(z) - q(z) = (-1)^{\lvert s \rvert + 1}\,\pi(z)\int \frac{1}{z + t}\,
\frac{t\,d\mu(t)}{\prod_{\theta \in s}(\theta + t)} \,.$$
The integrand is integrable because $t/\prod_\theta(\theta + t) \le 1$ for one node.
[ChenPersson2026, Lemma 4, part 2]. -/
theorem HasStieltjesMeasure.sub_eval_interpolate_eq_of_div
    (hf : HasStieltjesMeasure (fun z => f z / z) μ) (hne : s.Nonempty) (hs : ∀ θ ∈ s, 0 < θ)
    {z : ℝ} (hz : 0 < z) :
    f z - (Lagrange.interpolate s id f).eval z =
      (-1) ^ (s.card + 1) * (Lagrange.nodal s id).eval z *
        ∫ t, (z + t)⁻¹ * (t * (∏ θ ∈ s, (θ + t))⁻¹) ∂μ := by
  have hrep : ∀ x, 0 < x → f x = ∫ t, x / (x + t) ∂μ := fun x hx => by
    simp only [div_eq_mul_inv x]
    rw [integral_const_mul, ← hf.eq_integral x hx]
    field_simp
  have hint : ∀ x, 0 < x → Integrable (fun t => x / (x + t)) μ := fun x hx => by
    simpa only [div_eq_mul_inv] using (hf.integrable_inv_add hx).const_mul x
  obtain ⟨he, hi⟩ := eval_interpolate_eq_integral (k := fun θ t => θ / (θ + t))
    (fun θ hθ => hrep θ (hs θ hθ)) (fun θ hθ => hint θ (hs θ hθ)) z
  rw [he, hrep z hz, ← integral_sub (hint z hz) hi, ← integral_const_mul]
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_nonneg] with t ht
  rw [div_add_sub_eval_interpolate hne (fun θ hθ => by linarith [hs θ hθ]) (by linarith)]
  field_simp

/-- A bounded density turns a representing measure into one: for $\mu$ representing a
Stieltjes function and a measurable density $d \le C$ on $[0, \infty)$, the measure
$d\,\mu$ represents $z \mapsto \int (z + t)^{-1}\,d(t)\,d\mu(t)$. -/
private theorem HasStieltjesMeasure.withDensity {g : ℝ → ℝ} (hf : HasStieltjesMeasure g μ)
    {d : ℝ → ℝ≥0} (hd : Measurable d) {C : ℝ} (hC : ∀ t, 0 ≤ t → (d t : ℝ) ≤ C) :
    HasStieltjesMeasure (fun z => ∫ t, (z + t)⁻¹ ∂μ.withDensity fun t => (d t : ℝ≥0∞))
      (μ.withDensity fun t => (d t : ℝ≥0∞)) := by
  refine ⟨?_, ?_, fun z _ => rfl⟩
  · rw [withDensity_apply _ measurableSet_Iio, Measure.restrict_eq_zero.mpr hf.measure_Iio,
      lintegral_zero_measure]
  · rw [integrable_withDensity_iff_integrable_smul hd]
    refine (hf.integrable.const_mul C).mono'
      ((hd.coe_nnreal_real.smul (measurable_const.add measurable_id).inv).aestronglyMeasurable) ?_
    filter_upwards [hf.ae_nonneg] with t ht
    rw [NNReal.smul_def, smul_eq_mul, norm_mul, Real.norm_of_nonneg (d t).coe_nonneg,
      Real.norm_of_nonneg (inv_nonneg.mpr (by linarith))]
    exact mul_le_mul_of_nonneg_right (hC t ht) (inv_nonneg.mpr (by linarith))

/-- Integrating against $d\,\mu$ with $d = D$ on $[0, \infty)$ is integrating $D$ against
$\mu$. -/
private theorem integral_withDensity_toNNReal (hf : HasStieltjesMeasure f μ) {D : ℝ → ℝ}
    (hD : Measurable D) (hD0 : ∀ t, 0 ≤ t → 0 ≤ D t) (z : ℝ) :
    ∫ t, (z + t)⁻¹ ∂μ.withDensity (fun t => ((D t).toNNReal : ℝ≥0∞)) =
      ∫ t, (z + t)⁻¹ * D t ∂μ := by
  rw [integral_withDensity_eq_integral_smul hD.real_toNNReal]
  refine integral_congr_ae ?_
  filter_upwards [hf.ae_nonneg] with t ht
  rw [NNReal.smul_def, smul_eq_mul, Real.coe_toNNReal _ (hD0 t ht), mul_comm]

private theorem measurable_prod_add (s : Finset ℝ) : Measurable fun t => ∏ θ ∈ s, (θ + t) :=
  Finset.measurable_prod s fun _ _ => measurable_const.add measurable_id

/-- The interpolation remainder of a Stieltjes function is Stieltjes, with a measure absolutely
continuous with respect to $\mu$: with $\varsigma(z) = \int (z + t)^{-1}\,d\varrho(t)$ and
$d\varrho = d\mu/\prod_{\theta \in s}(\theta + t)$ (`μ.withDensity`),
$f - q = (-1)^{\lvert s \rvert}\,\pi\,\varsigma$ on $(0, \infty)$. Absolute continuity lets
a ratio bound that holds $\mu$-almost everywhere pass to $\varsigma$.
[ChenPersson2026, Lemma 4, part 1]. -/
theorem HasStieltjesMeasure.exists_sub_eval_interpolate_eq (hf : HasStieltjesMeasure f μ)
    (hs : ∀ θ ∈ s, 0 < θ) :
    ∃ (ς : ℝ → ℝ) (ρ : Measure ℝ), HasStieltjesMeasure ς ρ ∧ ρ ≪ μ ∧ ∀ z, 0 < z →
      f z - (Lagrange.interpolate s id f).eval z =
        (-1) ^ s.card * (Lagrange.nodal s id).eval z * ς z := by
  have hpos : ∀ t, 0 ≤ t → 0 < ∏ θ ∈ s, (θ + t) := fun t ht =>
    Finset.prod_pos fun θ hθ => by linarith [hs θ hθ]
  set D : ℝ → ℝ := fun t => (∏ θ ∈ s, (θ + t))⁻¹
  have hD : Measurable D := (measurable_prod_add s).inv
  have hbound : ∀ t, 0 ≤ t → ((D t).toNNReal : ℝ) ≤ (∏ θ ∈ s, θ)⁻¹ := fun t ht => by
    rw [Real.coe_toNNReal _ (inv_nonneg.mpr (hpos t ht).le)]
    exact inv_anti₀ (Finset.prod_pos hs) (Finset.prod_le_prod (fun θ hθ => (hs θ hθ).le)
      fun θ _ => by linarith)
  refine ⟨_, _, hf.withDensity hD.real_toNNReal hbound, withDensity_absolutelyContinuous _ _,
    fun z hz => ?_⟩
  rw [integral_withDensity_toNNReal hf hD (fun t ht => inv_nonneg.mpr (hpos t ht).le),
    hf.sub_eval_interpolate_eq hs hz]

/-- The interpolation remainder is Stieltjes when $f(z)/z$ is: $f - q =
(-1)^{\lvert s \rvert + 1}\,\pi\,\varsigma$ on $(0, \infty)$ with $\varsigma$ represented by
$d\varrho = t\,d\mu/\prod_{\theta \in s}(\theta + t)$, absolutely continuous with respect to
$\mu$. [ChenPersson2026, Lemma 4, part 2]. -/
theorem HasStieltjesMeasure.exists_sub_eval_interpolate_eq_of_div
    (hf : HasStieltjesMeasure (fun z => f z / z) μ) (hne : s.Nonempty) (hs : ∀ θ ∈ s, 0 < θ) :
    ∃ (ς : ℝ → ℝ) (ρ : Measure ℝ), HasStieltjesMeasure ς ρ ∧ ρ ≪ μ ∧ ∀ z, 0 < z →
      f z - (Lagrange.interpolate s id f).eval z =
        (-1) ^ (s.card + 1) * (Lagrange.nodal s id).eval z * ς z := by
  have hpos : ∀ t, 0 ≤ t → 0 < ∏ θ ∈ s, (θ + t) := fun t ht =>
    Finset.prod_pos fun θ hθ => by linarith [hs θ hθ]
  set D : ℝ → ℝ := fun t => t * (∏ θ ∈ s, (θ + t))⁻¹
  have hD : Measurable D := measurable_id.mul (measurable_prod_add s).inv
  have hD0 : ∀ t, 0 ≤ t → 0 ≤ D t := fun t ht => mul_nonneg ht (inv_nonneg.mpr (hpos t ht).le)
  obtain ⟨θ₀, hθ₀⟩ := hne
  have hP₀ : 0 < ∏ θ ∈ s.erase θ₀, θ :=
    Finset.prod_pos fun θ hθ => hs θ (Finset.mem_of_mem_erase hθ)
  -- $t \prod_\theta (\theta + t)^{-1} \le \prod_{\theta \ne \theta_0} \theta^{-1}$ for $t \ge 0$
  have hbound : ∀ t, 0 ≤ t → ((D t).toNNReal : ℝ) ≤ (∏ θ ∈ s.erase θ₀, θ)⁻¹ := fun t ht => by
    rw [Real.coe_toNNReal _ (hD0 t ht)]
    simp only [D, ← div_eq_mul_inv]
    rw [div_le_iff₀ (hpos t ht), ← div_eq_inv_mul, le_div_iff₀ hP₀,
      ← Finset.mul_prod_erase s (fun θ => θ + t) hθ₀]
    refine mul_le_mul (by linarith [hs θ₀ hθ₀]) (Finset.prod_le_prod
      (fun θ hθ => (hs θ (Finset.mem_of_mem_erase hθ)).le) fun θ _ => by linarith) hP₀.le
      (by linarith [hs θ₀ hθ₀])
  refine ⟨_, _, hf.withDensity hD.real_toNNReal hbound, withDensity_absolutelyContinuous _ _,
    fun z hz => ?_⟩
  rw [integral_withDensity_toNNReal hf hD hD0,
    hf.sub_eval_interpolate_eq_of_div ⟨θ₀, hθ₀⟩ hs hz]

end NLAlib
