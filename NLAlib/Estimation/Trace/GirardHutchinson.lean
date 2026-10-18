/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Block
public import NLAlib.Probability.QuadraticForm.HansonWright
public import NLAlib.Probability.QuadraticForm.Moments
public import NLAlib.RandomMatrix.Haar.Moments

/-!
# The Girard–Hutchinson trace estimator

For a square $\mathbf{A}$ and a test matrix $\mathbf{\Omega}$ with $m$ columns (the probes
$\boldsymbol{\omega}_1, \dots, \boldsymbol{\omega}_m$), the **Girard–Hutchinson estimate** is
$$\mathsf{girardHutchinson}(\mathbf{A}, \mathbf{\Omega}) :=
\frac{1}{m}\operatorname{tr}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})
= \frac{1}{m}\sum_{j=1}^m \boldsymbol{\omega}_j^{\mathsf{H}}\mathbf{A}\boldsymbol{\omega}_j\,.$$
It is unbiased when every probe is isotropic, and with independent probes its variance is the
single-probe variance divided by $m$. The single-probe variances are proved where their laws live:
independent coordinates (real Gaussian, Rademacher) in
`NLAlib/Probability/QuadraticForm/Moments.lean`, the real sphere and Haar frames in
`NLAlib/RandomMatrix/Haar/Moments.lean`. With the probes $\sqrt{\lvert n \rvert}$ times the columns
of a Haar frame, which are not independent, the variance is computed exactly here.

## Main definitions

* `NLAlib.girardHutchinson`.

## Main results

* `NLAlib.girardHutchinson_eq_sum`: the average of the single-probe estimates.
* `NLAlib.integral_girardHutchinson`: unbiasedness.
* `NLAlib.integral_norm_girardHutchinson_sub_trace_sq`, `NLAlib.variance_girardHutchinson`: the
  variance with $m$ independent probes is the single-probe variance divided by $m$.
* `NLAlib.variance_girardHutchinson_sqrt_smul_of_hasLaw_haarFrame`: orthonormal (Haar) probes.
* `NLAlib.measureReal_abs_girardHutchinson_sub_trace_ge_le`: the tail with independent
  sub-Gaussian entries, from Hanson–Wright.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n m : Type*} [Fintype n] [Fintype m]

/-- The **Girard–Hutchinson estimate** of $\operatorname{tr}\mathbf{A}$ from the test matrix
$\mathbf{\Omega}$, whose $m$ columns are the probes:
$\mathsf{girardHutchinson}(\mathbf{A}, \mathbf{\Omega}) :=
\operatorname{tr}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}) / m$. Junk value: $0$ when
$\mathbf{\Omega}$ has no columns. [Epperly2023, Girard–Hutchinson Estimator: The Basics];
the prototype's `hutchinsonEstimate`, there over $\mathbb{R}$. -/
noncomputable def girardHutchinson (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) : 𝕜 :=
  (Ωᴴ * A * Ω).trace / Fintype.card m

/-- The Girard–Hutchinson estimate is the average of the single-probe estimates
$\boldsymbol{\omega}_j^{\mathsf{H}}\mathbf{A}\boldsymbol{\omega}_j$. -/
theorem girardHutchinson_eq_sum (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    girardHutchinson A Ω = (∑ j, quadForm A fun i => Ω i j) / Fintype.card m := by
  rw [girardHutchinson]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.diag_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, quadForm_eq_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The Girard–Hutchinson estimator is unbiased**: if every probe is isotropic,
$\mathbb{E}[\mathsf{girardHutchinson}(\mathbf{A}, \mathbf{\Omega})] = \operatorname{tr}\mathbf{A}$.
No independence is needed. [Epperly2023, Unbiasedness].
Result: girard-hutchinson-unbiased -/
theorem integral_girardHutchinson [DecidableEq n] [Nonempty m] {X : Ω → Matrix n m 𝕜}
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) (A : Matrix n n 𝕜) :
    ∫ ω, girardHutchinson A (X ω) ∂μ = A.trace := by
  simp only [girardHutchinson_eq_sum]
  rw [integral_div, integral_finsetSum _ fun j _ => (hX j).integrable_quadForm A]
  rw [Finset.sum_congr rfl fun j _ => (hX j).integral_quadForm A]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card m : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  field_simp

omit [Fintype m] in
/-- The cross moments of centred independent probes vanish:
$\mathbb{E}[Y_j \overline{Y_l}] = 0$ for $j \ne l$, $Y_j = \boldsymbol{\omega}_j^{\mathsf{H}}
\mathbf{A}\boldsymbol{\omega}_j - \operatorname{tr}\mathbf{A}$. -/
private theorem integral_mul_star_eq_zero [DecidableEq n] {X : Ω → Matrix n m 𝕜}
    (hind : iIndepFun (fun j ω i => X ω i j) μ) (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ)
    (A : Matrix n n 𝕜) {j l : m} (hjl : j ≠ l) :
    ∫ ω, (quadForm A (fun i => X ω i j) - A.trace) *
      star (quadForm A (fun i => X ω i l) - A.trace) ∂μ = 0 := by
  have := hind.isProbabilityMeasure
  have hm (j : m) : AEMeasurable (fun ω i => X ω i j) μ :=
    aemeasurable_pi_lambda _ fun i => ((hX j).memLp i).aestronglyMeasurable.aemeasurable
  have hF : Continuous fun z : n → 𝕜 => quadForm A z - A.trace := by
    simp only [quadForm_eq_sum]
    fun_prop
  rw [(hind.indepFun hjl).integral_fun_comp_mul_comp (hm j) (hm l)
    (f := fun z => quadForm A z - A.trace) (g := fun z => star (quadForm A z - A.trace))
    hF.aestronglyMeasurable (continuous_star.comp hF).aestronglyMeasurable,
    integral_sub ((hX j).integrable_quadForm A) (integrable_const _),
    (hX j).integral_quadForm A]
  simp

/-- **The variance of the Girard–Hutchinson estimator**: for $m$ independent isotropic probes
whose single-probe estimates are square integrable with second moment $v$ about the mean,
$\mathbb{E}\lvert \mathsf{girardHutchinson}(\mathbf{A}, \mathbf{\Omega}) -
\operatorname{tr}\mathbf{A}\rvert^2 = v / m$. Over $\mathbb{C}$ the left side is the variance of
the complex estimate; the real `variance` form is `NLAlib.variance_girardHutchinson`.
[Epperly2023, Variance].
Result: girard-hutchinson-variance -/
theorem integral_norm_girardHutchinson_sub_trace_sq [DecidableEq n] [Nonempty m]
    {X : Ω → Matrix n m 𝕜} (hind : iIndepFun (fun j ω i => X ω i j) μ)
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) {A : Matrix n n 𝕜}
    (hL2 : ∀ j, MemLp (fun ω => quadForm A fun i => X ω i j) 2 μ) {v : ℝ}
    (hv : ∀ j, ∫ ω, ‖(quadForm A fun i => X ω i j) - A.trace‖ ^ 2 ∂μ = v) :
    ∫ ω, ‖girardHutchinson A (X ω) - A.trace‖ ^ 2 ∂μ = v / Fintype.card m := by
  classical
  have := hind.isProbabilityMeasure
  set Y : m → Ω → 𝕜 := fun j ω => (quadForm A fun i => X ω i j) - A.trace
  have hm0 : (Fintype.card m : 𝕜) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hY2 (j : m) : MemLp (Y j) 2 μ := (hL2 j).sub (memLp_const _)
  have hsum (ω : Ω) : girardHutchinson A (X ω) - A.trace =
      (Fintype.card m : 𝕜)⁻¹ * ∑ j, Y j ω := by
    rw [girardHutchinson_eq_sum]
    simp only [Y, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  have hnorm (z : 𝕜) : ‖z‖ ^ 2 = RCLike.re (z * star z) := by
    rw [RCLike.star_def, RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hint (j l : m) : Integrable (fun ω => Y j ω * star (Y l ω)) μ :=
    (hY2 l).star.integrable_mul (hY2 j) |>.congr (ae_of_all _ fun ω => mul_comm _ _)
  have hexp (ω : Ω) : ‖girardHutchinson A (X ω) - A.trace‖ ^ 2 =
      ((Fintype.card m : ℝ) ^ 2)⁻¹ * ∑ j, ∑ l, RCLike.re (Y j ω * star (Y l ω)) := by
    rw [hsum, norm_mul, mul_pow, hnorm (∑ j, Y j ω), star_sum, Finset.sum_mul_sum, map_sum]
    simp only [map_sum, norm_inv, RCLike.norm_natCast, inv_pow]
  simp only [hexp]
  rw [integral_const_mul, integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
    (hint j l).re]
  have hjl (j l : m) : ∫ ω, RCLike.re (Y j ω * star (Y l ω)) ∂μ = if j = l then v else 0 := by
    rw [integral_re (hint j l)]
    split_ifs with h
    · subst h
      rw [← integral_re (hint j j), ← hv j]
      exact integral_congr_ae (ae_of_all _ fun ω => (hnorm _).symm)
    · rw [integral_mul_star_eq_zero hind hX A h, map_zero]
  calc _ = ((Fintype.card m : ℝ) ^ 2)⁻¹ * ∑ j : m, ∑ l : m, if j = l then v else 0 := by
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_finsetSum _ fun l _ => (hint j l).re]
        exact Finset.sum_congr rfl fun l _ => hjl j l
    _ = _ := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul]
        have : (Fintype.card m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
        field_simp

/-- **The variance of the real Girard–Hutchinson estimator**: for $m$ independent isotropic real
probes whose single-probe estimates are square integrable with variance $v$,
$\operatorname{Var}[\mathsf{girardHutchinson}(\mathbf{A}, \mathbf{\Omega})] = v / m$. With the
single-probe variances of `NLAlib.variance_quadForm_of_hasLaw_gaussianVector`,
`NLAlib.variance_quadForm_of_hasLaw_rademacherVector` and
`NLAlib.variance_quadForm_sqrt_smul_of_hasLaw_uniformSphereVector`.
[Epperly2023, Variance]. -/
theorem variance_girardHutchinson [DecidableEq n] [Nonempty m] {X : Ω → Matrix n m ℝ}
    (hind : iIndepFun (fun j ω i => X ω i j) μ) (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ)
    {A : Matrix n n ℝ} (hL2 : ∀ j, MemLp (fun ω => quadForm A fun i => X ω i j) 2 μ) {v : ℝ}
    (hv : ∀ j, variance (fun ω => quadForm A fun i => X ω i j) μ = v) :
    variance (fun ω => girardHutchinson A (X ω)) μ = v / Fintype.card m := by
  have hGH : MemLp (fun ω => girardHutchinson A (X ω)) 2 μ := by
    have h1 : MemLp (fun ω => ∑ j, quadForm A fun i => X ω i j) 2 μ :=
      memLp_finsetSum _ fun j _ => hL2 j
    have he : (fun ω => girardHutchinson A (X ω)) =
        fun ω => (∑ j, quadForm A fun i => X ω i j) * (Fintype.card m : ℝ)⁻¹ := by
      funext ω
      rw [girardHutchinson_eq_sum, div_eq_mul_inv]
    rw [he]
    exact h1.mul_const _
  rw [variance_eq_integral hGH.aestronglyMeasurable.aemeasurable, integral_girardHutchinson hX]
  have h := integral_norm_girardHutchinson_sub_trace_sq hind hX hL2 (v := v) fun j => by
    rw [← hv j, variance_eq_integral (hL2 j).aestronglyMeasurable.aemeasurable,
      (hX j).integral_quadForm A]
    simp only [Real.norm_eq_abs, sq_abs]
  simpa only [Real.norm_eq_abs, sq_abs] using h

/-- **The Girard–Hutchinson estimator with orthonormal probes**: with the test matrix
$\sqrt{\lvert n \rvert}\,\mathbf{Q}$ for an $n \times k$ Haar frame $\mathbf{Q}$,
$1 \le \lvert k \rvert \le \lvert n \rvert$, $\lvert n \rvert \ge 2$, and real symmetric
$\mathbf{A}$,
$$\operatorname{Var}\bigl[\mathsf{girardHutchinson}(\mathbf{A},
\sqrt{\lvert n \rvert}\,\mathbf{Q})\bigr]
= \frac{2\lvert n \rvert(\lvert n \rvert - \lvert k \rvert)}
{\lvert k \rvert(\lvert n \rvert - 1)(\lvert n \rvert + 2)}
\Bigl(\|\mathbf{A}\|_{\mathsf{F}}^2 - \frac{(\operatorname{tr}\mathbf{A})^2}{\lvert n \rvert}
\Bigr)\,.$$
The probes are uniform on the sphere of radius $\sqrt{\lvert n \rvert}$ but not independent; the
factor $(\lvert n \rvert - \lvert k \rvert)/(\lvert n \rvert - 1)$ against $k$ independent sphere
probes is the gain from orthogonality, and the estimate is exact at $\lvert k \rvert =
\lvert n \rvert$. From `NLAlib.variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame`.
[Epperly2023, Uniform on the Real Sphere], there $\lvert k \rvert = 1$. -/
theorem variance_girardHutchinson_sqrt_smul_of_hasLaw_haarFrame {k : Type*} [Fintype k]
    [DecidableEq k] [Nonempty k] {X : Ω → Matrix n k ℝ} (hX : HasLaw X (haarFrame n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hn : 1 < Fintype.card n) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) :
    variance (fun ω => girardHutchinson A (√(Fintype.card n : ℝ) • X ω)) μ =
      2 * Fintype.card n * (Fintype.card n - Fintype.card k) /
          (Fintype.card k * (Fintype.card n - 1) * (Fintype.card n + 2)) *
        (frobNorm A ^ 2 - A.trace ^ 2 / Fintype.card n) := by
  have hGH (ω : Ω) : girardHutchinson A (√(Fintype.card n : ℝ) • X ω) =
      Fintype.card n / Fintype.card k * ((X ω)ᴴ * A * X ω).trace := by
    rw [girardHutchinson, Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul,
      smul_eq_mul, ← mul_assoc, Real.mul_self_sqrt (Nat.cast_nonneg _)]
    ring
  simp only [hGH]
  rw [variance_const_mul, variance_trace_conjTranspose_mul_mul_of_hasLaw_haarFrame hX hk hn hA]
  have hN : (1 : ℝ) < Fintype.card n := by exact_mod_cast hn
  have hK : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hN0 : (Fintype.card n : ℝ) ≠ 0 := by linarith
  have hN1 : (Fintype.card n : ℝ) - 1 ≠ 0 := by linarith
  have hN2 : (Fintype.card n : ℝ) + 2 ≠ 0 := by linarith
  field_simp

-- Stage TE-1

/-- The quadratic form of the stacked columns $\operatorname{vec}(\mathbf{X})$ in
$\mathbf{I}_m \otimes \mathbf{B}$ is the sum of the quadratic forms of the columns:
$\operatorname{vec}(\mathbf{X})^{\mathsf{H}}(\mathbf{I}_m \otimes \mathbf{B})
\operatorname{vec}(\mathbf{X}) = \sum_j \mathbf{x}_j^{\mathsf{H}}\mathbf{B}\mathbf{x}_j$. -/
private theorem quadForm_blockDiagonal_const [DecidableEq m] (B : Matrix n n 𝕜)
    (X : Matrix n m 𝕜) :
    quadForm (Matrix.blockDiagonal fun _ : m => B) (fun p => X p.1 p.2) =
      ∑ j, quadForm B fun i => X i j := by
  simp only [quadForm_def, dotProduct, Fintype.sum_prod_type_right]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type_right, Matrix.blockDiagonal_apply,
    ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp [Finset.sum_ite_eq]

/-- **The tail of the Girard–Hutchinson estimator with sub-Gaussian probes.** If the entries of
the real $n \times m$ test matrix $\mathbf{\Omega}$ are independent, each satisfies the
sub-Gaussian moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and
has second moment $1$, then for every real square $\mathbf{B}$ and every
$\tau \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\lvert \mathsf{girardHutchinson}(\mathbf{B}, \mathbf{\Omega}) -
\operatorname{tr}\mathbf{B} \rvert \ge \tau\bigr] \le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{m\tau^2}{c^2\|\mathbf{B}\|_{\mathsf{F}}^2}, \frac{m\tau}{c\|\mathbf{B}\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`. No symmetry of $\mathbf{B}$ is needed. Junk cases: with no
columns ($m = 0$) the estimate is $0$ and the bound is $2$; a zero denominator makes its fraction
$0$, and the bound is again $2$. The proof is Hanson–Wright
(`NLAlib.measureReal_abs_quadForm_sub_integral_ge_le`) for
$m \cdot \mathsf{girardHutchinson}(\mathbf{B}, \mathbf{\Omega}) =
\operatorname{vec}(\mathbf{\Omega})^{\mathsf{T}}(\mathbf{I}_m \otimes \mathbf{B})
\operatorname{vec}(\mathbf{\Omega})$, whose matrix has squared Frobenius norm
$m\|\mathbf{B}\|_{\mathsf{F}}^2$ and spectral norm $\|\mathbf{B}\|_2$.
[MeyerMuscoMuscoWoodruff2021, Lemma 2 and Appendix A]; there with unspecified constants, in the
sample-size form $m = O(\log(1/\delta)/\varepsilon^2)$ for
$\lvert \cdot \rvert \le \varepsilon\|\mathbf{B}\|_{\mathsf{F}}$.
Result: girard-hutchinson-tail -/
theorem measureReal_abs_girardHutchinson_sub_trace_ge_le {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) (B : Matrix n n ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |girardHutchinson B (X ω) - B.trace|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm B ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm B)))) := by
  classical
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty m with hm | hm
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul, zero_div, min_self, mul_zero,
      neg_zero, Real.exp_zero, mul_one]
    exact measureReal_le_one.trans one_le_two
  set x : Ω → n × m → ℝ := fun ω p => X ω p.1 p.2 with hx
  set M : Matrix (n × m) (n × m) ℝ := Matrix.blockDiagonal fun _ : m => B with hM
  have hiso : IsIsotropic x μ := IsIsotropic.of_iIndepFun hind (fun p => by
      simpa using (hsub p.1 p.2).memLp 2) (fun p => (hsub p.1 p.2).integral_eq_zero)
    fun p => by simpa only [Real.norm_eq_abs, sq_abs] using hvar p.1 p.2
  have hL : (0 : ℝ) < Fintype.card m := Nat.cast_pos.2 Fintype.card_pos
  have hmean : ∫ ω, quadForm M (x ω) ∂μ = Fintype.card m * B.trace := by
    rw [hiso.integral_quadForm, hM, Matrix.trace_blockDiagonal, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
  have hq (ω : Ω) : quadForm M (x ω) = Fintype.card m * girardHutchinson B (X ω) := by
    rw [hM, hx, quadForm_blockDiagonal_const, girardHutchinson_eq_sum]
    field_simp
  have hset : {ω | τ ≤ |girardHutchinson B (X ω) - B.trace|} =
      {ω | Fintype.card m * τ ≤ |quadForm M (x ω) - ∫ ω', quadForm M (x ω') ∂μ|} := by
    ext ω
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hmean, hq, ← mul_sub, abs_mul, Nat.abs_cast]
    exact (mul_le_mul_iff_of_pos_left hL).symm
  rw [hset]
  have h := measureReal_abs_quadForm_sub_integral_ge_le (x := x) hind (fun p => hsub p.1 p.2) M
    (mul_nonneg hL.le hτ)
  have hF : frobNorm M ^ 2 = Fintype.card m * frobNorm B ^ 2 := by
    rw [hM, frobNorm_blockDiagonal_const_sq]
  have hS : specNorm M = specNorm B := by rw [hM, specNorm_blockDiagonal_const]
  rw [hF, hS] at h
  convert h using 6
  rw [mul_pow, sq (Fintype.card m : ℝ), mul_assoc, mul_left_comm ((c : ℝ) ^ 2),
    mul_div_mul_left _ _ hL.ne']

end NLAlib
