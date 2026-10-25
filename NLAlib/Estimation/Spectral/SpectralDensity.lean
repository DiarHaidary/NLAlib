/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlib.Estimation.Trace.GirardHutchinson
public import NLAlib.Estimation.Trace.StochasticLanczosQuadrature
public import NLAlib.ForMathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import NLAlib.RandomMatrix.Haar.Sphere

/-!
# Spectral density estimation

Two random estimates of the empirical spectral measure $\nu_{\mathbf{A}}$ of a Hermitian
$\mathbf{A}$ from a test matrix $\mathbf{\Omega}$ whose $m$ columns are the probes. The **probe
spectral measure** is the average of the probes' spectral measures (probe densities)
$\mu_j = \mu_{\mathbf{A},\boldsymbol{\omega}_j}$, scaled by $1/(\lvert n\rvert m)$: its integral
of $f$ is the Girard–Hutchinson estimate of $\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$, and
for isotropic probes it is $\nu_{\mathbf{A}}$ in expectation. The **SLQ spectral-density
estimate** is the same average of the $q$-point Gauss rules of the probe densities, what $q$
Lanczos steps per probe compute: atoms at each probe's Ritz values. It is not the Gauss rule of
the probe spectral measure: it has up to $mq$ nodes and matches $2q$ moments of it. Neither is a
probability measure in general; their masses are
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$.
[ChenTrogdonUbaru2021]; [UbaruChenSaad2017].

The probe spectral measure integrates $f$ to the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$, so its distribution function at $x$ is a
Girard–Hutchinson estimate of a spectral projector; it is unbiased for isotropic probes. The SLQ
estimate is the average of the Lanczos rules, matches $2q$ moments of the probe spectral measure
and equals it for $q \ge \lvert n\rvert$. With independent sub-Gaussian entries, the distribution
functions of the probe spectral measure and of the empirical spectral measure are uniformly close
at the eigenvalues except with probability
$2\lvert n\rvert\exp(-\tfrac{1}{196}m\lvert n\rvert\min(\tau^2/c^2, \tau/c))$, and on that event a
finite Abel summation bounds the error on every Lipschitz test function at once, for the probe
measure, for SLQ (adding the Gauss error) and for the mass-normalised SLQ measure. With probes
$\sqrt{\lvert n\rvert}\,\mathbf{u}_j$, $\mathbf{u}_j$ independent and uniform on the unit
sphere, both measures are probability measures and the sharp Beta proxy gives the failure
probability $2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)$, with no unknown constant.
[ChenTrogdonUbaru2025]. Design: `docs/design/Estimation-SLQ.md` §§3.3–3.6.

## Main definitions

* `NLAlib.probeSpectralMeasure`: the average of the probe densities.
* `NLAlib.slqMeasure`: the average of their Gauss rules.

## Main results

* `NLAlib.isFiniteMeasure_probeSpectralMeasure`, `NLAlib.isFiniteMeasure_slqMeasure`: both are
  finite measures.
* `NLAlib.integral_probeSpectralMeasure`, `NLAlib.integral_slqMeasure`: the integrals are the
  Girard–Hutchinson and SLQ trace estimates, divided by $\lvert n\rvert$.
* `Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature`: the SLQ measure is what the Lanczos
  algorithm computes.
* `NLAlib.probeSpectralMeasure_real`: the probe spectral measure of a set is a Girard–Hutchinson
  estimate.
* `Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure`,
  `Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le`: moment matching and
  exactness.
* `NLAlib.integral_integral_probeSpectralMeasure`: unbiasedness for isotropic probes.
* `Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le`:
  the deterministic bound over Lipschitz test functions.
* `NLAlib.measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le`:
  the Kolmogorov-distance tail.
* `NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`:
  SLQ approximates the spectral density uniformly in Lipschitz test functions; its asymptotic
  form and the mass-normalised form follow it.
* The same with sphere probes: the tails at one set and at every eigenvalue, the Lipschitz tail,
  the sample size and its asymptotic form (the last section; the names are too long for this
  list).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix NNReal ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The **probe spectral measure**: the average of the probes' spectral measures (probe
densities), scaled so that isotropic probes give the empirical spectral measure in expectation,
$$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) :=
\frac{1}{\lvert n\rvert m}\sum_{j=1}^m \mu_{\mathbf{A},\boldsymbol{\omega}_j}\,,$$
$\boldsymbol{\omega}_1, \dots, \boldsymbol{\omega}_m$ the columns of $\mathbf{\Omega}$. It is SLQ
with exact quadrature (`Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le`); its
integral of $f$ is the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$ (`integral_probeSpectralMeasure`). Mass
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$. Junk value: $0$ when $n$ or $m$ is empty
($0^{-1} = 0$ in $\mathbb{R}_{\ge 0}$) and when $\mathbf{A}$ is not Hermitian.
[ChenTrogdonUbaru2021, §2] (locator to check). -/
noncomputable def probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) • ∑ j, spectralMeasure A (fun i => Ω i j)

/-- The **SLQ spectral-density estimate**: the average, scaled as `probeSpectralMeasure`, of the
$q$-point Gauss rules of the probe densities,
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) := \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{gaussQuadrature}(\mu_{\mathbf{A},\boldsymbol{\omega}_j}, q)\,,$$
$\boldsymbol{\omega}_1, \dots, \boldsymbol{\omega}_m$ the columns of $\mathbf{\Omega}$. It is not
the Gauss rule of `probeSpectralMeasure`: it has up to $mq$ nodes and matches $2q$ moments of it.
For Hermitian $\mathbf{A}$ it is the average of the Lanczos rules, atoms at each probe's Ritz
values (`Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature`). Its integral of $f$ is
$\operatorname{Re}\,\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)/\lvert n\rvert$
(`integral_slqMeasure`). Junk value: $0$ when $n$ or $m$ is empty or $q = 0$.
[ChenTrogdonUbaru2021, §2] (locator to check); [UbaruChenSaad2017, §3] (locator to check). -/
noncomputable def slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) : Measure ℝ :=
  ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) •
    ∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q

/-- The probe spectral measure is a finite measure (the definition is not reducible, so the
instances for sums and scalar multiples are not found through it). -/
instance isFiniteMeasure_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    IsFiniteMeasure (probeSpectralMeasure A Ω) := by
  unfold probeSpectralMeasure
  infer_instance

/-- The SLQ spectral-density estimate is a finite measure. -/
instance isFiniteMeasure_slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) :
    IsFiniteMeasure (slqMeasure A Ω q) := by
  unfold slqMeasure
  infer_instance

/-! ### Integrals and the Lanczos form -/

private lemma re_div_natCast (z : 𝕜) (k : ℕ) : RCLike.re (z / (k : 𝕜)) = RCLike.re z / k := by
  rw [← RCLike.ofReal_natCast, RCLike.div_re_ofReal]

/-- The real spectrum lies in a compact interval. -/
private lemma exists_spectrum_subset_Icc (A : Matrix n n 𝕜) :
    ∃ a a' : ℝ, spectrum ℝ A ⊆ Set.Icc a a' := by
  obtain ⟨a, ha⟩ := A.finite_real_spectrum.bddBelow
  obtain ⟨a', ha'⟩ := A.finite_real_spectrum.bddAbove
  exact ⟨a, a', fun x hx => ⟨ha hx, ha' hx⟩⟩

/-- Every function is integrable against the probe spectral measure: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$ and every $f : \mathbb{R} \to \mathbb{R}$, $f$
is integrable against `probeSpectralMeasure A Ω`, a finite atomic measure. -/
theorem integrable_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (f : ℝ → ℝ) :
    Integrable f (probeSpectralMeasure A Ω) := by
  unfold probeSpectralMeasure
  exact (integrable_finsetSum_measure.2 fun j _ =>
    integrable_spectralMeasure _ _ f).smul_measure_nnreal

/-- Every function is integrable against the SLQ spectral-density estimate: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$, every $q$ and every
$f : \mathbb{R} \to \mathbb{R}$, $f$ is integrable against `slqMeasure A Ω q`, a finite sum of
Dirac masses. -/
theorem integrable_slqMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (q : ℕ) (f : ℝ → ℝ) :
    Integrable f (slqMeasure A Ω q) := by
  unfold slqMeasure
  exact (integrable_finsetSum_measure.mpr fun j _ =>
    integrable_gaussQuadrature _ _ _).smul_measure_nnreal

/-- The probe spectral measure integrates every $f$ to the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$: for every square $\mathbf{A}$, every
$f : \mathbb{R} \to \mathbb{R}$ and every test matrix $\mathbf{\Omega}$,
$$\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) =
\frac{\operatorname{Re}\,\mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})}{\lvert n\rvert}\,;$$
both sides vanish off Hermitian. With $f = T_k$ these are the moments of the kernel polynomial
method. -/
theorem integral_probeSpectralMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) :
    ∫ x, f x ∂probeSpectralMeasure A Ω =
      RCLike.re (girardHutchinson (cfc f A) Ω) / Fintype.card n := by
  unfold probeSpectralMeasure
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure, girardHutchinson_eq_sum,
    re_div_natCast,
    map_sum]
  · simp only [integral_spectralMeasure, NNReal.smul_def, smul_eq_mul, NNReal.coe_inv,
      NNReal.coe_mul, NNReal.coe_natCast]
    ring
  · exact fun i _ => integrable_spectralMeasure _ _ _

/-- The SLQ spectral-density estimate integrates every $f$ to the SLQ trace estimate divided by
$\lvert n\rvert$: for every square $\mathbf{A}$, every $f : \mathbb{R} \to \mathbb{R}$, every
test matrix $\mathbf{\Omega}$ and every $q$,
$$\int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) =
\frac{\operatorname{Re}\,\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)}{\lvert n\rvert}\,.$$ -/
theorem integral_slqMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ∫ x, f x ∂slqMeasure A Ω q = RCLike.re (slq A f Ω q) / Fintype.card n := by
  unfold slqMeasure slq
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure]
  · rw [← RCLike.ofReal_natCast (Fintype.card m), ← RCLike.ofReal_div, RCLike.ofReal_re]
    simp only [NNReal.smul_def, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast, smul_eq_mul]
    field_simp
  · exact fun j _ => integrable_gaussQuadrature _ _ _

/-- **The SLQ measure is the average of the probes' Lanczos rules**: for Hermitian $\mathbf{A}$,
every test matrix $\mathbf{\Omega}$ with columns $\boldsymbol{\omega}_j$ and every $q$,
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) = \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{lanczosQuadrature}(\mathbf{A}, \boldsymbol{\omega}_j, q)\,,$$
the identification of each probe's Gauss rule with its Lanczos rule; atoms at the Ritz values,
weights from the tridiagonal matrices (`Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`). -/
theorem _root_.Matrix.IsHermitian.slqMeasure_eq_sum_lanczosQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) (q : ℕ) :
    slqMeasure A Ω q = ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹) •
      ∑ j, lanczosQuadrature A (fun i => Ω i j) q := by
  unfold slqMeasure
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  exact (hA.lanczosQuadrature_eq_gaussQuadrature _ q).symm

/-! ### Distribution functions, masses and supports -/

/-- The probe spectral measure of every set is a Girard–Hutchinson estimate: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$ and every $S \subseteq \mathbb{R}$,
$$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(S) =
\frac{\operatorname{Re}\,\mathsf{girardHutchinson}(\mathbf{1}_S(\mathbf{A}),
\mathbf{\Omega})}{\lvert n\rvert}\,,$$
$\mathbf{1}_S(\mathbf{A})$ the spectral projector of $S$, an orthogonal projector
(`isStarProjection_cfc_indicator`). No measurability of $S$ is needed. -/
theorem probeSpectralMeasure_real (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (S : Set ℝ) :
    (probeSpectralMeasure A Ω).real S =
      RCLike.re (girardHutchinson (cfc (S.indicator fun _ => (1 : ℝ)) A) Ω) /
        Fintype.card n := by
  unfold probeSpectralMeasure
  rw [measureReal_def, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_smul, ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)]
  simp only [← measureReal_def, spectralMeasure_real, girardHutchinson_eq_sum, Finset.sum_div,
    map_sum]
  simp only [re_div_natCast, Finset.smul_sum, NNReal.smul_def, smul_eq_mul,
    NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- The mass of the probe spectral measure: for Hermitian $\mathbf{A}$ and every test matrix
$\mathbf{\Omega}$,
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(\mathbb{R}) =
\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$. -/
theorem _root_.Matrix.IsHermitian.probeSpectralMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) :
    (probeSpectralMeasure A Ω).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m) := by
  unfold probeSpectralMeasure
  simp only [Measure.real, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply,
    ENNReal.toReal_smul, ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)]
  have h : ∑ j, ((spectralMeasure A fun i => Ω i j) Set.univ).toReal = frobNorm Ω ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    exact Finset.sum_congr rfl fun j _ => hA.spectralMeasure_real_univ (fun i => Ω i j)
  rw [h, NNReal.smul_def, NNReal.coe_inv, NNReal.coe_mul, smul_eq_mul, div_eq_inv_mul]
  push_cast
  rfl

/-- The mass of the SLQ spectral-density estimate: for Hermitian $\mathbf{A}$, every test matrix
$\mathbf{\Omega}$ and $q > 0$,
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)(\mathbb{R}) =
\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$, the mass of the probe spectral measure. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ} (hq : 0 < q) :
    (slqMeasure A Ω q).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m) := by
  obtain ⟨a, a', hs⟩ := exists_spectrum_subset_Icc A
  have hg : ∀ j, (gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q).real Set.univ =
      ‖WithLp.toLp 2 (Ω.col j)‖ ^ 2 := fun j => by
    rw [gaussQuadrature_real_univ (ae_mem_Icc_spectralMeasure A hs _) hq,
      hA.spectralMeasure_real_univ]
    rfl
  have hsum : (∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q).real Set.univ =
      ∑ j, (gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q).real Set.univ := by
    simp only [measureReal_def, Measure.coe_finsetSum, Finset.sum_apply,
      ENNReal.toReal_sum (fun j _ => measure_ne_top _ _)]
  unfold slqMeasure
  rw [measureReal_nnreal_smul_apply, hsum, Finset.sum_congr rfl fun j _ => hg j,
    ← frobNorm_sq_eq_sum_col, NNReal.coe_inv, NNReal.coe_mul]
  push_cast
  ring

/-- The probe spectral measure lives on the spectrum: for every square $\mathbf{A}$ and every
test matrix $\mathbf{\Omega}$, almost every point of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ is an eigenvalue of $\mathbf{A}$. -/
theorem ae_mem_spectrum_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ spectrum ℝ A := by
  unfold probeSpectralMeasure
  rw [ae_iff, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_zero]
  right
  exact Finset.sum_eq_zero fun j _ => spectralMeasure_compl_spectrum_eq_zero A _

/-- The probe spectral measure lives in every interval containing the spectrum: for every square
$\mathbf{A}$ with spectrum in $[a, a']$ and every test matrix $\mathbf{\Omega}$, almost every
point of $\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ lies in $[a, a']$. -/
theorem ae_mem_Icc_probeSpectralMeasure (A : Matrix n n 𝕜) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ Set.Icc a a' := by
  filter_upwards [ae_mem_spectrum_probeSpectralMeasure A Ω] with x hx
  exact hs hx

-- hA is unused (compiler and environment linters); see decision UNUSED-HA
set_option linter.unusedVariables false in
/-- The SLQ spectral-density estimate lives in every interval containing the spectrum: for
Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, every test matrix $\mathbf{\Omega}$ and every
$q$, almost every point of $\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)$ lies in
$[a, a']$: the Ritz values lie between the extreme eigenvalues. -/
@[nolint unusedArguments]
theorem _root_.Matrix.IsHermitian.ae_mem_Icc_slqMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜)
    (q : ℕ) : ∀ᵐ x ∂slqMeasure A Ω q, x ∈ Set.Icc a a' := by
  have hprobe : ∀ j, ∀ᵐ x ∂spectralMeasure A (fun i => Ω i j), x ∈ Set.Icc a a' :=
    fun j => ae_mem_Icc_spectralMeasure A hs _
  have hgauss : ∀ j, ∀ᵐ x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q,
      x ∈ Set.Icc a a' := fun j => ae_mem_Icc_gaussQuadrature (hprobe j) q
  have hsum : ∀ᵐ x ∂(∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q),
      x ∈ Set.Icc a a' := by
    simp only [ae_iff, Measure.coe_finsetSum, Finset.sum_apply] at hgauss ⊢
    exact Finset.sum_eq_zero fun j _ => hgauss j
  unfold slqMeasure
  rw [ae_iff] at hsum ⊢
  rw [Measure.smul_apply, hsum, smul_zero]

/-! ### Moments and exactness -/

/-- A Hermitian matrix has at most $\lvert n\rvert$ distinct eigenvalues. -/
private lemma _root_.Matrix.IsHermitian.card_toFinset_spectrum_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) : A.finite_real_spectrum.toFinset.card ≤ Fintype.card n := by
  have hfin : A.finite_real_spectrum.toFinset = Finset.univ.image hA.eigenvalues := by
    ext x
    simp [hA.spectrum_real_eq_range_eigenvalues]
  rw [hfin]
  exact Finset.card_image_le.trans_eq Finset.card_univ

-- hA is unused (compiler and environment linters); see decision UNUSED-HA
set_option linter.unusedVariables false in
/-- **SLQ matches $2q$ moments of the probe spectral measure**: for Hermitian $\mathbf{A}$, every
test matrix $\mathbf{\Omega}$ and every $q$,
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ and
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)$ give every real polynomial of degree less
than $2q$ the same integral: each probe density matches $2q$ moments of its Gauss rule, and the
averages match. [Gautschi2004, Theorem 1.45]; [GolubMeurant2010, Ch. 6]; there for one measure,
here probe by probe and averaged.
Result: gauss-quadrature -/
@[nolint unusedArguments]
theorem _root_.Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) (q : ℕ) :
    MatchesMoments (probeSpectralMeasure A Ω) (slqMeasure A Ω q) (2 * q) := by
  obtain ⟨a, a', hs⟩ := exists_spectrum_subset_Icc A
  have hprobe : ∀ j, ∀ᵐ x ∂spectralMeasure A (fun i => Ω i j), x ∈ Set.Icc a a' :=
    fun j => ae_mem_Icc_spectralMeasure A hs _
  have hper : ∀ j, MatchesMoments (spectralMeasure A (fun i => Ω i j))
      (gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q) (2 * q) :=
    fun j => matchesMoments_gaussQuadrature (hprobe j) q
  have hsum : MatchesMoments (∑ j, spectralMeasure A (fun i => Ω i j))
      (∑ j, gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q) (2 * q) :=
    MatchesMoments.finsetSum (fun j _ => hprobe j)
      (fun j _ => ae_mem_Icc_gaussQuadrature (hprobe j) q) (fun j _ => hper j)
  unfold probeSpectralMeasure slqMeasure
  exact MatchesMoments.smul hsum _

/-- With at least $\lvert n\rvert$ nodes SLQ is exact: for Hermitian $\mathbf{A}$, every test
matrix $\mathbf{\Omega}$ and $q \ge \lvert n\rvert$,
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) =
\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$: each probe density lives on at most
$\lvert n\rvert \le q$ points, so it is its own $q$-point Gauss rule. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ}
    (hq : Fintype.card n ≤ q) : slqMeasure A Ω q = probeSpectralMeasure A Ω := by
  obtain ⟨a, a', hs⟩ := exists_spectrum_subset_Icc A
  have hcard := (hA.card_toFinset_spectrum_le).trans hq
  unfold slqMeasure probeSpectralMeasure
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  symm
  refine MatchesMoments.eq_gaussQuadrature (a := a) (b := a') (MatchesMoments.refl _ _)
    ?_ ?_ hcard
  · exact ae_mem_Icc_spectralMeasure A hs _
  · have h0 := spectralMeasure_compl_spectrum_eq_zero A (fun i => Ω i j)
    exact (ae_iff.mpr h0).mono fun x hx => by simpa using hx

/-! ### Unbiasedness -/

/-- **The probe spectral measure is unbiased**: if every probe (column of the random test matrix
$\mathbf{\Omega}$) is isotropic and $m$ is nonempty, then for Hermitian $\mathbf{A}$ and every
$f : \mathbb{R} \to \mathbb{R}$,
$$\mathbb{E}\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) =
\int f\,d\nu_{\mathbf{A}}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure. No independence of the probes is needed:
Gaussian, sign, and $\sqrt{\lvert n\rvert}$ times uniform-sphere or Haar-frame probes are
instances. With $f = \mathbf{1}_S$, the expected measure of every Borel set is
$\nu_{\mathbf{A}}(S)$. [ChenTrogdonUbaru2021, §3] (locator to check).
Result: probe-spectral-measure-unbiased -/
theorem integral_integral_probeSpectralMeasure [Nonempty m] {X : Ω → Matrix n m 𝕜}
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    ∫ ω, (∫ x, f x ∂probeSpectralMeasure A (X ω)) ∂μ = ∫ x, f x ∂empiricalSpectralMeasure A := by
  have hint : Integrable (fun ω => girardHutchinson (cfc f A) (X ω)) μ := by
    simp only [girardHutchinson_eq_sum]
    exact (integrable_finsetSum _ fun j _ => (hX j).integrable_quadForm (cfc f A)).div_const _
  calc ∫ ω, (∫ x, f x ∂probeSpectralMeasure A (X ω)) ∂μ
      = ∫ ω, RCLike.re (girardHutchinson (cfc f A) (X ω)) / Fintype.card n ∂μ := by
        simp only [integral_probeSpectralMeasure]
    _ = (∫ ω, RCLike.re (girardHutchinson (cfc f A) (X ω)) ∂μ) / Fintype.card n :=
        integral_div _ _
    _ = RCLike.re (∫ ω, girardHutchinson (cfc f A) (X ω) ∂μ) / Fintype.card n := by
        rw [integral_re hint]
    _ = RCLike.re (cfc f A).trace / Fintype.card n := by
        rw [integral_girardHutchinson hX]
    _ = ∫ x, f x ∂empiricalSpectralMeasure A := (hA.integral_empiricalSpectralMeasure f).symm

/-! ### Deterministic bounds over Lipschitz test functions -/

omit [DecidableEq n] in
private lemma isFiniteMeasure_empiricalSpectralMeasure_aux (A : Matrix n n 𝕜) :
    IsFiniteMeasure (empiricalSpectralMeasure A) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · unfold empiricalSpectralMeasure
    simp only [Fintype.card_eq_zero, Finset.range_zero, Finset.sum_empty, smul_zero]
    infer_instance
  · infer_instance

/-- **Distribution functions control Lipschitz test functions.** For Hermitian $\mathbf{A}$ with
spectrum in $[a, b]$, $a \le b$, a test matrix $\mathbf{\Omega}$ and $\tau \ge 0$: if at every
eigenvalue $x$ the distribution functions of $\nu_{\mathbf{A}}$ (the empirical spectral measure)
and of $\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$,
then every $f$ that is $L$-Lipschitz on $[a, b]$ has
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} -
\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})\Bigr\rvert \le
(\lvert f(b)\rvert + L(b - a))\tau\,.$$ -/
theorem
_root_.Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a ≤ b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂probeSpectralMeasure A Ω| ≤
      (|f b| + L * (b - a)) * τ := by
  have := isFiniteMeasure_empiricalSpectralMeasure_aux A
  exact MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith
    (by
      filter_upwards [hA.ae_mem_spectrum_empiricalSpectralMeasure] with x hx
      exact A.finite_real_spectrum.mem_toFinset.2 hx)
    (by
      filter_upwards [ae_mem_spectrum_probeSpectralMeasure A Ω] with x hx
      exact A.finite_real_spectrum.mem_toFinset.2 hx)
    (fun x hx => hs (A.finite_real_spectrum.mem_toFinset.1 hx)) hab hf hτ
    (fun x hx => hK x (A.finite_real_spectrum.mem_toFinset.1 hx))

/-- **The Kolmogorov event controls the mass**: for Hermitian $\mathbf{A}$, $n$ nonempty, and a
test matrix $\mathbf{\Omega}$: if at every eigenvalue the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$, then
$\lvert 1 - \mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(\mathbb{R})\rvert \le
\tau$, the mass being $\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$: at the largest
eigenvalue both distribution functions equal the masses. -/
theorem _root_.Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ}
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) :
    |1 - (probeSpectralMeasure A Ω).real Set.univ| ≤ τ := by
  classical
  have hpos : 0 < Fintype.card n := Fintype.card_pos
  have hx : eigenvalue A 0 ∈ spectrum ℝ A := hA.eigenvalue_mem_spectrum hpos
  have hle : ∀ y ∈ spectrum ℝ A, y ≤ eigenvalue A 0 := by
    rw [hA.spectrum_eq_image_eigenvalue]
    rintro _ ⟨k, hk, rfl⟩
    exact hA.eigenvalue_le_eigenvalue (Nat.zero_le k) (Set.mem_Iio.mp hk)
  have h1 : (empiricalSpectralMeasure A).real (Set.Iic (eigenvalue A 0)) = 1 :=
    (measureReal_congr (Filter.eventuallyEq_set.2
      ((hA.ae_mem_spectrum_empiricalSpectralMeasure).mono fun y hy =>
        ⟨fun _ => Set.mem_univ _, fun _ => hle y hy⟩))).trans probReal_univ
  have h2 : (probeSpectralMeasure A Ω).real (Set.Iic (eigenvalue A 0)) =
      (probeSpectralMeasure A Ω).real Set.univ :=
    measureReal_congr (Filter.eventuallyEq_set.2
      ((ae_mem_spectrum_probeSpectralMeasure A Ω).mono fun y hy =>
        ⟨fun _ => Set.mem_univ _, fun _ => hle y hy⟩))
  have := hK _ hx
  rwa [h1, h2] at this

/-- From the eigenvalues to every threshold: for Hermitian $\mathbf{A}$, a test matrix
$\mathbf{\Omega}$ and $\tau \ge 0$, if at every eigenvalue the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$, then they
differ by at most $\tau$ at every $x \in \mathbb{R}$: both are constant between eigenvalues and
$0$ below the smallest. -/
theorem
_root_.Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) (x : ℝ) :
    |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ := by
  -- both measures live on the spectrum, so sets agreeing there have the same mass
  have hcongr : ∀ (μ : Measure ℝ) (S T : Set ℝ), (∀ᵐ y ∂μ, y ∈ spectrum ℝ A) →
      (∀ y ∈ spectrum ℝ A, y ∈ S ↔ y ∈ T) → μ.real S = μ.real T := by
    intro μ S T hμ hST
    refine MeasureTheory.measureReal_congr (Filter.eventuallyEq_set.2 ?_)
    filter_upwards [hμ] with y hy
    exact hST y hy
  have hE : ∀ᵐ y ∂empiricalSpectralMeasure A, y ∈ spectrum ℝ A :=
    hA.ae_mem_spectrum_empiricalSpectralMeasure
  have hP : ∀ᵐ y ∂probeSpectralMeasure A Ω, y ∈ spectrum ℝ A :=
    ae_mem_spectrum_probeSpectralMeasure A Ω
  by_cases hex : ∃ y ∈ spectrum ℝ A, y ≤ x
  · -- x' is the largest eigenvalue ≤ x; Iic x and Iic x' agree on the spectrum
    set F := A.finite_real_spectrum.toFinset.filter (· ≤ x) with hF
    have hne : F.Nonempty := by
      obtain ⟨y, hy, hyx⟩ := hex
      exact ⟨y, Finset.mem_filter.2 ⟨A.finite_real_spectrum.mem_toFinset.2 hy, hyx⟩⟩
    have hmem := Finset.mem_filter.1 (F.max'_mem hne)
    have hmax : ∀ y ∈ spectrum ℝ A, y ≤ x ↔ y ≤ F.max' hne := by
      intro y hy
      exact ⟨fun hyx => Finset.le_max' _ _
          (Finset.mem_filter.2 ⟨A.finite_real_spectrum.mem_toFinset.2 hy, hyx⟩),
        fun h => le_trans h hmem.2⟩
    have hx' : F.max' hne ∈ spectrum ℝ A := A.finite_real_spectrum.mem_toFinset.1 hmem.1
    rw [hcongr _ (Set.Iic x) (Set.Iic (F.max' hne)) hE (fun y hy => by simpa using hmax y hy),
      hcongr _ (Set.Iic x) (Set.Iic (F.max' hne)) hP (fun y hy => by simpa using hmax y hy)]
    exact hK _ hx'
  · -- no eigenvalue is ≤ x: both masses of Iic x vanish
    have hno : ∀ y ∈ spectrum ℝ A, y ∉ Set.Iic x := fun y hy h => hex ⟨y, hy, h⟩
    rw [hcongr _ (Set.Iic x) ∅ hE (fun y hy => by simp [hno y hy]),
      hcongr _ (Set.Iic x) ∅ hP (fun y hy => by simp [hno y hy])]
    simpa using hτ

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The quadrature term, uniformly in Lipschitz test functions.** For Hermitian $\mathbf{A}$
with spectrum in $[a, b]$, $a < b$, every test matrix $\mathbf{\Omega}$, every $q$, and every $f$
that is $L$-Lipschitz on $[a, b]$, <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega}) -
\int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q + 1)\Bigr\rvert \le
\frac{\pi L(b - a)}{2q + 3}\cdot\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{\lvert n\rvert m}\,;$$
the constant is `jacksonApproximationConstant`. Per probe, the Gauss-rule error for Lipschitz
functions (Jackson's polynomial of degree $2q + 1$) is at most
$\pi L(b - a)\mu_j(\mathbb{R})/(2q + 3)$, $\mu_j$ the probe density; averaging gives the bound.
[ChenTrogdonUbaru2025, the uniform quadrature bound] (locator to check);
[ChenTrogdonUbaru2022, Appendix C, Theorem 38], the approximation step. -/
theorem
_root_.Matrix.IsHermitian.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m 𝕜) (q : ℕ) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂probeSpectralMeasure A Ω - ∫ x, f x ∂slqMeasure A Ω (q + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
        (frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m)) := by
  have hper : ∀ j ∈ Finset.univ,
      |∫ x, f x ∂spectralMeasure A (fun i => Ω i j) -
        ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) (q + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
        (spectralMeasure A (fun i => Ω i j)).real Set.univ := fun j _ =>
    abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith
      (ae_mem_Icc_spectralMeasure A hs _) hab hf q
  have hP : ∫ x, f x ∂probeSpectralMeasure A Ω =
      ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
        ∑ j, ∫ x, f x ∂spectralMeasure A (fun i => Ω i j) := by
    unfold probeSpectralMeasure
    rw [integral_smul_nnreal_measure, integral_finsetSum_measure fun j _ =>
      integrable_spectralMeasure _ _ _]
    simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
  have hQ : ∫ x, f x ∂slqMeasure A Ω (q + 1) =
      ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
        ∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) (q + 1) := by
    unfold slqMeasure
    rw [integral_smul_nnreal_measure, integral_finsetSum_measure fun j _ =>
      integrable_gaussQuadrature _ _ _]
    simp only [NNReal.smul_def, smul_eq_mul, NNReal.coe_inv]
  have hmass : ∑ j, (spectralMeasure A (fun i => Ω i j)).real Set.univ = frobNorm Ω ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    exact Finset.sum_congr rfl fun j _ => hA.spectralMeasure_real_univ _
  rw [hP, hQ, ← mul_sub, ← Finset.sum_sub_distrib, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ))]
  calc ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
        |∑ j, (∫ x, f x ∂spectralMeasure A (fun i => Ω i j) -
          ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) (q + 1))|
      ≤ ((Fintype.card n * Fintype.card m : ℝ≥0)⁻¹ : ℝ) *
          ∑ j, jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
            (spectralMeasure A (fun i => Ω i j)).real Set.univ := by
        gcongr
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hper)
    _ = jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
          (frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m)) := by
        rw [← Finset.mul_sum, hmass]
        push_cast
        ring

/-! ### Tails with independent sub-Gaussian entries -/

/-- The exponent of the Girard–Hutchinson tail dominates the exponent of the spectral tail: if
$F^2 \le 1/N$ and $S \le 1/N$ with $F, S > 0$, then $M N \min(\tau^2/c^2, \tau/c)$ is at most
$\min(M\tau^2/(c^2F^2), M\tau/(cS))$. -/
private lemma card_mul_min_le_min_girardHutchinson {M N τ c F S : ℝ} (hM : 0 ≤ M) (hN : 0 < N)
    (hc : 0 < c) (hτ : 0 ≤ τ) (hF : 0 < F) (hS : 0 < S) (hF2 : F ^ 2 ≤ 1 / N) (hS1 : S ≤ 1 / N) :
    M * N * min (τ ^ 2 / c ^ 2) (τ / c) ≤ min (M * τ ^ 2 / (c ^ 2 * F ^ 2)) (M * τ / (c * S)) := by
  have hNF : N * F ^ 2 ≤ 1 := (le_div_iff₀' hN).1 hF2
  have hNS : N * S ≤ 1 := (le_div_iff₀' hN).1 hS1
  refine le_min ?_ ?_
  · rw [le_div_iff₀ (by positivity)]
    calc M * N * min (τ ^ 2 / c ^ 2) (τ / c) * (c ^ 2 * F ^ 2)
        ≤ M * N * (τ ^ 2 / c ^ 2) * (c ^ 2 * F ^ 2) := by
          gcongr
          exact min_le_left _ _
      _ = M * τ ^ 2 * (N * F ^ 2) := by field_simp
      _ ≤ M * τ ^ 2 * 1 := by gcongr
      _ = M * τ ^ 2 := mul_one _
  · rw [le_div_iff₀ (by positivity)]
    calc M * N * min (τ ^ 2 / c ^ 2) (τ / c) * (c * S)
        ≤ M * N * (τ / c) * (c * S) := by
          gcongr
          exact min_le_right _ _
      _ = M * τ * (N * S) := by field_simp
      _ ≤ M * τ * 1 := by gcongr
      _ = M * τ := mul_one _

/-- **The distribution of the probe spectral measure, at one set.** Let the entries of the real
$n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and having second
moment $1$. Then for real symmetric $\mathbf{A}$, every $S \subseteq \mathbb{R}$ and every
$\tau \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\bigl[\tau \le \lvert\nu_{\mathbf{A}}(S) - \mathsf{probeSpectralMeasure}(\mathbf{A},
\mathbf{\Omega})(S)\rvert\bigr] \le 2\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert
\min\Bigl(\frac{\tau^2}{c^2}, \frac{\tau}{c}\Bigr)\Bigr)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant is `hansonWrightConstant`. The
error is that of Girard–Hutchinson on $\mathbf{1}_S(\mathbf{A})/\lvert n\rvert$, a projector
divided by $\lvert n\rvert$, of squared Frobenius norm at most $1/\lvert n\rvert$ and spectral
norm at most $1/\lvert n\rvert$; the factor $\lvert n\rvert$ in the exponent is the "dimension
helps" effect. -/
theorem measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (S : Set ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
        (probeSpectralMeasure A (X ω)).real S|} ≤
      2 * Real.exp (-(hansonWrightConstant * (Fintype.card m * Fintype.card n *
        min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have := hind.isProbabilityMeasure
  set P : Matrix n n ℝ := cfc (S.indicator fun _ => (1 : ℝ)) A with hPdef
  have hP : IsStarProjection P := isStarProjection_cfc_indicator A S
  set B : Matrix n n ℝ := (1 / (Fintype.card n : ℝ)) • P with hBdef
  have hset : {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
      (probeSpectralMeasure A (X ω)).real S|} =
      {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hBdef, hPdef, hA.empiricalSpectralMeasure_real,
      probeSpectralMeasure_real, girardHutchinson_smul, Matrix.trace_smul, smul_eq_mul,
      RCLike.re_to_real]
    ring_nf
  rw [hset]
  -- for `τ = 0` or `c = 0` the bound is `2`
  have h2 : μ.real {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|} ≤ 2 :=
    measureReal_le_one.trans one_le_two
  rcases eq_or_lt_of_le hτ with rfl | hτpos
  · simp
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using h2
  have hc' : (0:ℝ) < c := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  by_cases hB : B = 0
  · have hempty : {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|} = ∅ := by
      ext ω
      simp [hB, girardHutchinson, not_le.2 hτpos]
    rw [hempty, measureReal_empty]
    positivity
  have hN : (0:ℝ) < Fintype.card n := by
    refine Nat.cast_pos.2 (Fintype.card_pos_iff.2 (not_isEmpty_iff.1 fun _ => ?_))
    exact hB (Subsingleton.elim _ _)
  have hF : 0 < frobNorm B :=
    lt_of_le_of_ne (frobNorm_nonneg _) (fun h => hB (frobNorm_eq_zero_iff.1 h.symm))
  have hS : 0 < specNorm B :=
    lt_of_le_of_ne (specNorm_nonneg _) (fun h => hB (specNorm_eq_zero_iff.1 h.symm))
  have hF2 : frobNorm B ^ 2 ≤ 1 / (Fintype.card n : ℝ) := by
    rw [hBdef, frobNorm_smul, mul_pow, hP.frobNorm_sq_eq_rank,
      Real.norm_of_nonneg (by positivity)]
    have hr : (P.rank : ℝ) ≤ Fintype.card n := by exact_mod_cast Matrix.rank_le_card_width P
    calc (1 / (Fintype.card n : ℝ)) ^ 2 * (P.rank : ℝ) ≤ (1 / (Fintype.card n : ℝ)) ^ 2 *
          (Fintype.card n : ℝ) := by gcongr
      _ = 1 / (Fintype.card n : ℝ) := by field_simp
  have hS1 : specNorm B ≤ 1 / (Fintype.card n : ℝ) := by
    rw [hBdef, specNorm_smul, Real.norm_of_nonneg (by positivity)]
    exact mul_le_of_le_one_right (by positivity) hP.specNorm_le_one
  have hmin := card_mul_min_le_min_girardHutchinson (M := (Fintype.card m : ℝ))
    (Nat.cast_nonneg _) hN hc' hτ hF hS hF2 hS1
  calc μ.real {ω | τ ≤ |B.trace - girardHutchinson B (X ω)|}
      ≤ 2 * Real.exp (-(hansonWrightConstant *
          min ((Fintype.card m : ℝ) * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm B ^ 2))
            ((Fintype.card m : ℝ) * τ / ((c : ℝ) * specNorm B)))) :=
        measureReal_abs_trace_sub_girardHutchinson_ge_le hind hsub hvar B hτpos.le
    _ ≤ 2 * Real.exp (-(hansonWrightConstant * ((Fintype.card m : ℝ) * Fintype.card n *
          min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
        gcongr
        exact hansonWrightConstant_pos.le

/-- **The Kolmogorov-distance tail of the probe spectral measure.** Let the entries of the real
$n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ and having second moment $1$. Then for
real symmetric $\mathbf{A}$ and every $\tau \ge 0$, the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by more than $\tau$ at some
eigenvalue with probability at most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
the constant being `hansonWrightConstant`: a union bound over the at most $\lvert n\rvert$
eigenvalues; both distribution functions are constant between eigenvalues, and
`Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le`
extends the bound to every threshold. [ChenTrogdonUbaru2021, §3] (locator to check); there for
probes uniform on the sphere.
Result: spectral-density-kolmogorov-tail -/
theorem measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (X ω)).real (Set.Iic x)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have := hind.isProbabilityMeasure
  -- union bound over the eigenvalues, indexed by `n`
  calc _ ≤ μ.real (⋃ i ∈ (Finset.univ : Finset n), {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic (hA.eigenvalues i)) -
            (probeSpectralMeasure A (X ω)).real (Set.Iic (hA.eigenvalues i))|}) := by
        refine measureReal_mono (fun ω ⟨x, hx, hlt⟩ => ?_) (measure_ne_top _ _)
        obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
        exact Set.mem_biUnion (Finset.mem_univ i) hlt.le
    _ ≤ ∑ i : n, μ.real {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic (hA.eigenvalues i)) -
            (probeSpectralMeasure A (X ω)).real (Set.Iic (hA.eigenvalues i))|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ _i : n, 2 * Real.exp (-(hansonWrightConstant * (Fintype.card m *
          Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) :=
        Finset.sum_le_sum fun i _ =>
          measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le
            hind hsub hvar hA _ hτ
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring

/-- **The probe spectral measure approximates the spectral density, uniformly in Lipschitz test
functions.** Let the entries of the real $n \times m$ test matrix $\mathbf{\Omega}$ be
independent, each satisfying the sub-Gaussian moment generating function bound with variance
proxy $c$ and having second moment $1$; let $\mathbf{A}$ be real symmetric with spectrum in
$[a, b]$, $a \le b$, and let $L \ge 0$ and $\tau \ge 0$. Then, except with probability at
most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
every $f$ that is $L$-Lipschitz on $[a, b]$ satisfies
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} -
\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})\Bigr\rvert \le
(\lvert f(b)\rvert + L(b - a))\tau\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant is `hansonWrightConstant`. This is
SLQ with exact quadrature. [ChenTrogdonUbaru2021, §3] (locator to check); there for probes
uniform on the sphere.
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a ≤ b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂probeSpectralMeasure A (X ω)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have := hind.isProbabilityMeasure
  refine (measureReal_mono fun ω hω => ?_).trans
    (measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
      hind hsub hvar hA hτ)
  obtain ⟨f, hf, hlt⟩ := hω
  by_contra hK
  simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hK
  exact hlt.not_ge
    (hA.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le hab hs hτ hK hf)

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **Stochastic Lanczos quadrature approximates the spectral density, uniformly in Lipschitz
test functions.** Let the entries of the real $n \times m$ test matrix $\mathbf{\Omega}$ be
independent, each satisfying the sub-Gaussian moment generating function bound with variance
proxy $c$ and having second moment $1$; let $\mathbf{A}$ be real symmetric with spectrum in
$[a, b]$, $a < b$; let $L \ge 0$, $q \in \mathbb{N}$ and $\tau \ge 0$. Then, except with
probability at most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
every $f$ that is $L$-Lipschitz on $[a, b]$ satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega},
q + 1)\Bigr\rvert \le (\lvert f(b)\rvert + L(b - a))\tau +
\frac{\pi L(b - a)}{2q + 3}(1 + \tau)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constants are `hansonWrightConstant` and
`jacksonApproximationConstant`. For test functions with $f(b) = 0$ and equal masses this is a
Wasserstein-1 bound. The factor $1 + \tau$ bounds the random mass
$\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$ on the same event. Gaussian and sign test
matrices are the case $c = 1$.
Asymptotic form:
`NLAlib.exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`.
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ] (theorem number to check); there for probes
uniform on the sphere, with the sharper sub-Gaussian constant of Beta laws and the bound in the
Wasserstein distance; the Jackson step is [ChenTrogdonUbaru2022, Appendix C, Theorem 38].
Result: spectral-density-lipschitz-tail -/
theorem measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) (q : ℕ) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ +
          jacksonApproximationConstant * L * (b - a) / (2 * q + 3) * (1 + τ) <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂slqMeasure A (X ω) (q + 1)|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  set T := {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
    (probeSpectralMeasure A (X ω)).real (Set.Iic x)|}
  have hT :=
    measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
      hind hsub hvar hA hτ
  rcases eq_or_ne (μ T) ∞ with hTtop | hTtop
  · -- `μ` is not finite, so `n` or `m` is empty and the event does not depend on `ω`.
    have hμ : μ Set.univ = ∞ := top_le_iff.mp (hTtop ▸ measure_mono (Set.subset_univ T))
    have hsing : Subsingleton (Matrix n m ℝ) := by
      rcases isEmpty_or_nonempty n with hn | ⟨⟨i⟩⟩
      · infer_instance
      rcases isEmpty_or_nonempty m with hm | ⟨⟨j⟩⟩
      · infer_instance
      have hint := (hsub i j).integrable_exp_mul 0
      simp only [zero_mul, Real.exp_zero] at hint
      have := (integrable_const_iff.mp hint).resolve_left one_ne_zero
      exact absurd hμ (measure_ne_top μ _)
    have key : ∀ S : Set Ω, (∀ ω ∈ S, ∀ ω', ω' ∈ S) → μ.real S = 0 := fun S hS => by
      rcases S.eq_empty_or_nonempty with rfl | ⟨ω₀, h₀⟩
      · exact measureReal_empty
      · rw [Set.eq_univ_of_forall (hS ω₀ h₀), measureReal_def, hμ, ENNReal.toReal_top]
    refine le_trans (le_of_eq (key _ fun ω hω ω' => ?_)) (hT.trans' measureReal_nonneg)
    obtain ⟨f, hf, hlt⟩ := hω
    exact ⟨f, hf, Subsingleton.elim (X ω) (X ω') ▸ hlt⟩
  refine le_trans (measureReal_mono (fun ω hω => ?_) hTtop) hT
  obtain ⟨f, hf, hlt⟩ := hω
  by_contra hK
  simp only [T, Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hK
  have hmass : frobNorm (X ω) ^ 2 / (Fintype.card n * Fintype.card m) ≤ 1 + τ := by
    rcases isEmpty_or_nonempty n with hn | hn
    · simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul, div_zero]
      linarith
    · rw [← hA.probeSpectralMeasure_real_univ (X ω)]
      linarith [abs_le.mp (hA.abs_one_sub_probeSpectralMeasure_real_univ_le hK)]
  have h1 := hA.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le
    hab.le hs hτ hK hf
  have h2 := hA.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith
    hab hs (X ω) q hf
  have hJ : 0 ≤ jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
    have := jacksonApproximationConstant_pos
    have : 0 ≤ b - a := by linarith
    positivity
  have h3 := abs_sub_le (∫ x, f x ∂empiricalSpectralMeasure A)
    (∫ x, f x ∂probeSpectralMeasure A (X ω)) (∫ x, f x ∂slqMeasure A (X ω) (q + 1))
  nlinarith [mul_le_mul_of_nonneg_left hmass hJ]

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(c^2\log(\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2))$ probes suffice for SLQ to
approximate the spectral density, uniformly in Lipschitz test functions**: there is an absolute
constant $C > 0$ such that the following holds. Let the entries of the real $n \times m$ test
matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian moment generating
function bound with variance proxy $c > 0$ and having second moment $1$; let $\mathbf{A}$ be real
symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$, $q \in \mathbb{N}$,
$0 < \tau \le 1$ and $0 < \delta \le 1$. If
$m \ge C c^2\log(2\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2)$, then except with probability
at most $\delta$ every $f$ that is $L$-Lipschitz on $[a, b]$
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega},
q + 1)\Bigr\rvert \le (\lvert f(b)\rvert + L(b - a))\tau +
\frac{\pi L(b - a)}{2q + 3}(1 + \tau)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. The constant $C$ comes before every dimension, matrix and
parameter. With $\lvert n\rvert$ in the denominator, for large $n$ a single probe suffices.
Proved from
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`
with $C = 196$. [ChenTrogdonUbaru2021, the Wasserstein bound for SLQ] (theorem number to check);
there for probes uniform on the sphere.
Asymptotic:
NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
Result: spectral-density-lipschitz-tail -/
theorem
exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n m : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
      [Fintype m] (μ : Measure Ω) (X : Ω → Matrix n m ℝ) (c : ℝ≥0)
      (A : Matrix n n ℝ) (a b : ℝ) (L : ℝ≥0) (q : ℕ) (τ δ : ℝ), 0 < c →
      iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ →
      (∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ) →
      (∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) → A.IsHermitian → a < b →
      spectrum ℝ A ⊆ Set.Icc a b → 0 < τ → τ ≤ 1 → 0 < δ → δ ≤ 1 →
      C * (c : ℝ) ^ 2 * Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) ≤
        Fintype.card m →
      μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        (|f b| + L * (b - a)) * τ +
          jacksonApproximationConstant * L * (b - a) / (2 * q + 3) * (1 + τ) <
        |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂slqMeasure A (X ω) (q + 1)|} ≤ δ := by
  refine ⟨196, by norm_num, ?_⟩
  intro Ω n m _ _ _ _ μ X c A a b L q τ δ hc hind hsub hvar hA hab hs hτ hτ1 hδ hδ1 hsize
  have := hind.isProbabilityMeasure
  refine (measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
    hind hsub hvar hA hab hs L q hτ.le).trans ?_
  rcases isEmpty_or_nonempty n with hn | hn
  · simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, mul_zero, zero_mul]
    exact hδ.le
  have hN : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr hn)
  have hlog : 0 < Real.log (2 * Fintype.card n / δ) := Real.log_pos (by
    rw [one_lt_div hδ]; nlinarith [(Nat.one_le_cast (α := ℝ)).mpr (Fintype.card_pos_iff.mpr hn)])
  rcases isEmpty_or_nonempty m with hm | hm
  · exfalso
    rw [Fintype.card_eq_zero (α := m), Nat.cast_zero] at hsize
    have : 0 < 196 * (c : ℝ) ^ 2 * Real.log (2 * Fintype.card n / δ) /
        (Fintype.card n * τ ^ 2) := by positivity
    linarith
  obtain ⟨i⟩ := hn
  obtain ⟨j⟩ := hm
  have hc1 : (1 : ℝ) ≤ c := hvar i j ▸ (hsub i j).integral_sq_le
  have hc0 : (0 : ℝ) < c := by linarith
  have hτc : τ ^ 2 / (c : ℝ) ^ 2 ≤ τ / c := by
    rw [sq, sq, ← div_mul_div_comm]
    exact mul_le_of_le_one_left (by positivity) ((div_le_one hc0).mpr (hτ1.trans hc1))
  have hle : Real.log (2 * Fintype.card n / δ) ≤
      hansonWrightConstant * (Fintype.card m * Fintype.card n * (τ ^ 2 / (c : ℝ) ^ 2)) := by
    rw [div_le_iff₀ (by positivity)] at hsize
    have hy : Real.log (2 * Fintype.card n / δ) ≤
        1 / 196 * (Fintype.card m * Fintype.card n * (τ ^ 2 / (c : ℝ) ^ 2)) := by
      rw [mul_div_assoc', mul_div_assoc', le_div_iff₀ (by positivity)]
      linarith
    exact hy.trans (by gcongr; exact le_hansonWrightConstant)
  calc 2 * (Fintype.card n : ℝ) * Real.exp (-(hansonWrightConstant *
        (Fintype.card m * Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) ≤
      2 * Fintype.card n * Real.exp (-Real.log (2 * Fintype.card n / δ)) := by
        rw [min_eq_left hτc]; gcongr
    _ = δ := by
        rw [Real.exp_neg, Real.exp_log (by positivity)]
        field_simp

/-- A Lipschitz function on $[a, b]$ is integrable against a finite measure carried by $[a, b]$. -/
private theorem integrable_of_lipschitz_ae {ρ : Measure ℝ} [IsFiniteMeasure ρ] {a b : ℝ}
    (hρ : ∀ᵐ x ∂ρ, x ∈ Set.Icc a b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) : Integrable f ρ := by
  have h := hf.continuousOn.integrableOn_Icc (μ := ρ)
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hρ] at h

/-- Scaling a measure by the inverse of the mass of the probe spectral measure. -/
private theorem measureReal_inv_mass_smul (P R : Measure ℝ) (S : Set ℝ) :
    ((P Set.univ)⁻¹ • R).real S = (P.real Set.univ)⁻¹ * R.real S := by
  simp only [measureReal_def, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    ENNReal.toReal_inv]

/-- Scaling a measure by the inverse of the mass of $P$ gives mass $1$ when the masses agree. -/
private theorem measureReal_inv_mass_smul_univ {P R : Measure ℝ}
    (hPR : R.real Set.univ = P.real Set.univ) (hP : 0 < P.real Set.univ) :
    ((P Set.univ)⁻¹ • R).real Set.univ = 1 := by
  rw [measureReal_inv_mass_smul, hPR]
  exact inv_mul_cancel₀ hP.ne'

/-- On the good event, the empirical measure and the normalised probe measure are close against
Lipschitz test functions: the distribution functions differ by at most $2\tau$. -/
private theorem abs_integral_empirical_sub_normalised_probe_le [Nonempty n]
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m ℝ) {τ : ℝ}
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    (hτ : 0 ≤ τ) (hMpos : 0 < (probeSpectralMeasure A Ω).real Set.univ) {L : ℝ≥0} {f : ℝ → ℝ}
    (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A -
      ∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω)| ≤
      L * (b - a) * (2 * τ) := by
  have hM : |(probeSpectralMeasure A Ω).real Set.univ - 1| ≤ τ := by
    rw [abs_sub_comm]
    exact hA.abs_one_sub_probeSpectralMeasure_real_univ_le hK
  have hfin := Matrix.finite_real_spectrum (A := A)
  have hνs : ∀ᵐ x ∂empiricalSpectralMeasure A, x ∈ hfin.toFinset :=
    (hA.ae_mem_spectrum_empiricalSpectralMeasure).mono fun x hx => hfin.mem_toFinset.mpr hx
  have hρs : ∀ᵐ x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω),
      x ∈ hfin.toFinset := Measure.ae_smul_measure
    ((ae_mem_spectrum_probeSpectralMeasure A Ω).mono fun x hx => hfin.mem_toFinset.mpr hx) _
  -- normalising moves the probe distribution function by `(u / M) |M - 1| ≤ τ`
  have hK2 : ∀ x ∈ hfin.toFinset, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      ((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω).real (Set.Iic x)| ≤
        2 * τ := by
    intro x hx
    rw [measureReal_inv_mass_smul]
    set M := (probeSpectralMeasure A Ω).real Set.univ
    set u := (probeSpectralMeasure A Ω).real (Set.Iic x)
    set v := (empiricalSpectralMeasure A).real (Set.Iic x)
    have hinv : |M⁻¹ * u| ≤ 1 := by
      rw [abs_of_nonneg (by positivity), inv_mul_le_iff₀ hMpos, mul_one]
      exact measureReal_mono (Set.subset_univ _)
    have e : v - M⁻¹ * u = (v - u) + M⁻¹ * u * (M - 1) := by
      field_simp
      ring
    calc |v - M⁻¹ * u| ≤ |v - u| + |M⁻¹ * u| * |M - 1| := by
          rw [e, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ τ + 1 * τ := add_le_add (hK x (hfin.mem_toFinset.mp hx))
          (mul_le_mul hinv hM (abs_nonneg _) zero_le_one)
      _ = 2 * τ := by ring
  have hfν := integrable_of_lipschitz_ae
    ((hA.ae_mem_spectrum_empiricalSpectralMeasure).mono fun x hx => hs hx) hf
  have hfρ := integrable_of_lipschitz_ae
    (Measure.ae_smul_measure (ae_mem_Icc_probeSpectralMeasure A hs Ω)
      (probeSpectralMeasure A Ω Set.univ)⁻¹) hf
  have hg : LipschitzOnWith L (fun x => f x - f b) (Set.Icc a b) := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    simpa only [dist_sub_right] using hf.dist_le_mul x hx y hy
  have hmain := MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith hνs hρs
    (fun x hx => hs (hfin.mem_toFinset.mp hx)) hab.le hg (by linarith) hK2
  simp only [sub_self, abs_zero, zero_add] at hmain
  rw [integral_sub hfν (integrable_const _), integral_sub hfρ (integrable_const _)] at hmain
  have hρ1 : ((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω).real Set.univ =
      1 := measureReal_inv_mass_smul_univ rfl hMpos
  simpa [integral_const, hρ1, sub_sub_sub_cancel_right] using hmain

/-- The normalised probe measure and the normalised SLQ measure differ, against Lipschitz test
functions, by the Gauss-rule term: Jackson's polynomial and moment matching. -/
private theorem abs_integral_normalised_probe_sub_slq_le
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m ℝ) (q : ℕ)
    (hMpos : 0 < (probeSpectralMeasure A Ω).real Set.univ)
    (hQM : (slqMeasure A Ω (q + 1)).real Set.univ = (probeSpectralMeasure A Ω).real Set.univ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω) -
      ∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • slqMeasure A Ω (q + 1))| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
  have hmatch := (hA.matchesMoments_probeSpectralMeasure_slqMeasure Ω (q + 1)).smul
    (probeSpectralMeasure A Ω Set.univ)⁻¹
  have hPne : probeSpectralMeasure A Ω Set.univ ≠ 0 := fun h => by
    simp [measureReal_def, h] at hMpos
  have := (slqMeasure A Ω (q + 1)).smul_finite (ENNReal.inv_ne_top.2 hPne)
  have hPab := Measure.ae_smul_measure (ae_mem_Icc_probeSpectralMeasure A hs Ω)
    (probeSpectralMeasure A Ω Set.univ)⁻¹
  have hQab := Measure.ae_smul_measure (hA.ae_mem_Icc_slqMeasure hs Ω (q + 1))
    (probeSpectralMeasure A Ω Set.univ)⁻¹
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) hab hf (2 * q + 1)
  have hp' : p.degree < 2 * ((q + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  have h := hmatch.abs_integral_sub_integral_le_of_isUniformApproxOn hPab hQab
    (integrable_of_lipschitz_ae hPab hf) (integrable_of_lipschitz_ae hQab hf) hp' hε
  rw [measureReal_inv_mass_smul_univ rfl hMpos, measureReal_inv_mass_smul_univ hQM hMpos] at h
  refine h.trans (le_of_eq ?_)
  push_cast
  field_simp
  ring

/-- Deterministic step for the normalised SLQ measure: on the Kolmogorov-good event, every
Lipschitz test function is within the normalised SLQ error. -/
private theorem abs_integral_sub_integral_slq_le_of_hK
    {A : Matrix n n ℝ} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m ℝ) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ)
    (hτ1 : τ < 1)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    {L : ℝ≥0} {f : ℝ → ℝ} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A -
        ∫ x, f x ∂((slqMeasure A Ω (q + 1) Set.univ)⁻¹ • slqMeasure A Ω (q + 1))| ≤
      L * (b - a) * (2 * τ) + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : empiricalSpectralMeasure A = 0 := by simp [empiricalSpectralMeasure]
    have h1 : slqMeasure A Ω (q + 1) = 0 := by simp [slqMeasure]
    simp only [h0, h1, integral_zero_measure, sub_zero, abs_zero, smul_zero]
    have := jacksonApproximationConstant_pos
    have : 0 ≤ b - a := by linarith
    positivity
  have hM : |1 - (probeSpectralMeasure A Ω).real Set.univ| ≤ τ :=
    Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le hA hK
  have hMpos : 0 < (probeSpectralMeasure A Ω).real Set.univ := by linarith [abs_le.mp hM]
  have hQM : (slqMeasure A Ω (q + 1)).real Set.univ = (probeSpectralMeasure A Ω).real Set.univ :=
    ((hA.matchesMoments_probeSpectralMeasure_slqMeasure Ω (q + 1)).measureReal_univ_eq
      (by omega)).symm
  have hQP : slqMeasure A Ω (q + 1) Set.univ = probeSpectralMeasure A Ω Set.univ :=
    (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp hQM
  rw [hQP]
  have h1 := abs_integral_empirical_sub_normalised_probe_le hA hab hs Ω hK hτ hMpos hf
  have h2 := abs_integral_normalised_probe_sub_slq_le hA hab hs Ω q hMpos hQM hf
  have h3 := abs_sub_le (∫ x, f x ∂empiricalSpectralMeasure A)
    (∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • probeSpectralMeasure A Ω))
    (∫ x, f x ∂((probeSpectralMeasure A Ω Set.univ)⁻¹ • slqMeasure A Ω (q + 1)))
  linarith

/-- **The mass-normalised SLQ measure approximates the spectral density, uniformly in Lipschitz
test functions.** Let the entries of the real $n \times m$ test matrix $\mathbf{\Omega}$ be
independent, each satisfying the sub-Gaussian moment generating function bound with variance
proxy $c$ and having second moment $1$; let $\mathbf{A}$ be real symmetric with spectrum in
$[a, b]$, $a < b$; let $L \ge 0$, $q \in \mathbb{N}$ and $0 \le \tau < 1$. Then, except with
probability at most <!-- value hansonWrightConstant -->
$$2\lvert n\rvert\exp\Bigl(-\frac{1}{196}\,m\lvert n\rvert\min\Bigl(\frac{\tau^2}{c^2},
\frac{\tau}{c}\Bigr)\Bigr)\,,$$
the SLQ measure divided by its mass satisfies, for every $f$ that is $L$-Lipschitz on
$[a, b]$, <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\frac{\mathsf{slqMeasure}(\mathbf{A},
\mathbf{\Omega},q+1)}{\mathsf{slqMeasure}(\mathbf{A},\mathbf{\Omega},q+1)(\mathbb{R})}\Bigr\rvert
\le 2L(b - a)\tau + \frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constants are `hansonWrightConstant` and
`jacksonApproximationConstant`. Both measures are probability measures, so there is no term in
$\lvert f(b)\rvert$; $\tau < 1$ keeps the mass positive. Junk: for empty $n$ the normalisation is
$\infty \cdot 0 = 0$ and the event is empty.
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ] (theorem number to check); there for probes
uniform on the sphere, whose SLQ measure has mass $1$.
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_smul_slqMeasure_gt_le
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0) (q : ℕ) {τ : ℝ}
    (hτ : 0 ≤ τ) (hτ1 : τ < 1) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * (2 * τ) + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂((slqMeasure A (X ω) (q + 1) Set.univ)⁻¹ • slqMeasure A (X ω) (q + 1))|} ≤
      2 * Fintype.card n * Real.exp (-(hansonWrightConstant * (Fintype.card m *
        Fintype.card n * min (τ ^ 2 / (c : ℝ) ^ 2) (τ / c)))) := by
  have hEv : {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * (2 * τ) + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂((slqMeasure A (X ω) (q + 1) Set.univ)⁻¹ • slqMeasure A (X ω) (q + 1))|} ⊆
      {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (X ω)).real (Set.Iic x)|} := by
    rintro ω ⟨f, hf, hlt⟩
    by_contra hcon
    simp only [Set.mem_ofPred_eq, not_exists, not_and, not_lt] at hcon
    exact absurd hlt (not_lt.mpr (abs_integral_sub_integral_slq_le_of_hK hA hab hs (X ω) q hτ hτ1
      hcon hf))
  have := hind.isProbabilityMeasure
  refine (measureReal_mono hEv).trans ?_
  exact measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le
    hind hsub hvar hA hτ

/-! ### Sphere probes: tails with the sharp Beta constant -/

-- The declaration name exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The distribution of the probe spectral measure with sphere probes, at one set.** Let the
columns $\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$
be independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law
`uniformSphereVector n`), and take the probes $\sqrt{\lvert n\rvert}\,\mathbf{u}_j$. Then for
real symmetric $\mathbf{A}$, every $S \subseteq \mathbb{R}$ and every $\tau \ge 0$,
$$\mathbb{P}\bigl[\tau \le \lvert\nu_{\mathbf{A}}(S) - \mathsf{probeSpectralMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U})(S)\rvert\bigr] \le 2\exp(-m(\lvert n\rvert + 2)\tau^2)\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure. The error is a centred mean of $m$ independent
$\mathrm{Beta}(r/2, (\lvert n\rvert - r)/2)$ variables, $r$ the rank of the spectral projector
$\mathbf{1}_S(\mathbf{A})$, with sub-Gaussian proxy $1/(2(\lvert n\rvert + 2))$; ranks $0$ and
$\lvert n\rvert$ are deterministic. Compared with
`NLAlib.measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le`
(independent sub-Gaussian entries) the exponent has no unknown constant and no minimum.
[ChenTrogdonUbaru2021, §3] (locator to check). -/
theorem
measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (S : Set ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
        (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S|} ≤
      2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  classical
  have hP := isStarProjection_cfc_indicator A S
  obtain ⟨V, hV, hVV⟩ := hP.exists_hasOrthonormalCols_mul_conjTranspose_eq
    (p := Fin (cfc (S.indicator fun _ => (1 : ℝ)) A).rank) (by simp)
  have hquad : ∀ z : n → ℝ, quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A) z =
      ‖WithLp.toLp 2 (Vᴴ *ᵥ z)‖ ^ 2 := fun z => by
    have h := quadForm_mul_conjTranspose_self V z
    rw [hVV] at h
    simpa using h
  have hemp : (empiricalSpectralMeasure A).real S =
      (Fintype.card (Fin (cfc (S.indicator fun _ => (1 : ℝ)) A).rank) : ℝ) / Fintype.card n := by
    rw [hA.empiricalSpectralMeasure_real S, RCLike.re_to_real, hP.trace_eq_rank, Fintype.card_fin]
  have hprobe : ∀ ω, (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S =
      (∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ fun i => U ω i j)‖ ^ 2) / Fintype.card m := by
    intro ω
    rw [probeSpectralMeasure_real, girardHutchinson_eq_sum, RCLike.re_to_real]
    rcases eq_or_ne (Fintype.card n) 0 with h0 | h0
    · have : IsEmpty n := Fintype.card_eq_zero_iff.mp h0
      have hz : ∀ z : n → ℝ, Vᴴ *ᵥ z = 0 := fun z => by
        rw [Subsingleton.elim z 0, Matrix.mulVec_zero]
      simp only [hz]
      simp
    · have hn : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast h0
      have hcol : ∀ j, quadForm (cfc (S.indicator fun _ => (1 : ℝ)) A)
          (√(Fintype.card n : ℝ) • fun i => U ω i j) =
          (Fintype.card n : ℝ) * ‖WithLp.toLp 2 (Vᴴ *ᵥ fun i => U ω i j)‖ ^ 2 := by
        intro j
        rw [quadForm_smul_right, hquad, star_trivial, Real.mul_self_sqrt (Nat.cast_nonneg _)]
      have hcol' : ∀ j, (fun i => (√(Fintype.card n : ℝ) • U ω) i j) =
          √(Fintype.card n : ℝ) • fun i => U ω i j := fun j => rfl
      simp only [hcol', hcol]
      rw [← Finset.mul_sum]
      field_simp
  have key : ∀ ω, (empiricalSpectralMeasure A).real S -
      (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S =
      -((∑ j, ‖WithLp.toLp 2 (Vᴴ *ᵥ fun i => U ω i j)‖ ^ 2) / Fintype.card m -
        (Fintype.card (Fin (cfc (S.indicator fun _ => (1 : ℝ)) A).rank) : ℝ) / Fintype.card n) := by
    intro ω
    rw [hemp, hprobe ω]
    ring
  simp only [key, abs_neg]
  exact
    measureReal_abs_sum_norm_conjTranspose_mulVec_sq_div_card_sub_div_card_ge_le_of_hasLaw_uniformSphereVector
      (u := fun j ω i => U ω i j) hind hU hV hτ

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **The Kolmogorov-distance tail of the probe spectral measure with sphere probes.** Let the
columns $\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$
be independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law
`uniformSphereVector n`). Then for real symmetric $\mathbf{A}$ and every $\tau \ge 0$, the
distribution functions of $\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \sqrt{\lvert n\rvert}\,\mathbf{U})$ differ by more
than $\tau$ at some eigenvalue with probability at most
$$2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)\,:$$
a union bound over the at most $\lvert n\rvert$ eigenvalues; both distribution functions are
constant between eigenvalues, and
`Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le`
extends the bound to every threshold. [ChenTrogdonUbaru2021, §3] (locator to check).
Result: spectral-density-kolmogorov-tail -/
theorem
measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|} ≤
      2 * Fintype.card n * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  have hcard := hA.card_toFinset_spectrum_le
  have hpt := fun x =>
    measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le_of_hasLaw_uniformSphereVector
      hind hU hA (Set.Iic x) hτ
  rcases isEmpty_or_nonempty m with hm | hm
  · -- No columns: the event does not depend on `ω`, so it is one of the per-point events.
    rcases Set.eq_empty_or_nonempty {ω | ∃ x ∈ spectrum ℝ A,
        τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
          (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|} with he | he
    · rw [he, measureReal_empty]
      positivity
    obtain ⟨ω₀, x₀, hx₀, h₀⟩ := he
    have hU' : ∀ ω, U ω = U ω₀ := fun ω => Subsingleton.elim _ _
    have hn : (1 : ℝ) ≤ Fintype.card n := by
      have := (Finset.card_pos.mpr ⟨x₀, (Set.Finite.mem_toFinset _).mpr hx₀⟩).trans_le
        hcard
      exact_mod_cast this
    calc _ = μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real (Set.Iic x₀) -
          (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x₀)|} := by
          congr 1
          ext ω
          simp only [Set.mem_ofPred_eq, hU' ω]
          exact ⟨fun _ => h₀.le, fun _ => ⟨x₀, hx₀, h₀⟩⟩
      _ ≤ _ := hpt x₀
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_mul_of_one_le_right (by norm_num) hn)
          (Real.exp_nonneg _)
  have := (hU hm.some).isProbabilityMeasure
  calc _ ≤ μ.real (⋃ x ∈ A.finite_real_spectrum.toFinset, {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic x) -
            (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|}) := by
        refine measureReal_mono (fun ω ⟨x, hx, h⟩ => ?_) (measure_ne_top _ _)
        simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Set.Finite.mem_toFinset]
        exact ⟨x, hx, h.le⟩
    _ ≤ ∑ x ∈ A.finite_real_spectrum.toFinset, μ.real {ω | τ ≤
          |(empiricalSpectralMeasure A).real (Set.Iic x) -
            (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|} :=
        measureReal_biUnion_finset_le _ _
    _ ≤ A.finite_real_spectrum.toFinset.card •
          (2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2))) :=
        Finset.sum_le_card_nsmul _ _ _ fun x _ => hpt x
    _ ≤ _ := by
        rw [nsmul_eq_mul, ← mul_assoc, mul_comm (_ : ℝ) 2]
        gcongr

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **SLQ with sphere probes, uniformly in Lipschitz test functions.** Let the columns
$\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$ be
independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`);
let $\mathbf{A}$ be real symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$,
$q \in \mathbb{N}$ and $\tau \ge 0$. Then, except with probability at most
$2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)$, every $f$ that is $L$-Lipschitz on
$[a, b]$ satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U}, q + 1)\Bigr\rvert \le L(b - a)\tau +
\frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. With sphere probes the probe and SLQ measures have mass exactly
$1$, so there is no term in $\lvert f(b)\rvert$ and no factor $1 + \tau$: this is a
Wasserstein-1 bound.
Asymptotic form:
`NLAlib.exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`.
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ] (theorem number to check); the Jackson
step is [ChenTrogdonUbaru2022, Appendix C, Theorem 38].
Result: spectral-density-lipschitz-tail -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0)
    (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1)|} ≤
      2 * Fintype.card n * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · refine le_trans (le_of_eq ?_) (by positivity)
    convert measureReal_empty (μ := μ)
    refine Set.eq_empty_of_forall_notMem fun ω ⟨f, _, hlt⟩ => ?_
    rw [integral_empiricalSpectralMeasure, integral_slqMeasure] at hlt
    simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, div_zero, sub_zero, abs_zero] at hlt
    have := jacksonApproximationConstant_pos
    have : 0 ≤ b - a := by linarith
    have : 0 ≤ L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) := by
      positivity
    linarith
  have := hind.isProbabilityMeasure
  rcases isEmpty_or_nonempty m with hm | hm
  · refine measureReal_le_one.trans ?_
    have : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.mpr Fintype.card_pos
    simp only [Fintype.card_eq_zero, CharP.cast_eq_zero, zero_mul, neg_zero, Real.exp_zero]
    linarith
  -- Almost surely every probe has squared norm `card n`, so the probe measure has mass `1`.
  have hmass : ∀ᵐ ω ∂μ,
      (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real Set.univ = 1 := by
    have hcol : ∀ᵐ ω ∂μ, ∀ j, ‖WithLp.toLp 2 (fun i => U ω i j)‖ = 1 :=
      ae_all_iff.mpr fun j => ae_of_ae_map (hU j).aemeasurable
        ((hU j).map_eq ▸ ae_norm_eq_one_uniformSphereVector)
    filter_upwards [hcol] with ω hω
    have hn0 : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr Fintype.card_pos
    have h (j : m) : ‖WithLp.toLp 2 ((√(Fintype.card n : ℝ) • U ω).col j)‖ ^ 2 =
        Fintype.card n := by
      rw [show (√(Fintype.card n : ℝ) • U ω).col j = √(Fintype.card n : ℝ) • fun i => U ω i j
        from rfl, WithLp.toLp_smul, norm_smul, hω j, mul_one,
        Real.norm_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt hn0.le]
    rw [hA.probeSpectralMeasure_real_univ, frobNorm_sq_eq_sum_col]
    simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
  refine (measureReal_mono_ae ?_).trans
    (measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le_of_hasLaw_uniformSphereVector
      hind hU hA hτ)
  filter_upwards [hmass] with ω hω ⟨f, hf, hlt⟩
  by_contra hK
  change ¬∃ x ∈ spectrum ℝ A, _ at hK
  push Not at hK
  -- The Kolmogorov bound for `f - f b`; equal masses remove the shift.
  have h1 := hA.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le hab.le
    hs hτ hK (f := fun x => f x - f b)
    (fun x hx y hy => by simpa only [edist_sub_right] using hf hx hy)
  have h2 :=
    hA.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith hab hs
      (√(Fintype.card n : ℝ) • U ω) q hf
  rw [← hA.probeSpectralMeasure_real_univ, hω, mul_one] at h2
  have hE : ∫ x, f x - f b ∂empiricalSpectralMeasure A =
      ∫ x, f x ∂empiricalSpectralMeasure A - f b := by
    have : (Fintype.card n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [integral_empiricalSpectralMeasure, integral_empiricalSpectralMeasure,
      Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  rw [hE, integral_sub (integrable_probeSpectralMeasure _ _ _) (integrable_const _),
    integral_const, smul_eq_mul, hω, one_mul, sub_sub_sub_cancel_right, sub_self, abs_zero,
    zero_add] at h1
  linarith [abs_sub_le (∫ x, f x ∂empiricalSpectralMeasure A)
    (∫ x, f x ∂probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω))
    (∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1))]

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **A sample size for SLQ with sphere probes.** Let the columns
$\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$ be
independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`);
let $\mathbf{A}$ be real symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$,
$q \in \mathbb{N}$, $\tau > 0$ and $\delta > 0$. If
$$m \ge \frac{\log(2\lvert n\rvert/\delta)}{(\lvert n\rvert + 2)\tau^2}\,,$$
then except with probability at most $\delta$ every $f$ that is $L$-Lipschitz on $[a, b]$
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U}, q + 1)\Bigr\rvert \le L(b - a)\tau +
\frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. The sharp Beta proxy leaves no unknown constant in the sample
size. The tail form is
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`,
and its asymptotic form is
`NLAlib.exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`.
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ] (theorem number to check). -/
theorem
measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector_of_log_div_le
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {a b : ℝ} (hab : a < b) (hs : spectrum ℝ A ⊆ Set.Icc a b) (L : ℝ≥0)
    (q : ℕ) {τ δ : ℝ} (hτ : 0 < τ) (hδ : 0 < δ)
    (hm : Real.log (2 * Fintype.card n / δ) / ((Fintype.card n + 2) * τ ^ 2) ≤ Fintype.card m) :
    μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1)|} ≤ δ := by
  refine
    (measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector
      hind hU hA hab hs L q hτ.le).trans ?_
  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · simp [hn, hδ.le]
  · have hnR : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr hn
    have hτ2 : 0 < ((Fintype.card n : ℝ) + 2) * τ ^ 2 := by positivity
    have hlog : Real.log (2 * Fintype.card n / δ) ≤
        Fintype.card m * ((Fintype.card n + 2) * τ ^ 2) := (div_le_iff₀ hτ2).mp hm
    have hpos : 0 < 2 * (Fintype.card n : ℝ) / δ := by positivity
    have hexp : Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) ≤
        δ / (2 * Fintype.card n) := by
      calc Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2))
          ≤ Real.exp (-Real.log (2 * Fintype.card n / δ)) :=
            Real.exp_le_exp.mpr (neg_le_neg (by
              linarith [mul_assoc (Fintype.card m : ℝ) (Fintype.card n + 2) (τ ^ 2)]))
        _ = δ / (2 * Fintype.card n) := by
            rw [Real.exp_neg, Real.exp_log hpos]; field_simp
    calc _ ≤ 2 * (Fintype.card n : ℝ) * (δ / (2 * Fintype.card n)) := by gcongr
      _ = δ := by field_simp

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(\log(\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2))$ sphere probes suffice for SLQ to
approximate the spectral density, uniformly in Lipschitz test functions**: there is an absolute
constant $C > 0$ such that the following holds. Let the columns
$\mathbf{u}_1, \dots, \mathbf{u}_m$ of the random real $n \times m$ matrix $\mathbf{U}$ be
independent, each uniform on the unit sphere of $\mathbb{R}^n$ (law `uniformSphereVector n`);
let $\mathbf{A}$ be real symmetric with spectrum in $[a, b]$, $a < b$; let $L \ge 0$,
$q \in \mathbb{N}$, $\tau > 0$ and $\delta > 0$. If
$m \ge C\log(2\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2)$, then except with probability at
most $\delta$ every $f$ that is $L$-Lipschitz on $[a, b]$
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} - \int f\,d\,\mathsf{slqMeasure}(\mathbf{A},
\sqrt{\lvert n\rvert}\,\mathbf{U}, q + 1)\Bigr\rvert \le L(b - a)\tau +
\frac{\pi L(b - a)}{2q + 3}\,,$$
$\nu_{\mathbf{A}}$ the empirical spectral measure; the constant of the Gauss term is
`jacksonApproximationConstant`. The constant $C$ comes before every dimension, matrix and
parameter; $C = 1$ works. Proved from
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector`
through its sample-size form
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector_of_log_div_le`.
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ] (theorem number to check).
Asymptotic:
NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector
Result: spectral-density-lipschitz-tail -/
theorem
exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n m : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
      [Fintype m] (μ : Measure Ω) (U : Ω → Matrix n m ℝ) (A : Matrix n n ℝ) (a b : ℝ)
      (L : ℝ≥0) (q : ℕ) (τ δ : ℝ),
      iIndepFun (fun j ω i => U ω i j) μ →
      (∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) → A.IsHermitian → a < b →
      spectrum ℝ A ⊆ Set.Icc a b → 0 < τ → 0 < δ →
      C * Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) ≤ Fintype.card m →
      μ.real {ω | ∃ f : ℝ → ℝ, LipschitzOnWith L f (Set.Icc a b) ∧
        L * (b - a) * τ + jacksonApproximationConstant * L * (b - a) / (2 * q + 3) <
        |∫ x, f x ∂empiricalSpectralMeasure A -
          ∫ x, f x ∂slqMeasure A (√(Fintype.card n : ℝ) • U ω) (q + 1)|} ≤ δ := by
  refine ⟨1, one_pos, ?_⟩
  intro Ω n m _ _ _ _ μ U A a b L q τ δ hind hU hA hab hs hτ hδ hm
  have hm' : Real.log (2 * Fintype.card n / δ) / ((Fintype.card n + 2) * τ ^ 2) ≤
      Fintype.card m := by
    rcases le_or_gt (Real.log (2 * Fintype.card n / δ)) 0 with hl | hl
    · exact (div_nonpos_of_nonpos_of_nonneg hl (by positivity)).trans (Nat.cast_nonneg _)
    · rcases Nat.eq_zero_or_pos (Fintype.card n) with h0 | hpos
      · simp [h0]
      · have hn : (0 : ℝ) < Fintype.card n := Nat.cast_pos.mpr hpos
        calc Real.log (2 * Fintype.card n / δ) / ((Fintype.card n + 2) * τ ^ 2)
            ≤ Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) :=
              div_le_div_of_nonneg_left hl.le (by positivity) (by gcongr; linarith)
          _ = 1 * Real.log (2 * Fintype.card n / δ) / (Fintype.card n * τ ^ 2) := by ring
          _ ≤ Fintype.card m := hm
  exact
    measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le_of_hasLaw_uniformSphereVector_of_log_div_le
      hind hU hA hab hs L q hτ hδ hm'

end NLAlib
