/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Spectral.SpectralDensity
public import NLAlibScaffold.Estimation.Trace.GirardHutchinson
public import NLAlibScaffold.Estimation.Trace.StochasticLanczosQuadrature
public import NLAlibScaffold.ForMathlib.MeasureTheory.Integral.Bochner.SumMeasure
public import NLAlibScaffold.RandomMatrix.Haar.Sphere

/-!
# Spectral density estimation: the theorems of stage SLQ, phase B

Statements for `NLAlib/Estimation/Spectral/SpectralDensity.lean` whose proofs are deferred
(`docs/design/Estimation-SLQ.md`, §§3.3–3.6). The probe spectral measure
`probeSpectralMeasure A Ω` integrates $f$ to the Girard–Hutchinson estimate of
$\operatorname{tr} f(\mathbf{A})/\lvert n\rvert$, so its distribution function at $x$ is a
Girard–Hutchinson estimate of a spectral projector; it is unbiased for isotropic probes. The SLQ
estimate `slqMeasure A Ω q` is the average of the Lanczos rules, matches $2q$ moments of the probe
spectral measure and equals it for $q \ge \lvert n\rvert$. With independent sub-Gaussian entries,
the distribution functions of the probe spectral measure and of the empirical spectral measure
$\nu_{\mathbf{A}}$ are uniformly close at the eigenvalues except with probability
$2\lvert n\rvert\exp(-\tfrac{1}{196}m\lvert n\rvert\min(\tau^2/c^2, \tau/c))$, and on that event a
finite Abel summation bounds the error on every Lipschitz test function at once, for the probe
measure, for SLQ (adding the Gauss error) and for the mass-normalised SLQ measure. With probes
$\sqrt{\lvert n\rvert}\,\mathbf{u}_j$, $\mathbf{u}_j$ independent and uniform on the unit
sphere, both measures are probability measures and the sharp Beta proxy gives the failure
probability $2\lvert n\rvert\exp(-m(\lvert n\rvert + 2)\tau^2)$, with no unknown constant.
[ChenTrogdonUbaru2021]; [ChenTrogdonUbaru2025]; [UbaruChenSaad2017].

## Main results

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
  SLQ approximates the spectral density uniformly in Lipschitz test functions; the
  mass-normalised form and the asymptotic form follow it.
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

/-! ### Integrals and the Lanczos form -/

/-- Every function is integrable against the probe spectral measure: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$ and every $f : \mathbb{R} \to \mathbb{R}$, $f$
is integrable against `probeSpectralMeasure A Ω`, a finite atomic measure.
Proof: S, about 8 lines. Unfold `probeSpectralMeasure`; `Integrable.smul_measure_nnreal`,
`integrable_finset_sum_measure`, `integrable_spectralMeasure`. -/
theorem integrable_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (f : ℝ → ℝ) :
    Integrable f (probeSpectralMeasure A Ω) := by
  unfold probeSpectralMeasure
  exact (integrable_finsetSum_measure.2 fun j _ =>
    integrable_spectralMeasure _ _ f).smul_measure_nnreal

/-- Every function is integrable against the SLQ spectral-density estimate: for every square
$\mathbf{A}$, every test matrix $\mathbf{\Omega}$, every $q$ and every
$f : \mathbb{R} \to \mathbb{R}$, $f$ is integrable against `slqMeasure A Ω q`, a finite sum of
Dirac masses.
Proof: S, about 8 lines. Unfold `slqMeasure`; `Integrable.smul_measure_nnreal`,
`integrable_finset_sum_measure`, `integrable_gaussQuadrature` (KS7). -/
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
method.
Proof: S, about 20 lines. `integral_smul_nnreal_measure`, `integral_finsetSum_measure`
(`integrable_spectralMeasure`), `integral_spectralMeasure`, `girardHutchinson_eq_sum`, `map_sum`,
the real part of a division by a natural number (`RCLike.div_re_ofReal`, `map_div₀`),
`NNReal.coe_inv`, `NNReal.coe_mul`; `field_simp`. -/
theorem integral_probeSpectralMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) :
    ∫ x, f x ∂probeSpectralMeasure A Ω =
      RCLike.re (girardHutchinson (cfc f A) Ω) / Fintype.card n := by
  have hdiv : ∀ z : 𝕜, RCLike.re (z / (Fintype.card m : 𝕜)) = RCLike.re z / Fintype.card m :=
    fun z => by rw [← RCLike.ofReal_natCast, RCLike.div_re_ofReal]
  unfold probeSpectralMeasure
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure, girardHutchinson_eq_sum, hdiv,
    map_sum]
  · simp only [integral_spectralMeasure, NNReal.smul_def, smul_eq_mul, NNReal.coe_inv,
      NNReal.coe_mul, NNReal.coe_natCast]
    ring
  · exact fun i _ => integrable_spectralMeasure _ _ _

/-- The SLQ spectral-density estimate integrates every $f$ to the SLQ trace estimate divided by
$\lvert n\rvert$: for every square $\mathbf{A}$, every $f : \mathbb{R} \to \mathbb{R}$, every
test matrix $\mathbf{\Omega}$ and every $q$,
$$\int f\,d\,\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) =
\frac{\operatorname{Re}\,\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)}{\lvert n\rvert}\,.$$
Proof: S, about 15 lines. `integral_smul_nnreal_measure`, `integral_finsetSum_measure`
(`integrable_gaussQuadrature`, KS7), unfold `slq`; `RCLike.ofReal_re` after `map_div₀`
(`RCLike.div_re_ofReal`), `NNReal.coe_inv`, `NNReal.coe_mul`; `field_simp`. -/
theorem integral_slqMeasure (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ∫ x, f x ∂slqMeasure A Ω q = RCLike.re (slq A f Ω q) / Fintype.card n := by
  unfold slqMeasure slq
  rw [integral_smul_nnreal_measure, integral_finsetSum_measure]
  · rw [← RCLike.ofReal_natCast (Fintype.card m), ← RCLike.ofReal_div, RCLike.ofReal_re]
    simp only [NNReal.smul_def, NNReal.coe_inv, NNReal.coe_mul, NNReal.coe_natCast, smul_eq_mul]
    field_simp
  · intro j _
    exact integrable_gaussQuadrature _ _ _

/-- **The SLQ measure is the average of the probes' Lanczos rules**: for Hermitian $\mathbf{A}$,
every test matrix $\mathbf{\Omega}$ with columns $\boldsymbol{\omega}_j$ and every $q$,
$$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) = \frac{1}{\lvert n\rvert m}\sum_{j=1}^m
\mathsf{lanczosQuadrature}(\mathbf{A}, \boldsymbol{\omega}_j, q)\,,$$
the identification of each probe's Gauss rule with its Lanczos rule; atoms at the Ritz values,
weights from the tridiagonal matrices (`Matrix.IsHermitian.lanczosQuadrature_succ_eq_sum`).
Proof: S, about 4 lines. Unfold `slqMeasure`; `Finset.sum_congr` with
`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature` (KS7). -/
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
(`isStarProjection_cfc_indicator`). No measurability of $S$ is needed.
Proof: S, about 20 lines. `measureReal_def`, `Measure.smul_apply`, `Measure.coe_finsetSum`,
`ENNReal.toReal_sum` (finiteness: `measure_ne_top`), `spectralMeasure_real` per probe,
`girardHutchinson_eq_sum`, `map_sum`, `RCLike.div_re_ofReal`-type rewriting, `NNReal.coe_inv`. -/
theorem probeSpectralMeasure_real (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) (S : Set ℝ) :
    (probeSpectralMeasure A Ω).real S =
      RCLike.re (girardHutchinson (cfc (S.indicator fun _ => (1 : ℝ)) A) Ω) /
        Fintype.card n := by
  sorry

/-- The mass of the probe spectral measure: for Hermitian $\mathbf{A}$ and every test matrix
$\mathbf{\Omega}$,
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(\mathbb{R}) =
\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$.
Proof: S, about 15 lines. `measureReal_def`, `Measure.smul_apply`, `Measure.coe_finsetSum`,
`ENNReal.toReal_sum`, `Matrix.IsHermitian.spectralMeasure_real_univ` per probe,
`frobNorm_sq_eq_sum_col` (`Matrix.col_apply`); `NNReal.coe_inv`, `div_eq_inv_mul`. -/
theorem _root_.Matrix.IsHermitian.probeSpectralMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) :
    (probeSpectralMeasure A Ω).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m) := by
  sorry

/-- The mass of the SLQ spectral-density estimate: for Hermitian $\mathbf{A}$, every test matrix
$\mathbf{\Omega}$ and $q > 0$,
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)(\mathbb{R}) =
\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$, the mass of the probe spectral measure.
Proof: S, about 15 lines. As `Matrix.IsHermitian.probeSpectralMeasure_real_univ`, with
`gaussQuadrature_real_univ` (KS7, $q > 0$; support `ae_mem_Icc_spectralMeasure` on an interval
containing the finite spectrum) and `Matrix.IsHermitian.spectralMeasure_real_univ` per probe. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_real_univ {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ} (hq : 0 < q) :
    (slqMeasure A Ω q).real Set.univ =
      frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m) := by
  sorry

/-- The probe spectral measure lives on the spectrum: for every square $\mathbf{A}$ and every
test matrix $\mathbf{\Omega}$, almost every point of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ is an eigenvalue of $\mathbf{A}$.
Proof: S, about 10 lines. `ae_iff`, `Measure.smul_apply`, `Measure.coe_finsetSum`,
`Finset.sum_apply`, `spectralMeasure_compl_spectrum_eq_zero` per probe, `smul_zero`. -/
theorem ae_mem_spectrum_probeSpectralMeasure (A : Matrix n n 𝕜) (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ spectrum ℝ A := by
  sorry

/-- The probe spectral measure lives in every interval containing the spectrum: for every square
$\mathbf{A}$ with spectrum in $[a, a']$ and every test matrix $\mathbf{\Omega}$, almost every
point of $\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ lies in $[a, a']$.
Proof: S, about 3 lines. `filter_upwards [ae_mem_spectrum_probeSpectralMeasure A Ω]` with
`hs`. -/
theorem ae_mem_Icc_probeSpectralMeasure (A : Matrix n n 𝕜) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜) :
    ∀ᵐ x ∂probeSpectralMeasure A Ω, x ∈ Set.Icc a a' := by
  sorry

/-- The SLQ spectral-density estimate lives in every interval containing the spectrum: for
Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, every test matrix $\mathbf{\Omega}$ and every
$q$, almost every point of $\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)$ lies in
$[a, a']$: the Ritz values lie between the extreme eigenvalues.
Proof: S, about 12 lines. As `ae_mem_spectrum_probeSpectralMeasure`, with
`ae_mem_Icc_gaussQuadrature` (KS7) and `ae_mem_Icc_spectralMeasure` per probe. -/
theorem _root_.Matrix.IsHermitian.ae_mem_Icc_slqMeasure {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (Ω : Matrix n m 𝕜)
    (q : ℕ) : ∀ᵐ x ∂slqMeasure A Ω q, x ∈ Set.Icc a a' := by
  sorry

/-! ### Moments and exactness -/

/-- **SLQ matches $2q$ moments of the probe spectral measure**: for Hermitian $\mathbf{A}$, every
test matrix $\mathbf{\Omega}$ and every $q$, the probe spectral measure and
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q)$ give every real polynomial of degree less
than $2q$ the same integral: each probe density matches $2q$ moments of its Gauss rule, and the
averages match. [Gautschi2004, Theorem 1.45]; [GolubMeurant2010, Ch. 6]; there for one measure,
here probe by probe and averaged.
Proof: S, about 20 lines. An interval containing the finite spectrum
(`A.finite_real_spectrum.isCompact.isBounded`, or the extreme eigenvalues) and
`ae_mem_Icc_spectralMeasure`; per probe `matchesMoments_gaussQuadrature` (KS7); the sum by
`MatchesMoments.finsetSum` (KS7) and the scalar by `MatchesMoments.smul` (KS7, through
`ENNReal.coe_smul`-type rewriting of the `ℝ≥0` action).
Result: gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) (q : ℕ) :
    MatchesMoments (probeSpectralMeasure A Ω) (slqMeasure A Ω q) (2 * q) := by
  sorry

/-- With at least $\lvert n\rvert$ nodes SLQ is exact: for Hermitian $\mathbf{A}$, every test
matrix $\mathbf{\Omega}$ and $q \ge \lvert n\rvert$,
$\mathsf{slqMeasure}(\mathbf{A}, \mathbf{\Omega}, q) =
\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$: each probe density lives on at most
$\lvert n\rvert \le q$ points, so it is its own $q$-point Gauss rule.
Proof: S, about 12 lines. Unfold both; per probe `MatchesMoments.eq_gaussQuadrature` (KS7) with
`MatchesMoments.refl`, `s := A.finite_real_spectrum.toFinset`
(`spectralMeasure_compl_spectrum_eq_zero`), card at most `Fintype.card n ≤ q`
(`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, `Finset.card_image_le`-type); `.symm`. -/
theorem _root_.Matrix.IsHermitian.slqMeasure_eq_probeSpectralMeasure_of_card_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Ω : Matrix n m 𝕜) {q : ℕ}
    (hq : Fintype.card n ≤ q) : slqMeasure A Ω q = probeSpectralMeasure A Ω := by
  sorry

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
Proof: S, about 20 lines. `integral_probeSpectralMeasure` under the integral, `integral_div`,
`integral_re` (integrability: `IsIsotropic.integrable_quadForm` summed through
`girardHutchinson_eq_sum`), `integral_girardHutchinson`,
`Matrix.IsHermitian.integral_empiricalSpectralMeasure`.
Result: probe-spectral-measure-unbiased -/
theorem integral_integral_probeSpectralMeasure [Nonempty m] {X : Ω → Matrix n m 𝕜}
    (hX : ∀ j, IsIsotropic (fun ω i => X ω i j) μ) {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) :
    ∫ ω, (∫ x, f x ∂probeSpectralMeasure A (X ω)) ∂μ = ∫ x, f x ∂empiricalSpectralMeasure A := by
  sorry

/-! ### Deterministic bounds over Lipschitz test functions -/

/-- **Distribution functions control Lipschitz test functions.** For Hermitian $\mathbf{A}$ with
spectrum in $[a, b]$, $a \le b$, a test matrix $\mathbf{\Omega}$ and $\tau \ge 0$: if at every
eigenvalue $x$ the distribution functions of $\nu_{\mathbf{A}}$ (the empirical spectral measure)
and of $\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$,
then every $f$ that is $L$-Lipschitz on $[a, b]$ has
$$\Bigl\lvert\int f\,d\nu_{\mathbf{A}} -
\int f\,d\,\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})\Bigr\rvert \le
(\lvert f(b)\rvert + L(b - a))\tau\,.$$
Proof: S, about 20 lines. `MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith` with
`s := A.finite_real_spectrum.toFinset` (`Set.Finite.mem_toFinset`); supports
`Matrix.IsHermitian.ae_mem_spectrum_empiricalSpectralMeasure` and
`ae_mem_spectrum_probeSpectralMeasure`; `hs` for $s \subseteq [a, b]$. -/
theorem
_root_.Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a ≤ b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ)
    {f : ℝ → ℝ} {L : ℝ≥0} (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂empiricalSpectralMeasure A - ∫ x, f x ∂probeSpectralMeasure A Ω| ≤
      (|f b| + L * (b - a)) * τ := by
  sorry

/-- **The Kolmogorov event controls the mass**: for Hermitian $\mathbf{A}$, $n$ nonempty, and a
test matrix $\mathbf{\Omega}$: if at every eigenvalue the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$, then
$\lvert 1 - \mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})(\mathbb{R})\rvert \le
\tau$, the mass being $\|\mathbf{\Omega}\|_{\mathsf{F}}^2/(\lvert n\rvert m)$: at the largest
eigenvalue both distribution functions equal the masses.
Proof: S, about 20 lines. $x^\ast$ the largest eigenvalue (`Finset.max'` of
`A.finite_real_spectrum.toFinset`, nonempty for nonempty $n$ via
`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`);
`(empiricalSpectralMeasure A).real (Set.Iic x*) = 1`
(`Matrix.IsHermitian.ae_mem_spectrum_empiricalSpectralMeasure`, `measureReal_congr`,
`measureReal_univ_eq_one`); the probe distribution function at $x^\ast$ is its mass
(`ae_mem_spectrum_probeSpectralMeasure`, `measureReal_congr`); `hK x*`. -/
theorem _root_.Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le [Nonempty n]
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ}
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) :
    |1 - (probeSpectralMeasure A Ω).real Set.univ| ≤ τ := by
  sorry

/-- From the eigenvalues to every threshold: for Hermitian $\mathbf{A}$, a test matrix
$\mathbf{\Omega}$ and $\tau \ge 0$, if at every eigenvalue the distribution functions of
$\nu_{\mathbf{A}}$ (the empirical spectral measure) and of
$\mathsf{probeSpectralMeasure}(\mathbf{A}, \mathbf{\Omega})$ differ by at most $\tau$, then they
differ by at most $\tau$ at every $x \in \mathbb{R}$: both are constant between eigenvalues and
$0$ below the smallest.
Proof: S, about 25 lines. `s := A.finite_real_spectrum.toFinset`, both measures carried by `s`;
`MeasureTheory.measureReal_Iic_eq_sum` for both; if no eigenvalue is $\le x$ both sums are empty
(`Finset.filter_false_of_mem`) and `hτ`; else $x'$ the largest eigenvalue $\le x$ (`Finset.max'`
of the filter) has the same filter (`Finset.filter_congr`), so `hK x'`. -/
theorem
_root_.Matrix.IsHermitian.abs_empiricalSpectralMeasure_real_Iic_sub_probeSpectralMeasure_real_Iic_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {Ω : Matrix n m 𝕜} {τ : ℝ} (hτ : 0 ≤ τ)
    (hK : ∀ x ∈ spectrum ℝ A, |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ) (x : ℝ) :
    |(empiricalSpectralMeasure A).real (Set.Iic x) -
      (probeSpectralMeasure A Ω).real (Set.Iic x)| ≤ τ := by
  sorry

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
[ChenTrogdonUbaru2022, Appendix C, Theorem 38], the approximation step.
Proof: S, about 25 lines. `integral_smul_nnreal_measure`, `integral_finsetSum_measure`
(`integrable_probeSpectralMeasure`'s and `integrable_slqMeasure`'s ingredients:
`integrable_spectralMeasure`, `integrable_gaussQuadrature`), `← mul_sub`,
`← Finset.sum_sub_distrib`, `Finset.abs_sum_le_sum_abs`; per probe
`abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith` (KS7) with
`ae_mem_Icc_spectralMeasure`; the masses sum to `frobNorm Ω ^ 2`
(`Matrix.IsHermitian.spectralMeasure_real_univ`, `frobNorm_sq_eq_sum_col`). -/
theorem
_root_.Matrix.IsHermitian.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a b : ℝ} (hab : a < b)
    (hs : spectrum ℝ A ⊆ Set.Icc a b) (Ω : Matrix n m 𝕜) (q : ℕ) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) :
    |∫ x, f x ∂probeSpectralMeasure A Ω - ∫ x, f x ∂slqMeasure A Ω (q + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * q + 3) *
        (frobNorm Ω ^ 2 / (Fintype.card n * Fintype.card m)) := by
  sorry

/-! ### Tails with independent sub-Gaussian entries -/

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
helps" effect.
Proof: M, about 55 lines (split off a private helper "the exponent decreases when
$\|\mathbf{B}\|_{\mathsf{F}}^2 \le 1/n$ and $\|\mathbf{B}\|_2 \le 1/n$", 20 to 30 lines, if
longer). Rewrite the event with `probeSpectralMeasure_real` and
`Matrix.IsHermitian.empiricalSpectralMeasure_real` over ℝ (`RCLike.re_to_real`) as the
Girard–Hutchinson event of `B := (1 / card n) • cfc 1_S A` (`girardHutchinson_smul`,
`Matrix.trace_smul`); `measureReal_abs_trace_sub_girardHutchinson_ge_le` at `B`;
`isStarProjection_cfc_indicator` with `IsStarProjection.frobNorm_sq_eq_rank`,
`Matrix.rank_le_card_width`, `IsStarProjection.specNorm_le_one`, `frobNorm_smul`,
`specNorm_smul`; monotonicity `Real.exp_le_exp`, `min_le_min`, `div_le_div_of_nonneg_left`; the
cases `B = 0`, `c = 0` and empty `n` separately. -/
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
  sorry

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
Proof: S/M, about 30 lines. The event is contained in
`⋃ x ∈ A.finite_real_spectrum.toFinset, {ω | τ ≤ |…|}` (`Set.Finite.mem_toFinset`, `le_of_lt`);
`measureReal_mono`, `measureReal_biUnion_finset_le`,
`measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le` per point,
`Finset.sum_le_card_nsmul`; a private helper, the spectrum has at most `Fintype.card n` points
(`Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`, `Finset.card_image_le`), 10 to 15
lines.
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
  sorry

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
Proof: S, about 20 lines. `measureReal_mono` into the event of
`measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le`: on
its complement (`not_lt`, `push_neg`)
`Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le`
gives `≤`, contradicting `<`.
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
  sorry

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
Proof: S/M, about 30 lines. `measureReal_mono` into the event of
`measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le`; on
its complement the triangle inequality through the probe spectral measure (`abs_sub_le`),
`Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le`,
`Matrix.IsHermitian.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith`,
and the mass at most $1 + \tau$ by
`Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le` with
`Matrix.IsHermitian.probeSpectralMeasure_real_univ`; empty $n$ (`isEmpty_or_nonempty`): both
integrals are $0$.
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
  sorry

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
Proof: S/M, about 40 lines. On the complement of the event of
`measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le`:
`Matrix.IsHermitian.abs_one_sub_probeSpectralMeasure_real_univ_le` gives mass $M > 0$;
`integral_smul_measure`; at each eigenvalue the normalised distribution functions differ by at
most $2\tau$ (the probe one by $\tau$, plus $(F/M)\lvert M - 1\rvert \le \tau$);
`MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith` on $f - f(b)$
(`LipschitzOnWith.sub_const`) between $\nu_{\mathbf{A}}$ and the normalised probe measure; the
normalised probe and SLQ measures match $2(q + 1)$ moments
(`Matrix.IsHermitian.matchesMoments_probeSpectralMeasure_slqMeasure`, `MatchesMoments.smul`), so
`MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn` with Jackson's polynomial of
degree $2q + 1$ (`exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith`).
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
  sorry

-- The declaration name, or a name in its docstring, exceeds 100 characters.
set_option linter.style.longLine false in
/-- **$O(c^2\log(\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2))$ probes suffice for SLQ to
approximate the spectral density, uniformly in Lipschitz test functions**: there is an absolute
constant $C > 0$ such that the following holds. Let the entries of the real $n \times m$ test
matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian moment generating
function bound with variance proxy $c$ and having second moment $1$; let $\mathbf{A}$ be real
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
Proof: M, about 50 lines. `C := 196`; the explicit theorem; for $n$, $m$ nonempty, $c \ge 1$ by
`HasSubgaussianMGF.integral_sq_le` with `hvar` at some entry (`hind.isProbabilityMeasure`), so
`min_eq_left` from $\tau \le 1 \le c$; `le_hansonWrightConstant`-type comparison (the current
value $1/196$); `Real.exp_log`, `Real.exp_le_exp`, `Real.log_le_log`; empty $n$: the bound is
$0$; empty $m$ with nonempty $n$: the size hypothesis fails ($\log 2 > 0$).
Asymptotic:
NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le
Result: spectral-density-lipschitz-tail -/
theorem
exists_forall_measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le :
    ∃ C : ℝ, 0 < C ∧ ∀ {Ω n m : Type} [MeasurableSpace Ω] [Fintype n] [DecidableEq n]
      [Fintype m] (μ : Measure Ω) (X : Ω → Matrix n m ℝ) (c : ℝ≥0)
      (A : Matrix n n ℝ) (a b : ℝ) (L : ℝ≥0) (q : ℕ) (τ δ : ℝ),
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
  sorry

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
[ChenTrogdonUbaru2021, §3] (locator to check).
Proof: S/M, about 40 lines. Rewrite the event with `probeSpectralMeasure_real` and
`Matrix.IsHermitian.empiricalSpectralMeasure_real` over ℝ (`RCLike.re_to_real`): with
$\mathbf{P} = \mathbf{1}_S(\mathbf{A})$ (`isStarProjection_cfc_indicator`), write
$\mathbf{P} = \mathbf{V}\mathbf{V}^{\mathsf{H}}$ with $\mathbf{V}$ of $r = \operatorname{rank}
\mathbf{P}$ orthonormal columns (`IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq`
with `p := Fin r`), so $\operatorname{tr}\mathbf{P} = r$ (`IsStarProjection.trace_eq_rank`) and
the probe estimate is $\frac1m\sum_j\|\mathbf{V}^{\mathsf{H}}\mathbf{u}_j\|^2$
(`girardHutchinson_eq_sum`, `quadForm`, `Matrix.mulVec_smul`, $(\sqrt{n})^2 = n$); then
`measureReal_abs_sum_norm_conjTranspose_mulVec_sq_div_card_sub_div_card_ge_le_of_hasLaw_uniformSphereVector`
with `u j := fun ω i => U ω i j`; empty $n$: both sides of the event are $0$. -/
theorem
measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) (S : Set ℝ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ ≤ |(empiricalSpectralMeasure A).real S -
        (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real S|} ≤
      2 * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  sorry

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
Proof: S, about 25 lines. As
`measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le`: the
event is contained in `⋃ x ∈ A.finite_real_spectrum.toFinset, {ω | τ ≤ |…|}`
(`Set.Finite.mem_toFinset`, `le_of_lt`); `measureReal_mono`, `measureReal_biUnion_finset_le`,
`measureReal_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_ge_le_of_hasLaw_uniformSphereVector`
per point, `Finset.sum_le_card_nsmul`, and the private helper of that theorem bounding the
number of eigenvalues by `Fintype.card n`.
Result: spectral-density-kolmogorov-tail -/
theorem
measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le_of_hasLaw_uniformSphereVector
    {U : Ω → Matrix n m ℝ} (hind : iIndepFun (fun j ω i => U ω i j) μ)
    (hU : ∀ j, HasLaw (fun ω i => U ω i j) (uniformSphereVector n) μ) {A : Matrix n n ℝ}
    (hA : A.IsHermitian) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ∃ x ∈ spectrum ℝ A, τ < |(empiricalSpectralMeasure A).real (Set.Iic x) -
        (probeSpectralMeasure A (√(Fintype.card n : ℝ) • U ω)).real (Set.Iic x)|} ≤
      2 * Fintype.card n * Real.exp (-(Fintype.card m * (Fintype.card n + 2) * τ ^ 2)) := by
  sorry

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
Proof: M, about 45 lines. `measureReal_mono_ae` into the event of
`measureReal_exists_abs_empiricalSpectralMeasure_real_sub_probeSpectralMeasure_real_gt_le_of_hasLaw_uniformSphereVector`
(an almost-everywhere superset): almost surely every probe has $\|\sqrt{n}\,\mathbf{u}_j\|^2 = n$
(`ae_norm_eq_one_uniformSphereVector` through `hU`, `ae_all_iff`), so the probe measure has mass
$1$ (`Matrix.IsHermitian.probeSpectralMeasure_real_univ`, `frobNorm_sq_eq_sum_col`); on that
event and off the Kolmogorov event, `MeasureTheory.abs_integral_sub_integral_le_of_lipschitzOnWith`
on $f - f(b)$ (`LipschitzOnWith.sub_const`; equal masses remove $\lvert f(b)\rvert$) between
$\nu_{\mathbf{A}}$ and the probe measure, as in
`Matrix.IsHermitian.abs_integral_empiricalSpectralMeasure_sub_integral_probeSpectralMeasure_le`;
`Matrix.IsHermitian.abs_integral_probeSpectralMeasure_sub_integral_slqMeasure_le_of_lipschitzOnWith`
with mass $1$; the triangle inequality (`abs_sub_le`); empty $n$: both integrals are $0$.
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
  sorry

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
[ChenTrogdonUbaru2021, the Wasserstein bound for SLQ] (theorem number to check).
Proof: S/M, about 25 lines. The tail form, then
$2n e^{-m(n+2)\tau^2} \le 2n e^{-\log(2n/\delta)} = \delta$: `Real.exp_le_exp` with the size
hypothesis times $(n+2)\tau^2 > 0$ (`div_le_iff₀`), `Real.exp_neg`, `Real.exp_log`; empty $n$:
the bound is $0 \le \delta$. -/
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
  sorry

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
Proof: S/M, about 20 lines. `C := 1`; the sample-size form, whose hypothesis follows since
$\lvert n\rvert\tau^2 \le (\lvert n\rvert + 2)\tau^2$ when the logarithm is nonnegative
(`div_le_div_of_nonneg_left`), and trivially ($m \ge 0$) when it is negative; empty $n$: the
threshold is $0$.
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
  sorry

end NLAlib
