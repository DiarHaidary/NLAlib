/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Gauss

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

The theorems (identities, masses, supports, moment matching, unbiasedness, and the tails uniform
over Lipschitz test functions) are deferred to
`NLAlibScaffold/Estimation/Spectral/SpectralDensity.lean` (`docs/design/Estimation-SLQ.md`).

## Main definitions

* `NLAlib.probeSpectralMeasure`: the average of the probe densities.
* `NLAlib.slqMeasure`: the average of their Gauss rules.

## Main results

* `NLAlib.isFiniteMeasure_probeSpectralMeasure`, `NLAlib.isFiniteMeasure_slqMeasure`: both are
  finite measures.
-/

@[expose] public section

open MeasureTheory
open scoped NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

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

end NLAlib
