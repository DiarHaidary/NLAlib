/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SpectralMeasure
public import NLAlib.Polynomial.Orthogonal.Gauss

/-!
# Stochastic Lanczos quadrature

For a square $\mathbf{A}$, a function $f : \mathbb{R} \to \mathbb{R}$ and a test matrix
$\mathbf{\Omega}$ whose $m$ columns $\boldsymbol{\omega}_1, \dots, \boldsymbol{\omega}_m$ are the
probes, the **stochastic Lanczos quadrature** estimate of $\operatorname{tr} f(\mathbf{A})$
replaces each single-probe Girard–Hutchinson term
$\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j = \int f\,d\mu_j$ by its
$q$-point Gauss rule, $\mu_j = \mu_{\mathbf{A},\boldsymbol{\omega}_j}$ the probe's spectral
measure, and averages over the probes. For Hermitian $\mathbf{A}$ this is what $q$ Lanczos steps
per probe compute. Its error is the Girard–Hutchinson error plus the averaged Gauss error, so
every Girard–Hutchinson result (unbiasedness, variance, tails) composes with every Gauss-rule
error bound (uniform approximation, Lipschitz, analytic). Exact arithmetic throughout.
[UbaruChenSaad2017]; [MartinssonTropp2020].

The theorems are deferred to `NLAlibScaffold/Estimation/Trace/StochasticLanczosQuadrature.lean`
(`docs/design/Estimation-SLQ.md`).

## Main definitions

* `NLAlib.slq`: the stochastic Lanczos quadrature estimate.
-/

@[expose] public section

open MeasureTheory

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

/-- The **stochastic Lanczos quadrature** estimate of $\operatorname{tr} f(\mathbf{A})$ from the
test matrix $\mathbf{\Omega}$, whose $m$ columns $\boldsymbol{\omega}_1, \dots,
\boldsymbol{\omega}_m$ are the probes: the average over the probes of the $q$-point Gauss rule of
each probe's spectral measure $\mu_j = \mu_{\mathbf{A},\boldsymbol{\omega}_j}$ applied to $f$,
$$\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) := \frac{1}{m}\sum_{j=1}^m
\int f\,d\,\mathsf{gaussQuadrature}(\mu_j, q)\,,$$
the Girard–Hutchinson estimate with each
$\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j = \int f\,d\mu_j$ replaced
by its Gauss quadrature. For Hermitian $\mathbf{A}$ this is what $q$ Lanczos steps per probe
compute, $\tfrac{1}{m}\sum_j\boldsymbol{\omega}_j^{\mathsf{H}}\mathsf{lanczosFA}(\mathbf{A}, f,
\boldsymbol{\omega}_j, q) = \tfrac{1}{m}\sum_j\|\boldsymbol{\omega}_j\|^2\mathbf{e}_1^{\mathsf{T}}
f(\mathbf{T}_j)\mathbf{e}_1$ (`Matrix.IsHermitian.slq_eq_sum_lanczosFA`), with $mq$ products with
$\mathbf{A}$. A real number in `𝕜`. Junk value: $0$ when $\mathbf{\Omega}$ has no columns, when
$q = 0$ and when $\mathbf{A}$ is not Hermitian.
[UbaruChenSaad2017, §3] (locator to check); [MartinssonTropp2020, §6.6, Algorithm 6]. -/
noncomputable def slq (A : Matrix n n 𝕜) (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) : 𝕜 :=
  ((∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q : ℝ) : 𝕜) /
    Fintype.card m

end NLAlib
