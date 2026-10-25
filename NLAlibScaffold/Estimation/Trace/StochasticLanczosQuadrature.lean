/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.GirardHutchinson
public import NLAlib.Estimation.Trace.StochasticLanczosQuadrature
public import NLAlib.Polynomial.Approximation.AnalyticApproximation
public import NLAlib.Krylov.Functions.Quadrature

/-!
# Stochastic Lanczos quadrature: the theorems of stage SLQ, phase A

Statements for `NLAlib/Estimation/Trace/StochasticLanczosQuadrature.lean` whose proofs are
deferred (`docs/design/Estimation-SLQ.md`, §3.2). For Hermitian $\mathbf{A}$ the estimate
`slq A f Ω q` is what $q$ Lanczos steps per probe compute. Its error splits into the
Girard–Hutchinson error of $f(\mathbf{A})$ plus the averaged per-probe Gauss error
$2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2/m$, $\varepsilon$ the uniform distance from $f$
to polynomials of degree less than $2q$ on an interval containing the spectrum, with the
Lipschitz (Jackson) and analytic (Bernstein ellipse) rates; composing with the Hanson–Wright tail
of Girard–Hutchinson gives the tails with independent sub-Gaussian entries, the quadrature term
random inside the event. [UbaruChenSaad2017]; [CortinovisKressner2022]; [MartinssonTropp2020].

## Main results

* `Matrix.IsHermitian.slq_eq_sum_lanczosFA`: SLQ is what the Lanczos algorithm computes.
* `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn`: the error splits.
* `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_lipschitzOnWith`,
  `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_differentiableOn`: the Lipschitz and analytic
  rates.
* `NLAlib.measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn`,
  `NLAlib.measureReal_abs_trace_cfc_sub_slq_ge_le_of_lipschitzOnWith`,
  `NLAlib.measureReal_abs_trace_cfc_sub_slq_ge_le_of_differentiableOn`: the tails with
  independent sub-Gaussian entries.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### The algorithm -/

/-- A probe's Lanczos-FA quadratic form is real, for Hermitian $\mathbf{A}$. -/
private theorem coe_re_star_dotProduct_lanczosFA {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (b : n → 𝕜) (q : ℕ) :
    ((RCLike.re (star b ⬝ᵥ lanczosFA A f b q) : ℝ) : 𝕜) = star b ⬝ᵥ lanczosFA A f b q := by
  obtain ⟨k, Q, hQ, hK⟩ := exists_hasOrthonormalCols_range_eq_krylovSpace A b q
  have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
  have key : star b ⬝ᵥ lanczosFA A f b q = quadForm (cfc f (Qᴴ * A * Q)) (Qᴴ *ᵥ b) := by
    rw [hQ.lanczosFA_eq hK f, quadForm_def, Matrix.dotProduct_mulVec, Matrix.star_mulVec,
      Matrix.conjTranspose_conjTranspose]
  have hH : (cfc f (Qᴴ * A * Q)).IsHermitian := cfc_predicate (p := IsSelfAdjoint) f _
  rw [key, hH.coe_re_quadForm]

/-- **SLQ is what the Lanczos algorithm computes**: for Hermitian $\mathbf{A}$, every
$f : \mathbb{R} \to \mathbb{R}$, every test matrix $\mathbf{\Omega}$ with $m$ columns
$\boldsymbol{\omega}_j$ and every $q$,
$$\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) = \frac{1}{m}\sum_{j=1}^m
\boldsymbol{\omega}_j^{\mathsf{H}}\,\mathsf{lanczosFA}(\mathbf{A}, f, \boldsymbol{\omega}_j, q)\,:$$
each probe's Gauss rule is its Lanczos rule
(`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`) and the Lanczos rule
integrates $f$ to the Lanczos-FA quadratic form, which is real.
[MartinssonTropp2020, §6.6, Algorithm 6]; there as the definition.
Proof: S, about 25 lines. Unfold `slq`; per probe
`← Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature` and `integral_lanczosQuadrature`;
`star b ⬝ᵥ lanczosFA A f b q` is real: the frame form
`HasOrthonormalCols.lanczosFA_eq` makes it a quadratic form of the Hermitian
`cfc f (Qᴴ * A * Q)` (`cfc_predicate`); `RCLike.ofReal_re`-type rewriting, `Finset.sum_congr`,
`map_sum` (`RCLike.ofReal_sum`). -/
theorem _root_.Matrix.IsHermitian.slq_eq_sum_lanczosFA {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (Ω : Matrix n m 𝕜) (q : ℕ) :
    slq A f Ω q =
      (∑ j, star (fun i => Ω i j) ⬝ᵥ lanczosFA A f (fun i => Ω i j) q) / Fintype.card m := by
  unfold slq
  congr 1
  rw [RCLike.ofReal_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← hA.lanczosQuadrature_eq_gaussQuadrature, integral_lanczosQuadrature,
    coe_re_star_dotProduct_lanczosFA hA]

/-! ### The error, deterministically -/

/-- **The error of stochastic Lanczos quadrature splits** into the Girard–Hutchinson error and a
quadrature error: for Hermitian $\mathbf{A}$ with spectrum in $[a, a']$, if a real polynomial $p$
of degree less than $2q$ is within $\varepsilon$ of $f$ on $[a, a']$, then for every test matrix
$\mathbf{\Omega}$ with $m$ columns
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}\,.$$
Probe by probe, $\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j =
\int f\,d\mu_j$, $\mu_j$ the spectral measure of $\mathbf{A}$ and $\boldsymbol{\omega}_j$, is
replaced by its Gauss rule, whose error is at most
$2\varepsilon\mu_j(\mathbb{R}) = 2\varepsilon\|\boldsymbol{\omega}_j\|^2$; the errors are
averaged. With no columns both sides reduce to $\lvert\operatorname{tr} f(\mathbf{A})\rvert$.
[UbaruChenSaad2017, §4] (locator to check); [MartinssonTropp2020, §6.6]; there with the
quadrature error bounded through analytic $f$ and Chebyshev approximation.
Proof: S/M, about 35 lines. `girardHutchinson_eq_sum`, unfold `slq`, `← sub_div`,
`← Finset.sum_sub_distrib`; per probe `quadForm (cfc f A) ωⱼ = ∫ f ∂μⱼ` (`integral_spectralMeasure`;
the quadratic form of a Hermitian matrix is real, `Matrix.IsHermitian.coe_re_quadForm`-type),
then `abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn` on `μⱼ` with
`ae_mem_Icc_spectralMeasure`, `integrable_spectralMeasure`; the mass
`Matrix.IsHermitian.spectralMeasure_real_univ`; `norm_sum_le`, `frobNorm_sq_eq_sum_col`,
`norm_div`, `RCLike.norm_ofReal`; the case `Fintype.card m = 0` separately.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) (Ω : Matrix n m 𝕜) :
    ‖(cfc f A).trace - slq A f Ω q‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        2 * ε * frobNorm Ω ^ 2 / Fintype.card m := by
  have hH : (cfc f A).IsHermitian := cfc_predicate f A
  have hprobe : ∀ j, ‖quadForm (cfc f A) (fun i => Ω i j) -
      ((∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q : ℝ) : 𝕜)‖ ≤
        2 * ε * ‖WithLp.toLp 2 (Ω.col j)‖ ^ 2 := by
    intro j
    have hreal : quadForm (cfc f A) (fun i => Ω i j) =
        ((RCLike.re (quadForm (cfc f A) (fun i => Ω i j)) : ℝ) : 𝕜) := by
      refine RCLike.ext_iff.2 ⟨by simp, ?_⟩
      simpa [quadForm_def] using hH.im_star_dotProduct_mulVec_self (fun i => Ω i j)
    have hint := abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn
      (μ := spectralMeasure A (fun i => Ω i j)) (ae_mem_Icc_spectralMeasure A hs (fun i => Ω i j))
      (integrable_spectralMeasure A (fun i => Ω i j) f) hp hε
    rw [integral_spectralMeasure A (fun i => Ω i j) f,
      hA.spectralMeasure_real_univ] at hint
    rw [hreal, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
    exact hint
  have hdiff : (cfc f A).trace - slq A f Ω q - ((cfc f A).trace - girardHutchinson (cfc f A) Ω) =
      (∑ j, (quadForm (cfc f A) (fun i => Ω i j) -
        ((∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q : ℝ) : 𝕜))) /
        Fintype.card m := by
    rw [girardHutchinson_eq_sum, slq, RCLike.ofReal_sum, Finset.sum_sub_distrib, sub_div]
    ring
  calc ‖(cfc f A).trace - slq A f Ω q‖
      = ‖((cfc f A).trace - girardHutchinson (cfc f A) Ω) +
          ((cfc f A).trace - slq A f Ω q - ((cfc f A).trace - girardHutchinson (cfc f A) Ω))‖ := by
        congr 1; ring
    _ ≤ ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
          ‖(cfc f A).trace - slq A f Ω q - ((cfc f A).trace - girardHutchinson (cfc f A) Ω)‖ :=
        norm_add_le _ _
    _ ≤ ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
          2 * ε * frobNorm Ω ^ 2 / Fintype.card m := by
        gcongr
        rw [hdiff, norm_div, RCLike.norm_natCast]
        gcongr
        calc ‖∑ j, (quadForm (cfc f A) (fun i => Ω i j) -
              ((∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q : ℝ) : 𝕜))‖
            ≤ ∑ j, ‖quadForm (cfc f A) (fun i => Ω i j) -
              ((∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q : ℝ) : 𝕜)‖ :=
              norm_sum_le _ _
          _ ≤ ∑ j, 2 * ε * ‖WithLp.toLp 2 (Ω.col j)‖ ^ 2 :=
              Finset.sum_le_sum fun j _ => hprobe j
          _ = 2 * ε * frobNorm Ω ^ 2 := by
              rw [frobNorm_sq_eq_sum_col, Finset.mul_sum]

/-- **The error of stochastic Lanczos quadrature for Lipschitz functions**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $a < a'$, $f$ $L$-Lipschitz on $[a, a']$, every test
matrix $\mathbf{\Omega}$ with $m$ columns and every $q$, with $q + 1$ Lanczos steps per
probe, <!-- value jacksonApproximationConstant -->
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{\pi L(a' - a)}{2q + 3}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}\,;$$
the constant is `jacksonApproximationConstant`. Per probe, the Gauss-rule error for Lipschitz
functions (Jackson's theorem in degree $2q + 1$), averaged.
[UbaruChenSaad2017, §4] (locator to check); the rate from [ChenTrogdonUbaru2022, Appendix C,
Theorem 38], the approximation step.
Proof: S, about 20 lines. The proof of
`Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn` with
`abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith` (KS7, $k + 1 = q + 1$ nodes)
per probe in place of the uniform-approximation bound; `integrable_spectralMeasure`;
`Matrix.IsHermitian.spectralMeasure_real_univ`, `frobNorm_sq_eq_sum_col`; arithmetic.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_lipschitzOnWith
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) *
          (frobNorm Ω ^ 2 / Fintype.card m) := by
  sorry

/-- **The error of stochastic Lanczos quadrature for analytic functions**: let $\mathbf{A}$ be
Hermitian with spectrum in $[a, a']$, $a < a'$, and let $f$, transported to $[-1, 1]$ by the
affine map onto $[a, a']$, extend to a function $F$ holomorphic on the open Bernstein ellipse
$E_\rho$, $\rho > 1$, with $\lvert F\rvert \le M$ there. Then for every test matrix
$\mathbf{\Omega}$ with $m$ columns and every $q$, with $q + 1$ Lanczos steps per probe,
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{4M}{\rho^{2q + 1}(\rho - 1)}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}\,,$$
from the Chebyshev truncation of degree $2q + 1$.
[UbaruChenSaad2017, Theorem 4.1] (locator to check); the setting of their analysis, there with
relative error for positive definite $\mathbf{A}$.
Proof: S, about 15 lines. `exists_degree_le_isUniformApproxOn_Icc_of_differentiableOn` (`𝕜 := ℝ`)
at `N := 2 * q + 1` (the Bernstein corollary of the Gauss error that KS7 leaves to SLQ), its
degree bound turned into `p.degree < 2 * (q + 1)` (`Order.lt_add_one_iff`-type, `push_cast`), then
`Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn`; `hExt` matches after
`RCLike.toComplex` at `𝕜 := ℝ` (`Complex.ofReal`, `rfl` or `simp`); arithmetic.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_differentiableOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (haa : a < a')
    (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ} {ρ M : ℝ} (hρ : 1 < ρ)
    (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1))
    (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * (frobNorm Ω ^ 2 / Fintype.card m) := by
  sorry

/-! ### Tails with independent sub-Gaussian entries -/

/-- **The tail of stochastic Lanczos quadrature with sub-Gaussian probes.** Let the entries of the
real $n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and having second
moment $1$. Let $\mathbf{A}$ be real symmetric with spectrum in $[a, a']$ and let a real
polynomial $p$ of degree less than $2q$ be within $\varepsilon$ of $f$ on $[a, a']$. Then for
every $\tau \ge 0$, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{2\varepsilon\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m} \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\bigr\rvert\Bigr]
\le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`; the quadrature term is random, inside the event. No
definiteness of $f(\mathbf{A})$ is needed. Gaussian and sign test matrices are the case $c = 1$.
No measurability of the estimate is needed: the event lies in the Girard–Hutchinson event.
[UbaruChenSaad2017, Theorem 4.1] (locator to check), there for positive definite $\mathbf{A}$
with Rademacher probes and relative error; [CortinovisKressner2022, §4] (locator to check), the
indefinite case.
Proof: S, about 20 lines. `measureReal_mono` (a finite measure: `hind.isProbabilityMeasure`) into
the event of `measureReal_abs_trace_sub_girardHutchinson_ge_le` with `B := cfc f A`: on the event,
`Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn` over ℝ (`Real.norm_eq_abs`)
and `linarith` give `τ ≤ |tr f(A) - girardHutchinson (cfc f A) (X ω)|`.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {q : ℕ} {p : ℝ[X]}
    (hp : p.degree < 2 * q) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε) {τ : ℝ}
    (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 2 * ε * frobNorm (X ω) ^ 2 / Fintype.card m ≤
        |(cfc f A).trace - slq A f (X ω) q|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  sorry

/-- **The tail of stochastic Lanczos quadrature for Lipschitz functions.** Let the entries of the
real $n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ and having second moment $1$. Let
$\mathbf{A}$ be real symmetric with spectrum in $[a, a']$, $a < a'$, and $f$ $L$-Lipschitz on
$[a, a']$. Then for every $q$ and $\tau \ge 0$, with $q + 1$ Lanczos steps per probe and
quadrature term <!-- value jacksonApproximationConstant -->$\pi L(a' - a)/(2q + 3)$ per unit
of mass, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{\pi L(a' - a)}{2q + 3}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}
\le \bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega},
q + 1)\bigr\rvert\Bigr] \le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constants are `hansonWrightConstant` and `jacksonApproximationConstant`; the quadrature term
is random, inside the event. Gaussian and sign test matrices are the case $c = 1$.
[UbaruChenSaad2017, Theorem 4.1] (locator to check), there for analytic $f$;
[CortinovisKressner2022, §4] (locator to check).
Proof: S, about 15 lines. As `measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn`, with
`Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_lipschitzOnWith` in place of the
uniform-approximation split.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_lipschitzOnWith
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (haa : a < a') (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a a')) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + jacksonApproximationConstant * L * (a' - a) / (2 * q + 3) *
          (frobNorm (X ω) ^ 2 / Fintype.card m) ≤
        |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  sorry

/-- **The tail of stochastic Lanczos quadrature for analytic functions**, the setting of Ubaru,
Chen and Saad for any real symmetric matrix, in absolute error. Let the entries of the real
$n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ and having second moment $1$. Let
$\mathbf{A}$ be real symmetric with spectrum in $[a, a']$, $a < a'$, and let $f$, transported to
$[-1, 1]$ by the affine map onto $[a, a']$, extend to a function $F$ holomorphic on the open
Bernstein ellipse $E_\rho$, $\rho > 1$, with $\lvert F\rvert \le M$ there. Then for every $q$ and
$\tau \ge 0$, with $q + 1$ Lanczos steps per probe, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{4M}{\rho^{2q + 1}(\rho - 1)}\cdot
\frac{\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m} \le \bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert\Bigr] \le
2\exp\Bigl(-\frac{1}{196}\min\Bigl(\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`; the quadrature term is random, inside the event.
[UbaruChenSaad2017, Theorem 4.1] (locator to check), there for positive definite $\mathbf{A}$
with Rademacher probes and relative error; [CortinovisKressner2022, §4] (locator to check).
Proof: S, about 15 lines. As `measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn`, with
`Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_differentiableOn` in place of the
uniform-approximation split.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_differentiableOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (haa : a < a') (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ} {F : ℂ → ℂ}
    {ρ M : ℝ} (hρ : 1 < ρ) (hFd : DifferentiableOn ℂ F (openBernsteinEllipse ρ))
    (hM : Metric.IsUniformApproxOn F (fun _ => 0) (openBernsteinEllipse ρ) M)
    (hExt : Set.EqOn (fun t : ℝ => ((f (((a' - a) * t + a' + a) / 2) : ℝ) : ℂ))
      (fun t : ℝ => F t) (Set.Icc (-1 : ℝ) 1)) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 4 * M / (ρ ^ (2 * q + 1) * (ρ - 1)) * (frobNorm (X ω) ^ 2 / Fintype.card m) ≤
        |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  sorry

end NLAlib
