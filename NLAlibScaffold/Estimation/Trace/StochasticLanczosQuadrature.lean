/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.StochasticLanczosQuadrature
public import NLAlibScaffold.Polynomial.Orthogonal.Gauss

/-!
# SLQ brackets the Girard–Hutchinson estimate: the theorems of stage KS8

Statements for `NLAlib/Estimation/Trace/StochasticLanczosQuadrature.lean` whose proofs are
deferred (`docs/design/Polynomial-QuadratureRemainder.md`, S1, S2). For every test matrix, SLQ
with $q$ Lanczos steps is below the Girard–Hutchinson estimate of
$\operatorname{tr}f(\mathbf{A})$ when $f^{(2q)} \ge 0$ on an interval containing the spectrum,
and above it when $f^{(2q)} \le 0$: the quadrature error has a sign probe by probe, so the
SLQ error is the Girard–Hutchinson error plus a one-signed bias.

## Main results

* `NLAlib.re_slq_le_re_girardHutchinson_cfc_of_iteratedDeriv_nonneg`,
  `NLAlib.re_girardHutchinson_cfc_le_re_slq_of_iteratedDeriv_nonpos`: the sign of
  the SLQ bias.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]

/-- **SLQ underestimates for $f$ with nonnegative derivative of order $2q$**: for
$\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$), $a < a'$,
$q > 0$, $f$ continuous on $[a, a']$,
$C^{2q}$ on $(a, a')$ with $f^{(2q)} \ge 0$ there, and every test matrix $\mathbf{\Omega}$,
$$\operatorname{Re}\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q) \le
\operatorname{Re}\mathsf{girardHutchinson}(f(\mathbf{A}), \mathbf{\Omega})\,.$$
[UbaruChenSaad2017, §3]; [GolubMeurant2010, Ch. 7] (locators to check); the per-probe Gauss
bound summed.
Proof: S, about 20 lines. Unfold `slq` and `girardHutchinson` (`Matrix.trace`,
`Matrix.mul_apply`: the trace of $\mathbf{\Omega}^{\mathsf{H}}f(\mathbf{A})\mathbf{\Omega}$ is
$\sum_j\boldsymbol{\omega}_j^{\mathsf{H}}f(\mathbf{A})\boldsymbol{\omega}_j$, as in the proofs
in `NLAlib/Estimation/Trace/GirardHutchinson.lean`), take real parts (`RCLike.div_re`-style with
the real cardinality), and sum `integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg` for
each $\mu_{\mathbf{A},\boldsymbol{\omega}_j}$ (`ae_mem_Icc_spectralMeasure`) with
`integral_spectralMeasure` (`Finset.sum_le_sum`, `div_le_div_of_nonneg_right`). -/
theorem re_slq_le_re_girardHutchinson_cfc_of_iteratedDeriv_nonneg {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (haa' : a < a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', 0 ≤ iteratedDeriv (2 * q) f x) (Ω : Matrix n m 𝕜) :
    RCLike.re (slq A f Ω q) ≤ RCLike.re (girardHutchinson (cfc f A) Ω) := by
  have hslq : RCLike.re (slq A f Ω q) =
      (∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q) /
        Fintype.card m := by
    unfold slq
    rw [div_eq_mul_inv, div_eq_mul_inv, ← RCLike.ofReal_natCast, ← RCLike.ofReal_inv,
      RCLike.re_mul_ofReal, RCLike.ofReal_re]
  have hgh : RCLike.re (girardHutchinson (cfc f A) Ω) =
      (∑ j, RCLike.re (quadForm (cfc f A) fun i => Ω i j)) / Fintype.card m := by
    rw [girardHutchinson_eq_sum, div_eq_mul_inv, div_eq_mul_inv, ← RCLike.ofReal_natCast,
      ← RCLike.ofReal_inv, RCLike.re_mul_ofReal]
    congr 1
    exact map_sum RCLike.reLm _ _
  rw [hslq, hgh]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg _)
  rw [← integral_spectralMeasure A (fun i => Ω i j) f]
  exact integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg
    (ae_mem_Icc_spectralMeasure A hs _) haa' hq hf hf' hD

/-- **SLQ overestimates for $f$ with nonpositive derivative of order $2q$**: for
$\mathbf{A}$ with spectrum in $[a, a']$ (Hermitian; otherwise both sides are $0$), $a < a'$,
$q > 0$, $f$ continuous on $[a, a']$,
$C^{2q}$ on $(a, a')$ with $f^{(2q)} \le 0$ there (such as $\log$ on $[a, a']$, $a > 0$), and
every test matrix $\mathbf{\Omega}$,
$$\operatorname{Re}\mathsf{girardHutchinson}(f(\mathbf{A}), \mathbf{\Omega}) \le
\operatorname{Re}\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q)\,.$$
[UbaruChenSaad2017, §3]; [GolubMeurant2010, Ch. 7] (locators to check).
Proof: S, about 20 lines. As
`re_slq_le_re_girardHutchinson_cfc_of_iteratedDeriv_nonneg`, with
`integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos`. -/
theorem re_girardHutchinson_cfc_le_re_slq_of_iteratedDeriv_nonpos {A : Matrix n n 𝕜}
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') (haa' : a < a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) {q : ℕ} (hq : 0 < q)
    (hf' : ContDiffOn ℝ (2 * q : ℕ) f (Set.Ioo a a'))
    (hD : ∀ x ∈ Set.Ioo a a', iteratedDeriv (2 * q) f x ≤ 0) (Ω : Matrix n m 𝕜) :
    RCLike.re (girardHutchinson (cfc f A) Ω) ≤ RCLike.re (slq A f Ω q) := by
  have hGH : RCLike.re (girardHutchinson (cfc f A) Ω) =
      (∑ j, ∫ x, f x ∂spectralMeasure A (fun i => Ω i j)) / Fintype.card m := by
    rw [girardHutchinson_eq_sum, ← RCLike.ofReal_natCast, RCLike.div_re_ofReal, map_sum]
    simp only [integral_spectralMeasure]
  have hSLQ : RCLike.re (slq A f Ω q) =
      (∑ j, ∫ x, f x ∂gaussQuadrature (spectralMeasure A (fun i => Ω i j)) q) / Fintype.card m := by
    unfold slq
    rw [← RCLike.ofReal_natCast, RCLike.div_re_ofReal, RCLike.ofReal_re]
  rw [hGH, hSLQ]
  refine div_le_div_of_nonneg_right (Finset.sum_le_sum fun j _ => ?_) (Nat.cast_nonneg _)
  exact integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos
    (ae_mem_Icc_spectralMeasure A hs _) haa' hq hf hf' hD

end NLAlib
