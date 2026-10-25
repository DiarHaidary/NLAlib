/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Spectral.SpectralDensity

/-!
# Spectral density estimation: the asymptotic form of the Lipschitz tail

Statement for `NLAlib/Estimation/Spectral/SpectralDensity.lean` whose proof is deferred
(`docs/design/Estimation-SLQ.md`, §3.6): the sample-size form, with an absolute constant, of
`NLAlib.measureReal_exists_abs_integral_empiricalSpectralMeasure_sub_integral_slqMeasure_gt_le`,
the tail with independent sub-Gaussian entries uniform over Lipschitz test functions. The rest of
the stage is proved and lives in the `NLAlib` file.

## Main results

* The asymptotic form, $O(c^2\log(\lvert n\rvert/\delta)/(\lvert n\rvert\tau^2))$ probes suffice
  (the only theorem of the file; its name is too long for this list).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace NLAlib

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

end NLAlib
