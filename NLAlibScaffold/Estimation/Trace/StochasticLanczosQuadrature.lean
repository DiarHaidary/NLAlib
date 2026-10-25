/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.StochasticLanczosQuadrature
public import NLAlib.Polynomial.Approximation.MinimaxError

/-!
# Stochastic Lanczos quadrature and the minimax error: the theorems of stage Poly-Best

Statements for `NLAlib/Estimation/Trace/StochasticLanczosQuadrature.lean` whose proofs are
deferred (`docs/design/Polynomial-BestApproximation.md`, §3.4): the error split and the
sub-Gaussian tail of SLQ with $q + 1$ Lanczos steps per probe, the quadrature term written with
the minimax error $E_{2q + 1}(f)$.

## Main results

* `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_continuousOn`: the deterministic split.
* `NLAlib.measureReal_abs_trace_cfc_sub_slq_ge_le_of_continuousOn`: the tail.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Polynomial
open scoped Matrix NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **The error of stochastic Lanczos quadrature and the minimax error**: for Hermitian
$\mathbf{A}$ with spectrum in $[a, a']$, $f$ continuous on $[a, a']$, every test matrix
$\mathbf{\Omega}$ with $m$ columns and $q + 1$ Lanczos steps per probe,
$$\bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert \le
\bigl\lvert\operatorname{tr} f(\mathbf{A}) - \mathsf{girardHutchinson}(f(\mathbf{A}),
\mathbf{\Omega})\bigr\rvert + \frac{2E_{2q + 1}(f; [a, a'])\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}
\,,$$
$E_{2q + 1}$ the error of the best uniform approximation of $f$ on $[a, a']$ by polynomials of
degree at most $2q + 1$ (`minimaxError`). [UbaruChenSaad2017, §4] (locator to check); there
with the quadrature error bounded through analytic $f$ and Chebyshev approximation.
Proof: S, about 8 lines. `exists_degree_le_isUniformApproxOn_minimaxError` in degree $2q + 1$,
$2q + 1 < 2(q + 1)$; then `Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn`.
Result: stochastic-lanczos-quadrature-error -/
theorem _root_.Matrix.IsHermitian.norm_trace_cfc_sub_slq_le_of_continuousOn
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a a')) (Ω : Matrix n m 𝕜) (q : ℕ) :
    ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        2 * minimaxError f (Set.Icc a a') (2 * q + 1) * frobNorm Ω ^ 2 / Fintype.card m := by
  have hdeg : ∀ p : ℝ[X], p.degree ≤ ↑(2 * q + 1) → p.degree < ↑(2 * (q + 1)) := fun p hp =>
    hp.trans_lt (by exact_mod_cast (by omega : 2 * q + 1 < 2 * (q + 1)))
  set E := minimaxError f (Set.Icc a a') (2 * q + 1)
  rcases (Set.Icc a a').eq_empty_or_nonempty with he | hne
  · exact_mod_cast hA.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn hs (f := f) (p := 0)
      (hdeg 0 (by simp)) (ε := E) (by rw [he]; intro x hx; exact hx.elim) Ω
  -- `f` is bounded on the compact interval, so the set defining `E` is nonempty
  obtain ⟨C, hC⟩ := (isCompact_Icc.image_of_continuousOn hf).isBounded.subset_closedBall 0
  have hSne : C ∈ {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ ↑(2 * q + 1) ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε} := by
    refine ⟨0, by simp, fun x hx => ?_⟩
    have := hC (Set.mem_image_of_mem f hx)
    rw [Metric.mem_closedBall] at this
    simpa [dist_comm] using this
  -- the bound with `E + δ` for every `δ > 0`
  have key : ∀ δ > 0, ‖(cfc f A).trace - slq A f Ω (q + 1)‖ ≤
      ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
        2 * (E + δ) * frobNorm Ω ^ 2 / Fintype.card m := by
    intro δ hδ
    obtain ⟨ε, ⟨p, hp, hpε⟩, hlt⟩ := exists_lt_of_csInf_lt ⟨C, hSne⟩ (lt_add_of_pos_right E hδ)
    exact_mod_cast hA.norm_trace_cfc_sub_slq_le_of_isUniformApproxOn hs (hdeg p hp)
      (hpε.mono_error hlt.le) Ω
  have hc : Continuous fun δ : ℝ => ‖(cfc f A).trace - girardHutchinson (cfc f A) Ω‖ +
      2 * (E + δ) * frobNorm Ω ^ 2 / Fintype.card m := by fun_prop
  refine ge_of_tendsto (x := nhdsWithin 0 (Set.Ioi 0)) ?_ (eventually_nhdsWithin_of_forall key)
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **The tail of stochastic Lanczos quadrature and the minimax error.** Let the entries of the
real $n \times m$ test matrix $\mathbf{\Omega}$ be independent, each satisfying the sub-Gaussian
moment generating function bound with variance proxy $c$ (`HasSubgaussianMGF`) and having second
moment $1$. Let $\mathbf{A}$ be real symmetric with spectrum in $[a, a']$ and $f$ continuous on
$[a, a']$. Then for every $q$ and $\tau \ge 0$, with $q + 1$ Lanczos steps per
probe, <!-- value hansonWrightConstant -->
$$\mathbb{P}\Bigl[\tau + \frac{2E_{2q + 1}(f; [a, a'])\|\mathbf{\Omega}\|_{\mathsf{F}}^2}{m}
\le \bigl\lvert\operatorname{tr} f(\mathbf{A}) -
\mathsf{slq}(\mathbf{A}, f, \mathbf{\Omega}, q + 1)\bigr\rvert\Bigr]
\le 2\exp\Bigl(-\frac{1}{196}\min\Bigl(\frac{m\tau^2}{c^2\|f(\mathbf{A})\|_{\mathsf{F}}^2},
\frac{m\tau}{c\|f(\mathbf{A})\|_2}\Bigr)\Bigr)\,;$$
the constant is `hansonWrightConstant`; $E_{2q + 1}$ is the error of the best uniform
approximation of $f$ on $[a, a']$ by polynomials of degree at most $2q + 1$ (`minimaxError`), and
the quadrature term is random, inside the event. Gaussian and sign test matrices are the case
$c = 1$. [UbaruChenSaad2017, Theorem 4.1] (locator to check), there for positive definite
$\mathbf{A}$ with Rademacher probes and relative error; [CortinovisKressner2022, §4] (locator to
check).
Proof: S, about 8 lines. `exists_degree_le_isUniformApproxOn_minimaxError` in degree $2q + 1$,
$2q + 1 < 2(q + 1)$; then `measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn`.
Result: stochastic-lanczos-quadrature-tail -/
theorem measureReal_abs_trace_cfc_sub_slq_ge_le_of_continuousOn
    {X : Ω → Matrix n m ℝ} {c : ℝ≥0}
    (hind : iIndepFun (fun p : n × m => fun ω => X ω p.1 p.2) μ)
    (hsub : ∀ i j, HasSubgaussianMGF (fun ω => X ω i j) c μ)
    (hvar : ∀ i j, ∫ ω, X ω i j ^ 2 ∂μ = 1) {A : Matrix n n ℝ} (hA : A.IsHermitian)
    {a a' : ℝ} (hs : spectrum ℝ A ⊆ Set.Icc a a') {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) (q : ℕ) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | τ + 2 * minimaxError f (Set.Icc a a') (2 * q + 1) * frobNorm (X ω) ^ 2 /
        Fintype.card m ≤ |(cfc f A).trace - slq A f (X ω) (q + 1)|} ≤
      2 * Real.exp (-(hansonWrightConstant *
        min (Fintype.card m * τ ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
          (Fintype.card m * τ / ((c : ℝ) * specNorm (cfc f A))))) := by
  sorry

end NLAlib
