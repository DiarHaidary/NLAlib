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

/-- A near-best approximant: for $f$ continuous on $[a, a']$ and $\delta > 0$, some polynomial
of degree at most $N$ is within $E_N(f) + \delta$ of $f$ on $[a, a']$. -/
private lemma exists_degree_le_isUniformApproxOn_minimaxError_add {f : ℝ → ℝ} {a a' : ℝ}
    (hf : ContinuousOn f (Set.Icc a a')) (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ p : ℝ[X], p.degree ≤ N ∧ Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a')
      (minimaxError f (Set.Icc a a') N + δ) := by
  rcases (Set.Icc a a').eq_empty_or_nonempty with he | hne
  · exact ⟨0, by simp, fun x hx => by simp [he] at hx⟩
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  have hT : (({ε : ℝ | ∃ p : ℝ[X], p.degree ≤ N ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε}).Nonempty) :=
    ⟨C, 0, by simp, fun x hx => by simpa [Real.dist_eq] using hC x hx⟩
  have hB : BddBelow {ε : ℝ | ∃ p : ℝ[X], p.degree ≤ N ∧
      Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a a') ε} :=
    ⟨0, fun ε ⟨_, _, hε⟩ => hε.nonneg hne⟩
  obtain ⟨ε, ⟨p, hp, hε⟩, hlt⟩ := exists_lt_of_csInf_lt hT
    (lt_add_of_pos_right (minimaxError f (Set.Icc a a') N) hδ)
  exact ⟨p, hp, hε.mono_error hlt.le⟩

/-- A limit argument for tails: if the tail bound holds at every error $E + \delta$, $\delta > 0$,
and every level $\tau' \ge 0$, with $g$ continuous, it holds at $E$ and $\tau > 0$. -/
private lemma measureReal_le_of_forall_pos_add [IsFiniteMeasure μ] {F D : Ω → ℝ} {E M τ : ℝ}
    (hτ : 0 < τ) {g : ℝ → ℝ} (hg : Continuous g) (hg0 : 0 ≤ g τ)
    (h : ∀ δ : ℝ, 0 < δ → ∀ τ' : ℝ, 0 ≤ τ' →
      μ.real {ω | τ' + 2 * (E + δ) * F ω / M ≤ D ω} ≤ g τ') :
    μ.real {ω | τ + 2 * E * F ω / M ≤ D ω} ≤ g τ := by
  set S := {ω | τ + 2 * E * F ω / M ≤ D ω}
  -- on `{2F/M ≤ N}` the error `E` costs at most `τ - τ'` more than `E + δ`, `δ = (τ - τ')/(N+1)`
  have hN (N : ℕ) : μ.real (S ∩ {ω | 2 * F ω / M ≤ N}) ≤ g τ := by
    refine ge_of_tendsto ((hg.tendsto τ).mono_left (nhdsWithin_le_nhds (s := Set.Iio τ))) ?_
    filter_upwards [Ioo_mem_nhdsLT hτ] with τ' hτ'
    have hδ : 0 < (τ - τ') / (N + 1) := div_pos (by linarith [hτ'.2]) (by positivity)
    refine (measureReal_mono fun ω hω => ?_).trans (h _ hδ τ' hτ'.1.le)
    simp only [S, Set.mem_inter_iff, Set.mem_ofPred_eq] at hω ⊢
    have h1 : (τ - τ') / (N + 1) * (N + 1) = τ - τ' := div_mul_cancel₀ _ (by positivity)
    have h2 := mul_le_mul_of_nonneg_left hω.2 hδ.le
    have h3 : 2 * (E + (τ - τ') / (N + 1)) * F ω / M =
        2 * E * F ω / M + (τ - τ') / (N + 1) * (2 * F ω / M) := by ring
    nlinarith [hω.1]
  have hmono : Monotone fun N : ℕ => S ∩ {ω | 2 * F ω / M ≤ N} := fun N N' hNN' =>
    Set.inter_subset_inter_right _ fun ω (hω : 2 * F ω / M ≤ N) => show 2 * F ω / M ≤ N' from
      hω.trans (Nat.cast_le.mpr hNN')
  have hU : S = ⋃ N : ℕ, S ∩ {ω | 2 * F ω / M ≤ N} := by
    ext ω
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    exact ⟨fun hω => (exists_nat_ge _).imp fun _ hN => ⟨hω, hN⟩, fun ⟨_, hω, _⟩ => hω⟩
  refine ENNReal.toReal_le_of_le_ofReal hg0 ?_
  rw [hU, hmono.measure_iUnion]
  exact iSup_le fun N => (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hg0).mpr (hN N)

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
  have := hind.isProbabilityMeasure
  rcases hτ.eq_or_lt with rfl | hτ
  · refine measureReal_le_one.trans ?_
    simp
  refine measureReal_le_of_forall_pos_add (g := fun t => 2 * Real.exp (-(hansonWrightConstant *
      min (Fintype.card m * t ^ 2 / ((c : ℝ) ^ 2 * frobNorm (cfc f A) ^ 2))
        (Fintype.card m * t / ((c : ℝ) * specNorm (cfc f A))))))
    hτ (by fun_prop) (by positivity) fun δ hδ τ' hτ' => ?_
  obtain ⟨p, hp, hε⟩ := exists_degree_le_isUniformApproxOn_minimaxError_add hf (2 * q + 1) hδ
  have hp' : p.degree < (2 * (q + 1) : ℕ) :=
    hp.trans_lt (Nat.cast_lt.mpr (by omega))
  exact measureReal_abs_trace_cfc_sub_slq_ge_le_of_isUniformApproxOn hind hsub hvar hA hs
    (by exact_mod_cast hp') hε hτ'

end NLAlib
