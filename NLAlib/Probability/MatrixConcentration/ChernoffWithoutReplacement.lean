/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef
public import NLAlib.Matrix.Functions.TraceFunctions
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Probability.ConvexOrder
public import NLAlib.Probability.Distributions.Sampling
public import NLAlib.Probability.MatrixConcentration.Chernoff
public import NLAlib.Probability.MatrixConcentration.MGFBound

/-!
# The matrix Chernoff inequalities for sampling without replacement

For a population of positive semidefinite matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq
L\mathbf{I}$, $i \in n$, and a uniformly random injection $\iota : k \to n$ (sampling
$\lvert k \rvert$ members without replacement), the sum $\mathbf{Y} = \sum_j \mathbf{X}_{\iota(j)}$
has mean
$$\mathbf{V} = \frac{\lvert k \rvert}{\lvert n \rvert} \sum_i \mathbf{X}_i \,,$$
and the matrix Chernoff trace bound of the i.i.d. sum with the same mean,
$\mathbb{E} \operatorname{tr} e^{\theta \mathbf{Y}}
\le \operatorname{tr} e^{((e^{\theta L} - 1)/L)\, \mathbf{V}}$ for every real $\theta$. It follows
from Hoeffding's comparison (`NLAlib.integral_uniformOn_injective_le_integral_pi`) with
$f = \operatorname{re} \operatorname{tr} e^{\theta \cdot}$ on the positive semidefinite cone and the
i.i.d. bound (`NLAlib.HasMatrixMGFBound.integral_re_trace_exp_sum_le`). The trace-form tails of
`NLAlib.Probability.MatrixConcentration.Chernoff` then give the Chernoff tails of the extreme
eigenvalues of $\mathbf{Y}$ relative to those of $\mathbf{V}$, with the constants of sampling with
replacement.

Degenerate cases. For $\lvert n \rvert < \lvert k \rvert$ there is no injection, the law of $\iota$
is the zero measure, `HasLaw` forces $\mu = 0$, and every statement holds with left side $0$; so
no $\lvert k \rvert \le \lvert n \rvert$ is assumed. For empty `k` the sum and $\mathbf{V}$ are
$\mathbf{0}$ and the bounds are at least $\lvert m \rvert \ge 1$.

Design: Sketching stage S5 (`docs/design/Sketching-S5.md` §3.3, §8). The trace bound rests on
Hoeffding's comparison (`NLAlib/Probability/ConvexOrder.lean`).

## Main results

* `NLAlib.integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective`: the trace bound.
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective`,
  `NLAlib.measureReal_eigenvalue_sum_le_le_chernoff_of_hasLaw_uniformOn_injective`: the tails,
  source form.
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp_of_hasLaw_uniformOn_injective`,
  `NLAlib.measureReal_eigenvalue_sum_le_le_card_mul_exp_of_hasLaw_uniformOn_injective`: the
  simplified forms.
* `NLAlib.integral_eigenvalue_zero_sum_le_chernoff_of_hasLaw_uniformOn_injective`,
  `NLAlib.le_integral_eigenvalue_sum_chernoff_of_hasLaw_uniformOn_injective`: the means.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 5.
* [J. A. Tropp, *Improved analysis of the subsampled randomized Hadamard transform*][Tropp2011a].
* [D. Gross and V. Nesme, *Note on sampling without replacing from a finite collection of
  matrices*][GrossNesme2010].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open NormedSpace (exp)

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k m n : Type*} [Fintype k] [Fintype m] [Fintype n] [DecidableEq m] [MeasurableSpace n]
  [MeasurableSingletonClass n] {ι : Ω → k → n} {X : n → Matrix m m 𝕜} {L δ : ℝ}

omit [Fintype n] in
/-- The trace exponential of a sum sampled by a random injection is integrable: it takes finitely
many values and the law of the injection is finite. -/
theorem integrable_re_trace_exp_sum_of_hasLaw_uniformOn_injective [Finite n]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (θ : ℝ) :
    Integrable (fun ω => RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace) μ :=
  (hι.integrable_comp_iff (f := fun J : k → n => RCLike.re (exp (θ • ∑ j, X (J j))).trace)
    .of_discrete).2 .of_finite

omit [MeasurableSingletonClass n] in
/-- With fewer members than samples, the probability space of a uniform injection is zero. -/
private theorem eq_zero_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ)
    (hk : Fintype.card n < Fintype.card k) : μ = 0 := by
  have h := hι.map_eq
  rw [uniformOn_injective_of_card_lt hk] at h
  exact (Measure.map_eq_zero_iff hι.aemeasurable).1 h

/-- **The matrix Chernoff trace bound without replacement.** For a population
$\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ with $L > 0$ and a uniformly random
injection $\iota : k \to n$, for every real $\theta$
$$\mathbb{E} \operatorname{tr} e^{\theta \sum_j \mathbf{X}_{\iota(j)}} \le
\operatorname{tr} \exp\Bigl(\frac{e^{\theta L} - 1}{L} \cdot \frac{\lvert k \rvert}{\lvert n \rvert}
\sum_i \mathbf{X}_i\Bigr) \,,$$
the bound of the i.i.d. sum with the same mean; the hypothesis `htr` of the trace-form tails of
`NLAlib.Probability.MatrixConcentration.Chernoff`. [GrossNesme2010, Section D];
[Tropp2011a, proof of Theorem 2.1] (the matrix Chernoff bound without replacement, through Gross
and Nesme's comparison);
[Tropp2015, Theorem 5.1.1] (the i.i.d. form). Here real parts of traces over any `RCLike` field,
any population index type and any $\theta$. -/
theorem integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) (θ : ℝ) :
    ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ ≤
      RCLike.re (exp (((Real.exp (θ * L) - 1) / L) •
        (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i))).trace := by
  set V := ((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i with hVdef
  have hV : V.PosSemidef := (Matrix.posSemidef_sum _ fun i _ => hpsd i).smul (by positivity)
  have hR : 0 ≤ RCLike.re (exp (((Real.exp (θ * L) - 1) / L) • V)).trace := by
    rcases isEmpty_or_nonempty m with hm | hm
    · simp [Matrix.trace]
    · exact Matrix.IsHermitian.re_trace_exp_pos
        ((IsSelfAdjoint.all ((Real.exp (θ * L) - 1) / L)).smul hV.isHermitian) |>.le
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [eq_zero_of_hasLaw_uniformOn_injective hι hk, integral_zero_measure]
    exact hR
  have : IsProbabilityMeasure μ :=
    hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  rcases isEmpty_or_nonempty k with hk0 | ⟨⟨j₀⟩⟩
  · simp [hVdef, Fintype.card_eq_zero]
  have : Nonempty n := ⟨(Function.Embedding.nonempty_of_card_le hk).some j₀⟩
  -- transport to the law of the injection
  have h1 : ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ =
      ∫ J, RCLike.re (exp (θ • ∑ j, X (J j))).trace
        ∂uniformOn {f : k → n | Function.Injective f} :=
    hι.integral_comp (f := fun J : k → n => RCLike.re (exp (θ • ∑ j, X (J j))).trace)
      .of_discrete
  -- Hoeffding's comparison with `re tr exp (θ •)` on the positive semidefinite cone
  have hf : ConvexOn ℝ {A : Matrix m m 𝕜 | A.PosSemidef}
      fun A => RCLike.re (exp (θ • A)).trace := by
    have h0 := (convexOn_re_trace_exp (𝕜 := 𝕜) (n := m)).comp_linearMap
      (θ • LinearMap.id : Matrix m m 𝕜 →ₗ[ℝ] Matrix m m 𝕜)
    have hfun : (fun A : Matrix m m 𝕜 => RCLike.re (exp A).trace) ∘
        ⇑(θ • LinearMap.id : Matrix m m 𝕜 →ₗ[ℝ] Matrix m m 𝕜) =
        fun A => RCLike.re (exp (θ • A)).trace := by
      funext A
      simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hfun] at h0
    refine h0.subset (fun A hA => ?_) convex_setOf_posSemidef
    simp only [Set.mem_preimage, LinearMap.smul_apply, LinearMap.id_apply, Set.mem_ofPred_eq]
    exact (IsSelfAdjoint.all θ).smul hA.isHermitian
  have hexp : Continuous (exp : Matrix m m 𝕜 → Matrix m m 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  have hfc : ContinuousOn (fun A : Matrix m m 𝕜 => RCLike.re (exp (θ • A)).trace)
      {A | A.PosSemidef} :=
    (RCLike.continuous_re.comp (hexp.comp (continuous_const_smul θ)).matrix_trace).continuousOn
  have h2 := integral_uniformOn_injective_le_integral_pi hf hfc Matrix.isClosed_setOf_posSemidef
    hk X fun J => Matrix.posSemidef_sum _ fun j _ => hpsd (J j)
  -- the i.i.d. bound
  have hind : iIndepFun (fun j (J : k → n) => X (J j))
      (Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) :=
    iIndepFun_pi (X := fun (_ : k) (i : n) => X i) fun _ => (measurable_of_countable _).aemeasurable
  have hmgf (j : k) := hasMatrixMGFBound_of_posSemidef_of_le
    (μ := Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) (X := fun J : k → n => X (J j))
    (measurable_of_countable _).aemeasurable hL (ae_of_all _ fun J => hpsd (J j))
    (ae_of_all _ fun J => hle (J j))
  have h3 := HasMatrixMGFBound.integral_re_trace_exp_sum_le hind hmgf (Set.mem_univ θ)
  have hmean : ∑ j : k, ∫ J, X (J j) ∂(Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) =
      V := by
    have hj (j : k) : ∫ J, X (J j) ∂(Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) =
        (Fintype.card n : ℝ)⁻¹ • ∑ i, X i := by
      rw [integral_comp_eval (μ := fun _ : k => uniformOn (Set.univ : Set n)) (i := j) (f := X)
        .of_discrete, ← samplingMeasure_const_inv_card, integral_samplingMeasure,
        Finset.smul_sum]
      simp only [NNReal.coe_inv, NNReal.coe_natCast]
    rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← div_eq_mul_inv]
  rw [hmean] at h3
  exact h1.trans_le (h2.trans h3)

/-- The hypotheses of the trace-form Chernoff tails for $\mathbf{Y} = \sum_j \mathbf{X}_{\iota(j)}$
and $\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$. -/
private theorem chernoff_hyps_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) :
    (∀ᵐ ω ∂μ, (∑ j, X (ι ω j)).IsHermitian) ∧
      (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i).PosSemidef ∧
      (∀ θ : ℝ, Integrable (fun ω => RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace) μ) ∧
      ∀ θ : ℝ, ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ ≤
        RCLike.re (exp (((Real.exp (θ * L) - 1) / L) •
          (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i))).trace :=
  ⟨ae_of_all _ fun ω => (Matrix.posSemidef_sum _ fun j _ => hpsd (ι ω j)).isHermitian,
    (Matrix.posSemidef_sum _ fun i _ => hpsd i).smul (by positivity),
    integrable_re_trace_exp_sum_of_hasLaw_uniformOn_injective hι,
    integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective hι hL hpsd hle⟩

/-- **Matrix Chernoff without replacement, upper tail**, source form. For a population of
$m \times m$ matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ over $\Bbbk$,
$i \in n$, $m$ nonempty, with $L > 0$, a uniformly random injection $\iota : k \to n$ (its law
under $\mu$ is uniform on the injections),
$\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$ and $\delta \ge 0$,
$$\mathbb{P}\Bigl[\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \ge
(1 + \delta) \lambda_0(\mathbf{V})\Bigr] \le \lvert m \rvert
\Bigl(\frac{e^\delta}{(1 + \delta)^{1+\delta}}\Bigr)^{\lambda_0(\mathbf{V}) / L} \,.$$
[Tropp2011a, Theorem 2.1] (sampling without replacement from a finite set of matrices; there $B$
is $L$ and $\mu_{\max}$ is $\lambda_0(\mathbf{V})$, here a population that may repeat members);
[Tropp2015, Theorem 5.1.1] (the i.i.d. form, the same bound). No
$\lvert k \rvert \le \lvert n \rvert$: otherwise $\mu = 0$.
Result: matrix-chernoff-without-replacement -/
theorem measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective [Nonempty m]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) (hδ : 0 ≤ δ) :
    μ.real {ω | (1 + δ) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 ≤
        eigenvalue (∑ j, X (ι ω j)) 0} ≤
      Fintype.card m * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^
        (eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 / L) := by
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [eq_zero_of_hasLaw_uniformOn_injective hι hk, measureReal_zero_apply]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (div_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)) _)
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_hyps_of_hasLaw_uniformOn_injective hι hL hpsd hle
  exact measureReal_eigenvalue_zero_ge_le_chernoff_of_integral_le hY hV hL (fun θ _ => hint θ)
    (fun θ _ => htr θ) hδ

/-- **Matrix Chernoff without replacement, lower tail**, source form. For a population of
$m \times m$ matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ over $\Bbbk$,
$i \in n$, with $L > 0$, a uniformly random injection $\iota : k \to n$ (its law under $\mu$ is
uniform on the injections), $\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$,
$0 \le \delta < 1$ and the smallest eigenvalue, index $j + 1 = \lvert m \rvert$,
$$\mathbb{P}\Bigl[\lambda_j\Bigl(\sum_{j'} \mathbf{X}_{\iota(j')}\Bigr) \le
(1 - \delta) \lambda_j(\mathbf{V})\Bigr] \le \lvert m \rvert
\Bigl(\frac{e^{-\delta}}{(1 - \delta)^{1-\delta}}\Bigr)^{\lambda_j(\mathbf{V}) / L} \,.$$
[Tropp2011a, Theorem 2.1] (sampling without replacement); [Tropp2015, Theorem 5.1.1] (the i.i.d.
form, the same bound).
Result: matrix-chernoff-without-replacement -/
theorem measureReal_eigenvalue_sum_le_le_chernoff_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {j : ℕ}
    (hj : j + 1 = Fintype.card m) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ j', X (ι ω j')) j ≤
        (1 - δ) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j} ≤
      Fintype.card m * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^
        (eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j / L) := by
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [eq_zero_of_hasLaw_uniformOn_injective hι hk, measureReal_zero_apply]
    exact mul_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg
      (div_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith) _)) _)
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_hyps_of_hasLaw_uniformOn_injective hι hL hpsd hle
  exact measureReal_eigenvalue_le_le_chernoff_of_integral_le hY hV hL hj (fun θ _ => hint θ)
    (fun θ _ => htr θ) hδ0 hδ1

/-- **Matrix Chernoff without replacement, upper tail**, simplified: for a population of
$m \times m$ matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ over $\Bbbk$,
$i \in n$, $m$ nonempty, with $L > 0$, a uniformly random injection $\iota : k \to n$ (its law
under $\mu$ is uniform on the injections),
$\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$ and $0 \le \delta \le 1$,
$$\mathbb{P}\Bigl[\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \ge
(1 + \delta) \lambda_0(\mathbf{V})\Bigr] \le
\lvert m \rvert\, e^{-\delta^2 \lambda_0(\mathbf{V}) / (3L)} \,;$$
weaker than the source form
`NLAlib.measureReal_eigenvalue_zero_sum_ge_le_chernoff_of_hasLaw_uniformOn_injective` in every
regime and proved from the same trace bound. [Tropp2015, Theorem 5.1.1] (the i.i.d. form). -/
theorem measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp_of_hasLaw_uniformOn_injective
    [Nonempty m] (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) (hδ0 : 0 ≤ δ)
    (hδ1 : δ ≤ 1) :
    μ.real {ω | (1 + δ) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 ≤
        eigenvalue (∑ j, X (ι ω j)) 0} ≤
      Fintype.card m * Real.exp (-δ ^ 2 *
        eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 / (3 * L)) := by
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [eq_zero_of_hasLaw_uniformOn_injective hι hk, measureReal_zero_apply]
    positivity
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_hyps_of_hasLaw_uniformOn_injective hι hL hpsd hle
  exact measureReal_eigenvalue_zero_ge_le_card_mul_exp_of_integral_le hY hV hL
    (fun θ _ => hint θ) (fun θ _ => htr θ) hδ0 hδ1

/-- **Matrix Chernoff without replacement, lower tail**, simplified: for a population of
$m \times m$ matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ over $\Bbbk$,
$i \in n$, with $L > 0$, a uniformly random injection $\iota : k \to n$ (its law under $\mu$ is
uniform on the injections), $\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$,
$0 \le \delta < 1$ and the smallest eigenvalue, index $j + 1 = \lvert m \rvert$,
$$\mathbb{P}\Bigl[\lambda_j\Bigl(\sum_{j'} \mathbf{X}_{\iota(j')}\Bigr) \le
(1 - \delta) \lambda_j(\mathbf{V})\Bigr] \le
\lvert m \rvert\, e^{-\delta^2 \lambda_j(\mathbf{V}) / (2L)} \,;$$
weaker than the source form
`NLAlib.measureReal_eigenvalue_sum_le_le_chernoff_of_hasLaw_uniformOn_injective` in every regime
and proved from the same trace bound. [Tropp2015, Theorem 5.1.1] (the i.i.d. form). -/
theorem measureReal_eigenvalue_sum_le_le_card_mul_exp_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {j : ℕ}
    (hj : j + 1 = Fintype.card m) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) :
    μ.real {ω | eigenvalue (∑ j', X (ι ω j')) j ≤
        (1 - δ) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j} ≤
      Fintype.card m * Real.exp (-δ ^ 2 *
        eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j / (2 * L)) := by
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [eq_zero_of_hasLaw_uniformOn_injective hι hk, measureReal_zero_apply]
    positivity
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_hyps_of_hasLaw_uniformOn_injective hι hL hpsd hle
  exact measureReal_eigenvalue_le_le_card_mul_exp_of_integral_le hY hV hL hj
    (fun θ _ => hint θ) (fun θ _ => htr θ) hδ0 hδ1

omit [Fintype n] in
/-- The sum sampled by a random injection is integrable: it takes finitely many values. -/
private theorem integrable_sum_of_hasLaw_uniformOn_injective [Finite n]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) :
    Integrable (fun ω => ∑ j, X (ι ω j)) μ :=
  (hι.integrable_comp_iff (f := fun J : k → n => ∑ j, X (J j)) .of_discrete).2 .of_finite

/-- **Matrix Chernoff without replacement for the mean of the largest eigenvalue**: for a
population of $m \times m$ matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ over
$\Bbbk$, $i \in n$, $m$ nonempty, with $L > 0$, a uniformly random injection $\iota : k \to n$
and $\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$,
$$\mathbb{E}\,\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \le
(e - 1)\lambda_0(\mathbf{V}) + L\log\lvert m\rvert\,,$$
the bound of the i.i.d. sum with the same mean, from the trace bound
`NLAlib.integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective` at $\theta = 1/L$.
[Tropp2015, Theorem 5.1.1] (the i.i.d. means). -/
theorem integral_eigenvalue_zero_sum_le_chernoff_of_hasLaw_uniformOn_injective [Nonempty m]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) :
    ∫ ω, eigenvalue (∑ j, X (ι ω j)) 0 ∂μ ≤
      (Real.exp 1 - 1) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) 0 +
        L * Real.log (Fintype.card m) := by
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_hyps_of_hasLaw_uniformOn_injective hι hL hpsd hle
  set V := ((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i with hVdef
  have hd : (1 : ℝ) ≤ Fintype.card m := by exact_mod_cast Fintype.card_pos
  have he : 0 ≤ Real.exp 1 - 1 := by linarith [Real.add_one_le_exp 1]
  have hR : 0 ≤ (Real.exp 1 - 1) * eigenvalue V 0 + L * Real.log (Fintype.card m) :=
    add_nonneg (mul_nonneg he (hV.eigenvalue_nonneg 0))
      (mul_nonneg hL.le (Real.log_nonneg hd))
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [eq_zero_of_hasLaw_uniformOn_injective hι hk, integral_zero_measure]
    exact hR
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  have hmean := integral_eigenvalue_zero_le hY (integrable_sum_of_hasLaw_uniformOn_injective hι)
    (inv_pos.mpr hL) (hint L⁻¹)
  have hθL : L⁻¹ * L = 1 := inv_mul_cancel₀ hL.ne'
  have htr' := htr L⁻¹
  rw [hθL] at htr'
  set c := (Real.exp 1 - 1) / L with hcdef
  have hc : 0 ≤ c := div_nonneg he hL.le
  have hcV : (c • V).IsHermitian := (IsSelfAdjoint.all c).smul hV.isHermitian
  have htrd := hcV.re_trace_exp_le_card_mul_exp
  rw [eigenvalue_real_smul _ hc] at htrd
  have hpos : 0 < ∫ ω, RCLike.re (exp (L⁻¹ • ∑ j, X (ι ω j))).trace ∂μ :=
    integral_pos_of_ae_pos (hint _) (hY.mono fun ω hω =>
      Matrix.IsHermitian.re_trace_exp_pos ((IsSelfAdjoint.all L⁻¹).smul hω))
  have hlog := Real.log_le_log hpos (htr'.trans htrd)
  rw [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_exp] at hlog
  rw [inv_inv] at hmean
  refine hmean.trans ?_
  calc L * Real.log (∫ ω, RCLike.re (exp (L⁻¹ • ∑ j, X (ι ω j))).trace ∂μ)
      ≤ L * (Real.log (Fintype.card m) + c * eigenvalue V 0) :=
        mul_le_mul_of_nonneg_left hlog hL.le
    _ = (Real.exp 1 - 1) * eigenvalue V 0 + L * Real.log (Fintype.card m) := by
        rw [hcdef]
        field_simp
        ring

/-- **Matrix Chernoff without replacement for the mean of the smallest eigenvalue**: for a
population of $m \times m$ matrices $\mathbf{0} \preceq \mathbf{X}_i \preceq L\mathbf{I}$ over
$\Bbbk$, $i \in n$, with $L > 0$, $\lvert k\rvert \le \lvert n\rvert$, a uniformly random
injection $\iota : k \to n$, $\mathbf{V} = (\lvert k \rvert / \lvert n \rvert) \sum_i \mathbf{X}_i$
and $j + 1 = \lvert m\rvert$,
$$\mathbb{E}\,\lambda_j\Bigl(\sum_{j'} \mathbf{X}_{\iota(j')}\Bigr) \ge
(1 - e^{-1})\lambda_j(\mathbf{V}) - L\log\lvert m\rvert\,,$$
the bound of the i.i.d. sum with the same mean, from the trace bound at $\theta = -1/L$. The
hypothesis $\lvert k\rvert \le \lvert n\rvert$ is needed: otherwise $\mu = 0$ and the left side of
the inequality need not be at most $0$. [Tropp2015, Theorem 5.1.1] (the i.i.d. means). -/
theorem le_integral_eigenvalue_sum_chernoff_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ)
    (hk : Fintype.card k ≤ Fintype.card n) (hL : 0 < L)
    (hpsd : ∀ i, (X i).PosSemidef) (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {j : ℕ}
    (hj : j + 1 = Fintype.card m) :
    (1 - Real.exp (-1)) * eigenvalue (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i) j -
        L * Real.log (Fintype.card m) ≤ ∫ ω, eigenvalue (∑ j', X (ι ω j')) j ∂μ := by
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  obtain ⟨hY, hV, hint, htr⟩ := chernoff_hyps_of_hasLaw_uniformOn_injective hι hL hpsd hle
  set V := ((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i with hVdef
  have hθ : -L⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hL)
  have hlow := le_integral_eigenvalue hY (integrable_sum_of_hasLaw_uniformOn_injective hι) hj hθ
    (hint (-L⁻¹))
  have hθL : -L⁻¹ * L = -1 := by rw [neg_mul, inv_mul_cancel₀ hL.ne']
  have htr' := htr (-L⁻¹)
  rw [hθL] at htr'
  rw [inv_neg, inv_inv] at hlow
  set c := (Real.exp (-1) - 1) / L with hcdef
  have hc : c ≤ 0 := div_nonpos_of_nonpos_of_nonneg
    (by linarith [Real.exp_le_one_iff.mpr (show (-1 : ℝ) ≤ 0 by norm_num)]) hL.le
  have hcV : (c • V).IsHermitian := (IsSelfAdjoint.all c).smul hV.isHermitian
  have htrd := hcV.re_trace_exp_le_card_mul_exp
  have heig : eigenvalue (c • V) 0 = c * eigenvalue V j := by
    rw [show c • V = -((-c) • V) by rw [neg_smul, neg_neg],
      eigenvalue_neg _ (show 0 + j + 1 = Fintype.card m by omega),
      eigenvalue_real_smul _ (neg_nonneg.mpr hc), neg_mul, neg_neg]
  rw [heig] at htrd
  have hd : (0 : ℝ) < Fintype.card m := Nat.cast_pos.mpr (by omega)
  have hpos : 0 < ∫ ω, RCLike.re (exp (-L⁻¹ • ∑ j', X (ι ω j'))).trace ∂μ := by
    have : Nonempty m := Fintype.card_pos_iff.mp (by omega)
    exact integral_pos_of_ae_pos (hint _) (hY.mono fun ω hω =>
      Matrix.IsHermitian.re_trace_exp_pos ((IsSelfAdjoint.all (-L⁻¹)).smul hω))
  have hlog := Real.log_le_log hpos (htr'.trans htrd)
  rw [Real.log_mul hd.ne' (Real.exp_pos _).ne', Real.log_exp] at hlog
  refine le_trans ?_ hlow
  calc (1 - Real.exp (-1)) * eigenvalue V j - L * Real.log (Fintype.card m)
      = -L * (Real.log (Fintype.card m) + c * eigenvalue V j) := by
        rw [hcdef]
        field_simp
        ring
    _ ≤ -L * Real.log (∫ ω, RCLike.re (exp (-L⁻¹ • ∑ j', X (ι ω j'))).trace ∂μ) :=
        mul_le_mul_of_nonpos_left hlog (neg_nonpos.mpr hL.le)

end NLAlib
