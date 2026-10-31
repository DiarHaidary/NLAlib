/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.MatrixConcentration.Bernstein
public import NLAlib.Probability.MatrixConcentration.ChernoffWithoutReplacement

/-!
# Matrix Bernstein for sampling without replacement

For a centred population of Hermitian matrices, $\sum_i \mathbf{X}_i = \mathbf{0}$ with
$\mathbf{X}_i \preceq L\mathbf{I}$, $i \in n$, and a uniformly random injection $\iota : k \to n$
(sampling $\lvert k \rvert$ members without replacement), the sum
$\mathbf{Y} = \sum_j \mathbf{X}_{\iota(j)}$ satisfies the matrix Bernstein trace bound of the
i.i.d. sum with the same variance $(\lvert k\rvert/\lvert n\rvert)\sum_i \mathbf{X}_i^2$:
Hoeffding's comparison (`NLAlib.integral_uniformOn_injective_le_integral_pi`) with
$f = \operatorname{re}\operatorname{tr} e^{\theta\,\cdot}$, convex on the Hermitian matrices
(`NLAlib.convexOn_re_trace_exp`), and the i.i.d. bound
(`NLAlib.HasMatrixMGFBound.integral_re_trace_exp_sum_le` with
`NLAlib.hasMatrixMGFBound_of_integral_eq_zero_of_le`). The trace-form tails of
`NLAlib.Probability.MatrixConcentration.Bernstein` then give the tail and the mean of
$\lambda_0(\mathbf{Y})$; rectangular populations go through the Hermitian dilation, with
dimension $\lvert q\rvert + \lvert r\rvert$, and the $1 \times 1$ case is Bernstein's inequality
without replacement, Hoeffding's setting [Hoeffding1963].

The population is centred: a consumer with a population
of mean $\bar{\mathbf{X}}$ centres its atoms in one line. Lower tails follow by
$\mathbf{X} \mapsto -\mathbf{X}$; the rectangular form covers two-sided Hermitian use.

Degenerate cases. For $\lvert n \rvert < \lvert k \rvert$ there is no injection, the law of $\iota$
is the zero measure, `HasLaw` forces $\mu = 0$, and every statement holds; so no
$\lvert k \rvert \le \lvert n \rvert$ is assumed.

## Main results

* `NLAlib.integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective`: the trace bound.
* `NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`,
  `NLAlib.integral_eigenvalue_zero_sum_le_bernstein_of_hasLaw_uniformOn_injective`: Hermitian
  populations.
* `NLAlib.measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`,
  `NLAlib.integral_specNorm_sum_le_bernstein_of_hasLaw_uniformOn_injective`: rectangular
  populations.
* `NLAlib.measureReal_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`: the scalar case.

## References

* [J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*][Tropp2015], chapter 6.
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
  [MeasurableSingletonClass n] {ι : Ω → k → n} {L : ℝ}

section Hermitian

variable {X : n → Matrix m m 𝕜}

omit [Fintype k] [DecidableEq m] [MeasurableSingletonClass n] in
/-- The integral of a function of one coordinate of a uniform draw with replacement is the
population mean. -/
private theorem integral_comp_eval_pi_uniformOn [Nonempty n] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [Fintype k] [DiscreteMeasurableSpace n] (f : n → E)
    (j : k) :
    ∫ J, f (J j) ∂(Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) =
      (Fintype.card n : ℝ)⁻¹ • ∑ i, f i := by
  rw [integral_comp_eval (μ := fun _ : k => uniformOn (Set.univ : Set n)) (i := j) (f := f)
    .of_discrete, ← samplingMeasure_const_inv_card, integral_samplingMeasure, Finset.smul_sum]
  simp only [NNReal.coe_inv, NNReal.coe_natCast]

/-- **The matrix Bernstein trace bound without replacement**: for Hermitian $\mathbf{X}_i$ with
$\sum_i \mathbf{X}_i = \mathbf{0}$ and $\mathbf{X}_i \preceq L\mathbf{I}$, $L > 0$, a uniformly
random injection $\iota : k \to n$ and $0 < \theta < 3/L$,
$$\mathbb{E}\operatorname{tr}\exp\Bigl(\theta\sum_j\mathbf{X}_{\iota(j)}\Bigr) \le
\operatorname{tr}\exp\Bigl(\frac{\theta^2/2}{1 - L\theta/3}\cdot
\frac{\lvert k\rvert}{\lvert n\rvert}\sum_i\mathbf{X}_i^2\Bigr)\,,$$
the bound of the i.i.d. sum with the same variance; the hypothesis of the trace-form tails
`NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le` and
`NLAlib.integral_eigenvalue_zero_le_bernstein_of_integral_le`. Hoeffding's comparison on the
Hermitian matrices and [Tropp2015, Lemma 6.6.2]; [GrossNesme2010, Section D]; [Tropp2011a, proof
of Theorem 2.1] (the same comparison for the Chernoff bound,
`NLAlib.integral_re_trace_exp_sum_le_of_hasLaw_uniformOn_injective`). -/
theorem integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hX : ∀ i, (X i).IsHermitian) (hsum : ∑ i, X i = 0)
    (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (3 / L)) :
    ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ ≤
      RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) •
        (((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i ^ 2))).trace := by
  set V := ((Fintype.card k : ℝ) / Fintype.card n) • ∑ i, X i ^ 2 with hVdef
  have hV : V.IsHermitian :=
    (IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun i _ => (hX i).pow 2)
  have hR : 0 ≤ RCLike.re (exp ((θ ^ 2 / 2 / (1 - L * θ / 3)) • V)).trace := by
    rcases isEmpty_or_nonempty m with hm | hm
    · simp [Matrix.trace]
    · exact Matrix.IsHermitian.re_trace_exp_pos ((IsSelfAdjoint.all _).smul hV) |>.le
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [(Measure.map_eq_zero_iff hι.aemeasurable).1
      (by rw [hι.map_eq, uniformOn_injective_of_card_lt hk]), integral_zero_measure]
    exact hR
  have : IsProbabilityMeasure μ :=
    hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  rcases isEmpty_or_nonempty k with hk0 | ⟨⟨j₀⟩⟩
  · simp [hVdef, Fintype.card_eq_zero]
  have : Nonempty n := ⟨(Function.Embedding.nonempty_of_card_le hk).some j₀⟩
  have h1 : ∫ ω, RCLike.re (exp (θ • ∑ j, X (ι ω j))).trace ∂μ =
      ∫ J, RCLike.re (exp (θ • ∑ j, X (J j))).trace
        ∂uniformOn {f : k → n | Function.Injective f} :=
    hι.integral_comp (f := fun J : k → n => RCLike.re (exp (θ • ∑ j, X (J j))).trace)
      .of_discrete
  -- Hoeffding's comparison with `re tr exp (θ •)` on the Hermitian matrices
  have hf : ConvexOn ℝ {A : Matrix m m 𝕜 | A.IsHermitian}
      fun A => RCLike.re (exp (θ • A)).trace := by
    have h0 := (convexOn_re_trace_exp (𝕜 := 𝕜) (n := m)).comp_linearMap
      (θ • LinearMap.id : Matrix m m 𝕜 →ₗ[ℝ] Matrix m m 𝕜)
    have hfun : (fun A : Matrix m m 𝕜 => RCLike.re (exp A).trace) ∘
        ⇑(θ • LinearMap.id : Matrix m m 𝕜 →ₗ[ℝ] Matrix m m 𝕜) =
        fun A => RCLike.re (exp (θ • A)).trace := by
      funext A
      simp only [Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply]
    rw [hfun] at h0
    refine h0.subset (fun A hA => ?_) ?_
    · simp only [Set.mem_preimage, LinearMap.smul_apply, LinearMap.id_apply, Set.mem_ofPred_eq]
      exact (IsSelfAdjoint.all θ).smul hA
    · intro A hA B hB a b ha hb hab
      exact ((IsSelfAdjoint.all a).smul hA).add ((IsSelfAdjoint.all b).smul hB)
  have hexp : Continuous (exp : Matrix m m 𝕜 → Matrix m m 𝕜) := by
    open scoped Matrix.Norms.Operator in exact NormedSpace.exp_continuous
  have hfc : ContinuousOn (fun A : Matrix m m 𝕜 => RCLike.re (exp (θ • A)).trace)
      {A | A.IsHermitian} :=
    (RCLike.continuous_re.comp (hexp.comp (continuous_const_smul θ)).matrix_trace).continuousOn
  have hcl : IsClosed {A : Matrix m m 𝕜 | A.IsHermitian} :=
    isClosed_eq continuous_id.matrix_conjTranspose continuous_id
  have h2 := integral_uniformOn_injective_le_integral_pi hf hfc hcl hk X
    fun J => isSelfAdjoint_sum _ fun j _ => hX (J j)
  -- the i.i.d. bound
  have hind : iIndepFun (fun j (J : k → n) => X (J j))
      (Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) :=
    iIndepFun_pi (X := fun (_ : k) (i : n) => X i) fun _ => (measurable_of_countable _).aemeasurable
  have hmgf (j : k) := hasMatrixMGFBound_of_integral_eq_zero_of_le
    (μ := Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) (X := fun J : k → n => X (J j))
    hL .of_discrete (by rw [integral_comp_eval_pi_uniformOn X j, hsum, smul_zero])
    (ae_of_all _ fun J => hle (J j))
  have h3 := HasMatrixMGFBound.integral_re_trace_exp_sum_le hind hmgf hθ
  have hvar : ∑ j : k, ∫ J, X (J j) ^ 2 ∂(Measure.pi fun _ : k => uniformOn (Set.univ : Set n)) =
      V := by
    simp only [integral_comp_eval_pi_uniformOn (fun i => X i ^ 2), Finset.sum_const,
      Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, ← div_eq_mul_inv]
  rw [hvar] at h3
  exact h1.trans_le (h2.trans h3)

/-- **Matrix Bernstein without replacement**, Hermitian population: for Hermitian
$\mathbf{X}_i$, $i \in n$, with $\sum_i \mathbf{X}_i = \mathbf{0}$ and
$\mathbf{X}_i \preceq L\mathbf{I}$, $L > 0$, $m$ nonempty, a uniformly random injection
$\iota : k \to n$ and $t \ge 0$,
$$\mathbb{P}\Bigl[\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \ge t\Bigr]
\le \lvert m\rvert \exp\Bigl(\frac{-t^2/2}{v + Lt/3}\Bigr), \qquad
v = \frac{\lvert k\rvert}{\lvert n\rvert}\Bigl\|\sum_i \mathbf{X}_i^2\Bigr\|_2\,.$$
The trace bound `NLAlib.integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective`
in `NLAlib.measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le`. [Tropp2015,
Theorem 6.6.1] (the i.i.d. form, the same bound); [GrossNesme2010, Section D] for the
comparison.
Result: matrix-bernstein-without-replacement -/
theorem measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective
    [Nonempty m] (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hX : ∀ i, (X i).IsHermitian) (hsum : ∑ i, X i = 0)
    (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ eigenvalue (∑ j, X (ι ω j)) 0} ≤
      Fintype.card m * Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n * specNorm (∑ i, X i ^ 2) + L * t / 3)) := by
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [(Measure.map_eq_zero_iff hι.aemeasurable).1
      (by rw [hι.map_eq, uniformOn_injective_of_card_lt hk]), measureReal_zero_apply]
    positivity
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  have h := measureReal_eigenvalue_zero_ge_le_bernstein_of_integral_le
    (ae_of_all _ fun ω => isSelfAdjoint_sum _ fun j _ => hX (ι ω j))
    ((IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun i _ => (hX i).pow 2)) hL
    (fun θ _ => integrable_re_trace_exp_sum_of_hasLaw_uniformOn_injective hι θ)
    (fun θ hθ => integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective hι hL hX
      hsum hle hθ) ht
  rwa [specNorm_real_smul, abs_of_nonneg (by positivity)] at h

/-- **Matrix Bernstein without replacement for the mean**, Hermitian population: for Hermitian
$\mathbf{X}_i$, $i \in n$, with $\sum_i \mathbf{X}_i = \mathbf{0}$ and
$\mathbf{X}_i \preceq L\mathbf{I}$, $L > 0$, $m$ nonempty and a uniformly random injection
$\iota : k \to n$,
$$\mathbb{E}\,\lambda_0\Bigl(\sum_j \mathbf{X}_{\iota(j)}\Bigr) \le \sqrt{2v\log\lvert m\rvert} +
\frac{L\log\lvert m\rvert}{3}, \qquad
v = \frac{\lvert k\rvert}{\lvert n\rvert}\Bigl\|\sum_i \mathbf{X}_i^2\Bigr\|_2\,.$$
The mean form of
`NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`.
[Tropp2015, Theorem 6.6.1] (the i.i.d. form). -/
theorem integral_eigenvalue_zero_sum_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty m]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hX : ∀ i, (X i).IsHermitian) (hsum : ∑ i, X i = 0)
    (hle : ∀ i, X i ≤ L • (1 : Matrix m m 𝕜)) :
    ∫ ω, eigenvalue (∑ j, X (ι ω j)) 0 ∂μ ≤
      √(2 * ((Fintype.card k : ℝ) / Fintype.card n * specNorm (∑ i, X i ^ 2)) *
        Real.log (Fintype.card m)) + L * Real.log (Fintype.card m) / 3 := by
  have hd : (1 : ℝ) ≤ Fintype.card m := by exact_mod_cast Fintype.card_pos
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [(Measure.map_eq_zero_iff hι.aemeasurable).1
      (by rw [hι.map_eq, uniformOn_injective_of_card_lt hk]), integral_zero_measure]
    have := Real.log_nonneg hd
    positivity
  have := hι.isProbabilityMeasure_iff.2 (isProbabilityMeasure_uniformOn_injective hk)
  have h := integral_eigenvalue_zero_le_bernstein_of_integral_le
    (ae_of_all _ fun ω => isSelfAdjoint_sum _ fun j _ => hX (ι ω j))
    ((hι.integrable_comp_iff (f := fun J : k → n => ∑ j, X (J j)) .of_discrete).2 .of_finite)
    ((IsSelfAdjoint.all _).smul (isSelfAdjoint_sum _ fun i _ => (hX i).pow 2)) hL
    (fun θ _ => integrable_re_trace_exp_sum_of_hasLaw_uniformOn_injective hι θ)
    (fun θ hθ => integral_re_trace_exp_sum_le_bernstein_of_hasLaw_uniformOn_injective hι hL hX
      hsum hle hθ)
  rwa [specNorm_real_smul, abs_of_nonneg (by positivity)] at h

end Hermitian

section Rectangular

variable {q r : Type*} [Fintype q] [Fintype r] {S : n → Matrix q r 𝕜}

/-- **Matrix Bernstein without replacement**, rectangular population: for
$\mathbf{S}_i \in \Bbbk^{q \times r}$, $i \in n$, with $\sum_i \mathbf{S}_i = \mathbf{0}$ and
$\|\mathbf{S}_i\|_2 \le L$, $L > 0$, $r$ nonempty, a uniformly random injection $\iota : k \to n$
and $t \ge 0$,
$$\mathbb{P}\Bigl[\Bigl\|\sum_j \mathbf{S}_{\iota(j)}\Bigr\|_2 \ge t\Bigr]
\le (\lvert q\rvert + \lvert r\rvert)\exp\Bigl(\frac{-t^2/2}{v + Lt/3}\Bigr)$$
with variance
$v = (\lvert k\rvert/\lvert n\rvert)\max(\|\sum_i\mathbf{S}_i\mathbf{S}_i^{\mathsf{H}}\|_2,
\|\sum_i\mathbf{S}_i^{\mathsf{H}}\mathbf{S}_i\|_2)$: the Hermitian form on the dilations.
[Tropp2015, Theorem 6.1.1] (the i.i.d. form).
Result: matrix-bernstein-without-replacement -/
theorem measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty r]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hsum : ∑ i, S i = 0) (hle : ∀ i, specNorm (S i) ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ specNorm (∑ j, S (ι ω j))} ≤
      (Fintype.card q + Fintype.card r) * Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n *
          max (specNorm (∑ i, S i * (S i)ᴴ)) (specNorm (∑ i, (S i)ᴴ * S i)) + L * t / 3)) := by
  classical
  have h := measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective
    (X := fun i => dilation (S i)) hι hL (fun i => isHermitian_dilation _)
    (by rw [← dilation_sum, hsum, dilation_zero])
    (fun i => (isHermitian_dilation _).le_smul_one_of_specNorm_le
      (by rw [specNorm_dilation]; exact hle i)) ht
  have hsq (A : Matrix q r 𝕜) : dilation A ^ 2 = Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
    rw [sq, dilation_mul_dilation]
  simp only [← dilation_sum, eigenvalue_zero_dilation, hsq, Matrix.sum_fromBlocks,
    Finset.sum_const_zero, specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

/-- **Matrix Bernstein without replacement for the mean**, rectangular population: for
$\mathbf{S}_i \in \Bbbk^{q \times r}$, $i \in n$, with $\sum_i \mathbf{S}_i = \mathbf{0}$ and
$\|\mathbf{S}_i\|_2 \le L$, $L > 0$, $r$ nonempty and a uniformly random injection
$\iota : k \to n$,
$$\mathbb{E}\Bigl\|\sum_j \mathbf{S}_{\iota(j)}\Bigr\|_2 \le \sqrt{2v\log d} + \frac{L\log d}{3}$$
with variance
$v = (\lvert k\rvert/\lvert n\rvert)\max(\|\sum_i\mathbf{S}_i\mathbf{S}_i^{\mathsf{H}}\|_2,
\|\sum_i\mathbf{S}_i^{\mathsf{H}}\mathbf{S}_i\|_2)$ and $d = \lvert q\rvert + \lvert r\rvert$.
The mean form of
`NLAlib.measureReal_specNorm_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`.
[Tropp2015, Theorem 6.1.1] (the i.i.d. form). -/
theorem integral_specNorm_sum_le_bernstein_of_hasLaw_uniformOn_injective [Nonempty r]
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hsum : ∑ i, S i = 0) (hle : ∀ i, specNorm (S i) ≤ L) :
    ∫ ω, specNorm (∑ j, S (ι ω j)) ∂μ ≤
      √(2 * ((Fintype.card k : ℝ) / Fintype.card n *
          max (specNorm (∑ i, S i * (S i)ᴴ)) (specNorm (∑ i, (S i)ᴴ * S i))) *
        Real.log (Fintype.card q + Fintype.card r)) +
      L * Real.log (Fintype.card q + Fintype.card r) / 3 := by
  classical
  have h := integral_eigenvalue_zero_sum_le_bernstein_of_hasLaw_uniformOn_injective
    (X := fun i => dilation (S i)) hι hL (fun i => isHermitian_dilation _)
    (by rw [← dilation_sum, hsum, dilation_zero])
    (fun i => (isHermitian_dilation _).le_smul_one_of_specNorm_le
      (by rw [specNorm_dilation]; exact hle i))
  have hsq (A : Matrix q r 𝕜) : dilation A ^ 2 = Matrix.fromBlocks (A * Aᴴ) 0 0 (Aᴴ * A) := by
    rw [sq, dilation_mul_dilation]
  simp only [← dilation_sum, eigenvalue_zero_dilation, hsq, Matrix.sum_fromBlocks,
    Finset.sum_const_zero, specNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum, Nat.cast_add] at h
  exact h

end Rectangular

/-- **Bernstein's inequality without replacement**, the $1 \times 1$ case: for a centred
population $a : n \to \mathbb{R}$, $\sum_i a_i = 0$, with $a_i \le L$, $L > 0$, a uniformly random
injection $\iota : k \to n$ and $t \ge 0$,
$$\mathbb{P}\Bigl[\sum_j a_{\iota(j)} \ge t\Bigr] \le
\exp\Bigl(\frac{-t^2/2}{(\lvert k\rvert/\lvert n\rvert)\sum_i a_i^2 + Lt/3}\Bigr)\,,$$
the bound of the i.i.d. sum with the same variance. [Hoeffding1963, Theorem 4] for the comparison
of sampling with and without replacement; the $1 \times 1$ case of
`NLAlib.measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective`. -/
theorem measureReal_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective {a : n → ℝ}
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hL : 0 < L)
    (hsum : ∑ i, a i = 0) (hle : ∀ i, a i ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ ∑ j, a (ι ω j)} ≤
      Real.exp (-(t ^ 2 / 2) /
        ((Fintype.card k : ℝ) / Fintype.card n * ∑ i, a i ^ 2 + L * t / 3)) := by
  have hk1 : 0 < Fintype.card Unit := Fintype.card_pos
  have h := measureReal_eigenvalue_zero_sum_ge_le_bernstein_of_hasLaw_uniformOn_injective
    (𝕜 := ℝ) (m := Unit) (X := fun i => a i • (1 : Matrix Unit Unit ℝ)) hι hL
    (fun i => (IsSelfAdjoint.all (a i)).smul Matrix.isHermitian_one)
    (by rw [← Finset.sum_smul, hsum, zero_smul])
    (fun i => Matrix.le_iff.2 (by
      rw [← sub_smul]
      exact Matrix.PosSemidef.one.smul (sub_nonneg.2 (hle i)))) ht
  have hs : 0 ≤ ∑ i, a i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hspec : specNorm (∑ i, (a i • (1 : Matrix Unit Unit ℝ)) ^ 2) = ∑ i, a i ^ 2 := by
    simp only [smul_pow, one_pow, ← Finset.sum_smul]
    rw [(Matrix.PosSemidef.one.smul hs).specNorm_eq_eigenvalue_zero,
      eigenvalue_real_smul_one _ hk1]
  simp only [← Finset.sum_smul, eigenvalue_real_smul_one _ hk1, Fintype.card_unit,
    Nat.cast_one, one_mul] at h
  rwa [hspec] at h

end NLAlib
