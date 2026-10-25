/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import NLAlib.ForMathlib.InformationTheory.TotalVariation

/-!
# Total variation distance: the theorems of stage LB-A

Statements for `NLAlib/ForMathlib/InformationTheory/TotalVariation.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.7): nonnegativity, the data-processing
inequality, Le Cam's two-point bound for a test, and Pinsker's inequality against Mathlib's
`InformationTheory.klDiv`. These are the information-theoretic tools of the testing route to
query lower bounds (non-adaptive trace estimation, Meyer–Musco–Musco–Woodruff). Upstream
candidates.

## Main results

* `InformationTheory.tvDist_nonneg`, `InformationTheory.tvDist_map_le`.
* `InformationTheory.one_sub_tvDist_le_measureReal_add_measureReal_compl`: Le Cam.
* `InformationTheory.ofReal_two_mul_tvDist_sq_le_klDiv`: Pinsker.
-/

@[expose] public section

open MeasureTheory

namespace InformationTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}

/-- The total variation distance is nonnegative.
Proof: S, about 4 lines. `Real.iSup_nonneg` (or `le_ciSup_of_le` at `A = ∅`, where the term is
`|0 - 0| = 0`, with `abs_nonneg`). -/
theorem tvDist_nonneg (μ ν : Measure α) : 0 ≤ tvDist μ ν := by
  unfold tvDist
  exact Real.iSup_nonneg fun A => abs_nonneg _

/-- The terms of the supremum defining `tvDist` are bounded, for finite measures. -/
private theorem bddAbove_range_abs_sub (μ ν : Measure α) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    BddAbove (Set.range fun A : {A : Set α // MeasurableSet A} => |μ.real A - ν.real A|) := by
  refine ⟨μ.real Set.univ + ν.real Set.univ, ?_⟩
  rintro _ ⟨A, rfl⟩
  have hμ : μ.real A ≤ μ.real Set.univ := measureReal_mono (Set.subset_univ _)
  have hν : ν.real A ≤ ν.real Set.univ := measureReal_mono (Set.subset_univ _)
  rw [abs_sub_le_iff]
  constructor <;> linarith [measureReal_nonneg (μ := μ) (s := A),
    measureReal_nonneg (μ := ν) (s := A)]

/-- **Data processing for total variation**: for finite measures and a measurable map $f$,
$\mathrm{TV}(f_*\mu, f_*\nu) \le \mathrm{TV}(\mu, \nu)$. Applied to the transcript of a query
algorithm, it bounds how well any output distinguishes two input laws.
[Tsybakov2009, Section 2.4]; there for probability measures.
Proof: S, about 10 lines. `ciSup_le`: for measurable $A$, `Measure.map_apply` writes the term as
$\lvert\mu(f^{-1}A) - \nu(f^{-1}A)\rvert$, at most `tvDist μ ν` by `le_ciSup` at
`⟨f ⁻¹' A, hf hA⟩`; the range is bounded above by `μ.real univ + ν.real univ`
(`measureReal_mono`, `abs_sub_le_iff`). -/
theorem tvDist_map_le {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {f : α → β}
    (hf : Measurable f) : tvDist (μ.map f) (ν.map f) ≤ tvDist μ ν := by
  refine ciSup_le fun ⟨A, hA⟩ => ?_
  rw [map_measureReal_apply hf hA, map_measureReal_apply hf hA]
  exact le_ciSup (bddAbove_range_abs_sub μ ν) ⟨f ⁻¹' A, hf hA⟩

/-- **Le Cam's two-point bound**: for probability measures $\mu$, $\nu$ and a measurable set
$A$ (the region where a test decides $\nu$),
$$1 - \mathrm{TV}(\mu, \nu) \le \mu(A) + \nu(A^{c})\,:$$
the two error probabilities of any test sum to at least $1 - \mathrm{TV}(\mu, \nu)$.
[Tsybakov2009, Theorem 2.2]; there as a lower bound on the minimax probability of error.
Proof: S, about 6 lines. `prob_compl_eq_one_sub` for $\nu(A^{c})$ (`measureReal_compl`); then
$1 - (\mu(A) + \nu(A^c)) = \nu(A) - \mu(A) \le \lvert\mu(A) - \nu(A)\rvert \le \mathrm{TV}$
(`le_abs_self`, `abs_sub_comm`, `le_ciSup`; the range is bounded by $2$). -/
theorem one_sub_tvDist_le_measureReal_add_measureReal_compl {μ ν : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {A : Set α} (hA : MeasurableSet A) :
    1 - tvDist μ ν ≤ μ.real A + ν.real Aᶜ := by
  have hle : |μ.real A - ν.real A| ≤ tvDist μ ν :=
    le_ciSup (bddAbove_range_abs_sub μ ν) ⟨A, hA⟩
  rw [measureReal_compl hA, probReal_univ]
  linarith [neg_abs_le (μ.real A - ν.real A)]

/-- The logit minus $4x$ is monotone on $(0, 1)$. -/
private lemma log_sub_log_one_sub_sub_le {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    Real.log a - Real.log (1 - a) - 4 * a ≤ Real.log b - Real.log (1 - b) - 4 * b := by
  have hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt
      (fun x => Real.log x - Real.log (1 - x) - 4 * x) (1 / x + 1 / (1 - x) - 4) x := by
    intro x hx
    have h1 : 1 - x ≠ 0 := by linarith [hx.2]
    have h := ((Real.hasDerivAt_log hx.1.ne').sub
      (((hasDerivAt_id' x).const_sub 1).log h1)).sub ((hasDerivAt_id' x).const_mul 4)
    exact h.congr_deriv (by ring)
  refine monotoneOn_of_hasDerivWithinAt_nonneg (f' := fun x => 1 / x + 1 / (1 - x) - 4)
    (convex_Ioo 0 1)
    (fun x hx => (hd x hx).continuousAt.continuousWithinAt) (fun x hx => ?_) (fun x hx => ?_)
    ⟨ha, hab.trans_lt hb⟩ ⟨ha.trans_le hab, hb⟩ hab
  · rw [interior_Ioo] at hx ⊢; exact (hd x hx).hasDerivWithinAt
  · rw [interior_Ioo] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1 : 0 < 1 - x := by linarith
    rw [div_add_div _ _ hx0.ne' h1.ne', sub_nonneg, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2 * x - 1)]

/-- Binary Pinsker on the open square: the derivative step. -/
private lemma two_mul_sub_sq_le_binary_of_pos {p r : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hr0 : 0 < r) (hr1 : r < 1) :
    2 * (p - r) ^ 2 ≤ p * Real.log (p / r) + (1 - p) * Real.log ((1 - p) / (1 - r)) := by
  set G : ℝ → ℝ := fun x => x * Real.log x - x * Real.log r + (1 - x) * Real.log (1 - x)
    - (1 - x) * Real.log (1 - r) - 2 * (x - r) ^ 2
  have hGr : G r = 0 := by simp only [G]; ring
  have hcont : Continuous G := by
    have h1 := Real.continuous_mul_log
    have h2 : Continuous fun x : ℝ => (1 - x) * Real.log (1 - x) :=
      Real.continuous_mul_log.comp (by fun_prop)
    fun_prop
  set G' : ℝ → ℝ := fun x => (Real.log x - Real.log (1 - x) - 4 * x)
      - (Real.log r - Real.log (1 - r) - 4 * r)
  have hd : ∀ x ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt G (G' x) x := by
    intro x hx
    have h1 : 1 - x ≠ 0 := by linarith [hx.2]
    have h := ((((Real.hasDerivAt_mul_log hx.1.ne').sub
      ((hasDerivAt_id' x).mul_const (Real.log r))).add
      ((Real.hasDerivAt_mul_log h1).comp x ((hasDerivAt_id' x).const_sub 1))).sub
      (((hasDerivAt_id' x).const_sub 1).mul_const (Real.log (1 - r)))).sub
      ((((hasDerivAt_id' x).sub_const r).pow 2).const_mul 2)
    exact h.congr_deriv (by ring)
  have hGp : 0 ≤ G p := by
    rcases le_total r p with hrp | hpr
    · refine hGr ▸ monotoneOn_of_hasDerivWithinAt_nonneg (f' := G') (convex_Icc r 1)
        hcont.continuousOn
        (fun x hx => ?_) (fun x hx => ?_) ⟨le_rfl, hr1.le⟩ ⟨hrp, hp1⟩ hrp
      · rw [interior_Icc] at hx ⊢
        exact (hd x ⟨hr0.trans hx.1, hx.2⟩).hasDerivWithinAt
      · rw [interior_Icc] at hx
        linarith [log_sub_log_one_sub_sub_le hr0 hx.1.le hx.2]
    · refine hGr ▸ antitoneOn_of_hasDerivWithinAt_nonpos (f' := G') (convex_Icc 0 r)
        hcont.continuousOn
        (fun x hx => ?_) (fun x hx => ?_) ⟨hp0, hpr⟩ ⟨hr0.le, le_rfl⟩ hpr
      · rw [interior_Icc] at hx ⊢
        exact (hd x ⟨hx.1, hx.2.trans hr1⟩).hasDerivWithinAt
      · rw [interior_Icc] at hx
        linarith [log_sub_log_one_sub_sub_le hx.1 hx.2.le hr1]
  have e1 : p * Real.log (p / r) = p * Real.log p - p * Real.log r := by
    rcases eq_or_ne p 0 with rfl | hp
    · simp
    rw [Real.log_div hp hr0.ne']; ring
  have e2 : (1 - p) * Real.log ((1 - p) / (1 - r))
      = (1 - p) * Real.log (1 - p) - (1 - p) * Real.log (1 - r) := by
    rcases eq_or_ne (1 - p) 0 with hp | hp
    · simp [hp]
    rw [Real.log_div hp (by linarith)]; ring
  simp only [G] at hGp
  linarith

/-- The Kullback–Leibler divergence of two equal-mass finite measures on a finite type. -/
private lemma toReal_klDiv_eq_sum {γ : Type*} [Fintype γ] [MeasurableSpace γ]
    [MeasurableSingletonClass γ] {P Q : Measure γ} [IsFiniteMeasure P] [IsFiniteMeasure Q]
    (hPQ : P ≪ Q) (h_eq : P Set.univ = Q Set.univ) :
    (klDiv P Q).toReal = ∑ b, P.real {b} * Real.log (P.real {b} / Q.real {b}) := by
  rw [toReal_klDiv_of_measure_eq hPQ h_eq, integral_fintype .of_finite]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases eq_or_ne (Q {b}) 0 with hQ | hQ
  · simp [measureReal_def, hPQ hQ]
  have h2 : P {b} = P.rnDeriv Q b * Q {b} := by
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq P Q hPQ]
    rw [withDensity_apply _ (measurableSet_singleton b), lintegral_singleton]
  rw [smul_eq_mul, llr_def, measureReal_def, measureReal_def, h2, ENNReal.toReal_mul,
    mul_div_cancel_right₀ _ (ENNReal.toReal_ne_zero.mpr ⟨hQ, measure_ne_top _ _⟩)]

/-- **Pinsker's inequality**: for probability measures,
$2\,\mathrm{TV}(\mu, \nu)^2 \le \mathrm{KL}(\mu \,\|\, \nu)$, stated in `ℝ≥0∞` so that it holds
also when the divergence is infinite.
[Tsybakov2009, Lemma 2.5]; there as $\mathrm{TV} \le \sqrt{\mathrm{KL}/2}$.
Proof: L, about 60 lines. If `klDiv μ ν = ⊤` there is nothing to prove. Otherwise, for measurable
$A$ the indicator map $\mathbf{1}_A : \alpha \to$ `Bool` gives
$\mathrm{KL}(\mathrm{Ber}(\mu(A)) \,\|\, \mathrm{Ber}(\nu(A))) \le \mathrm{KL}(\mu \,\|\, \nu)$ by
`InformationTheory.klDiv_map_le`; the two-point divergence is
$p\log\frac{p}{r} + (1-p)\log\frac{1-p}{1-r}$ (compute `klDiv` on `Bool` from `toReal_klDiv`
and `llr` of measures on a finite type), and the binary Pinsker inequality
$2(p - r)^2 \le p\log\frac{p}{r} + (1-p)\log\frac{1-p}{1-r}$ for $p, r \in [0, 1]$ (a private
real lemma: the right side minus the left is
$\int_r^p \bigl(\frac{p - t}{t(1-t)} - 4(p - t)\bigr)\,dt \ge 0$, or monotonicity in $r$ on
each side of $p$ by the derivative) closes it; take the supremum over $A$
(`ENNReal.ofReal` of a `ciSup`, `Real.iSup` bounded). -/
theorem ofReal_two_mul_tvDist_sq_le_klDiv (μ ν : Measure α) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : ENNReal.ofReal (2 * tvDist μ ν ^ 2) ≤ klDiv μ ν := by
  by_cases hKL : klDiv μ ν = ⊤
  · simp [hKL]
  have hac : μ ≪ ν := (klDiv_ne_top_iff.mp hKL).1
  have hK : 0 ≤ (klDiv μ ν).toReal := ENNReal.toReal_nonneg
  have key : ∀ A, MeasurableSet A → 2 * (μ.real A - ν.real A) ^ 2 ≤ (klDiv μ ν).toReal := by
    intro A hA
    classical
    rcases (measureReal_nonneg (μ := ν) (s := A)).eq_or_lt with h0 | h0
    · have : μ.real A = 0 :=
        (measureReal_eq_zero_iff).mpr (hac ((measureReal_eq_zero_iff).mp h0.symm))
      rw [this, ← h0]; simp [hK]
    rcases (measureReal_le_one (μ := ν) (s := A)).eq_or_lt with h1 | h1
    · have hc : ν.real Aᶜ = 0 := by rw [measureReal_compl hA, h1]; simp
      have := measureReal_compl (μ := μ) hA
      rw [(measureReal_eq_zero_iff).mpr (hac ((measureReal_eq_zero_iff).mp hc))] at this
      replace this : μ.real A = 1 := by simp at this; linarith
      rw [this, h1]; simp [hK]
    set g : α → Bool := fun x => (x ∈ A : Bool)
    have hg : Measurable g :=
      measurable_to_countable' fun b => by
        cases b <;> simp [g, Set.preimage, ← Set.compl_ofPred, hA.compl, hA]
    have hpre : ∀ (ρ : Measure α) [IsProbabilityMeasure ρ],
        (ρ.map g).real {true} = ρ.real A ∧ (ρ.map g).real {false} = 1 - ρ.real A := by
      intro ρ _
      have ht : g ⁻¹' {true} = A := by ext; simp [g]
      have hf : g ⁻¹' {false} = Aᶜ := by ext; simp [g]
      rw [map_measureReal_apply hg (measurableSet_singleton _), ht,
        map_measureReal_apply hg (measurableSet_singleton _), hf, measureReal_compl hA]
      simp
    have hmono := klDiv_map_le (μ := μ) (ν := ν) hg
    have := Measure.isProbabilityMeasure_map (μ := μ) hg.aemeasurable
    have := Measure.isProbabilityMeasure_map (μ := ν) hg.aemeasurable
    calc 2 * (μ.real A - ν.real A) ^ 2
        ≤ μ.real A * Real.log (μ.real A / ν.real A)
          + (1 - μ.real A) * Real.log ((1 - μ.real A) / (1 - ν.real A)) :=
          two_mul_sub_sq_le_binary_of_pos measureReal_nonneg measureReal_le_one h0 h1
      _ = (klDiv (μ.map g) (ν.map g)).toReal := by
          rw [toReal_klDiv_eq_sum (hac.map hg) (by rw [measure_univ, measure_univ]),
            Fintype.sum_bool, (hpre μ).1, (hpre μ).2, (hpre ν).1, (hpre ν).2]
      _ ≤ _ := ENNReal.toReal_mono hKL hmono
  have htv : tvDist μ ν ≤ √((klDiv μ ν).toReal / 2) := by
    refine ciSup_le fun A => Real.abs_le_sqrt ?_
    linarith [key A.1 A.2]
  rw [← ENNReal.ofReal_toReal hKL]
  refine ENNReal.ofReal_le_ofReal ?_
  have := pow_le_pow_left₀ (tvDist_nonneg μ ν) htv 2
  rw [Real.sq_sqrt (by positivity)] at this
  linarith

end InformationTheory
