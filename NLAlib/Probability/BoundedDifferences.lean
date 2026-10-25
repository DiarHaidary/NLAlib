/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import NLAlib.Probability.Entropy
public import NLAlib.Probability.EntropyTensorization

/-!
# The bounded differences inequality

A function $f$ of independent coordinates $X_i \in S_i$ whose value changes by at most $c_i$ when
the $i$-th coordinate alone changes is sub-Gaussian about its mean with proxy $\sum_i c_i^2 / 4$,
and its upper tail is McDiarmid's $\exp(-2t^2 / \sum_i c_i^2)$. The proof is the entropy method:
the tensorization of entropy over the product law of $X$ (`NLAlib.entropy_pi_le_sum`), the entropy
form of Hoeffding's lemma on each fibre (`NLAlib.entropy_exp_mul_le_of_abs_sub_le`) and Herbst's
argument (`NLAlib.hasSubgaussianMGF_sub_integral_of_entropy_le`).

The coordinates live in arbitrary measurable spaces. No integrability is assumed: bounded
differences on a finite product make $f$ bounded. No probability hypothesis is assumed either:
`iIndepFun` gives it (`ProbabilityTheory.iIndepFun.isProbabilityMeasure`). Lower and two-sided
tails are the same statements for $-f$, with `NLAlib.measureReal_abs_ge_le_add`; they are not
restated.

## Main results

* `NLAlib.hasSubgaussianMGF_sub_integral_of_abs_update_sub_le`: bounded differences.
* `NLAlib.measureReal_sub_integral_ge_le_mcdiarmid`: McDiarmid's inequality.

## References

* [S. Boucheron, G. Lugosi, P. Massart, *Concentration Inequalities*][BoucheronLugosiMassart2013],
  Theorem 6.2.
* [C. McDiarmid, *On the method of bounded differences*][McDiarmid1989].
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ι : Type*} [Fintype ι]
  [DecidableEq ι] {S : ι → Type*} [∀ i, MeasurableSpace (S i)] {X : Ω → ∀ i, S i}
  {f : (∀ i, S i) → ℝ} {c : ι → ℝ≥0}

omit [∀ i, MeasurableSpace (S i)] in
/-- Bounded differences bound the oscillation of $f$ by $\sum_i c_i$:
$\lvert f(y) - f(x)\rvert \le \sum_i c_i$. -/
private theorem abs_sub_le_sum_of_abs_update_sub_le
    (hc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) (x y : ∀ i, S i) :
    |f y - f x| ≤ ∑ i, (c i : ℝ) := by
  have key : ∀ T : Finset ι, |f (T.piecewise y x) - f x| ≤ ∑ i ∈ T, (c i : ℝ) := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert i T hi ih =>
      rw [Finset.piecewise_insert, Finset.sum_insert hi]
      calc |f (Function.update (T.piecewise y x) i (y i)) - f x|
          ≤ |f (Function.update (T.piecewise y x) i (y i)) - f (T.piecewise y x)| +
            |f (T.piecewise y x) - f x| := abs_sub_le _ _ _
        _ ≤ _ := add_le_add (hc _ _ _) ih
  simpa using key Finset.univ

omit [Fintype ι] [DecidableEq ι] in
/-- A bounded measurable $F$ makes $e^{sF} \log e^{sF}$ integrable under a finite measure. -/
private theorem integrable_exp_mul_mul_log_of_abs_le {α : Type*} {mα : MeasurableSpace α}
    {ρ : Measure α} [IsFiniteMeasure ρ] {F : α → ℝ} (hF : Measurable F) {B : ℝ}
    (hB : ∀ a, |F a| ≤ B) (s : ℝ) :
    Integrable (fun a => rexp (s * F a) * Real.log (rexp (s * F a))) ρ := by
  have hsB : ∀ a, |s * F a| ≤ |s| * B := fun a => by
    rw [abs_mul]; gcongr; exact hB a
  have hb : ∀ a, |rexp (s * F a)| ≤ rexp (|s| * B) := fun a => by
    rw [abs_of_pos (Real.exp_pos _), Real.exp_le_exp]
    exact (le_abs_self _).trans (hsB a)
  simp only [Real.log_exp]
  refine Integrable.of_bound (by fun_prop) (rexp (|s| * B) * (|s| * B))
    (ae_of_all _ fun a => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  gcongr
  · exact hb a
  · exact hsB a

/-- Bounded differences on the product of the coordinate laws: under `Measure.pi ν`,
$f - \mathbb{E} f$ is sub-Gaussian with proxy $\sum_i c_i^2 / 4$. -/
private theorem hasSubgaussianMGF_pi_sub_integral_of_abs_update_sub_le
    (ν : ∀ i, Measure (S i)) [∀ i, IsProbabilityMeasure (ν i)] (hf : Measurable f)
    (hc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) :
    HasSubgaussianMGF (fun x => f x - ∫ x', f x' ∂Measure.pi ν) ((∑ i, c i ^ 2) / 4)
      (Measure.pi ν) := by
  obtain ⟨x₀⟩ := nonempty_of_isProbabilityMeasure (Measure.pi ν)
  set B := |f x₀| + ∑ i, (c i : ℝ) with hB
  have hbd : ∀ x, |f x| ≤ B := fun x => by
    have h1 := abs_sub_le_sum_of_abs_update_sub_le hc x₀ x
    have h2 := abs_sub_abs_le_abs_sub (f x) (f x₀)
    linarith
  have hfib : ∀ i x, Measurable (fun y => f (Function.update x i y)) := fun i x =>
    hf.comp (measurable_update x)
  have hint (s : ℝ) : Integrable (fun x => rexp (s * f x)) (Measure.pi ν) :=
    integrable_exp_mul_of_mem_Icc hf.aemeasurable (ae_of_all _ fun x => abs_le.mp (hbd x))
  refine hasSubgaussianMGF_sub_integral_of_entropy_le hint (fun s => ?_)
  have hT := entropy_pi_le_sum ν (by fun_prop) (fun x => (Real.exp_pos (s * f x)).le) (hint s)
    (integrable_exp_mul_mul_log_of_abs_le (ρ := Measure.pi ν) hf hbd s)
  refine hT.trans ?_
  have hent : ∀ i x, entropy (ν i) (fun y => rexp (s * f (Function.update x i y))) ≤
      s ^ 2 * (c i : ℝ) ^ 2 / 8 * ∫ y, rexp (s * f (Function.update x i y)) ∂ν i :=
    fun i x => entropy_exp_mul_le_of_abs_sub_le (hfib i x).aemeasurable (fun y y' => by
      have h := hc i (Function.update x i y') y
      rwa [Function.update_idem] at h) s
  have hnn : ∀ i x, 0 ≤ entropy (ν i) (fun y => rexp (s * f (Function.update x i y))) :=
    fun i x => entropy_nonneg (ae_of_all _ fun _ => (Real.exp_pos _).le)
      (integrable_exp_mul_of_mem_Icc (hfib i x).aemeasurable
        (ae_of_all _ fun y => abs_le.mp (hbd _)))
      (integrable_exp_mul_mul_log_of_abs_le (hfib i x) (fun y => hbd _) s)
  set E := ∫ x, rexp (s * f x) ∂Measure.pi ν with hE
  calc ∑ i, ∫ x, entropy (ν i) (fun y => rexp (s * f (Function.update x i y))) ∂Measure.pi ν
      ≤ ∑ i, ∫ x, s ^ 2 * (c i : ℝ) ^ 2 / 8 *
          ∫ y, rexp (s * f (Function.update x i y)) ∂ν i ∂Measure.pi ν :=
        Finset.sum_le_sum fun i _ => integral_mono_of_nonneg (ae_of_all _ (hnn i))
          ((integrable_integral_update_pi ν i (hint s)).const_mul _) (ae_of_all _ (hent i))
    _ = ∑ i, (c i : ℝ) ^ 2 * (s ^ 2 / 8 * E) := Finset.sum_congr rfl fun i _ => by
        rw [integral_const_mul, integral_integral_update_pi ν i (hint s)]
        ring
    _ = _ := by
        rw [← Finset.sum_mul]
        push_cast
        ring

/-- **The bounded differences inequality**: a measurable function $f$ of independent coordinates
$X_i$ whose value changes by at most $c_i$ when the $i$-th coordinate alone changes,
$\lvert f(x') - f(x)\rvert \le c_i$ whenever $x'$ differs from $x$ only in coordinate $i$, is
sub-Gaussian about its mean, $f(X) - \mathbb{E} f(X)$, with proxy
$$\frac{\sum_i c_i^2}{4}\,.$$
[BoucheronLugosiMassart2013, Theorem 6.2]; [McDiarmid1989]. Coordinates in arbitrary measurable
spaces; no integrability or probability hypothesis ($f$ is bounded; `iIndepFun` gives a
probability measure).
Result: bounded-differences -/
theorem hasSubgaussianMGF_sub_integral_of_abs_update_sub_le
    (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ) (hind : iIndepFun (fun i ω => X ω i) μ)
    (hf : Measurable f) (hc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) :
    HasSubgaussianMGF (fun ω => f (X ω) - ∫ ω', f (X ω') ∂μ) ((∑ i, c i ^ 2) / 4) μ := by
  have hprob : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hν : ∀ i, IsProbabilityMeasure (μ.map fun ω => X ω i) := fun i =>
    Measure.isProbabilityMeasure_map (hX i)
  have hXm : AEMeasurable X μ := aemeasurable_pi_lambda _ hX
  have hlaw : μ.map X = Measure.pi fun i => μ.map fun ω => X ω i :=
    (iIndepFun_iff_map_fun_eq_pi_map hX).1 hind
  have h := hasSubgaussianMGF_pi_sub_integral_of_abs_update_sub_le
    (fun i => μ.map fun ω => X ω i) hf hc
  rw [← hlaw, integral_map hXm hf.aestronglyMeasurable] at h
  exact h.of_map hXm

/-- **McDiarmid's inequality**: for a measurable function $f$ of independent coordinates with
bounded differences $c_i$ and $t \ge 0$,
$$\mathbb{P}\bigl[t \le f(X) - \mathbb{E} f(X)\bigr]
\le \exp\Bigl(-\frac{2t^2}{\sum_i c_i^2}\Bigr).$$
[McDiarmid1989]; [BoucheronLugosiMassart2013, Theorem 6.2]. The source's constant. At
$\sum_i c_i^2 = 0$ the bound is $e^0 = 1$ (Lean's $x / 0 = 0$), which is true.
Result: mcdiarmid -/
theorem measureReal_sub_integral_ge_le_mcdiarmid (hX : ∀ i, AEMeasurable (fun ω => X ω i) μ)
    (hind : iIndepFun (fun i ω => X ω i) μ) (hf : Measurable f)
    (hc : ∀ i x y, |f (Function.update x i y) - f x| ≤ c i) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | t ≤ f (X ω) - ∫ ω', f (X ω') ∂μ} ≤ rexp (-2 * t ^ 2 / ∑ i, (c i : ℝ) ^ 2) := by
  refine ((hasSubgaussianMGF_sub_integral_of_abs_update_sub_le hX hind hf hc).measure_ge_le
    ht).trans_eq ?_
  congr 1
  push_cast
  ring

end NLAlib
