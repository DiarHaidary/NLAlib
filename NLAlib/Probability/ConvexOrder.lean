/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Convex.Integral
public import Mathlib.GroupTheory.GroupAction.MultipleTransitivity
public import Mathlib.Probability.Kernel.Composition.IntegralCompProd
public import NLAlib.Probability.Distributions.UniformInjection

/-!
# Convex order from a barycenter, and Hoeffding's comparison

A random vector $Y$ dominates $X$ in convex order when $\mathbb{E} f(X) \le \mathbb{E} f(Y)$ for
every convex $f$. The easy direction of Strassen's theorem gives it from a coupling in which
$X$ is the conditional barycenter of $Y$: if a Markov kernel $\kappa$ moves the law $\mu$ of the
first variable to $\kappa \circ \mu$ and $\int Y \, d\kappa(a) = X(a)$, Jensen's inequality in
each fibre and integration in $a$ give the comparison
(`ConvexOn.integral_comp_le_integral_comp_of_integral_eq`). Its main instance is
**Hoeffding's comparison**: a population sum $\sum_j \mathbf{a}_{\iota(j)}$ over a uniformly random
injection $\iota : k \to n$ (sampling without replacement) is dominated in convex order by the
same sum over $\lvert k \rvert$ i.i.d. uniform indices (sampling with replacement)
(`ConvexOn.integral_uniformOn_injective_le_integral_pi`). Through one convex function each, it
transfers every exponential-moment tail of sampling with replacement to sampling without
replacement; the matrix Chernoff tails without replacement are the first consumer
(`NLAlib.Probability.MatrixConcentration.ChernoffWithoutReplacement`).

The values lie in any real Banach space, and $f$ is convex and continuous on a closed convex set
$s$ holding the values (the positive semidefinite cone for $\operatorname{tr} e^{\theta \cdot}$,
which is convex only on Hermitian matrices). Neither theorem uses NLAlib vocabulary; both are
upstream candidates, declared in the `ConvexOn` namespace for dot notation.

This file is a skeleton of Sketching stage S5 (`docs/design/Sketching-S5.md` §3.2, §8): the
proof of Hoeffding's comparison is deferred (`sorry`); the kernel form is proved.

## Main results

* `ConvexOn.integral_comp_le_integral_comp_of_integral_eq`: convex order from a conditional
  barycenter, in kernel form.
* `ConvexOn.integral_uniformOn_injective_le_integral_pi`: Hoeffding's comparison of sampling
  without and with replacement.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {α β E : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} [NormedAddCommGroup E]
  [NormedSpace ℝ E] [CompleteSpace E] {s : Set E} {f : E → ℝ}

/-- **Convex order from a conditional barycenter.** Let $\kappa$ be a Markov kernel from $\alpha$
to $\beta$, $\mu$ an s-finite measure on $\alpha$, and $X : \alpha \to E$, $Y : \beta \to E$ with
$Y$ integrable under almost every $\kappa(a)$ and with barycenter
$\int Y \, d\kappa(a) = X(a)$. Then for every $f$ convex and continuous on a closed set $s$
holding the values of $Y$,
$$\int f(X(a)) \, d\mu(a) \le \int f(Y(b)) \, d(\kappa \circ \mu)(b) \,.$$
Jensen's inequality (`ConvexOn.map_integral_le`) in each fibre, then integration in $a$. This is
the easy direction of Strassen's theorem (Strassen 1965, not in hand); proved from Jensen's
inequality alone. The integrability of $f \circ X$ is a hypothesis: it follows from that of
$f \circ Y$ only through a supporting hyperplane and a measurability argument, and every consumer
has it from finiteness. -/
theorem _root_.ConvexOn.integral_comp_le_integral_comp_of_integral_eq (hf : ConvexOn ℝ s f)
    (hfc : ContinuousOn f s) (hs : IsClosed s) {μ : Measure α} [SFinite μ] {κ : Kernel α β}
    [IsMarkovKernel κ] {X : α → E} {Y : β → E} (hY : ∀ᵐ a ∂μ, Integrable Y (κ a))
    (hYs : ∀ᵐ a ∂μ, ∀ᵐ b ∂(κ a), Y b ∈ s) (hbar : ∀ᵐ a ∂μ, ∫ b, Y b ∂(κ a) = X a)
    (hfX : Integrable (fun a => f (X a)) μ) (hfY : Integrable (fun b => f (Y b)) (κ ∘ₘ μ)) :
    ∫ a, f (X a) ∂μ ≤ ∫ b, f (Y b) ∂(κ ∘ₘ μ) := by
  have hc : κ ∘ₘ μ = (κ ∘ₖ Kernel.const Unit μ) () := Measure.comp_eq_comp_const_apply
  have hfY' : Integrable (fun b => f (Y b)) ((κ ∘ₖ Kernel.const Unit μ) ()) := hc ▸ hfY
  have hint : Integrable (fun a => ∫ b, f (Y b) ∂(κ a)) μ := by
    simpa only [Kernel.const_apply] using hfY'.integral_comp
  have hfYa : ∀ᵐ a ∂μ, Integrable (fun b => f (Y b)) (κ a) :=
    Measure.ae_integrable_of_integrable_comp hfY
  have heq : ∫ b, f (Y b) ∂(κ ∘ₘ μ) = ∫ a, ∫ b, f (Y b) ∂(κ a) ∂μ := by
    rw [hc, Kernel.integral_comp hfY', Kernel.const_apply]
  rw [heq]
  refine integral_mono_ae hfX hint ?_
  filter_upwards [hY, hYs, hbar, hfYa] with a h1 h2 h3 h4
  rw [← h3]
  exact hf.map_integral_le hfc hs h2 h1 h4

/-- **Hoeffding's comparison**: a population sum sampled without replacement is dominated in
convex order by the same sum sampled with replacement. For a population
$\mathbf{a} : n \to E$ in a real Banach space, $\lvert k \rvert \le \lvert n \rvert$, and $f$
convex and continuous on a closed set $s$ holding every with-replacement sum
$\sum_j \mathbf{a}_{J(j)}$,
$$\mathbb{E}_{\iota} f\Bigl(\sum_j \mathbf{a}_{\iota(j)}\Bigr) \le
\mathbb{E}_{J} f\Bigl(\sum_j \mathbf{a}_{J(j)}\Bigr) \,,$$
$\iota : k \to n$ a uniform injection, $J$ a vector of $\lvert k \rvert$ i.i.d. uniform indices.
[Hoeffding1963] (there scalar, $f$ continuous and convex); [GrossNesme2010] (the matrix form).
Here any real Banach space and any $f$ convex and continuous on a closed convex $s$; the hypothesis
$\lvert k \rvert \le \lvert n \rvert$ is needed since otherwise the left side is $0$ and a convex
$f$ may be negative. Proof: the kernel form with a private kernel that composes the injection
with a random pattern $k \to k$ whose law is invariant under permutations of $k$ (the barycenter
is the injective sum) and whose composition with a uniform injection is uniform on $k \to n$.
Port of the prototype's `integral_uniform_subset_convex_le_iid` (there on subsets, `PMF`, `Fin k`
and $s$ the whole space).
Result: hoeffding-sampling-without-replacement -/
theorem _root_.ConvexOn.integral_uniformOn_injective_le_integral_pi {k n : Type*} [Fintype k]
    [Fintype n] [MeasurableSpace n] [MeasurableSingletonClass n] (hf : ConvexOn ℝ s f)
    (hfc : ContinuousOn f s) (hs : IsClosed s) (hk : Fintype.card k ≤ Fintype.card n) (A : n → E)
    (hA : ∀ J : k → n, ∑ j, A (J j) ∈ s) :
    ∫ ι, f (∑ j, A (ι j)) ∂uniformOn {ι : k → n | Function.Injective ι} ≤
      ∫ J, f (∑ j, A (J j)) ∂Measure.pi fun _ : k => uniformOn (Set.univ : Set n) := by
  sorry

end NLAlib
