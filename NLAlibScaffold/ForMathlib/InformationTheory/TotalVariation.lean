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
  sorry

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
  sorry

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
  sorry

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
  sorry

end InformationTheory
