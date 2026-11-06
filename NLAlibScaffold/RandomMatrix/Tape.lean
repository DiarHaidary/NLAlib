/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Tape
public import NLAlib.Computation.Contract

/-!
# Uniform draws and the rounded probabilistic model (scaffold)

Statements for `NLAlib/RandomMatrix/Tape.lean` (stage COMPDYN S1b, design note
`docs/design/Computation-DynamicPrograms.md`, §4.5, §6.3 and "S1 implementation status"): the
uniform law on $[-1, 1]$, almost every ideal uniform draw lies in $[-1, 1]$, so does almost every
stored one under the tape-rounding contract, and the rounded probabilistic model is monotone in
its bound.

## Main results

* `NLAlib.Computation.Dist.law_uniform_Icc`: the uniform law gives $[-1, 1]$ mass one.
* `NLAlib.Computation.Dist.measureReal_law_uniform_Icc`: the mass of a subinterval.
* `NLAlib.Computation.ae_forall_mem_Icc_of_hasLaw_tapeLaw`: ideal uniform draws lie in
  $[-1, 1]$.
* `NLAlib.Computation.IsTapeRounding.ae_forall_mem_Icc_of_hasLaw_tapeLaw`: so do stored ones.
* `NLAlib.Computation.MatrixFreeRoundedProb.mono`: a larger bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace NLAlib.Computation

/-- **The uniform law lives on $[-1, 1]$**: the law of a uniform draw gives the interval
$[-1, 1]$ mass one. No printed source.
Proof: `Dist.law` at `.uniform` is `volume[|Set.Icc (-1) 1]`; `ProbabilityTheory.cond_apply_self`
with `volume (Set.Icc (-1 : ℝ) 1) ≠ 0` (`Real.volume_Icc`, `ENNReal.ofReal_eq_zero`, `norm_num`) and
`≠ ∞` (`measure_Icc_lt_top`). S, about 4 lines. -/
theorem Dist.law_uniform_Icc : Dist.uniform.law (Set.Icc (-1) 1) = 1 := by
  have h0 : volume (Set.Icc (-1 : ℝ) 1) ≠ 0 := by
    rw [Real.volume_Icc]
    norm_num
  have htop : volume (Set.Icc (-1 : ℝ) 1) ≠ ⊤ := measure_Icc_lt_top.ne
  change (volume[|Set.Icc (-1 : ℝ) 1]) (Set.Icc (-1) 1) = 1
  rw [cond_apply measurableSet_Icc, Set.inter_self, ENNReal.inv_mul_cancel h0 htop]

/-- **The uniform law of a subinterval**: for $-1 \le a \le b \le 1$, a uniform draw lies in
$[a, b]$ with probability
$$\frac{b - a}{2}.$$
No printed source.
Proof: `Measure.real`, `ProbabilityTheory.cond_apply` (`measurableSet_Icc`),
`Set.Icc_inter_Icc` with `max (-1) a = a`, `min 1 b = b`, `Real.volume_Icc`, `ENNReal.toReal_mul`,
`ENNReal.toReal_inv`, `ENNReal.toReal_ofReal` (both lengths nonnegative), `ring`. M, about 12
lines. -/
theorem Dist.measureReal_law_uniform_Icc {a b : ℝ} (ha : -1 ≤ a) (hab : a ≤ b) (hb : b ≤ 1) :
    Dist.uniform.law.real (Set.Icc a b) = (b - a) / 2 := by
  have hab' : 0 ≤ b - a := by linarith
  have h2 : 0 ≤ 1 - (-1 : ℝ) := by norm_num
  change ((volume[|Set.Icc (-1 : ℝ) 1]) (Set.Icc a b)).toReal = _
  rw [cond_apply measurableSet_Icc, Set.Icc_inter_Icc, max_eq_right ha, min_eq_right hb,
    ENNReal.toReal_mul, ENNReal.toReal_inv, Real.volume_Icc, Real.volume_Icc,
    ENNReal.toReal_ofReal hab', ENNReal.toReal_ofReal h2]
  ring

/-- **Ideal uniform draws lie in $[-1, 1]$**: if the tape $\xi$ has the law of the tape
`NLAlib.Computation.tapeLaw` under $\mu$, then $\mu$-almost surely every uniform draw
$\xi(\omega)(\mathsf{uniform}, i)$, $i \in \mathbb{N}$, lies in $[-1, 1]$. No printed source.
Proof: `ae_all_iff` (countably many positions); for one position $i$, the draw has law
`Dist.uniform.law`: `NLAlib.Computation.hasLaw_apply_of_hasLaw_tapeLaw` gives the law
`iidSequence Dist.uniform.law` of the uniform tape, and the coordinate $i$ of it has law
`Dist.uniform.law` by `measurePreserving_eval_infinitePi`. Then `HasLaw.map_eq` turns the event
into one under the law, `ae_map_iff` (with `measurableSet_Icc`) moves it there, and
`ae_iff`, `prob_compl_eq_zero_iff` and `NLAlib.Computation.Dist.law_uniform_Icc` finish it.
M, about 20 lines. -/
theorem ae_forall_mem_Icc_of_hasLaw_tapeLaw {Ω : Type} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ} (hξ : HasLaw ξ tapeLaw μ) :
    ∀ᵐ ω ∂μ, ∀ i, ξ ω .uniform i ∈ Set.Icc (-1 : ℝ) 1 := by
  sorry

/-- **Stored uniform draws lie in $[-1, 1]$**: under the tape-rounding contract
`NLAlib.Computation.IsTapeRounding` for $\rho$, at tag `p`, and an ideal tape $\xi$ with the law of
the tape under $\mu$, $\mu$-almost surely every stored uniform draw
$\rho(\mathsf{uniform}, i, \xi(\omega)(\mathsf{uniform}, i))$ decodes into $[-1, 1]$.
No printed source.
Proof: `(ae_forall_mem_Icc_of_hasLaw_tapeLaw hξ).mono fun ω hω i => h.2 i _ (hω i)`. S, 1
line. -/
theorem IsTapeRounding.ae_forall_mem_Icc_of_hasLaw_tapeLaw {P K : Type} {dec : P → K → ℝ}
    {p : P} {u τ Ω : ℝ} {c : Dist → ℝ} {ρ : Dist → ℕ → ℝ → K}
    (h : IsTapeRounding dec p u τ Ω c ρ)
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {ξ : Ω → Dist → ℕ → ℝ}
    (hξ : HasLaw ξ tapeLaw μ) :
    ∀ᵐ ω ∂μ, ∀ i, dec p (ρ .uniform i (ξ ω .uniform i)) ∈ Set.Icc (-1 : ℝ) 1 := by
  sorry

/-- **A larger bound**: a result in the rounded probabilistic model with the bound `bound` holds
with every pointwise larger bound `bound'`. No printed source.
Proof: `fun N n hv x hpre I ρ hI hρ Ω _ μ ξ hξ => (h N n hv x hpre I ρ hI hρ Ω _ μ ξ hξ).trans
(hb N n x)`. S, 2 lines. -/
theorem MatrixFreeRoundedProb.mono {P ι K : Type} [DecidableEq P] {r b : ℕ} {p : P}
    {prog : Prog P ι r b} {valid : ℕ → (Fin r → ℕ) → Prop} {X : ℕ → (Fin r → ℕ) → Type}
    {inputs : (N : ℕ) → (n : Fin r → ℕ) → X N n → Fin b → Array (Option K)}
    {Contracts : ℕ → (Fin r → ℕ) → Interp P ι K (OpCount P ι) → Prop}
    {ρOK : (Dist → ℕ → ℝ → K) → Prop} {pre : (N : ℕ) → (n : Fin r → ℕ) → X N n → Prop}
    {good : (N : ℕ) → (n : Fin r → ℕ) → X N n → St P K (OpCount P ι) → Prop}
    {bound bound' : (N : ℕ) → (n : Fin r → ℕ) → X N n → ℝ}
    (h : MatrixFreeRoundedProb p prog valid X inputs Contracts ρOK pre good bound)
    (hb : ∀ N n x, bound N n x ≤ bound' N n x) :
    MatrixFreeRoundedProb p prog valid X inputs Contracts ρOK pre good bound' :=
  fun N n hv x hpre I ρ hI hρ Ω _ μ ξ hξ => (h N n hv x hpre I ρ hI hρ Ω _ μ ξ hξ).trans (hb N n x)

end NLAlib.Computation
