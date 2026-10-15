/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Sym.Card
public import NLAlib.Probability.Law
public import NLAlib.Probability.Tail

/-!
# The Johnson–Lindenstrauss property

A random sketch $\mathbf{S}$ with values in $\Bbbk^{k \times n}$ has the *distributional
Johnson–Lindenstrauss property* with distortion $\varepsilon$ and failure probability $\delta$
when, for every unit vector $\mathbf{x}$,
$\mathbb{P}(\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert) \le \delta$; it has the
*JL moment property* with exponent $p$ when
$\mathbb{E}\lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert^p \le \varepsilon^p \delta$ for unit
$\mathbf{x}$. The moment property implies the tail property (Markov), and both scale to every
nonzero vector; the tail property gives the Johnson–Lindenstrauss lemma for finitely many points
by a union bound over pairs. The moment property also gives approximate matrix multiplication
(`NLAlib.Sketching.Properties.MatrixMultiplication`).

Both are stated with the non-strict threshold event $\{\varepsilon \le X\}$. Design:
`docs/design/Sketching-S1.md` §3.5.

## Main definitions

* `NLAlib.HasJLProperty S ε δ μ`, `NLAlib.HasJLMoment S ε δ p μ`.

## Main results

* `NLAlib.HasJLProperty.measure_exists_abs_norm_mulVec_sq_sub_ge_le`: the JL lemma.
* `NLAlib.HasJLMoment.hasJLProperty`: moments give tails.
* `NLAlib.HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le`: the moment bound for every
  $\mathbf{x}$.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n : Type*} [Fintype k] [Fintype n] {S : Ω → Matrix k n 𝕜} {ε ε' δ δ' p : ℝ}

/-- **Distributional Johnson–Lindenstrauss property** on unit vectors: for every unit
$\mathbf{x}$, $\mathbb{P}(\varepsilon \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert) \le \delta$.
[Woodruff2014, proof of Lemma 18]; [MartinssonTropp2020, §8.6]. -/
def HasJLProperty (S : Ω → Matrix k n 𝕜) (ε δ : ℝ) (μ : Measure Ω) : Prop :=
  ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    μ.real {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1|} ≤ δ

/-- **JL moment property** with real exponent $p$: for every unit $\mathbf{x}$, the $p$-th moment
is integrable and
$\mathbb{E}\lvert \|\mathbf{S}\mathbf{x}\|^2 - 1 \rvert^p \le \varepsilon^p \delta$. Junk for
$\varepsilon < 0$ (real powers of negative numbers). [Woodruff2014, Definition 12]. -/
structure HasJLMoment (S : Ω → Matrix k n 𝕜) (ε δ p : ℝ) (μ : Measure Ω) : Prop where
  /-- The $p$-th moment of the distortion is finite at every unit vector. -/
  integrable : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    Integrable (fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p) μ
  /-- The $p$-th moment of the distortion is at most $\varepsilon^p \delta$ at every unit
  vector. -/
  integral_le : ∀ x : n → 𝕜, ‖WithLp.toLp 2 x‖ = 1 →
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p ∂μ ≤ ε ^ p * δ

/-- A nonzero vector is its norm times a unit vector, and the distortion scales by
$\|\mathbf{x}\|^2$. -/
private theorem exists_unit_of_ne_zero {x : n → 𝕜} (hx : x ≠ 0) :
    ∃ u : n → 𝕜, ‖WithLp.toLp 2 u‖ = 1 ∧ ∀ A : Matrix k n 𝕜,
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 =
        ‖WithLp.toLp 2 x‖ ^ 2 * (‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 - 1) := by
  set c := ‖WithLp.toLp 2 x‖ with hc
  have hc0 : 0 < c := norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])
  refine ⟨(c⁻¹ : ℝ) • x, ?_, fun A => ?_⟩
  · rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hc0,
      inv_mul_cancel₀ hc0.ne']
  · have hx' : x = c • ((c⁻¹ : ℝ) • x) := by rw [smul_smul, mul_inv_cancel₀ hc0.ne', one_smul]
    conv_lhs => rw [hx']
    rw [Matrix.mulVec_smul, WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hc0]
    ring

/-- The distortion at $\mathbf{x} \ne \mathbf{0}$, to the power $p$, is $\|\mathbf{x}\|^{2p}$
times that at a unit vector. -/
private theorem abs_sub_rpow_eq {x u : n → 𝕜} (hu : ∀ A : Matrix k n 𝕜,
      ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2 =
        ‖WithLp.toLp 2 x‖ ^ 2 * (‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 - 1)) (A : Matrix k n 𝕜) :
    |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p =
      ‖WithLp.toLp 2 x‖ ^ (2 * p) * |‖WithLp.toLp 2 (A *ᵥ u)‖ ^ 2 - 1| ^ p := by
  rw [hu, abs_mul, abs_of_nonneg (sq_nonneg _), Real.mul_rpow (sq_nonneg _) (abs_nonneg _),
    Real.rpow_mul (norm_nonneg _), Real.rpow_two]

/-- The JL property depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasJLProperty_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasJLProperty S ε δ μ ↔ HasJLProperty id ε δ ν := by
  refine forall₂_congr fun x _ => ?_
  have hc : Continuous fun A : Matrix k n 𝕜 => |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| := by
    fun_prop
  rw [hS.measureReal_eq (p := fun A => ε ≤ |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1|)
    (measurableSet_le measurable_const hc.measurable)]
  rfl

/-- The JL moment property depends only on the law of the sketch. -/
theorem _root_.ProbabilityTheory.HasLaw.hasJLMoment_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : HasJLMoment S ε δ p μ ↔ HasJLMoment id ε δ p ν := by
  have hm (x : n → 𝕜) : AEStronglyMeasurable
      (fun A : Matrix k n 𝕜 => |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| ^ p) ν := by
    have hc : Continuous fun A : Matrix k n 𝕜 => |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| := by
      fun_prop
    exact (hc.measurable.pow_const p).aestronglyMeasurable
  have hint (x : n → 𝕜) : ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ p ∂μ =
      ∫ A, |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - 1| ^ p ∂ν := hS.integral_comp (hm x)
  constructor
  · intro h
    exact ⟨fun x hx => (hS.integrable_comp_iff (hm x)).1 (h.integrable x hx),
      fun x hx => (hint x).symm.trans_le (h.integral_le x hx)⟩
  · intro h
    exact ⟨fun x hx => (hS.integrable_comp_iff (hm x)).2 (h.integrable x hx),
      fun x hx => (hint x).trans_le (h.integral_le x hx)⟩

/-- The JL property holds with any larger distortion and failure probability. -/
theorem HasJLProperty.mono [IsFiniteMeasure μ] (h : HasJLProperty S ε δ μ) (hε : ε ≤ ε')
    (hδ : δ ≤ δ') : HasJLProperty S ε' δ' μ := by
  exact fun x hx => (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω =>
    hε.trans hω)).trans ((h x hx).trans hδ)

/-- The JL moment property holds with any larger distortion and failure probability, for
$0 \le \varepsilon$, $0 \le p$, $0 \le \delta$. -/
theorem HasJLMoment.mono (h : HasJLMoment S ε δ p μ) (hε : ε ≤ ε') (hδ : δ ≤ δ') (hε0 : 0 ≤ ε)
    (hp : 0 ≤ p) (hδ0 : 0 ≤ δ) : HasJLMoment S ε' δ' p μ := by
  refine ⟨h.integrable, fun x hx => (h.integral_le x hx).trans ?_⟩
  have hε' : 0 ≤ ε' := hε0.trans hε
  calc ε ^ p * δ ≤ ε' ^ p * δ :=
        mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hε0 hε hp) hδ0
    _ ≤ ε' ^ p * δ' := mul_le_mul_of_nonneg_left hδ (Real.rpow_nonneg hε' p)

/-- The JL property at a nonzero vector $\mathbf{x}$:
$\mathbb{P}(\varepsilon \|\mathbf{x}\|^2 \le \lvert \|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2
\rvert) \le \delta$. -/
theorem HasJLProperty.measure_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ)
    {x : n → 𝕜} (hx : x ≠ 0) :
    μ.real {ω | ε * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2|} ≤ δ := by
  obtain ⟨u, hu, hSu⟩ := exists_unit_of_ne_zero (k := k) hx
  have hc0 : 0 < ‖WithLp.toLp 2 x‖ ^ 2 :=
    pow_pos (norm_pos_iff.2 (by rwa [Ne, WithLp.toLp_eq_zero])) 2
  have e : {ω | ε * ‖WithLp.toLp 2 x‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2|} =
      {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ u)‖ ^ 2 - 1|} := by
    ext ω
    simp only [Set.mem_ofPred_eq, hSu, abs_mul, abs_of_pos hc0]
    constructor
    · intro h'
      exact le_of_mul_le_mul_right (by rwa [mul_comm _ |_|] at h') hc0
    · intro h'
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left h' hc0.le
  rw [e]
  exact h u hu

/-- **Johnson–Lindenstrauss lemma**: for finitely many points $\mathbf{x}_i$, $i \in \iota$, and
$\delta \ge 0$, the probability that some pairwise difference $\mathbf{x}_i - \mathbf{x}_j \ne
\mathbf{0}$ has its squared norm distorted by a factor $\varepsilon$ or more,
$$\varepsilon \|\mathbf{x}_i - \mathbf{x}_j\|^2
\le \bigl\lvert \|\mathbf{S}(\mathbf{x}_i - \mathbf{x}_j)\|^2 - \|\mathbf{x}_i - \mathbf{x}_j\|^2
\bigr\rvert,$$
is at most $\binom{\lvert \iota \rvert}{2} \delta$ (union over unordered pairs).
[Woodruff2014, Definition 3]; there inner products on a finite set, here squared norms of
differences.
Result: jl-lemma -/
theorem HasJLProperty.measure_exists_abs_norm_mulVec_sq_sub_ge_le (h : HasJLProperty S ε δ μ)
    (hδ : 0 ≤ δ) {ι : Type*} [Fintype ι] (x : ι → n → 𝕜) :
    μ.real {ω | ∃ i j, x i ≠ x j ∧ ε * ‖WithLp.toLp 2 (x i - x j)‖ ^ 2 ≤
      |‖WithLp.toLp 2 (S ω *ᵥ (x i - x j))‖ ^ 2 - ‖WithLp.toLp 2 (x i - x j)‖ ^ 2|} ≤
      (Fintype.card ι).choose 2 * δ := by
  classical
  set P : (n → 𝕜) → Ω → Prop := fun v ω => ε * ‖WithLp.toLp 2 v‖ ^ 2 ≤
    |‖WithLp.toLp 2 (S ω *ᵥ v)‖ ^ 2 - ‖WithLp.toLp 2 v‖ ^ 2| with hP
  have hPneg (v : n → 𝕜) (ω : Ω) : P (-v) ω ↔ P v ω := by
    simp only [hP, Matrix.mulVec_neg, WithLp.toLp_neg, norm_neg]
  let F : Sym2 ι → Set Ω := Sym2.lift ⟨fun i j => {ω | x i ≠ x j ∧ P (x i - x j) ω},
    fun i j => by
      ext ω
      simp only [Set.mem_ofPred_eq, ne_comm (a := x i), ← neg_sub (x i) (x j), hPneg]⟩
  have hF (i j : ι) : F s(i, j) = {ω | x i ≠ x j ∧ P (x i - x j) ω} := Sym2.lift_mk _ i j
  have e : {ω | ∃ i j, x i ≠ x j ∧ P (x i - x j) ω} = ⋃ z : {z : Sym2 ι // ¬ z.IsDiag}, F z := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, j, hne, hω⟩
      refine ⟨⟨s(i, j), fun hd => hne (by rw [Sym2.mk_isDiag_iff.1 hd])⟩, ?_⟩
      rw [hF]
      exact ⟨hne, hω⟩
    · rintro ⟨⟨z, hz⟩, hω⟩
      induction z using Sym2.ind with
      | _ i j =>
        rw [hF] at hω
        exact ⟨i, j, hω⟩
  have hle (z : {z : Sym2 ι // ¬ z.IsDiag}) : μ.real (F z) ≤ δ := by
    obtain ⟨z, hz⟩ := z
    induction z using Sym2.ind with
    | _ i j =>
      rw [hF]
      by_cases hne : x i = x j
      · simp only [hne, ne_eq, not_true_eq_false, false_and, Set.ofPred_false, measureReal_empty]
        exact hδ
      · have hs : {ω | x i ≠ x j ∧ P (x i - x j) ω} = {ω | P (x i - x j) ω} := by
          ext ω
          simp only [Set.mem_ofPred_eq, ne_eq, hne, not_false_eq_true, true_and]
        rw [hs]
        exact h.measure_abs_norm_mulVec_sq_sub_ge_le (sub_ne_zero.2 hne)
  change μ.real {ω | ∃ i j, x i ≠ x j ∧ P (x i - x j) ω} ≤ _
  rw [e]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  refine (Finset.sum_le_sum fun z _ => hle z).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Sym2.card_subtype_not_diag, nsmul_eq_mul]

/-- **Moments give tails**: for $\varepsilon > 0$ and $p > 0$, the JL moment property implies the
JL property with the same $\varepsilon$ and $\delta$ (Markov's inequality in $L^p$).
[Woodruff2014, §2.2]. -/
theorem HasJLMoment.hasJLProperty (h : HasJLMoment S ε δ p μ) (hε : 0 < ε) (hp : 0 < p) :
    HasJLProperty S ε δ μ := by
  intro x hx
  refine (measureReal_abs_ge_le_integral_rpow_div hp (h.integrable x hx) hε).trans ?_
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hε p), mul_comm]
  exact h.integral_le x hx

/-- The $p$-th moment of the distortion at any vector is integrable. -/
theorem HasJLMoment.integrable_abs_norm_mulVec_sq_sub_rpow (h : HasJLMoment S ε δ p μ)
    (hp : 0 < p) (x : n → 𝕜) :
    Integrable (fun ω => |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p) μ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sub_self, abs_zero,
      Real.zero_rpow hp.ne']
    exact integrable_zero _ _ _
  obtain ⟨u, hu, hSu⟩ := exists_unit_of_ne_zero (k := k) hx
  simp only [abs_sub_rpow_eq hSu]
  exact (h.integrable u hu).const_mul _

/-- The JL moment bound at any vector, for $p > 0$:
$\mathbb{E}\lvert \|\mathbf{S}\mathbf{x}\|^2 - \|\mathbf{x}\|^2 \rvert^p
\le \varepsilon^p \delta \|\mathbf{x}\|^{2p}$. -/
theorem HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hp : 0 < p) (x : n → 𝕜) :
    ∫ ω, |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ p ∂μ ≤
      ε ^ p * δ * ‖WithLp.toLp 2 x‖ ^ (2 * p) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp only [Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sub_self, abs_zero,
      Real.zero_rpow hp.ne', integral_zero, Real.zero_rpow (mul_pos two_pos hp).ne', mul_zero,
      le_refl]
  obtain ⟨u, hu, hSu⟩ := exists_unit_of_ne_zero (k := k) hx
  simp only [abs_sub_rpow_eq hSu]
  rw [integral_const_mul, mul_comm (ε ^ p * δ)]
  exact mul_le_mul_of_nonneg_left (h.integral_le u hu) (Real.rpow_nonneg (norm_nonneg _) _)

end NLAlib
