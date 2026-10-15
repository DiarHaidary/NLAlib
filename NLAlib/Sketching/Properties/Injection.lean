/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Probability.Tail
public import NLAlib.Sketching.Properties.LeastSquares
public import NLAlib.Sketching.Properties.Oblivious

/-!
# Tail bounds from a subspace injection

The two probabilistic consequences of an oblivious subspace injection in
[CamanoEpperlyMeyerTropp2025]: *OSIs respect orthogonality* (their Lemma 2.1), the step behind
the randomized range finder, Nyström and generalized Nyström bounds; and *sketch-and-solve with an
OSI* (their Theorem 2.7), for a vector and for a matrix right-hand side. Each is stated for a
random subspace injection of a fixed subspace together with isotropy, and again for an OSI.

Each event is the negation of the guarantee ($\{c < X\}$ for $X \le c$), so the degenerate cases
$\mathbf{B}\mathbf{Z}^{\mathsf{H}} = \mathbf{0}$,
$(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y} = \mathbf{0}$ need no hypothesis. The proofs
combine the deterministic bounds of `NLAlib.Sketching.Properties.LeastSquares` with Markov's
inequality for $\mathbb{E}\|\mathbf{S}\mathbf{M}\|_{\mathsf{F}}^2 = \|\mathbf{M}\|_{\mathsf{F}}^2$.
Design: `docs/design/Sketching-S1.md` §3.4.

## Main results

* `NLAlib.HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le`,
  `NLAlib.IsObliviousSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le`: CEMT Lemma 2.1.
* `NLAlib.HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le`: sketch-and-solve, CEMT
  Theorem 2.7.
* `NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`: its matrix form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k l n p q r : Type*} [Fintype k] [Fintype l] [Fintype n] [Fintype p] [Fintype q] [Fintype r]
  [DecidableEq n] {S : Ω → Matrix k n 𝕜} {Q : Matrix n p 𝕜} {A : Matrix n q 𝕜} {a δ t : ℝ}
  {d : ℕ}

/-! ### OSIs respect orthogonality -/

omit [DecidableEq n] in
/-- The common tail step: off the failure event $G^c$, the bad event forces $t m < M$ for a
nonnegative $M$ of mean $m$, which has probability at most $1 / t$ by Markov's inequality. -/
private theorem measureReal_le_add_one_div [IsFiniteMeasure μ] {G E : Set Ω}
    (hG : μ.real Gᶜ ≤ δ) {M : Ω → ℝ} (hM0 : ∀ ω, 0 ≤ M ω) (hM : Integrable M μ) {m : ℝ}
    (hm : ∫ ω, M ω ∂μ = m) (hm0 : m = 0 → ∀ ω, M ω = 0) (ht : 0 < t)
    (hE : ∀ᵐ ω ∂μ, ω ∈ G → ω ∈ E → t * m < M ω) : μ.real E ≤ δ + 1 / t := by
  have hae : ∀ᵐ ω ∂μ, ω ∈ E → ω ∈ Gᶜ ∪ {ω | t * m < M ω} := by
    filter_upwards [hE] with ω hω hωE
    by_cases hωG : ω ∈ G
    · exact Or.inr (hω hωG hωE)
    · exact Or.inl hωG
  have hF : μ.real {ω | t * m < M ω} ≤ 1 / t := by
    rcases eq_or_ne m 0 with h0 | h0
    · have he : {ω | t * m < M ω} = ∅ := by
        ext ω
        simp only [hm0 h0 ω, h0, mul_zero, lt_self_iff_false, Set.mem_ofPred_eq,
          Set.mem_empty_iff_false]
      rw [he, measureReal_empty]
      positivity
    · have hm' : 0 < m := lt_of_le_of_ne (hm ▸ integral_nonneg hM0) (Ne.symm h0)
      calc μ.real {ω | t * m < M ω} ≤ μ.real {ω | t * m ≤ M ω} :=
            measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => hω.le)
        _ ≤ (∫ ω, M ω ∂μ) / (t * m) :=
            measureReal_ge_le_integral_div (ae_of_all _ hM0) hM (mul_pos ht hm')
        _ = 1 / t := by
            rw [hm]
            field_simp
  calc μ.real E ≤ μ.real (Gᶜ ∪ {ω | t * m < M ω}) :=
        ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hae)
    _ ≤ μ.real Gᶜ + μ.real {ω | t * m < M ω} := measureReal_union_le _ _
    _ ≤ δ + 1 / t := add_le_add hG hF


/-- **OSIs respect orthogonality**: if $\mathbf{S}$ is isotropic and a subspace injection for
$\operatorname{range}\mathbf{Q}$ with constant $a > 0$ and failure probability $\delta$,
$\mathbf{Q}$ with orthonormal columns, then for $t > 0$
$$\bigl\|\mathbf{B}(\mathbf{S}\mathbf{Z})^{\mathsf{H}}
((\mathbf{S}\mathbf{Q})^{\mathsf{H}})^{+}\bigr\|_{\mathsf{F}}^2
\le \frac{t \|\mathbf{B}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}}^2}{a}$$
except with probability $\delta + 1 / t$.
[CamanoEpperlyMeyerTropp2025, Lemma 2.1]; there $\mathbf{Q}^{\mathsf{H}}\mathbf{Z} = \mathbf{0}$
(unused here), $\mathbf{Z}$ with orthonormal columns and $t = 20$. -/
theorem HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le [IsFiniteMeasure μ]
    [DecidableEq p] (h : HasSubspaceInjection S Q a δ μ) (hiso : IsIsotropicSketch S μ)
    (hQ : HasOrthonormalCols Q) (ha : 0 < a) (ht : 0 < t) (B : Matrix l r 𝕜)
    (Z : Matrix n r 𝕜) :
    μ.real {ω | t * frobNorm (B * Zᴴ) ^ 2 / a <
      frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t := by
  have hm : ∫ ω, frobNorm (S ω * (Z * Bᴴ)) ^ 2 ∂μ = frobNorm (B * Zᴴ) ^ 2 := by
    rw [hiso.integral_frobNorm_mul_sq, ← frobNorm_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  refine measureReal_le_add_one_div (G := {ω | IsSubspaceInjection (S ω) Q a}) h
    (fun ω => sq_nonneg _) (hiso.integrable_frobNorm_mul_sq _) hm (fun h0 ω => ?_) ht
    (ae_of_all _ fun ω hω hE => ?_)
  · have hZB : Z * Bᴴ = 0 := by
      rw [← Matrix.conjTranspose_conjTranspose (Z * Bᴴ), Matrix.conjTranspose_mul,
        Matrix.conjTranspose_conjTranspose,
        frobNorm_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), Matrix.conjTranspose_zero]
    rw [hZB, Matrix.mul_zero, frobNorm_zero, sq, mul_zero]
  · have hdet := (hω : IsSubspaceInjection (S ω) Q a).frobNorm_mul_pinv_sq_le hQ ha
      (B * (S ω * Z)ᴴ)
    have e : frobNorm (B * (S ω * Z)ᴴ) = frobNorm (S ω * (Z * Bᴴ)) := by
      rw [← frobNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        Matrix.mul_assoc]
    rw [e] at hdet
    have hE' : t * frobNorm (B * Zᴴ) ^ 2 / a <
        frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2 := hE
    exact (div_lt_div_iff_of_pos_right ha).1 (hE'.trans_le hdet)

/-- **OSIs respect orthogonality**, in CEMT's form: for an OSI for dimension $d \ge \lvert p \rvert$
with constant $a > 0$ and failure probability $\delta$, $\mathbf{Q}$ (with $p$ columns) and
$\mathbf{Z}$ with orthonormal columns, and $t > 0$,
$$\bigl\|\mathbf{B}(\mathbf{S}\mathbf{Z})^{\mathsf{H}}
((\mathbf{S}\mathbf{Q})^{\mathsf{H}})^{+}\bigr\|_{\mathsf{F}}^2
\le \frac{t \|\mathbf{B}\|_{\mathsf{F}}^2}{a}$$
except with probability $\delta + 1 / t$. [CamanoEpperlyMeyerTropp2025, Lemma 2.1]; there
$\mathbf{Q}^{\mathsf{H}}\mathbf{Z} = \mathbf{0}$ (unused here) and $t = 20$. -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le [IsFiniteMeasure μ]
    [DecidableEq p] [DecidableEq r] (h : IsObliviousSubspaceInjection S d a δ μ)
    (hQ : HasOrthonormalCols Q) (hpd : Fintype.card p ≤ d) {Z : Matrix n r 𝕜}
    (hZ : HasOrthonormalCols Z) (ha : 0 < a) (ht : 0 < t) (B : Matrix l r 𝕜) :
    μ.real {ω | t * frobNorm B ^ 2 / a <
      frobNorm (B * (S ω * Z)ᴴ * pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t := by
  have h' := (h.hasSubspaceInjection (hQ.rank_eq ▸ hpd)).measure_frobNorm_mul_pinv_sq_gt_le
    h.isotropic hQ ha ht B Z
  rwa [hZ.frobNorm_mul_conjTranspose_right] at h'

/-! ### Sketch-and-solve with an injection -/

/-- **Sketch-and-solve with an OSI**: if $\mathbf{S}$ is isotropic and a subspace injection for
$\operatorname{range}\mathbf{A}$ with constant $a > 0$ and failure probability $\delta$, and
$\mathbf{x}(\omega)$ is (almost surely) a minimizer of
$\|\mathbf{S}\mathbf{A}\mathbf{x} - \mathbf{S}\mathbf{y}\|$, then for $t > 0$
$$\|\mathbf{y} - \mathbf{A}\mathbf{x}\|^2
\le \Bigl(1 + \frac{t}{a}\Bigr) \|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{y}\|^2$$
except with probability $\delta + 1 / t$. [CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there for an
OSI, the minimum-norm solution and a fixed $t$, here a tail in $t$ for every minimizer.
Result: sketch-and-solve-ls -/
theorem HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le [IsFiniteMeasure μ]
    (h : HasSubspaceInjection S A a δ μ) (hiso : IsIsotropicSketch S μ) (ha : 0 < a)
    (ht : 0 < t) (y : n → 𝕜) {x : Ω → q → 𝕜}
    (hx : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x ω)) :
    μ.real {ω | (1 + t / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2} ≤ δ + 1 / t := by
  set w := (1 - rangeProjector A) *ᵥ y
  refine measureReal_le_add_one_div (G := {ω | IsSubspaceInjection (S ω) A a}) h
    (fun ω => sq_nonneg _) (hiso.integrable_norm_mulVec_sq w) (hiso.integral_norm_mulVec_sq w)
    (fun h0 ω => ?_) ht (hx.mono fun ω hxω hω hE => ?_)
  · have hw : w = 0 := by
      have := pow_eq_zero_iff two_ne_zero |>.1 h0
      rwa [norm_eq_zero, WithLp.toLp_eq_zero] at this
    rw [hw, Matrix.mulVec_zero, WithLp.toLp_zero, norm_zero, sq, mul_zero]
  · have hdet := (hω : IsSubspaceInjection (S ω) A a).norm_sub_mulVec_sq_le ha hxω
    have hE' : (1 + t / a) * ‖WithLp.toLp 2 w‖ ^ 2 < ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2 := hE
    have e : (1 + t / a) * ‖WithLp.toLp 2 w‖ ^ 2 =
        ‖WithLp.toLp 2 w‖ ^ 2 + t * ‖WithLp.toLp 2 w‖ ^ 2 / a := by ring
    refine (div_lt_div_iff_of_pos_right ha).1 ?_
    linarith

/-- **Sketch-and-solve with an OSI, matrix right-hand side**, for the minimum-norm output
$(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{Y}$: if $\mathbf{S}$ is isotropic and a subspace
injection for $\operatorname{range}\mathbf{A}$ with constant $a > 0$ and failure probability
$\delta$, then for $t > 0$
$$\|\mathbf{Y} - \mathbf{A}(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{Y}\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{t}{a}\Bigr)
\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{Y}\|_{\mathsf{F}}^2$$
except with probability $\delta + 1 / t$. [CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there a
vector right-hand side. -/
theorem HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le [IsFiniteMeasure μ]
    (h : HasSubspaceInjection S A a δ μ) (hiso : IsIsotropicSketch S μ) (ha : 0 < a)
    (ht : 0 < t) (Y : Matrix n r 𝕜) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector A) * Y) ^ 2 <
      frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2} ≤ δ + 1 / t := by
  set C := (1 - rangeProjector A) * Y
  refine measureReal_le_add_one_div (G := {ω | IsSubspaceInjection (S ω) A a}) h
    (fun ω => sq_nonneg _) (hiso.integrable_frobNorm_mul_sq C) (hiso.integral_frobNorm_mul_sq C)
    (fun h0 ω => ?_) ht (ae_of_all _ fun ω hω hE => ?_)
  · rw [frobNorm_eq_zero_iff.1 (pow_eq_zero_iff two_ne_zero |>.1 h0), Matrix.mul_zero,
      frobNorm_zero, sq, mul_zero]
  · have hdet := (hω : IsSubspaceInjection (S ω) A a).frobNorm_sub_mul_pinv_mul_sq_le ha Y
    have hE' : (1 + t / a) * frobNorm C ^ 2 <
        frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2 := hE
    have e : (1 + t / a) * frobNorm C ^ 2 = frobNorm C ^ 2 + t * frobNorm C ^ 2 / a := by ring
    refine (div_lt_div_iff_of_pos_right ha).1 ?_
    linarith

/-- **Sketch-and-solve with an OSI** for dimension $d \ge \operatorname{rank}\mathbf{A}$: the
bound of `NLAlib.HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.7]. -/
theorem IsObliviousSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le [IsFiniteMeasure μ]
    (h : IsObliviousSubspaceInjection S d a δ μ) (hA : A.rank ≤ d) (ha : 0 < a) (ht : 0 < t)
    (y : n → 𝕜) {x : Ω → q → 𝕜}
    (hx : ∀ᵐ ω ∂μ, IsLeastSquaresSolution (S ω * A) (S ω *ᵥ y) (x ω)) :
    μ.real {ω | (1 + t / a) * ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ y)‖ ^ 2 <
      ‖WithLp.toLp 2 (y - A *ᵥ x ω)‖ ^ 2} ≤ δ + 1 / t := by
  exact (h.hasSubspaceInjection hA).measure_norm_sub_mulVec_sq_gt_le h.isotropic ha ht y hx

/-- **Sketch-and-solve with an OSI, matrix right-hand side**, for dimension
$d \ge \operatorname{rank}\mathbf{A}$: the bound of
`NLAlib.HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`.
[CamanoEpperlyMeyerTropp2025, Theorem 2.7]; there a vector right-hand side. -/
theorem IsObliviousSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le
    [IsFiniteMeasure μ] (h : IsObliviousSubspaceInjection S d a δ μ) (hA : A.rank ≤ d)
    (ha : 0 < a) (ht : 0 < t) (Y : Matrix n r 𝕜) :
    μ.real {ω | (1 + t / a) * frobNorm ((1 - rangeProjector A) * Y) ^ 2 <
      frobNorm (Y - A * (pinv (S ω * A) * (S ω * Y))) ^ 2} ≤ δ + 1 / t := by
  exact (h.hasSubspaceInjection hA).measure_frobNorm_sub_mul_pinv_mul_sq_gt_le h.isotropic ha ht
    Y

end NLAlib
