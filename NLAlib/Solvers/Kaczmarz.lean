/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.Richardson
public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Probability.Distributions.Sampling
public import NLAlib.Solvers.SketchAndProject

/-!
# Randomized Kaczmarz

`NLAlib.kaczmarzIterate A ι b x₀ q` is the sketch-and-project iterate whose $q$-th sketch selects
row $\iota_q$ of $\mathbf{A}$: each step projects the iterate orthogonally onto the hyperplane
$\{\mathbf{y} : (\mathbf{A}\mathbf{y})_{\iota_q} = b_{\iota_q}\}$, and the familiar row-action
update is `NLAlib.kaczmarzIterate_succ`. Randomized Kaczmarz draws the rows independently with
the squared-row-norm probabilities $p_i = \|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$
(`NLAlib.rowNormSqDistribution`), written as the i.i.d.-sequence hypothesis
`HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ`.

The rate is $1 - (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^{-2}$, with the Frobenius
pseudo-condition number `NLAlib.frobPseudoConditionNumber`, and no rank assumption is needed.
For any right-hand side the expected squared error about any reference point
$\mathbf{x}_\star$ with $\mathbf{x}_\star - \mathbf{x}_0$ in the row space contracts at this rate
up to the horizon $\|\mathbf{A}^{+}\|_2^2\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2$; about the
least-squares solution nearest $\mathbf{x}_0$ the horizon is the optimal residual. For consistent
systems this is Strohmer and Vershynin's theorem. Through sketch-and-project, any row
probabilities give the rate of the least eigenvalue of the expected row projector on the row space;
and the mean iterate is Landweber's iteration with step $\|\mathbf{A}\|_{\mathsf{F}}^{-2}$.
[StrohmerVershynin2009]; [ZouziasFreris2013]; [GowerRichtarik2015]; [LeventhalLewis2010];
[Needell2010]; [MaNeedellRamdas2015]. Block Kaczmarz with row pavings [NeedellTropp2014] and the
randomized extended Kaczmarz method are not here yet.
Design: `docs/design/Regression-Kaczmarz.md`.

## Main definitions

* `NLAlib.kaczmarzIterate`: the Kaczmarz iterate for a sequence of rows.

## Main results

* `NLAlib.kaczmarzIterate_succ`: the row-action formula.
* `NLAlib.integral_norm_sub_kaczmarzIterate_succ_sq_le`: the one-step bound in expectation.
* `NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_add`: randomized Kaczmarz for any right-hand
  side.
* `NLAlib.integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le`: convergence to the
  least-squares solution nearest the start, up to the horizon.
* `NLAlib.integral_norm_sub_kaczmarzIterate_sq_le`: Strohmer and Vershynin's theorem, any rank.
* `NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_of_hasLaw_samplingMeasure`: any row
  probabilities.
* `NLAlib.integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose`,
  `NLAlib.integral_kaczmarzIterate`: the mean iterate is Landweber's iteration.
* `NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_of_mul_log_le`,
  `NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le`:
  the iteration counts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder NNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m]

/-! ### The iterate and the row-action formula -/

/-- The **Kaczmarz iterate** for $\mathbf{A} \in \Bbbk^{m \times n}$ with row choices
$\iota_0, \iota_1, \ldots$: the sketch-and-project iterate
$$\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q) :=
\mathsf{sketchAndProjectIterate}(\mathbf{A}, \mathbf{S}, \mathbf{b}, \mathbf{x}_0, q)$$
whose $q$-th sketch $\mathbf{S}_q$ selects row $\iota_q$, so that each step is the orthogonal
projection onto the hyperplane $\{\mathbf{y} : (\mathbf{A}\mathbf{y})_{\iota_q} = b_{\iota_q}\}$.
The row-action formula
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \frac{b_{\iota_q} - (\mathbf{A}\mathbf{x}_q)_{\iota_q}}
{\|\mathbf{a}_{\iota_q}\|^2}\,\overline{\mathbf{a}_{\iota_q}}\,,$$
with $\mathbf{a}_i$ the rows of $\mathbf{A}$, is `NLAlib.kaczmarzIterate_succ`; a zero row leaves
the iterate unchanged. Randomized Kaczmarz draws the rows independently with probabilities
`NLAlib.rowNormSqDistribution A`. [StrohmerVershynin2009, Algorithm 1];
[MaNeedellRamdas2015, (2.1)], the complex update; [GowerRichtarik2015, §3.3], as
sketch-and-project. -/
noncomputable def kaczmarzIterate (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) :
    ℕ → n → 𝕜 :=
  sketchAndProjectIterate A (fun q => (selectionMatrix fun _ : Unit => ι q)ᴴ) b x₀

section Deterministic

variable {A : Matrix m n 𝕜} {b : m → 𝕜} {x₀ : n → 𝕜}

omit [Fintype n] in
/-- The row-selection sketch times $\mathbf{A}$ is the selected row. -/
private lemma conjTranspose_selectionMatrix_unit_mul (A : Matrix m n 𝕜) (i : m) :
    (selectionMatrix fun _ : Unit => i)ᴴ * A = Matrix.replicateRow Unit (A i) := by
  rw [conjTranspose_selectionMatrix_mul]
  rfl

omit [DecidableEq m] in
/-- The pseudoinverse of a row applied to a scalar. -/
private lemma pinv_replicateRow_mulVec (a : n → 𝕜) (w : Unit → 𝕜) :
    pinv (Matrix.replicateRow Unit a) *ᵥ w =
      (w () / ((‖WithLp.toLp 2 a‖ ^ 2 : ℝ) : 𝕜)) • star a := by
  rw [pinv_replicateRow, Matrix.smul_mulVec]
  ext j
  simp only [Matrix.mulVec, dotProduct, Matrix.replicateCol_apply, Finset.univ_unique,
    Finset.sum_singleton, Pi.smul_apply, Pi.star_apply, smul_eq_mul, RCLike.real_smul_eq_coe_mul]
  push_cast
  ring

omit [DecidableEq m] in
/-- The squared norm of a Kaczmarz correction. -/
private lemma norm_toLp_div_smul_star_sq (a : n → 𝕜) (s : 𝕜) :
    ‖WithLp.toLp 2 ((s / ((‖WithLp.toLp 2 a‖ ^ 2 : ℝ) : 𝕜)) • star a)‖ ^ 2 =
      ‖s‖ ^ 2 / ‖WithLp.toLp 2 a‖ ^ 2 := by
  rw [WithLp.toLp_smul, norm_smul, EuclideanSpace.norm_toLp_star, norm_div, RCLike.norm_ofReal,
    abs_of_nonneg (sq_nonneg _)]
  rcases eq_or_ne ‖WithLp.toLp 2 a‖ 0 with h | h
  · rw [h]
    simp
  · field_simp

/-- One Kaczmarz step from any point. -/
private lemma sketchAndProject_conjTranspose_selectionMatrix (A : Matrix m n 𝕜) (i : m)
    (b : m → 𝕜) (x : n → 𝕜) :
    sketchAndProject A (selectionMatrix fun _ : Unit => i)ᴴ b x =
      x + ((b i - (A *ᵥ x) i) / ((‖WithLp.toLp 2 (A i)‖ ^ 2 : ℝ) : 𝕜)) • star (A i) := by
  rw [sketchAndProject, conjTranspose_selectionMatrix_unit_mul,
    conjTranspose_selectionMatrix_mulVec, pinv_replicateRow_mulVec]
  rfl

/-- Pythagoras for one Kaczmarz step from any point. -/
private lemma norm_sub_sketchAndProject_conjTranspose_selectionMatrix_sq (A : Matrix m n 𝕜)
    (i : m) (b : m → 𝕜) (x xs : n → 𝕜) :
    ‖WithLp.toLp 2 (xs - sketchAndProject A (selectionMatrix fun _ : Unit => i)ᴴ b x)‖ ^ 2 =
      ‖WithLp.toLp 2 (xs - x)‖ ^ 2 -
        ‖(A *ᵥ (xs - x)) i‖ ^ 2 / ‖WithLp.toLp 2 (A i)‖ ^ 2 +
        ‖(b - A *ᵥ xs) i‖ ^ 2 / ‖WithLp.toLp 2 (A i)‖ ^ 2 := by
  have hrow := conjTranspose_selectionMatrix_unit_mul A i
  have hP : rangeProjector ((selectionMatrix fun _ : Unit => i)ᴴ * A)ᴴ *ᵥ (xs - x) =
      ((A *ᵥ (xs - x)) i / ((‖WithLp.toLp 2 (A i)‖ ^ 2 : ℝ) : 𝕜)) • star (A i) := by
    rw [← pinv_mul, ← Matrix.mulVec_mulVec, hrow, Matrix.replicateRow_mulVec_eq_const,
      pinv_replicateRow_mulVec]
    rfl
  have hr : pinv ((selectionMatrix fun _ : Unit => i)ᴴ * A) *ᵥ
      ((selectionMatrix fun _ : Unit => i)ᴴ *ᵥ (b - A *ᵥ xs)) =
      ((b - A *ᵥ xs) i / ((‖WithLp.toLp 2 (A i)‖ ^ 2 : ℝ) : 𝕜)) • star (A i) := by
    rw [hrow, conjTranspose_selectionMatrix_mulVec, pinv_replicateRow_mulVec]
    rfl
  rw [norm_sub_sketchAndProject_sq, hP, hr, norm_toLp_div_smul_star_sq,
    norm_toLp_div_smul_star_sq]

/-- The zeroth Kaczmarz iterate is the start:
$\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, 0) = \mathbf{x}_0$. -/
@[simp]
theorem kaczmarzIterate_zero (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) :
    kaczmarzIterate A ι b x₀ 0 = x₀ :=
  rfl

/-- **The row-action formula** of the Kaczmarz iterate: with $\mathbf{a}_i$ the rows of
$\mathbf{A}$ and $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)$,
$$\mathbf{x}_{q+1} = \mathbf{x}_q + \frac{b_{\iota_q} - (\mathbf{A}\mathbf{x}_q)_{\iota_q}}
{\|\mathbf{a}_{\iota_q}\|^2}\,\overline{\mathbf{a}_{\iota_q}}\,,$$
and $\mathbf{x}_{q+1} = \mathbf{x}_q$ when $\mathbf{a}_{\iota_q} = \mathbf{0}$ (division by zero is
zero). [StrohmerVershynin2009, Algorithm 1]; [MaNeedellRamdas2015, (2.1)]. -/
theorem kaczmarzIterate_succ (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    kaczmarzIterate A ι b x₀ (q + 1) =
      kaczmarzIterate A ι b x₀ q +
        ((b (ι q) - (A *ᵥ kaczmarzIterate A ι b x₀ q) (ι q)) /
          ((‖WithLp.toLp 2 (A (ι q))‖ ^ 2 : ℝ) : 𝕜)) • star (A (ι q)) := by
  exact sketchAndProject_conjTranspose_selectionMatrix A (ι q) b _

/-- **Each step solves its equation**: if row $\iota_q$ of $\mathbf{A}$ is nonzero, the iterate
$\mathbf{x}_{q+1} = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q + 1)$
satisfies $(\mathbf{A}\mathbf{x}_{q+1})_{\iota_q} = b_{\iota_q}$.
[MaNeedellRamdas2015, (2.2)]. -/
theorem mulVec_kaczmarzIterate_succ_apply {ι : ℕ → m} {q : ℕ} (hA : A (ι q) ≠ 0) :
    (A *ᵥ kaczmarzIterate A ι b x₀ (q + 1)) (ι q) = b (ι q) := by
  have h1 : (A *ᵥ star (A (ι q))) (ι q) = ((‖WithLp.toLp 2 (A (ι q))‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, dotProduct_comm]
    rfl
  have h2 : ((‖WithLp.toLp 2 (A (ι q))‖ ^ 2 : ℝ) : 𝕜) ≠ 0 := by
    rw [RCLike.ofReal_ne_zero]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (by rwa [Ne, WithLp.toLp_eq_zero]))
  rw [kaczmarzIterate_succ, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, h1, div_mul_cancel₀ _ h2, add_sub_cancel]

/-- **The one-step identity**, for any reference point $\mathbf{x}_\star$ and every row: with
$\mathbf{a}_i$ the rows of $\mathbf{A}$ and $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A},
\iota, \mathbf{b}, \mathbf{x}_0, q)$,
$$\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 = \|\mathbf{x}_\star - \mathbf{x}_q\|^2 -
\frac{\lvert(\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q))_{\iota_q}\rvert^2}
{\|\mathbf{a}_{\iota_q}\|^2} + \frac{\lvert(\mathbf{b} -
\mathbf{A}\mathbf{x}_\star)_{\iota_q}\rvert^2}{\|\mathbf{a}_{\iota_q}\|^2}\,;$$
for a zero row both fractions are $0$ and the step is the identity.
[StrohmerVershynin2009, proof of Theorem 2], there for a consistent system. -/
theorem norm_sub_kaczmarzIterate_succ_sq (ι : ℕ → m) (xs : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (xs - kaczmarzIterate A ι b x₀ (q + 1))‖ ^ 2 =
      ‖WithLp.toLp 2 (xs - kaczmarzIterate A ι b x₀ q)‖ ^ 2 -
        ‖(A *ᵥ (xs - kaczmarzIterate A ι b x₀ q)) (ι q)‖ ^ 2 / ‖WithLp.toLp 2 (A (ι q))‖ ^ 2 +
        ‖(b - A *ᵥ xs) (ι q)‖ ^ 2 / ‖WithLp.toLp 2 (A (ι q))‖ ^ 2 := by
  exact norm_sub_sketchAndProject_conjTranspose_selectionMatrix_sq A (ι q) b _ xs

/-- **The Kaczmarz iterate stays in the row space through the start**: for every sequence of
rows, $\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q) - \mathbf{x}_0
\in \operatorname{range}\mathbf{A}^{\mathsf{H}}$. -/
theorem kaczmarzIterate_sub_mem_range (A : Matrix m n 𝕜) (ι : ℕ → m) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) : kaczmarzIterate A ι b x₀ q - x₀ ∈ LinearMap.range Aᴴ.mulVecLin := by
  exact sketchAndProjectIterate_sub_mem_range A _ b x₀ q

end Deterministic

/-! ### Squared-row-norm sampling -/

section Random

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [MeasurableSpace m]
  [MeasurableSingletonClass m] {A : Matrix m n 𝕜} {b : m → 𝕜} {ι : Ω → ℕ → m} {x₀ : n → 𝕜}

/-- The Kaczmarz iterate is a measurable function of the row sequence. -/
private lemma measurable_kaczmarzIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    Measurable fun ι : ℕ → m => kaczmarzIterate A ι b x₀ q :=
  (measurable_sketchAndProjectIterate A b x₀ q).comp
    (measurable_pi_lambda _ fun j => (measurable_of_countable fun i : m =>
      (selectionMatrix fun _ : Unit => i : Matrix m Unit 𝕜)ᴴ).comp (measurable_pi_apply j))

omit [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- The $q$-th Kaczmarz iterate depends only on the first $q$ rows. -/
private lemma dependsOn_kaczmarzIterate (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) :
    DependsOn (fun ι : ℕ → m => kaczmarzIterate A ι b x₀ q) (Set.Iio q) := by
  intro ι ι' h
  simp only [kaczmarzIterate]
  exact dependsOn_sketchAndProjectIterate A b x₀ q fun j hj => by simp only [h j hj]

omit [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- A function of the $q$-th Kaczmarz iterate is bounded: the iterate takes finitely many
values. -/
private lemma exists_forall_norm_le_kaczmarzIterate {E : Type*} [NormedAddCommGroup E]
    (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) (f : (n → 𝕜) → E) :
    ∃ R, ∀ ι : ℕ → m, ‖f (kaczmarzIterate A ι b x₀ q)‖ ≤ R := by
  rcases isEmpty_or_nonempty m with hm | ⟨⟨i₀⟩⟩
  · exact ⟨0, fun ι => (IsEmpty.false (ι 0)).elim⟩
  obtain ⟨e, he⟩ : ∃ e : (Fin q → m) → ℕ → m, ∀ s (j : ℕ) (h : j < q), e s j = s ⟨j, h⟩ :=
    ⟨fun s j => if h : j < q then s ⟨j, h⟩ else i₀, fun s j h => dif_pos h⟩
  refine ⟨∑ s, ‖f (kaczmarzIterate A (e s) b x₀ q)‖, fun ι => ?_⟩
  have h : kaczmarzIterate A ι b x₀ q = kaczmarzIterate A (e fun j => ι j) b x₀ q :=
    dependsOn_kaczmarzIterate A b x₀ q fun j hj => by
      rw [he _ j (Set.mem_Iio.mp hj)]
  calc ‖f (kaczmarzIterate A ι b x₀ q)‖ = ‖f (kaczmarzIterate A (e fun j => ι j) b x₀ q)‖ := by
        rw [h]
    _ ≤ _ := Finset.single_le_sum (f := fun s => ‖f (kaczmarzIterate A (e s) b x₀ q)‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ _)

/-- A continuous function of the Kaczmarz iterate is integrable. -/
private lemma integrable_comp_kaczmarzIterate {E : Type*} [NormedAddCommGroup E]
    [IsFiniteMeasure μ] (hι : AEMeasurable ι μ) (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜)
    (q : ℕ) {f : (n → 𝕜) → E} (hf : Continuous f) :
    Integrable (fun ω => f (kaczmarzIterate A (ι ω) b x₀ q)) μ := by
  obtain ⟨R, hR⟩ := exists_forall_norm_le_kaczmarzIterate A b x₀ q f
  exact Integrable.of_bound (hf.comp_aestronglyMeasurable
    ((measurable_kaczmarzIterate A b x₀ q).comp_aemeasurable hι).aestronglyMeasurable) R
    (ae_of_all _ fun ω => hR (ι ω))

/-- Conditioning on the past for the Kaczmarz iterate. -/
private lemma integral_comp_kaczmarzIterate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {p : m → ℝ≥0}
    (hp : ∑ i, p i = 1) (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure p) μ)
    (A : Matrix m n 𝕜) (b : m → 𝕜) (x₀ : n → 𝕜) (q : ℕ) {f : (n → 𝕜) × m → E}
    (hf : ∀ i, Continuous fun x => f (x, i)) :
    ∫ ω, f (kaczmarzIterate A (ι ω) b x₀ q, ι ω q) ∂μ =
      ∫ ω, ∫ i, f (kaczmarzIterate A (ι ω) b x₀ q, i) ∂samplingMeasure p ∂μ := by
  have := isProbabilityMeasure_samplingMeasure p hp
  have : IsProbabilityMeasure μ := hι.isProbabilityMeasure
  have hF := measurable_kaczmarzIterate A b x₀ q
  have hFS : AEMeasurable (fun ω => kaczmarzIterate A (ι ω) b x₀ q) μ :=
    hF.comp_aemeasurable hι.aemeasurable
  have hg : Continuous fun x => ∑ i, ‖f (x, i)‖ := continuous_finsetSum _ fun i _ => (hf i).norm
  have hgi : Integrable (fun x => ∑ i, ‖f (x, i)‖)
      (μ.map fun ω => kaczmarzIterate A (ι ω) b x₀ q) :=
    (integrable_map_measure hg.aestronglyMeasurable hFS).mpr
      (integrable_comp_kaczmarzIterate hι.aemeasurable A b x₀ q hg)
  have hfm : Measurable f := measurable_from_prod_countable_left fun i => (hf i).measurable
  exact hι.integral_comp_eq_integral_integral_of_dependsOn hF (dependsOn_kaczmarzIterate A b x₀ q)
    ((hgi.comp_fst _).mono' hfm.aestronglyMeasurable (ae_of_all _ fun y =>
      Finset.single_le_sum (f := fun i => ‖f (y.1, i)‖) (fun _ _ => norm_nonneg _)
        (Finset.mem_univ y.2)))

omit [DecidableEq m] [MeasurableSingletonClass m] in
/-- For $\mathbf{A} = \mathbf{0}$ the squared-row-norm law is zero, so is the sample space. -/
private lemma eq_zero_of_hasLaw_rowNormSqDistribution_zero
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ =>
      samplingMeasure (rowNormSqDistribution (0 : Matrix m n 𝕜))) μ) : μ = 0 := by
  have h0 : samplingMeasure (rowNormSqDistribution (0 : Matrix m n 𝕜)) = 0 := by
    simp [samplingMeasure, rowNormSqDistribution]
  have hpi : Measure.infinitePi
      (fun _ : ℕ => samplingMeasure (rowNormSqDistribution (0 : Matrix m n 𝕜))) = 0 := by
    rw [Measure.infinitePi, dif_neg]
    intro h
    have h1 := (h 0).measure_univ
    rw [h0] at h1
    simp at h1
  have h := hι.map_eq
  rw [hpi] at h
  exact (Measure.map_eq_zero_iff hι.aemeasurable).mp h

omit [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- A squared-row-norm weight times a quotient by the squared row norm. -/
private lemma coe_rowNormSqDistribution_mul_div (A : Matrix m n 𝕜) (i : m) {t : ℝ}
    (ht : A i = 0 → t = 0) :
    (rowNormSqDistribution A i : ℝ) * (t / ‖WithLp.toLp 2 (A i)‖ ^ 2) = t / frobNorm A ^ 2 := by
  rw [coe_rowNormSqDistribution]
  by_cases h : A i = 0
  · rw [ht h]
    simp
  · have : ‖WithLp.toLp 2 (A i)‖ ≠ 0 := norm_ne_zero_iff.mpr (by rwa [Ne, WithLp.toLp_eq_zero])
    field_simp

omit [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- The same weight is at most the quotient by the squared Frobenius norm. -/
private lemma coe_rowNormSqDistribution_mul_div_le (A : Matrix m n 𝕜) (i : m) {t : ℝ}
    (ht : 0 ≤ t) :
    (rowNormSqDistribution A i : ℝ) * (t / ‖WithLp.toLp 2 (A i)‖ ^ 2) ≤ t / frobNorm A ^ 2 := by
  by_cases h : A i = 0
  · rw [coe_rowNormSqDistribution, h, WithLp.toLp_zero, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, div_zero,
      mul_zero]
    positivity
  · exact (coe_rowNormSqDistribution_mul_div A i fun h' => absurd h' h).le

omit [Fintype m] [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- A zero row gives a zero entry of every product. -/
private lemma mulVec_apply_eq_zero_of_row_eq_zero {A : Matrix m n 𝕜} {i : m} (h : A i = 0)
    (v : n → 𝕜) : (A *ᵥ v) i = 0 := by
  simp [Matrix.mulVec, dotProduct, fun j => congrFun h j]

/-- The expected squared error after one Kaczmarz step from a fixed point. -/
private lemma integral_norm_sub_sketchAndProject_conjTranspose_selectionMatrix_sq
    (hA : A ≠ 0) (x xs : n → 𝕜) :
    ∫ i, ‖WithLp.toLp 2 (xs - sketchAndProject A (selectionMatrix fun _ : Unit => i)ᴴ b x)‖ ^ 2
        ∂samplingMeasure (rowNormSqDistribution A) =
      ‖WithLp.toLp 2 (xs - x)‖ ^ 2 - ‖WithLp.toLp 2 (A *ᵥ (xs - x))‖ ^ 2 / frobNorm A ^ 2 +
        ∑ i, (rowNormSqDistribution A i : ℝ) *
          (‖(b - A *ᵥ xs) i‖ ^ 2 / ‖WithLp.toLp 2 (A i)‖ ^ 2) := by
  have hp : ∑ i, (rowNormSqDistribution A i : ℝ) = 1 := by
    rw [← NNReal.coe_sum, sum_rowNormSqDistribution hA, NNReal.coe_one]
  have hu : ∑ i, (rowNormSqDistribution A i : ℝ) *
      (‖(A *ᵥ (xs - x)) i‖ ^ 2 / ‖WithLp.toLp 2 (A i)‖ ^ 2) =
      ‖WithLp.toLp 2 (A *ᵥ (xs - x))‖ ^ 2 / frobNorm A ^ 2 := by
    rw [Finset.sum_congr rfl fun i _ => coe_rowNormSqDistribution_mul_div A i fun h => by
      rw [mulVec_apply_eq_zero_of_row_eq_zero h, norm_zero, zero_pow two_ne_zero],
      ← Finset.sum_div, EuclideanSpace.norm_sq_eq]
  rw [integral_samplingMeasure]
  simp only [norm_sub_sketchAndProject_conjTranspose_selectionMatrix_sq, smul_eq_mul, mul_add,
    mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, hu]

omit [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- A Kaczmarz step is continuous in the point. -/
private lemma continuous_sketchAndProject_conjTranspose_selectionMatrix (A : Matrix m n 𝕜)
    (b : m → 𝕜) (i : m) :
    Continuous fun x : n → 𝕜 => sketchAndProject A (selectionMatrix fun _ : Unit => i)ᴴ b x :=
  continuous_id.add (continuous_const.matrix_mulVec (continuous_const.matrix_mulVec
    (continuous_const.sub (continuous_const.matrix_mulVec continuous_id))))

/-- The expected squared error after one Kaczmarz step, for $\mathbf{A} \ne \mathbf{0}$. -/
private lemma integral_norm_sub_kaczmarzIterate_succ_sq_eq (hA : A ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (xs : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (q + 1))‖ ^ 2 ∂μ =
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ -
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 +
        ∑ i, (rowNormSqDistribution A i : ℝ) *
          (‖(b - A *ᵥ xs) i‖ ^ 2 / ‖WithLp.toLp 2 (A i)‖ ^ 2) := by
  have hp := sum_rowNormSqDistribution hA
  have := isProbabilityMeasure_samplingMeasure _ hp
  have : IsProbabilityMeasure μ := hι.isProbabilityMeasure
  have hN : Continuous fun v : n → 𝕜 => ‖WithLp.toLp 2 v‖ ^ 2 :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 _)).pow 2
  have hc1 : Continuous fun x : n → 𝕜 => ‖WithLp.toLp 2 (xs - x)‖ ^ 2 :=
    hN.comp (continuous_const.sub continuous_id)
  have hNm : Continuous fun v : m → 𝕜 => ‖WithLp.toLp 2 v‖ ^ 2 :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 _)).pow 2
  have hc2 : Continuous fun x : n → 𝕜 => ‖WithLp.toLp 2 (A *ᵥ (xs - x))‖ ^ 2 :=
    hNm.comp ((Matrix.mulVecLin A).continuous_of_finiteDimensional.comp
      (continuous_const.sub continuous_id))
  have hI1 := integrable_comp_kaczmarzIterate hι.aemeasurable A b x₀ q hc1
  have hI2 := integrable_comp_kaczmarzIterate hι.aemeasurable A b x₀ q hc2
  have hfub := integral_comp_kaczmarzIterate hp hι A b x₀ q
    (f := fun y => ‖WithLp.toLp 2
      (xs - sketchAndProject A (selectionMatrix fun _ : Unit => y.2)ᴴ b y.1)‖ ^ 2)
    fun i => hN.comp (continuous_const.sub
      (continuous_sketchAndProject_conjTranspose_selectionMatrix A b i))
  simp only [integral_norm_sub_sketchAndProject_conjTranspose_selectionMatrix_sq hA] at hfub
  change ∫ ω, ‖WithLp.toLp 2 (xs - sketchAndProject A (selectionMatrix fun _ : Unit => ι ω q)ᴴ b
    (kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ = _
  have hI12 : Integrable (fun ω => ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 -
      ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 / frobNorm A ^ 2) μ :=
    hI1.sub (hI2.div_const _)
  rw [hfub, integral_add hI12 (integrable_const _),
    integral_sub hI1 (hI2.div_const _), integral_div, integral_const, probReal_univ, one_smul]

omit [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- The Kaczmarz rate is nonnegative for $\mathbf{A} \ne \mathbf{0}$. -/
private lemma zero_le_one_sub_one_div_frobPseudoConditionNumber_sq {A : Matrix m n 𝕜}
    (hA : A ≠ 0) : 0 ≤ 1 - 1 / frobPseudoConditionNumber A ^ 2 := by
  have hκ := one_le_frobPseudoConditionNumber hA
  rw [sub_nonneg, div_le_one (by nlinarith)]
  nlinarith

omit [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m] in
/-- The Kaczmarz rate to the power $q \ge \kappa^2\log(1/\varepsilon)$ is at most $\varepsilon$. -/
private lemma one_sub_one_div_frobPseudoConditionNumber_sq_pow_le {A : Matrix m n 𝕜}
    (hA : A ≠ 0) {ε : ℝ} (hε : 0 < ε) {q : ℕ}
    (hq : frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε) ≤ q) :
    (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q ≤ ε := by
  have hκ := one_le_frobPseudoConditionNumber hA
  have hκ2 : 0 < frobPseudoConditionNumber A ^ 2 := by nlinarith
  calc _ ≤ Real.exp (-(1 / frobPseudoConditionNumber A ^ 2)) ^ q :=
        pow_le_pow_left₀ (zero_le_one_sub_one_div_frobPseudoConditionNumber_sq hA)
          (by linarith [Real.add_one_le_exp (-(1 / frobPseudoConditionNumber A ^ 2))]) q
    _ = Real.exp (-(q / frobPseudoConditionNumber A ^ 2)) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
    _ ≤ Real.exp (Real.log ε) := by
        refine Real.exp_le_exp.mpr ?_
        have h1 : Real.log (1 / ε) ≤ q / frobPseudoConditionNumber A ^ 2 := by
          rw [le_div_iff₀ hκ2]
          linarith
        rw [one_div, Real.log_inv] at h1
        linarith
    _ = ε := Real.exp_log hε

/-- **The one-step bound in expectation**, for any right-hand side and reference point: with rows
drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$), the
iterates $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q)$
satisfy, for every $\mathbf{x}_\star$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 \le \mathbb{E}\|\mathbf{x}_\star -
\mathbf{x}_q\|^2 - \frac{\mathbb{E}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2} + \frac{\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2}\,.$$
The gap is the residual on the zero rows, which are never chosen; with no zero row it is an
identity (`NLAlib.integral_norm_sub_kaczmarzIterate_succ_sq`).
[StrohmerVershynin2009, proof of Theorem 2]; [ZouziasFreris2013, Theorem 7, (5)], there after
the singular-value bound. -/
theorem integral_norm_sub_kaczmarzIterate_succ_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (xs : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (q + 1))‖ ^ 2 ∂μ ≤
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ -
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 +
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2 := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [eq_zero_of_hasLaw_rowNormSqDistribution_zero hι]
    simp [frobNorm_zero]
  rw [integral_norm_sub_kaczmarzIterate_succ_sq_eq hA hι xs q]
  have hc : ∑ i, (rowNormSqDistribution A i : ℝ) *
      (‖(b - A *ᵥ xs) i‖ ^ 2 / ‖WithLp.toLp 2 (A i)‖ ^ 2) ≤
      ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2 := by
    calc _ ≤ ∑ i, ‖(b - A *ᵥ xs) i‖ ^ 2 / frobNorm A ^ 2 :=
          Finset.sum_le_sum fun i _ => coe_rowNormSqDistribution_mul_div_le A i (sq_nonneg _)
      _ = _ := by rw [← Finset.sum_div, EuclideanSpace.norm_sq_eq]
  linarith

/-- **The one-step identity in expectation**, when no row of $\mathbf{A}$ is zero: with rows
drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i \ne \mathbf{0}$ the rows of
$\mathbf{A}$), the iterates $\mathbf{x}_q = \mathsf{kaczmarzIterate}(\mathbf{A}, \iota,
\mathbf{b}, \mathbf{x}_0, q)$ satisfy, for every $\mathbf{x}_\star$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathbf{x}_{q+1}\|^2 = \mathbb{E}\|\mathbf{x}_\star -
\mathbf{x}_q\|^2 - \frac{\mathbb{E}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2} + \frac{\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2}
{\|\mathbf{A}\|_{\mathsf{F}}^2}\,.$$
Without the hypothesis it fails: for
$\mathbf{A} = \begin{bmatrix} 1 \\ 0 \end{bmatrix}$, $\mathbf{b} = (0, 1)$ and
$\mathbf{x}_0 = \mathbf{x}_\star = \mathbf{0}$ the left side is $0$ and the right side $1$.
[StrohmerVershynin2009, proof of Theorem 2], there for a consistent system. -/
theorem integral_norm_sub_kaczmarzIterate_succ_sq (hA : ∀ i, A i ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (xs : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (q + 1))‖ ^ 2 ∂μ =
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ -
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ q))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 +
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2 := by
  rcases eq_or_ne A 0 with rfl | hA0
  · rw [eq_zero_of_hasLaw_rowNormSqDistribution_zero hι]
    simp [frobNorm_zero]
  rw [integral_norm_sub_kaczmarzIterate_succ_sq_eq hA0 hι xs q,
    Finset.sum_congr rfl fun i _ => coe_rowNormSqDistribution_mul_div A i fun h => absurd h (hA i),
    ← Finset.sum_div, EuclideanSpace.norm_sq_eq]

/-- **Randomized Kaczmarz, any right-hand side**: with rows drawn independently from the
squared-row-norm law, row $i$ with probability $\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$
($\mathbf{a}_i$ the rows of
$\mathbf{A}$), for every $\mathbf{x}_\star$ with $\mathbf{x}_\star - \mathbf{x}_0$ in the row
space of $\mathbf{A}$ and with
$\rho = 1 - (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^{-2}$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \rho^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2 + (1 - \rho^q)\,
\|\mathbf{A}^{+}\|_2^2\,\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2\,.$$
No rank assumption. **The reference point.** For $\mathbf{x}_0 = \mathbf{0}$ take
$\mathbf{x}_\star = \mathbf{A}^{+}\mathbf{b}$; in general take the least-squares solution
nearest $\mathbf{x}_0$, $\mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$,
which minimises the horizon (`NLAlib.integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le`).
The choice $\mathbf{x}_\star = \mathbf{A}^{+}\mathbf{b}$ with a generic $\mathbf{x}_0$ violates the
row-space hypothesis, and the bound then fails. [ZouziasFreris2013, Theorem 7]; the same horizon
$\|\mathbf{w}\|^2/\sigma_{\min}^2$, here with the factor $1 - \rho^q$. [Needell2010,
Theorem 2.1]; there for full column rank, in the unsquared norm and with the larger horizon
$R\gamma^2 \ge \|\mathbf{A}^{+}\|_2^2\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2$, which this
implies by Jensen's inequality. Port of `NLAlib.Kaczmarz.expErr_le_add_of_sub_mem_range` and
five variants. Iteration count:
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le`.
Result: kaczmarz-inconsistent -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_add
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
        (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q) * specNorm (pinv A) ^ 2 *
          ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [eq_zero_of_hasLaw_rowNormSqDistribution_zero hι]
    simp [frobPseudoConditionNumber_zero]
  have := isProbabilityMeasure_samplingMeasure _ (sum_rowNormSqDistribution hA)
  have : IsProbabilityMeasure μ := hι.isProbabilityMeasure
  have hs : 0 < specNorm (pinv A) := (specNorm_nonneg _).lt_of_ne fun h =>
    hA (pinv_eq_zero.mp (specNorm_eq_zero_iff.mp h.symm))
  have hF : 0 < frobNorm A := (frobNorm_nonneg A).lt_of_ne fun h =>
    hA (frobNorm_eq_zero_iff.mp h.symm)
  have hκ2 : frobPseudoConditionNumber A ^ 2 = frobNorm A ^ 2 * specNorm (pinv A) ^ 2 := by
    rw [frobPseudoConditionNumber_def, mul_pow]
  have hρ0 := zero_le_one_sub_one_div_frobPseudoConditionNumber_sq hA
  have hN : Continuous fun v : n → 𝕜 => ‖WithLp.toLp 2 v‖ ^ 2 :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 _)).pow 2
  have hNm : Continuous fun v : m → 𝕜 => ‖WithLp.toLp 2 v‖ ^ 2 :=
    (continuous_norm.comp (PiLp.continuous_toLp 2 _)).pow 2
  have hstep : ∀ j, ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ (j + 1))‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) *
        ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ j)‖ ^ 2 ∂μ +
      (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2)) * specNorm (pinv A) ^ 2 *
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := fun j => by
    have h1 := integral_norm_sub_kaczmarzIterate_succ_sq_le (b := b) (x₀ := x₀) hι xs j
    have h2 : (∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ j)‖ ^ 2 ∂μ) /
        specNorm (pinv A) ^ 2 ≤
        ∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ j))‖ ^ 2 ∂μ := by
      rw [← integral_div]
      refine integral_mono ((integrable_comp_kaczmarzIterate hι.aemeasurable A b x₀ j
        (hN.comp (continuous_const.sub continuous_id))).div_const _)
        (integrable_comp_kaczmarzIterate hι.aemeasurable A b x₀ j (hNm.comp
          ((Matrix.mulVecLin A).continuous_of_finiteDimensional.comp
            (continuous_const.sub continuous_id)))) fun ω => ?_
      have hmem := Submodule.sub_mem _ hx₀ (kaczmarzIterate_sub_mem_range A (ι ω) b x₀ j)
      rw [sub_sub_sub_cancel_right] at hmem
      have h := pow_le_pow_left₀ (norm_nonneg _)
        (norm_le_specNorm_pinv_mul_norm_mulVec_of_mem_range A hmem) 2
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    have h3 : (∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ j)‖ ^ 2 ∂μ) /
        (frobNorm A ^ 2 * specNorm (pinv A) ^ 2) ≤
        (∫ ω, ‖WithLp.toLp 2 (A *ᵥ (xs - kaczmarzIterate A (ι ω) b x₀ j))‖ ^ 2 ∂μ) /
          frobNorm A ^ 2 := by
      rw [mul_comm, ← div_div]
      exact div_le_div_of_nonneg_right h2 (by positivity)
    have h4 : (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2)) * specNorm (pinv A) ^ 2 *
        ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 = ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 / frobNorm A ^ 2 := by
      rw [hκ2]
      field_simp
      ring
    rw [h4, hκ2]
    have h5 : (1 - 1 / (frobNorm A ^ 2 * specNorm (pinv A) ^ 2)) *
        ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ j)‖ ^ 2 ∂μ =
        ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ j)‖ ^ 2 ∂μ -
          (∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ j)‖ ^ 2 ∂μ) /
            (frobNorm A ^ 2 * specNorm (pinv A) ^ 2) := by ring
    rw [h5]
    linarith
  induction q with
  | zero =>
    simp only [kaczmarzIterate_zero, integral_const, probReal_univ, one_smul, pow_zero, one_mul,
      sub_self, zero_mul, add_zero, le_refl]
  | succ q ih =>
    calc _ ≤ _ := hstep q
      _ ≤ (1 - 1 / frobPseudoConditionNumber A ^ 2) *
            ((1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
              (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q) * specNorm (pinv A) ^ 2 *
                ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2) +
          (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2)) * specNorm (pinv A) ^ 2 *
            ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by gcongr
      _ = _ := by ring

/-- **From any start, randomized Kaczmarz converges to the least-squares solution nearest the
start, up to the horizon**, for any right-hand side and with no hypothesis: with rows drawn
independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$\mathbf{x}_\star = \mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$ and
$\rho = 1 - (\|\mathbf{A}\|_{\mathsf{F}}\|\mathbf{A}^{+}\|_2)^{-2}$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \rho^q\|\mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)\|^2 +
(1 - \rho^q)\,\|\mathbf{A}^{+}\|_2^2\,\|(\mathbf{I} - \mathbf{P}_{\mathbf{A}})\mathbf{b}\|^2\,.$$
From $\mathbf{x}_0 = \mathbf{0}$ the limit is $\mathbf{A}^{+}\mathbf{b}$.
[ZouziasFreris2013, Theorem 7], there from $\mathbf{x}_0 = \mathbf{0}$;
[LeventhalLewis2010, Theorem 4.7], there for consistent systems.
Port of `NLAlib.Kaczmarz.expErr_zero_le_moorePenroseInverse`.
Result: kaczmarz-rank-deficient -/
theorem integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (x₀ + pinv A *ᵥ (b - A *ᵥ x₀) - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q *
          ‖WithLp.toLp 2 (pinv A *ᵥ (b - A *ᵥ x₀))‖ ^ 2 +
        (1 - (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q) * specNorm (pinv A) ^ 2 *
          ‖WithLp.toLp 2 ((1 - rangeProjector A) *ᵥ b)‖ ^ 2 := by
  have hx : x₀ + pinv A *ᵥ (b - A *ᵥ x₀) - x₀ ∈ LinearMap.range Aᴴ.mulVecLin := by
    rw [add_sub_cancel_left, ← range_pinv]
    exact ⟨_, rfl⟩
  have hr : b - A *ᵥ (x₀ + pinv A *ᵥ (b - A *ᵥ x₀)) = (1 - rangeProjector A) *ᵥ b := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, mul_pinv, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_sub (rangeProjector A), Matrix.mulVec_mulVec x₀ (rangeProjector A) A,
      rangeProjector_mul_self]
    abel
  have h := integral_norm_sub_kaczmarzIterate_sq_le_add (b := b) hι hx q
  rwa [hr, add_sub_cancel_left] at h

/-- **Randomized Kaczmarz for a consistent system converges to the projection of the start onto
the solution set**: with rows drawn independently from the squared-row-norm law, row $i$ with
probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$\mathbf{b} \in \operatorname{range}\mathbf{A}$ and
$\mathbf{x}_\star = \mathbf{x}_0 + \mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \Bigl(1 - \frac{1}{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2}
\Bigr)^q\|\mathbf{A}^{+}(\mathbf{b} - \mathbf{A}\mathbf{x}_0)\|^2\,.$$
[LeventhalLewis2010, Theorem 4.7]; [ZouziasFreris2013, Theorem 4], there from
$\mathbf{x}_0 = \mathbf{0}$. -/
theorem integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le_of_mem_range
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (hb : b ∈ LinearMap.range A.mulVecLin) (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (x₀ + pinv A *ᵥ (b - A *ᵥ x₀) - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q *
        ‖WithLp.toLp 2 (pinv A *ᵥ (b - A *ᵥ x₀))‖ ^ 2 := by
  have hb' : (1 - rangeProjector A) *ᵥ b = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, rangeProjector_mulVec_eq_self_iff.mpr hb, sub_self]
  have h := integral_norm_add_pinv_mulVec_sub_kaczmarzIterate_sq_le (b := b) hι x₀ q
  rwa [hb', WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero, mul_zero, add_zero] at h

/-- **Randomized Kaczmarz converges linearly in expectation** (Strohmer–Vershynin), any rank: for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of
$\mathbf{A}$ and rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \Bigl(1 - \frac{1}{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2}
\Bigr)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,,$$
the rate in $[0, 1)$ for $\mathbf{A} \ne \mathbf{0}$. [StrohmerVershynin2009, Theorem 2]; there
for full column rank, where the row-space hypothesis is empty. [ZouziasFreris2013, Theorem 4].
Port of `NLAlib.integral_sqErr_kaczmarz_le_frobPseudoConditionNumber`. Iteration count:
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le`.
Result: randomized-kaczmarz -/
theorem integral_norm_sub_kaczmarzIterate_sq_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - 1 / frobPseudoConditionNumber A ^ 2) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  have h := integral_norm_sub_kaczmarzIterate_sq_le_add (b := b) hι hx₀ q
  rwa [hxs, sub_self, WithLp.toLp_zero, norm_zero, zero_pow two_ne_zero, mul_zero, add_zero] at h

/-- **Randomized Kaczmarz, iteration count**: for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\mathbf{x}_\star - \mathbf{x}_0$ in the row space of $\mathbf{A}$, rows drawn independently from
the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$
the rows of $\mathbf{A}$), $\varepsilon > 0$ and
$q \ge \|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
[StrohmerVershynin2009, (11)], which counts $2\kappa(\mathbf{A})^2\log(1/\varepsilon)$ steps for
the unsquared error.
Asymptotic form:
`NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_of_mul_log_le`. -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε) ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [eq_zero_of_hasLaw_rowNormSqDistribution_zero hι, integral_zero_measure]
    exact mul_nonneg hε.le (sq_nonneg _)
  exact (integral_norm_sub_kaczmarzIterate_sq_le hι hxs hx₀ q).trans
    (mul_le_mul_of_nonneg_right (one_sub_one_div_frobPseudoConditionNumber_sq_pow_le hA hε hq)
      (sq_nonneg _))

/-- **Randomized Kaczmarz, any right-hand side, iteration count**: for every $\mathbf{x}_\star$
with $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of $\mathbf{A}$, rows drawn independently
from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$\varepsilon > 0$ and
$q \ge \|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2 +
\|\mathbf{A}^{+}\|_2^2\,\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2\,.$$
[ZouziasFreris2013, Theorem 7].
Asymptotic form:
`NLAlib.exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le`. -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    {xs : n → 𝕜} (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin)
    {ε : ℝ} (hε : 0 < ε) {q : ℕ} (hq : frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε) ≤ q) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
        specNorm (pinv A) ^ 2 * ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by
  rcases eq_or_ne A 0 with rfl | hA
  · rw [eq_zero_of_hasLaw_rowNormSqDistribution_zero hι, integral_zero_measure]
    positivity
  have hρq := one_sub_one_div_frobPseudoConditionNumber_sq_pow_le hA hε hq
  have hρ0 := pow_nonneg (zero_le_one_sub_one_div_frobPseudoConditionNumber_sq hA) q
  have hh : 0 ≤ specNorm (pinv A) ^ 2 * ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by positivity
  refine (integral_norm_sub_kaczmarzIterate_sq_le_add hι hx₀ q).trans ?_
  nlinarith [mul_le_mul_of_nonneg_right hρq (sq_nonneg ‖WithLp.toLp 2 (xs - x₀)‖),
    mul_nonneg hρ0 hh]

/-! ### Kaczmarz as sketch-and-project; the mean iterate -/

/-- **The expected projector of a random row**: for weights $p_i$ (any, not necessarily summing
to one), with $\mathbf{a}_i$ the rows of $\mathbf{A}$ and the row-selection sketch
$\mathbf{e}_i^{\mathsf{T}}$,
$$\int \mathbf{P}_{(\mathbf{e}_i^{\mathsf{T}}\mathbf{A})^{\mathsf{H}}}\,dp(i) = \sum_i p_i\,
\mathbf{P}_{\overline{\mathbf{a}_i}}\,,$$
the integral against `NLAlib.samplingMeasure p`, and
$\mathbf{P}_{\overline{\mathbf{a}_i}}$ the projector onto the span of $\overline{\mathbf{a}_i}$.
[StrohmerVershynin2009, (8)], there the random projection $\mathbf{Z}$. -/
theorem integral_rangeProjector_conjTranspose_selectionMatrix_mul [DecidableEq n]
    (A : Matrix m n 𝕜) (p : m → ℝ≥0) :
    ∫ i, rangeProjector ((selectionMatrix fun _ : Unit => i)ᴴ * A)ᴴ ∂samplingMeasure p =
      ∑ i, (p i : ℝ) • rangeProjector (Matrix.replicateCol Unit (star (A i))) := by
  rw [integral_samplingMeasure]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [conjTranspose_selectionMatrix_unit_mul, Matrix.conjTranspose_replicateRow]

/-- **The expected projector at squared-row-norm weights** is
$\mathbf{A}^{\mathsf{H}}\mathbf{A}/\|\mathbf{A}\|_{\mathsf{F}}^2$: with $\mathbf{e}_i^{\mathsf{T}}$
the row-selection sketch and the integral against `NLAlib.samplingMeasure` at the weights
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\int \mathbf{P}_{(\mathbf{e}_i^{\mathsf{T}}\mathbf{A})^{\mathsf{H}}}\,dp(i) =
\frac{\mathbf{A}^{\mathsf{H}}\mathbf{A}}{\|\mathbf{A}\|_{\mathsf{F}}^2}\,.$$
[StrohmerVershynin2009, (7)–(9)]. -/
theorem integral_rangeProjector_conjTranspose_selectionMatrix_mul_rowNormSqDistribution
    [DecidableEq n] (A : Matrix m n 𝕜) :
    ∫ i, rangeProjector ((selectionMatrix fun _ : Unit => i)ᴴ * A)ᴴ
        ∂samplingMeasure (rowNormSqDistribution A) = (frobNorm A ^ 2)⁻¹ • (Aᴴ * A) := by
  rw [integral_rangeProjector_conjTranspose_selectionMatrix_mul]
  have hcol : ∀ a : n → 𝕜, rangeProjector (Matrix.replicateCol Unit (star a)) =
      (‖WithLp.toLp 2 a‖ ^ 2)⁻¹ •
        (Matrix.replicateCol Unit (star a) * Matrix.replicateRow Unit a) :=
    fun a => by
      rw [← mul_pinv, ← Matrix.conjTranspose_replicateRow, pinv_conjTranspose, pinv_replicateRow,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_replicateCol, star_star, star_trivial,
        Matrix.mul_smul]
  have hsum : ∑ i, Matrix.replicateCol Unit (star (A i)) * Matrix.replicateRow Unit (A i) =
      Aᴴ * A := by
    ext j k
    simp [Matrix.mul_apply, Matrix.sum_apply, Matrix.conjTranspose_apply]
  rw [← hsum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hcol, smul_smul, coe_rowNormSqDistribution]
  by_cases h : A i = 0
  · simp [h]
  · have : ‖WithLp.toLp 2 (A i)‖ ≠ 0 := norm_ne_zero_iff.mpr (by rwa [Ne, WithLp.toLp_eq_zero])
    congr 1
    field_simp

/-- **Randomized Kaczmarz with any row probabilities**, consistent systems: for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space of
$\mathbf{A}$, rows drawn independently from the squared-row-norm law, row $i$ with probability $p_i$
($\sum_i p_i = 1$), and $\lambda\mathbf{P}_{\mathbf{A}^{\mathsf{H}}} \preceq \sum_i p_i
\mathbf{P}_{\overline{\mathbf{a}_i}}$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$,
$\mathbf{P}_{\overline{\mathbf{a}_i}}$ the projector onto the span of $\overline{\mathbf{a}_i}$),
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le (1 - \lambda)^q\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
Uniform sampling is $p_i = 1/\lvert m \rvert$. The sketch-and-project theorem
`NLAlib.integral_norm_sub_sketchAndProjectIterate_sq_le` with row-selection sketches.
[GowerRichtarik2015, §3.3]. -/
theorem integral_norm_sub_kaczmarzIterate_sq_le_of_hasLaw_samplingMeasure
    {p : m → ℝ≥0} (hp : ∑ i, p i = 1)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure p) μ)
    {xs : n → 𝕜} (hxs : A *ᵥ xs = b) (hx₀ : xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin) {lam : ℝ}
    (hlam : lam • rangeProjector Aᴴ ≤
      ∑ i, (p i : ℝ) • rangeProjector (Matrix.replicateCol Unit (star (A i)))) (q : ℕ) :
    ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
      (1 - lam) ^ q * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  classical
  have := isProbabilityMeasure_samplingMeasure p hp
  have hT : Measurable fun i : m => (selectionMatrix fun _ : Unit => i : Matrix m Unit 𝕜)ᴴ :=
    measurable_of_countable _
  have : IsProbabilityMeasure ((samplingMeasure p).map fun i : m =>
      (selectionMatrix fun _ : Unit => i : Matrix m Unit 𝕜)ᴴ) :=
    Measure.isProbabilityMeasure_map hT.aemeasurable
  have hS : HasLaw (fun ω j => (selectionMatrix fun _ : Unit => ι ω j : Matrix m Unit 𝕜)ᴴ)
      (Measure.infinitePi fun _ : ℕ => (samplingMeasure p).map fun i : m =>
        (selectionMatrix fun _ : Unit => i : Matrix m Unit 𝕜)ᴴ) μ := by
    have hmp : MeasurePreserving (fun (s : ℕ → m) j =>
        (selectionMatrix fun _ : Unit => s j : Matrix m Unit 𝕜)ᴴ)
        (Measure.infinitePi fun _ : ℕ => samplingMeasure p)
        (Measure.infinitePi fun _ : ℕ => (samplingMeasure p).map fun i : m =>
          (selectionMatrix fun _ : Unit => i : Matrix m Unit 𝕜)ᴴ) :=
      ⟨measurable_pi_lambda _ fun j => hT.comp (measurable_pi_apply j),
        Measure.infinitePi_map_pi (fun _ => samplingMeasure p) fun _ => hT⟩
    exact hmp.fun_comp_hasLaw hι
  have hE : ∫ T, rangeProjector (T * A)ᴴ ∂(samplingMeasure p).map (fun i : m =>
      (selectionMatrix fun _ : Unit => i : Matrix m Unit 𝕜)ᴴ) =
      ∑ i, (p i : ℝ) • rangeProjector (Matrix.replicateCol Unit (star (A i))) := by
    have hm : AEStronglyMeasurable (fun T : Matrix Unit m 𝕜 => rangeProjector (T * A)ᴴ)
        ((samplingMeasure p).map fun i : m => (selectionMatrix fun _ : Unit => i)ᴴ) :=
      (measurable_rangeProjector.comp (Measurable.matrix_conjTranspose continuous_star.measurable
        (measurable_id.matrix_mul measurable_const))).aestronglyMeasurable
    rw [integral_map hT.aemeasurable hm]
    exact integral_rangeProjector_conjTranspose_selectionMatrix_mul A p
  exact integral_norm_sub_sketchAndProjectIterate_sq_le hS hxs hx₀ (hE ▸ hlam) q

/-- **The mean Kaczmarz iterate is Landweber's iteration** with step
$\|\mathbf{A}\|_{\mathsf{F}}^{-2}$, for any right-hand side: for $\mathbf{A} \ne \mathbf{0}$ and
rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\mathbb{E}[\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q)] =
\mathsf{richardsonIterate}(\mathbf{A}, \|\mathbf{A}\|_{\mathsf{F}}^{-2}\mathbf{A}^{\mathsf{H}},
\mathbf{b}, \mathbf{x}_0, q)\,,$$
that is $\mathbb{E}[\mathbf{x}_{q+1}] = \mathbb{E}[\mathbf{x}_q] +
\|\mathbf{A}\|_{\mathsf{F}}^{-2}\mathbf{A}^{\mathsf{H}}(\mathbf{b} -
\mathbf{A}\mathbb{E}[\mathbf{x}_q])$. For $\mathbf{A} = \mathbf{0}$ the law is the zero measure and
the identity fails. The averaged form of the observation that randomized Kaczmarz is stochastic
gradient descent on the least-squares objective [MaNeedellRamdas2015, §2.1]. Its
normal-equations form is `NLAlib.integral_kaczmarzIterate`. -/
theorem integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose (hA : A ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, kaczmarzIterate A (ι ω) b x₀ q ∂μ =
      richardsonIterate A ((frobNorm A ^ 2)⁻¹ • Aᴴ) b x₀ q := by
  have hp := sum_rowNormSqDistribution hA
  have := isProbabilityMeasure_samplingMeasure _ hp
  have : IsProbabilityMeasure μ := hι.isProbabilityMeasure
  have hp' : ∑ i, (rowNormSqDistribution A i : ℝ) = 1 := by
    rw [← NNReal.coe_sum, hp, NNReal.coe_one]
  have hmean : ∀ x : n → 𝕜, ∫ i, sketchAndProject A (selectionMatrix fun _ : Unit => i)ᴴ b x
      ∂samplingMeasure (rowNormSqDistribution A) =
      x + ((frobNorm A ^ 2)⁻¹ • Aᴴ) *ᵥ (b - A *ᵥ x) := fun x => by
    simp only [sketchAndProject_conjTranspose_selectionMatrix]
    rw [integral_samplingMeasure]
    simp only [smul_add, Finset.sum_add_distrib, ← Finset.sum_smul, hp', one_smul]
    congr 1
    have hAr : Aᴴ *ᵥ (b - A *ᵥ x) = ∑ i, (b - A *ᵥ x) i • star (A i) := by
      ext j
      simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, Finset.sum_apply, mul_comm]
    rw [Matrix.smul_mulVec, hAr, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases h : A i = 0
    · simp [h]
    have : ‖WithLp.toLp 2 (A i)‖ ≠ 0 := norm_ne_zero_iff.mpr (by rwa [Ne, WithLp.toLp_eq_zero])
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_smul,
      smul_smul, coe_rowNormSqDistribution, Pi.sub_apply]
    congr 1
    push_cast
    field_simp
  have hI : ∀ j, Integrable (fun ω => kaczmarzIterate A (ι ω) b x₀ j) μ := fun j =>
    integrable_comp_kaczmarzIterate hι.aemeasurable A b x₀ j continuous_id
  induction q with
  | zero =>
    simp only [kaczmarzIterate_zero, richardsonIterate_zero, integral_const, probReal_univ,
      one_smul]
  | succ q ih =>
    have hfub := integral_comp_kaczmarzIterate hp hι A b x₀ q
      (f := fun y => sketchAndProject A (selectionMatrix fun _ : Unit => y.2)ᴴ b y.1)
      (continuous_sketchAndProject_conjTranspose_selectionMatrix A b)
    simp only [hmean] at hfub
    change ∫ ω, sketchAndProject A (selectionMatrix fun _ : Unit => ι ω q)ᴴ b
      (kaczmarzIterate A (ι ω) b x₀ q) ∂μ = _
    have hL : ∫ ω, ((frobNorm A ^ 2)⁻¹ • Aᴴ * A) *ᵥ kaczmarzIterate A (ι ω) b x₀ q ∂μ =
        ((frobNorm A ^ 2)⁻¹ • Aᴴ * A) *ᵥ ∫ ω, kaczmarzIterate A (ι ω) b x₀ q ∂μ :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin
        ((frobNorm A ^ 2)⁻¹ • Aᴴ * A))).integral_comp_comm (hI q)
    simp only [Matrix.mulVec_sub, Matrix.mulVec_mulVec] at hfub ⊢
    have hI2 : Integrable (fun ω => ((frobNorm A ^ 2)⁻¹ • Aᴴ * A) *ᵥ
        kaczmarzIterate A (ι ω) b x₀ q) μ :=
      integrable_comp_kaczmarzIterate hι.aemeasurable A b x₀ q
        (Matrix.mulVecLin ((frobNorm A ^ 2)⁻¹ • Aᴴ * A)).continuous_of_finiteDimensional
    have hI3 : Integrable (fun ω => ((frobNorm A ^ 2)⁻¹ • Aᴴ) *ᵥ b -
        ((frobNorm A ^ 2)⁻¹ • Aᴴ * A) *ᵥ kaczmarzIterate A (ι ω) b x₀ q) μ :=
      (integrable_const _).sub hI2
    rw [hfub, richardsonIterate_succ, ← ih, integral_add (hI q) hI3,
      integral_sub (integrable_const _) hI2, integral_const, probReal_univ, one_smul, hL,
      Matrix.mulVec_sub, Matrix.mulVec_mulVec]

/-- **The mean Kaczmarz iterate is Richardson's iteration on the normal equations** with step
$\|\mathbf{A}\|_{\mathsf{F}}^{-2}$, for any right-hand side: for $\mathbf{A} \ne \mathbf{0}$ and
rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$$\mathbb{E}[\mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b}, \mathbf{x}_0, q)] =
\mathsf{richardsonIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \|\mathbf{A}\|_{\mathsf{F}}^{-2}
\mathbf{I}, \mathbf{A}^{\mathsf{H}}\mathbf{b}, \mathbf{x}_0, q)\,.$$
The Landweber form, which avoids $\mathbf{A}^{\mathsf{H}}\mathbf{A}$, is
`NLAlib.integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose`.
[MaNeedellRamdas2015, §2.1], the stochastic-gradient reading. -/
theorem integral_kaczmarzIterate [DecidableEq n] (hA : A ≠ 0)
    (hι : HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ)
    (x₀ : n → 𝕜) (q : ℕ) :
    ∫ ω, kaczmarzIterate A (ι ω) b x₀ q ∂μ =
      richardsonIterate (Aᴴ * A) ((frobNorm A ^ 2)⁻¹ • (1 : Matrix n n 𝕜)) (Aᴴ *ᵥ b) x₀ q := by
  rw [integral_kaczmarzIterate_eq_richardsonIterate_conjTranspose hA hι x₀ q,
    show (frobNorm A ^ 2)⁻¹ • Aᴴ = ((frobNorm A ^ 2)⁻¹ • (1 : Matrix n n 𝕜)) * Aᴴ by
      rw [Matrix.smul_mul, Matrix.one_mul], richardsonIterate_mul_conjTranspose]

end Random

/-! ### Asymptotic iteration counts -/

/-- **$O(\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon))$ iterations
suffice for randomized Kaczmarz**: there are absolute constants $C, \varepsilon_0 > 0$ such that
for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, $\mathbf{x}_\star - \mathbf{x}_0$ in the row space
of $\mathbf{A}$, rows drawn independently from the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$ the rows of $\mathbf{A}$),
$0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2\,.$$
The constants come before every dimension. Proved from
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le` with $C = 1$ and
$\varepsilon_0 = 1$. [StrohmerVershynin2009, (11)], which counts
$2\kappa(\mathbf{A})^2\log(1/\varepsilon)$ steps for the unsquared error.
Asymptotic: NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le
Result: randomized-kaczmarz -/
theorem exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_of_mul_log_le :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
      [Fintype n] [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m]
      (μ : Measure Ω) (A : Matrix m n 𝕜) (b : m → 𝕜) (ι : Ω → ℕ → m) (xs x₀ : n → 𝕜) (q : ℕ)
      (ε : ℝ),
      HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ →
      A *ᵥ xs = b → xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < ε → ε ≤ ε₀ →
      C * (frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε)) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro Ω 𝕜 m n _ _ _ _ _ _ _ μ A b ι xs x₀ q ε hι hxs hx₀ hε _ hq
  exact integral_norm_sub_kaczmarzIterate_sq_le_mul_of_mul_log_le hι hxs hx₀ hε
    (by rwa [one_mul] at hq)

/-- **$O(\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon))$ iterations
suffice for randomized Kaczmarz to reach its horizon**, for any right-hand side: there are
absolute constants $C, \varepsilon_0 > 0$ such that for every $\mathbf{x}_\star$ with
$\mathbf{x}_\star - \mathbf{x}_0$ in the row space of $\mathbf{A}$, rows drawn independently from
the squared-row-norm law, row $i$ with probability
$\|\mathbf{a}_i\|^2/\|\mathbf{A}\|_{\mathsf{F}}^2$ ($\mathbf{a}_i$
the rows of $\mathbf{A}$), $0 < \varepsilon \le \varepsilon_0$ and
$q \ge C\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{A}^{+}\|_2^2\log(1/\varepsilon)$,
$$\mathbb{E}\|\mathbf{x}_\star - \mathsf{kaczmarzIterate}(\mathbf{A}, \iota, \mathbf{b},
\mathbf{x}_0, q)\|^2 \le \varepsilon\|\mathbf{x}_\star - \mathbf{x}_0\|^2 +
\|\mathbf{A}^{+}\|_2^2\,\|\mathbf{b} - \mathbf{A}\mathbf{x}_\star\|^2\,.$$
The constants come before every dimension. Proved from
`NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le` with $C = 1$ and
$\varepsilon_0 = 1$. [ZouziasFreris2013, Theorem 7].
Asymptotic: NLAlib.integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le
Result: kaczmarz-inconsistent -/
theorem exists_forall_integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 m n : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
      [Fintype n] [DecidableEq m] [MeasurableSpace m] [MeasurableSingletonClass m]
      (μ : Measure Ω) (A : Matrix m n 𝕜) (b : m → 𝕜) (ι : Ω → ℕ → m) (xs x₀ : n → 𝕜) (q : ℕ)
      (ε : ℝ),
      HasLaw ι (Measure.infinitePi fun _ : ℕ => samplingMeasure (rowNormSqDistribution A)) μ →
      xs - x₀ ∈ LinearMap.range Aᴴ.mulVecLin → 0 < ε → ε ≤ ε₀ →
      C * (frobPseudoConditionNumber A ^ 2 * Real.log (1 / ε)) ≤ q →
      ∫ ω, ‖WithLp.toLp 2 (xs - kaczmarzIterate A (ι ω) b x₀ q)‖ ^ 2 ∂μ ≤
        ε * ‖WithLp.toLp 2 (xs - x₀)‖ ^ 2 +
          specNorm (pinv A) ^ 2 * ‖WithLp.toLp 2 (b - A *ᵥ xs)‖ ^ 2 := by
  refine ⟨1, 1, one_pos, one_pos, ?_⟩
  intro Ω 𝕜 m n _ _ _ _ _ _ _ μ A b ι xs x₀ q ε hι hx₀ hε _ hq
  exact integral_norm_sub_kaczmarzIterate_sq_le_mul_add_of_mul_log_le hι hx₀ hε
    (by rwa [one_mul] at hq)

end NLAlib
