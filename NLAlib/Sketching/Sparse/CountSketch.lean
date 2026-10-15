/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.MeasureTheory.MeasurableSpace.Defs
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.Probability.Distributions.Rademacher
public import NLAlib.Probability.Distributions.Sampling
public import NLAlib.Probability.Law
public import NLAlib.Probability.QuadraticForm.Moments
public import NLAlib.Probability.Tail
public import NLAlib.Sketching.Properties.Isotropic
public import NLAlib.Sketching.Properties.JohnsonLindenstrauss
public import NLAlib.Sketching.Properties.Oblivious
public import NLAlib.Sketching.Properties.TraceMoment
public import NLAlib.Matrix.Subspaces.Leverage

/-!
# CountSketch

For a hash $h : n \to k$ and signs $\sigma : n \to \mathbb{R}$, the CountSketch matrix
`NLAlib.countSketchMatrix h σ` $\in \Bbbk^{k \times n}$ has a single nonzero entry per column:
column $i$ is $\sigma_i \mathbf{e}_{h(i)}$. Its law `NLAlib.countSketch k n` takes i.i.d. uniform
hash values and independent Rademacher signs; it is the pushforward of the primitive hash and signs
with `⊤` on `k` inside the definition, `NLAlib.countSketch_eq_map` restates it under any
measurable space on `k` with measurable singletons, and `NLAlib.hasLaw_countSketchMatrix` takes a
user's own hash and signs. The entries are $0$ and $\pm 1$ in any `RCLike` field.

Everything rests on one computation. For signs with $\sigma_i^2 = 1$ the Gram error
$\mathbf{H} = \mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}$ is hollow, with entry
$\sigma_i \sigma_j$ where $i \ne j$ collide, and averaging the second moment of a hollow
Rademacher quadratic form over collisions of probability $1/\lvert k \rvert$ gives, for every
$\mathbf{M}$,
$$\mathbb{E}\lvert \operatorname{tr}(\mathbf{M}\mathbf{H})\rvert^2
= \frac{\|\mathbf{M}\|_{\mathsf{F}}^2 + \langle \mathbf{M}, \mathbf{M}^{\mathsf{T}}
\rangle_{\mathsf{F}} - 2 \sum_i \lvert \mathbf{M}_{i,i} \rvert^2}{\lvert k \rvert}\,.$$
Its instances are the exact second moment of approximate matrix multiplication, the exact mean of
the squared Gram error of an orthonormal $\mathbf{U}$, and the JL moment; from these the trace
moment at $q = 1$ with bound $(d^2 + d)/\lvert k \rvert$, the oblivious subspace embedding and
injection with failure probability $(d^2 + d)/(\lvert k \rvert \varepsilon^2)$, and the sizes. The
transpose terms ($\langle \mathbf{M}, \mathbf{M}^{\mathsf{T}} \rangle_{\mathsf{F}}$,
$\|\mathbf{A}^{\mathsf{T}}\mathbf{B}\|_{\mathsf{F}}^2$,
$\|\mathbf{U}^{\mathsf{T}}\mathbf{U}\|_{\mathsf{F}}^2$) are at most their Cauchy–Schwarz values,
which is all the bounds use, so every bound is the same over $\mathbb{R}$ and $\mathbb{C}$.

Degenerate cases. Empty `k` and nonempty `n`: there is no hash, the law is the zero measure,
`HasLaw` forces $\mu = 0$, every identity reads $0 = 0$ (each right side divides by
$\lvert k \rvert = 0$) and every tail holds; the sketch is not isotropic, hence `[Nonempty k]` on
isotropy, on the OSI and on the probability instance, and nowhere else. Empty `k` and empty `n`:
the law is the Dirac mass at the empty matrix, a probability measure that
`NLAlib.isProbabilityMeasure_countSketch` leaves out. Empty `n`: every Gram product is
$\mathbf{0}$ and no unit vector exists. Dimension $d = 0$: every bound is $0$ and every embedding
event is empty; for $d > \lvert n \rvert$ the OSE at $d$ is the one at $\lvert n \rvert$, so no
$d \le \lvert n \rvert$ is assumed. Signs off $\{\pm 1\}$ form a null set. For
$\varepsilon \ge 1$ the injection is vacuous and the bound is still true. Design:
`docs/design/Sketching-S7.md` §3.2, §8.

## Main definitions

* `NLAlib.countSketchMatrix`: the sketch built from a given hash and signs.
* `NLAlib.countSketch`: its law for a uniform hash and Rademacher signs.
* `NLAlib.countSketchRows`: the number of rows, at present
  <!-- value countSketchRows d \varepsilon \delta -->
  $(d^2 + d)/(\delta \varepsilon^2)$<!-- /value -->.

## Main results

* `NLAlib.countSketch_eq_map`, `NLAlib.hasLaw_countSketchMatrix`: the law as a pushforward, and
  the bridge from a user's own hash and signs.
* `NLAlib.conjTranspose_countSketchMatrix_mul_self_apply`,
  `NLAlib.conjTranspose_countSketchMatrix_mul_self_sub_one`: the Gram matrix, and the hollow Gram
  identity.
* `NLAlib.isIsotropicSketch_of_hasLaw_countSketch`: isotropy.
* `NLAlib.integral_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch`: the
  exact second moment.
* `NLAlib.integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch`,
  `NLAlib.integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_countSketch`,
  `NLAlib.measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch`: approximate
  matrix multiplication.
* `HasOrthonormalCols.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch`
  (in `NLAlib`), `NLAlib.hasGramTraceMoment_of_hasLaw_countSketch`: the Gram error and the
  trace moment.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch`,
  `NLAlib.isObliviousSubspaceInjection_of_hasLaw_countSketch`: the CountSketch OSE and OSI.
* `NLAlib.hasJLMoment_of_hasLaw_countSketch`: the JL moment at $p = 2$.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchRows_le`,
  `NLAlib.isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchRows_le`,
  `NLAlib.hasJLMoment_of_hasLaw_countSketch_of_le_card`: sizes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n q r : Type*} [Fintype k] [Fintype n] [DecidableEq k]
  {S : Ω → Matrix k n 𝕜} {ε δ : ℝ}

/-! ### The sketch and its law -/

/-- The **CountSketch matrix** of a hash $h : n \to k$ and signs $\sigma : n \to \mathbb{R}$:
$\mathbf{S}_{a,i} = \sigma_i$ if $h(i) = a$ and $0$ otherwise, so column $i$ is
$\sigma_i \mathbf{e}_{h(i)}$ and $\mathbf{S} = \mathbf{P}_h \operatorname{diag}(\sigma)$ for the
selection matrix $\mathbf{P}_h$ of $h$ (`NLAlib.selectionMatrix h`). Real entries, in any `RCLike`
field. Its law for uniform hashes and Rademacher signs is `NLAlib.countSketch`.
[Woodruff2014, §2.1, before Theorem 8] (the sparse embedding matrix, $S_{h(i),i} = \sigma(i)$);
[CamanoEpperlyMeyerTropp2025, (B.1)] (there $\mathbf{\Phi} = \mathbf{S}^{\mathsf{T}}$, over
$\mathbb{C}$ with Rademacher signs); [MartinssonTropp2020, Remark 9.1] (history). -/
def countSketchMatrix (h : n → k) (σ : n → ℝ) : Matrix k n 𝕜 :=
  Matrix.of fun a i => if h i = a then (σ i : 𝕜) else 0

variable (k n) in
/-- The **CountSketch law**: the pushforward by `NLAlib.countSketchMatrix` of i.i.d. uniform hash
values (`NLAlib.samplingMeasure` at weights $1/\lvert k \rvert$, which is Mathlib's
`uniformOn Set.univ` by `NLAlib.samplingMeasure_const_inv_card`; by `uniformOn_pi`, a uniform
function $n \to k$) and independent Rademacher signs (`NLAlib.rademacherVector n`). The measurable
space on `k` is `⊤` inside the definition, so no statement carries an instance on `k`;
`NLAlib.countSketch_eq_map` restates it under any measurable space on `k` with measurable
singletons. Junk value: the zero measure when `k` is empty and `n` is not.
[Woodruff2014, §2.1]; [CamanoEpperlyMeyerTropp2025, (B.1)]. -/
noncomputable def countSketch : Measure (Matrix k n 𝕜) :=
  let _ : MeasurableSpace k := ⊤
  ((Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹).prod
      (rademacherVector n)).map fun x => countSketchMatrix x.1 x.2

omit [Fintype k] [Fintype n] in
/-- For a fixed hash, the sketch is continuous in the signs. -/
private theorem continuous_countSketchMatrix (h : n → k) :
    Continuous fun σ : n → ℝ => (countSketchMatrix h σ : Matrix k n 𝕜) := by
  refine continuous_matrix fun a i => ?_
  simp only [countSketchMatrix, Matrix.of_apply]
  split_ifs
  · fun_prop
  · exact continuous_const

omit [Fintype k] [Fintype n] in
/-- Under a measurable space with measurable singletons on `k`, the sketch is measurable in the
hash and the signs jointly. -/
private theorem measurable_countSketchMatrix [Finite k] [Finite n] [MeasurableSpace k]
    [MeasurableSingletonClass k] :
    Measurable fun x : (n → k) × (n → ℝ) => (countSketchMatrix x.1 x.2 : Matrix k n 𝕜) :=
  measurable_from_prod_countable_right fun h => (continuous_countSketchMatrix h).measurable

/-- The CountSketch law is a finite measure. -/
instance isFiniteMeasure_countSketch : IsFiniteMeasure (countSketch (𝕜 := 𝕜) k n) := by
  unfold countSketch
  infer_instance

/-- The CountSketch law is a probability measure for nonempty `k`. -/
theorem isProbabilityMeasure_countSketch [Nonempty k] :
    IsProbabilityMeasure (countSketch (𝕜 := 𝕜) k n) := by
  let _ : MeasurableSpace k := ⊤
  have := isProbabilityMeasure_samplingMeasure (fun _ : k => (Fintype.card k : ℝ≥0)⁻¹)
    NNReal.sum_const_inv_card
  exact Measure.isProbabilityMeasure_map measurable_countSketchMatrix.aemeasurable

/-- The CountSketch law is the pushforward of i.i.d. uniform hash values and independent
Rademacher signs under any measurable space on `k` with measurable singletons (a finite
measurable space with measurable singletons is `⊤`, `DiscreteMeasurableSpace.eq_top`). The sign
factor is not finite, so the law has no finite-mixture form. -/
theorem countSketch_eq_map [MeasurableSpace k] [MeasurableSingletonClass k] :
    countSketch (𝕜 := 𝕜) k n =
      ((Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹).prod
        (rademacherVector n)).map fun x => countSketchMatrix x.1 x.2 := by
  obtain rfl := DiscreteMeasurableSpace.eq_top (α := k)
  rfl

/-- **From the user's own hash and signs**: for i.i.d. uniform hash values $h$ and independent
Rademacher signs $\sigma$, under any measurable space on `k` with measurable singletons, the
CountSketch matrix built from them has law `NLAlib.countSketch k n`. A uniform hash function,
`HasLaw h (uniformOn Set.univ) μ`, gives `hh` by `uniformOn_pi` and
`NLAlib.samplingMeasure_const_inv_card`. -/
theorem hasLaw_countSketchMatrix [MeasurableSpace k] [MeasurableSingletonClass k]
    {h : Ω → n → k} {σ : Ω → n → ℝ}
    (hh : HasLaw h
      (Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹) μ)
    (hσ : HasLaw σ (rademacherVector n) μ) (hind : IndepFun h σ μ) :
    HasLaw (fun ω => (countSketchMatrix (h ω) (σ ω) : Matrix k n 𝕜)) (countSketch k n) μ := by
  rw [countSketch_eq_map]
  have : IsProbabilityMeasure μ := hσ.isProbabilityMeasure_iff.2 inferInstance
  exact (⟨measurable_countSketchMatrix.aemeasurable, rfl⟩ : HasLaw
    (fun x : (n → k) × (n → ℝ) => (countSketchMatrix x.1 x.2 : Matrix k n 𝕜)) _
    ((Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹).prod
      (rademacherVector n))).comp (hind.hasLaw_prod hh hσ)

/-! ### The hollow Gram identity and isotropy -/

omit [Fintype n] in
/-- **The Gram matrix of a CountSketch**: for any real signs,
$(\mathbf{S}^{\mathsf{H}}\mathbf{S})_{i,j} = \sigma_i \sigma_j$ when $h(i) = h(j)$ and $0$
otherwise. The general form of the hollow Gram identity
(`NLAlib.conjTranspose_countSketchMatrix_mul_self_sub_one`), for a family that scales its signs.
[Woodruff2014, proof of Theorem 14] (the same expansion, for $\|\mathbf{S}\mathbf{x}\|^2$). -/
theorem conjTranspose_countSketchMatrix_mul_self_apply (h : n → k) (σ : n → ℝ) (i j : n) :
    ((countSketchMatrix h σ : Matrix k n 𝕜)ᴴ * countSketchMatrix h σ : Matrix n n 𝕜) i j =
      if h i = h j then ((σ i * σ j : ℝ) : 𝕜) else 0 := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, countSketchMatrix, Matrix.of_apply]
  rw [Finset.sum_eq_single (h i)]
  · by_cases hij : h i = h j
    · simp [hij]
    · simp [hij, Ne.symm hij]
  · intro a _ ha
    simp [Ne.symm ha]
  · exact fun hi => absurd (Finset.mem_univ _) hi

omit [Fintype n] in
/-- **The hollow Gram identity.** For signs with $\sigma_i^2 = 1$, the Gram error
$\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}$ of a CountSketch has zero diagonal, and entry
$\sigma_i \sigma_j$ at $i \ne j$ when $h(i) = h(j)$, $0$ otherwise. The deferred sparse families
(SparseStack, a stack of independent CountSketches) expand their Gram errors through it.
[Woodruff2014, proof of Theorem 14] (the same expansion, for $\|\mathbf{S}\mathbf{x}\|^2$);
[CamanoEpperlyMeyerTropp2025, proof of Lemma B.1]. -/
theorem conjTranspose_countSketchMatrix_mul_self_sub_one [DecidableEq n] (h : n → k)
    {σ : n → ℝ} (hσ : ∀ i, σ i ^ 2 = 1) :
    (countSketchMatrix h σ : Matrix k n 𝕜)ᴴ * countSketchMatrix h σ - 1 =
      Matrix.of fun i j => if i ≠ j ∧ h i = h j then ((σ i * σ j : ℝ) : 𝕜) else 0 := by
  ext i j
  rw [Matrix.sub_apply, conjTranspose_countSketchMatrix_mul_self_apply, Matrix.one_apply,
    Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    have h1 : σ i * σ i = 1 := by rw [← sq, hσ i]
    simp [h1]
  · simp [hij]

/-! ### Integrals against the law

Every integral against `NLAlib.countSketch k n` is computed on the product space of hashes and
signs: an iterated integral, signs inside. Almost surely the signs are $\pm 1$, so the entries of
the sketch lie in the compact set of matrices with entries of modulus at most $1$, and every
continuous function of the sketch is integrable. -/

/-- The hash factor of the CountSketch law. -/
private noncomputable abbrev hashLaw (k n : Type*) [Fintype k] [Fintype n] [MeasurableSpace k] :
    Measure (n → k) :=
  Measure.pi fun _ : n => samplingMeasure fun _ : k => (Fintype.card k : ℝ≥0)⁻¹

/-- Almost surely, the signs read in `𝕜` have modulus $1$ and square $1$
(`NLAlib.ae_norm_ofReal_eq_one_of_hasLaw_rademacherVector` on the identity). -/
private theorem ae_norm_ofReal_eq_one :
    ∀ᵐ σ ∂rademacherVector n, ∀ i, ‖((σ i : ℝ) : 𝕜)‖ = 1 ∧ ((σ i : ℝ) : 𝕜) ^ 2 = 1 :=
  ae_norm_ofReal_eq_one_of_hasLaw_rademacherVector HasLaw.id

/-- The integral of a function of the signs equal to $c$ almost surely is $c$. -/
private theorem integral_eq_of_ae_rademacherVector {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {f : (n → ℝ) → E} {c : E}
    (hf : ∀ᵐ σ ∂rademacherVector n, f σ = c) :
    ∫ σ, f σ ∂rademacherVector n = c := by
  rw [integral_congr_ae hf, integral_const, probReal_univ, one_smul]

omit [Fintype k] [Fintype n] [DecidableEq k] in
/-- The set of matrices with entries of modulus at most $1$ is compact. -/
private theorem isCompact_setOf_norm_apply_le_one :
    IsCompact {A : Matrix k n 𝕜 | ∀ a i, ‖A a i‖ ≤ 1} := by
  have h : {A : Matrix k n 𝕜 | ∀ a i, ‖A a i‖ ≤ 1} =
      Set.univ.pi fun _ : k => Set.univ.pi fun _ : n => Metric.closedBall (0 : 𝕜) 1 := by
    ext A
    change _ ↔ ∀ a ∈ Set.univ, ∀ i ∈ Set.univ, A a i ∈ Metric.closedBall (0 : 𝕜) 1
    simp only [Set.mem_ofPred_eq, Set.mem_univ, forall_const, mem_closedBall_zero_iff]
  rw [h]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1

/-- A continuous function of the sketch is integrable on the product space of hashes and signs. -/
private theorem integrable_comp_countSketchMatrix [MeasurableSpace k]
    [MeasurableSingletonClass k] {E : Type*} [NormedAddCommGroup E] {f : Matrix k n 𝕜 → E}
    (hf : Continuous f) :
    Integrable (fun x : (n → k) × (n → ℝ) => f (countSketchMatrix x.1 x.2))
      ((hashLaw k n).prod (rademacherVector n)) := by
  obtain ⟨C, hC⟩ := isCompact_setOf_norm_apply_le_one.exists_bound_of_continuousOn hf.continuousOn
  refine Integrable.of_bound
    (hf.comp_aestronglyMeasurable measurable_countSketchMatrix.aestronglyMeasurable) C ?_
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae (ae_norm_ofReal_eq_one (𝕜 := 𝕜))]
    with x hx
  refine hC _ fun a i => ?_
  simp only [countSketchMatrix, Matrix.of_apply]
  split_ifs
  · exact (hx i).1.le
  · simp

/-- A continuous function of a CountSketch is integrable. -/
private theorem integrable_comp_of_hasLaw_countSketch (hS : HasLaw S (countSketch k n) μ)
    {E : Type*} [NormedAddCommGroup E] {f : Matrix k n 𝕜 → E} (hf : Continuous f) :
    Integrable (fun ω => f (S ω)) μ := by
  let _ : MeasurableSpace k := ⊤
  rw [hS.integrable_comp_iff hf.aestronglyMeasurable, countSketch_eq_map,
    integrable_map_measure hf.aestronglyMeasurable measurable_countSketchMatrix.aemeasurable]
  exact integrable_comp_countSketchMatrix hf

/-- The integral of a continuous function of a CountSketch, iterated over the hash and the
signs. -/
private theorem integral_comp_of_hasLaw_countSketch [MeasurableSpace k]
    [MeasurableSingletonClass k] (hS : HasLaw S (countSketch k n) μ) {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Matrix k n 𝕜 → E}
    (hf : Continuous f) :
    ∫ ω, f (S ω) ∂μ =
      ∫ h, ∫ σ, f (countSketchMatrix h σ) ∂rademacherVector n ∂hashLaw k n := by
  refine (hS.integral_comp hf.aestronglyMeasurable).trans ?_
  rw [countSketch_eq_map,
    integral_map measurable_countSketchMatrix.aemeasurable hf.aestronglyMeasurable]
  exact integral_prod _ (integrable_comp_countSketchMatrix hf)

omit [DecidableEq k] in
/-- Two distinct hash values collide with probability $1/\lvert k \rvert$; for empty `k` both
sides are $0$. -/
private theorem measureReal_hashLaw_setOf_apply_eq_apply [MeasurableSpace k]
    [MeasurableSingletonClass k] {i j : n} (hij : i ≠ j) :
    (hashLaw k n).real {h | h i = h j} = (Fintype.card k : ℝ)⁻¹ := by
  rcases isEmpty_or_nonempty k with hk | hk
  · have h0 : hashLaw k n = 0 := by
      rw [← Measure.measure_univ_eq_zero, Measure.pi_univ]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [samplingMeasure])
    rw [h0, Fintype.card_eq_zero, Nat.cast_zero, inv_zero, measureReal_zero_apply]
  · have hc : (Fintype.card k : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [measureReal_pi_samplingMeasure_setOf_apply_eq_apply _ NNReal.sum_const_inv_card hij]
    have hc' : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    simp only [NNReal.coe_inv, NNReal.coe_natCast, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    field_simp

/-- For a fixed hash, $\mathbb{E}_\sigma\|\mathbf{S}\mathbf{x}\|^2 = \|\mathbf{x}\|^2$: the
quadratic form of the signs against $[h(i) = h(j)]\,\overline{\mathbf{x}_i}\mathbf{x}_j$, whose
trace is $\|\mathbf{x}\|^2$. -/
private theorem integral_norm_countSketchMatrix_mulVec_sq (h : n → k) (x : n → 𝕜) :
    ∫ σ, ‖WithLp.toLp 2 ((countSketchMatrix h σ : Matrix k n 𝕜) *ᵥ x)‖ ^ 2 ∂rademacherVector n =
      ‖WithLp.toLp 2 x‖ ^ 2 := by
  classical
  set D : Matrix n n 𝕜 := Matrix.of fun i j => if h i = h j then star (x i) * x j else 0
  have e (σ : n → ℝ) :
      ((‖WithLp.toLp 2 ((countSketchMatrix h σ : Matrix k n 𝕜) *ᵥ x)‖ ^ 2 : ℝ) : 𝕜) =
        quadForm D fun i => ((σ i : ℝ) : 𝕜) := by
    rw [← quadForm_conjTranspose_mul_self, quadForm_eq_sum, quadForm_eq_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [conjTranspose_countSketchMatrix_mul_self_apply]
    simp only [D, Matrix.of_apply, RCLike.star_def, RCLike.conj_ofReal]
    split_ifs
    · push_cast
      ring
    · simp
  have hx : IsIsotropic (fun σ : n → ℝ => fun i => ((σ i : ℝ) : 𝕜)) (rademacherVector n) :=
    isIsotropic_ofReal_of_hasLaw_rademacherVector HasLaw.id
  have htr : D.trace = ((‖WithLp.toLp 2 x‖ ^ 2 : ℝ) : 𝕜) := by
    simp only [Matrix.trace, Matrix.diag, D, Matrix.of_apply, if_true, EuclideanSpace.norm_sq_eq]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [RCLike.star_def, RCLike.conj_mul]
  apply RCLike.ofReal_injective (K := 𝕜)
  rw [← integral_ofReal]
  simp only [e]
  rw [hx.integral_quadForm D, htr]

/-- **CountSketch is isotropic**, $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$, for
nonempty `k`. [CamanoEpperlyMeyerTropp2025, Lemma B.1] (first part, there
$\mathbb{E}[\mathbf{\Phi}\mathbf{\Phi}^*] = \mathbf{I}$). -/
theorem isIsotropicSketch_of_hasLaw_countSketch [Nonempty k] [DecidableEq n]
    (hS : HasLaw S (countSketch k n) μ) : IsIsotropicSketch S μ := by
  let _ : MeasurableSpace k := ⊤
  have := isProbabilityMeasure_samplingMeasure (fun _ : k => (Fintype.card k : ℝ≥0)⁻¹)
    NNReal.sum_const_inv_card
  refine isIsotropicSketch_iff.2 ⟨fun a i => ?_, fun x => ?_⟩
  · exact (memLp_two_iff_integrable_sq_norm
      ((Matrix.measurable_apply a i).comp_aemeasurable hS.aemeasurable).aestronglyMeasurable).2
      (integrable_comp_of_hasLaw_countSketch hS ((continuous_id.matrix_elem a i).norm.pow 2))
  · rw [integral_comp_of_hasLaw_countSketch hS
      (f := fun A => ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2) (by fun_prop)]
    simp only [integral_norm_countSketchMatrix_mulVec_sq, integral_const, probReal_univ,
      one_smul]

/-! ### The exact second moment -/

/-- The squared trace of $\mathbf{M}$ against the Gram error of a CountSketch is integrable. -/
theorem integrable_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    [DecidableEq n] (hS : HasLaw S (countSketch k n) μ) (M : Matrix n n 𝕜) :
    Integrable (fun ω => ‖(M * ((S ω)ᴴ * S ω - 1)).trace‖ ^ 2) μ :=
  integrable_comp_of_hasLaw_countSketch hS (f := fun A => ‖(M * (Aᴴ * A - 1)).trace‖ ^ 2)
    (by fun_prop)

/-- For a fixed hash, the second moment over the signs: $\operatorname{tr}(\mathbf{M}\mathbf{H})$
is almost surely the quadratic form in the signs of the hollow matrix with entries
$[i \ne j,\ h(i) = h(j)]\,\mathbf{M}_{i,j}$, whose second moment is
`NLAlib.integral_norm_quadForm_sub_trace_sq` at $s = 1$, $m_4 = 1$. -/
private theorem integral_norm_trace_mul_countSketchMatrix_sq [DecidableEq n] (h : n → k)
    (M : Matrix n n 𝕜) :
    ∫ σ, ‖(M * ((countSketchMatrix h σ : Matrix k n 𝕜)ᴴ * countSketchMatrix h σ - 1)).trace‖ ^ 2
        ∂rademacherVector n =
      ∑ i, ∑ j, if i ≠ j ∧ h i = h j then ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i)
        else 0 := by
  set A : Matrix n n 𝕜 := Matrix.of fun i j => if i ≠ j ∧ h i = h j then M i j else 0
  have hdiag (i : n) : A i i = 0 := by simp [A]
  have hA : A.trace = 0 := by simp [Matrix.trace, hdiag]
  have hσ : HasLaw (fun σ : n → ℝ => σ) (rademacherVector n) (rademacherVector n) := HasLaw.id
  have e : ∀ᵐ σ ∂rademacherVector n,
      ‖(M * ((countSketchMatrix h σ : Matrix k n 𝕜)ᴴ * countSketchMatrix h σ - 1)).trace‖ ^ 2 =
        ‖quadForm A (fun i => ((σ i : ℝ) : 𝕜)) - A.trace‖ ^ 2 := by
    filter_upwards [ae_sq_eq_one_of_hasLaw_rademacherVector hσ] with σ hσ
    rw [conjTranspose_countSketchMatrix_mul_self_sub_one h hσ, hA, sub_zero, quadForm_eq_sum,
      Matrix.trace]
    congr 2
    simp only [Matrix.diag, Matrix.mul_apply, Matrix.of_apply, A]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases hc : i ≠ j ∧ h i = h j
    · have hc' : j ≠ i ∧ h j = h i := ⟨hc.1.symm, hc.2.symm⟩
      rw [if_pos hc, if_pos hc', RCLike.star_def, RCLike.conj_ofReal]
      push_cast
      ring
    · have hc' : ¬(j ≠ i ∧ h j = h i) := fun h' => hc ⟨h'.1.symm, h'.2.symm⟩
      rw [if_neg hc, if_neg hc']
      ring
  have hind : iIndepFun (fun i (σ : n → ℝ) => ((σ i : ℝ) : 𝕜)) (rademacherVector n) :=
    iIndepFun_ofReal_of_hasLaw_rademacherVector HasLaw.id
  rw [integral_congr_ae e, integral_norm_quadForm_sub_trace_sq hind
    (fun i => memLp_ofReal_of_hasLaw_rademacherVector hσ 4 i)
    (integral_ofReal_of_hasLaw_rademacherVector hσ)
    (fun i => integral_eq_of_ae_rademacherVector
      (ae_norm_ofReal_eq_one.mono fun σ h => by rw [(h i).1, one_pow]))
    (s := 1) (fun i => integral_eq_of_ae_rademacherVector
      (ae_norm_ofReal_eq_one.mono fun σ h => (h i).2))
    (m₄ := 1) (fun i => integral_eq_of_ae_rademacherVector
      (ae_norm_ofReal_eq_one.mono fun σ h => by rw [(h i).1, one_pow])) A]
  simp only [hdiag, norm_zero, norm_one, one_pow, one_mul, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, Finset.sum_const_zero, mul_zero, add_zero, frobNorm_sq_eq_sum,
    frobInner_eq_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [A, Matrix.of_apply, Matrix.transpose_apply]
  by_cases hc : i ≠ j ∧ h i = h j
  · have hc' : j ≠ i ∧ h j = h i := ⟨hc.1.symm, hc.2.symm⟩
    rw [if_pos hc, if_pos hc', if_pos hc]
  · have hc' : ¬(j ≠ i ∧ h j = h i) := fun h' => hc ⟨h'.1.symm, h'.2.symm⟩
    rw [if_neg hc, if_neg hc', if_neg hc]
    simp

/-- The off-diagonal sum in closed form:
$$\sum_{i \ne j} \bigl(\lvert \mathbf{M}_{i,j} \rvert^2 +
\operatorname{Re}(\overline{\mathbf{M}_{i,j}}\mathbf{M}_{j,i})\bigr) =
\|\mathbf{M}\|_{\mathsf{F}}^2 + \langle \mathbf{M}, \mathbf{M}^{\mathsf{T}} \rangle_{\mathsf{F}} -
2 \sum_i \lvert \mathbf{M}_{i,i} \rvert^2\,.$$ -/
private theorem sum_sum_ite_ne [DecidableEq n] (M : Matrix n n 𝕜) :
    ∑ i, ∑ j, (if i ≠ j then ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) else 0) =
      frobNorm M ^ 2 + frobInner M Mᵀ - 2 * ∑ i, ‖M i i‖ ^ 2 := by
  have hd (i : n) : ‖M i i‖ ^ 2 + RCLike.re (star (M i i) * M i i) = 2 * ‖M i i‖ ^ 2 := by
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
    ring
  have e (i j : n) : (if i ≠ j then ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) else 0) =
      ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) -
        if i = j then ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) else 0 := by
    split_ifs <;> simp_all
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hd,
    Finset.sum_add_distrib, frobNorm_sq_eq_sum, frobInner_eq_sum, Matrix.transpose_apply,
    ← Finset.mul_sum]

/-- **The second moment of a CountSketch**: for every $\mathbf{M}$,
$$\mathbb{E}\lvert \operatorname{tr}(\mathbf{M}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}))
\rvert^2 = \frac{\|\mathbf{M}\|_{\mathsf{F}}^2 + \langle \mathbf{M}, \mathbf{M}^{\mathsf{T}}
\rangle_{\mathsf{F}} - 2 \sum_i \lvert \mathbf{M}_{i,i} \rvert^2}{\lvert k \rvert}\,.$$
[CamanoEpperlyMeyerTropp2025, Lemma B.1 and its proof] (there for self-adjoint $\mathbf{M}$, the
uncentred moment $\mathbb{E}[\operatorname{tr}(\mathbf{M}\mathbf{\Phi}\mathbf{\Phi}^*)^2]$, which
adds $(\operatorname{tr}\mathbf{M})^2$; the exact expression is in the proof, the statement is
the bound $(\operatorname{tr}\mathbf{M})^2 + 2\|\mathbf{M}\|_{\mathsf{F}}^2/b$ for $b$ rows).
Here centred, any $\mathbf{M}$, any field. For a fixed hash,
$\operatorname{tr}(\mathbf{M}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}))$ is a hollow
Rademacher quadratic form (`NLAlib.integral_norm_quadForm_sub_trace_sq` at $s = 1$, $m_4 = 1$),
and the collision probability `NLAlib.measureReal_pi_samplingMeasure_setOf_apply_eq_apply`
averages the hash.
Result: countsketch-second-moment -/
theorem integral_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    [DecidableEq n] (hS : HasLaw S (countSketch k n) μ) (M : Matrix n n 𝕜) :
    ∫ ω, ‖(M * ((S ω)ᴴ * S ω - 1)).trace‖ ^ 2 ∂μ =
      (frobNorm M ^ 2 + frobInner M Mᵀ - 2 * ∑ i, ‖M i i‖ ^ 2) / Fintype.card k := by
  let _ : MeasurableSpace k := ⊤
  have hint (i j : n) : ∫ h, (if i ≠ j ∧ h i = h j then
      ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) else 0) ∂hashLaw k n =
      (Fintype.card k : ℝ)⁻¹ *
        if i ≠ j then ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) else 0 := by
    by_cases hij : i = j
    · simp [hij]
    · have hs : MeasurableSet {h : n → k | h i = h j} :=
        measurableSet_eq_fun (measurable_pi_apply i) (measurable_pi_apply j)
      have e : (fun h : n → k => if i ≠ j ∧ h i = h j then
          ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) else 0) =
          {h : n → k | h i = h j}.indicator
            fun _ => ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) := by
        ext h
        simp [Set.indicator_apply, hij]
      rw [e, integral_indicator_const _ hs, measureReal_hashLaw_setOf_apply_eq_apply hij,
        if_pos hij, smul_eq_mul]
  refine (integral_comp_of_hasLaw_countSketch hS
    (f := fun A : Matrix k n 𝕜 => ‖(M * (Aᴴ * A - 1)).trace‖ ^ 2) (by fun_prop)).trans ?_
  simp only [integral_norm_trace_mul_countSketchMatrix_sq]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => Integrable.of_finite]
  simp only [fun i => integral_finsetSum (μ := hashLaw k n) _
    fun j (_ : j ∈ Finset.univ) => Integrable.of_finite (f := fun h : n → k =>
      if i ≠ j ∧ h i = h j then ‖M i j‖ ^ 2 + RCLike.re (star (M i j) * M j i) else 0), hint,
    inv_mul_eq_div]
  rw [← sum_sum_ite_ne, Finset.sum_div]
  simp only [Finset.sum_div]

/-! ### Approximate matrix multiplication -/

section AMM

variable [Fintype q] [Fintype r]

/-- The squared error of approximate matrix multiplication with a CountSketch is integrable. -/
theorem integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2) μ :=
  integrable_comp_of_hasLaw_countSketch hS
    (f := fun T : Matrix k n 𝕜 => frobNorm (Aᴴ * Tᴴ * T * B - Aᴴ * B) ^ 2)
    ((continuous_frobNorm.comp (by fun_prop)).pow 2)

omit [DecidableEq k] [Fintype q] [Fintype r] in
/-- Entry $(a, b)$ of the AMM error is the trace of the rank-one matrix with entries
$\mathbf{B}_{j,b}\overline{\mathbf{A}_{i,a}}$ against the Gram error. -/
private theorem conjTranspose_mul_sub_apply_eq_trace [DecidableEq n] (A : Matrix n q 𝕜)
    (B : Matrix n r 𝕜) (T : Matrix k n 𝕜) (a : q) (b : r) :
    (Aᴴ * Tᴴ * T * B - Aᴴ * B) a b =
      ((Matrix.of fun j i => B j b * star (A i a)) * (Tᴴ * T - 1)).trace := by
  have e : Aᴴ * Tᴴ * T * B - Aᴴ * B = Aᴴ * (Tᴴ * T - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.mul_assoc Aᴴ Tᴴ T]
  rw [e, Matrix.trace]
  simp only [Matrix.mul_apply, Matrix.diag, Matrix.of_apply, Matrix.conjTranspose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

omit [Fintype k] [DecidableEq k] in
/-- The first term of the AMM identity: the rank-one matrices have total squared Frobenius norm
$\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2$. -/
private theorem sum_sum_frobNorm_of_mul_star_sq (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    ∑ a, ∑ b, frobNorm (Matrix.of fun j i => B j b * star (A i a)) ^ 2 =
      frobNorm A ^ 2 * frobNorm B ^ 2 := by
  have hA : frobNorm A ^ 2 = ∑ a, ∑ i, ‖A i a‖ ^ 2 := by rw [frobNorm_sq_eq_sum, Finset.sum_comm]
  have hB : frobNorm B ^ 2 = ∑ b, ∑ j, ‖B j b‖ ^ 2 := by rw [frobNorm_sq_eq_sum, Finset.sum_comm]
  have h (a : q) (b : r) : frobNorm (Matrix.of fun j i => B j b * star (A i a)) ^ 2 =
      (∑ j, ‖B j b‖ ^ 2) * ∑ i, ‖A i a‖ ^ 2 := by
    rw [frobNorm_sq_eq_sum, Finset.sum_mul_sum]
    simp only [Matrix.of_apply, norm_mul, norm_star, mul_pow]
  rw [hA, hB]
  simp only [h, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

omit [Fintype k] [DecidableEq k] in
/-- The second term of the AMM identity: the transpose pairings of the rank-one matrices sum to
$\|\mathbf{A}^{\mathsf{T}}\mathbf{B}\|_{\mathsf{F}}^2$. -/
private theorem sum_sum_frobInner_of_mul_star_transpose (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    ∑ a, ∑ b, frobInner (Matrix.of fun j i => B j b * star (A i a))
      (Matrix.of fun j i => B j b * star (A i a))ᵀ = frobNorm (Aᵀ * B) ^ 2 := by
  have hz (z : 𝕜) : ‖z‖ ^ 2 = RCLike.re (star z * z) := by
    rw [RCLike.star_def, RCLike.conj_mul, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [frobNorm_sq_eq_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [frobInner_eq_sum, hz, Matrix.mul_apply, star_sum, Finset.sum_mul_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  simp only [Matrix.of_apply, Matrix.transpose_apply, star_mul', star_star]
  ring

omit [Fintype k] [DecidableEq k] in
/-- The third term of the AMM identity: the squared diagonals of the rank-one matrices sum to
$\sum_i \|\mathbf{a}_i\|^2 \|\mathbf{b}_i\|^2$. -/
private theorem sum_sum_sum_norm_of_mul_star_apply_sq (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    ∑ a, ∑ b, ∑ i, ‖(Matrix.of fun j i => B j b * star (A i a) : Matrix n n 𝕜) i i‖ ^ 2 =
      ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 := by
  simp only [Matrix.of_apply, norm_mul, norm_star, mul_pow, EuclideanSpace.norm_sq_eq,
    Finset.sum_mul_sum]
  calc ∑ a, ∑ b, ∑ i, ‖B i b‖ ^ 2 * ‖A i a‖ ^ 2
      = ∑ a, ∑ i, ∑ b, ‖A i a‖ ^ 2 * ‖B i b‖ ^ 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => mul_comm _ _
    _ = ∑ i, ∑ a, ∑ b, ‖A i a‖ ^ 2 * ‖B i b‖ ^ 2 := Finset.sum_comm

/-- **AMM with a CountSketch, exact second moment**:
$$\mathbb{E}\|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}^2
= \frac{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2 +
\|\mathbf{A}^{\mathsf{T}}\mathbf{B}\|_{\mathsf{F}}^2 -
2\sum_i \|\mathbf{a}_i\|^2 \|\mathbf{b}_i\|^2}{\lvert k \rvert}$$
for the rows $\mathbf{a}_i$, $\mathbf{b}_i$ of $\mathbf{A}$, $\mathbf{B}$. Proved without a
literature source; Woodruff's proof of Theorem 14 computes its case
$\mathbf{A} = \mathbf{B} = \mathbf{x}$ over $\mathbb{R}$. Entry $(a, b)$ of the error is
$\operatorname{tr}(\mathbf{M}_{ab}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}))$ for the
rank-one $\mathbf{M}_{ab}$ with entries $\mathbf{B}_{j,b}\overline{\mathbf{A}_{i,a}}$, and the
exact second moment is summed over $(a, b)$.
Result: amm-countsketch -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ =
      (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (Aᵀ * B) ^ 2 -
        2 * ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2) / Fintype.card k := by
  classical
  have e (ω : Ω) : frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 =
      ∑ a, ∑ b,
        ‖((Matrix.of fun j i => B j b * star (A i a)) * ((S ω)ᴴ * S ω - 1)).trace‖ ^ 2 := by
    rw [frobNorm_sq_eq_sum]
    simp only [conjTranspose_mul_sub_apply_eq_trace]
  have hI (a : q) (b : r) :=
    integrable_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch hS
      (Matrix.of fun j i => B j b * star (A i a))
  simp only [e]
  rw [integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => hI a b]
  simp only [fun a => integral_finsetSum (μ := μ) _ fun b (_ : b ∈ Finset.univ) => hI a b,
    integral_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch hS]
  rw [← sum_sum_frobNorm_of_mul_star_sq, ← sum_sum_frobInner_of_mul_star_transpose,
    ← sum_sum_sum_norm_of_mul_star_apply_sq, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]

/-- **AMM with a CountSketch**, the bound
$$\mathbb{E}\|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}^2
\le \frac{2\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2}{\lvert k \rvert}\,,$$
over any field. [Woodruff2014, Theorems 13 and 14] (there $3\varepsilon$ through the JL moment,
over $\mathbb{R}$).
Result: amm-countsketch -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ ≤
      2 * frobNorm A ^ 2 * frobNorm B ^ 2 / Fintype.card k := by
  rw [integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS A B]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  have h1 : frobNorm (Aᵀ * B) ^ 2 ≤ frobNorm A ^ 2 * frobNorm B ^ 2 := by
    rw [← mul_pow, ← frobNorm_transpose A]
    exact pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_mul_le _ _) 2
  have h2 : 0 ≤ ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2 := by positivity
  linarith

/-- **AMM with a CountSketch, tail form**: for $\varepsilon > 0$ and nonzero $\mathbf{A}$,
$\mathbf{B}$,
$$\mathbb{P}\bigl(\varepsilon \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}
\le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}\bigr)
\le \frac{2}{\lvert k \rvert \varepsilon^2}\,.$$
S1's AMM route (`NLAlib.HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le` at
`NLAlib.hasJLMoment_of_hasLaw_countSketch`) is over $\mathbb{R}$ only, where it gives the same
$2/(\lvert k \rvert \varepsilon^2)$; the direct identity is the only AMM for a complex
CountSketch, and is a factor $2$ better in the failure probability than the
$\sqrt{2}\,\varepsilon$ form S1 would state. [Woodruff2014, Theorem 13] (there $3\varepsilon$,
over $\mathbb{R}$). -/
theorem measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (hε : 0 < ε) {A : Matrix n q 𝕜} {B : Matrix n r 𝕜}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤
      2 / (Fintype.card k * ε ^ 2) := by
  have ha : 0 < frobNorm A :=
    lt_of_le_of_ne (frobNorm_nonneg _) (Ne.symm (mt frobNorm_eq_zero_iff.1 hA))
  have hb : 0 < frobNorm B :=
    lt_of_le_of_ne (frobNorm_nonneg _) (Ne.symm (mt frobNorm_eq_zero_iff.1 hB))
  have ht : 0 < ε * frobNorm A * frobNorm B := by positivity
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  calc μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)}
      ≤ μ.real {ω | (ε * frobNorm A * frobNorm B) ^ 2 ≤
          frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2} :=
        measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω => pow_le_pow_left₀ ht.le hω 2)
    _ ≤ (∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ) /
          (ε * frobNorm A * frobNorm B) ^ 2 :=
        measureReal_ge_le_integral_div (ae_of_all _ fun _ => sq_nonneg _)
          (integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS A B)
          (pow_pos ht 2)
    _ ≤ (2 * frobNorm A ^ 2 * frobNorm B ^ 2 / Fintype.card k) /
          (ε * frobNorm A * frobNorm B) ^ 2 :=
        div_le_div_of_nonneg_right
          (integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_countSketch hS A B)
          (sq_nonneg _)
    _ = 2 / (Fintype.card k * ε ^ 2) := by
        rcases eq_or_ne (Fintype.card k : ℝ) 0 with hk | hk
        · simp [hk]
        · field_simp

end AMM

/-! ### The Gram error and the embedding -/

section Gram

variable [Fintype r] [DecidableEq r] {U : Matrix n r 𝕜}

omit [DecidableEq k] [Fintype r] [DecidableEq r] in
/-- The sketched Gram matrix, expanded. -/
private theorem conjTranspose_mul_mul_self_eq (A : Matrix k n 𝕜) (U : Matrix n r 𝕜) :
    (A * U)ᴴ * (A * U) = Uᴴ * Aᴴ * A * U := by
  rw [Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- The squared Gram error of a CountSketch on the columns of any $\mathbf{U}$ is integrable. -/
theorem integrable_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (U : Matrix n r 𝕜) :
    Integrable (fun ω => frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  have hX := integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS U U
  refine ((hX.const_mul 2).add (integrable_const (2 * frobNorm (Uᴴ * U - 1) ^ 2))).mono' ?_ ?_
  · have hc : Continuous fun A : Matrix k n 𝕜 => frobNorm ((A * U)ᴴ * (A * U) - 1) ^ 2 :=
      (continuous_frobNorm.comp (by fun_prop)).pow 2
    exact (hc.measurable.comp_aemeasurable hS.aemeasurable).aestronglyMeasurable
  · refine ae_of_all _ fun ω => ?_
    have e : (S ω * U)ᴴ * (S ω * U) - 1 =
        (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U) + (Uᴴ * U - 1) := by
      rw [conjTranspose_mul_mul_self_eq]
      abel
    have h := frobNorm_add_le (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U) (Uᴴ * U - 1)
    have h0 := frobNorm_nonneg (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U)
    have h1 := frobNorm_nonneg (Uᴴ * U - 1)
    have hsq := pow_le_pow_left₀ (frobNorm_nonneg _) h 2
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), e, Pi.add_apply]
    nlinarith [sq_nonneg (frobNorm (Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U) - frobNorm (Uᴴ * U - 1))]

/-- **The exact mean of the squared Gram error** of a CountSketch for $\mathbf{U}$ with orthonormal
columns, $d = \lvert r \rvert$:
$$\mathbb{E}\|(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U} - \mathbf{I}\|_{\mathsf{F}}^2
= \frac{d^2 + \|\mathbf{U}^{\mathsf{T}}\mathbf{U}\|_{\mathsf{F}}^2 -
2 \sum_i \ell_i^2}{\lvert k \rvert}\,,$$
$\ell_i$ the leverage scores (`NLAlib.leverageScore`); over $\mathbb{R}$ the middle term is $d$.
The AMM identity at $\mathbf{A} = \mathbf{B} = \mathbf{U}$. Proved without a literature source.
Result: countsketch-second-moment -/
theorem HasOrthonormalCols.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    (hU : HasOrthonormalCols U) (hS : HasLaw S (countSketch k n) μ) :
    ∫ ω, frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2 ∂μ =
      ((Fintype.card r : ℝ) ^ 2 + frobNorm (Uᵀ * U) ^ 2 - 2 * ∑ i, leverageScore U i ^ 2) /
        Fintype.card k := by
  have e (ω : Ω) : (S ω * U)ᴴ * (S ω * U) - 1 = Uᴴ * (S ω)ᴴ * S ω * U - Uᴴ * U := by
    rw [conjTranspose_mul_mul_self_eq, show Uᴴ * U = 1 from hU]
  have hl (i : n) : ‖WithLp.toLp 2 (U i)‖ ^ 2 * ‖WithLp.toLp 2 (U i)‖ ^ 2 =
      leverageScore U i ^ 2 := by
    rw [hU.leverageScore_eq]
    ring
  simp only [e]
  rw [integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS U U,
    hU.frobNorm_sq]
  simp only [hl]
  ring

/-- **The trace moment of a CountSketch** at $q = 1$: for $\mathbf{U}$ with orthonormal columns
and $d = \lvert r \rvert$,
$$\mathbb{E}\|(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U} - \mathbf{I}\|_{\mathsf{F}}^2
\le \frac{d^2 + d}{\lvert k \rvert}\,.$$
[Woodruff2014, Theorem 9 and the discussion following it] (the
proof of Meng and Mahoney and of Nelson and Nguyen, as Woodruff describes it). The exact mean
with $\|\mathbf{U}^{\mathsf{T}}\mathbf{U}\|_{\mathsf{F}}^2 \le d$. -/
theorem hasGramTraceMoment_of_hasLaw_countSketch (hS : HasLaw S (countSketch k n) μ)
    (hU : HasOrthonormalCols U) :
    HasGramTraceMoment S U 1 (((Fintype.card r : ℝ) ^ 2 + Fintype.card r) / Fintype.card k) μ := by
  have e (ω : Ω) : RCLike.re (((S ω * U)ᴴ * (S ω * U) - 1) ^ (2 * 1)).trace =
      frobNorm ((S ω * U)ᴴ * (S ω * U) - 1) ^ 2 := by
    have hH : ((S ω * U)ᴴ * (S ω * U) - 1).IsHermitian :=
      (Matrix.isHermitian_conjTranspose_mul_self _).sub Matrix.isHermitian_one
    rw [frobNorm_sq_eq_re_trace, hH.eq, mul_one, sq]
  refine ⟨?_, ?_⟩
  · simp only [e]
    exact integrable_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch hS U
  · simp only [e]
    rw [hU.integral_frobNorm_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch hS]
    refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
    have h1 : frobNorm (Uᵀ * U) ^ 2 ≤ Fintype.card r := by
      rw [← hU.frobNorm_sq]
      have h := frobNorm_mul_le_specNorm_mul_frobNorm Uᵀ U
      rw [specNorm_transpose] at h
      exact pow_le_pow_left₀ (frobNorm_nonneg _)
        (h.trans (mul_le_of_le_one_left (frobNorm_nonneg _) hU.specNorm_le_one)) 2
    have h2 : 0 ≤ ∑ i, leverageScore U i ^ 2 := by positivity
    linarith

end Gram

/-- **CountSketch OSE**: for $\varepsilon > 0$, a CountSketch is an oblivious subspace embedding
for dimension $d$ with constants $1 \mp \varepsilon$ and failure probability
$$\frac{d^2 + d}{\lvert k \rvert \varepsilon^2}\,.$$
[Woodruff2014, Theorem 9] (there $O(d^2/(\delta\varepsilon^2))$ rows, after Meng and Mahoney and
Nelson and Nguyen; Woodruff's own route through Theorems 13 and 14 reaches
$18 d^2/(\delta\varepsilon^2)$). The constant is the proof's; the second-moment route is Meng and
Mahoney 2013 and Nelson and Nguyen 2013 (Woodruff, Theorem 9), neither in hand, so the constant is
not attributed.
Result: sparse-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_countSketch (hS : HasLaw S (countSketch k n) μ)
    (d : ℕ) (hε : 0 < ε) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2)) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  have h := isObliviousSubspaceEmbedding_of_hasGramTraceMoment (S := S)
    (p := Fin (min d (Fintype.card n))) (q := 1)
    (by rw [Fintype.card_fin]; exact min_le_right _ _)
    (fun U hU => hasGramTraceMoment_of_hasLaw_countSketch hS hU) hε
  intro U hU
  refine (h U ?_).mono le_rfl le_rfl ?_
  · rw [Fintype.card_fin]
    exact le_min hU (Matrix.rank_le_card_width U)
  · have hc : ((min d (Fintype.card n) : ℕ) : ℝ) ≤ d := Nat.cast_le.2 (min_le_left _ _)
    rw [Fintype.card_fin, mul_one, div_div]
    exact div_le_div_of_nonneg_right (by gcongr) (by positivity)

/-- **CountSketch OSI**: for $\varepsilon > 0$ and nonempty `k`, a CountSketch is an oblivious
subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure probability
$(d^2 + d)/(\lvert k \rvert \varepsilon^2)$: the lower half of the OSE, with isotropy.
[CamanoEpperlyMeyerTropp2025, Definition 1.2] for the notion; their Table 3 lists CountSketch only
as an OSE, with $k = O(r^2)$.
Result: countsketch-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_countSketch [Nonempty k] [DecidableEq n]
    (hS : HasLaw S (countSketch k n) μ) (d : ℕ) (hε : 0 < ε) :
    IsObliviousSubspaceInjection S d (1 - ε) (((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2)) μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  exact (isObliviousSubspaceEmbedding_of_hasLaw_countSketch hS d hε).isObliviousSubspaceInjection
    (isIsotropicSketch_of_hasLaw_countSketch hS)

omit [DecidableEq k] in
/-- The Gram entry of a one-column matrix is the squared norm of its column. -/
private theorem conjTranspose_replicateCol_mul_self_apply {m : Type*} [Fintype m] (v : m → 𝕜) :
    ((Matrix.replicateCol Unit v)ᴴ * Matrix.replicateCol Unit v) () () =
      ((‖WithLp.toLp 2 v‖ ^ 2 : ℝ) : 𝕜) := by
  rw [Matrix.mul_apply, EuclideanSpace.norm_sq_eq]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_apply, Matrix.replicateCol_apply, RCLike.star_def, RCLike.conj_mul]

omit [DecidableEq k] in
/-- At a one-column matrix $\mathbf{x}$, the AMM error is the distortion
$\|\mathbf{A}\mathbf{x}\|^2 - \|\mathbf{x}\|^2$. -/
private theorem frobNorm_replicateCol_sq (A : Matrix k n 𝕜) (x : n → 𝕜) :
    frobNorm ((Matrix.replicateCol Unit x)ᴴ * Aᴴ * A * Matrix.replicateCol Unit x -
      (Matrix.replicateCol Unit x)ᴴ * Matrix.replicateCol Unit x) ^ 2 =
      |‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 - ‖WithLp.toLp 2 x‖ ^ 2| ^ 2 := by
  have e : (Matrix.replicateCol Unit x)ᴴ * Aᴴ * A * Matrix.replicateCol Unit x =
      (Matrix.replicateCol Unit (A *ᵥ x))ᴴ * Matrix.replicateCol Unit (A *ᵥ x) := by
    rw [Matrix.replicateCol_mulVec, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  rw [e, frobNorm_sq_eq_sum, Fintype.sum_unique, Fintype.sum_unique, Matrix.sub_apply,
    conjTranspose_replicateCol_mul_self_apply, conjTranspose_replicateCol_mul_self_apply,
    ← RCLike.ofReal_sub, RCLike.norm_ofReal]

/-- **CountSketch JL moment** at $p = 2$ with $\delta = 2/(\lvert k \rvert \varepsilon^2)$, any
field: $\mathbb{E}(\|\mathbf{S}\mathbf{x}\|^2 - 1)^2 \le 2/\lvert k \rvert$ for unit
$\mathbf{x}$, the AMM bound at a one-column matrix. [Woodruff2014, Theorem 14] (after Thorup and
Zhang, not in hand; over $\mathbb{R}$, there in size form).
Result: countsketch-jl-moment -/
theorem hasJLMoment_of_hasLaw_countSketch (hS : HasLaw S (countSketch k n) μ) (hε : 0 < ε) :
    HasJLMoment S ε (2 / (Fintype.card k * ε ^ 2)) 2 μ := by
  have e (x : n → 𝕜) (hx : ‖WithLp.toLp 2 x‖ = 1) (ω : Ω) :
      |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1| ^ (2 : ℝ) =
        frobNorm ((Matrix.replicateCol Unit x)ᴴ * (S ω)ᴴ * S ω * Matrix.replicateCol Unit x -
          (Matrix.replicateCol Unit x)ᴴ * Matrix.replicateCol Unit x) ^ 2 := by
    rw [Real.rpow_two, frobNorm_replicateCol_sq, hx, one_pow]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · simp only [e x hx]
    exact integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch hS _ _
  · simp only [e x hx]
    have hX : frobNorm (Matrix.replicateCol Unit x) ^ 2 = 1 := by
      rw [frobNorm_sq_eq_re_trace, Matrix.trace, Fintype.sum_unique, Matrix.diag_apply,
        conjTranspose_replicateCol_mul_self_apply, RCLike.ofReal_re, hx, one_pow]
    refine (integral_frobNorm_conjTranspose_mul_sub_sq_le_of_hasLaw_countSketch hS _ _).trans
      (le_of_eq ?_)
    rw [hX, Real.rpow_two]
    rcases eq_or_ne (Fintype.card k : ℝ) 0 with hk | hk
    · simp [hk]
    · field_simp

/-! ### Sizes -/

/-- The **CountSketch rows** <!-- value countSketchRows d \varepsilon \delta -->
$(d^2 + d)/(\delta \varepsilon^2)$<!-- /value -->: a CountSketch with at least this
many rows is an OSE (and, with a row, an OSI) for dimension $d$ with constants $1 \mp \varepsilon$
and failure probability $\delta$
(`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchRows_le`). The value the
proof reaches; [Woodruff2014, Theorem 9] has $O(d^2/(\delta\varepsilon^2))$ with no constant.
Consumers use `NLAlib.countSketchRows_le`. Junk value: $0$ at $\varepsilon = 0$ or
$\delta = 0$. -/
noncomputable irreducible_def countSketchRows (d : ℕ) (ε δ : ℝ) : ℝ :=
  ((d : ℝ) ^ 2 + d) / (δ * ε ^ 2)

/-- The number of CountSketch rows is nonnegative for $\delta \ge 0$. -/
theorem countSketchRows_nonneg (d : ℕ) (ε : ℝ) (hδ : 0 ≤ δ) : 0 ≤ countSketchRows d ε δ := by
  rw [countSketchRows_def]
  positivity

/-- The number of CountSketch rows is monotone in the dimension $d$ and antitone in the
distortion $\varepsilon > 0$ and the failure probability $\delta > 0$. -/
theorem countSketchRows_mono {d d' : ℕ} {ε' δ' : ℝ} (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε')
    (hδ : 0 < δ) (hδδ' : δ ≤ δ') : countSketchRows d ε' δ' ≤ countSketchRows d' ε δ := by
  rw [countSketchRows_def, countSketchRows_def]
  have hdd : (d : ℝ) ≤ d' := Nat.cast_le.2 hd
  exact div_le_div₀ (by positivity) (by gcongr) (by positivity)
    (mul_le_mul hδδ' (pow_le_pow_left₀ hε.le hεε' 2) (by positivity) (hδ.le.trans hδδ'))

/-- The explicit comparison of `NLAlib.countSketchRows d ε δ`, at present
<!-- value countSketchRows d \varepsilon \delta -->
$(d^2 + d)/(\delta \varepsilon^2)$<!-- /value -->, with
$(d^2 + d)/(\delta\varepsilon^2)$ that consumers invert with; an improved definition keeps it
true. -/
theorem countSketchRows_le (d : ℕ) (ε δ : ℝ) :
    countSketchRows d ε δ ≤ ((d : ℝ) ^ 2 + d) / (δ * ε ^ 2) := by
  rw [countSketchRows_def]

omit [DecidableEq k] in
/-- At least `NLAlib.countSketchRows d ε δ` rows (at present
<!-- value countSketchRows d \varepsilon \delta -->
$(d^2 + d)/(\delta \varepsilon^2)$<!-- /value -->) give the failure probability $\delta$. -/
private theorem div_card_mul_sq_le_of_countSketchRows_le {d : ℕ} (hε : 0 < ε) (hδ : 0 < δ)
    (hk : countSketchRows d ε δ ≤ Fintype.card k) :
    ((d : ℝ) ^ 2 + d) / (Fintype.card k * ε ^ 2) ≤ δ := by
  rw [countSketchRows_def] at hk
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp only [CharP.cast_eq_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, zero_div]
    exact hδ.le
  · have hd' : (0 : ℝ) < (d : ℝ) ^ 2 + d := by positivity
    have hm : (0 : ℝ) < Fintype.card k := (div_pos hd' (by positivity)).trans_le hk
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ (by positivity)] at hk
    nlinarith

/-- **CountSketch OSE, size form**: with at least `NLAlib.countSketchRows d ε δ` rows (at present
<!-- value countSketchRows d \varepsilon \delta -->
$(d^2 + d)/(\delta \varepsilon^2)$<!-- /value -->), for
$\varepsilon, \delta > 0$, a CountSketch is an oblivious subspace embedding for dimension $d$ with
constants $1 \mp \varepsilon$ and failure probability $\delta$. [Woodruff2014, Theorem 9] (there
$O(d^2/(\delta\varepsilon^2))$ rows). -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchRows_le
    (hS : HasLaw S (countSketch k n) μ) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : countSketchRows d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  exact (isObliviousSubspaceEmbedding_of_hasLaw_countSketch hS d hε).mono le_rfl le_rfl le_rfl
    (div_card_mul_sq_le_of_countSketchRows_le hε hδ hk)

/-- **CountSketch OSI, size form**: with at least `NLAlib.countSketchRows d ε δ` rows (at present
<!-- value countSketchRows d \varepsilon \delta -->
$(d^2 + d)/(\delta \varepsilon^2)$<!-- /value -->), for
$\varepsilon, \delta > 0$ and nonempty `k`, a CountSketch is an oblivious subspace injection for
dimension $d$ with constant $1 - \varepsilon$ and failure probability $\delta$. -/
theorem isObliviousSubspaceInjection_of_hasLaw_countSketch_of_countSketchRows_le [Nonempty k]
    [DecidableEq n] (hS : HasLaw S (countSketch k n) μ) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : countSketchRows d ε δ ≤ Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ := by
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  exact (isObliviousSubspaceInjection_of_hasLaw_countSketch hS d hε).mono le_rfl le_rfl
    (div_card_mul_sq_le_of_countSketchRows_le hε hδ hk)

/-- **CountSketch JL moment, size form**, Woodruff's Theorem 14 as stated: at least
$2/(\varepsilon^2\delta)$ rows give the $(\varepsilon, \delta, 2)$ JL moment, for
$\varepsilon, \delta > 0$. The source's formula, so not a named size. [Woodruff2014, Theorem 14]
(over $\mathbb{R}$). -/
theorem hasJLMoment_of_hasLaw_countSketch_of_le_card (hS : HasLaw S (countSketch k n) μ)
    (hε : 0 < ε) (hδ : 0 < δ) (hk : 2 / (ε ^ 2 * δ) ≤ Fintype.card k) :
    HasJLMoment S ε δ 2 μ := by
  have hm : (0 : ℝ) < Fintype.card k := (by positivity : (0 : ℝ) < 2 / (ε ^ 2 * δ)).trans_le hk
  refine (hasJLMoment_of_hasLaw_countSketch hS hε).mono le_rfl ?_ hε.le zero_le_two
    (by positivity)
  rw [div_le_iff₀ (by positivity)]
  rw [div_le_iff₀ (by positivity)] at hk
  nlinarith

end NLAlib
