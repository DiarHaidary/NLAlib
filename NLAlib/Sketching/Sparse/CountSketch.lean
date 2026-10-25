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
Its instances are the exact second moment of approximate matrix multiplication, here, and the exact
mean of the squared Gram error of an orthonormal $\mathbf{U}$ and the JL moment, in
`NLAlib/Sketching/Sparse/CountSketchEmbedding.lean`, which derives from them the trace moment at
$q = 1$ with bound $(d^2 + d)/\lvert k \rvert$, the oblivious subspace embedding and injection with
failure probability $(d^2 + d)/(\lvert k \rvert \varepsilon^2)$, and the sizes. The
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
$\varepsilon \ge 1$ the injection is vacuous and the bound is still true. Split at the boundary
"The Gram error and the embedding" into this file and
`NLAlib/Sketching/Sparse/CountSketchEmbedding.lean` (2026-10-16, LowRank S9). Design:
`docs/design/Sketching-S7.md` §3.2, §8.

## Main definitions

* `NLAlib.countSketchMatrix`: the sketch built from a given hash and signs.
* `NLAlib.countSketch`: its law for a uniform hash and Rademacher signs.

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

/-- From the user's own hash and signs: for i.i.d. uniform hash values $h$ and independent
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
$\mathbb{E}[\mathbf{\Phi}\mathbf{\Phi}^{\mathsf{H}}] = \mathbf{I}$). -/
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
    (fun i => integral_eq_const
      (ae_norm_ofReal_eq_one.mono fun σ h => by rw [(h i).1, one_pow]))
    (s := 1) (fun i => integral_eq_const
      (ae_norm_ofReal_eq_one.mono fun σ h => (h i).2))
    (m₄ := 1) (fun i => integral_eq_const
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
    by_cases h : i = j <;> simp [h]
  simp only [e, Finset.sum_sub_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true, hd,
    Finset.sum_add_distrib, frobNorm_sq_eq_sum, frobInner_eq_sum, Matrix.transpose_apply,
    ← Finset.mul_sum]

/-- **The second moment of a CountSketch**: for every $\mathbf{M}$,
$$\mathbb{E}\lvert \operatorname{tr}(\mathbf{M}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}))
\rvert^2 = \frac{\|\mathbf{M}\|_{\mathsf{F}}^2 + \langle \mathbf{M}, \mathbf{M}^{\mathsf{T}}
\rangle_{\mathsf{F}} - 2 \sum_i \lvert \mathbf{M}_{i,i} \rvert^2}{\lvert k \rvert}\,.$$
[CamanoEpperlyMeyerTropp2025, Lemma B.1 and its proof] (there for self-adjoint $\mathbf{M}$, the
uncentred moment
$\mathbb{E}[\operatorname{tr}(\mathbf{M}\mathbf{\Phi}\mathbf{\Phi}^{\mathsf{H}})^2]$, which adds
$(\operatorname{tr}\mathbf{M})^2$; the exact expression is in the proof, the statement is
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
for the rows $\mathbf{a}_i$, $\mathbf{b}_i$ of $\mathbf{A}$, $\mathbf{B}$.
[Woodruff2014, proof of Theorem 14] computes its case $\mathbf{A} = \mathbf{B} = \mathbf{x}$ over
$\mathbb{R}$ (there as $\mathbb{E}\|\mathbf{S}\mathbf{x}\|^4$, then bounded); the general case is
proved here without a literature source. Entry $(a, b)$ of the error is
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
$$\mathbb{P}\bigl[\varepsilon \|\mathbf{A}\|_{\mathsf{F}} \|\mathbf{B}\|_{\mathsf{F}}
\le \|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}\bigr]
\le \frac{2}{\lvert k \rvert \varepsilon^2}\,.$$
S1's AMM route (`NLAlib.HasJLMoment.measureReal_frobNorm_conjTranspose_mul_sub_ge_le` at
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

end NLAlib
