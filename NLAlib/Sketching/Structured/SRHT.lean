/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Sketching.Properties.Isotropic
public import NLAlib.Sketching.Properties.Oblivious
public import NLAlib.Sketching.Sampling.RowSampling
public import NLAlib.Sketching.Sampling.WithoutReplacement
public import NLAlib.Sketching.Structured.Flattening

/-!
# The subsampled randomized trigonometric transform (SRHT)

For a bounded orthonormal transform $\mathbf{F}$ with constant $\beta$
(`NLAlib.IsBoundedOrthonormal F β`: the normalised Walsh–Hadamard or Fourier matrix at
$\beta = 1$, the cosine or Hartley transform at $\beta = 2$), independent random signs
$\boldsymbol{\xi}$ and $\lvert k \rvert$ row indices $\iota : k \to n$, the sketch is
$$\mathbf{S} = \sqrt{\lvert n \rvert / \lvert k \rvert}\; \mathbf{P}^{\mathsf{H}} \mathbf{F}
  \operatorname{diag}(\boldsymbol{\xi})\,,$$
$\mathbf{P}$ the selection matrix of $\iota$ (`NLAlib.srhtMatrix`). Its law is `NLAlib.srht k F`
when $\iota$ is a uniform injection (sampling without replacement, the classical SRHT) and
`NLAlib.srhtWithReplacement k F` when the indices are i.i.d. uniform. Both laws are pushforwards of
the primitive signs and indices with `⊤` on `n` inside the definition; `NLAlib.srht_eq_map_prod`
and `NLAlib.srhtWithReplacement_eq_map_prod` write them as the signs times the row-sampling laws,
and the bridges take a user's own signs and indices. The name `srht` is kept for every
$\mathbf{F}$ (the general term is SRTT).

The sketch is isotropic, without replacement a scaled partial isometry
($\mathbf{S}\mathbf{S}^{\mathsf{H}} = (\lvert n \rvert / \lvert k \rvert)\mathbf{I}$ almost surely),
and an oblivious subspace injection and embedding for dimension $d$ with failure probability
$$d\, e^{-\varepsilon^2 k / (2 L_d(t))} + \lvert n \rvert e^{-t}, \qquad
  2 d\, e^{-\varepsilon^2 k / (3 L_d(t))} + \lvert n \rvert e^{-t}, \qquad
  L_d(t) = \beta\,(d + 2\sqrt{d t} + 2t)\,,$$
for every $t \ge 0$: flattening (`NLAlib.Sketching.Structured.Flattening`) followed by uniform row
sampling (`NLAlib.Sketching.Sampling.RowSampling`, `NLAlib.Sketching.Sampling.WithoutReplacement`),
through the flatten-then-sample transfer. The sample sizes are the row-sampling sizes
`NLAlib.samplingSize` and `NLAlib.samplingInjectionSize`, at present
<!-- value samplingSize d L \varepsilon \delta -->
$3 L \log(2d/\delta)/\varepsilon^2$<!-- /value --> and
<!-- value samplingInjectionSize d L \varepsilon \delta -->
$2 L \log(d/\delta)/\varepsilon^2$<!-- /value -->, at
$L = \beta\,\mathrm{srhtRowBound}(\lvert n \rvert, d, \delta/2)$, with the failure split
$\delta/2 + \delta/2$.

The instances are hypothesis discharges, not separate theorems. The real Walsh OSE, for
`hS : HasLaw S (srht k (((√((2 : ℝ) ^ b))⁻¹ : ℝ) • walshHadamard ℝ b)) μ`:
```
isObliviousSubspaceEmbedding_of_hasLaw_srht (isBoundedOrthonormal_smul_walshHadamard b) hS d
  hε hε1 ht
```
and likewise `isBoundedOrthonormal_fourierMatrix n` for the Fourier transform over $\mathbb{C}$
with real signs, `Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul` for any Hadamard matrix.

Degenerate cases. For $\lvert n \rvert < \lvert k \rvert$ there is no injection, the law
`NLAlib.srht k F` is the zero measure, `HasLaw` forces $\mu = 0$ and every tail holds; so
$\lvert k \rvert \le \lvert n \rvert$ is assumed only on the probability instance, isotropy, the
injection (its isotropy field) and the injection's size form, never on an embedding or a tail.
Empty `k`: $\mathbf{S} = \mathbf{0}$, not isotropic, hence `[Nonempty k]` on isotropy and the
injections. Empty `n` with replacement: the law is $0$ for nonempty `k`, hence `[Nonempty n]` on
that model's isotropy and injections. $\lvert k \rvert = \lvert n \rvert$ without replacement:
$\mathbf{S}$ is unitary and every event is empty. Rank zero: every event is empty. Design:
`docs/design/Sketching-S6.md` §3.3, §8.

## Main definitions

* `NLAlib.srhtMatrix`: the sketch built from given signs and indices.
* `NLAlib.srht`, `NLAlib.srhtWithReplacement`: its laws.

## Main results

* `NLAlib.srht_eq_map_prod`, `NLAlib.srhtWithReplacement_eq_map_prod`,
  `NLAlib.hasLaw_srhtMatrix_of_hasLaw_uniformOn_injective`, `NLAlib.hasLaw_srhtMatrix_of_hasLaw_pi`:
  the laws through row sampling, and the bridges.
* `NLAlib.isIsotropicSketch_of_hasLaw_srht`,
  `NLAlib.isIsotropicSketch_of_hasLaw_srhtWithReplacement`: isotropy.
* `NLAlib.ae_mul_conjTranspose_eq_of_hasLaw_srht`, `NLAlib.ae_specNorm_eq_of_hasLaw_srht`: the
  scaled partial isometry.
* `NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht`,
  `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` and their with-replacement forms: the SRHT
  OSI and OSE.
* `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le`,
  `NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le` and their
  with-replacement forms: sample sizes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n : Type*} [Fintype k] [Fintype n] [DecidableEq n]
  {S : Ω → Matrix k n 𝕜} {F : Matrix n n 𝕜} {ξ : Ω → n → ℝ} {β ε t δ : ℝ}

/-! ### The sketch and its laws -/

/-- The **SRHT built from given signs and indices**:
$\sqrt{\lvert n \rvert / \lvert k \rvert}\, \mathbf{P}^{\mathsf{H}} \mathbf{F} \mathbf{D}$, with
$\mathbf{P}$ the selection matrix of $\iota$ and
$\mathbf{D} = \operatorname{diag}(\boldsymbol{\xi})$; row $j$ is
$\sqrt{\lvert n \rvert / \lvert k \rvert}$ times row $\iota(j)$ of $\mathbf{F}\mathbf{D}$.
The factor $\sqrt{\lvert n \rvert / \lvert k \rvert}\, \mathbf{P}^{\mathsf{H}}$ is
`NLAlib.samplingSketchMatrix` at uniform weights. Its laws are `NLAlib.srht` (a uniform injection)
and `NLAlib.srhtWithReplacement` (i.i.d. uniform indices). Halko, Martinsson and Tropp's test
matrix $\sqrt{n/\ell}\, \mathbf{D}\mathbf{F}\mathbf{R}$ acts on the right: it is
$\mathbf{S}^{\mathsf{H}}$ for their $\mathbf{F}^{\mathsf{H}}$ in place of $\mathbf{F}$, which
`NLAlib.IsBoundedOrthonormal.conjTranspose` carries across.
[MartinssonTropp2020, §9.3] (there $\sqrt{n/d}\, \mathbf{R}\mathbf{F}\mathbf{E}\mathbf{\Pi}$, no
permutation here); [HalkoMartinssonTropp2011, §4.6] (the SRFT, there with complex unimodular
$\mathbf{D}$); [Woodruff2014, Theorem 7]. -/
noncomputable def srhtMatrix (F : Matrix n n 𝕜) (ξ : n → ℝ) (ι : k → n) : Matrix k n 𝕜 :=
  samplingSketchMatrix (fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) ι * F *
    Matrix.diagonal fun i => (ξ i : 𝕜)

variable (k) in
/-- The **SRHT law**: the pushforward by `NLAlib.srhtMatrix F` of independent signs
(`NLAlib.rademacherVector n`) and an independent uniform injection $k \to n$ (sampling without
replacement). The measurable space on `n` is `⊤` inside the definition (no statement carries an
instance on `n`); `NLAlib.srht_eq_map_prod` writes it through the row-sampling law
`NLAlib.samplingSketchWithoutReplacement`. Junk value: the zero measure when
$\lvert n \rvert < \lvert k \rvert$. [Tropp2011a]; [HalkoMartinssonTropp2011, §11]. -/
noncomputable def srht (F : Matrix n n 𝕜) : Measure (Matrix k n 𝕜) :=
  let _ : MeasurableSpace n := ⊤
  ((rademacherVector n).prod (uniformOn {ι : k → n | Function.Injective ι})).map
    fun x => srhtMatrix F x.1 x.2

variable (k) in
/-- The **SRHT law with replacement**: the pushforward by `NLAlib.srhtMatrix F` of independent
signs and $\lvert k \rvert$ independent uniform indices. The measurable space on `n` is `⊤` inside
the definition; `NLAlib.srhtWithReplacement_eq_map_prod` writes it through the row-sampling law
`NLAlib.samplingSketch`. Junk value: the zero measure when `n` is empty and `k` is not.
[MartinssonTropp2020, §9.3]. -/
noncomputable def srhtWithReplacement (F : Matrix n n 𝕜) : Measure (Matrix k n 𝕜) :=
  let _ : MeasurableSpace n := ⊤
  ((rademacherVector n).prod
      (Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)).map
    fun x => srhtMatrix F x.1 x.2

/-- With `⊤` on `n`, the sketch is measurable in the signs and the indices jointly. -/
private theorem measurable_srhtMatrix (F : Matrix n n 𝕜) :
    let _ : MeasurableSpace n := ⊤
    Measurable fun x : (n → ℝ) × (k → n) => srhtMatrix F x.1 x.2 := by
  let _ : MeasurableSpace n := ⊤
  refine measurable_from_prod_countable_left fun ι => Continuous.measurable ?_
  unfold srhtMatrix
  fun_prop

omit [Fintype k] in
/-- The sketch built from signs and a sampling matrix is measurable in both. -/
private theorem measurable_mul_diagonal [Finite k] (F : Matrix n n 𝕜) :
    Measurable fun x : (n → ℝ) × Matrix k n 𝕜 => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜) :=
  (by fun_prop : Continuous _).measurable

omit [Fintype k] in
/-- Independent signs and a sampling matrix with law `ρ` give the pushforward of
`(rademacherVector n).prod ρ`. -/
private theorem hasLaw_mul_diagonal [Finite k] {ρ : Measure (Matrix k n 𝕜)} {P : Ω → Matrix k n 𝕜}
    (hξ : HasLaw ξ (rademacherVector n) μ) (hP : HasLaw P ρ μ) (hind : IndepFun ξ P μ) :
    HasLaw (fun ω => P ω * F * Matrix.diagonal fun i => (ξ ω i : 𝕜))
      (((rademacherVector n).prod ρ).map
        fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)) μ := by
  have : IsProbabilityMeasure μ := hξ.isProbabilityMeasure_iff.2 inferInstance
  exact (⟨(measurable_mul_diagonal F).aemeasurable, rfl⟩ : HasLaw
    (fun x : (n → ℝ) × Matrix k n 𝕜 => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)) _
    ((rademacherVector n).prod ρ)).comp (hind.hasLaw_prod hξ hP)

/-- The SRHT law is a finite measure. -/
instance isFiniteMeasure_srht (F : Matrix n n 𝕜) : IsFiniteMeasure (srht k F) := by
  unfold srht
  infer_instance

/-- The SRHT law with replacement is a finite measure. -/
instance isFiniteMeasure_srhtWithReplacement (F : Matrix n n 𝕜) :
    IsFiniteMeasure (srhtWithReplacement k F) := by
  unfold srhtWithReplacement
  infer_instance

/-- The SRHT law is a probability measure when $\lvert k \rvert \le \lvert n \rvert$. -/
theorem isProbabilityMeasure_srht (F : Matrix n n 𝕜) (hk : Fintype.card k ≤ Fintype.card n) :
    IsProbabilityMeasure (srht k F) := by
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_uniformOn_injective (k := k) (n := n) hk
  exact Measure.isProbabilityMeasure_map (measurable_srhtMatrix F).aemeasurable

/-- The SRHT law with replacement is a probability measure for nonempty `n`. -/
theorem isProbabilityMeasure_srhtWithReplacement [Nonempty n] (F : Matrix n n 𝕜) :
    IsProbabilityMeasure (srhtWithReplacement k F) := by
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_samplingMeasure (fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)
    NNReal.sum_const_inv_card
  exact Measure.isProbabilityMeasure_map (measurable_srhtMatrix F).aemeasurable

/-- **The SRHT law as signs times row sampling without replacement**: the pushforward of
independent signs and the law `NLAlib.samplingSketchWithoutReplacement k n` by
$(\boldsymbol{\xi}, \mathbf{P}) \mapsto \mathbf{P}\mathbf{F}\operatorname{diag}(\boldsymbol{\xi})$;
the form the proofs use. -/
theorem srht_eq_map_prod (F : Matrix n n 𝕜) :
    srht k F = ((rademacherVector n).prod (samplingSketchWithoutReplacement k n)).map
      fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜) := by
  let _ : MeasurableSpace n := ⊤
  have hP : Measurable (samplingSketchMatrix (𝕜 := 𝕜) (k := k)
      fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) := measurable_of_countable _
  have e1 : samplingSketchWithoutReplacement (𝕜 := 𝕜) k n =
      (uniformOn {ι : k → n | Function.Injective ι}).map
        (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹) := rfl
  have e2 : rademacherVector n = (rademacherVector n).map id := Measure.map_id.symm
  rw [e1]
  conv_rhs => rw [e2]
  rw [Measure.map_prod_map _ _ measurable_id hP,
    Measure.map_map (measurable_mul_diagonal F) (measurable_id.prodMap hP)]
  rfl

/-- **The SRHT law with replacement as signs times row sampling**: the pushforward of independent
signs and the law `NLAlib.samplingSketch k` at uniform weights by
$(\boldsymbol{\xi}, \mathbf{P}) \mapsto \mathbf{P}\mathbf{F}\operatorname{diag}(\boldsymbol{\xi})$;
the form the proofs use. -/
theorem srhtWithReplacement_eq_map_prod (F : Matrix n n 𝕜) :
    srhtWithReplacement k F =
      ((rademacherVector n).prod (samplingSketch k fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)).map
        fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜) := by
  let _ : MeasurableSpace n := ⊤
  have hP : Measurable (samplingSketchMatrix (𝕜 := 𝕜) (k := k)
      fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) := measurable_of_finite _
  have e1 : samplingSketch (𝕜 := 𝕜) k (fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) =
      (Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : ℝ≥0)⁻¹).map
        (samplingSketchMatrix fun _ => (Fintype.card n : ℝ≥0)⁻¹) := rfl
  have e2 : rademacherVector n = (rademacherVector n).map id := Measure.map_id.symm
  rw [e1]
  conv_rhs => rw [e2]
  rw [Measure.map_prod_map _ _ measurable_id hP,
    Measure.map_map (measurable_mul_diagonal F) (measurable_id.prodMap hP)]
  rfl

/-- **From the user's own signs and injection**: for independent signs $\boldsymbol{\xi}$ and a
uniform injection $\iota : k \to n$, under any measurable space on `n` with measurable
singletons, the sketch built from them has law `NLAlib.srht k F`. -/
theorem hasLaw_srhtMatrix_of_hasLaw_uniformOn_injective [MeasurableSpace n]
    [MeasurableSingletonClass n] {ι : Ω → k → n} (hξ : HasLaw ξ (rademacherVector n) μ)
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hind : IndepFun ξ ι μ) :
    HasLaw (fun ω => srhtMatrix F (ξ ω) (ι ω)) (srht k F) μ := by
  rw [srht_eq_map_prod]
  exact hasLaw_mul_diagonal hξ (hasLaw_samplingSketchMatrix_of_hasLaw_uniformOn_injective hι)
    (hind.comp (φ := id) (ψ := samplingSketchMatrix (𝕜 := 𝕜) fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)
      measurable_id (measurable_of_countable _))

/-- **From the user's own signs and indices**: for independent signs $\boldsymbol{\xi}$ and
independent i.i.d. uniform indices $\iota : k \to n$, under any measurable space on `n` with
measurable singletons, the sketch built from them has law `NLAlib.srhtWithReplacement k F`. -/
theorem hasLaw_srhtMatrix_of_hasLaw_pi [MeasurableSpace n] [MeasurableSingletonClass n]
    {ι : Ω → k → n} (hξ : HasLaw ξ (rademacherVector n) μ)
    (hι : HasLaw ι
      (Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) μ)
    (hind : IndepFun ξ ι μ) :
    HasLaw (fun ω => srhtMatrix F (ξ ω) (ι ω)) (srhtWithReplacement k F) μ := by
  rw [srhtWithReplacement_eq_map_prod]
  exact hasLaw_mul_diagonal hξ (hasLaw_samplingSketchMatrix hι)
    (hind.comp (φ := id) (ψ := samplingSketchMatrix (𝕜 := 𝕜) fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)
      measurable_id (measurable_of_countable _))

/-! ### Isotropy and the partial isometry -/

section Product

variable {ρ : Measure (Matrix k n 𝕜)}

omit [Fintype k] [DecidableEq n] in
/-- On the product space, the signs have the Rademacher law. -/
private theorem hasLaw_fst_prod [IsProbabilityMeasure ρ] :
    HasLaw Prod.fst (rademacherVector n) ((rademacherVector n).prod ρ) :=
  ⟨measurable_fst.aemeasurable, by rw [Measure.map_fst_prod, measure_univ, one_smul]⟩

omit [Fintype k] [DecidableEq n] in
/-- On the product space, the sampling matrix has law `ρ`. -/
private theorem hasLaw_snd_prod [IsProbabilityMeasure ρ] :
    HasLaw Prod.snd ρ ((rademacherVector n).prod ρ) :=
  ⟨measurable_snd.aemeasurable, by rw [Measure.map_snd_prod, measure_univ, one_smul]⟩

omit [Fintype k] in
/-- On the product space, the sampling matrix and the randomized transform are independent. -/
private theorem indepFun_snd_mul_diagonal [IsProbabilityMeasure ρ] (F : Matrix n n 𝕜) :
    IndepFun Prod.snd (fun x : (n → ℝ) × Matrix k n 𝕜 => F * Matrix.diagonal fun i => (x.1 i : 𝕜))
      ((rademacherVector n).prod ρ) :=
  (indepFun_prod (μ := rademacherVector n) (ν := ρ)
    (X := fun ξ : n → ℝ => F * Matrix.diagonal fun i => (ξ i : 𝕜)) (Y := id) (by fun_prop)
    measurable_id).symm

omit [Fintype k] in
/-- The randomized transform $\mathbf{F}\mathbf{D}$ is measurable in the signs. -/
private theorem measurable_mul_diagonal_fst [Finite k] (F : Matrix n n 𝕜) :
    Measurable fun x : (n → ℝ) × Matrix k n 𝕜 => F * Matrix.diagonal fun i => (x.1 i : 𝕜) :=
  (by fun_prop : Continuous _).measurable

omit [Fintype k] in
/-- The sketch on the product space has the pushforward law. -/
private theorem hasLaw_map_prod [Finite k] (F : Matrix n n 𝕜) :
    HasLaw (fun x : (n → ℝ) × Matrix k n 𝕜 => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜))
      (((rademacherVector n).prod ρ).map
        fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)) ((rademacherVector n).prod ρ) :=
  ⟨(measurable_mul_diagonal F).aemeasurable, rfl⟩

omit [Fintype k] in
/-- The sketch on the product space is the sampling matrix times the randomized transform. -/
private theorem mul_diagonal_eq (F : Matrix n n 𝕜) :
    (fun x : (n → ℝ) × Matrix k n 𝕜 => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)) =
      fun x => x.2 * (F * Matrix.diagonal fun i => (x.1 i : 𝕜)) :=
  funext fun _ => Matrix.mul_assoc _ _ _

/-- The pushforward of the signs and an independent isotropic sampling law is isotropic, for a
unitary $\mathbf{F}$. -/
private theorem isIsotropicSketch_map_prod [IsProbabilityMeasure ρ] (hF : HasOrthonormalCols F)
    (hρ : IsIsotropicSketch id ρ) :
    IsIsotropicSketch id (((rademacherVector n).prod ρ).map
      fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)) := by
  classical
  refine (hasLaw_map_prod (ρ := ρ) F).isIsotropicSketch_iff.1 ?_
  rw [mul_diagonal_eq]
  have hfst := hasLaw_fst_prod (ρ := ρ)
  have hT : IsIsotropicSketch (fun x : (n → ℝ) × Matrix k n 𝕜 =>
      F * Matrix.diagonal fun i => (x.1 i : 𝕜)) ((rademacherVector n).prod ρ) := by
    refine ⟨fun i j => ?_, ?_⟩
    · have hb : ∀ᵐ x ∂(rademacherVector n).prod ρ,
          ‖(F * Matrix.diagonal fun i => (x.1 i : 𝕜)) i j‖ ≤ ‖F i j‖ := by
        filter_upwards [ae_sq_eq_one_of_hasLaw_rademacherVector hfst] with x hx
        have h1 : |x.1 j| = 1 := by
          rw [← Real.sqrt_sq_eq_abs, show x.1 j ^ 2 = 1 from hx j, Real.sqrt_one]
        rw [Matrix.mul_diagonal, norm_mul, RCLike.norm_ofReal, h1, mul_one]
      exact MemLp.of_bound ((Continuous.matrix_elem (by fun_prop) i j).measurable
        |>.aestronglyMeasurable) _ hb
    · have h1 : (fun x : (n → ℝ) × Matrix k n 𝕜 => (F * Matrix.diagonal fun i => (x.1 i : 𝕜))ᴴ *
          (F * Matrix.diagonal fun i => (x.1 i : 𝕜))) =ᵐ[(rademacherVector n).prod ρ] fun _ => 1 :=
        ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector hF hfst
      rw [integral_congr_ae h1]
      simp
  exact (hasLaw_snd_prod.isIsotropicSketch_iff.2 hρ).mul hT (indepFun_snd_mul_diagonal F)

end Product

/-- **The SRHT is isotropic**: $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$ for a
unitary $\mathbf{F}$, nonempty `k` and $\lvert k \rvert \le \lvert n \rvert$.
$\mathbf{S} = \mathbf{P}\mathbf{T}$ with $\mathbf{P}$ row sampling without replacement and
$\mathbf{T} = \mathbf{F}\mathbf{D}$ (unitary almost surely) independent and isotropic
(`NLAlib.IsIsotropicSketch.mul`). [CamanoEpperlyMeyerTropp2025, §1.5.2]. -/
theorem isIsotropicSketch_of_hasLaw_srht [Nonempty k] (hF : HasOrthonormalCols F)
    (hS : HasLaw S (srht k F) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    IsIsotropicSketch S μ := by
  have := isProbabilityMeasure_samplingSketchWithoutReplacement (𝕜 := 𝕜) hk
  refine hS.isIsotropicSketch_iff.2 ?_
  rw [srht_eq_map_prod]
  exact isIsotropicSketch_map_prod hF
    (isIsotropicSketch_of_hasLaw_samplingSketchWithoutReplacement HasLaw.id hk)

/-- **The SRHT with replacement is isotropic**, for a unitary $\mathbf{F}$ and nonempty `k`,
`n`. [CamanoEpperlyMeyerTropp2025, §1.5.2]. -/
theorem isIsotropicSketch_of_hasLaw_srhtWithReplacement [Nonempty k] [Nonempty n]
    (hF : HasOrthonormalCols F) (hS : HasLaw S (srhtWithReplacement k F) μ) :
    IsIsotropicSketch S μ := by
  have hp := NNReal.sum_const_inv_card (ι := n)
  have := isProbabilityMeasure_samplingSketch (𝕜 := 𝕜) (k := k) hp
  refine hS.isIsotropicSketch_iff.2 ?_
  rw [srhtWithReplacement_eq_map_prod]
  exact isIsotropicSketch_map_prod hF (isIsotropicSketch_of_hasLaw_samplingSketch HasLaw.id hp
    fun _ => inv_pos.2 (Nat.cast_pos.2 Fintype.card_pos))

/-- **The SRHT is a scaled partial isometry**: for a unitary $\mathbf{F}$, almost surely
$\mathbf{S}\mathbf{S}^{\mathsf{H}} = (\lvert n \rvert / \lvert k \rvert)\, \mathbf{I}$. Without
replacement only: repeated rows break it. [HalkoMartinssonTropp2011, §11.1];
[MartinssonTropp2020, §9.3]. Almost surely the signs are $\pm 1$, so
$\mathbf{S}\mathbf{S}^{\mathsf{H}} = \mathbf{P}\mathbf{P}^{\mathsf{H}}$, and the sampled rows are
distinct (`NLAlib.samplingSketchMatrix_mul_conjTranspose_of_injective`). -/
theorem ae_mul_conjTranspose_eq_of_hasLaw_srht [DecidableEq k] (hF : HasOrthonormalCols F)
    (hS : HasLaw S (srht k F) μ) :
    ∀ᵐ ω ∂μ, S ω * (S ω)ᴴ = ((Fintype.card n : ℝ) / Fintype.card k) • (1 : Matrix k k 𝕜) := by
  have hset : MeasurableSet {A : Matrix k n 𝕜 |
      A * Aᴴ = ((Fintype.card n : ℝ) / Fintype.card k) • (1 : Matrix k k 𝕜)} :=
    (isClosed_eq (by fun_prop) continuous_const).measurableSet
  refine (hS.ae_iff (measurableSet_setOfPred.1 hset)).2 ?_
  rw [srht_eq_map_prod, ae_map_iff (measurable_mul_diagonal F).aemeasurable hset]
  have hP : ∀ᵐ P ∂(samplingSketchWithoutReplacement (𝕜 := 𝕜) k n),
      P * Pᴴ = ((Fintype.card n : ℝ) / Fintype.card k) • (1 : Matrix k k 𝕜) := by
    let _ : MeasurableSpace n := ⊤
    rw [samplingSketchWithoutReplacement_eq_map,
      ae_map_iff (measurable_of_countable _).aemeasurable hset]
    filter_upwards [ae_cond_mem (Set.toFinite {ι : k → n | Function.Injective ι}).measurableSet]
      with ι hι
    rw [samplingSketchMatrix_mul_conjTranspose_of_injective _ hι]
    ext i j
    rw [Matrix.diagonal_apply, Matrix.smul_apply, Matrix.one_apply]
    split_ifs
    · rw [NNReal.coe_inv, NNReal.coe_natCast, mul_inv, inv_inv, RCLike.real_smul_eq_coe_mul,
        mul_one, div_eq_inv_mul]
    · rw [smul_zero]
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hP, Measure.quasiMeasurePreserving_fst.ae
    (ae_sq_eq_one_of_hasLaw_rademacherVector HasLaw.id)] with x hx hs
  have hD : (Matrix.diagonal fun i => (x.1 i : 𝕜)) * (Matrix.diagonal fun i => (x.1 i : 𝕜))ᴴ =
      1 := by
    rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← sq,
      show x.1 i ^ 2 = 1 from hs i, RCLike.ofReal_one]
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Matrix.diagonal _), hD, Matrix.one_mul, ← Matrix.mul_assoc F,
    hF.mul_conjTranspose_self, Matrix.one_mul]
  exact hx

/-- **The spectral norm of the SRHT**: for a unitary $\mathbf{F}$, almost surely
$\|\mathbf{S}\|_2 = \sqrt{\lvert n \rvert / \lvert k \rvert}$ ($0$ for empty `k`). The bound
$\|\boldsymbol{\Omega}_2\|_2 \le \sqrt{n/\ell}$ of [HalkoMartinssonTropp2011, Theorem 11.2] and
[MartinssonTropp2020, Theorem 11.6]. -/
theorem ae_specNorm_eq_of_hasLaw_srht (hF : HasOrthonormalCols F) (hS : HasLaw S (srht k F) μ) :
    ∀ᵐ ω ∂μ, specNorm (S ω) = √(Fintype.card n / Fintype.card k : ℝ) := by
  classical
  filter_upwards [ae_mul_conjTranspose_eq_of_hasLaw_srht hF hS] with ω h
  rcases isEmpty_or_nonempty k with hk | hk
  · rw [Subsingleton.elim (S ω) 0, specNorm_eq_zero_iff.2 rfl, Fintype.card_eq_zero (α := k),
      Nat.cast_zero, div_zero, Real.sqrt_zero]
  rw [← Real.sqrt_sq (specNorm_nonneg (S ω)), ← specNorm_mul_conjTranspose_self, h,
    RCLike.real_smul_eq_coe_smul (K := 𝕜), specNorm_smul, specNorm_one, mul_one,
    RCLike.norm_ofReal, abs_of_nonneg (by positivity)]

/-! ### Oblivious subspace injections and embeddings -/

/-- With fewer members than samples, the probability space of the SRHT is zero. -/
private theorem eq_zero_of_hasLaw_srht (hS : HasLaw S (srht k F) μ)
    (hk : Fintype.card n < Fintype.card k) : μ = 0 := by
  have h0 : srht k F = 0 := by
    rw [srht_eq_map_prod]
    let _ : MeasurableSpace n := ⊤
    rw [samplingSketchWithoutReplacement_eq_map, uniformOn_injective_of_card_lt hk,
      Measure.map_zero, Measure.prod_zero, Measure.map_zero]
  exact (Measure.map_eq_zero_iff hS.aemeasurable).1 (hS.map_eq.trans h0)

/-- Every event has probability at most one under a sketch with the SRHT law: the space is a
probability space, or zero when $\lvert n \rvert < \lvert k \rvert$. -/
private theorem measureReal_le_one_of_hasLaw_srht (hS : HasLaw S (srht k F) μ) (s : Set Ω) :
    μ.real s ≤ 1 := by
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [eq_zero_of_hasLaw_srht hS hk, measureReal_zero_apply]
    exact zero_le_one
  · have := hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hk)
    exact measureReal_le_one

omit [DecidableEq n] in
/-- The sampling failure probability at the flattened bound of a subspace of rank $r \le d$ is at
most the one at dimension $d$. -/
private theorem rank_mul_exp_le {V : Matrix n n 𝕜} {r d : ℕ} {c K : ℝ} (hc : 0 < c)
    (hK : 0 ≤ K) (ht : 0 ≤ t) (hVr : V.rank ≤ r) (hrd : r ≤ d)
    (hl : ∀ i, leverageScore V i ≤ β * (r + 2 * √(r * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹) :
    V.rank * Real.exp (-ε ^ 2 * K / (c * (β * (r + 2 * √(r * t) + 2 * t)))) ≤
      d * Real.exp (-ε ^ 2 * K / (c * (β * (d + 2 * √(d * t) + 2 * t)))) := by
  rcases Nat.eq_zero_or_pos V.rank with h0 | hpos
  · rw [h0, Nat.cast_zero, zero_mul]
    positivity
  have hL := pos_of_leverageScore_le_mul_inv_card hl hpos
  have hB : 0 ≤ (r : ℝ) + 2 * √(r * t) + 2 * t := by positivity
  have hβ : 0 ≤ β := by
    by_contra h
    nlinarith [not_le.1 h]
  have hrd' : (r : ℝ) ≤ d := Nat.cast_le.2 hrd
  have hBB : (r : ℝ) + 2 * √(r * t) + 2 * t ≤ d + 2 * √(d * t) + 2 * t := by
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_right hrd' ht)
    linarith
  have hLL : β * ((r : ℝ) + 2 * √(r * t) + 2 * t) ≤ β * (d + 2 * √(d * t) + 2 * t) :=
    mul_le_mul_of_nonneg_left hBB hβ
  refine mul_le_mul (Nat.cast_le.2 (hVr.trans hrd)) (Real.exp_le_exp.2 ?_) (by positivity)
    (by positivity)
  rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_left (by positivity) (by positivity)
    (mul_le_mul_of_nonneg_left hLL hc.le)

section Product

variable {ρ : Measure (Matrix k n 𝕜)} {a b δ₁ : ℝ}

/-- **Flatten, then sample** on the product space (injection): the pushforward of the signs and
an independent sampling law `ρ` that injects every fixed subspace of rank at most
$\operatorname{rank}\mathbf{U}$ whose leverage scores are at most
$\beta\,(r + 2\sqrt{r t} + 2t) / \lvert n \rvert$, $r = \operatorname{rank}\mathbf{U}$. -/
private theorem hasSubspaceInjection_map_prod [IsProbabilityMeasure ρ]
    (hF : IsBoundedOrthonormal F β) (U : Matrix n n 𝕜) (hδ₁ : 0 ≤ δ₁) (ht : 0 ≤ t)
    (hsample : ∀ V : Matrix n n 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤
        β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹) →
      HasSubspaceInjection id V a δ₁ ρ) :
    HasSubspaceInjection id U a (δ₁ + Fintype.card n * Real.exp (-t))
      (((rademacherVector n).prod ρ).map
        fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)) := by
  have hfst := hasLaw_fst_prod (ρ := ρ)
  refine (hasLaw_map_prod (ρ := ρ) F).hasSubspaceInjection_iff.1 ?_
  rw [mul_diagonal_eq]
  exact hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le (indepFun_snd_mul_diagonal F)
    measurable_snd.aemeasurable (measurable_mul_diagonal_fst F).aemeasurable
    (ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector hF.hasOrthonormalCols hfst) hδ₁
    (fun V hV hl => hasLaw_snd_prod.hasSubspaceInjection_iff.2 (hsample V hV hl))
    (measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector hF hfst U ht)

/-- **Flatten, then sample** on the product space (embedding), as
`hasSubspaceInjection_map_prod`. -/
private theorem hasSubspaceEmbedding_map_prod [IsProbabilityMeasure ρ]
    (hF : IsBoundedOrthonormal F β) (U : Matrix n n 𝕜) (hδ₁ : 0 ≤ δ₁) (ht : 0 ≤ t)
    (hsample : ∀ V : Matrix n n 𝕜, V.rank ≤ U.rank →
      (∀ i, leverageScore V i ≤
        β * (U.rank + 2 * √(U.rank * t) + 2 * t) * (Fintype.card n : ℝ)⁻¹) →
      HasSubspaceEmbedding id V a b δ₁ ρ) :
    HasSubspaceEmbedding id U a b (δ₁ + Fintype.card n * Real.exp (-t))
      (((rademacherVector n).prod ρ).map
        fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜)) := by
  have hfst := hasLaw_fst_prod (ρ := ρ)
  refine (hasLaw_map_prod (ρ := ρ) F).hasSubspaceEmbedding_iff.1 ?_
  rw [mul_diagonal_eq]
  exact hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le (indepFun_snd_mul_diagonal F)
    measurable_snd.aemeasurable (measurable_mul_diagonal_fst F).aemeasurable
    (ae_hasOrthonormalCols_mul_diagonal_of_hasLaw_rademacherVector hF.hasOrthonormalCols hfst) hδ₁
    (fun V hV hl => hasLaw_snd_prod.hasSubspaceEmbedding_iff.2 (hsample V hV hl))
    (measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector hF hfst U ht)

end Product

/-- **The SRHT OSI**: for a bounded orthonormal $\mathbf{F}$ with constant $\beta$, nonempty `k`,
$\lvert k \rvert \le \lvert n \rvert$, $\varepsilon \ge 0$ and $t \ge 0$, the SRHT is an
oblivious subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure
probability
$$d \exp\Bigl(-\frac{\varepsilon^2 \lvert k \rvert}{2 \beta (d + 2\sqrt{d t} + 2t)}\Bigr) +
  \lvert n \rvert e^{-t}\,:$$
the lower matrix Chernoff half after flattening.
[CamanoEpperlyMeyerTropp2025, §1.5.2] (the OSI view; $k = \Omega(d \log d)$ is necessary, their
citation of Tropp 2011a); [Tropp2011a]. Flattening
(`NLAlib.measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector`), then
`NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement` through
`NLAlib.hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le`.
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srht [Nonempty k] (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) :
    IsObliviousSubspaceInjection S d (1 - ε)
      (d * Real.exp (-ε ^ 2 * Fintype.card k / (2 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  have := isProbabilityMeasure_samplingSketchWithoutReplacement (𝕜 := 𝕜) hk
  refine ⟨isIsotropicSketch_of_hasLaw_srht hF.hasOrthonormalCols hS hk, fun U hU => ?_⟩
  refine hS.hasSubspaceInjection_iff.2 ?_
  rw [srht_eq_map_prod]
  refine hasSubspaceInjection_map_prod hF U (by positivity) ht fun V hV hl => ?_
  exact (hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement HasLaw.id hl hε).mono
    le_rfl (rank_mul_exp_le two_pos (Nat.cast_nonneg _) ht hV hU hl)

/-- **The SRHT OSE**: for a bounded orthonormal $\mathbf{F}$ with constant $\beta$,
$0 \le \varepsilon \le 1$ and $t \ge 0$, the SRHT is an oblivious subspace embedding for
dimension $d$ with constants $1 \mp \varepsilon$ and failure probability
$$2 d \exp\Bigl(-\frac{\varepsilon^2 \lvert k \rvert}{3 \beta (d + 2\sqrt{d t} + 2t)}\Bigr) +
  \lvert n \rvert e^{-t}\,.$$
[Woodruff2014, Theorem 7] (there
$r = \Omega(\varepsilon^{-2} \log d\, (\sqrt{d} + \sqrt{\log n})^2)$ rows, probability $0.99$,
real Walsh, $n$ a power of two); [MartinssonTropp2020, §9.3]
($d = O(k \log k)$, any SRTT); [HalkoMartinssonTropp2011, Theorem 11.1] (the SRFT with complex
signs, $0.40 \le \sigma_{\min}$, $\sigma_{\max} \le 1.48$, failure $O(1/k)$); [Tropp2011a]. Here
any field, any $\mathbf{F}$ with entry bound $\beta$, the tail in natural parameters. For
$\lvert n \rvert < \lvert k \rvert$ the law is $0$, so $\mu = 0$.
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srht (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (d : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (2 * d * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  intro U hU
  rcases lt_or_ge (Fintype.card n) (Fintype.card k) with hk | hk
  · rw [HasSubspaceEmbedding, eq_zero_of_hasLaw_srht hS hk, measureReal_zero_apply]
    positivity
  have := isProbabilityMeasure_samplingSketchWithoutReplacement (𝕜 := 𝕜) hk
  refine hS.hasSubspaceEmbedding_iff.2 ?_
  rw [srht_eq_map_prod]
  refine hasSubspaceEmbedding_map_prod hF U (by positivity) ht fun V hV hl => ?_
  refine (hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement HasLaw.id hl hε
    hε1).mono le_rfl le_rfl ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (rank_mul_exp_le three_pos (Nat.cast_nonneg _) ht hV hU hl)
    two_pos.le

/-- **The SRHT OSI with replacement**: the bound of
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht` for i.i.d. uniform indices, nonempty `k` and
`n`, through `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch` at uniform weights.
[CamanoEpperlyMeyerTropp2025, §1.5.2].
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement [Nonempty k] [Nonempty n]
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    IsObliviousSubspaceInjection S d (1 - ε)
      (d * Real.exp (-ε ^ 2 * Fintype.card k / (2 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  have := isProbabilityMeasure_samplingSketch (𝕜 := 𝕜) (k := k) (NNReal.sum_const_inv_card (ι := n))
  refine ⟨isIsotropicSketch_of_hasLaw_srhtWithReplacement hF.hasOrthonormalCols hS,
    fun U hU => ?_⟩
  refine hS.hasSubspaceInjection_iff.2 ?_
  rw [srhtWithReplacement_eq_map_prod]
  refine hasSubspaceInjection_map_prod hF U (by positivity) ht fun V hV hl => ?_
  exact (hasSubspaceInjection_of_hasLaw_samplingSketch HasLaw.id NNReal.sum_const_inv_card
    (leverageScore_le_mul_const_inv_card hl) hε).mono le_rfl
    (rank_mul_exp_le two_pos (Nat.cast_nonneg _) ht hV hU hl)

/-- **The SRHT OSE with replacement**: the bound of
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` for i.i.d. uniform indices.
[MartinssonTropp2020, §9.3].
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (2 * d * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  intro U hU
  rcases isEmpty_or_nonempty n with hn | hn
  · rw [show U = 0 from Matrix.ext fun i => isEmptyElim i]
    exact hasSubspaceEmbedding_of_rank_eq_zero Matrix.rank_zero (by positivity)
  have := isProbabilityMeasure_samplingSketch (𝕜 := 𝕜) (k := k) (NNReal.sum_const_inv_card (ι := n))
  refine hS.hasSubspaceEmbedding_iff.2 ?_
  rw [srhtWithReplacement_eq_map_prod]
  refine hasSubspaceEmbedding_map_prod hF U (by positivity) ht fun V hV hl => ?_
  refine (hasSubspaceEmbedding_of_hasLaw_samplingSketch HasLaw.id NNReal.sum_const_inv_card
    (leverageScore_le_mul_const_inv_card hl) hε hε1).mono le_rfl le_rfl ?_
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_left (rank_mul_exp_le three_pos (Nat.cast_nonneg _) ht hV hU hl)
    two_pos.le

/-! ### Sample sizes -/

/-- The choice $t = \log(2\lvert n \rvert / \delta)$ for $0 < \delta < 1$: $t \ge 0$, the flattening
term is $\delta / 2$, the flattened bound is $\beta\,\mathrm{srhtRowBound}(\lvert n \rvert, d,
\delta/2)$, and it is positive. -/
private theorem log_div_half_spec [Nonempty n] (hF : IsBoundedOrthonormal F β) (d : ℕ)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 ≤ Real.log (Fintype.card n / (δ / 2)) ∧
      Fintype.card n * Real.exp (-Real.log (Fintype.card n / (δ / 2))) = δ / 2 ∧
      β * (d + 2 * √(d * Real.log (Fintype.card n / (δ / 2))) +
        2 * Real.log (Fintype.card n / (δ / 2))) =
        β * srhtRowBound (Fintype.card n) d (δ / 2) ∧
      0 < β * srhtRowBound (Fintype.card n) d (δ / 2) := by
  have hn : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.2 Fintype.card_pos
  have hpos : 0 < (Fintype.card n : ℝ) / (δ / 2) := by positivity
  have hlog : 0 < Real.log (Fintype.card n / (δ / 2)) :=
    Real.log_pos ((one_lt_div (by positivity)).2 (by linarith))
  refine ⟨hlog.le, ?_, by rw [srhtRowBound_def], ?_⟩
  · rw [Real.exp_neg, Real.exp_log hpos, inv_div, mul_div_cancel₀ _ (by positivity)]
  · rw [srhtRowBound_def]
    exact mul_pos (one_pos.trans_le hF.one_le)
      (add_pos_of_nonneg_of_pos (by positivity) (by linarith))

/-- **The SRHT OSE, sample-size form**: with at least `NLAlib.samplingSize d L ε (δ/2)` rows (at
present <!-- value samplingSize d L \varepsilon (\delta/2) -->
$3 L \log(2d/(\delta/2))/\varepsilon^2$<!-- /value -->), at
$L = \beta\, \mathrm{srhtRowBound}(\lvert n \rvert, d, \delta/2)$, the SRHT is an oblivious
subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and failure probability
$\delta$, for $0 < \varepsilon \le 1$ and $\delta > 0$; flattening and sampling each fail with
probability at most $\delta/2$. The size of uniform row sampling at the flattened coherence.
[Woodruff2014, Theorem 7]; [Tropp2011a]. The tail
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` at $t = \log(2\lvert n \rvert / \delta)$,
where $\lvert n \rvert e^{-t} = \delta/2$.
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ) (d : ℕ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · intro U _
    rw [show U = 0 from Matrix.ext fun i => isEmptyElim i]
    exact hasSubspaceEmbedding_of_rank_eq_zero Matrix.rank_zero hδ.le
  have : IsFiniteMeasure μ := hS.isFiniteMeasure_iff.2 inferInstance
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact fun U _ => (measureReal_le_one_of_hasLaw_srht hS _).trans hδ1
  obtain ⟨ht, hexp, hL, hLpos⟩ := log_div_half_spec hF d hδ hδ1
  refine (isObliviousSubspaceEmbedding_of_hasLaw_srht hF hS d hε.le hε1 ht).mono le_rfl le_rfl
    le_rfl ?_
  rw [hL, hexp]
  linarith [two_mul_mul_exp_le_of_samplingSize_le hLpos hε (half_pos hδ) hk]

/-- **The SRHT OSI, sample-size form**: with at least `NLAlib.samplingInjectionSize d L ε (δ/2)`
rows (at present <!-- value samplingInjectionSize d L \varepsilon (\delta/2) -->
$2 L \log(d/(\delta/2))/\varepsilon^2$<!-- /value -->), at
$L = \beta\, \mathrm{srhtRowBound}(\lvert n \rvert, d, \delta/2)$, nonempty `k` and
$\lvert k \rvert \le \lvert n \rvert$, the SRHT is an oblivious subspace injection for dimension
$d$ with constant $1 - \varepsilon$ and failure probability $\delta$, for $\varepsilon > 0$ and
$\delta > 0$; the tail `NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht` at
$t = \log(2\lvert n \rvert / \delta)$. [Tropp2011a].
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le [Nonempty k]
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ)
    (hkn : Fintype.card k ≤ Fintype.card n) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ := by
  have : IsProbabilityMeasure μ := hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srht F hkn)
  have : Nonempty n := Fintype.card_pos_iff.1 (Fintype.card_pos.trans_le hkn)
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact ⟨isIsotropicSketch_of_hasLaw_srht hF.hasOrthonormalCols hS hkn,
      fun U _ => measureReal_le_one.trans hδ1⟩
  obtain ⟨ht, hexp, hL, hLpos⟩ := log_div_half_spec hF d hδ hδ1
  refine (isObliviousSubspaceInjection_of_hasLaw_srht hF hS hkn d hε.le ht).mono le_rfl le_rfl ?_
  rw [hL, hexp]
  linarith [mul_exp_le_of_samplingInjectionSize_le hLpos hε (half_pos hδ) hk]

/-- **The SRHT OSE with replacement, sample-size form**: the size of
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le` for i.i.d. uniform
indices. [MartinssonTropp2020, §9.3].
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement_of_samplingSize_le
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · intro U _
    rw [show U = 0 from Matrix.ext fun i => isEmptyElim i]
    exact hasSubspaceEmbedding_of_rank_eq_zero Matrix.rank_zero hδ.le
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srhtWithReplacement F)
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact fun U _ => measureReal_le_one.trans hδ1
  obtain ⟨ht, hexp, hL, hLpos⟩ := log_div_half_spec hF d hδ hδ1
  refine (isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement hF hS d hε.le hε1 ht).mono
    le_rfl le_rfl le_rfl ?_
  rw [hL, hexp]
  linarith [two_mul_mul_exp_le_of_samplingSize_le hLpos hε (half_pos hδ) hk]

/-- **The SRHT OSI with replacement, sample-size form**: the size of
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le` for i.i.d.
uniform indices, nonempty `k` and `n`.
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionSize_le
    [Nonempty k] [Nonempty n] (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_srhtWithReplacement F)
  rcases le_or_gt 1 δ with hδ1 | hδ1
  · exact ⟨isIsotropicSketch_of_hasLaw_srhtWithReplacement hF.hasOrthonormalCols hS,
      fun U _ => measureReal_le_one.trans hδ1⟩
  obtain ⟨ht, hexp, hL, hLpos⟩ := log_div_half_spec hF d hδ hδ1
  refine (isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement hF hS d hε.le ht).mono le_rfl
    le_rfl ?_
  rw [hL, hexp]
  linarith [mul_exp_le_of_samplingInjectionSize_le hLpos hε (half_pos hδ) hk]

end NLAlib
