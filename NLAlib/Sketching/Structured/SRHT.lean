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
`NLAlib.samplingSize` and `NLAlib.samplingInjectionSize` at
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

This file is part of the skeleton of Sketching stage S6 (`docs/design/Sketching-S6.md` §8,
item 15); the proofs of the laws' explicit forms, the bridges, isotropy, the partial isometry and
the oblivious theorems are deferred.

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
  have hc : (Fintype.card n : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := isProbabilityMeasure_samplingMeasure (fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc])
  exact Measure.isProbabilityMeasure_map (measurable_srhtMatrix F).aemeasurable

/-- **The SRHT law as signs times row sampling without replacement**: the pushforward of
independent signs and the law `NLAlib.samplingSketchWithoutReplacement k n` by
$(\boldsymbol{\xi}, \mathbf{P}) \mapsto \mathbf{P}\mathbf{F}\operatorname{diag}(\boldsymbol{\xi})$;
the form the proofs use.
Proof: the map of a product is the product of maps on the second factor
(`MeasureTheory.Measure.map_prod_map`), with the same `⊤` on `n` in both definitions. Easy. -/
theorem srht_eq_map_prod (F : Matrix n n 𝕜) :
    srht k F = ((rademacherVector n).prod (samplingSketchWithoutReplacement k n)).map
      fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜) := by
  sorry

/-- **The SRHT law with replacement as signs times row sampling**: the pushforward of independent
signs and the law `NLAlib.samplingSketch k` at uniform weights by
$(\boldsymbol{\xi}, \mathbf{P}) \mapsto \mathbf{P}\mathbf{F}\operatorname{diag}(\boldsymbol{\xi})$.
Proof: as for `NLAlib.srht_eq_map_prod`. Easy. -/
theorem srhtWithReplacement_eq_map_prod (F : Matrix n n 𝕜) :
    srhtWithReplacement k F =
      ((rademacherVector n).prod (samplingSketch k fun _ : n => (Fintype.card n : ℝ≥0)⁻¹)).map
        fun x => x.2 * F * Matrix.diagonal fun i => (x.1 i : 𝕜) := by
  sorry

/-- **From the user's own signs and injection**: for independent signs $\boldsymbol{\xi}$ and a
uniform injection $\iota : k \to n$, under any measurable space on `n` with measurable
singletons, the sketch built from them has law `NLAlib.srht k F`.
Proof: `ProbabilityTheory.IndepFun.hasLaw_prod`, then `HasLaw.comp` with the measurable sketch;
a measurable space with measurable singletons on a finite type is `⊤`. Easy. -/
theorem hasLaw_srhtMatrix_of_hasLaw_uniformOn_injective [MeasurableSpace n]
    [MeasurableSingletonClass n] {ι : Ω → k → n} (hξ : HasLaw ξ (rademacherVector n) μ)
    (hι : HasLaw ι (uniformOn {f : k → n | Function.Injective f}) μ) (hind : IndepFun ξ ι μ) :
    HasLaw (fun ω => srhtMatrix F (ξ ω) (ι ω)) (srht k F) μ := by
  sorry

/-- **From the user's own signs and indices**: for independent signs $\boldsymbol{\xi}$ and
independent i.i.d. uniform indices $\iota : k \to n$, under any measurable space on `n` with
measurable singletons, the sketch built from them has law `NLAlib.srhtWithReplacement k F`.
Proof: as for `NLAlib.hasLaw_srhtMatrix_of_hasLaw_uniformOn_injective`. Easy. -/
theorem hasLaw_srhtMatrix_of_hasLaw_pi [MeasurableSpace n] [MeasurableSingletonClass n]
    {ι : Ω → k → n} (hξ : HasLaw ξ (rademacherVector n) μ)
    (hι : HasLaw ι
      (Measure.pi fun _ : k => samplingMeasure fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) μ)
    (hind : IndepFun ξ ι μ) :
    HasLaw (fun ω => srhtMatrix F (ξ ω) (ι ω)) (srhtWithReplacement k F) μ := by
  sorry

/-! ### Isotropy and the partial isometry -/

/-- **The SRHT is isotropic**: $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$ for a
unitary $\mathbf{F}$, nonempty `k` and $\lvert k \rvert \le \lvert n \rvert$.
[CamanoEpperlyMeyerTropp2025, §1.5.2].
Proof: on the product space $\mathbf{S} = \mathbf{P}\mathbf{T}$ with $\mathbf{P}$ row sampling
without replacement (isotropic) and $\mathbf{T} = \mathbf{F}\mathbf{D}$ (isotropic: unitary almost
surely, bounded entries) independent; `NLAlib.IsIsotropicSketch.mul`, transported by
`NLAlib.srht_eq_map_prod`. Moderate. -/
theorem isIsotropicSketch_of_hasLaw_srht [Nonempty k] (hF : HasOrthonormalCols F)
    (hS : HasLaw S (srht k F) μ) (hk : Fintype.card k ≤ Fintype.card n) :
    IsIsotropicSketch S μ := by
  sorry

/-- **The SRHT with replacement is isotropic**, for a unitary $\mathbf{F}$ and nonempty `k`,
`n`. [CamanoEpperlyMeyerTropp2025, §1.5.2].
Proof: as for `NLAlib.isIsotropicSketch_of_hasLaw_srht`, with row sampling with replacement.
Moderate. -/
theorem isIsotropicSketch_of_hasLaw_srhtWithReplacement [Nonempty k] [Nonempty n]
    (hF : HasOrthonormalCols F) (hS : HasLaw S (srhtWithReplacement k F) μ) :
    IsIsotropicSketch S μ := by
  sorry

/-- **The SRHT is a scaled partial isometry**: for a unitary $\mathbf{F}$, almost surely
$\mathbf{S}\mathbf{S}^{\mathsf{H}} = (\lvert n \rvert / \lvert k \rvert)\, \mathbf{I}$. Without
replacement only: repeated rows break it. [HalkoMartinssonTropp2011, §11.1];
[MartinssonTropp2020, §9.3].
Proof: $\mathbf{S}\mathbf{S}^{\mathsf{H}} = \mathbf{P}\mathbf{F}\mathbf{D}\mathbf{D}^{\mathsf{H}}
\mathbf{F}^{\mathsf{H}}\mathbf{P}^{\mathsf{H}} = \mathbf{P}\mathbf{P}^{\mathsf{H}}$ on the event
that the signs are $\pm 1$, then
`NLAlib.samplingSketchMatrix_mul_conjTranspose_of_injective` at uniform weights; the injection is
injective almost surely. Easy. -/
theorem ae_mul_conjTranspose_eq_of_hasLaw_srht [DecidableEq k] (hF : HasOrthonormalCols F)
    (hS : HasLaw S (srht k F) μ) :
    ∀ᵐ ω ∂μ, S ω * (S ω)ᴴ = ((Fintype.card n : ℝ) / Fintype.card k) • (1 : Matrix k k 𝕜) := by
  sorry

/-- **The spectral norm of the SRHT**: for a unitary $\mathbf{F}$, almost surely
$\|\mathbf{S}\|_2 = \sqrt{\lvert n \rvert / \lvert k \rvert}$ ($0$ for empty `k`). The bound
$\|\boldsymbol{\Omega}_2\|_2 \le \sqrt{n/\ell}$ of [HalkoMartinssonTropp2011, Theorem 11.2] and
[MartinssonTropp2020, Theorem 11.6].
Proof: $\|\mathbf{S}\|_2^2 = \|\mathbf{S}\mathbf{S}^{\mathsf{H}}\|_2$ and
`NLAlib.ae_mul_conjTranspose_eq_of_hasLaw_srht`. Easy. -/
theorem ae_specNorm_eq_of_hasLaw_srht (hF : HasOrthonormalCols F) (hS : HasLaw S (srht k F) μ) :
    ∀ᵐ ω ∂μ, specNorm (S ω) = √(Fintype.card n / Fintype.card k : ℝ) := by
  sorry

/-! ### Oblivious subspace injections and embeddings -/

/-- **The SRHT OSI**: for a bounded orthonormal $\mathbf{F}$ with constant $\beta$, nonempty `k`,
$\lvert k \rvert \le \lvert n \rvert$, $\varepsilon \ge 0$ and $t \ge 0$, the SRHT is an
oblivious subspace injection for dimension $d$ with constant $1 - \varepsilon$ and failure
probability
$$d \exp\Bigl(-\frac{\varepsilon^2 \lvert k \rvert}{2 \beta (d + 2\sqrt{d t} + 2t)}\Bigr) +
  \lvert n \rvert e^{-t}\,:$$
the lower matrix Chernoff half after flattening.
[CamanoEpperlyMeyerTropp2025, §1.5.2] (the OSI view; $k = \Omega(d \log d)$ is necessary, their
citation of Tropp 2011a); [Tropp2011a].
Proof: on the product space, `NLAlib.hasSubspaceInjection_mul_of_indepFun_of_leverageScore_le`
with $\mathbf{P}$ row sampling without replacement, $\mathbf{T} = \mathbf{F}\mathbf{D}$,
$L = \beta (d + 2\sqrt{d t} + 2t)$: the sampling hypothesis is
`NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketchWithoutReplacement`, monotone from
$\operatorname{rank}\mathbf{V}$ to $d$, and the flattening hypothesis is
`NLAlib.measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector`, whose
threshold is monotone in the rank ($\beta \ge 1$). Isotropy from
`NLAlib.isIsotropicSketch_of_hasLaw_srht`. Moderate.
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srht [Nonempty k] (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (hk : Fintype.card k ≤ Fintype.card n) (d : ℕ) (hε : 0 ≤ ε)
    (ht : 0 ≤ t) :
    IsObliviousSubspaceInjection S d (1 - ε)
      (d * Real.exp (-ε ^ 2 * Fintype.card k / (2 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  sorry

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
any field, any $\mathbf{F}$ with entry bound $\beta$, the tail in natural parameters.
Proof: as for `NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht`, with
`NLAlib.hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le` and
`NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement`; for
$\lvert n \rvert < \lvert k \rvert$, $\mu = 0$. Moderate.
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srht (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srht k F) μ) (d : ℕ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (2 * d * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  sorry

/-- **The SRHT OSI with replacement**: the bound of
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht` for i.i.d. uniform indices, nonempty `k` and
`n`. [CamanoEpperlyMeyerTropp2025, §1.5.2].
Proof: as without replacement, with `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch` at
uniform weights. Moderate.
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement [Nonempty k] [Nonempty n]
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ)
    (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    IsObliviousSubspaceInjection S d (1 - ε)
      (d * Real.exp (-ε ^ 2 * Fintype.card k / (2 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  sorry

/-- **The SRHT OSE with replacement**: the bound of
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` for i.i.d. uniform indices.
[MartinssonTropp2020, §9.3].
Proof: as without replacement, with `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch` at
uniform weights; for empty `n` and nonempty `k`, $\mu = 0$. Moderate.
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ)
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1) (ht : 0 ≤ t) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε)
      (2 * d * Real.exp (-ε ^ 2 * Fintype.card k / (3 * (β * (d + 2 * √(d * t) + 2 * t)))) +
        Fintype.card n * Real.exp (-t)) μ := by
  sorry

/-! ### Sample sizes -/

/-- **The SRHT OSE, sample-size form**: with at least `NLAlib.samplingSize d L ε (δ/2)` rows, at
$L = \beta\, \mathrm{srhtRowBound}(\lvert n \rvert, d, \delta/2)$, the SRHT is an oblivious
subspace embedding for dimension $d$ with constants $1 \mp \varepsilon$ and failure probability
$\delta$, for $0 < \varepsilon \le 1$ and $\delta > 0$; flattening and sampling each fail with
probability at most $\delta/2$. The size of uniform row sampling at the flattened coherence.
[Woodruff2014, Theorem 7]; [Tropp2011a].
Proof: trivial for $\delta \ge 1$ ($\mu$ is a probability measure or $0$); empty `n` and $d = 0$
have empty events (rank zero); otherwise
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht` at $t = \log(2n/\delta)$, where
$n e^{-t} = \delta/2$ and $\beta(d + 2\sqrt{dt} + 2t) = L$ by `NLAlib.srhtRowBound_def`, and
the inversion of `NLAlib.samplingSize` as in
`NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le` ($L > 0$ since
$\beta \ge 1$ and $d \ge 1$). Arithmetic only, moderate; the route through the transfer with the
$\delta$ form of flattening (`docs/design/Sketching-S6.md` §3.3) also works.
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ) (d : ℕ) (hε : 0 < ε)
    (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ := by
  sorry

/-- **The SRHT OSI, sample-size form**: with at least `NLAlib.samplingInjectionSize d L ε (δ/2)`
rows, at $L = \beta\, \mathrm{srhtRowBound}(\lvert n \rvert, d, \delta/2)$, nonempty `k` and
$\lvert k \rvert \le \lvert n \rvert$, the SRHT is an oblivious subspace injection for dimension
$d$ with constant $1 - \varepsilon$ and failure probability $\delta$, for $\varepsilon > 0$ and
$\delta > 0$. [Tropp2011a].
Proof: as for `NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le`, from
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht` and the inversion of
`NLAlib.samplingInjectionSize`. Moderate.
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le [Nonempty k]
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srht k F) μ)
    (hkn : Fintype.card k ≤ Fintype.card n) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ := by
  sorry

/-- **The SRHT OSE with replacement, sample-size form**: the size of
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srht_of_samplingSize_le` for i.i.d. uniform
indices. [MartinssonTropp2020, §9.3].
Proof: as without replacement, from
`NLAlib.isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement`. Moderate.
Result: srht-ose -/
theorem isObliviousSubspaceEmbedding_of_hasLaw_srhtWithReplacement_of_samplingSize_le
    (hF : IsBoundedOrthonormal F β) (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceEmbedding S d (1 - ε) (1 + ε) δ μ := by
  sorry

/-- **The SRHT OSI with replacement, sample-size form**: the size of
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_srht_of_samplingInjectionSize_le` for i.i.d.
uniform indices, nonempty `k` and `n`.
Proof: as without replacement, from
`NLAlib.isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement`. Moderate.
Result: srht-osi -/
theorem isObliviousSubspaceInjection_of_hasLaw_srhtWithReplacement_of_samplingInjectionSize_le
    [Nonempty k] [Nonempty n] (hF : IsBoundedOrthonormal F β)
    (hS : HasLaw S (srhtWithReplacement k F) μ) (d : ℕ) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionSize d (β * srhtRowBound (Fintype.card n) d (δ / 2)) ε (δ / 2) ≤
      Fintype.card k) :
    IsObliviousSubspaceInjection S d (1 - ε) δ μ := by
  sorry

end NLAlib
