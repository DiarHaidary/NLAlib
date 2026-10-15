/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Probability.Distributions.Sampling
public import NLAlib.Probability.Law
public import NLAlib.Probability.MatrixConcentration.ChernoffSum
public import NLAlib.Sketching.Properties.FixedSubspace
public import NLAlib.Sketching.Properties.Isotropic
public import NLAlib.Matrix.Subspaces.Leverage

/-!
# Row sampling

For weights $p : n \to \mathbb{R}_{\ge 0}$ and indices $\iota : k \to n$, the row-sampling
sketch `NLAlib.samplingSketchMatrix p ι : Matrix k n 𝕜` has row $j$ equal to
$(\lvert k \rvert \, p_{\iota(j)})^{-1/2} \, \mathbf{e}_{\iota(j)}^{\mathsf{H}}$; its law
`NLAlib.samplingSketch k p` is the pushforward of $\lvert k \rvert$ i.i.d. indices with law
`NLAlib.samplingMeasure p`. The measurable space on the row index `n` is fixed to `⊤` inside the
definition, so no statement carries an instance on `n`;
`NLAlib.samplingSketch_eq_sum_smul_dirac` gives the law as a finite mixture of Diracs and
`NLAlib.samplingSketch_eq_map` recovers the pushforward under any measurable space on `n` with
measurable singletons.

For a fixed $\mathbf{U} : n \times r$ of any shape and rank and weights dominating its leverage
scores, $\ell_i(\mathbf{U}) \le L p_i$ for every $i$, the sketch is a random subspace injection
with failure probability $d\, e^{-\varepsilon^2 k / (2L)}$ and a random subspace embedding with
constants $1 \mp \varepsilon$ and failure probability $2 d\, e^{-\varepsilon^2 k / (3L)}$ for
$0 \le \varepsilon \le 1$, $d = \operatorname{rank}\mathbf{U}$ and $k$ the number of samples
(matrix Chernoff). Exact leverage sampling is $L = \operatorname{rank}\mathbf{U}$, uniform
sampling $L = \operatorname{coh}\mathbf{U}$, the coherence. The sample sizes are named quantities
(CONTRIBUTING §5.2, rule 2), with their inversions `NLAlib.two_mul_mul_exp_le_of_samplingSize_le`
and `NLAlib.mul_exp_le_of_samplingInjectionSize_le`; the "$k \ge \ldots$ suffices" forms are
corollaries of the tails.

Degenerate cases. Rank zero ($\mathbf{U} = \mathbf{0}$): every failure event is empty and every
bound is $0$. Empty `k`: $\mathbf{S} = \mathbf{0}$, the bound $d \cdot e^0$ is at least $1$ when
$\mathbf{U} \ne \mathbf{0}$, and the upper half holds surely; the sketch is not isotropic, hence
`[Nonempty k]` on isotropy. A zero weight $p_i = 0$ gives a zero sketch row (junk
$(\sqrt{0})^{-1} = 0$), and the domination hypothesis then forces row $i$ of $\mathbf{U}$ to
vanish (`NLAlib.leverageScore_eq_zero_iff`). $L \le 0$ forces rank zero, so no $0 < L$ is
assumed. For $\varepsilon \ge 1$ the injection is vacuous (`NLAlib.isSubspaceInjection_of_nonpos`).
The two corollaries at the leverage-score distribution and at uniform weights take no
$\sum_i p_i = 1$: when their weights fail it ($\mathbf{U} = \mathbf{0}$, or `n` empty) the law is
the zero measure for nonempty `k`, so `HasLaw` forces $\mu = 0$, and for empty `k` the law is a
Dirac mass at $\mathbf{0}$, a probability measure; in both subcases
$\operatorname{rank}\mathbf{U} = 0$ and every embedding event is full. Design:
`docs/design/Sketching-S4.md` §3.2, §8.

Proofs. The two halves pass to an orthonormal basis $\mathbf{Q}$ of
$\operatorname{range}\mathbf{U}$, whose rows satisfy $\|\mathbf{q}_i\|^2 \le L p_i$, and to the
product space of the indices; there the Gram-atoms identity writes
$(\mathbf{S}\mathbf{Q})^{\mathsf{H}} \mathbf{S}\mathbf{Q}$ as a sum of independent positive
semidefinite atoms, each at most $(L / \lvert k \rvert) \, \mathbf{I}$, with means summing to
$\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$, and matrix Chernoff
(`NLAlib.Probability.MatrixConcentration.ChernoffSum`) bounds its extreme eigenvalues. Isotropy is
the same identity at $\mathbf{A} = \mathbf{B} = \mathbf{I}$.

## Main definitions

* `NLAlib.samplingSketchMatrix`: the sketch built from given indices.
* `NLAlib.samplingSketch`: its law for i.i.d. indices.
* `NLAlib.samplingSize`, `NLAlib.samplingInjectionSize`: sample sizes.

## Main results

* `NLAlib.samplingSketch_eq_sum_smul_dirac`, `NLAlib.samplingSketch_eq_map`,
  `NLAlib.hasLaw_samplingSketchMatrix`: the law as a mixture, as a pushforward, and the bridge
  from a user's own indices.
* `NLAlib.conjTranspose_samplingSketchMatrix_mul_mul`: the sketched cross-Gram matrix as an
  average of rank-one atoms.
* `NLAlib.samplingSketchMatrix_mul_conjTranspose_of_injective`: distinct indices give a diagonal
  $\mathbf{S}\mathbf{S}^{\mathsf{H}}$.
* `NLAlib.isIsotropicSketch_of_hasLaw_samplingSketch`: isotropy for positive weights.
* `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch`,
  `NLAlib.hasSubspaceEmbedding_zero_of_hasLaw_samplingSketch`: the two halves.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch`: row sampling under leverage
  domination.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_leverageScoreDistribution`,
  `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_const_inv_card`: exact leverage and
  uniform sampling.
* `NLAlib.two_mul_mul_exp_le_of_samplingSize_le`,
  `NLAlib.mul_exp_le_of_samplingInjectionSize_le`: the tails inverted at the sample sizes.
* `NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le`,
  `NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le`: sample
  sizes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder NNReal ENNReal Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k n q r : Type*} [Fintype k] [Fintype n] [Fintype q] [Fintype r] [DecidableEq n]
  {S : Ω → Matrix k n 𝕜} {U : Matrix n r 𝕜} {p : n → ℝ≥0} {L ε δ : ℝ}

/-! ### The sketch and its law -/

/-- The **row-sampling sketch** with weights $p$ and indices $\iota : k \to n$: row $j$ is
$(\lvert k \rvert \, p_{\iota(j)})^{-1/2} \, \mathbf{e}_{\iota(j)}^{\mathsf{H}}$. Junk value: a
zero row where $p_{\iota(j)} = 0$. Its law for i.i.d. indices is `NLAlib.samplingSketch`.
[Woodruff2014, Definition 16], there $\mathbf{D}\mathbf{\Omega}^{\mathsf{T}}$;
[MartinssonTropp2020, §9.6.3]. -/
noncomputable def samplingSketchMatrix (p : n → ℝ≥0) (ι : k → n) : Matrix k n 𝕜 :=
  Matrix.of fun j i => if ι j = i then (((√((Fintype.card k : ℝ) * p i))⁻¹ : ℝ) : 𝕜) else 0

variable (k) in
/-- The **law of the row-sampling sketch**: the pushforward by `NLAlib.samplingSketchMatrix p` of
$\lvert k \rvert$ i.i.d. indices with law `NLAlib.samplingMeasure p`. The measurable space on `n`
is `⊤` inside the definition; `NLAlib.samplingSketch_eq_map` restates it under any measurable
space on `n` with measurable singletons, and `NLAlib.samplingSketch_eq_sum_smul_dirac` as a finite
mixture of Diracs. A probability measure when $\sum_i p_i = 1$ or `k` is empty.
[Woodruff2014, Definition 16]; [MartinssonTropp2020, §9.6.3]. -/
noncomputable def samplingSketch (p : n → ℝ≥0) : Measure (Matrix k n 𝕜) :=
  let _ : MeasurableSpace n := ⊤
  (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p)

omit [DecidableEq n] in
/-- The product of $\lvert k \rvert$ copies of `samplingMeasure p`, as a finite mixture of
Diracs. -/
private theorem pi_samplingMeasure_eq_sum [DecidableEq k] [MeasurableSpace n]
    [MeasurableSingletonClass n] (p : n → ℝ≥0) :
    Measure.pi (fun _ : k => samplingMeasure p) =
      ∑ ι : k → n, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac ι := by
  refine Measure.ext_of_singleton fun ι => ?_
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  classical
  simp only [samplingMeasure_singleton, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, smul_eq_mul, Set.univ_pi_singleton,
    Measure.dirac_apply' _ (measurableSet_singleton ι), Set.indicator_apply,
    Set.mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

/-- The pushforward of $\lvert k \rvert$ i.i.d. indices by the sketch, as a finite mixture of
Diracs, under any measurable space on `n` with measurable singletons. -/
private theorem map_pi_samplingMeasure_eq_sum [DecidableEq k] [MeasurableSpace n]
    [MeasurableSingletonClass n] (p : n → ℝ≥0) :
    (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix (𝕜 := 𝕜) p) =
      ∑ ι : k → n, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac (samplingSketchMatrix p ι) := by
  have hf : Measurable (samplingSketchMatrix (𝕜 := 𝕜) (k := k) p) := measurable_of_finite _
  ext s hs
  rw [Measure.map_apply hf hs, pi_samplingMeasure_eq_sum]
  simp only [Measure.coe_finsetSum, Finset.sum_apply, Measure.smul_apply, smul_eq_mul,
    Measure.dirac_apply' _ (hf hs), Measure.dirac_apply' _ hs]
  rfl

/-- The law of the row-sampling sketch as a finite mixture of Diracs, one atom per index map
$\iota : k \to n$ with mass $\prod_j p_{\iota(j)}$. -/
theorem samplingSketch_eq_sum_smul_dirac [DecidableEq k] (p : n → ℝ≥0) :
    samplingSketch (𝕜 := 𝕜) k p =
      ∑ ι : k → n, (∏ j, (p (ι j) : ℝ≥0∞)) • Measure.dirac (samplingSketchMatrix p ι) := by
  let _ : MeasurableSpace n := ⊤
  exact map_pi_samplingMeasure_eq_sum p

/-- The law of the row-sampling sketch is a finite measure, for any weights. -/
instance isFiniteMeasure_samplingSketch (p : n → ℝ≥0) :
    IsFiniteMeasure (samplingSketch (𝕜 := 𝕜) k p) := by
  unfold samplingSketch
  infer_instance

/-- The law of the row-sampling sketch is a probability measure for weights summing to one. -/
theorem isProbabilityMeasure_samplingSketch (hp : ∑ i, p i = 1) :
    IsProbabilityMeasure (samplingSketch (𝕜 := 𝕜) k p) := by
  let _ : MeasurableSpace n := ⊤
  have : IsProbabilityMeasure (samplingMeasure p) := isProbabilityMeasure_samplingMeasure p hp
  exact Measure.isProbabilityMeasure_map (measurable_of_finite _).aemeasurable

/-- The law of the row-sampling sketch is the pushforward of i.i.d. indices under any measurable
space on `n` with measurable singletons. -/
theorem samplingSketch_eq_map [MeasurableSpace n] [MeasurableSingletonClass n] (p : n → ℝ≥0) :
    samplingSketch (𝕜 := 𝕜) k p =
      (Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p) := by
  classical
  rw [samplingSketch_eq_sum_smul_dirac, map_pi_samplingMeasure_eq_sum]

/-- **From the user's own indices**: if $\iota$ is a vector of $\lvert k \rvert$ i.i.d. indices
with law `NLAlib.samplingMeasure p`, the sketch built from it has law
`NLAlib.samplingSketch k p`. -/
theorem hasLaw_samplingSketchMatrix [MeasurableSpace n] [MeasurableSingletonClass n]
    {ι : Ω → k → n} (hι : HasLaw ι (Measure.pi fun _ : k => samplingMeasure p) μ) :
    HasLaw (fun ω => (samplingSketchMatrix p (ι ω) : Matrix k n 𝕜)) (samplingSketch k p) μ := by
  rw [samplingSketch_eq_map]
  have hY : HasLaw (samplingSketchMatrix (𝕜 := 𝕜) p)
      ((Measure.pi fun _ : k => samplingMeasure p).map (samplingSketchMatrix p))
      (Measure.pi fun _ : k => samplingMeasure p) :=
    ⟨(measurable_of_finite _).aemeasurable, rfl⟩
  exact hY.comp hι

/-! ### Deterministic identities -/

omit [Fintype n] in
/-- The row-sampling sketch is a diagonal scaling of the transposed selection matrix:
$\mathbf{S} = \operatorname{diag}\bigl((\lvert k \rvert \, p_{\iota(j)})^{-1/2}\bigr)
\mathbf{P}^{\mathsf{H}}$ for the selection matrix $\mathbf{P}$ of $\iota$. -/
theorem samplingSketchMatrix_eq_diagonal_mul [DecidableEq k] (p : n → ℝ≥0) (ι : k → n) :
    (samplingSketchMatrix p ι : Matrix k n 𝕜) =
      Matrix.diagonal (fun j => (((√((Fintype.card k : ℝ) * p (ι j)))⁻¹ : ℝ) : 𝕜)) *
        (selectionMatrix ι)ᴴ := by
  ext j i
  rw [Matrix.diagonal_mul, Matrix.conjTranspose_apply, selectionMatrix_apply]
  simp only [samplingSketchMatrix, Matrix.of_apply]
  by_cases h : ι j = i
  · subst h
    simp
  · simp [h, Ne.symm h]

/-- **Distinct indices give orthogonal rows**: for an injective $\iota$, the rows of the sketch have
disjoint supports, so $\mathbf{S}\mathbf{S}^{\mathsf{H}}$ is diagonal with entries
$(\lvert k \rvert \, p_{\iota(j)})^{-1}$ ($0$ where $p_{\iota(j)} = 0$). At uniform weights it is
$(\lvert n \rvert / \lvert k \rvert) \mathbf{I}$, the partial isometry of row sampling without
replacement and of the subsampled randomized Hadamard transform. Amendment of
`docs/design/Sketching-S4.md` by `docs/design/Sketching-S6.md` §1, item 4. -/
theorem samplingSketchMatrix_mul_conjTranspose_of_injective [DecidableEq k] (p : n → ℝ≥0)
    {ι : k → n} (hι : Function.Injective ι) :
    (samplingSketchMatrix p ι : Matrix k n 𝕜) * (samplingSketchMatrix p ι)ᴴ =
      Matrix.diagonal fun j => ((((Fintype.card k : ℝ) * p (ι j))⁻¹ : ℝ) : 𝕜) := by
  have hP : (selectionMatrix ι : Matrix n k 𝕜)ᴴ * (selectionMatrix ι : Matrix n k 𝕜) = 1 :=
    (hasOrthonormalCols_selectionMatrix (𝕜 := 𝕜) hι).conjTranspose_mul_self
  rw [samplingSketchMatrix_eq_diagonal_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc, ← Matrix.mul_assoc _ (selectionMatrix ι),
    hP, Matrix.one_mul, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  have hx : 0 ≤ (Fintype.card k : ℝ) * p (ι j) := by positivity
  rw [Pi.star_apply, RCLike.star_def, RCLike.conj_ofReal, ← RCLike.ofReal_mul, ← mul_inv,
    Real.mul_self_sqrt hx]

/-- Row $j$ of a sampled matrix is the scaled row $\iota(j)$. -/
private theorem samplingSketchMatrix_mul_apply {q' : Type*} (p : n → ℝ≥0) (ι : k → n)
    (C : Matrix n q' 𝕜) (j : k) :
    (samplingSketchMatrix p ι * C : Matrix k q' 𝕜) j =
      ((((√((Fintype.card k : ℝ) * p (ι j)))⁻¹ : ℝ) : 𝕜)) • C (ι j) := by
  ext a
  simp [Matrix.mul_apply, samplingSketchMatrix, ite_mul, Finset.sum_ite_eq]

omit [Fintype q] [Fintype r] in
/-- **The Gram-atoms identity**: the sketched cross-Gram matrix
$(\mathbf{S}\mathbf{A})^{\mathsf{H}} (\mathbf{S}\mathbf{B})$ is the sum over the samples $j$ of
the rank-one atoms
$(\lvert k \rvert \, p_{\iota(j)})^{-1} \mathbf{a}_{\iota(j)}^{\mathsf{H}} \mathbf{b}_{\iota(j)}$,
$\mathbf{a}_i$ and $\mathbf{b}_i$ the rows of $\mathbf{A}$ and $\mathbf{B}$, the zero matrix where
$p_{\iota(j)} = 0$. -/
theorem conjTranspose_samplingSketchMatrix_mul_mul (p : n → ℝ≥0) (ι : k → n)
    (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    (samplingSketchMatrix p ι * A)ᴴ * (samplingSketchMatrix p ι * B) =
      ∑ j, ((Fintype.card k : ℝ) * p (ι j))⁻¹ • Matrix.vecMulVec (star (A (ι j))) (B (ι j)) := by
  ext a b
  rw [Matrix.mul_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hx : 0 ≤ (Fintype.card k : ℝ) * p (ι j) := by positivity
  have hc : (√((Fintype.card k : ℝ) * p (ι j)))⁻¹ * (√((Fintype.card k : ℝ) * p (ι j)))⁻¹ =
      ((Fintype.card k : ℝ) * p (ι j))⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hx]
  rw [Matrix.conjTranspose_apply, samplingSketchMatrix_mul_apply, samplingSketchMatrix_mul_apply,
    Matrix.smul_apply, Matrix.vecMulVec_apply, RCLike.real_smul_eq_coe_mul, ← hc]
  simp only [Pi.smul_apply, smul_eq_mul, star_mul', RCLike.star_def, RCLike.conj_ofReal,
    Pi.star_apply, RCLike.ofReal_mul]
  ring

/-! ### The Chernoff atoms

Private proof material: the atoms of the sketched Gram matrix and the two Chernoff halves on the
product space of the indices. The Loewner bound on one atom is
`NLAlib.inv_mul_smul_vecMulVec_star_self_le` (`NLAlib.Matrix.Norms.Loewner`). -/

/-- The $j$-th rank-one atom
$(\lvert k \rvert \, p_{\iota(j)})^{-1} \, \mathbf{b}_{\iota(j)}^{\mathsf{H}} \mathbf{b}_{\iota(j)}$
of the sketched Gram matrix of $\mathbf{B}$, as a function of the indices $\iota$. -/
private noncomputable def samplingAtom (p : n → ℝ≥0) (B : Matrix n r 𝕜) (j : k) (ι : k → n) :
    Matrix r r 𝕜 :=
  ((Fintype.card k : ℝ) * p (ι j))⁻¹ • Matrix.vecMulVec (star (B (ι j))) (B (ι j))

open scoped ComplexOrder in
omit [Fintype n] [DecidableEq n] [Fintype r] in
/-- The atoms are positive semidefinite. -/
private theorem posSemidef_samplingAtom [Finite r] (p : n → ℝ≥0) (B : Matrix n r 𝕜) (j : k)
    (ι : k → n) :
    (samplingAtom p B j ι).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_star_self _).smul (by positivity)

section Pi

variable [MeasurableSpace n] [MeasurableSingletonClass n]

omit [DecidableEq n] [Fintype r] in
/-- The atoms are independent under the product of the index laws. -/
private theorem iIndepFun_samplingAtom (hp : ∑ i, p i = 1) (B : Matrix n r 𝕜) :
    iIndepFun (samplingAtom (k := k) p B) (Measure.pi fun _ : k => samplingMeasure p) := by
  have := isProbabilityMeasure_samplingMeasure p hp
  exact iIndepFun_pi (X := fun (_ : k) (i : n) =>
    ((Fintype.card k : ℝ) * p i)⁻¹ • Matrix.vecMulVec (star (B i)) (B i))
    fun _ => (measurable_of_finite _).aemeasurable

omit [DecidableEq n] in
/-- The means of the atoms sum to the Gram matrix $\mathbf{B}^{\mathsf{H}}\mathbf{B}$, when
$\mathbf{B}$ vanishes on the rows of zero weight. -/
private theorem sum_integral_samplingAtom [Nonempty k] [DecidableEq r] (hp : ∑ i, p i = 1)
    {B : Matrix n r 𝕜} (hB : ∀ i, p i = 0 → B i = 0) :
    ∑ j, ∫ ι, samplingAtom p B j ι ∂(Measure.pi fun _ : k => samplingMeasure p) = Bᴴ * B := by
  have := isProbabilityMeasure_samplingMeasure p hp
  have hj (j : k) : ∫ ι, samplingAtom p B j ι ∂(Measure.pi fun _ : k => samplingMeasure p) =
      (Fintype.card k : ℝ)⁻¹ • (Bᴴ * B) := by
    refine (integral_comp_eval (μ := fun _ : k => samplingMeasure p) (i := j)
      (f := fun i : n => ((Fintype.card k : ℝ) * p i)⁻¹ • Matrix.vecMulVec (star (B i)) (B i))
      AEStronglyMeasurable.of_discrete).trans ?_
    rw [integral_samplingMeasure, Matrix.conjTranspose_mul_eq_sum_vecMulVec, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul]
    rcases eq_or_ne (p i) 0 with h0 | h0
    · rw [hB i h0, star_zero, Matrix.zero_vecMulVec, smul_zero, smul_zero]
    · have hpos : (p i : ℝ) ≠ 0 := by exact_mod_cast h0
      congr 1
      field_simp
  have hk : (Fintype.card k : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [hj, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    mul_inv_cancel₀ hk, one_smul]

omit [Fintype n] [DecidableEq n] [MeasurableSpace n] [MeasurableSingletonClass n] in
/-- A row of zero weight vanishes under the domination $\|\mathbf{b}_i\|^2 \le L p_i$. -/
private theorem eq_zero_of_norm_sq_le {B : Matrix n r 𝕜}
    (hB : ∀ i, ‖WithLp.toLp 2 (B i)‖ ^ 2 ≤ L * p i) (i : n) (h0 : p i = 0) : B i = 0 := by
  have h := hB i
  rw [h0, NNReal.coe_zero, mul_zero] at h
  have h' : ‖WithLp.toLp 2 (B i)‖ = 0 :=
    pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm h (sq_nonneg _))
  rwa [norm_eq_zero, WithLp.toLp_eq_zero] at h'

/-- The lower Chernoff tail on the primitive space, for $\mathbf{Q}$ with orthonormal
columns. -/
private theorem hasSubspaceInjection_samplingSketchMatrix [Nonempty k] [Nonempty r]
    [DecidableEq r] {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) (hp : ∑ i, p i = 1)
    (hL : 0 < L) (hdom : ∀ i, ‖WithLp.toLp 2 (Q i)‖ ^ 2 ≤ L * p i) (hε : 0 ≤ ε) :
    HasSubspaceInjection (samplingSketchMatrix (𝕜 := 𝕜) p) Q (1 - ε)
      (Fintype.card r * Real.exp (-ε ^ 2 * Fintype.card k / (2 * L)))
      (Measure.pi fun _ : k => samplingMeasure p) := by
  have := isProbabilityMeasure_samplingMeasure p hp
  rcases le_or_gt 1 ε with h1 | h1
  · have he : {ι : k → n | ¬ IsSubspaceInjection (samplingSketchMatrix (𝕜 := 𝕜) p ι) Q (1 - ε)} =
        ∅ := Set.eq_empty_of_forall_notMem fun ι hι =>
      hι (isSubspaceInjection_of_nonpos _ _ (by linarith))
    rw [HasSubspaceInjection, he, measureReal_empty]
    positivity
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  obtain ⟨j₀, hj₀⟩ : ∃ j, j + 1 = Fintype.card r :=
    ⟨Fintype.card r - 1, Nat.sub_add_cancel Fintype.card_pos⟩
  have hC := measureReal_eigenvalue_sum_le_le_card_mul_exp (iIndepFun_samplingAtom hp Q)
    (fun _ => (measurable_of_finite _).aemeasurable) (div_pos hL hk)
    (fun j => ae_of_all _ (posSemidef_samplingAtom p Q j))
    (fun j => ae_of_all _ fun ι =>
      inv_mul_smul_vecMulVec_star_self_le (Nat.cast_nonneg _) hL.le (hdom (ι j))) hj₀ hε h1
  rw [sum_integral_samplingAtom hp (eq_zero_of_norm_sq_le hdom), hQ.conjTranspose_mul_self,
    eigenvalue_one (by omega)] at hC
  refine (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ι hι => ?_)).trans (hC.trans_eq ?_)
  · have hG : ((samplingSketchMatrix p ι : Matrix k n 𝕜) * Q)ᴴ *
        ((samplingSketchMatrix p ι : Matrix k n 𝕜) * Q) = ∑ j, samplingAtom p Q j ι :=
      conjTranspose_samplingSketchMatrix_mul_mul p ι Q Q
    have hH : (∑ j, samplingAtom p Q j ι).IsHermitian :=
      hG ▸ Matrix.isHermitian_conjTranspose_mul_self _
    rw [hQ.isSubspaceInjection_iff, hG, hH.smul_one_le_iff hj₀, not_le] at hι
    rw [mul_one]
    exact hι.le
  · congr 2
    field_simp

/-- The upper Chernoff tail on the primitive space, for $\mathbf{Q}$ with orthonormal
columns. -/
private theorem hasSubspaceEmbedding_zero_samplingSketchMatrix [Nonempty k] [Nonempty r]
    [DecidableEq r] {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) (hp : ∑ i, p i = 1)
    (hL : 0 < L) (hdom : ∀ i, ‖WithLp.toLp 2 (Q i)‖ ^ 2 ≤ L * p i) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding (samplingSketchMatrix (𝕜 := 𝕜) p) Q 0 (1 + ε)
      (Fintype.card r * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)))
      (Measure.pi fun _ : k => samplingMeasure p) := by
  have := isProbabilityMeasure_samplingMeasure p hp
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hC := measureReal_eigenvalue_zero_sum_ge_le_card_mul_exp (iIndepFun_samplingAtom hp Q)
    (fun _ => (measurable_of_finite _).aemeasurable) (div_pos hL hk)
    (fun j => ae_of_all _ (posSemidef_samplingAtom p Q j))
    (fun j => ae_of_all _ fun ι =>
      inv_mul_smul_vecMulVec_star_self_le (Nat.cast_nonneg _) hL.le (hdom (ι j))) hε hε1
  rw [sum_integral_samplingAtom hp (eq_zero_of_norm_sq_le hdom), hQ.conjTranspose_mul_self,
    eigenvalue_one Fintype.card_pos] at hC
  refine hQ.hasSubspaceEmbedding_zero_of_measureReal_le
    ((measureReal_mono (Set.ofPred_subset_ofPred.2 fun ι hι => ?_)).trans (hC.trans_eq ?_))
  · rw [sq_singularValues, conjTranspose_samplingSketchMatrix_mul_mul] at hι
    rw [mul_one]
    exact hι
  · congr 2
    field_simp

end Pi

/-! ### Isotropy -/

/-- **Row sampling with positive weights is isotropic.** With zero weights the second moment is
$\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \operatorname{diag}([p_i \ne 0]) \preceq
\mathbf{I}$, which is not isotropy; mixing in uniform weights,
$p_i = (\ell_i / d + 1 / \lvert n \rvert) / 2$ for the leverage scores $\ell_i$ of $\mathbf{U}$ and
$d = \operatorname{rank}\mathbf{U}$, restores isotropy at the price of a factor $2$ in the
domination constant ($\ell_i \le 2 d p_i$). A weakening of the fixed-subspace injection tails of
`NLAlib.Sketching.Properties.Injection` to
$\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] \preceq \mathbf{I}$ (sub-isotropy) would admit zero
weights; it is open work for an S1 interface review (`docs/design/Sketching-S4.md` §8, item 10).
[MartinssonTropp2020, §9.6.3]. -/
theorem isIsotropicSketch_of_hasLaw_samplingSketch [Nonempty k]
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1) (hpos : ∀ i, 0 < p i) :
    IsIsotropicSketch S μ := by
  let _ : MeasurableSpace n := ⊤
  have := isProbabilityMeasure_samplingMeasure p hp
  refine hS.isIsotropicSketch_iff.2
    ((hasLaw_samplingSketchMatrix HasLaw.id).isIsotropicSketch_iff.1
      ⟨fun i j => MemLp.of_discrete, ?_⟩)
  have e (ι : k → n) : (samplingSketchMatrix p ι : Matrix k n 𝕜)ᴴ * samplingSketchMatrix p ι =
      ∑ j, samplingAtom p (1 : Matrix n n 𝕜) j ι := by
    have h := conjTranspose_samplingSketchMatrix_mul_mul p ι (1 : Matrix n n 𝕜)
      (1 : Matrix n n 𝕜)
    rwa [Matrix.mul_one] at h
  simp only [id, e]
  rw [integral_finsetSum _ fun j _ => Integrable.of_finite,
    sum_integral_samplingAtom (B := (1 : Matrix n n 𝕜)) hp fun i h => absurd h (hpos i).ne',
    Matrix.conjTranspose_one, Matrix.mul_one]

/-! ### Subspace injection and embedding for a fixed subspace -/

/-- **The lower half of row sampling**: under leverage domination
$\ell_i(\mathbf{U}) \le L p_i$, the row-sampling sketch with $k$ samples is a subspace injection
for $\operatorname{range}\mathbf{U}$ with constant $1 - \varepsilon$ outside probability
$\operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (2L)}$, for every
$\varepsilon \ge 0$ (vacuous for $\varepsilon \ge 1$). Matrix Chernoff's lower tail with
$R = L / k$. [Tropp2015, Theorem 5.1.1, (5.1.5), weakened after (5.1.8)]; there
$\varepsilon \in [0, 1)$ and the source form
$(e^{-\varepsilon} / (1 - \varepsilon)^{1 - \varepsilon})^{k/L}$. -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketch (hS : HasLaw S (samplingSketch k p) μ)
    (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 ≤ ε) :
    HasSubspaceInjection S U (1 - ε)
      (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (2 * L))) μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, zero_mul]
    exact (hasSubspaceEmbedding_of_rank_eq_zero (b := 0) hd le_rfl).hasSubspaceInjection
  have hL : 0 < L := (Nat.cast_pos.2 hd).trans_le (rank_le_of_leverageScore_le hp hdom)
  obtain ⟨Q, hQ, hUQ, hdomQ⟩ := exists_hasOrthonormalCols_of_leverageScore_le hdom
  rcases isEmpty_or_nonempty k with hk | hk
  · refine measureReal_le_one.trans ?_
    rw [Fintype.card_eq_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    exact_mod_cast hd
  have : Nonempty (Fin U.rank) := ⟨⟨0, hd⟩⟩
  let _ : MeasurableSpace n := ⊤
  have h := hasSubspaceInjection_samplingSketchMatrix (k := k) hQ hp hL hdomQ hε
  rw [Fintype.card_fin] at h
  exact (hS.hasSubspaceInjection_iff.2
    ((hasLaw_samplingSketchMatrix HasLaw.id).hasSubspaceInjection_iff.1 h)).of_range_le hUQ

/-- **The upper half of row sampling**: under leverage domination
$\ell_i(\mathbf{U}) \le L p_i$, the row-sampling sketch with $k$ samples satisfies
$(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U}
\preceq (1 + \varepsilon)\, \mathbf{U}^{\mathsf{H}}\mathbf{U}$ outside probability
$\operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (3L)}$, for
$0 \le \varepsilon \le 1$; the lower constant $0$ holds surely. Matrix Chernoff's upper tail with
$R = L / k$. [Tropp2015, Theorem 5.1.1, (5.1.6)], with
$\varepsilon - (1 + \varepsilon) \log(1 + \varepsilon) \le -\varepsilon^2/3$ on $[0, 1]$; there
the source form for every $\varepsilon \ge 0$. -/
theorem hasSubspaceEmbedding_zero_of_hasLaw_samplingSketch (hS : HasLaw S (samplingSketch k p) μ)
    (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U 0 (1 + ε)
      (U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, zero_mul]
    exact hasSubspaceEmbedding_of_rank_eq_zero hd le_rfl
  have hL : 0 < L := (Nat.cast_pos.2 hd).trans_le (rank_le_of_leverageScore_le hp hdom)
  obtain ⟨Q, hQ, hUQ, hdomQ⟩ := exists_hasOrthonormalCols_of_leverageScore_le hdom
  rcases isEmpty_or_nonempty k with hk | hk
  · refine measureReal_le_one.trans ?_
    rw [Fintype.card_eq_zero, Nat.cast_zero, mul_zero, zero_div, Real.exp_zero, mul_one]
    exact_mod_cast hd
  have : Nonempty (Fin U.rank) := ⟨⟨0, hd⟩⟩
  let _ : MeasurableSpace n := ⊤
  have h := hasSubspaceEmbedding_zero_samplingSketchMatrix (k := k) hQ hp hL hdomQ hε hε1
  rw [Fintype.card_fin] at h
  exact (hS.hasSubspaceEmbedding_iff.2
    ((hasLaw_samplingSketchMatrix HasLaw.id).hasSubspaceEmbedding_iff.1 h)).of_range_le hUQ

/-- **Row sampling under leverage domination**: if $\ell_i(\mathbf{U}) \le L p_i$ for every row,
the row-sampling sketch with $k$ samples is a subspace embedding for
$\operatorname{range}\mathbf{U}$ with constants $1 \mp \varepsilon$ outside probability
$2 \operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (3L)}$, for
$0 \le \varepsilon \le 1$ and any $\mathbf{U}$. [Woodruff2014, Theorem 17], there $\mathbf{U}$
with orthonormal columns, $p$ a $\beta$-approximation of the leverage-score distribution and
$s > 144 d \log(2d/\delta) / (\beta \varepsilon^2)$ samples through a Bernstein bound (Fact 1);
here matrix Chernoff, $L = d/\beta$, any shape and rank; [MartinssonTropp2020, §9.6.3];
[Tropp2015, Theorem 5.1.1].
Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch (hS : HasLaw S (samplingSketch k p) μ)
    (hp : ∑ i, p i = 1) (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L))) μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  have hL : 0 ≤ L := (Nat.cast_nonneg _).trans (rank_le_of_leverageScore_le hp hdom)
  have hlow := hasSubspaceInjection_of_hasLaw_samplingSketch hS hp hdom hε
  have hb : μ.real {ω | ¬ (S ω * U)ᴴ * (S ω * U) ≤ (1 + ε) • (Uᴴ * U)} ≤
      U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)) :=
    (measureReal_mono (Set.ofPred_subset_ofPred.2 fun ω hω h' => hω h'.upper)).trans
      (hasSubspaceEmbedding_zero_of_hasLaw_samplingSketch hS hp hdom hε hε1)
  refine (hlow.hasSubspaceEmbedding hb).mono le_rfl le_rfl ?_
  have hexp : Real.exp (-ε ^ 2 * Fintype.card k / (2 * L)) ≤
      Real.exp (-ε ^ 2 * Fintype.card k / (3 * L)) := by
    rw [Real.exp_le_exp]
    rcases hL.eq_or_lt with h0 | h0
    · simp [← h0]
    · rw [neg_mul, neg_div, neg_div, neg_le_neg_iff]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have := mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg (α := ℝ) U.rank)
  linarith

/-- **Exact leverage-score sampling**: sampling rows by the leverage-score distribution of
$\mathbf{U}$ gives a subspace embedding with constants $1 \mp \varepsilon$ outside probability
$2 d \, e^{-\varepsilon^2 k / (3 d)}$, $d = \operatorname{rank}\mathbf{U}$, for
$0 \le \varepsilon \le 1$; the domination constant is $L = d$. No normalisation hypothesis: for
$\mathbf{U} = \mathbf{0}$ the bound is $0$ and every embedding event is full.
[MartinssonTropp2020, §9.6.3]; [Woodruff2014, Theorem 17], there $\beta = 1$.
Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_leverageScoreDistribution
    (hS : HasLaw S (samplingSketch k (leverageScoreDistribution U)) μ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * U.rank))) μ := by
  rcases eq_or_ne U 0 with hU | hU
  · exact hasSubspaceEmbedding_of_rank_eq_zero (by rw [hU, Matrix.rank_zero]) (by positivity)
  · exact hasSubspaceEmbedding_of_hasLaw_samplingSketch hS (sum_leverageScoreDistribution hU)
      (leverageScore_le_rank_mul_leverageScoreDistribution U) hε hε1

/-- **Uniform row sampling**: sampling rows uniformly gives a subspace embedding with constants
$1 \mp \varepsilon$ outside probability
$2 \operatorname{rank}\mathbf{U} \cdot e^{-\varepsilon^2 k / (3 \operatorname{coh}\mathbf{U})}$,
for $0 \le \varepsilon \le 1$; the domination constant is the coherence
$L = \operatorname{coh}\mathbf{U}$ (`NLAlib.coherence`). No normalisation hypothesis: for empty
`n` the bound is $0$ and every embedding event is full. [MartinssonTropp2020, §9.6.2], there the
sample size $2 \varepsilon^{-2} \mu \log(2d/\delta)$ for a coherence $\mu$, through matrix
Chernoff. -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_const_inv_card
    (hS : HasLaw S (samplingSketch k fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) μ) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε)
      (2 * U.rank * Real.exp (-ε ^ 2 * Fintype.card k / (3 * coherence U))) μ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · exact hasSubspaceEmbedding_of_rank_eq_zero
      (Matrix.rank_eq_zero.2 (Matrix.ext fun i => isEmptyElim i)) (by positivity)
  · exact hasSubspaceEmbedding_of_hasLaw_samplingSketch hS NNReal.sum_const_inv_card
      (leverageScore_le_mul_const_inv_card (leverageScore_le_coherence_mul_inv U)) hε hε1

/-! ### Sample sizes -/

/-- The **row-sampling size** $3 L \log(2d/\delta) / \varepsilon^2$: with at least this many
samples, row sampling under leverage domination with constant $L$ is a subspace embedding with
constants $1 \mp \varepsilon$ and failure probability $\delta$ for a subspace of dimension $d$,
for $0 < \varepsilon \le 1$
(`NLAlib.hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le`). The value the proof
reaches, inverting $2 d \, e^{-\varepsilon^2 k / (3L)} \le \delta$
(`NLAlib.two_mul_mul_exp_le_of_samplingSize_le`); [Woodruff2014, Theorem 17] has
$144 d \log(2d/\delta) / (\beta \varepsilon^2)$, which at $L = d/\beta$ is $48$ times larger.
Consumers use `NLAlib.samplingSize_le`. Junk values: $0$ at $\varepsilon = 0$; at most $0$ for
$\delta \ge 2d$, where the tail bound is at least $1$. -/
noncomputable irreducible_def samplingSize (d : ℕ) (L ε δ : ℝ) : ℝ :=
  3 * L * Real.log (2 * d / δ) / ε ^ 2

/-- The row-sampling size is nonnegative for $0 \le L$ and $0 < \delta \le 2d$. -/
theorem samplingSize_nonneg {d : ℕ} (hL : 0 ≤ L) (hδ : 0 < δ) (hδd : δ ≤ 2 * d) :
    0 ≤ samplingSize d L ε δ := by
  rw [samplingSize_def]
  have hlog : 0 ≤ Real.log (2 * d / δ) := Real.log_nonneg ((one_le_div₀ hδ).2 hδd)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hlog) (sq_nonneg ε)

/-- The row-sampling size is monotone in the dimension $d$ and in the domination constant
$L \ge 0$, and antitone in the distortion $\varepsilon > 0$ and the failure probability
$\delta > 0$, as long as the larger side is in its nontrivial range $\delta \le 2 d'$. -/
theorem samplingSize_mono {d d' : ℕ} {L' ε' δ' : ℝ} (hd : d ≤ d') (hL : 0 ≤ L) (hLL' : L ≤ L')
    (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδd : δ ≤ 2 * d') :
    samplingSize d L ε' δ' ≤ samplingSize d' L' ε δ := by
  have hR := samplingSize_nonneg (ε := ε) (hL.trans hLL') hδ hδd
  rw [samplingSize_def] at hR ⊢
  rw [samplingSize_def]
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  rcases le_or_gt (Real.log (2 * d / δ')) 0 with h0 | h0
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hL) h0) (sq_nonneg ε')).trans hR
  · have hpos : 0 < 2 * (d : ℝ) / δ' := by
      refine lt_of_le_of_ne (by positivity) fun h => ?_
      rw [← h, Real.log_zero] at h0
      exact lt_irrefl _ h0
    have hdd : (d : ℝ) ≤ d' := by exact_mod_cast hd
    have hlog : Real.log (2 * d / δ') ≤ Real.log (2 * d' / δ) :=
      Real.log_le_log hpos (div_le_div₀ (by positivity) (by linarith) hδ hδδ')
    exact div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) (hL.trans hLL')) (h0.le.trans hlog))
      (mul_le_mul (by linarith) hlog h0.le (mul_nonneg (by norm_num) (hL.trans hLL')))
      (by positivity) (pow_le_pow_left₀ hε.le hεε' 2)

/-- The explicit comparison: `samplingSize d L ε δ` is at most
$3 L \log(2d/\delta) / \varepsilon^2$, the value the proof reaches; an improved definition keeps it
true. -/
theorem samplingSize_le (d : ℕ) (L ε δ : ℝ) :
    samplingSize d L ε δ ≤ 3 * L * Real.log (2 * d / δ) / ε ^ 2 := by
  rw [samplingSize_def]

/-- The **row-sampling injection size** $2 L \log(d/\delta) / \varepsilon^2$: with at least this
many samples, row sampling under leverage domination with constant $L$ is a subspace injection
with constant $1 - \varepsilon$ and failure probability $\delta$ for a subspace of dimension $d$,
for $\varepsilon > 0$
(`NLAlib.hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le`). The value
the proof reaches, inverting $d \, e^{-\varepsilon^2 k / (2L)} \le \delta$
(`NLAlib.mul_exp_le_of_samplingInjectionSize_le`); one tail, against the embedding's two.
Consumers use `NLAlib.samplingInjectionSize_le`. Junk values: $0$ at $\varepsilon = 0$; at most
$0$ for $\delta \ge d$, where the tail bound is at least $1$. -/
noncomputable irreducible_def samplingInjectionSize (d : ℕ) (L ε δ : ℝ) : ℝ :=
  2 * L * Real.log (d / δ) / ε ^ 2

/-- The row-sampling injection size is nonnegative for $0 \le L$ and $0 < \delta \le d$. -/
theorem samplingInjectionSize_nonneg {d : ℕ} (hL : 0 ≤ L) (hδ : 0 < δ) (hδd : δ ≤ d) :
    0 ≤ samplingInjectionSize d L ε δ := by
  rw [samplingInjectionSize_def]
  have hlog : 0 ≤ Real.log (d / δ) := Real.log_nonneg ((one_le_div₀ hδ).2 hδd)
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL) hlog) (sq_nonneg ε)

/-- The row-sampling injection size is monotone in the dimension $d$ and in the domination
constant $L \ge 0$, and antitone in the distortion $\varepsilon > 0$ and the failure probability
$\delta > 0$, as long as the larger side is in its nontrivial range $\delta \le d'$. -/
theorem samplingInjectionSize_mono {d d' : ℕ} {L' ε' δ' : ℝ} (hd : d ≤ d') (hL : 0 ≤ L)
    (hLL' : L ≤ L') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') (hδd : δ ≤ d') :
    samplingInjectionSize d L ε' δ' ≤ samplingInjectionSize d' L' ε δ := by
  have hR := samplingInjectionSize_nonneg (ε := ε) (hL.trans hLL') hδ hδd
  rw [samplingInjectionSize_def] at hR ⊢
  rw [samplingInjectionSize_def]
  have hδ' : 0 < δ' := hδ.trans_le hδδ'
  rcases le_or_gt (Real.log (d / δ')) 0 with h0 | h0
  · exact (div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) hL) h0) (sq_nonneg ε')).trans hR
  · have hpos : 0 < (d : ℝ) / δ' := by
      refine lt_of_le_of_ne (by positivity) fun h => ?_
      rw [← h, Real.log_zero] at h0
      exact lt_irrefl _ h0
    have hdd : (d : ℝ) ≤ d' := by exact_mod_cast hd
    have hlog : Real.log (d / δ') ≤ Real.log (d' / δ) :=
      Real.log_le_log hpos (div_le_div₀ (by positivity) hdd hδ hδδ')
    exact div_le_div₀ (mul_nonneg (mul_nonneg (by norm_num) (hL.trans hLL')) (h0.le.trans hlog))
      (mul_le_mul (by linarith) hlog h0.le (mul_nonneg (by norm_num) (hL.trans hLL')))
      (by positivity) (pow_le_pow_left₀ hε.le hεε' 2)

/-- The explicit comparison: `samplingInjectionSize d L ε δ` is at most
$2 L \log(d/\delta) / \varepsilon^2$, the value the proof reaches; an improved definition keeps it
true. -/
theorem samplingInjectionSize_le (d : ℕ) (L ε δ : ℝ) :
    samplingInjectionSize d L ε δ ≤ 2 * L * Real.log (d / δ) / ε ^ 2 := by
  rw [samplingInjectionSize_def]

/-- **Inverting the embedding tail at `NLAlib.samplingSize`**: for $L > 0$, $\varepsilon > 0$,
$\delta > 0$ and $K \ge$ `samplingSize d L ε δ`,
$2 d \, e^{-\varepsilon^2 K / (3L)} \le \delta$. The step from the tails of row sampling (with or
without replacement, and after flattening in the SRHT) to their sample-size forms. -/
theorem two_mul_mul_exp_le_of_samplingSize_le {d : ℕ} {K : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hδ : 0 < δ) (hK : samplingSize d L ε δ ≤ K) :
    2 * d * Real.exp (-ε ^ 2 * K / (3 * L)) ≤ δ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Nat.cast_zero, mul_zero, zero_mul]
    exact hδ.le
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [samplingSize_def, div_le_iff₀ (by positivity)] at hK
  have hlog : Real.log (2 * d / δ) ≤ ε ^ 2 * K / (3 * L) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hδ] at hlog
  rw [neg_mul, neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **Inverting the injection tail at `NLAlib.samplingInjectionSize`**: for $L > 0$,
$\varepsilon > 0$, $\delta > 0$ and $K \ge$ `samplingInjectionSize d L ε δ`,
$d \, e^{-\varepsilon^2 K / (2L)} \le \delta$. -/
theorem mul_exp_le_of_samplingInjectionSize_le {d : ℕ} {K : ℝ} (hL : 0 < L) (hε : 0 < ε)
    (hδ : 0 < δ) (hK : samplingInjectionSize d L ε δ ≤ K) :
    d * Real.exp (-ε ^ 2 * K / (2 * L)) ≤ δ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [Nat.cast_zero, zero_mul]
    exact hδ.le
  have hd' : (0 : ℝ) < d := Nat.cast_pos.2 hd
  rw [samplingInjectionSize_def, div_le_iff₀ (by positivity)] at hK
  have hlog : Real.log (d / δ) ≤ ε ^ 2 * K / (2 * L) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  rw [Real.log_le_iff_le_exp (by positivity), div_le_iff₀ hδ] at hlog
  rw [neg_mul, neg_div, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **Row sampling, sample-size form**: with at least `NLAlib.samplingSize U.rank L ε δ` samples,
row sampling under leverage domination $\ell_i(\mathbf{U}) \le L p_i$ is a subspace embedding for
$\operatorname{range}\mathbf{U}$ with constants $1 \mp \varepsilon$ and failure probability
$\delta$, for $0 < \varepsilon \le 1$ and $\delta > 0$. [Woodruff2014, Theorem 17], constant
$144/\beta$ there, $3$ here at $L = d/\beta$; [MartinssonTropp2020, §9.6.3].
Result: leverage-sampling-ose -/
theorem hasSubspaceEmbedding_of_hasLaw_samplingSketch_of_samplingSize_le
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hk : samplingSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceEmbedding S U (1 - ε) (1 + ε) δ μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  refine (hasSubspaceEmbedding_of_hasLaw_samplingSketch hS hp hdom hε.le hε1).mono le_rfl le_rfl ?_
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, mul_zero, zero_mul]
    exact hδ.le
  exact two_mul_mul_exp_le_of_samplingSize_le
    ((Nat.cast_pos.2 hd).trans_le (rank_le_of_leverageScore_le hp hdom)) hε hδ hk

/-- **The lower half, sample-size form**: with at least
`NLAlib.samplingInjectionSize U.rank L ε δ` samples, row sampling under leverage domination
$\ell_i(\mathbf{U}) \le L p_i$ is a subspace injection for $\operatorname{range}\mathbf{U}$ with
constant $1 - \varepsilon$ and failure probability $\delta$, for $\varepsilon > 0$ and
$\delta > 0$. -/
theorem hasSubspaceInjection_of_hasLaw_samplingSketch_of_samplingInjectionSize_le
    (hS : HasLaw S (samplingSketch k p) μ) (hp : ∑ i, p i = 1)
    (hdom : ∀ i, leverageScore U i ≤ L * p i) (hε : 0 < ε) (hδ : 0 < δ)
    (hk : samplingInjectionSize U.rank L ε δ ≤ Fintype.card k) :
    HasSubspaceInjection S U (1 - ε) δ μ := by
  have : IsProbabilityMeasure μ :=
    hS.isProbabilityMeasure_iff.2 (isProbabilityMeasure_samplingSketch hp)
  refine (hasSubspaceInjection_of_hasLaw_samplingSketch hS hp hdom hε.le).mono le_rfl ?_
  rcases Nat.eq_zero_or_pos U.rank with hd | hd
  · rw [hd, Nat.cast_zero, zero_mul]
    exact hδ.le
  exact mul_exp_le_of_samplingInjectionSize_le
    ((Nat.cast_pos.2 hd).trans_le (rank_le_of_leverageScore_le hp hdom)) hε hδ hk

end NLAlib
