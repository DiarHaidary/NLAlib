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
public import NLAlib.Sketching.Sampling.Leverage

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

This file is the skeleton of Sketching stage S7 (`docs/design/Sketching-S7.md` §8, item 17),
with proofs deferred: isotropy, the exact second moment in trace form and in AMM form, and their
integrability. Everything after them is proved from them.

## Main definitions

* `NLAlib.countSketchMatrix`: the sketch built from a given hash and signs.
* `NLAlib.countSketch`: its law for a uniform hash and Rademacher signs.
* `NLAlib.countSketchRows`: the number of rows.

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
  have hc : (Fintype.card k : ℝ≥0) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := isProbabilityMeasure_samplingMeasure (fun _ : k => (Fintype.card k : ℝ≥0)⁻¹)
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hc])
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

/-- **CountSketch is isotropic**, $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$, for
nonempty `k`. [CamanoEpperlyMeyerTropp2025, Lemma B.1] (first part, there
$\mathbb{E}[\mathbf{\Phi}\mathbf{\Phi}^*] = \mathbf{I}$).
Proof: the entries are bounded by $1$ almost surely, so in $L^2$; by the hollow Gram identity the
off-diagonal entries of $\mathbf{S}^{\mathsf{H}}\mathbf{S}$ are $[h(i) = h(j)]\,\sigma_i\sigma_j$,
of mean $0$ by independence of the signs, and the diagonal is $1$ almost surely. On the product
space, then `ProbabilityTheory.HasLaw.isIsotropicSketch_iff`. Moderate. -/
theorem isIsotropicSketch_of_hasLaw_countSketch [Nonempty k] [DecidableEq n]
    (hS : HasLaw S (countSketch k n) μ) : IsIsotropicSketch S μ := by
  sorry

/-! ### The exact second moment -/

/-- The squared trace of $\mathbf{M}$ against the Gram error of a CountSketch is integrable.
Proof: on the product space the hash space is finite, and for each hash the integrand is the
squared modulus of a quadratic form in bounded signs. Easy. -/
theorem integrable_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    [DecidableEq n] (hS : HasLaw S (countSketch k n) μ) (M : Matrix n n 𝕜) :
    Integrable (fun ω => ‖(M * ((S ω)ᴴ * S ω - 1)).trace‖ ^ 2) μ := by
  sorry

/-- **The second moment of a CountSketch**: for every $\mathbf{M}$,
$$\mathbb{E}\lvert \operatorname{tr}(\mathbf{M}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}))
\rvert^2 = \frac{\|\mathbf{M}\|_{\mathsf{F}}^2 + \langle \mathbf{M}, \mathbf{M}^{\mathsf{T}}
\rangle_{\mathsf{F}} - 2 \sum_i \lvert \mathbf{M}_{i,i} \rvert^2}{\lvert k \rvert}\,.$$
[CamanoEpperlyMeyerTropp2025, Lemma B.1 and its proof] (there for self-adjoint $\mathbf{M}$, the
uncentred moment $\mathbb{E}[\operatorname{tr}(\mathbf{M}\mathbf{\Phi}\mathbf{\Phi}^*)^2]$, which
adds $(\operatorname{tr}\mathbf{M})^2$; the exact expression is in the proof, the statement is
the bound $(\operatorname{tr}\mathbf{M})^2 + 2\|\mathbf{M}\|_{\mathsf{F}}^2/b$ for $b$ rows).
Here centred, any $\mathbf{M}$, any field.
Proof: split on `Nonempty k` (the empty case is $0 = 0$). Fubini on the product space; for a fixed
hash, almost surely $\operatorname{tr}(\mathbf{M}\mathbf{H})$ is the quadratic form in the signs
of the hollow matrix $\mathbf{A}_h$ with entries $[i \ne j,\ h(i) = h(j)]\,\mathbf{M}_{j,i}$, and
`NLAlib.integral_norm_quadForm_sub_trace_sq` ($s = 1$, $m_4 = 1$) gives
$$\sum_{i \ne j,\ h(i) = h(j)} \bigl(\lvert \mathbf{M}_{i,j} \rvert^2 +
\operatorname{Re}(\overline{\mathbf{M}_{i,j}}\mathbf{M}_{j,i})\bigr)\,;$$
the collision probability `NLAlib.measureReal_pi_samplingMeasure_setOf_apply_eq_apply` at
uniform weights averages the hash.
About 150 lines. Hard.
Result: countsketch-second-moment -/
theorem integral_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch
    [DecidableEq n] (hS : HasLaw S (countSketch k n) μ) (M : Matrix n n 𝕜) :
    ∫ ω, ‖(M * ((S ω)ᴴ * S ω - 1)).trace‖ ^ 2 ∂μ =
      (frobNorm M ^ 2 + frobInner M Mᵀ - 2 * ∑ i, ‖M i i‖ ^ 2) / Fintype.card k := by
  sorry

/-! ### Approximate matrix multiplication -/

section AMM

variable [Fintype q] [Fintype r]

/-- The squared error of approximate matrix multiplication with a CountSketch is integrable.
Proof: each entry of the error
$\mathbf{A}^{\mathsf{H}}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I})\mathbf{B}$ is a trace
against a rank-one matrix, so the integrand is a finite sum of the integrable functions of
`NLAlib.integrable_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch`. Easy. -/
theorem integrable_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    Integrable (fun ω => frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2) μ := by
  sorry

/-- **AMM with a CountSketch, exact second moment**:
$$\mathbb{E}\|\mathbf{A}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{B} -
\mathbf{A}^{\mathsf{H}}\mathbf{B}\|_{\mathsf{F}}^2
= \frac{\|\mathbf{A}\|_{\mathsf{F}}^2\|\mathbf{B}\|_{\mathsf{F}}^2 +
\|\mathbf{A}^{\mathsf{T}}\mathbf{B}\|_{\mathsf{F}}^2 -
2\sum_i \|\mathbf{a}_i\|^2 \|\mathbf{b}_i\|^2}{\lvert k \rvert}$$
for the rows $\mathbf{a}_i$, $\mathbf{b}_i$ of $\mathbf{A}$, $\mathbf{B}$. Proved without a
literature source; Woodruff's proof of Theorem 14 computes its case
$\mathbf{A} = \mathbf{B} = \mathbf{x}$ over $\mathbb{R}$.
Proof: entry $(a, b)$ of the error is
$\operatorname{tr}(\mathbf{M}_{ab}(\mathbf{S}^{\mathsf{H}}\mathbf{S} - \mathbf{I}))$ for the
rank-one $\mathbf{M}_{ab}$ with entries $\mathbf{B}_{j,b}\overline{\mathbf{A}_{i,a}}$; sum the
exact second moment over $(a, b)$ (`NLAlib.frobNorm_vecMulVec`, `NLAlib.frobInner_eq_sum`).
Moderate.
Result: amm-countsketch -/
theorem integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_countSketch
    (hS : HasLaw S (countSketch k n) μ) (A : Matrix n q 𝕜) (B : Matrix n r 𝕜) :
    ∫ ω, frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B) ^ 2 ∂μ =
      (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (Aᵀ * B) ^ 2 -
        2 * ∑ i, ‖WithLp.toLp 2 (A i)‖ ^ 2 * ‖WithLp.toLp 2 (B i)‖ ^ 2) / Fintype.card k := by
  sorry

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

omit [DecidableEq k] in
/-- For orthonormal columns, $\|\mathbf{U}\|_{\mathsf{F}}^2 = \lvert r \rvert$. -/
private theorem frobNorm_sq_eq_card_of_hasOrthonormalCols (hU : HasOrthonormalCols U) :
    frobNorm U ^ 2 = Fintype.card r := by
  rw [frobNorm_sq_eq_re_trace, show Uᴴ * U = 1 from hU, Matrix.trace_one, RCLike.natCast_re]

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
    frobNorm_sq_eq_card_of_hasOrthonormalCols hU]
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
      rw [← frobNorm_sq_eq_card_of_hasOrthonormalCols hU]
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

/-- The **CountSketch rows** $(d^2 + d)/(\delta\varepsilon^2)$: a CountSketch with at least this
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

/-- The explicit comparison of `NLAlib.countSketchRows d ε δ` with
$(d^2 + d)/(\delta\varepsilon^2)$ that consumers invert with; an improved definition keeps it
true. -/
theorem countSketchRows_le (d : ℕ) (ε δ : ℝ) :
    countSketchRows d ε δ ≤ ((d : ℝ) ^ 2 + d) / (δ * ε ^ 2) := by
  rw [countSketchRows_def]

omit [DecidableEq k] in
/-- At least `NLAlib.countSketchRows d ε δ` rows give the failure probability $\delta$. -/
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

/-- **CountSketch OSE, size form**: with at least `NLAlib.countSketchRows d ε δ` rows, for
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

/-- **CountSketch OSI, size form**: with at least `NLAlib.countSketchRows d ε δ` rows, for
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
