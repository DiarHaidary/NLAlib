/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.LowerBounds.QueryModel.Basic
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# Deferred decision for adaptive matrix–vector queries

After an adaptive algorithm has queried a random matrix, the part of the matrix that the
queries have not touched is, conditionally on the transcript, distributed as before. For a
standard Gaussian $\mathbf{X} \in \mathbb{R}^{d \times k}$ queried through `twoSidedMulVec`
(products $\mathbf{X}\mathbf{w}$ and $\mathbf{X}^{\mathsf{H}}\mathbf{u}$), the untouched part is
$\mathbf{E}\mathbf{X}\mathbf{F}$, with $\mathbf{E}$ and $\mathbf{F}$ the orthogonal projectors onto
the complements of the spans of the left queries $\mathbf{u}_i$ and of the right queries
$\mathbf{w}_i$; it can be replaced by an independent copy without changing the joint law of the
transcript and the matrix (design note `docs/design/Probability-MatvecQueryModel.md` §3.4).

The replaced matrix is `QueryAlgorithm.resample`. It gives the same transcript
(`QueryAlgorithm.transcript_resample`) and the same joint law of transcript and matrix
(`QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix`); in frames, the
unqueried block is a standard Gaussian matrix independent of the transcript. The stabilizer
form for right unitarily invariant laws is in `NLAlib/RandomMatrix/Haar/Stabilizer.lean`
(non-adaptive) and `NLAlib/LowerBounds/QueryModel/HiddenHaar.lean` (adaptive).

## Main definitions

* `NLAlib.QueryAlgorithm.resample`: the matrix with its unqueried block replaced.

## Main results

* `NLAlib.QueryAlgorithm.transcript_resample`.
* `NLAlib.QueryAlgorithm.IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix`: adaptive
  deferred decision, resampling form.
* `NLAlib.QueryAlgorithm.IsMeasurable.hasLaw_prodMk_conjTranspose_mul_mul_of_hasLaw_gaussianMatrix`:
  adaptive deferred decision, frame form.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

namespace QueryAlgorithm

variable {𝕜 : Type*} [RCLike 𝕜] {d k β : Type*} [Fintype d] [Fintype k] [DecidableEq d]
  [DecidableEq k] {q : ℕ}

/-- The **resampled matrix** of an algorithm with `q` pair queries to `twoSidedMulVec X`,
$\mathbf{X} \in \Bbbk^{d \times k}$: with $\mathbf{E} = \mathbf{I} - \mathbf{P}_{\mathbf{U}}$ and
$\mathbf{F} = \mathbf{I} - \mathbf{P}_{\mathbf{W}}$, where the columns of $\mathbf{U}$ and
$\mathbf{W}$ are the left parts and the right parts of the queries made on $\mathbf{X}$
(`QueryAlgorithm.leftQueryMatrix`, `QueryAlgorithm.rightQueryMatrix`),
$$\mathsf{resample}(\mathbf{X}, \mathbf{X}') = \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
\mathbf{E}\mathbf{X}'\mathbf{F}\,.$$
It agrees with $\mathbf{X}$ on every query, so the algorithm cannot tell them apart
(`QueryAlgorithm.transcript_resample`). -/
noncomputable def resample (alg : QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) q β)
    (X X' : Matrix d k 𝕜) : Matrix d k 𝕜 :=
  let τ := alg.transcript (twoSidedMulVec X)
  let E := 1 - rangeProjector (alg.leftQueryMatrix τ)
  let F := 1 - rangeProjector (alg.rightQueryMatrix τ)
  X - E * X * F + E * X' * F

end QueryAlgorithm

end NLAlib


open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

namespace QueryAlgorithm

variable {d k β : Type*} [Fintype d] [Fintype k] {q : ℕ}

/-! ### Gaussian matrices -/

/-- A block $\mathbf{E}\mathbf{Z}\mathbf{F}$ with $\mathbf{F}\mathbf{w} = \mathbf{0}$ and
$\mathbf{E}\mathbf{u} = \mathbf{0}$ is invisible to the pair query $(\mathbf{w}, \mathbf{u})$. -/
private theorem twoSidedMulVec_add_mul_mul {𝕜 : Type*} [RCLike 𝕜] {E : Matrix d d 𝕜}
    {F : Matrix k k 𝕜} (hE : IsStarProjection E) {v : (k → 𝕜) × (d → 𝕜)} (hw : F *ᵥ v.1 = 0)
    (hu : E *ᵥ v.2 = 0) (Y Z : Matrix d k 𝕜) :
    twoSidedMulVec (Y + E * Z * F) v = twoSidedMulVec Y v := by
  simp only [twoSidedMulVec, Matrix.add_mulVec, Matrix.conjTranspose_add, Matrix.conjTranspose_mul,
    hE.conjTranspose_eq, ← Matrix.mulVec_mulVec, hw, hu, Matrix.mulVec_zero, add_zero]

/-- The resampled matrix gives the same transcript: an algorithm making `q` pair queries to
`twoSidedMulVec X`, $\mathbf{X} \in \Bbbk^{d \times k}$, gets the same responses from
`alg.resample X X'`, which differs from $\mathbf{X}$ only in the block
$\mathbf{E}\mathbf{X}\mathbf{F}$ orthogonal to all left queries and all right queries. -/
theorem transcript_resample [DecidableEq d] [DecidableEq k] {𝕜 : Type*} [RCLike 𝕜]
    (alg : QueryAlgorithm ((k → 𝕜) × (d → 𝕜)) ((d → 𝕜) × (k → 𝕜)) q β) (X X' : Matrix d k 𝕜) :
    alg.transcript (twoSidedMulVec (alg.resample X X')) = alg.transcript (twoSidedMulVec X) := by
  set τ := alg.transcript (twoSidedMulVec X) with hτ
  set P := rangeProjector (alg.rightQueryMatrix τ) with hP
  set Q := rangeProjector (alg.leftQueryMatrix τ) with hQ
  have hw : ∀ j, (alg.queries τ j).1 = alg.rightQueryMatrix τ *ᵥ Pi.single j 1 := by
    intro j; ext r; simp [QueryAlgorithm.rightQueryMatrix]
  have hu : ∀ j, (alg.queries τ j).2 = alg.leftQueryMatrix τ *ᵥ Pi.single j 1 := by
    intro j; ext r; simp [QueryAlgorithm.leftQueryMatrix]
  have hFw : ∀ j, (1 - P) *ᵥ (alg.queries τ j).1 = 0 := by
    intro j
    rw [hw j, Matrix.sub_mulVec, Matrix.one_mulVec, hP, rangeProjector_mulVec_mulVec, sub_self]
  have hEu : ∀ j, (1 - Q) *ᵥ (alg.queries τ j).2 = 0 := by
    intro j
    rw [hu j, Matrix.sub_mulVec, Matrix.one_mulVec, hQ, rangeProjector_mulVec_mulVec, sub_self]
  apply alg.transcript_eq_of_forall_apply_queries_eq
  intro j
  have hres : alg.resample X X' = X + (1 - Q) * (X' - X) * (1 - P) := by
    simp only [QueryAlgorithm.resample, ← hτ, ← hP, ← hQ, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [hres, twoSidedMulVec_add_mul_mul (isStarProjection_one_sub_rangeProjector _) (hFw j)
    (hEu j)]

/-- The transcript of `i + 1` truncated rounds appends the next response. -/
private theorem transcript_truncate_succ {Q R : Type*} (alg : QueryAlgorithm Q R q β) (f : Q → R)
    (i : ℕ) :
    (alg.truncate (i + 1)).transcript f = Fin.snoc (α := fun _ => R)
      ((alg.truncate i).transcript f) (f (alg.query i ((alg.truncate i).transcript f))) := by
  simp only [transcript_truncate]; rfl

/-- Appending a response does not change the earlier queries. -/
private theorem queries_truncate_succ_castSucc {Q R : Type*} (alg : QueryAlgorithm Q R q β)
    {i : ℕ}
    (h : Fin i → R) (r : R) (j : Fin i) :
    (alg.truncate (i + 1)).queries (Fin.snoc (α := fun _ => R) h r) j.castSucc =
      (alg.truncate i).queries h j := by
  simp only [queries, truncate]
  congr 1
  funext l
  have : (Fin.castLE j.castSucc.isLt.le l : Fin (i + 1)) = (Fin.castLE j.isLt.le l).castSucc :=
    Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- The last query after appending a response is the query of the shorter history. -/
private theorem queries_truncate_succ_last {Q R : Type*} (alg : QueryAlgorithm Q R q β)
    {i : ℕ}
    (h : Fin i → R) (r : R) :
    (alg.truncate (i + 1)).queries (Fin.snoc (α := fun _ => R) h r) (Fin.last i) =
      alg.query i h := by
  simp only [queries, truncate]
  congr 1
  funext l
  have : (Fin.castLE (Fin.last i).isLt.le l : Fin (i + 1)) =
      (Fin.cast (by simp) l : Fin i).castSucc :=
    Fin.ext rfl
  rw [this, Fin.snoc_castSucc]
  rfl

/-- Appending a column: the complement projectors are nested, and the new one kills the new
column. -/
private theorem projector_facts {𝕜 m : Type*} [RCLike 𝕜] [Fintype m] [DecidableEq m] {i : ℕ}
    {U : Matrix m (Fin i) 𝕜} {U' : Matrix m (Fin (i + 1)) 𝕜}
    (hcol : ∀ a j, U' a j.castSucc = U a j) :
    (1 - rangeProjector U') * (1 - rangeProjector U) = 1 - rangeProjector U' ∧
      (1 - rangeProjector U) * (1 - rangeProjector U') = 1 - rangeProjector U' ∧
      (1 - rangeProjector U') *ᵥ (fun a => U' a (Fin.last i)) = 0 := by
  have hle : LinearMap.range U.mulVecLin ≤ LinearMap.range U'.mulVecLin := by
    refine range_le_iff_exists_mul.2 ⟨Matrix.of fun j' j => if j' = j.castSucc then 1 else 0, ?_⟩
    ext a j
    simp [Matrix.mul_apply, hcol]
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      rangeProjector_mul_rangeProjector_of_range_le hle]
    abel
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      rangeProjector_mul_rangeProjector_of_range_le' hle]
    abel
  · have : (fun a => U' a (Fin.last i)) = U' *ᵥ Pi.single (Fin.last i) 1 := by
      ext a; simp
    rw [this, Matrix.mulVec_mulVec, one_sub_rangeProjector_mul_self, Matrix.zero_mulVec]


omit [Fintype d] [Fintype k] in
/-- The left query matrix after appending a response: old columns, then the new left part. -/
private theorem leftQueryMatrix_truncate_succ_snoc {R : Type*}
    (alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) R q β) {i : ℕ} (h : Fin i → R) (r : R) :
    (∀ a j, (alg.truncate (i + 1)).leftQueryMatrix (Fin.snoc (α := fun _ => R) h r) a j.castSucc =
      (alg.truncate i).leftQueryMatrix h a j) ∧
    (fun a => (alg.truncate (i + 1)).leftQueryMatrix (Fin.snoc (α := fun _ => R) h r) a
      (Fin.last i)) = (alg.query i h).2 := by
  refine ⟨fun a j => ?_, funext fun a => ?_⟩ <;>
    simp only [leftQueryMatrix, Matrix.of_apply, queries_truncate_succ_castSucc,
      queries_truncate_succ_last]

omit [Fintype d] [Fintype k] in
/-- The right query matrix after appending a response: old columns, then the new right part. -/
private theorem rightQueryMatrix_truncate_succ_snoc {R : Type*}
    (alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) R q β) {i : ℕ} (h : Fin i → R) (r : R) :
    (∀ a j, (alg.truncate (i + 1)).rightQueryMatrix (Fin.snoc (α := fun _ => R) h r) a j.castSucc =
      (alg.truncate i).rightQueryMatrix h a j) ∧
    (fun a => (alg.truncate (i + 1)).rightQueryMatrix (Fin.snoc (α := fun _ => R) h r) a
      (Fin.last i)) = (alg.query i h).1 := by
  refine ⟨fun a j => ?_, funext fun a => ?_⟩ <;>
    simp only [rightQueryMatrix, Matrix.of_apply, queries_truncate_succ_castSucc,
      queries_truncate_succ_last]

omit [Fintype d] [Fintype k] in
/-- The query matrices after appending a response do not depend on that response. -/
private theorem queryMatrices_truncate_succ_snoc {R : Type*}
    (alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) R q β) {i : ℕ} (h : Fin i → R) (r r' : R) :
    (alg.truncate (i + 1)).leftQueryMatrix (Fin.snoc (α := fun _ => R) h r) =
      (alg.truncate (i + 1)).leftQueryMatrix (Fin.snoc (α := fun _ => R) h r') ∧
    (alg.truncate (i + 1)).rightQueryMatrix (Fin.snoc (α := fun _ => R) h r) =
      (alg.truncate (i + 1)).rightQueryMatrix (Fin.snoc (α := fun _ => R) h r') := by
  have hq : (alg.truncate (i + 1)).queries (Fin.snoc (α := fun _ => R) h r) =
      (alg.truncate (i + 1)).queries (Fin.snoc (α := fun _ => R) h r') := by
    funext j
    induction j using Fin.lastCases with
    | last => rw [queries_truncate_succ_last, queries_truncate_succ_last]
    | cast j => rw [queries_truncate_succ_castSucc, queries_truncate_succ_castSucc]
  exact ⟨by rw [leftQueryMatrix, hq, ← leftQueryMatrix], by
    rw [rightQueryMatrix, hq, ← rightQueryMatrix]⟩

/-- The two-sided oracle is jointly measurable in the matrix and the query. -/
private theorem measurable_twoSidedMulVec {α : Type*} [MeasurableSpace α]
    {f : α → Matrix d k ℝ} {v : α → (k → ℝ) × (d → ℝ)} (hf : Measurable f) (hv : Measurable v) :
    Measurable fun a => twoSidedMulVec (f a) (v a) :=
  (hf.matrix_mulVec hv.fst).prodMk
    ((Measurable.matrix_conjTranspose continuous_star.measurable hf).matrix_mulVec hv.snd)

/-- The coordinates of a product of probability measures are independent. -/
private theorem indepFun_fst_snd' {α γ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure γ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IndepFun Prod.fst Prod.snd (μ.prod ν) :=
  indepFun_prod measurable_id measurable_id

/-- The frozen step: for fixed matrices the new response does not see the resampled block. -/
private theorem map_resample_step_eq {E E' : Matrix d d ℝ} {F F' : Matrix k k ℝ}
    (hE' : IsStarProjection E') (hF : IsStarProjection F) (hF' : IsStarProjection F')
    (hEE : E * E' = E') (hEE' : E' * E = E') (hFF : F * F' = F')
    {w : k → ℝ} {u : d → ℝ} (hw : F' *ᵥ w = 0) (hu : E' *ᵥ u = 0) (t : Matrix d k ℝ)
    {γ : Type*} [MeasurableSpace γ] {c : (d → ℝ) × (k → ℝ) → γ} (hc : Measurable c) :
    ((gaussianMatrix d k).prod (gaussianMatrix d k)).map
        (fun z => (c (twoSidedMulVec (t - E * t * F + E * z.1 * F) (w, u)),
          t - E * t * F + E * z.1 * F)) =
      ((gaussianMatrix d k).prod (gaussianMatrix d k)).map
        (fun z => (c (twoSidedMulVec (t - E * t * F + E * z.1 * F) (w, u)),
          t - E * t * F + E * z.1 * F - E' * (t - E * t * F + E * z.1 * F) * F' +
            E' * z.2 * F')) := by
  have hk : Measurable fun V : Matrix d k ℝ =>
      (c (twoSidedMulVec (t - E * t * F + V) (w, u)), t - E * t * F + V) := by
    exact (hc.comp (measurable_twoSidedMulVec (measurable_const.matrix_add measurable_id)
      measurable_const)).prodMk (measurable_const.matrix_add measurable_id)
  have h := (identDistrib_mul_mul_of_hasLaw_gaussianMatrix measurePreserving_fst.hasLaw
    measurePreserving_snd.hasLaw (indepFun_fst_snd' _ _) hE' hF hF' hEE hFF).comp hk
  refine h.map_eq.trans (congrArg (fun f => Measure.map f _) (funext fun z => ?_))
  have hY : t - E * t * F + (E * z.1 * F - E' * z.1 * F' + E' * z.2 * F') =
      t - E * t * F + E * z.1 * F + E' * (z.2 - z.1) * F' := by
    simp only [Matrix.mul_sub, Matrix.sub_mul]; abel
  have hY' : E' * (t - E * t * F + E * z.1 * F) * F' = E' * z.1 * F' := by
    have h1 : E' * (E * t * F) * F' = E' * t * F' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE', Matrix.mul_assoc _ F, hFF]
    have h2 : E' * (E * z.1 * F) * F' = E' * z.1 * F' := by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hEE', Matrix.mul_assoc _ F, hFF]
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, h1, h2]; abel
  simp only [Function.comp_apply, hY, twoSidedMulVec_add_mul_mul (v := (w, u)) hE' hw hu, hY']
  congr 1
  simp only [Matrix.mul_sub, Matrix.sub_mul]; abel

/-- Appending an entry to a tuple is measurable. -/
private theorem measurable_snoc {R : Type*} [MeasurableSpace R] {i : ℕ} :
    Measurable fun p : (Fin i → R) × R => Fin.snoc (α := fun _ => R) p.1 p.2 := by
  refine measurable_pi_iff.2 fun j => ?_
  induction j using Fin.lastCases with
  | last => simpa only [Fin.snoc_last] using measurable_snd
  | cast j =>
    simp only [Fin.snoc_castSucc]
    exact (measurable_pi_apply j).comp measurable_fst

/-- `IdentDistrib` transfers along a map that pushes one measure to the other. -/
private theorem identDistrib_comp_iff {α γ δ : Type*} [MeasurableSpace α] [MeasurableSpace γ]
    [MeasurableSpace δ] {μ : Measure α} {ν : Measure γ} {f g : α → δ} (hf : Measurable f)
    (hg : Measurable g) {e : γ → α} (he : AEMeasurable e ν) (hμ : ν.map e = μ) :
    IdentDistrib (f ∘ e) (g ∘ e) ν ν ↔ IdentDistrib f g μ μ := by
  subst hμ
  have hf' := AEMeasurable.map_map_of_aemeasurable hf.aemeasurable he
  have hg' := AEMeasurable.map_map_of_aemeasurable hg.aemeasurable he
  refine ⟨fun h => ⟨hf.aemeasurable, hg.aemeasurable, ?_⟩, fun h =>
    ⟨hf.comp_aemeasurable he, hg.comp_aemeasurable he, ?_⟩⟩
  · rw [hf', hg']; exact h.map_eq
  · rw [← hf', ← hg']; exact h.map_eq

/-- The transcript against `twoSidedMulVec (f a)` is measurable in `a`. -/
private theorem IsMeasurable.measurable_transcript_twoSidedMulVec {α : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable)
    {f : α → Matrix d k ℝ} (hf : Measurable f) :
    Measurable fun a => alg.transcript (twoSidedMulVec (f a)) :=
  halg.measurable_transcript (O := fun a => twoSidedMulVec (f a))
    (measurable_twoSidedMulVec (hf.comp measurable_fst) measurable_snd)

/-- The resampled matrix is jointly measurable in the two matrices. -/
private theorem IsMeasurable.measurable_resample [DecidableEq d] [DecidableEq k]
    [MeasurableSpace β]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable) :
    Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => alg.resample p.1 p.2 := by
  have hτ := halg.measurable_transcript_twoSidedMulVec
    (measurable_fst (α := Matrix d k ℝ) (β := Matrix d k ℝ))
  have hE := (measurable_const (a := (1 : Matrix d d ℝ))).matrix_sub
    (measurable_rangeProjector.comp (halg.measurable_leftQueryMatrix.comp hτ))
  have hF := (measurable_const (a := (1 : Matrix k k ℝ))).matrix_sub
    (measurable_rangeProjector.comp (halg.measurable_rightQueryMatrix.comp hτ))
  exact (measurable_fst.matrix_sub ((hE.matrix_mul measurable_fst).matrix_mul hF)).matrix_add
    ((hE.matrix_mul measurable_snd).matrix_mul hF)

/-- The frozen step of the induction: given the history and the matrix, the new response does
not see the block resampled at the next step. -/
private theorem identDistrib_step_freeze {T T' : Type*} [MeasurableSpace T] [MeasurableSpace T']
    {H : Matrix d k ℝ → T} (hHm : Measurable H) {E E' : T → Matrix d d ℝ}
    {F F' : T → Matrix k k ℝ} (hE'm : Measurable E') (hF'm : Measurable F')
    {Q : T → (k → ℝ) × (d → ℝ)} {c : T → (d → ℝ) × (k → ℝ) → T'} (hc : ∀ h, Measurable (c h))
    {Nx : T → Matrix d k ℝ → T'} (hNx : ∀ h y, Nx h y = c h (twoSidedMulVec y (Q h)))
    (hNxm : Measurable (Function.uncurry Nx))
    (hproj : ∀ h, IsStarProjection (E h) ∧ IsStarProjection (E' h) ∧ IsStarProjection (F h) ∧
      IsStarProjection (F' h) ∧ E h * E' h = E' h ∧ E' h * E h = E' h ∧ F h * F' h = F' h ∧
      F' h *ᵥ (Q h).1 = 0 ∧ E' h *ᵥ (Q h).2 = 0)
    {R : Matrix d k ℝ → Matrix d k ℝ → Matrix d k ℝ}
    (hR : ∀ x z, R x z = x - E (H x) * x * F (H x) + E (H x) * z * F (H x))
    (hRm : Measurable (Function.uncurry R)) :
    IdentDistrib (fun p : Matrix d k ℝ × (Matrix d k ℝ × Matrix d k ℝ) =>
        (Nx (H p.1) (R p.1 p.2.1), R p.1 p.2.1))
      (fun p => (Nx (H p.1) (R p.1 p.2.1), R p.1 p.2.1 - E' (H p.1) * R p.1 p.2.1 * F' (H p.1) +
        E' (H p.1) * p.2.2 * F' (H p.1)))
      ((gaussianMatrix d k).prod ((gaussianMatrix d k).prod (gaussianMatrix d k)))
      ((gaussianMatrix d k).prod ((gaussianMatrix d k).prod (gaussianMatrix d k))) := by
  have hR2 : Measurable fun p : Matrix d k ℝ × (Matrix d k ℝ × Matrix d k ℝ) => R p.1 p.2.1 :=
    hRm.comp (measurable_fst.prodMk measurable_snd.fst)
  have hH2 : Measurable fun p : Matrix d k ℝ × (Matrix d k ℝ × Matrix d k ℝ) => H p.1 :=
    hHm.comp measurable_fst
  have hN2 := hNxm.comp (hH2.prodMk hR2)
  have hE2 := hE'm.comp hH2
  have hF2 := hF'm.comp hH2
  refine ((indepFun_fst_snd' (gaussianMatrix d k)
    ((gaussianMatrix d k).prod (gaussianMatrix d k))).identDistrib_prodMk_of_forall_map_eq
    measurable_fst.aemeasurable measurable_snd.aemeasurable
    (F := fun t z => (Nx (H t) (R t z.1), R t z.1))
    (G := fun t z => (Nx (H t) (R t z.1), R t z.1 - E' (H t) * R t z.1 * F' (H t) +
      E' (H t) * z.2 * F' (H t))) (hN2.prodMk hR2)
    (hN2.prodMk ((hR2.matrix_sub ((hE2.matrix_mul hR2).matrix_mul hF2)).matrix_add
      ((hE2.matrix_mul measurable_snd.snd).matrix_mul hF2))) fun t => ?_).comp measurable_snd
  rw [measurePreserving_snd.map_eq]
  obtain ⟨hE1, hE'1, hF1, hF'1, hEE, hEE', hFF, hw, hu⟩ := hproj (H t)
  simp only [hNx, hR]
  exact map_resample_step_eq hE'1 hF1 hF'1 hEE hEE' hFF hw hu t (hc (H t))

/-- The induction step for abstract history, projector and next-history maps. -/
private theorem identDistrib_step_chain {T T' : Type*} [MeasurableSpace T] [MeasurableSpace T']
    {H : Matrix d k ℝ → T} (hHm : Measurable H) {E E' : T → Matrix d d ℝ}
    {F F' : T → Matrix k k ℝ} (hE'm : Measurable E') (hF'm : Measurable F')
    {Q : T → (k → ℝ) × (d → ℝ)} {c : T → (d → ℝ) × (k → ℝ) → T'} (hc : ∀ h, Measurable (c h))
    {Nx : T → Matrix d k ℝ → T'} (hNx : ∀ h y, Nx h y = c h (twoSidedMulVec y (Q h)))
    (hNxm : Measurable (Function.uncurry Nx))
    (hproj : ∀ h, IsStarProjection (E h) ∧ IsStarProjection (E' h) ∧ IsStarProjection (F h) ∧
      IsStarProjection (F' h) ∧ E h * E' h = E' h ∧ E' h * E h = E' h ∧ F h * F' h = F' h ∧
      F' h *ᵥ (Q h).1 = 0 ∧ E' h *ᵥ (Q h).2 = 0)
    {R : Matrix d k ℝ → Matrix d k ℝ → Matrix d k ℝ}
    (hR : ∀ x z, R x z = x - E (H x) * x * F (H x) + E (H x) * z * F (H x))
    (hRm : Measurable (Function.uncurry R))
    (hih : IdentDistrib (fun p : Matrix d k ℝ × Matrix d k ℝ => (H p.1, p.1))
      (fun p => (H p.1, R p.1 p.2)) ((gaussianMatrix d k).prod (gaussianMatrix d k))
      ((gaussianMatrix d k).prod (gaussianMatrix d k))) :
    IdentDistrib (fun p : Matrix d k ℝ × Matrix d k ℝ => (Nx (H p.1) p.1, p.1))
      (fun p => (Nx (H p.1) p.1,
        p.1 - E' (H p.1) * p.1 * F' (H p.1) + E' (H p.1) * p.2 * F' (H p.1)))
      ((gaussianMatrix d k).prod (gaussianMatrix d k))
      ((gaussianMatrix d k).prod (gaussianMatrix d k)) := by
  have hf1 : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => (H p.1, p.1) :=
    (hHm.comp measurable_fst).prodMk measurable_fst
  have hf2 : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => (H p.1, R p.1 p.2) :=
    (hHm.comp measurable_fst).prodMk hRm
  have S1 : IdentDistrib (fun p : Matrix d k ℝ × (Matrix d k ℝ × Matrix d k ℝ) =>
        (Nx (H p.1) p.1, p.1)) (fun p => (Nx (H p.1) (R p.1 p.2.1), R p.1 p.2.1))
      ((gaussianMatrix d k).prod ((gaussianMatrix d k).prod (gaussianMatrix d k)))
      ((gaussianMatrix d k).prod ((gaussianMatrix d k).prod (gaussianMatrix d k))) := by
    have hΨ : Measurable fun a : T × Matrix d k ℝ => (Nx a.1 a.2, a.2) :=
      hNxm.prodMk measurable_snd
    exact (identDistrib_comp_iff (hΨ.comp hf1) (hΨ.comp hf2) (e := Prod.map id Prod.fst)
      (measurable_id.prodMap measurable_fst).aemeasurable
      (MeasurePreserving.prod (MeasurePreserving.id _) measurePreserving_fst).map_eq).2
      (hih.comp hΨ)
  have S2 := identDistrib_step_freeze hHm hE'm hF'm hc hNx hNxm hproj hR hRm
  have S3 : IdentDistrib (fun p : Matrix d k ℝ × (Matrix d k ℝ × Matrix d k ℝ) =>
        (Nx (H p.1) p.1, p.1 - E' (H p.1) * p.1 * F' (H p.1) + E' (H p.1) * p.2.2 * F' (H p.1)))
      (fun p => (Nx (H p.1) (R p.1 p.2.1), R p.1 p.2.1 - E' (H p.1) * R p.1 p.2.1 * F' (H p.1) +
        E' (H p.1) * p.2.2 * F' (H p.1)))
      ((gaussianMatrix d k).prod ((gaussianMatrix d k).prod (gaussianMatrix d k)))
      ((gaussianMatrix d k).prod ((gaussianMatrix d k).prod (gaussianMatrix d k))) := by
    have h0 : IdentDistrib (Prod.map (fun p : Matrix d k ℝ × Matrix d k ℝ => (H p.1, p.1)) id)
        (Prod.map (fun p : Matrix d k ℝ × Matrix d k ℝ => (H p.1, R p.1 p.2)) id)
        (((gaussianMatrix d k).prod (gaussianMatrix d k)).prod (gaussianMatrix d k))
        (((gaussianMatrix d k).prod (gaussianMatrix d k)).prod (gaussianMatrix d k)) :=
      ⟨(hf1.prodMap measurable_id).aemeasurable, (hf2.prodMap measurable_id).aemeasurable, by
        rw [← Measure.map_prod_map _ _ hf1 measurable_id,
          ← Measure.map_prod_map _ _ hf2 measurable_id, hih.map_eq]⟩
    have hE3 : Measurable fun a : (T × Matrix d k ℝ) × Matrix d k ℝ =>
      E' a.1.1 := hE'm.comp measurable_fst.fst
    have hF3 : Measurable fun a : (T × Matrix d k ℝ) × Matrix d k ℝ =>
      F' a.1.1 := hF'm.comp measurable_fst.fst
    have hΦ : Measurable fun a : (T × Matrix d k ℝ) × Matrix d k ℝ =>
        (Nx a.1.1 a.1.2, a.1.2 - E' a.1.1 * a.1.2 * F' a.1.1 + E' a.1.1 * a.2 * F' a.1.1) :=
      (hNxm.comp measurable_fst).prodMk ((measurable_fst.snd.matrix_sub
        ((hE3.matrix_mul measurable_fst.snd).matrix_mul hF3)).matrix_add
        ((hE3.matrix_mul measurable_snd).matrix_mul hF3))
    exact (identDistrib_comp_iff (hΦ.comp (hf1.prodMap measurable_id))
      (hΦ.comp (hf2.prodMap measurable_id)) (e := MeasurableEquiv.prodAssoc.symm)
      (MeasurableEquiv.measurable _).aemeasurable
      (MeasurePreserving.symm _ (measurePreserving_prodAssoc _ _ _)).map_eq).2 (h0.comp hΦ)
  have hN1 : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => Nx (H p.1) p.1 :=
    hNxm.comp ((hHm.comp measurable_fst).prodMk measurable_fst)
  have hE1 : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => E' (H p.1) :=
    hE'm.comp (hHm.comp measurable_fst)
  have hF1 : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => F' (H p.1) :=
    hF'm.comp (hHm.comp measurable_fst)
  have hf : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => (Nx (H p.1) p.1, p.1) :=
    hN1.prodMk measurable_fst
  have hg : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => (Nx (H p.1) p.1,
      p.1 - E' (H p.1) * p.1 * F' (H p.1) + E' (H p.1) * p.2 * F' (H p.1)) :=
    hN1.prodMk ((measurable_fst.matrix_sub ((hE1.matrix_mul measurable_fst).matrix_mul
      hF1)).matrix_add ((hE1.matrix_mul measurable_snd).matrix_mul hF1))
  exact (identDistrib_comp_iff hf hg (e := Prod.map id Prod.snd)
    (measurable_id.prodMap measurable_snd).aemeasurable
    (MeasurePreserving.prod (MeasurePreserving.id _) measurePreserving_snd).map_eq).1
    ((S1.trans S2).trans S3.symm)

/-- The induction step of the deferred decision invariant. -/
private theorem identDistrib_truncate_resample_succ [DecidableEq d] [DecidableEq k]
    [MeasurableSpace β]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable)
    {i : ℕ} (hi : i < q)
    (ih : IdentDistrib
      (fun p : Matrix d k ℝ × Matrix d k ℝ =>
        ((alg.truncate i).transcript (twoSidedMulVec p.1), p.1))
      (fun p => ((alg.truncate i).transcript (twoSidedMulVec p.1),
        (alg.truncate i).resample p.1 p.2))
      ((gaussianMatrix d k).prod (gaussianMatrix d k))
      ((gaussianMatrix d k).prod (gaussianMatrix d k))) :
    IdentDistrib
      (fun p : Matrix d k ℝ × Matrix d k ℝ =>
        ((alg.truncate (i + 1)).transcript (twoSidedMulVec p.1), p.1))
      (fun p => ((alg.truncate (i + 1)).transcript (twoSidedMulVec p.1),
        (alg.truncate (i + 1)).resample p.1 p.2))
      ((gaussianMatrix d k).prod (gaussianMatrix d k))
      ((gaussianMatrix d k).prod (gaussianMatrix d k)) := by
  have halgi := halg.truncate hi.le
  obtain ⟨H, hH⟩ : ∃ H : Matrix d k ℝ → Fin i → (d → ℝ) × (k → ℝ),
      H = fun x => (alg.truncate i).transcript (twoSidedMulVec x) := ⟨_, rfl⟩
  have hHm : Measurable H := hH ▸ halgi.measurable_transcript_twoSidedMulVec measurable_id
  obtain ⟨E, hE⟩ : ∃ E : (Fin i → (d → ℝ) × (k → ℝ)) → Matrix d d ℝ,
      E = fun h => 1 - rangeProjector ((alg.truncate i).leftQueryMatrix h) := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F : (Fin i → (d → ℝ) × (k → ℝ)) → Matrix k k ℝ,
      F = fun h => 1 - rangeProjector ((alg.truncate i).rightQueryMatrix h) := ⟨_, rfl⟩
  obtain ⟨E', hE'⟩ : ∃ E' : (Fin i → (d → ℝ) × (k → ℝ)) → Matrix d d ℝ, E' = fun h =>
      1 - rangeProjector ((alg.truncate (i + 1)).leftQueryMatrix (Fin.snoc h 0)) := ⟨_, rfl⟩
  obtain ⟨F', hF'⟩ : ∃ F' : (Fin i → (d → ℝ) × (k → ℝ)) → Matrix k k ℝ, F' = fun h =>
      1 - rangeProjector ((alg.truncate (i + 1)).rightQueryMatrix (Fin.snoc h 0)) := ⟨_, rfl⟩
  obtain ⟨Nx, hNx⟩ : ∃ Nx : (Fin i → (d → ℝ) × (k → ℝ)) → Matrix d k ℝ → _,
      Nx = fun h y => Fin.snoc (α := fun _ => (d → ℝ) × (k → ℝ)) h
        (twoSidedMulVec y (alg.query i h)) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R : Matrix d k ℝ → Matrix d k ℝ → Matrix d k ℝ,
      R = fun x z => x - E (H x) * x * F (H x) + E (H x) * z * F (H x) := ⟨_, rfl⟩
  have hsnoc : Measurable fun h : Fin i → (d → ℝ) × (k → ℝ) => Fin.snoc
      (α := fun _ => (d → ℝ) × (k → ℝ)) h 0 := measurable_snoc.comp (measurable_id.prodMk
    measurable_const)
  have hEm : Measurable E := hE ▸ (measurable_const (a := (1 : Matrix d d ℝ))).matrix_sub
    (measurable_rangeProjector.comp halgi.measurable_leftQueryMatrix)
  have hFm : Measurable F := hF ▸ (measurable_const (a := (1 : Matrix k k ℝ))).matrix_sub
    (measurable_rangeProjector.comp halgi.measurable_rightQueryMatrix)
  have hE'm : Measurable E' := hE' ▸ (measurable_const (a := (1 : Matrix d d ℝ))).matrix_sub
    (measurable_rangeProjector.comp ((halg.truncate hi).measurable_leftQueryMatrix.comp hsnoc))
  have hF'm : Measurable F' := hF' ▸ (measurable_const (a := (1 : Matrix k k ℝ))).matrix_sub
    (measurable_rangeProjector.comp ((halg.truncate hi).measurable_rightQueryMatrix.comp hsnoc))
  have hNxm : Measurable (Function.uncurry Nx) := hNx ▸ measurable_snoc.comp
    (measurable_fst.prodMk (measurable_twoSidedMulVec measurable_snd
      ((halg.measurable_query i hi).comp measurable_fst)))
  have hRm : Measurable (Function.uncurry R) := by
    have hE1 : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => E (H p.1) :=
      hEm.comp (hHm.comp measurable_fst)
    have hF1 : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ => F (H p.1) :=
      hFm.comp (hHm.comp measurable_fst)
    exact hR ▸ (measurable_fst.matrix_sub ((hE1.matrix_mul measurable_fst).matrix_mul
      hF1)).matrix_add ((hE1.matrix_mul measurable_snd).matrix_mul hF1)
  have hproj : ∀ h, IsStarProjection (E h) ∧ IsStarProjection (E' h) ∧ IsStarProjection (F h) ∧
      IsStarProjection (F' h) ∧ E h * E' h = E' h ∧ E' h * E h = E' h ∧ F h * F' h = F' h ∧
      F' h *ᵥ (alg.query i h).1 = 0 ∧ E' h *ᵥ (alg.query i h).2 = 0 := fun h => by
    obtain ⟨hl, hl'⟩ := leftQueryMatrix_truncate_succ_snoc alg h 0
    obtain ⟨hr, hr'⟩ := rightQueryMatrix_truncate_succ_snoc alg h 0
    obtain ⟨e1, e2, e3⟩ := projector_facts hl
    obtain ⟨f1, f2, f3⟩ := projector_facts hr
    subst hE hE' hF hF'
    exact ⟨isStarProjection_one_sub_rangeProjector _, isStarProjection_one_sub_rangeProjector _,
      isStarProjection_one_sub_rangeProjector _, isStarProjection_one_sub_rangeProjector _, e2, e1,
      f2, hr' ▸ f3, hl' ▸ e3⟩
  have hT1 : ∀ x, (alg.truncate (i + 1)).transcript (twoSidedMulVec x) = Nx (H x) x := fun x => by
    rw [transcript_truncate_succ]; subst hNx hH; rfl
  have hR1 : ∀ x z, (alg.truncate (i + 1)).resample x z =
      x - E' (H x) * x * F' (H x) + E' (H x) * z * F' (H x) := fun x z => by
    have hl := queryMatrices_truncate_succ_snoc alg (H x) (twoSidedMulVec x (alg.query i (H x))) 0
    simp only [resample, hT1, hNx, hl.1, hl.2, hE', hF']
  have hih : IdentDistrib (fun p : Matrix d k ℝ × Matrix d k ℝ => (H p.1, p.1))
      (fun p => (H p.1, R p.1 p.2)) ((gaussianMatrix d k).prod (gaussianMatrix d k))
      ((gaussianMatrix d k).prod (gaussianMatrix d k)) := by
    subst hH hR hE hF; exact ih
  simp only [hT1, hR1]
  exact identDistrib_step_chain hHm hE'm hF'm (c := fun h r => Fin.snoc h r) (Q := alg.query i)
    (fun h => measurable_snoc.comp (measurable_const.prodMk measurable_id))
    (fun h y => by rw [hNx]) hNxm hproj (fun x z => by rw [hR]) hRm hih

/-- The deferred decision invariant for the first `i` queries, on the canonical space. -/
private theorem identDistrib_truncate_resample [DecidableEq d] [DecidableEq k]
    [MeasurableSpace β]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable)
    (i : ℕ) (hi : i ≤ q) :
    IdentDistrib
      (fun p : Matrix d k ℝ × Matrix d k ℝ =>
        ((alg.truncate i).transcript (twoSidedMulVec p.1), p.1))
      (fun p => ((alg.truncate i).transcript (twoSidedMulVec p.1),
        (alg.truncate i).resample p.1 p.2))
      ((gaussianMatrix d k).prod (gaussianMatrix d k))
      ((gaussianMatrix d k).prod (gaussianMatrix d k)) := by
  induction i with
  | zero =>
    have hR : ∀ p : Matrix d k ℝ × Matrix d k ℝ, (alg.truncate 0).resample p.1 p.2 = p.2 :=
      fun p => by
        simp only [resample, Subsingleton.elim ((alg.truncate 0).leftQueryMatrix _) 0,
          Subsingleton.elim ((alg.truncate 0).rightQueryMatrix _) 0, rangeProjector_zero,
          sub_zero, Matrix.one_mul, Matrix.mul_one, sub_self, zero_add]
    have hτ : ∀ p : Matrix d k ℝ × Matrix d k ℝ,
        (alg.truncate 0).transcript (twoSidedMulVec p.1) = Fin.elim0 :=
      fun _ => Subsingleton.elim _ _
    simp only [hR, hτ]
    exact (IdentDistrib.mk measurable_fst.aemeasurable measurable_snd.aemeasurable
      (by rw [measurePreserving_fst.map_eq, measurePreserving_snd.map_eq])).comp
      measurable_prodMk_left
  | succ i ih => exact identDistrib_truncate_resample_succ halg hi (ih (by omega))

/-- **Adaptive deferred decision for a Gaussian matrix, resampling form**: let
$\mathbf{X}, \mathbf{X}'$ be independent standard Gaussian $d \times k$ matrices and $\tau$ the
transcript of a measurable algorithm making `q` adaptive pair queries to `twoSidedMulVec X`
(products $\mathbf{X}\mathbf{w}$ and $\mathbf{X}^{\mathsf{H}}\mathbf{u}$). With
$\mathbf{E}$, $\mathbf{F}$ the projectors onto the orthogonal complements of the left and right
queries, $(\tau, \mathbf{X})$ has the law of $(\tau, \widetilde{\mathbf{X}})$,
$$\widetilde{\mathbf{X}} = \mathbf{X} - \mathbf{E}\mathbf{X}\mathbf{F} +
\mathbf{E}\mathbf{X}'\mathbf{F}\,:$$
conditionally on the transcript, the unqueried block is a fresh Gaussian block. With
`QueryAlgorithm.transcript_resample`, $\tau$ is also the transcript of $\widetilde{\mathbf{X}}$.
[ZhangEtAl2026, Lemma 4.1]; [BravermanHazanSimchowitzWoodworth2020, Lemma 3.4]; there with
entries $\mathcal{N}(0, 1/d)$, orthonormal queries, at most $s$ of them, and a $\sigma$-field,
conditional laws and a transcript-measurable rotation; here unit variance, basis-free (no
orthonormality assumption on the queries) and no bound on `q`. -/
theorem IsMeasurable.identDistrib_resample_of_hasLaw_gaussianMatrix [DecidableEq d]
    [DecidableEq k] [MeasurableSpace β]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable)
    {X X' : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    (hX' : HasLaw X' (gaussianMatrix d k) μ) (hXX' : IndepFun X X' μ) :
    IdentDistrib (fun ω => (alg.transcript (twoSidedMulVec (X ω)), X ω))
      (fun ω => (alg.transcript (twoSidedMulVec (X ω)), alg.resample (X ω) (X' ω))) μ μ := by
  have := hX.isProbabilityMeasure
  have hZ : AEMeasurable (fun ω => (X ω, X' ω)) μ := hX.aemeasurable.prodMk hX'.aemeasurable
  have hμ : μ.map (fun ω => (X ω, X' ω)) = (gaussianMatrix d k).prod (gaussianMatrix d k) := by
    rw [(indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hX'.aemeasurable).1 hXX',
      hX.map_eq, hX'.map_eq]
  have h := identDistrib_truncate_resample halg q le_rfl
  have hf : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ =>
      ((alg.truncate q).transcript (twoSidedMulVec p.1), p.1) :=
    ((halg.truncate le_rfl).measurable_transcript_twoSidedMulVec measurable_fst).prodMk
      measurable_fst
  have hg : Measurable fun p : Matrix d k ℝ × Matrix d k ℝ =>
      ((alg.truncate q).transcript (twoSidedMulVec p.1), (alg.truncate q).resample p.1 p.2) :=
    ((halg.truncate le_rfl).measurable_transcript_twoSidedMulVec measurable_fst).prodMk
      (halg.truncate le_rfl).measurable_resample
  have := (identDistrib_comp_iff hf hg hZ hμ).2 h
  simp only [Function.comp_def, transcript_truncate, resample] at this
  exact this

/-- **Adaptive deferred decision for a Gaussian matrix, frame form**: let $\tau$ be the transcript
of a measurable algorithm making `q` adaptive pair queries to `twoSidedMulVec X`, for a standard
Gaussian $\mathbf{X} \in \mathbb{R}^{d \times k}$. For frames
$\mathbf{W}_L(\tau) \in \mathbb{R}^{d \times r}$ and
$\mathbf{W}_R(\tau) \in \mathbb{R}^{k \times s}$ (orthonormal columns), chosen measurably
from the transcript and orthogonal to all left, respectively right, queries, the block
$\mathbf{W}_L^{\mathsf{H}}\mathbf{X}\mathbf{W}_R$ is a standard Gaussian $r \times s$ matrix
independent of $\tau$: $(\tau, \mathbf{W}_L^{\mathsf{H}}\mathbf{X}\mathbf{W}_R)$ has law
$\mathbb{P}_\tau \otimes \mathcal{N}(0, 1)^{r \times s}$.
[ZhangEtAl2026, Lemma 4.1] (the block $\mathbf{D}_t$; there entries $\mathcal{N}(0, 1/d)$,
orthonormal queries and at most $s$ of them, here unit variance, any queries, no bound on `q`);
[Shamir2026, Lemma 3] (the Haar analogue, non-adaptive).
For a non-adaptive algorithm the frames may be fixed, and this is
`NLAlib.indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix` on both sides. -/
theorem IsMeasurable.hasLaw_prodMk_conjTranspose_mul_mul_of_hasLaw_gaussianMatrix
    [MeasurableSpace β] {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]
    {alg : QueryAlgorithm ((k → ℝ) × (d → ℝ)) ((d → ℝ) × (k → ℝ)) q β} (halg : alg.IsMeasurable)
    {X : Ω → Matrix d k ℝ} (hX : HasLaw X (gaussianMatrix d k) μ)
    {WL : (Fin q → (d → ℝ) × (k → ℝ)) → Matrix d r ℝ}
    {WR : (Fin q → (d → ℝ) × (k → ℝ)) → Matrix k s ℝ}
    (hWLm : Measurable WL) (hWRm : Measurable WR) (hWLo : ∀ τ, HasOrthonormalCols (WL τ))
    (hWRo : ∀ τ, HasOrthonormalCols (WR τ)) (hWL : ∀ τ, (WL τ)ᴴ * alg.leftQueryMatrix τ = 0)
    (hWR : ∀ τ, (WR τ)ᴴ * alg.rightQueryMatrix τ = 0) :
    HasLaw (fun ω => (alg.transcript (twoSidedMulVec (X ω)),
        (WL (alg.transcript (twoSidedMulVec (X ω))))ᴴ * X ω *
          WR (alg.transcript (twoSidedMulVec (X ω)))))
      ((μ.map fun ω => alg.transcript (twoSidedMulVec (X ω))).prod (gaussianMatrix r s)) μ := by
  classical
  have := hX.isProbabilityMeasure
  set τ : Matrix d k ℝ → Fin q → (d → ℝ) × (k → ℝ) :=
    fun A => alg.transcript (twoSidedMulVec A)
  have hτ : Measurable τ := halg.measurable_transcript_twoSidedMulVec measurable_id
  -- the frame block, as a function of the transcript and a matrix
  set F : (Fin q → (d → ℝ) × (k → ℝ)) → Matrix d k ℝ → Matrix r s ℝ :=
    fun t Y => (WL t)ᴴ * Y * WR t
  have hF : Measurable (Function.uncurry F) :=
    ((continuous_star.measurable.matrix_conjTranspose (hWLm.comp measurable_fst)).matrix_mul
      measurable_snd).matrix_mul (hWRm.comp measurable_fst)
  set μ' := μ.prod (gaussianMatrix d k)
  have hfst : μ'.map Prod.fst = μ := (measurePreserving_fst (μ := μ)).map_eq
  have hX₁ : HasLaw (fun p : Ω × Matrix d k ℝ => X p.1) (gaussianMatrix d k) μ' :=
    hX.fun_comp ⟨measurable_fst.aemeasurable, hfst⟩
  have hX₂ : HasLaw (fun p : Ω × Matrix d k ℝ => p.2) (gaussianMatrix d k) μ' :=
    measurePreserving_snd.hasLaw
  have hind : IndepFun (fun p : Ω × Matrix d k ℝ => X p.1) (fun p => p.2) μ' :=
    indepFun_prod₀ hX.aemeasurable aemeasurable_id
  have hres := (halg.identDistrib_resample_of_hasLaw_gaussianMatrix hX₁ hX₂ hind).comp
    (measurable_fst.prodMk hF)
  have hfrz : HasLaw (fun p : Ω × Matrix d k ℝ => (τ (X p.1), F (τ (X p.1)) p.2))
      ((μ.map fun ω => τ (X ω)).prod (gaussianMatrix r s)) μ' := by
    have hT := hτ.comp_aemeasurable hX.aemeasurable
    have hmap : μ'.map (fun p => τ (X p.1)) = μ.map fun ω => τ (X ω) := by
      conv_rhs => rw [← hfst]
      exact (AEMeasurable.map_map_of_aemeasurable (hfst ▸ hT) measurable_fst.aemeasurable).symm
    rw [← hmap]
    refine (indepFun_prod₀ hT aemeasurable_id).hasLaw_prodMk_prod_of_forall_map_eq
      (hτ.comp_aemeasurable hX₁.aemeasurable) measurable_snd.aemeasurable hF fun t => ?_
    change (μ'.map fun p => p.2).map (F t) = _
    rw [hX₂.map_eq]
    exact (hasLaw_mul_mul_of_hasLaw_gaussianMatrix HasLaw.id
      (by simpa using hWLo t) (hWRo t)).map_eq
  -- the frames see neither correction term: `WLᴴ * Pₗ = 0` and `Pᵣ * WR = 0`
  have hblock : ∀ A Y, F (τ A) (alg.resample A Y) = F (τ A) Y := by
    intro A Y
    have hL0 : (WL (τ A))ᴴ * rangeProjector (alg.leftQueryMatrix (τ A)) = 0 := by
      have h := congrArg Matrix.conjTranspose (rangeProjector_mul_eq_zero_iff.2 (by
        simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (hWL (τ A))) :
        rangeProjector (alg.leftQueryMatrix (τ A)) * WL (τ A) = 0)
      rwa [Matrix.conjTranspose_mul, conjTranspose_rangeProjector, Matrix.conjTranspose_zero] at h
    have hL : ∀ M : Matrix d s ℝ,
        (WL (τ A))ᴴ * (rangeProjector (alg.leftQueryMatrix (τ A)) * M) = 0 := fun M => by
      rw [← Matrix.mul_assoc, hL0, Matrix.zero_mul]
    have hR0 : rangeProjector (alg.rightQueryMatrix (τ A)) * WR (τ A) = 0 :=
      rangeProjector_mul_eq_zero_iff.2 (by
        simpa [Matrix.conjTranspose_mul] using congrArg Matrix.conjTranspose (hWR (τ A)))
    change (WL (τ A))ᴴ * (A - (1 - rangeProjector (alg.leftQueryMatrix (τ A))) * A *
        (1 - rangeProjector (alg.rightQueryMatrix (τ A))) +
        (1 - rangeProjector (alg.leftQueryMatrix (τ A))) * Y *
        (1 - rangeProjector (alg.rightQueryMatrix (τ A)))) * WR (τ A) =
      (WL (τ A))ᴴ * Y * WR (τ A)
    simp only [Matrix.mul_add, Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc,
      Matrix.one_mul, hR0, hL, Matrix.mul_zero]
    abel
  have hG : Measurable fun A => (τ A, F (τ A) A) :=
    hτ.prodMk (hF.comp (hτ.prodMk measurable_id) : Measurable fun A => Function.uncurry F (τ A, A))
  have hGX := hG.comp_aemeasurable hX.aemeasurable
  change HasLaw ((fun A => (τ A, F (τ A) A)) ∘ X) _ μ
  refine ⟨hGX, ?_⟩
  conv_lhs => rw [← hfst]
  rw [AEMeasurable.map_map_of_aemeasurable (hfst ▸ hGX) measurable_fst.aemeasurable]
  refine hres.map_eq.trans (Eq.trans ?_ hfrz.map_eq)
  congr 1
  funext p
  exact Prod.ext rfl (hblock _ _)

end QueryAlgorithm

end NLAlib
