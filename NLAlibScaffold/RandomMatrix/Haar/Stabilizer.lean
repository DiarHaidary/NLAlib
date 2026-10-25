/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.RandomMatrix.Haar.Basic
public import NLAlib.RandomMatrix.UnitaryInvariance
public import NLAlibScaffold.ForMathlib.Probability.Independence.Basic

/-!
# The stabilizer form of right unitary invariance

Statements for `NLAlib/RandomMatrix/Haar/Stabilizer.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.4). For a right unitarily invariant law
(Gaussian, Haar) of $\mathbf{X}$ and a fixed block of queries $\mathbf{V}$, the matrix may be
rotated on the right by any orthogonal matrix that fixes $\mathbf{V}$, chosen as a function of the
response $\mathbf{X}\mathbf{V}$, without changing the joint law of response and matrix. The
adaptive form is
`NLAlib.QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`.

## Main results

* `NLAlib.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`: the non-adaptive stabilizer
  form.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

variable {m n : Type*} [Fintype n] [DecidableEq n]

/-- A frame of the orthogonal complement of the columns of `V`: $\mathbf{W}$ has orthonormal
columns, $\mathbf{W}^{\mathsf{H}}\mathbf{V} = \mathbf{0}$, and every $\mathbf{T}$ fixing
$\mathbf{V}$ fixes $\mathbf{I} - \mathbf{W}\mathbf{W}^{\mathsf{H}}$. -/
private theorem exists_hasOrthonormalCols_conjTranspose_mul_eq_zero {p : Type*}
    (V : Matrix n p ℝ) :
    ∃ (c : Type) (_ : Fintype c) (_ : DecidableEq c) (W : Matrix n c ℝ),
      HasOrthonormalCols W ∧ Wᴴ * V = 0 ∧
        ∀ T : Matrix n n ℝ, T * V = V → T * (1 - W * Wᴴ) = 1 - W * Wᴴ := by
  obtain ⟨f, hf, hspan, -⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (Set.range fun j i => V i j)
  set A : Matrix n _ ℝ := Matrix.of fun i k => f k i
  obtain ⟨W, hW, hWW⟩ :=
    (isStarProjection_one_sub_rangeProjector A).exists_hasOrthonormalCols_mul_conjTranspose_eq
      (p := Fin (1 - rangeProjector A).rank) (Fintype.card_fin _)
  have hP : 1 - W * Wᴴ = rangeProjector A := by rw [hWW, sub_sub_cancel]
  refine ⟨_, inferInstance, inferInstance, W, hW, ?_, fun T hT => ?_⟩
  · have hPV : rangeProjector A * V = V := by
      ext i j
      have hv : (fun l => V l j) ∈ LinearMap.range A.mulVecLin := by
        rw [Matrix.range_mulVecLin]
        have : Set.range A.col = Set.range f := rfl
        rw [this, hspan]
        exact Submodule.subset_span ⟨j, rfl⟩
      obtain ⟨w, hw⟩ := hv
      have := congrFun (congrArg (· *ᵥ w) (rangeProjector_mul_self A)) i
      simp only [← Matrix.mulVec_mulVec] at this
      change (rangeProjector A *ᵥ A.mulVecLin w) i = _ at this
      rw [hw] at this
      rw [show (A *ᵥ w) i = V i j from congrFun hw i] at this
      exact this
    rw [← hW.conjTranspose_mul_cancel_left (Wᴴ * V), ← Matrix.mul_assoc W, hWW,
      Matrix.sub_mul, Matrix.one_mul, hPV, sub_self, Matrix.mul_zero]
  · have hTA : T * A = A := by
      ext i k
      obtain ⟨j, hj⟩ := hf k
      have := congrFun (congrFun hT i) j
      simp only [Matrix.mul_apply] at this ⊢
      simpa [A, ← hj] using this
    rw [hP, ← mul_pinv, ← Matrix.mul_assoc, hTA]

/-- The block rotation $\mathbf{I} + \mathbf{W}(\mathbf{o} - \mathbf{I})\mathbf{W}^{\mathsf{H}}$
of a frame $\mathbf{W}$ by an orthogonal $\mathbf{o}$ is orthogonal. -/
private theorem hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose {c : Type*} [Fintype c]
    [DecidableEq c] {W : Matrix n c ℝ} (hW : HasOrthonormalCols W) {o : Matrix c c ℝ}
    (ho : HasOrthonormalCols o) : HasOrthonormalCols (1 + W * (o - 1) * Wᴴ) := by
  rw [hasOrthonormalCols_iff]
  have hM : (oᴴ - 1) + (o - 1) + (oᴴ - 1) * (o - 1) = 0 := by
    rw [sub_mul, mul_sub, mul_sub, ho.conjTranspose_mul_self, Matrix.mul_one, Matrix.one_mul,
      Matrix.one_mul]
    abel
  calc (1 + W * (o - 1) * Wᴴ)ᴴ * (1 + W * (o - 1) * Wᴴ)
      = 1 + W * ((oᴴ - 1) + (o - 1) + (oᴴ - 1) * (Wᴴ * W) * (o - 1)) * Wᴴ := by
        simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one, Matrix.conjTranspose_mul,
          Matrix.conjTranspose_sub, Matrix.conjTranspose_conjTranspose, Matrix.add_mul,
          Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
        abel
    _ = 1 := by
      rw [hW.conjTranspose_mul_self, Matrix.mul_one, hM, Matrix.mul_zero, Matrix.zero_mul,
        add_zero]

/-- Block rotations of a frame compose:
$(\mathbf{I} + \mathbf{W}(\mathbf{o} - \mathbf{I})\mathbf{W}^{\mathsf{H}})
(\mathbf{I} + \mathbf{W}(\mathbf{s} - \mathbf{I})\mathbf{W}^{\mathsf{H}})
= \mathbf{I} + \mathbf{W}(\mathbf{o}\mathbf{s} - \mathbf{I})\mathbf{W}^{\mathsf{H}}$. -/
private theorem one_add_mul_sub_one_mul_conjTranspose_mul {c : Type*} [Fintype c]
    [DecidableEq c] {W : Matrix n c ℝ} (hW : HasOrthonormalCols W) (o s : Matrix c c ℝ) :
    (1 + W * (o - 1) * Wᴴ) * (1 + W * (s - 1) * Wᴴ) = 1 + W * (o * s - 1) * Wᴴ := by
  have ho : o * s - 1 = (o - 1) + (s - 1) + (o - 1) * (s - 1) := by noncomm_ring
  simp only [ho, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, hW.conjTranspose_mul_cancel_left]
  abel

/-- An orthogonal $\mathbf{T}$ fixing $\mathbf{I} - \mathbf{W}\mathbf{W}^{\mathsf{H}}$ is the block
rotation of the frame $\mathbf{W}$ by the orthogonal
$\mathbf{s} = \mathbf{W}^{\mathsf{H}}\mathbf{T}\mathbf{W}$. -/
private theorem HasOrthonormalCols.eq_one_add_mul_sub_one_mul_conjTranspose {c : Type*}
    [Fintype c] [DecidableEq c] {T : Matrix n n ℝ} (hT : HasOrthonormalCols T)
    {W : Matrix n c ℝ} (hW : HasOrthonormalCols W) (hTP : T * (1 - W * Wᴴ) = 1 - W * Wᴴ) :
    HasOrthonormalCols (Wᴴ * T * W) ∧ T = 1 + W * (Wᴴ * T * W - 1) * Wᴴ := by
  have hPT : (1 - W * Wᴴ) * T = 1 - W * Wᴴ := by
    have h : Tᴴ * (1 - W * Wᴴ) = 1 - W * Wᴴ := by
      rw [← hTP, ← Matrix.mul_assoc, hT.conjTranspose_mul_self, Matrix.one_mul, hTP]
    simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      Matrix.conjTranspose_conjTranspose] using congrArg Matrix.conjTranspose h
  have hTW : T * W = W * (Wᴴ * T * W) := by
    have h := congrArg (· * W) hPT
    simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc,
      hW.conjTranspose_mul_self, Matrix.mul_one, sub_self] at h
    rw [← sub_eq_zero, ← h, Matrix.mul_assoc]
  refine ⟨?_, ?_⟩
  · rw [hasOrthonormalCols_iff]
    calc (Wᴴ * T * W)ᴴ * (Wᴴ * T * W) = (W * (Wᴴ * T * W))ᴴ * (W * (Wᴴ * T * W)) := by
          rw [Matrix.conjTranspose_mul W, Matrix.mul_assoc _ Wᴴ, hW.conjTranspose_mul_cancel_left]
      _ = 1 := by
          rw [← hTW, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Tᴴ,
            hT.conjTranspose_mul_self, Matrix.one_mul, hW.conjTranspose_mul_self]
  · calc T = T * (1 - W * Wᴴ) + T * W * Wᴴ := by
          rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, sub_add_cancel]
      _ = 1 + W * (Wᴴ * T * W - 1) * Wᴴ := by
          rw [hTP, hTW, Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
          abel

/-- A random element of the stabilizer of `V`: with $\mathbf{W}$ a frame of the orthogonal
complement of the columns of $\mathbf{V}$, the measurable map
$R(\mathbf{o}) = \mathbf{I} + \mathbf{W}(\mathbf{o} - \mathbf{I})\mathbf{W}^{\mathsf{H}}$
(set to $\mathbf{I}$ off the orthogonal matrices) takes orthogonal values fixing $\mathbf{V}$,
and for a Haar $\mathbf{O}$, $R(\mathbf{O})\mathbf{T}$ has the law of $R(\mathbf{O})$ for every
orthogonal $\mathbf{T}$ fixing $\mathbf{V}$. -/
private theorem exists_measurable_stabilizer {p : Type*} (V : Matrix n p ℝ) :
    ∃ (c : Type) (_ : Fintype c) (_ : DecidableEq c) (R : Matrix c c ℝ → Matrix n n ℝ),
      Measurable R ∧ (∀ o, HasOrthonormalCols (R o)) ∧ (∀ o, R o * V = V) ∧
        ∀ T, HasOrthonormalCols T → T * V = V →
          (haarFrame c c).map (fun o => R o * T) = (haarFrame c c).map R := by
  obtain ⟨c, _, _, W, hW, hWV, hfix⟩ := exists_hasOrthonormalCols_conjTranspose_mul_eq_zero V
  classical
  set R : Matrix c c ℝ → Matrix n n ℝ :=
    fun o => if HasOrthonormalCols o then 1 + W * (o - 1) * Wᴴ else 1 with hR
  have hRo : ∀ o, HasOrthonormalCols (R o) := fun o => by
    simp only [hR]
    split_ifs with ho
    exacts [hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose hW ho, hasOrthonormalCols_one]
  have hRV : ∀ o, R o * V = V := fun o => by
    simp only [hR]
    split_ifs
    exacts [by rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hWV, Matrix.mul_zero,
      add_zero], Matrix.one_mul V]
  have hRm : Measurable R := Measurable.ite isClosed_setOf_hasOrthonormalCols.measurableSet
    (by fun_prop : Continuous fun o : Matrix c c ℝ => 1 + W * (o - 1) * Wᴴ).measurable
    measurable_const
  have hmr : ∀ T : Matrix c c ℝ, Measurable fun o : Matrix c c ℝ => o * T := fun T =>
    measurable_id.matrix_mul measurable_const
  have hRS : ∀ T, HasOrthonormalCols T → T * V = V →
      (haarFrame c c).map (fun o => R o * T) = (haarFrame c c).map R := by
    intro T hT hTV
    obtain ⟨hs, hTeq⟩ :=
      hT.eq_one_add_mul_sub_one_mul_conjTranspose hW (hfix T hTV)
    rw [Measure.map_congr (g := R ∘ (· * (Wᴴ * T * W))), ← Measure.map_map hRm (hmr _),
      IsRightUnitarilyInvariant.map_mul_right_eq_self _ hs]
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame HasLaw.id le_rfl] with o ho
    replace ho : HasOrthonormalCols o := ho
    simp only [Function.comp_apply, hR]
    rw [if_pos ho, if_pos (ho.mul hs)]
    conv_lhs => rw [hTeq]
    exact one_add_mul_sub_one_mul_conjTranspose_mul hW _ _
  exact ⟨c, inferInstance, inferInstance, R, hRm, hRo, hRV, hRS⟩

/-- **Deferred decision for a unitarily invariant law, non-adaptive stabilizer form**: let the law
$\nu$ of $\mathbf{X} \in \mathbb{R}^{m \times n}$ be right unitarily invariant (Gaussian, Haar),
$\mathbf{V} \in \mathbb{R}^{n \times p}$ fixed, and $\mathbf{S}(\mathbf{Y})$ an orthogonal matrix
chosen measurably from the response $\mathbf{Y} = \mathbf{X}\mathbf{V}$ with
$\mathbf{S}(\mathbf{Y})\mathbf{V} = \mathbf{V}$. Then $(\mathbf{X}\mathbf{V}, \mathbf{X})$ has the
law of $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{S}(\mathbf{X}\mathbf{V}))$: given what the
queries revealed, $\mathbf{X}$ is invariant under the rotations that fix the queries.
[Shamir2026, Lemma 3]; there for a Haar orthogonal matrix and a fixed subspace, stated with
conditional laws.
Proof: L, about 60 lines. Fix a frame $\mathbf{W} \in \mathbb{R}^{n \times c}$ of the orthogonal
complement of the column span of $\mathbf{V}$
(`c := Fin (card n - finrank (span (range Vᵀ)))` internally, so `p` need not be finite; the
library's orthonormal completion), and on the extended space `μ.prod (haarFrame c c)` let
$\mathbf{O}_s = \mathbf{I} - \mathbf{W}\mathbf{W}^{\mathsf{H}} +
\mathbf{W}\mathbf{O}\mathbf{W}^{\mathsf{H}}$,
a random orthogonal matrix fixing $\mathbf{V}$, independent of $\mathbf{X}$. (1)
$(\mathbf{X}\mathbf{V}, \mathbf{X})$ and $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s)$ have
the same law by
freezing `ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq` with $T = \mathbf{O}$
and right invariance (`hasLaw_mul_const_of_isRightUnitarilyInvariant`), since
$\mathbf{O}_s\mathbf{V} = \mathbf{V}$. (2) Every orthogonal $\mathbf{S}$ fixing $\mathbf{V}$ is
$\mathbf{I} - \mathbf{W}\mathbf{W}^{\mathsf{H}} + \mathbf{W}\mathbf{s}\mathbf{W}^{\mathsf{H}}$ with
$\mathbf{s}$ orthogonal, so $\mathbf{O}_s\mathbf{S}$ has the law of $\mathbf{O}_s$
(`isRightUnitarilyInvariant_haarFrame`). Freezing with $T = \mathbf{X}$, $Z = \mathbf{O}$ shows
that $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s\mathbf{S}(\mathbf{X}\mathbf{V}))$ and
$(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s)$ have the same law. (3) Pushing (1) forward by
the measurable $\Phi(\mathbf{Y}, \mathbf{Z}) = (\mathbf{Y}, \mathbf{Z}\mathbf{S}(\mathbf{Y}))$
(`IdentDistrib.comp`) and using $\mathbf{X}\mathbf{O}_s\mathbf{V} = \mathbf{X}\mathbf{V}$, the
pair $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{S}(\mathbf{X}\mathbf{V}))$ has the law of
$(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{O}_s\mathbf{S}(\mathbf{X}\mathbf{V}))$; chain (3), (2),
(1). -/
theorem identDistrib_prodMk_mul_of_isRightUnitarilyInvariant [IsProbabilityMeasure μ]
    {p : Type*} {ν : Measure (Matrix m n ℝ)} [IsRightUnitarilyInvariant ν]
    {X : Ω → Matrix m n ℝ} (hX : HasLaw X ν μ) (V : Matrix n p ℝ)
    {S : Matrix m p ℝ → Matrix n n ℝ} (hSm : Measurable S) (hSo : ∀ Y, HasOrthonormalCols (S Y))
    (hSV : ∀ Y, S Y * V = V) :
    IdentDistrib (fun ω => (X ω * V, X ω)) (fun ω => (X ω * V, X ω * S (X ω * V))) μ μ := by
  obtain ⟨c, _, _, R, hRm, hRo, hRV, hRS⟩ := exists_measurable_stabilizer V
  set μ' := μ.prod (haarFrame c c)
  have hXae : AEMeasurable (fun z : Ω × Matrix c c ℝ => X z.1) μ' :=
    hX.aemeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst
  have hfst : μ'.map Prod.fst = μ := by rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hXlaw : μ'.map (fun z => X z.1) = ν := by
    rw [← hX.map_eq, ← hfst, AEMeasurable.map_map_of_aemeasurable (hfst ▸ hX.aemeasurable)
      measurable_fst.aemeasurable]
    rfl
  have hOlaw : μ'.map (fun z => id z.2) = haarFrame c c := by
    rw [show (fun z : Ω × Matrix c c ℝ => id z.2) = Prod.snd from rfl, Measure.map_snd_prod,
      measure_univ, one_smul]
  have hmV : Measurable fun x : Matrix m n ℝ => x * V := measurable_id.matrix_mul measurable_const
  have hφ : Measurable fun x : Matrix m n ℝ => (x * V, x) := hmV.prodMk measurable_id
  have hψ : Measurable fun x : Matrix m n ℝ => (x * V, x * S (x * V)) :=
    hmV.prodMk (measurable_id.matrix_mul (hSm.comp hmV))
  -- (1) rotating by the random stabilizer element keeps the joint law
  have h1 : IdentDistrib (fun z : Ω × Matrix c c ℝ => (X z.1 * V, X z.1))
      (fun z => (X z.1 * V, X z.1 * R z.2)) μ' μ' := by
    refine ((indepFun_prod₀ hX.aemeasurable aemeasurable_id).symm
      |>.identDistrib_prodMk_of_forall_map_eq
      (F := fun (_ : Matrix c c ℝ) (x : Matrix m n ℝ) => (x * V, x))
      (G := fun o x => (x * V, x * R o)) measurable_snd.aemeasurable hXae
      (hφ.comp measurable_snd)
      ((hmV.comp measurable_snd).prodMk (measurable_snd.matrix_mul (hRm.comp measurable_fst)))
      fun o => ?_).comp measurable_snd
    have h : (fun x : Matrix m n ℝ => (x * V, x * R o)) = (fun x => (x * V, x)) ∘ (· * R o) :=
      funext fun x => by simp only [Function.comp_apply, Matrix.mul_assoc, hRV]
    rw [hXlaw, h, ← Measure.map_map hφ (show Measurable fun x : Matrix m n ℝ => x * R o from
      measurable_id.matrix_mul measurable_const),
      IsRightUnitarilyInvariant.map_mul_right_eq_self _ (hRo o)]
  -- (2) the stabilizer element absorbs `S`
  have h2 : IdentDistrib (fun z : Ω × Matrix c c ℝ => (X z.1 * V, X z.1 * R z.2 * S (X z.1 * V)))
      (fun z => (X z.1 * V, X z.1 * R z.2)) μ' μ' := by
    refine ((indepFun_prod₀ hX.aemeasurable aemeasurable_id).identDistrib_prodMk_of_forall_map_eq
      (F := fun (x : Matrix m n ℝ) (o : Matrix c c ℝ) => (x * V, x * R o * S (x * V)))
      (G := fun x o => (x * V, x * R o)) hXae measurable_snd.aemeasurable
      ((hmV.comp measurable_fst).prodMk
        ((measurable_fst.matrix_mul (hRm.comp measurable_snd)).matrix_mul
          (hSm.comp (hmV.comp measurable_fst))))
      ((hmV.comp measurable_fst).prodMk (measurable_fst.matrix_mul (hRm.comp measurable_snd)))
      fun x => ?_).comp measurable_snd
    have hx : Measurable fun r : Matrix n n ℝ => (x * V, x * r) :=
      measurable_const.prodMk (measurable_const.matrix_mul measurable_id)
    have h : (fun o => (x * V, x * R o * S (x * V))) =
        (fun r => (x * V, x * r)) ∘ (fun o => R o * S (x * V)) :=
      funext fun o => by simp only [Function.comp_apply, Matrix.mul_assoc]
    rw [hOlaw, h, ← Measure.map_map hx (hRm.matrix_mul measurable_const),
      hRS _ (hSo _) (hSV _), Measure.map_map hx hRm]
    rfl
  -- (3) push (1) forward by `(y, z) ↦ (y, z S(y))`
  have h3 := h1.comp (u := fun yz : Matrix m p ℝ × Matrix m n ℝ => (yz.1, yz.2 * S yz.1))
    (measurable_fst.prodMk (measurable_snd.matrix_mul (hSm.comp measurable_fst)))
  have hmain := (h1.trans (h3.trans h2).symm).map_eq
  -- back from the extended space
  refine ⟨hφ.comp_aemeasurable hX.aemeasurable, hψ.comp_aemeasurable hX.aemeasurable, ?_⟩
  change μ.map ((fun x => (x * V, x)) ∘ X) = μ.map ((fun x => (x * V, x * S (x * V))) ∘ X)
  rw [← AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable hX.aemeasurable,
    ← AEMeasurable.map_map_of_aemeasurable hψ.aemeasurable hX.aemeasurable, hX.map_eq, ← hXlaw,
    AEMeasurable.map_map_of_aemeasurable hφ.aemeasurable hXae,
    AEMeasurable.map_map_of_aemeasurable hψ.aemeasurable hXae]
  exact hmain


end NLAlib
