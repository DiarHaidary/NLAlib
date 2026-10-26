/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import NLAlib.ForMathlib.Probability.Independence.Basic
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.RandomMatrix.Haar.Basic
public import NLAlib.RandomMatrix.UnitaryInvariance

/-!
# The stabilizer form of right unitary invariance

For a right unitarily invariant law (Gaussian, Haar) of $\mathbf{X}$ and a fixed block of queries
$\mathbf{V}$, the matrix may be rotated on the right by any orthogonal matrix that fixes
$\mathbf{V}$, chosen as a function of the response $\mathbf{X}\mathbf{V}$, without changing the
joint law of response and matrix (design note `docs/design/Probability-MatvecQueryModel.md` §3.4).
The adaptive form is
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
        rw [Matrix.range_mulVecLin, show Set.range A.col = Set.range f from rfl, hspan]
        exact Submodule.subset_span ⟨j, rfl⟩
      exact congrFun (rangeProjector_mulVec_eq_self_iff.2 hv) i
    rw [← hW.conjTranspose_mul_cancel_left (Wᴴ * V), ← Matrix.mul_assoc W, hWW,
      Matrix.sub_mul, Matrix.one_mul, hPV, sub_self, Matrix.mul_zero]
  · have hTA : T * A = A := by
      ext i k
      obtain ⟨j, hj⟩ := hf k
      simpa [A, Matrix.mul_apply, ← hj] using congrFun (congrFun hT i) j
    rw [hP, ← mul_pinv, ← Matrix.mul_assoc, hTA]

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
  have hRm : Measurable R := Measurable.ite isClosed_setOf_hasOrthonormalCols.measurableSet
    (by fun_prop : Continuous fun o : Matrix c c ℝ => 1 + W * (o - 1) * Wᴴ).measurable
    measurable_const
  refine ⟨c, inferInstance, inferInstance, R, hRm, fun o => ?_, fun o => ?_, fun T hT hTV => ?_⟩
  · simp only [hR]
    split_ifs with ho
    exacts [hW.hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose ho, hasOrthonormalCols_one]
  · simp only [hR]
    split_ifs
    · rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hWV, Matrix.mul_zero, add_zero]
    · exact Matrix.one_mul V
  obtain ⟨hs, hTeq⟩ := hT.eq_one_add_mul_sub_one_mul_conjTranspose hW (hfix T hTV)
  rw [Measure.map_congr (g := R ∘ (· * (Wᴴ * T * W))),
    ← Measure.map_map hRm (measurable_id'.matrix_mul measurable_const),
    IsRightUnitarilyInvariant.map_mul_right_eq_self _ hs]
  filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame HasLaw.id le_rfl] with o ho
  replace ho : HasOrthonormalCols o := ho
  simp only [Function.comp_apply, hR]
  rw [if_pos ho, if_pos (ho.mul hs)]
  conv_lhs => rw [hTeq]
  exact one_add_mul_sub_one_mul_conjTranspose_mul hW _ _

/-- **Deferred decision for a unitarily invariant law, non-adaptive stabilizer form**: let the law
$\nu$ of $\mathbf{X} \in \mathbb{R}^{m \times n}$ be right unitarily invariant (Gaussian, Haar),
$\mathbf{V} \in \mathbb{R}^{n \times p}$ fixed, and $\mathbf{S}(\mathbf{Y})$ an orthogonal matrix
chosen measurably from the response $\mathbf{Y} = \mathbf{X}\mathbf{V}$ with
$\mathbf{S}(\mathbf{Y})\mathbf{V} = \mathbf{V}$. Then $(\mathbf{X}\mathbf{V}, \mathbf{X})$ has the
law of $(\mathbf{X}\mathbf{V}, \mathbf{X}\mathbf{S}(\mathbf{X}\mathbf{V}))$: given what the
queries revealed, $\mathbf{X}$ is invariant under the rotations that fix the queries.
[Shamir2026, Lemma 3]; there for a Haar orthogonal matrix and a fixed subspace, stated with
conditional laws. -/
theorem identDistrib_prodMk_mul_of_isRightUnitarilyInvariant [IsProbabilityMeasure μ]
    {p : Type*} {ν : Measure (Matrix m n ℝ)} [IsRightUnitarilyInvariant ν]
    {X : Ω → Matrix m n ℝ} (hX : HasLaw X ν μ) (V : Matrix n p ℝ)
    {S : Matrix m p ℝ → Matrix n n ℝ} (hSm : Measurable S) (hSo : ∀ Y, HasOrthonormalCols (S Y))
    (hSV : ∀ Y, S Y * V = V) :
    IdentDistrib (fun ω => (X ω * V, X ω)) (fun ω => (X ω * V, X ω * S (X ω * V))) μ μ := by
  obtain ⟨c, _, _, R, hRm, hRo, hRV, hRS⟩ := exists_measurable_stabilizer V
  set μ' := μ.prod (haarFrame c c)
  have hXz : HasLaw (fun z : Ω × Matrix c c ℝ => X z.1) ν μ' :=
    hX.comp measurePreserving_fst.hasLaw
  have hOlaw : μ'.map (fun z => id z.2) = haarFrame c c := measurePreserving_snd.map_eq
  have hφ : Measurable fun x : Matrix m n ℝ => (x * V, x) := by fun_prop
  have hψ : Measurable fun x : Matrix m n ℝ => (x * V, x * S (x * V)) := by fun_prop
  -- (1) rotating by the random stabilizer element keeps the joint law
  have h1 : IdentDistrib (fun z : Ω × Matrix c c ℝ => (X z.1 * V, X z.1))
      (fun z => (X z.1 * V, X z.1 * R z.2)) μ' μ' := by
    refine ((indepFun_prod₀ hX.aemeasurable aemeasurable_id).symm
      |>.identDistrib_prodMk_of_forall_map_eq
      (F := fun (_ : Matrix c c ℝ) (x : Matrix m n ℝ) => (x * V, x))
      (G := fun o x => (x * V, x * R o)) measurable_snd.aemeasurable hXz.aemeasurable
      (by fun_prop) (by fun_prop) fun o => ?_).comp measurable_snd
    have h : (fun x : Matrix m n ℝ => (x * V, x * R o)) = (fun x => (x * V, x)) ∘ (· * R o) :=
      funext fun x => by simp only [Function.comp_apply, Matrix.mul_assoc, hRV]
    rw [hXz.map_eq, h, ← Measure.map_map hφ (measurable_id'.matrix_mul measurable_const),
      IsRightUnitarilyInvariant.map_mul_right_eq_self _ (hRo o)]
  -- (2) the stabilizer element absorbs `S`
  have h2 : IdentDistrib (fun z : Ω × Matrix c c ℝ => (X z.1 * V, X z.1 * R z.2 * S (X z.1 * V)))
      (fun z => (X z.1 * V, X z.1 * R z.2)) μ' μ' := by
    refine ((indepFun_prod₀ hX.aemeasurable aemeasurable_id).identDistrib_prodMk_of_forall_map_eq
      (F := fun (x : Matrix m n ℝ) (o : Matrix c c ℝ) => (x * V, x * R o * S (x * V)))
      (G := fun x o => (x * V, x * R o)) hXz.aemeasurable measurable_snd.aemeasurable
      (by fun_prop) (by fun_prop) fun x => ?_).comp measurable_snd
    have hx : Measurable fun r : Matrix n n ℝ => (x * V, x * r) := by fun_prop
    have h : (fun o => (x * V, x * R o * S (x * V))) =
        (fun r => (x * V, x * r)) ∘ (fun o => R o * S (x * V)) :=
      funext fun o => by simp only [Function.comp_apply, Matrix.mul_assoc]
    rw [hOlaw, h, ← Measure.map_map hx (hRm.matrix_mul measurable_const),
      hRS _ (hSo _) (hSV _), Measure.map_map hx hRm]
    rfl
  -- (3) push (1) forward by `(y, z) ↦ (y, z S(y))`
  have h3 := h1.comp (u := fun yz : Matrix m p ℝ × Matrix m n ℝ => (yz.1, yz.2 * S yz.1))
    (by fun_prop)
  -- back from the extended space
  have hXX := hX.identDistrib hXz
  exact (hXX.comp hφ).trans ((h1.trans (h3.trans h2).symm).trans (hXX.comp hψ).symm)

end NLAlib
