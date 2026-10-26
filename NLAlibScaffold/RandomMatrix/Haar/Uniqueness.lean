/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.RandomMatrix.Gaussian.Rank
public import NLAlib.RandomMatrix.Haar.Uniqueness

/-!
# The polar factor of a Gaussian matrix is independent of its Gram matrix (scaffold)

Statements for `NLAlib/RandomMatrix/Haar/Uniqueness.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.2): the Gaussianization step of the
Krylov coupling. A tall standard Gaussian matrix is its polar factor, a Haar frame, times the
square root of its Gram matrix, and the two factors are independent; so replacing the polar factor
by any Haar frame independent of the Gram matrix gives a standard Gaussian matrix again. All of it
also holds inside the range of an orthogonal projector $\mathbf{E}$, where the Haar frame law is
that of the polar factor of $\mathbf{E}\mathbf{Z}$ for a Gaussian $\mathbf{Z}$: the form the
coupling applies on the unrevealed subspace.

## Main results

* `NLAlib.indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix`, and the
  compressed form `NLAlib.indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix`.
* `NLAlib.eq_map_polarFactor_mul_of_forall_map_mul_left_eq`: uniqueness of the Haar frame law in
  the range of a projector.
* `NLAlib.hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix`: Gaussianization.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k : Type*} [Fintype n]
  [Fintype k]

/-- Rotating a standard Gaussian matrix on the left by an independent random orthogonal matrix
keeps the joint law of the polar factor and the Gram matrix of the rotated matrix. -/
private theorem map_mul_polarFactor_prodMk_conjTranspose_mul_self [DecidableEq n] [DecidableEq k]
    (ρ : Measure (Matrix n n ℝ)) [SFinite ρ] {R : Matrix n n ℝ → Matrix n n ℝ}
    (hRm : Measurable R) (hRo : ∀ U, HasOrthonormalCols (R U)) :
    (ρ.prod (gaussianMatrix n k)).map (fun p => (R p.1 * polarFactor p.2, p.2ᴴ * p.2)) =
      (ρ.prod (gaussianMatrix n k)).map (fun p => (polarFactor p.2, p.2ᴴ * p.2)) := by
  have hΦ : Measurable fun x : Matrix n k ℝ => (polarFactor x, xᴴ * x) :=
    measurable_polarFactor.prodMk (by fun_prop)
  have hF1 : Measurable fun p : Matrix n n ℝ × Matrix n k ℝ => (polarFactor p.2, p.2ᴴ * p.2) :=
    hΦ.comp measurable_snd
  have hF2 : Measurable fun p : Matrix n n ℝ × Matrix n k ℝ =>
      (R p.1 * polarFactor p.2, p.2ᴴ * p.2) :=
    ((hRm.comp measurable_fst).matrix_mul (measurable_polarFactor.comp measurable_snd)).prodMk
      ((by fun_prop : Measurable fun x : Matrix n k ℝ => xᴴ * x).comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hF1 hs, Measure.map_apply hF2 hs, Measure.prod_apply (hF1 hs),
    Measure.prod_apply (hF2 hs)]
  refine lintegral_congr fun U => ?_
  have hm : Measurable (R U * · : Matrix n k ℝ → Matrix n k ℝ) :=
    measurable_const.matrix_mul measurable_id
  have heq : Prod.mk U ⁻¹' ((fun p : Matrix n n ℝ × Matrix n k ℝ =>
      (R p.1 * polarFactor p.2, p.2ᴴ * p.2)) ⁻¹' s) =
      (R U * ·) ⁻¹' ((fun x : Matrix n k ℝ => (polarFactor x, xᴴ * x)) ⁻¹' s) := by
    ext x
    simp only [Set.mem_preimage, (hRo U).polarFactor_mul_left, (hRo U).conjTranspose_mul_mul]
  rw [heq, ← Measure.map_apply hm (hΦ hs),
    IsLeftUnitarilyInvariant.map_mul_left_eq_self _ (hRo U)]
  rfl

/-- The joint law of the polar factor and the Gram matrix of a tall standard Gaussian matrix is
the product of the Haar frame law and the law of the Gram matrix. -/
private theorem map_polarFactor_prodMk_conjTranspose_mul_self [DecidableEq k]
    (hk : Fintype.card k ≤ Fintype.card n) :
    (gaussianMatrix n k).map (fun x => (polarFactor x, xᴴ * x)) =
      (haarFrame n k).prod ((gaussianMatrix n k).map fun x => xᴴ * x) := by
  classical
  set ν := gaussianMatrix n k
  set ρ := haarFrame n n
  set P := ρ.prod ν
  obtain ⟨x₀, hx₀⟩ := (ae_hasOrthonormalCols_of_hasLaw_haarFrame
    (HasLaw.id (μ := haarFrame n k)) hk).exists
  set R : Matrix n n ℝ → Matrix n n ℝ := fun U => if HasOrthonormalCols U then U else 1
  have hRm : Measurable R := Measurable.ite isClosed_setOf_hasOrthonormalCols.measurableSet
    measurable_id measurable_const
  have hRo (U : Matrix n n ℝ) : HasOrthonormalCols (R U) := by
    simp only [R]; split_ifs with h
    exacts [h, hasOrthonormalCols_one]
  set pol : Matrix n k ℝ → Matrix n k ℝ :=
    fun x => if HasOrthonormalCols (polarFactor x) then polarFactor x else x₀
  have hpolm : Measurable pol := Measurable.ite
    (measurable_polarFactor isClosed_setOf_hasOrthonormalCols.measurableSet)
    measurable_polarFactor measurable_const
  have hpolo (x : Matrix n k ℝ) : HasOrthonormalCols (pol x) := by
    simp only [pol]; split_ifs with h
    exacts [h, hx₀]
  have hgm : Measurable fun x : Matrix n k ℝ => xᴴ * x := by fun_prop
  have hPν : P.map Prod.snd = ν := by simp [P, Measure.map_snd_prod]
  have hR0 : ∀ᵐ U ∂ρ, R U = U := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame (HasLaw.id (μ := ρ)) le_rfl]
      with U hU
    exact if_pos hU
  -- (1) rotating the Gaussian by an independent Haar matrix keeps its law
  have h1 := (map_mul_polarFactor_prodMk_conjTranspose_mul_self ρ (k := k) hRm hRo).symm
  -- (2) the polar factor is a frame almost surely
  have h2 : P.map (fun p => (R p.1 * polarFactor p.2, p.2ᴴ * p.2)) =
      P.map (fun p => (R p.1 * pol p.2, p.2ᴴ * p.2)) := by
    have hν : ∀ᵐ x ∂ν, HasOrthonormalCols (polarFactor x) :=
      ae_hasOrthonormalCols_of_hasLaw_haarFrame
        (hasLaw_polarFactor_of_hasLaw_gaussianMatrix HasLaw.id) hk
    refine Measure.map_congr ?_
    filter_upwards [ae_of_ae_map measurable_snd.aemeasurable (hPν ▸ hν)] with p hp
    simp only [pol, if_pos hp]
  -- (3) a Haar matrix times any fixed frame is a Haar frame
  have hρ (y : Matrix n k ℝ) (hy : HasOrthonormalCols y) :
      ρ.map (fun U => R U * y) = haarFrame n k := by
    rw [Measure.map_congr (g := (· * y)) (hR0.mono fun U hU => by simp only [hU])]
    exact (hasLaw_mul_const_of_hasLaw_haarFrame (HasLaw.id (μ := ρ)) le_rfl hy).map_eq
  have h3 : P.map (fun p => (R p.1 * pol p.2, p.2ᴴ * p.2)) =
      (haarFrame n k).prod (ν.map fun x => xᴴ * x) := by
    have hF3 : Measurable fun p : Matrix n n ℝ × Matrix n k ℝ => (R p.1 * pol p.2, p.2ᴴ * p.2) :=
      ((hRm.comp measurable_fst).matrix_mul (hpolm.comp measurable_snd)).prodMk
        (hgm.comp measurable_snd)
    ext s hs
    rw [Measure.map_apply hF3 hs, Measure.prod_apply_symm (hF3 hs), Measure.prod_apply_symm hs,
      lintegral_map (measurable_measure_prodMk_right hs) hgm]
    refine lintegral_congr fun x => ?_
    rw [← hρ (pol x) (hpolo x),
      Measure.map_apply (hRm.matrix_mul measurable_const) (measurable_prodMk_right hs)]
    rfl
  refine Eq.trans ?_ (h1.trans (h2.trans h3))
  rw [← hPν, Measure.map_map (measurable_polarFactor.prodMk hgm) measurable_snd]
  rfl

/-- **Polar factor and Gram matrix of a Gaussian matrix are independent**: for a standard Gaussian
$\mathbf{G} \in \mathbb{R}^{n \times k}$, the polar factor
$\mathbf{G}(\mathbf{G}^{\mathsf{H}}\mathbf{G})^{-1/2}$, a Haar frame, is independent of
$\mathbf{G}^{\mathsf{H}}\mathbf{G}$ when $\lvert k \rvert \le \lvert n \rvert$. (For a wide
$\mathbf{G}$ it is not: the Gram matrix fixes the row space of the polar factor.)
[Meckes2019, Ch. 1]; locator to verify.
Proof: for a Haar $\mathbf{O} \in O(n)$ independent of $\mathbf{G}$, $\mathbf{O}\mathbf{G}$ is
standard Gaussian (`NLAlib.hasLaw_mul_mul_of_hasLaw_gaussianMatrix`, frozen in $\mathbf{O}$ by
`ProbabilityTheory.IndepFun.identDistrib_prodMk_of_forall_map_eq`), with polar factor
$\mathbf{O}\,\mathrm{polar}(\mathbf{G})$ and the same Gram matrix. So the pair
$(\mathrm{polar}(\mathbf{G}), \mathbf{G}^{\mathsf{H}}\mathbf{G})$ has the law of
$(\mathbf{O}\,\mathrm{polar}(\mathbf{G}), \mathbf{G}^{\mathsf{H}}\mathbf{G})$, and given the second
coordinate the first is left invariant on the Stiefel manifold (orthonormal columns a.s. for
$\lvert k \rvert \le \lvert n \rvert$), hence Haar
(`NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`
for the conditional law, or directly: the joint law is the product of the Haar frame law and the law
of the Gram matrix, tested on rectangles). Rank-deficient $\mathbf{G}$ has probability zero
(`NLAlib.ae_rank_eq_min_of_hasLaw_gaussianMatrix`). L, about 80 lines. -/
theorem indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix
    [DecidableEq k] {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (hk : Fintype.card k ≤ Fintype.card n) :
    IndepFun (fun ω => polarFactor (G ω)) (fun ω => (G ω)ᴴ * G ω) μ := by
  have := hG.isProbabilityMeasure
  have hgm : Measurable fun x : Matrix n k ℝ => xᴴ * x := by fun_prop
  refine (indepFun_iff_map_prod_eq_prod_map_map
    (measurable_polarFactor.comp_aemeasurable hG.aemeasurable)
    (hgm.comp_aemeasurable hG.aemeasurable)).2 ?_
  have h := map_polarFactor_prodMk_conjTranspose_mul_self (n := n) (k := k) hk
  rw [← (hasLaw_polarFactor_of_hasLaw_gaussianMatrix hG).map_eq, ← hG.map_eq,
    AEMeasurable.map_map_of_aemeasurable (measurable_polarFactor.prodMk hgm).aemeasurable
      hG.aemeasurable,
    AEMeasurable.map_map_of_aemeasurable hgm.aemeasurable hG.aemeasurable] at h
  exact h

/-- **Compressed form**: for a standard Gaussian $\mathbf{G} \in \mathbb{R}^{n \times k}$ and an
orthogonal projector $\mathbf{P}$ of rank at least $\lvert k \rvert$, the polar factor of
$\mathbf{P}\mathbf{G}$ is independent of
$(\mathbf{P}\mathbf{G})^{\mathsf{H}}\mathbf{P}\mathbf{G}$. For $\mathbf{P} = \mathbf{I}$ this is
`NLAlib.indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix`.
[Meckes2019, Ch. 1]; there for $\mathbf{P} = \mathbf{I}$.
Proof: write $\mathbf{P} = \mathbf{E}_0\mathbf{E}_0^{\mathsf{H}}$ with $\mathbf{E}_0$ a frame of
$\operatorname{rank}\mathbf{P}$ columns
(`IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq`, indexed by
$\operatorname{Fin}(\operatorname{rank}\mathbf{P})$). Then
$\mathbf{P}\mathbf{G} = \mathbf{E}_0\mathbf{Y}$ with
$\mathbf{Y} = \mathbf{E}_0^{\mathsf{H}}\mathbf{G}$ standard Gaussian
(`NLAlib.hasLaw_const_mul_of_hasLaw_gaussianMatrix`), its polar factor is
$\mathbf{E}_0\operatorname{polar}(\mathbf{Y})$ (`NLAlib.HasOrthonormalCols.polarFactor_mul_left`)
and its Gram matrix is $\mathbf{Y}^{\mathsf{H}}\mathbf{Y}$; apply the uncompressed form to
$\mathbf{Y}$ and compose (`ProbabilityTheory.IndepFun.comp`, the map
$\mathbf{A} \mapsto \mathbf{E}_0\mathbf{A}$ is measurable). M, about 30 lines. -/
theorem indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix [DecidableEq k]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) {G : Ω → Matrix n k ℝ}
    (hG : HasLaw G (gaussianMatrix n k) μ) (hk : Fintype.card k ≤ P.rank) :
    IndepFun (fun ω => polarFactor (P * G ω)) (fun ω => (P * G ω)ᴴ * (P * G ω)) μ := by
  obtain ⟨E₀, hE₀, hP₀⟩ :=
    hP.exists_hasOrthonormalCols_mul_conjTranspose_eq (p := Fin P.rank) (Fintype.card_fin _)
  have hY := hasLaw_const_mul_of_hasLaw_gaussianMatrix hG
    (U := E₀ᴴ) (by rwa [Matrix.conjTranspose_conjTranspose])
  have hk' : Fintype.card k ≤ Fintype.card (Fin P.rank) := by simpa using hk
  have h := indepFun_polarFactor_conjTranspose_mul_self_of_hasLaw_gaussianMatrix hY hk'
  have horth : E₀ᴴ * E₀ = 1 := hE₀.conjTranspose_mul_self
  have hPG : ∀ ω, P * G ω = E₀ * (E₀ᴴ * G ω) := fun ω => by
    rw [← Matrix.mul_assoc, hP₀]
  have f1 : (fun ω => polarFactor (P * G ω)) =
      (fun A => E₀ * A) ∘ (fun ω => polarFactor (E₀ᴴ * G ω)) := by
    funext ω
    simp only [Function.comp_apply, hPG]
    exact hE₀.polarFactor_mul_left _
  have f2 : (fun ω => (P * G ω)ᴴ * (P * G ω)) = id ∘ (fun ω => (E₀ᴴ * G ω)ᴴ * (E₀ᴴ * G ω)) := by
    funext ω
    simp only [Function.comp_apply, id]
    rw [hPG, Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc E₀ᴴ E₀, horth,
      Matrix.one_mul]
  rw [f1, f2]
  exact h.comp (by fun_prop) measurable_id

/-- **The Haar frame law in a subspace is unique**: let $\mathbf{E}$ be an orthogonal projector
and $\nu$ a probability law on $n \times k$ frames (orthonormal columns) inside the range of
$\mathbf{E}$, invariant under left multiplication by every orthogonal $\mathbf{s}$ that fixes the
range of $\mathbf{I} - \mathbf{E}$ pointwise. Then $\nu$ is the law of
$\operatorname{polar}(\mathbf{E}\mathbf{Z})$ for a standard Gaussian $\mathbf{Z}$: the Haar frame
law of $\operatorname{range}\mathbf{E}$. (Such frames exist only if
$\lvert k \rvert \le \operatorname{rank}\mathbf{E}$.)
[Meckes2019, Ch. 1]; there for $\mathbf{E} = \mathbf{I}$
(`NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`).
Proof: in coordinates. Write $\mathbf{E} = \mathbf{E}_0\mathbf{E}_0^{\mathsf{H}}$ with a frame
$\mathbf{E}_0 \in \mathbb{R}^{n \times d}$, $d = \operatorname{rank}\mathbf{E}$
(`IsStarProjection.exists_hasOrthonormalCols_mul_conjTranspose_eq`). The image $\nu'$ of $\nu$
under $\mathbf{x} \mapsto \mathbf{E}_0^{\mathsf{H}}\mathbf{x}$ lives on $d \times k$ frames and is
left invariant: for $\mathbf{o}$ orthogonal $d \times d$, $\mathbf{s} =
\mathbf{E}_0\mathbf{o}\mathbf{E}_0^{\mathsf{H}} + \mathbf{I} - \mathbf{E}$ is orthogonal, fixes
$\operatorname{range}(\mathbf{I} - \mathbf{E})$ and satisfies $\mathbf{E}_0^{\mathsf{H}}\mathbf{s}
= \mathbf{o}\mathbf{E}_0^{\mathsf{H}}$; so $\nu' = $ `haarFrame (Fin d) k`
(`NLAlib.hasLaw_haarFrame_of_isLeftUnitarilyInvariant`, `HasLaw.id`). Since
$\mathbf{x} = \mathbf{E}_0\mathbf{E}_0^{\mathsf{H}}\mathbf{x}$ $\nu$-a.s., $\nu$ is the image of
$\nu'$ under $\mathbf{y} \mapsto \mathbf{E}_0\mathbf{y}$ (`MeasureTheory.Measure.map_congr`,
`MeasureTheory.Measure.map_map`); the right side is the same image, as
$\operatorname{polar}(\mathbf{E}\mathbf{Z}) =
\mathbf{E}_0\operatorname{polar}(\mathbf{E}_0^{\mathsf{H}}\mathbf{Z})$
(`NLAlib.HasOrthonormalCols.polarFactor_mul_left`) and
$\mathbf{E}_0^{\mathsf{H}}\mathbf{Z}$ is standard Gaussian
(`NLAlib.hasLaw_const_mul_of_hasLaw_gaussianMatrix`,
`NLAlib.hasLaw_polarFactor_of_hasLaw_gaussianMatrix`).
M, about 60 lines. -/
theorem eq_map_polarFactor_mul_of_forall_map_mul_left_eq [DecidableEq n] [DecidableEq k]
    {E : Matrix n n ℝ} (hE : IsStarProjection E) {ν : Measure (Matrix n k ℝ)}
    [IsProbabilityMeasure ν] (hν : ∀ᵐ x ∂ν, HasOrthonormalCols x ∧ E * x = x)
    (hinv : ∀ s : Matrix n n ℝ, HasOrthonormalCols s → s * (1 - E) = 1 - E →
      ν.map (s * ·) = ν) :
    ν = (gaussianMatrix n k).map fun Z => polarFactor (E * Z) := by
  obtain ⟨d, _, _, E₀, hE₀, hEE⟩ : ∃ (d : Type) (_ : Fintype d) (_ : DecidableEq d)
      (E₀ : Matrix n d ℝ), HasOrthonormalCols E₀ ∧ E₀ * E₀ᴴ = E :=
    ⟨Fin E.rank, inferInstance, inferInstance,
      hE.exists_hasOrthonormalCols_mul_conjTranspose_eq (Fintype.card_fin _)⟩
  have hm : Measurable (fun x : Matrix n k ℝ => E₀ᴴ * x) :=
    measurable_const.matrix_mul measurable_id
  have hm' : Measurable (fun y : Matrix d k ℝ => E₀ * y) :=
    measurable_const.matrix_mul measurable_id
  have hE0 : E₀ᴴ * (1 - E) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← hEE, ← Matrix.mul_assoc, hE₀.conjTranspose_mul_self,
      Matrix.one_mul, sub_self]
  have hpt : ∀ᵐ x ∂ν, E₀ * (E₀ᴴ * x) = x := hν.mono fun x hx => by
    rw [← Matrix.mul_assoc, hEE, hx.2]
  -- the pushforward of `ν` is a.s. orthonormal
  have hν'orth : ∀ᵐ x ∂(ν.map fun x => E₀ᴴ * x), HasOrthonormalCols x := by
    refine (ae_map_iff hm.aemeasurable isClosed_setOf_hasOrthonormalCols.measurableSet).2 ?_
    filter_upwards [hν] with x hx
    rw [hasOrthonormalCols_iff]
    calc (E₀ᴴ * x)ᴴ * (E₀ᴴ * x) = xᴴ * (E₀ * E₀ᴴ) * x := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = xᴴ * x := by rw [hEE, Matrix.mul_assoc, hx.2]
      _ = 1 := hasOrthonormalCols_iff.1 hx.1
  have : IsProbabilityMeasure (ν.map fun x => E₀ᴴ * x) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  -- the pushforward is left unitarily invariant
  have : IsLeftUnitarilyInvariant (ν.map fun x => E₀ᴴ * x) := by
    refine ⟨fun U hU => ?_⟩
    have hs := hE₀.hasOrthonormalCols_one_add_mul_sub_one_mul_conjTranspose hU
    have hsE : (1 + E₀ * (U - 1) * E₀ᴴ) * (1 - E) = 1 - E := by
      rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, hE0, Matrix.mul_zero, add_zero]
    have hEs : E₀ᴴ * (1 + E₀ * (U - 1) * E₀ᴴ) = U * E₀ᴴ := by
      simp only [Matrix.mul_add, Matrix.mul_one, Matrix.mul_assoc,
        hE₀.conjTranspose_mul_cancel_left, Matrix.mul_sub, Matrix.sub_mul]
      abel
    have hpt2 : ((fun x : Matrix d k ℝ => U * x) ∘ fun x : Matrix n k ℝ => E₀ᴴ * x) =
        fun x : Matrix n k ℝ => E₀ᴴ * ((1 + E₀ * (U - 1) * E₀ᴴ) * x) := funext fun x => by
      simp only [Function.comp_apply]
      rw [← Matrix.mul_assoc U, ← hEs, Matrix.mul_assoc]
    have hsm : Measurable (fun x : Matrix n k ℝ => (1 + E₀ * (U - 1) * E₀ᴴ) * x) :=
      measurable_const.matrix_mul measurable_id
    have key : ν.map (fun x => E₀ᴴ * ((1 + E₀ * (U - 1) * E₀ᴴ) * x)) = ν.map (fun x => E₀ᴴ * x) :=
      calc ν.map (fun x => E₀ᴴ * ((1 + E₀ * (U - 1) * E₀ᴴ) * x))
          = (ν.map fun x => (1 + E₀ * (U - 1) * E₀ᴴ) * x).map fun x => E₀ᴴ * x :=
            (Measure.map_map hm hsm).symm
        _ = ν.map fun x => E₀ᴴ * x := by rw [hinv _ hs hsE]
    have hUm : Measurable (fun x : Matrix d k ℝ => U * x) :=
      measurable_const.matrix_mul measurable_id
    rw [Measure.map_map hUm hm, hpt2, key]
  -- so it is the Haar frame law
  have hν'eq : ν.map (fun x => E₀ᴴ * x) = haarFrame d k := by
    have h := (hasLaw_haarFrame_of_isLeftUnitarilyInvariant (μ := ν.map fun x => E₀ᴴ * x)
      HasLaw.id hν'orth).map_eq
    rwa [Measure.map_id] at h
  have hνrec : ν = (ν.map fun x => E₀ᴴ * x).map fun y => E₀ * y := by
    rw [Measure.map_map hm' hm]
    exact Measure.map_id.symm.trans (Measure.map_congr (hpt.mono fun x hx => hx.symm))
  -- the right-hand side
  have hgauss : (gaussianMatrix n k).map (fun Z => E₀ᴴ * Z) = gaussianMatrix d k :=
    (hasLaw_const_mul_of_hasLaw_gaussianMatrix HasLaw.id (U := E₀ᴴ)
      (by rwa [Matrix.conjTranspose_conjTranspose])).map_eq
  have hEZ : ∀ Z : Matrix n k ℝ, polarFactor (E * Z) = E₀ * polarFactor (E₀ᴴ * Z) := fun Z => by
    rw [← hEE, Matrix.mul_assoc, hE₀.polarFactor_mul_left]
  have hR : (gaussianMatrix n k).map (fun Z : Matrix n k ℝ => polarFactor (E * Z)) =
      (haarFrame d k).map fun y => E₀ * y := by
    have hm'' : Measurable (fun y : Matrix d k ℝ => E₀ * polarFactor y) :=
      measurable_const.matrix_mul measurable_polarFactor
    rw [show (fun Z : Matrix n k ℝ => polarFactor (E * Z)) =
        (fun y => E₀ * polarFactor y) ∘ fun Z => E₀ᴴ * Z from funext hEZ,
      ← Measure.map_map hm'' hm, hgauss, haarFrame, Measure.map_map hm' measurable_polarFactor]
    rfl
  calc ν = (ν.map fun x => E₀ᴴ * x).map fun y => E₀ * y := hνrec
    _ = (haarFrame d k).map fun y => E₀ * y := by rw [hν'eq]
    _ = _ := hR.symm

/-- **Gaussianization in a subspace**: let $\mathbf{E}$ be an orthogonal projector of rank at
least $\lvert k \rvert$, $\mathbf{Y}$ a standard Gaussian $n \times k$ matrix and $\mathbf{F}$ a
Haar frame of $\operatorname{range}\mathbf{E}$ (the law of
$\operatorname{polar}(\mathbf{E}\mathbf{Z})$, $\mathbf{Z}$ Gaussian) independent of
$\mathbf{Y}$. Then
$$(\mathbf{I} - \mathbf{E})\mathbf{Y} + \mathbf{F}\bigl((\mathbf{E}\mathbf{Y})^{\mathsf{H}}
\mathbf{E}\mathbf{Y}\bigr)^{1/2}$$
is a standard Gaussian matrix. Its compression to $\operatorname{range}\mathbf{E}$ has the range
of $\mathbf{F}$ whenever $\mathbf{E}\mathbf{Y}$ has full column rank: a Gaussian block whose
unrevealed part spans a prescribed random frame, the step of the Krylov coupling.
[Shamir2026, Lemma 4] and OP5 (research note), Lemma C; there one column, resp. in an
orthonormal basis of the subspace.
Proof: $(\mathbf{I} - \mathbf{E})\mathbf{Y}$ and $\mathbf{E}\mathbf{Y}$ are independent
(`NLAlib.indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix` with the frames of
`IsStarProjection.exists_hasOrthonormalCols_fromCols_mul_conjTranspose_eq`), and
$\operatorname{polar}(\mathbf{E}\mathbf{Y})$ is independent of its Gram matrix
(`NLAlib.indepFun_polarFactor_mul_of_isStarProjection_of_hasLaw_gaussianMatrix`); so the triple
$(\operatorname{polar}(\mathbf{E}\mathbf{Y}),
(\mathbf{E}\mathbf{Y})^{\mathsf{H}}\mathbf{E}\mathbf{Y},
(\mathbf{I} - \mathbf{E})\mathbf{Y})$ has the product law of its first coordinate and the pair
of the others, tested on rectangles (`ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map`).
The same holds with $\mathbf{F}$ in the first coordinate ($\mathbf{F} \perp \mathbf{Y}$, same law
as $\operatorname{polar}(\mathbf{E}\mathbf{Y})$ by `HasLaw.comp`). Hence the displayed matrix has
the law of $(\mathbf{I} - \mathbf{E})\mathbf{Y} + \operatorname{polar}(\mathbf{E}\mathbf{Y})
((\mathbf{E}\mathbf{Y})^{\mathsf{H}}\mathbf{E}\mathbf{Y})^{1/2} = (\mathbf{I} -
\mathbf{E})\mathbf{Y} + \mathbf{E}\mathbf{Y} = \mathbf{Y}$ (`NLAlib.polarFactor_mul_sqrt`).
M, about 70 lines. -/
theorem hasLaw_one_sub_mul_add_mul_sqrt_of_hasLaw_gaussianMatrix [DecidableEq n] [DecidableEq k]
    {E : Matrix n n ℝ} (hE : IsStarProjection E) (hk : Fintype.card k ≤ E.rank)
    {F Y : Ω → Matrix n k ℝ}
    (hF : HasLaw F ((gaussianMatrix n k).map fun Z => polarFactor (E * Z)) μ)
    (hY : HasLaw Y (gaussianMatrix n k) μ) (hFY : IndepFun F Y μ) :
    HasLaw (fun ω => (1 - E) * Y ω + F ω * CFC.sqrt ((E * Y ω)ᴴ * (E * Y ω)))
      (gaussianMatrix n k) μ := by
  sorry

end NLAlib
