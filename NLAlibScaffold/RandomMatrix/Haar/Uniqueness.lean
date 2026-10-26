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
  sorry

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
  sorry

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
  sorry

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
