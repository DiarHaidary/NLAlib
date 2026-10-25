/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.IdentDistrib
public import NLAlib.RandomMatrix.Gaussian.Invariance

/-!
# Two-sided orthogonal blocks of a Gaussian matrix: the theorems of stage LB-A

Statements for `NLAlib/RandomMatrix/Gaussian/Invariance.lean` whose proofs are deferred
(`docs/design/Probability-MatvecQueryModel.md`, §3.4). For fixed nested orthogonal projectors
$\mathbf{E}_2 \preceq \mathbf{E}_1$ and $\mathbf{F}_2 \preceq \mathbf{F}_1$, the block
$\mathbf{E}_2\mathbf{X}\mathbf{F}_2$ of a standard Gaussian matrix is independent of the rest of
$\mathbf{E}_1\mathbf{X}\mathbf{F}_1$ and may be replaced by the same block of an independent copy.
This is one step of the adaptive deferred-decision induction; the one-sided special case with
frames is `NLAlib.indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix`.

## Main results

* `NLAlib.identDistrib_mul_mul_of_hasLaw_gaussianMatrix`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n : Type*} [Fintype m]
  [Fintype n]

/-- **Resampling a block of a Gaussian matrix**: let $\mathbf{X}$, $\mathbf{X}'$ be independent
standard Gaussian $m \times n$ matrices, and $\mathbf{E}_1, \mathbf{E}_2$,
$\mathbf{F}_1, \mathbf{F}_2$ orthogonal projectors with $\mathbf{E}_1\mathbf{E}_2 = \mathbf{E}_2$
and $\mathbf{F}_1\mathbf{F}_2 = \mathbf{F}_2$ (that is, $\mathbf{E}_2 \preceq \mathbf{E}_1$ and
$\mathbf{F}_2 \preceq \mathbf{F}_1$). Then
$\mathbf{E}_1\mathbf{X}\mathbf{F}_1$ has the law of
$$\mathbf{E}_1\mathbf{X}\mathbf{F}_1 - \mathbf{E}_2\mathbf{X}\mathbf{F}_2 +
\mathbf{E}_2\mathbf{X}'\mathbf{F}_2\,.$$
[ZhangEtAl2026, proof of Lemma 4.1]; there one query at a time with orthonormal frames and
entries $\mathcal{N}(0, 1/d)$; here unit variance and any nested projectors.
Proof: L, about 50 lines. Write $\mathbf{D} = \mathbf{E}_1\mathbf{X}\mathbf{F}_1 -
\mathbf{E}_2\mathbf{X}\mathbf{F}_2$ and $\mathbf{B} = \mathbf{E}_2\mathbf{X}\mathbf{F}_2$, both
linear in $\mathbf{X}$. (1) $\mathbf{D}$ and $\mathbf{B}$ are independent: the pair is a linear
image of the Gaussian vector `Function.uncurry (X ω)` (`hasLaw_uncurry_of_hasLaw_gaussianMatrix`;
`HasGaussianLaw` of a continuous linear map), and every entry covariance vanishes,
$\operatorname{Cov}(\mathbf{D}_{i,j}, \mathbf{B}_{k,l}) =
(\mathbf{E}_1\mathbf{E}_2)_{i,k}(\mathbf{F}_1\mathbf{F}_2)_{j,l} -
(\mathbf{E}_2)_{i,k}(\mathbf{F}_2)_{j,l} = 0$ (the entries of $\mathbf{X}$ are independent
standard normals; projectors are Hermitian and idempotent); conclude by Mathlib's
`HasGaussianLaw.indepFun_of_covariance_eval`. (2) $\mathbf{D}(\mathbf{X})$ and
$\mathbf{B}(\mathbf{X}')$ are independent because $\mathbf{X}$ and $\mathbf{X}'$ are
(`IndepFun.comp`), and $\mathbf{B}(\mathbf{X})$, $\mathbf{B}(\mathbf{X}')$ have the same law.
(3) Two independent pairs with equal marginals have equal joint laws
(`indepFun_iff_map_prod_eq_prod_map_map`), so the sums $\mathbf{D} + \mathbf{B}$ have equal
laws (`IdentDistrib.comp` with addition). -/
theorem identDistrib_mul_mul_of_hasLaw_gaussianMatrix {X X' : Ω → Matrix m n ℝ}
    (hX : HasLaw X (gaussianMatrix m n) μ) (hX' : HasLaw X' (gaussianMatrix m n) μ)
    (hXX' : IndepFun X X' μ) {E₁ E₂ : Matrix m m ℝ} {F₁ F₂ : Matrix n n ℝ}
    (hE₁ : IsStarProjection E₁) (hE₂ : IsStarProjection E₂) (hF₁ : IsStarProjection F₁)
    (hF₂ : IsStarProjection F₂) (hE : E₁ * E₂ = E₂) (hF : F₁ * F₂ = F₂) :
    IdentDistrib (fun ω => E₁ * X ω * F₁)
      (fun ω => E₁ * X ω * F₁ - E₂ * X ω * F₂ + E₂ * X' ω * F₂) μ μ := by
  sorry

end NLAlib
