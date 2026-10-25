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

-- `hE₁` is not used: `E₁ * E₂ = E₂` suffices on the left (decision UNUSED-HE1).
set_option linter.unusedVariables false in
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
@[nolint unusedArguments]
theorem identDistrib_mul_mul_of_hasLaw_gaussianMatrix {X X' : Ω → Matrix m n ℝ}
    (hX : HasLaw X (gaussianMatrix m n) μ) (hX' : HasLaw X' (gaussianMatrix m n) μ)
    (hXX' : IndepFun X X' μ) {E₁ E₂ : Matrix m m ℝ} {F₁ F₂ : Matrix n n ℝ}
    (hE₁ : IsStarProjection E₁) (hE₂ : IsStarProjection E₂) (hF₁ : IsStarProjection F₁)
    (hF₂ : IsStarProjection F₂) (hE : E₁ * E₂ = E₂) (hF : F₁ * F₂ = F₂) :
    IdentDistrib (fun ω => E₁ * X ω * F₁)
      (fun ω => E₁ * X ω * F₁ - E₂ * X ω * F₂ + E₂ * X' ω * F₂) μ μ := by
  classical
  have := hX.isProbabilityMeasure
  set P : Matrix (m × n) (m × n) ℝ := Matrix.kronecker E₂ F₂ᵀ with hPdef
  have hPH : Pᴴ = P := by
    have hF₂T : F₂ᵀ = F₂ := by
      rw [← Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.star_eq_conjTranspose,
        hF₂.isSelfAdjoint.star_eq]
    rw [hPdef, hF₂T, Matrix.kronecker, Matrix.conjTranspose_kronecker,
      ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose, hE₂.isSelfAdjoint.star_eq,
      hF₂.isSelfAdjoint.star_eq]
  have hPP : P * P = P := by
    rw [hPdef, Matrix.kronecker, ← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul,
      hE₂.isIdempotentElem.eq, hF₂.isIdempotentElem.eq]
  have hA : HasOrthonormalCols (Matrix.fromCols (1 - P) P)ᴴ := by
    rw [hasOrthonormalCols_iff, Matrix.conjTranspose_conjTranspose,
      Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromCols_mul_fromRows,
      Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hPH]
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.one_mul, hPP]
    abel
  -- the stacked pair `(X, X')`, flattened, is a standard Gaussian vector; swapping its
  -- `E₂ ⬝ F₂` blocks is the coisometry `[1 - P, P]`, so `Y = X - E₂XF₂ + E₂X'F₂` is Gaussian
  have hz : HasLaw (fun ω => (MeasurableEquiv.sumPiEquivProdPi fun _ : (m × n) ⊕ (m × n) => ℝ).symm
      (Function.uncurry (X ω), Function.uncurry (X' ω))) (gaussianVector ((m × n) ⊕ (m × n))) μ :=
    (measurePreserving_sumPiEquivProdPi fun _ : (m × n) ⊕ (m × n) => gaussianReal 0 1).symm
      |>.fun_comp_hasLaw <| (indepFun_iff_hasLaw_prodMk_prod
        (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX)
        (hasLaw_uncurry_of_hasLaw_gaussianMatrix hX')).1 (hXX'.comp
        (MeasurableEquiv.curry m n ℝ).symm.measurable
        (MeasurableEquiv.curry m n ℝ).symm.measurable)
  have hY : HasLaw (fun ω => X ω - E₂ * X ω * F₂ + E₂ * X' ω * F₂) (gaussianMatrix m n) μ := by
    refine hasLaw_gaussianMatrix_of_hasLaw_uncurry ?_
    convert hasLaw_mulVec_of_hasLaw_gaussianVector hz hA using 2 with ω
    change _ = (1 - P).fromCols P *ᵥ Sum.elim (Function.uncurry (X ω)) (Function.uncurry (X' ω))
    rw [Matrix.fromCols_mulVec_sumElim, Matrix.sub_mulVec, Matrix.one_mulVec, hPdef,
      Matrix.kronecker, ← uncurry_mul_mul, ← uncurry_mul_mul]
    rfl
  have hF' : F₂ * F₁ = F₂ := by
    have h := congrArg star hF
    rwa [star_mul, hF₁.isSelfAdjoint.star_eq, hF₂.isSelfAdjoint.star_eq] at h
  have hfun : (fun ω => E₁ * X ω * F₁ - E₂ * X ω * F₂ + E₂ * X' ω * F₂) =
      (fun M => E₁ * M * F₁) ∘ fun ω => X ω - E₂ * X ω * F₂ + E₂ * X' ω * F₂ := by
    funext ω
    simp only [Function.comp_apply, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add,
      Matrix.mul_sub, ← Matrix.mul_assoc, hE]
    simp only [Matrix.mul_assoc, hF']
  rw [hfun]
  exact (hX.identDistrib hY).comp
    ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const).measurable

end NLAlib
