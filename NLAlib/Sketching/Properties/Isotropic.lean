/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Law
public import NLAlib.Probability.MatrixIntegral

/-!
# Isotropic sketches

A random sketch `S : Ω → Matrix k n 𝕜` is isotropic when its entries are square integrable and
`E [Sᴴ S] = 1`, equivalently `E ‖S x‖² = ‖x‖²` for every `x`. Isotropy is the half of an oblivious
subspace injection that is not a tail bound (`NLAlib.IsObliviousSubspaceInjection`): with it,
`E ‖S M‖_F² = ‖M‖_F²`, which is the Markov step of the injection tails of
`NLAlib.Sketching.Properties.Injection`.

A matrix with isotropic rows, scaled by `(√k)⁻¹`, is an isotropic sketch, with no independence
between the rows; the product of two independent isotropic sketches is isotropic. Design:
`docs/design/Sketching-S1.md` §3.1.

## Main definitions

* `NLAlib.IsIsotropicSketch S μ`: square-integrable entries and `E [Sᴴ S] = 1`.

## Main results

* `NLAlib.isIsotropicSketch_iff`: the vector form `E ‖S x‖² = ‖x‖²`.
* `NLAlib.IsIsotropicSketch.integral_frobNorm_mul_sq`: `E ‖S M‖_F² = ‖M‖_F²`.
* `NLAlib.isIsotropicSketch_smul_of_isIsotropic`: isotropic rows, scaled.
* `NLAlib.IsIsotropicSketch.mul`: products of independent isotropic sketches.
* `ProbabilityTheory.HasLaw.isIsotropicSketch_iff`: isotropy depends only on the law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix Matrix.Norms.L2Operator

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {k l n p : Type*} [Fintype k] [Fintype l] [Fintype n] [Fintype p] [DecidableEq n]
  {S : Ω → Matrix k n 𝕜}

/-- **Isotropic sketch**: the entries of `S` are square integrable and `E [Sᴴ S] = 1`, that is
`E ‖S x‖² = ‖x‖²` for every `x` (`NLAlib.isIsotropicSketch_iff`).
[CamanoEpperlyMeyerTropp2025, Definition 1.2 (1.2)]; there the vector form. -/
structure IsIsotropicSketch (S : Ω → Matrix k n 𝕜) (μ : Measure Ω) : Prop where
  /-- Each entry is square integrable. -/
  memLp : ∀ i j, MemLp (fun ω => S ω i j) 2 μ
  /-- The second-moment matrix `E [Sᴴ S]` is the identity. -/
  integral_conjTranspose_mul_self : ∫ ω, (S ω)ᴴ * S ω ∂μ = 1

/-- Isotropy in vector form: square-integrable entries and `E ‖S x‖² = ‖x‖²` for every `x`. -/
theorem isIsotropicSketch_iff : IsIsotropicSketch S μ ↔ (∀ i j, MemLp (fun ω => S ω i j) 2 μ) ∧
    ∀ x : n → 𝕜, ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

namespace IsIsotropicSketch

/-- The squared norm `‖S x‖²` of an isotropic sketch applied to a fixed vector is integrable. -/
theorem integrable_norm_mulVec_sq (h : IsIsotropicSketch S μ) (x : n → 𝕜) :
    Integrable (fun ω => ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2) μ := by
  sorry

/-- An isotropic sketch preserves squared norms in expectation: `E ‖S x‖² = ‖x‖²`. -/
theorem integral_norm_mulVec_sq (h : IsIsotropicSketch S μ) (x : n → 𝕜) :
    ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2 := by
  sorry

/-- The squared Frobenius norm `‖S M‖_F²` of an isotropic sketch times a fixed matrix is
integrable. -/
theorem integrable_frobNorm_mul_sq (h : IsIsotropicSketch S μ) (M : Matrix n p 𝕜) :
    Integrable (fun ω => frobNorm (S ω * M) ^ 2) μ := by
  sorry

/-- An isotropic sketch preserves squared Frobenius norms in expectation:
`E ‖S M‖_F² = ‖M‖_F²`. [CamanoEpperlyMeyerTropp2025, proof of Lemma 2.1]. -/
theorem integral_frobNorm_mul_sq (h : IsIsotropicSketch S μ) (M : Matrix n p 𝕜) :
    ∫ ω, frobNorm (S ω * M) ^ 2 ∂μ = frobNorm M ^ 2 := by
  sorry

/-- An isotropic sketch preserves Gram matrices in expectation:
`E [(S U)ᴴ (S U)] = Uᴴ U`. -/
theorem integral_conjTranspose_mul_mul [DecidableEq p] (h : IsIsotropicSketch S μ)
    (U : Matrix n p 𝕜) :
    ∫ ω, (S ω * U)ᴴ * (S ω * U) ∂μ = Uᴴ * U := by
  sorry

end IsIsotropicSketch

/-- **Isotropic rows give an isotropic sketch**: if every row of `X` is an isotropic random
vector, `(√k)⁻¹ • X` is an isotropic sketch. No independence between the rows is assumed;
`[Nonempty k]` is needed, since for empty `k` the sketch is `0`. -/
theorem isIsotropicSketch_smul_of_isIsotropic [Nonempty k] {X : Ω → Matrix k n 𝕜}
    (hX : ∀ i, IsIsotropic (fun ω => X ω i) μ) :
    IsIsotropicSketch (fun ω => ((√(Fintype.card k : ℝ))⁻¹ : ℝ) • X ω) μ := by
  sorry

/-- **The product of independent isotropic sketches is isotropic**: for `S₂` and `S`
independent, `E [(S₂ S)ᴴ (S₂ S)] = E [Sᴴ E [S₂ᴴ S₂] S] = 1`. -/
theorem IsIsotropicSketch.mul [IsProbabilityMeasure μ] [DecidableEq k] {S₂ : Ω → Matrix l k 𝕜}
    (h₂ : IsIsotropicSketch S₂ μ) (h : IsIsotropicSketch S μ) (hind : IndepFun S₂ S μ) :
    IsIsotropicSketch (fun ω => S₂ ω * S ω) μ := by
  sorry

/-- Isotropy of a sketch depends only on its law: a sketch with law `ν` is isotropic exactly when
the identity is isotropic for `ν`. -/
theorem _root_.ProbabilityTheory.HasLaw.isIsotropicSketch_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : IsIsotropicSketch S μ ↔ IsIsotropicSketch id ν := by
  sorry

end NLAlib
