/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
public import NLAlib.ForMathlib.MeasureTheory.SpecificCodomains.Matrix

/-!
# Conditional expectations of matrix-valued functions

The conditional expectation $\mathbb{E}[\mathbf{X} \mid \mathcal{G}]$ of a random matrix
`X : Ω → Matrix l n 𝕜` given a σ-algebra $\mathcal{G}$ (`m` in Lean) is Mathlib's `μ[X | m]`,
under the same normed structure as the integral:
`open scoped Matrix.Norms.L2Operator` (`docs/design/Mathlib-deviations.md` entry 13;
`NLAlib/ForMathlib/MeasureTheory/SpecificCodomains/Matrix.lean`). It is entrywise, commutes with
the conjugate transpose and the trace, and preserves almost sure Hermitian and positive
semidefinite values. The conjugate transpose, Hermitian and positive semidefinite statements need
no integrability, because a non-integrable function has conditional expectation $\mathbf{0}$.
Loewner monotonicity is Mathlib's `MeasureTheory.condExp_mono`, through
`Matrix.instOrderClosedTopology` (`NLAlib/ForMathlib/LinearAlgebra/Matrix/PosDef.lean`), and is
not restated. Upstream candidates for a file
`Mathlib.MeasureTheory.Function.ConditionalExpectation.Matrix`.

## Main results

* `Matrix.condExp_apply`, `Matrix.condExp_conjTranspose`, `Matrix.condExp_trace`.
* `Matrix.ae_isHermitian_condExp`, `Matrix.ae_posSemidef_condExp`.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace Matrix

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {l n : Type*} [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq n]

omit [DecidableEq l] in
/-- The conditional expectation of a random matrix is entrywise: for integrable $\mathbf{X}$,
$\mathbb{E}[\mathbf{X} \mid \mathcal{G}]_{i,j} = \mathbb{E}[\mathbf{X}_{i,j} \mid \mathcal{G}]$
almost everywhere. -/
theorem condExp_apply {X : Ω → Matrix l n 𝕜} (hX : Integrable X μ) (i : l)
    (j : n) : (fun ω => μ[X | m] ω i j) =ᵐ[μ] μ[fun ω => X ω i j | m] :=
  (Matrix.entryLinearMap ℝ 𝕜 i j).toContinuousLinearMap.comp_condExp_comm hX

/-- The conjugate transpose as a continuous real linear equivalence. -/
private noncomputable def conjTransposeCLE : Matrix l n 𝕜 ≃L[ℝ] Matrix n l 𝕜 :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := Matrix.conjTranspose
      invFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := fun r A => by
        simp only [Matrix.conjTranspose_smul, star_trivial, RingHom.id_apply]
      left_inv := Matrix.conjTranspose_conjTranspose
      right_inv := Matrix.conjTranspose_conjTranspose }

/-- The conditional expectation commutes with the conjugate transpose:
$\mathbb{E}[\mathbf{X}^{\mathsf{H}} \mid \mathcal{G}] = \mathbb{E}[\mathbf{X} \mid
\mathcal{G}]^{\mathsf{H}}$ almost everywhere. No integrability hypothesis. -/
theorem condExp_conjTranspose (X : Ω → Matrix l n 𝕜) :
    μ[fun ω => (X ω)ᴴ | m] =ᵐ[μ] fun ω => (μ[X | m] ω)ᴴ := by
  by_cases hX : Integrable X μ
  · exact ((conjTransposeCLE (l := l) (n := n) (𝕜 := 𝕜)).toContinuousLinearMap.comp_condExp_comm
      hX).symm
  · have hXH : ¬Integrable (fun ω => (X ω)ᴴ) μ := fun h => hX <|
      ((conjTransposeCLE (l := n) (n := l) (𝕜 := 𝕜)).toContinuousLinearMap.integrable_comp h).congr
        (ae_of_all _ fun ω => Matrix.conjTranspose_conjTranspose (X ω))
    rw [condExp_of_not_integrable hX, condExp_of_not_integrable hXH]
    exact Filter.Eventually.of_forall fun ω => (Matrix.conjTranspose_zero).symm

/-- The conditional expectation commutes with the trace: for integrable $\mathbf{X}$,
$\operatorname{tr} \mathbb{E}[\mathbf{X} \mid \mathcal{G}]
= \mathbb{E}[\operatorname{tr} \mathbf{X} \mid \mathcal{G}]$ almost everywhere. -/
theorem condExp_trace {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) :
    (fun ω => (μ[X | m] ω).trace) =ᵐ[μ] μ[fun ω => (X ω).trace | m] :=
  (Matrix.traceLinearMap n ℝ 𝕜).toContinuousLinearMap.comp_condExp_comm hX

/-- An almost surely Hermitian random matrix has an almost surely Hermitian conditional
expectation. No integrability hypothesis. -/
theorem ae_isHermitian_condExp {X : Ω → Matrix n n 𝕜}
    (h : ∀ᵐ ω ∂μ, (X ω).IsHermitian) : ∀ᵐ ω ∂μ, (μ[X | m] ω).IsHermitian := by
  have hc : μ[fun ω => (X ω)ᴴ | m] =ᵐ[μ] μ[X | m] := condExp_congr_ae (h.mono fun _ hω => hω.eq)
  filter_upwards [Matrix.condExp_conjTranspose (m := m) (μ := μ) X, hc] with ω h₁ h₂
  exact h₁.symm.trans h₂

/-- An almost surely positive semidefinite random matrix has an almost surely positive
semidefinite conditional expectation. No integrability hypothesis. -/
theorem ae_posSemidef_condExp {X : Ω → Matrix n n 𝕜}
    (h : ∀ᵐ ω ∂μ, (X ω).PosSemidef) : ∀ᵐ ω ∂μ, (μ[X | m] ω).PosSemidef := by
  filter_upwards [condExp_nonneg (m := m) (h.mono fun _ hω => hω.nonneg)] with ω hω
  exact Matrix.nonneg_iff_posSemidef.mp hω

end Matrix
