/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.MeasureTheory.SpecificCodomains.Matrix
public import NLAlib.Matrix.Basic.QuadForm
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Probability.Isotropic

/-!
# Integrals of matrix-valued functions: quadratic forms and the functional calculus

The expectation $\mathbb{E}\mathbf{X}$ of a random matrix `X : Ω → Matrix m n 𝕜` is Mathlib's
Bochner integral `∫ ω, X ω ∂μ`, under the one scope NLAlib uses for it, library-wide:
`open scoped Matrix.Norms.L2Operator` (`docs/design/Mathlib-deviations.md` entry 13). The
norm-free bridges in Mathlib's vocabulary (integrability and the integral are entrywise; the
integral commutes with the conjugate transpose, reindexing, submatrices, the trace and products
with fixed matrices; Hermitian, positive semidefinite and positive definite means) are in
`NLAlib/ForMathlib/MeasureTheory/SpecificCodomains/Matrix.lean`. This file adds the ones about
NLAlib's objects: the integral commutes with quadratic forms and with the functional calculus of
a fixed Hermitian matrix, and an isotropic vector has identity second-moment matrix.

## Main results

* `NLAlib.integral_quadForm`: $\mathbb{E}[\mathbf{z}^{\mathsf{H}}\mathbf{X}\mathbf{z}]
  = \mathbf{z}^{\mathsf{H}}(\mathbb{E}\mathbf{X})\mathbf{z}$.
* `Matrix.IsHermitian.integrable_cfc`, `Matrix.IsHermitian.cfc_integral`: a random function of a
  fixed Hermitian matrix, with no continuity hypothesis.
* `NLAlib.IsIsotropic.integral_vecMulVec`: $\mathbb{E}[\mathbf{x}\mathbf{x}^{\mathsf{H}}]
  = \mathbf{I}$.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {n : Type*} [Fintype n] [DecidableEq n]

/-- The quadratic form at a fixed vector, as a real linear map of the matrix. -/
private def quadFormLinearMap (z : n → 𝕜) : Matrix n n 𝕜 →ₗ[ℝ] 𝕜 where
  toFun A := quadForm A z
  map_add' A A' := quadForm_add_left A A' z
  map_smul' r A := by
    simp only [RingHom.id_apply, RCLike.real_smul_eq_coe_smul (K := 𝕜), quadForm_smul_left,
      smul_eq_mul]

/-- The quadratic form of the mean is the mean of the quadratic form: for integrable $\mathbf{X}$,
$\mathbb{E}[\mathbf{z}^{\mathsf{H}}\mathbf{X}\mathbf{z}]
= \mathbf{z}^{\mathsf{H}}(\mathbb{E}\mathbf{X})\mathbf{z}$. -/
theorem integral_quadForm {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ)
    (z : n → 𝕜) : ∫ ω, quadForm (X ω) z ∂μ = quadForm (∫ ω, X ω ∂μ) z := by
  exact (quadFormLinearMap z).toContinuousLinearMap.integral_comp_comm hX

/-! ### Functions of a fixed Hermitian matrix -/

/-- Both halves of `Matrix.IsHermitian.integrable_cfc` and `Matrix.IsHermitian.cfc_integral`,
through a unitary diagonalisation of $\mathbf{B}$. -/
private theorem integrable_and_integral_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    Integrable (fun ω => cfc (f ω) B) μ ∧
      ∫ ω, cfc (f ω) B ∂μ = cfc (fun x => ∫ ω, f ω x ∂μ) B := by
  obtain ⟨U, hU, hBU⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  let L : (Fin (Fintype.card n) → ℝ) →ₗ[ℝ] Matrix n n 𝕜 :=
    { toFun := fun v => U * Matrix.diagonal (fun i => ((v i : ℝ) : 𝕜)) * Uᴴ
      map_add' := fun v w => by
        simp only [Pi.add_apply, RCLike.ofReal_add, ← Matrix.diagonal_add, Matrix.mul_add,
          Matrix.add_mul]
      map_smul' := fun a v => by
        have hd : (fun i => (((a • v) i : ℝ) : 𝕜)) = (a : 𝕜) • fun i => ((v i : ℝ) : 𝕜) := by
          funext i
          simp only [Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul]
        rw [RingHom.id_apply, hd, Matrix.diagonal_smul, Matrix.mul_smul, Matrix.smul_mul,
          ← RCLike.real_smul_eq_coe_smul] }
  let Lc := LinearMap.toContinuousLinearMap L
  have hcfc : ∀ g : ℝ → ℝ, cfc g B = Lc (fun i => g (eigenvalue B i)) := fun g =>
    HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU hr hBU g
  have hv : Integrable (fun ω => fun i : Fin (Fintype.card n) => f ω (eigenvalue B i)) μ :=
    integrable_pi_iff.2 fun i => hf _
  simp only [hcfc]
  refine ⟨Lc.integrable_comp hv, ?_⟩
  rw [Lc.integral_comp_comm hv]
  congr 1
  funext i
  exact eval_integral (fun i => hf _) i

/-- A random function of a fixed Hermitian matrix is integrable when its values are: for
Hermitian $\mathbf{B}$, if $\omega \mapsto f_\omega(x)$ is integrable for every $x$, so is
$\omega \mapsto f_\omega(\mathbf{B})$ (the functional calculus `cfc (f ω) B`). Unlike Mathlib's
`integrable_cfc`, no continuity in $\omega$ or $x$ is needed: the spectrum of a matrix is finite.
-/
theorem _root_.Matrix.IsHermitian.integrable_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    Integrable (fun ω => cfc (f ω) B) μ :=
  (integrable_and_integral_cfc hB hf).1

/-- The functional calculus of a fixed Hermitian matrix commutes with the integral: for
Hermitian $\mathbf{B}$, if $\omega \mapsto f_\omega(x)$ is integrable for every $x$, then
$g(\mathbf{B}) = \mathbb{E} f_\omega(\mathbf{B})$ with $g(x) = \mathbb{E} f_\omega(x)$, where
$f(\mathbf{B})$ is `cfc f B`. Unlike Mathlib's `cfc_integral`, no continuity in $\omega$ or $x$ is
needed: the spectrum of a matrix is finite. -/
theorem _root_.Matrix.IsHermitian.cfc_integral {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    cfc (fun x => ∫ ω, f ω x ∂μ) B = ∫ ω, cfc (f ω) B ∂μ :=
  (integrable_and_integral_cfc hB hf).2.symm

/-- The second-moment matrix of an isotropic vector is the identity:
$\mathbb{E}[\mathbf{x}\mathbf{x}^{\mathsf{H}}] = \mathbf{I}$. -/
theorem IsIsotropic.integral_vecMulVec {x : Ω → n → 𝕜} (hx : IsIsotropic x μ) :
    ∫ ω, Matrix.vecMulVec (x ω) (star (x ω)) ∂μ = 1 := by
  ext i j
  refine (Matrix.integral_apply (X := fun ω => Matrix.vecMulVec (x ω) (star (x ω)))
    (fun i j => hx.integrable_mul_star i j) i j).trans ?_
  exact (hx.integral_mul_star i j).trans Matrix.one_apply.symm

end NLAlib
