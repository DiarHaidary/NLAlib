/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.MeasureTheory.Function.ConditionalExpectation.Matrix
public import NLAlib.Matrix.Basic.Dilation
public import NLAlib.Probability.Measurability.Matrix
public import NLAlib.Probability.MatrixIntegral

/-!
# Conditional expectations of matrix-valued functions: definiteness, calculus, dilation

The conditional expectation $\mathbb{E}[\mathbf{X} \mid \mathcal{G}]$ of a random matrix
`X : Ω → Matrix l n 𝕜` given a σ-algebra $\mathcal{G}$ (`m` in Lean) is Mathlib's `μ[X | m]`,
under the same normed structure as the integral:
`open scoped Matrix.Norms.L2Operator` (`docs/design/Mathlib-deviations.md` entry 13). The
norm-free bridges in Mathlib's vocabulary (entrywise, the conjugate transpose, the trace, almost
sure Hermitian and positive semidefinite values) are in
`NLAlib/ForMathlib/MeasureTheory/Function/ConditionalExpectation/Matrix.lean`. This file adds the
ones whose proofs or statements use NLAlib's objects: the conditional expectation preserves almost
sure positive definite values (through the eigenvalues), and commutes with the functional calculus
of a fixed Hermitian matrix and with the Hermitian dilation.

The conditional sibling of `NLAlib/Probability/MatrixIntegral.lean`
(`docs/design/Probability-P5d.md` §3.1).

## Main results

* `NLAlib.ae_posDef_condExp`.
* `Matrix.IsHermitian.condExp_cfc`: the functional calculus of a fixed Hermitian matrix commutes
  with the conditional expectation.
* `NLAlib.condExp_dilation`, `NLAlib.condExp_dilation_sq`: for the rectangular Freedman
  inequality.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix Matrix.Norms.L2Operator MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {Ω : Type*} {m mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
  {l n : Type*} [Fintype l] [Fintype n] [DecidableEq l] [DecidableEq n]

omit [Fintype l] [DecidableEq l] [Fintype n] [DecidableEq n] in
/-- The conditional expectation of an integrable, almost surely positive function is almost surely
positive: $f > 0$ a.s. implies $\mathbb{E}[f \mid \mathcal{G}] > 0$ a.s. -/
private theorem ae_pos_condExp (hm : m ≤ mΩ) [SigmaFinite (μ.trim hm)] {f : Ω → ℝ}
    (hf : Integrable f μ) (hpos : ∀ᵐ ω ∂μ, 0 < f ω) : ∀ᵐ ω ∂μ, 0 < μ[f | m] ω := by
  let S : Set Ω := {ω | μ[f | m] ω ≤ 0}
  have hS : MeasurableSet[m] S :=
    measurableSet_le stronglyMeasurable_condExp.measurable measurable_const
  have hle : ∫ ω in S, f ω ∂μ ≤ 0 := by
    rw [← setIntegral_condExp hm hf hS]
    exact setIntegral_nonpos (hm S hS) fun ω hω => hω
  have hnn : 0 ≤ᵐ[μ.restrict S] f := ae_restrict_of_ae (hpos.mono fun _ hω => hω.le)
  have h0 : ¬ 0 < μ (Function.support f ∩ S) := by
    rw [← setIntegral_pos_iff_support_of_nonneg_ae hnn hf.integrableOn]
    exact not_lt.mpr hle
  have hsupp : S ≤ᵐ[μ] (Function.support f ∩ S : Set Ω) := by
    filter_upwards [hpos] with ω hω hωS
    exact ⟨hω.ne', hωS⟩
  have hS0 : μ S = 0 := measure_mono_null_ae hsupp (nonpos_iff_eq_zero.mp (not_lt.mp h0))
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hS0] with ω hω
  exact not_le.mp hω

/-- An integrable, almost surely positive definite random matrix has an almost surely positive
definite conditional expectation, under a finite measure. This removes the hypothesis that
$\mathbb{E}[e^{\mathbf{X}} \mid \mathcal{G}]$ is positive definite from conditional Lieb. -/
theorem ae_posDef_condExp (hm : m ≤ mΩ) [IsFiniteMeasure μ]
    {X : Ω → Matrix n n 𝕜} (hX : Integrable X μ) (h : ∀ᵐ ω ∂μ, (X ω).PosDef) :
    ∀ᵐ ω ∂μ, (μ[X | m] ω).PosDef := by
  rcases isEmpty_or_nonempty n with hn | hn
  · by_cases hμ : μ = 0
    · simp only [hμ, MeasureTheory.ae_zero, Filter.eventually_bot]
    have : (ae μ).NeBot := ae_neBot.mpr hμ
    obtain ⟨ω₀, hω₀⟩ := h.exists
    exact Filter.Eventually.of_forall fun ω => Subsingleton.elim (X ω₀) (μ[X | m] ω) ▸ hω₀
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by
    have := Fintype.card_pos (α := n); omega⟩
  let f : Ω → ℝ := fun ω => min (eigenvalue (X ω) k) 1
  have hev : Integrable (fun ω => eigenvalue (X ω) k) μ := by
    refine Integrable.mono' hX.norm
      ((measurable_eigenvalue k).comp_aemeasurable hX.aemeasurable).aestronglyMeasurable
      (ae_of_all _ fun ω => ?_)
    rw [Real.norm_eq_abs, ← specNorm_eq_norm]
    by_cases hω : (X ω).IsHermitian
    · exact hω.abs_eigenvalue_le_specNorm k
    · rw [eigenvalue_of_not_isHermitian hω, abs_zero]
      exact specNorm_nonneg _
  have hf : Integrable f μ := hev.inf (integrable_const 1)
  have hfpos : ∀ᵐ ω ∂μ, 0 < f ω := by
    filter_upwards [h] with ω hω
    exact lt_min ((hω.isHermitian.posDef_iff_eigenvalue_pos.mp hω) k (by omega)) one_pos
  let T : ℝ →L[ℝ] Matrix n n 𝕜 := (ContinuousLinearMap.id ℝ ℝ).smulRight 1
  have hTf : Integrable (T ∘ f) μ := T.integrable_comp hf
  have hle : T ∘ f ≤ᵐ[μ] X := by
    filter_upwards [h] with ω hω
    exact (hω.isHermitian.smul_one_le_iff hk).mpr (min_le_left _ _)
  filter_upwards [condExp_mono (m := m) hTf hX hle, T.comp_condExp_comm (m := m) hf,
    ae_pos_condExp hm hf hfpos] with ω h₁ h₂ h₃
  rw [← h₂] at h₁
  exact Matrix.PosDef.posDef_of_le (Matrix.PosDef.smul Matrix.PosDef.one h₃) h₁

/-- **The functional calculus of a fixed Hermitian matrix commutes with the conditional
expectation**: for a fixed Hermitian $n \times n$ matrix $\mathbf{B}$ over $\Bbbk$, a
$\sigma$-algebra $\mathcal{G}$ on $\Omega$ and real functions $f_\omega$, if
$\omega \mapsto f_\omega(x)$ is integrable for every real $x$, then almost surely
$$\mathbb{E}[f_\omega(\mathbf{B}) \mid \mathcal{G}] = g(\mathbf{B}), \qquad
g(x) = \mathbb{E}[f_\omega(x) \mid \mathcal{G}],$$
where $f(\mathbf{B})$ is the functional calculus `cfc f B`. The conditional form of
`Matrix.IsHermitian.cfc_integral`. No continuity in $\omega$ or $x$ is needed, since the
spectrum of a matrix is finite. -/
theorem _root_.Matrix.IsHermitian.condExp_cfc {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    {f : Ω → ℝ → ℝ} (hf : ∀ x, Integrable (fun ω => f ω x) μ) :
    μ[fun ω => cfc (f ω) B | m] =ᵐ[μ] fun ω' => cfc (fun x => μ[fun ω => f ω x | m] ω') B := by
  obtain ⟨U, hU, hBU⟩ := hB.exists_eq_mul_diagonal_mul_conjTranspose
  have hr := Fintype.card_fin (Fintype.card n)
  let Lc : (Fin (Fintype.card n) → ℝ) →L[ℝ] Matrix n n 𝕜 := LinearMap.toContinuousLinearMap
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
  have hcfc : ∀ g : ℝ → ℝ, cfc g B = Lc (fun i => g (eigenvalue B i)) := fun g =>
    HasOrthonormalCols.cfc_eq_mul_diagonal_mul_conjTranspose hU hr hBU g
  let v : Ω → Fin (Fintype.card n) → ℝ := fun ω i => f ω (eigenvalue B i)
  have hv : Integrable v μ := integrable_pi_iff.2 fun i => hf _
  have hcomp : (fun ω => cfc (f ω) B) = Lc ∘ v := funext fun ω => hcfc (f ω)
  have hproj : ∀ᵐ ω' ∂μ, ∀ i, μ[v | m] ω' i = μ[fun ω => f ω (eigenvalue B i) | m] ω' :=
    ae_all_iff.mpr fun i =>
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) i).comp_condExp_comm (m := m) hv
  rw [hcomp]
  filter_upwards [(Lc.comp_condExp_comm (m := m) hv).symm, hproj] with ω' h1 h2
  rw [h1, Function.comp_apply, hcfc]
  exact congrArg Lc (funext h2)

/-- The conditional expectation of the Hermitian dilation of an integrable random matrix is the
dilation of its conditional expectation:
$\mathbb{E}[\mathcal{H}(\mathbf{S}) \mid \mathcal{G}] = \mathcal{H}(\mathbb{E}[\mathbf{S} \mid
\mathcal{G}])$ almost everywhere. The conditional form of `NLAlib.integral_dilation`. -/
theorem condExp_dilation {S : Ω → Matrix l n 𝕜} (hS : Integrable S μ) :
    μ[fun ω => dilation (S ω) | m] =ᵐ[μ] fun ω => dilation (μ[S | m] ω) :=
  (LinearMap.toContinuousLinearMap
    { toFun := dilation
      map_add' := dilation_add
      map_smul' := dilation_smul_real } : Matrix l n 𝕜 →L[ℝ] _).comp_condExp_comm hS |>.symm

/-- The conditional expectation of the square of a dilation is block diagonal, with the
conditional expectations of $\mathbf{S}\mathbf{S}^{\mathsf{H}}$ and
$\mathbf{S}^{\mathsf{H}}\mathbf{S}$ on the diagonal: for $\mathbf{S} \in L^2$, almost everywhere
$$\mathbb{E}[\mathcal{H}(\mathbf{S})^2 \mid \mathcal{G}] = \begin{bmatrix}
\mathbb{E}[\mathbf{S}\mathbf{S}^{\mathsf{H}} \mid \mathcal{G}] & \mathbf{0} \\
\mathbf{0} & \mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S} \mid \mathcal{G}] \end{bmatrix}.$$
The conditional form of the
`integral_dilation_sq` step of `NLAlib/Probability/MatrixConcentration/Bernstein.lean`. -/
theorem condExp_dilation_sq {S : Ω → Matrix l n 𝕜}
    (hS : MemLp S 2 μ) :
    μ[fun ω => dilation (S ω) ^ 2 | m] =ᵐ[μ] fun ω =>
      Matrix.fromBlocks (μ[fun ω' => S ω' * (S ω')ᴴ | m] ω) 0 0
        (μ[fun ω' => (S ω')ᴴ * S ω' | m] ω) := by
  let B : Matrix l l 𝕜 × Matrix n n 𝕜 →L[ℝ] Matrix (l ⊕ n) (l ⊕ n) 𝕜 :=
    LinearMap.toContinuousLinearMap
      { toFun := fun p => Matrix.fromBlocks p.1 0 0 p.2
        map_add' := fun p q => by
          simp only [Prod.fst_add, Prod.snd_add, Matrix.fromBlocks_add, add_zero]
        map_smul' := fun c p => by
          simp only [Prod.smul_fst, Prod.smul_snd, Matrix.fromBlocks_smul, smul_zero,
            RingHom.id_apply] }
  have h1 : Integrable (fun ω => S ω * (S ω)ᴴ) μ :=
    (hS.integrable_norm_pow two_ne_zero).mono'
      ((continuous_id.matrix_mul continuous_id.matrix_conjTranspose).comp_aestronglyMeasurable
        hS.1) (ae_of_all _ fun ω => by
          rw [← specNorm_eq_norm, ← specNorm_eq_norm, specNorm_mul_conjTranspose_self])
  have h2 : Integrable (fun ω => (S ω)ᴴ * S ω) μ :=
    (hS.integrable_norm_pow two_ne_zero).mono'
      ((continuous_id.matrix_conjTranspose.matrix_mul continuous_id).comp_aestronglyMeasurable
        hS.1) (ae_of_all _ fun ω => by
          rw [← specNorm_eq_norm, ← specNorm_eq_norm, specNorm_conjTranspose_mul_self])
  let p : Ω → Matrix l l 𝕜 × Matrix n n 𝕜 := fun ω => (S ω * (S ω)ᴴ, (S ω)ᴴ * S ω)
  have hp : Integrable p μ := h1.prodMk h2
  have hpt : (fun ω => dilation (S ω) ^ 2) = B ∘ p := funext fun ω => by
    rw [Function.comp_apply, sq, dilation_mul_dilation]
    rfl
  have hfst := (ContinuousLinearMap.fst ℝ (Matrix l l 𝕜) (Matrix n n 𝕜)).comp_condExp_comm
    (m := m) hp
  have hsnd := (ContinuousLinearMap.snd ℝ (Matrix l l 𝕜) (Matrix n n 𝕜)).comp_condExp_comm
    (m := m) hp
  rw [hpt]
  filter_upwards [(B.comp_condExp_comm (m := m) hp).symm, hfst, hsnd] with ω hB h₁ h₂
  rw [hB, Function.comp_apply]
  change Matrix.fromBlocks (μ[p | m] ω).1 0 0 (μ[p | m] ω).2 = _
  change (μ[p | m] ω).1 = _ at h₁
  change (μ[p | m] ω).2 = _ at h₂
  rw [h₁, h₂]
  rfl

end NLAlib
