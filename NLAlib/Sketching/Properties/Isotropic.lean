/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Gram
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Probability.Law
public import NLAlib.Probability.MatrixIntegral

/-!
# Isotropic sketches

A random sketch $\mathbf{S}$ with values in $\Bbbk^{k \times n}$ is isotropic when its entries are
square integrable and $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$, equivalently
$\mathbb{E}\|\mathbf{S}\mathbf{x}\|^2 = \|\mathbf{x}\|^2$ for every $\mathbf{x}$. Isotropy is the
half of an oblivious subspace injection that is not a tail bound
(`NLAlib.IsObliviousSubspaceInjection`): with it,
$\mathbb{E}\|\mathbf{S}\mathbf{M}\|_{\mathsf{F}}^2 = \|\mathbf{M}\|_{\mathsf{F}}^2$, which is the
Markov step of the injection tails of `NLAlib.Regression.Oblivious`.

A matrix with isotropic rows, scaled by $1/\sqrt{\lvert k \rvert}$, is an isotropic sketch, with no
independence between the rows; the product of two independent isotropic sketches is isotropic.
Design: `docs/design/Sketching-S1.md` §3.1.

## Main definitions

* `NLAlib.IsIsotropicSketch S μ`: square-integrable entries and
  $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$.

## Main results

* `NLAlib.isIsotropicSketch_iff`: the vector form
  $\mathbb{E}\|\mathbf{S}\mathbf{x}\|^2 = \|\mathbf{x}\|^2$.
* `NLAlib.IsIsotropicSketch.integral_frobNorm_mul_sq`:
  $\mathbb{E}\|\mathbf{S}\mathbf{M}\|_{\mathsf{F}}^2 = \|\mathbf{M}\|_{\mathsf{F}}^2$.
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

/-- **Isotropic sketch**: the entries of $\mathbf{S}$ are square integrable and
$\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}] = \mathbf{I}$, that is
$\mathbb{E}\|\mathbf{S}\mathbf{x}\|^2 = \|\mathbf{x}\|^2$ for every $\mathbf{x}$
(`NLAlib.isIsotropicSketch_iff`).
[CamanoEpperlyMeyerTropp2025, Definition 1.2 (1.2)]; there the vector form. -/
structure IsIsotropicSketch (S : Ω → Matrix k n 𝕜) (μ : Measure Ω) : Prop where
  /-- Each entry is square integrable. -/
  memLp : ∀ i j, MemLp (fun ω => S ω i j) 2 μ
  /-- The second-moment matrix $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}]$ is the identity. -/
  integral_conjTranspose_mul_self : ∫ ω, (S ω)ᴴ * S ω ∂μ = 1

/-- The Gram matrix $\mathbf{S}^{\mathsf{H}}\mathbf{S}$ of a sketch with square-integrable entries
is integrable. -/
private theorem integrable_conjTranspose_mul_self_of_memLp
    (hS : ∀ i j, MemLp (fun ω => S ω i j) 2 μ) : Integrable (fun ω => (S ω)ᴴ * S ω) μ := by
  refine Matrix.integrable_iff.2 fun i j => ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact integrable_finsetSum _ fun c _ => (hS c i).star.integrable_mul (hS c j)

omit [DecidableEq n] in
/-- $\|\mathbf{S}\mathbf{x}\|^2$ is integrable for a sketch with square-integrable entries. -/
private theorem integrable_norm_mulVec_sq_of_memLp
    (hS : ∀ i j, MemLp (fun ω => S ω i j) 2 μ) (x : n → 𝕜) :
    Integrable (fun ω => ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2) μ := by
  simp only [EuclideanSpace.norm_sq_eq]
  refine integrable_finsetSum _ fun i _ => ?_
  have h : MemLp (fun ω => (S ω *ᵥ x) i) 2 μ := by
    simp only [Matrix.mulVec, dotProduct]
    exact memLp_finsetSum _ fun j _ => (hS i j).mul_const (x j)
  exact h.integrable_norm_pow two_ne_zero

/-- $\mathbb{E}\|\mathbf{S}\mathbf{x}\|^2$ is the quadratic form of
$\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}]$ at $\mathbf{x}$. -/
private theorem ofReal_integral_norm_mulVec_sq
    (hS : ∀ i j, MemLp (fun ω => S ω i j) 2 μ) (x : n → 𝕜) :
    ((∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ : ℝ) : 𝕜) =
      quadForm (∫ ω, (S ω)ᴴ * S ω ∂μ) x := by
  rw [← integral_ofReal, ← Matrix.integral_quadForm (integrable_conjTranspose_mul_self_of_memLp hS)]
  simp only [quadForm_conjTranspose_mul_self]

/-- Isotropy in vector form: square-integrable entries and
$\mathbb{E}\|\mathbf{S}\mathbf{x}\|^2 = \|\mathbf{x}\|^2$ for every $\mathbf{x}$. -/
theorem isIsotropicSketch_iff : IsIsotropicSketch S μ ↔ (∀ i j, MemLp (fun ω => S ω i j) 2 μ) ∧
    ∀ x : n → 𝕜, ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2 := by
  constructor
  · intro h
    refine ⟨h.memLp, fun x => ?_⟩
    have hx := ofReal_integral_norm_mulVec_sq h.memLp x
    rw [h.integral_conjTranspose_mul_self, quadForm_one] at hx
    exact_mod_cast hx
  · rintro ⟨hm, hv⟩
    refine ⟨hm, ?_⟩
    refine (Matrix.isHermitian_integral (ae_of_all _ fun ω =>
      Matrix.isHermitian_conjTranspose_mul_self (S ω))).ext_quadForm Matrix.isHermitian_one
      fun z => ?_
    rw [← ofReal_integral_norm_mulVec_sq hm z, hv z, quadForm_one]

namespace IsIsotropicSketch

/-- The squared norm $\|\mathbf{S}\mathbf{x}\|^2$ of an isotropic sketch applied to a fixed vector
is integrable. -/
theorem integrable_norm_mulVec_sq (h : IsIsotropicSketch S μ) (x : n → 𝕜) :
    Integrable (fun ω => ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2) μ :=
  integrable_norm_mulVec_sq_of_memLp h.memLp x

/-- An isotropic sketch preserves squared norms in expectation:
$\mathbb{E}\|\mathbf{S}\mathbf{x}\|^2 = \|\mathbf{x}\|^2$. -/
theorem integral_norm_mulVec_sq (h : IsIsotropicSketch S μ) (x : n → 𝕜) :
    ∫ ω, ‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 ∂μ = ‖WithLp.toLp 2 x‖ ^ 2 :=
  (isIsotropicSketch_iff.1 h).2 x

/-- The squared Frobenius norm $\|\mathbf{S}\mathbf{M}\|_{\mathsf{F}}^2$ of an isotropic sketch
times a fixed matrix is integrable. -/
theorem integrable_frobNorm_mul_sq (h : IsIsotropicSketch S μ) (M : Matrix n p 𝕜) :
    Integrable (fun ω => frobNorm (S ω * M) ^ 2) μ := by
  simp only [frobNorm_sq_eq_sum_col]
  exact integrable_finsetSum _ fun j _ => h.integrable_norm_mulVec_sq (M.col j)

/-- An isotropic sketch preserves squared Frobenius norms in expectation:
$\mathbb{E}\|\mathbf{S}\mathbf{M}\|_{\mathsf{F}}^2 = \|\mathbf{M}\|_{\mathsf{F}}^2$.
[CamanoEpperlyMeyerTropp2025, proof of Lemma 2.1]. -/
theorem integral_frobNorm_mul_sq (h : IsIsotropicSketch S μ) (M : Matrix n p 𝕜) :
    ∫ ω, frobNorm (S ω * M) ^ 2 ∂μ = frobNorm M ^ 2 := by
  simp only [frobNorm_sq_eq_sum_col]
  have hi (j : p) : Integrable (fun ω => ‖WithLp.toLp 2 ((S ω * M).col j)‖ ^ 2) μ :=
    h.integrable_norm_mulVec_sq (M.col j)
  rw [integral_finsetSum _ fun j _ => hi j]
  exact Finset.sum_congr rfl fun j _ => h.integral_norm_mulVec_sq (M.col j)

/-- An isotropic sketch preserves Gram matrices in expectation:
$\mathbb{E}[(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U}]
= \mathbf{U}^{\mathsf{H}}\mathbf{U}$. -/
theorem integral_conjTranspose_mul_mul [DecidableEq p] (h : IsIsotropicSketch S μ)
    (U : Matrix n p 𝕜) :
    ∫ ω, (S ω * U)ᴴ * (S ω * U) ∂μ = Uᴴ * U := by
  have hI := integrable_conjTranspose_mul_self_of_memLp h.memLp
  have hI' : Integrable (fun ω => Uᴴ * ((S ω)ᴴ * S ω)) μ := by
    refine Matrix.integrable_iff.2 fun i j => ?_
    simp only [Matrix.mul_apply]
    exact integrable_finsetSum _ fun c _ => (Matrix.integrable_iff.1 hI c j).const_mul _
  have e (ω : Ω) : (S ω * U)ᴴ * (S ω * U) = Uᴴ * ((S ω)ᴴ * S ω) * U := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  simp only [e]
  rw [Matrix.integral_mul_const hI', Matrix.integral_const_mul _ hI,
    h.integral_conjTranspose_mul_self, Matrix.mul_one]

end IsIsotropicSketch

/-- **Isotropic rows give an isotropic sketch**: if every row of the random matrix $\mathbf{X}$ is
an isotropic random vector, $\mathbf{X} / \sqrt{\lvert k \rvert}$ is an isotropic sketch. No
independence between the rows is assumed; `[Nonempty k]` is needed, since for empty $k$ the sketch
is $\mathbf{0}$. -/
theorem isIsotropicSketch_smul_of_isIsotropic [Nonempty k] {X : Ω → Matrix k n 𝕜}
    (hX : ∀ i, IsIsotropic (fun ω => X ω i) μ) :
    IsIsotropicSketch (fun ω => ((√(Fintype.card k : ℝ))⁻¹ : ℝ) • X ω) μ := by
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.2 Fintype.card_pos
  have hrow (x : n → 𝕜) (i : k) : MemLp (fun ω => x ⬝ᵥ X ω i) 2 μ := by
    simp only [dotProduct]
    exact memLp_finsetSum _ fun j _ => ((hX i).memLp j).const_mul (x j)
  refine isIsotropicSketch_iff.2 ⟨fun i j => ?_, fun x => ?_⟩
  · exact ((hX i).memLp j).const_smul ((√(Fintype.card k : ℝ))⁻¹ : ℝ)
  simp only [norm_inv_sqrt_card_smul_mulVec_sq]
  rw [integral_div, integral_finsetSum _ fun i _ => (hrow x i).integrable_norm_pow two_ne_zero]
  simp only [fun i => (hX i).integral_norm_dotProduct_sq x, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

omit [Fintype k] [Fintype l] [Fintype n] [Fintype p] [DecidableEq n] in
/-- The product of two independent square-integrable scalars is square integrable. -/
private theorem memLp_mul_of_indepFun {f g : Ω → 𝕜} (hfg : IndepFun f g μ) (hf : MemLp f 2 μ)
    (hg : MemLp g 2 μ) : MemLp (fun ω => f ω * g ω) 2 μ := by
  refine (memLp_two_iff_integrable_sq_norm (hf.1.mul hg.1)).2 ?_
  simp only [Pi.mul_apply, norm_mul, mul_pow]
  exact (hfg.comp (φ := fun z : 𝕜 => ‖z‖ ^ 2) (ψ := fun z : 𝕜 => ‖z‖ ^ 2) (by fun_prop)
    (by fun_prop)).integrable_mul (hf.integrable_norm_pow two_ne_zero)
    (hg.integrable_norm_pow two_ne_zero)

omit [Fintype l] [Fintype n] [Fintype p] [DecidableEq n] in
/-- The entries of $\mathbf{B}^{\mathsf{H}}\mathbf{M}\mathbf{B}$, with the middle factor kept
intact. -/
private theorem conjTranspose_mul_mul_apply_eq_sum (B : Matrix k n 𝕜) (M : Matrix k k 𝕜) (i j : n) :
    (Bᴴ * M * B) i j = ∑ b, ∑ a, M a b * (star (B a i) * B b j) := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => by ring

omit [Fintype l] [Fintype p] in
/-- The entries of $\mathbb{E}[\mathbf{S}^{\mathsf{H}}\mathbf{S}]$ for an isotropic sketch,
written as sums of entry products. -/
private theorem IsIsotropicSketch.sum_integral_star_mul (h : IsIsotropicSketch S μ) (i j : n) :
    ∑ a, ∫ ω, star (S ω a i) * S ω a j ∂μ = (1 : Matrix n n 𝕜) i j := by
  have hI := integrable_conjTranspose_mul_self_of_memLp h.memLp
  rw [← h.integral_conjTranspose_mul_self, Matrix.integral_apply (Matrix.integrable_iff.1 hI)]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hg (a : k) : Integrable (fun ω => star (S ω a i) * S ω a j) μ :=
    (h.memLp a i).star.integrable_mul (h.memLp a j)
  rw [integral_finsetSum _ fun a _ => hg a]

/-- **The product of independent isotropic sketches is isotropic**: for $\mathbf{S}_2$ and
$\mathbf{S}$ independent,
$\mathbb{E}[(\mathbf{S}_2\mathbf{S})^{\mathsf{H}}\mathbf{S}_2\mathbf{S}]
= \mathbb{E}[\mathbf{S}^{\mathsf{H}}\, \mathbb{E}[\mathbf{S}_2^{\mathsf{H}}\mathbf{S}_2]\,
\mathbf{S}] = \mathbf{I}$. -/
theorem IsIsotropicSketch.mul [DecidableEq k] {S₂ : Ω → Matrix l k 𝕜}
    (h₂ : IsIsotropicSketch S₂ μ) (h : IsIsotropicSketch S μ) (hind : IndepFun S₂ S μ) :
    IsIsotropicSketch (fun ω => S₂ ω * S ω) μ := by
  have hent (i : l) (j : n) : MemLp (fun ω => (S₂ ω * S ω) i j) 2 μ := by
    simp only [Matrix.mul_apply]
    exact memLp_finsetSum _ fun c _ => memLp_mul_of_indepFun
      (hind.comp (Matrix.measurable_apply i c) (Matrix.measurable_apply c j)) (h₂.memLp i c)
      (h.memLp c j)
  refine ⟨hent, ?_⟩
  have hT := integrable_conjTranspose_mul_self_of_memLp hent
  have hG₂ := Matrix.integrable_iff.1 (integrable_conjTranspose_mul_self_of_memLp h₂.memLp)
  ext i j
  rw [Matrix.integral_apply (Matrix.integrable_iff.1 hT)]
  have e (ω : Ω) : ((S₂ ω * S ω)ᴴ * (S₂ ω * S ω)) i j =
      ∑ b, ∑ a, ((S₂ ω)ᴴ * S₂ ω) a b * (star (S ω a i) * S ω b j) := by
    rw [← conjTranspose_mul_mul_apply_eq_sum, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hind' (a b : k) : IndepFun (fun ω => ((S₂ ω)ᴴ * S₂ ω) a b)
      (fun ω => star (S ω a i) * S ω b j) μ := hind.comp
    (Continuous.matrix_elem (continuous_id.matrix_conjTranspose.matrix_mul continuous_id) a
      b).measurable
    ((continuous_star.measurable.comp (Matrix.measurable_apply a i)).mul
      (Matrix.measurable_apply b j))
  have hg (a b : k) : Integrable (fun ω => star (S ω a i) * S ω b j) μ :=
    (h.memLp a i).star.integrable_mul (h.memLp b j)
  have hterm (a b : k) : ∫ ω, ((S₂ ω)ᴴ * S₂ ω) a b * (star (S ω a i) * S ω b j) ∂μ =
      (1 : Matrix k k 𝕜) a b * ∫ ω, star (S ω a i) * S ω b j ∂μ := by
    rw [(hind' a b).integral_fun_mul_eq_mul_integral (hG₂ a b).1 (hg a b).1,
      ← Matrix.integral_apply hG₂, h₂.integral_conjTranspose_mul_self]
  have hprod (a b : k) : Integrable
      (fun ω => ((S₂ ω)ᴴ * S₂ ω) a b * (star (S ω a i) * S ω b j)) μ :=
    (hind' a b).integrable_mul (hG₂ a b) (hg a b)
  simp only [e]
  rw [integral_finsetSum _ fun b _ => integrable_finsetSum _ fun a _ => hprod a b,
    Finset.sum_congr rfl fun b _ => integral_finsetSum _ fun a _ => hprod a b,
    ← h.sum_integral_star_mul i j]
  simp only [hterm, Matrix.one_apply, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- Isotropy of a sketch depends only on its law: a sketch with law $\nu$ is isotropic exactly
when the identity is isotropic for $\nu$. -/
theorem _root_.ProbabilityTheory.HasLaw.isIsotropicSketch_iff {ν : Measure (Matrix k n 𝕜)}
    (hS : HasLaw S ν μ) : IsIsotropicSketch S μ ↔ IsIsotropicSketch id ν := by
  have hmem (i : k) (j : n) :
      MemLp (fun ω => S ω i j) 2 μ ↔ MemLp (fun A : Matrix k n 𝕜 => A i j) 2 ν :=
    hS.memLp_comp_iff (Matrix.measurable_apply i j).aestronglyMeasurable
  have hint : ∫ ω, (S ω)ᴴ * S ω ∂μ = ∫ A, Aᴴ * A ∂ν :=
    hS.integral_comp
      (continuous_id.matrix_conjTranspose.matrix_mul continuous_id).aestronglyMeasurable
  constructor
  · intro h
    exact ⟨fun i j => (hmem i j).1 (h.memLp i j), hint.symm.trans h.integral_conjTranspose_mul_self⟩
  · intro h
    exact ⟨fun i j => (hmem i j).2 (h.memLp i j), hint.trans h.integral_conjTranspose_mul_self⟩

/-! ### Deprecated aliases -/

@[deprecated EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq (since := "2026-10-15")]
alias norm_inv_sqrt_card_smul_sq := EuclideanSpace.norm_toLp_inv_sqrt_card_smul_sq

end NLAlib
