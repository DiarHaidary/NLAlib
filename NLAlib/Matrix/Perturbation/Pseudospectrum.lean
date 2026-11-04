/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Spectral.EigenvectorPairing
public import NLAlib.Matrix.Spectral.LeastSingularValue
public import NLAlib.Matrix.Spectral.Normal

/-!
# Closed pseudospectral characterizations

The least singular value of the shifted matrix is the attained spectral-norm distance to a
perturbation producing the requested eigenvalue. This identifies the closed perturbation and
unit-residual descriptions, and, at positive radius, the eigenvalue-or-resolvent description.
For a normal complex matrix they are precisely the closed disks around its spectrum.

The matrix, shift, and perturbation use the same `RCLike` field. The real instance therefore
covers real shifts and real perturbations, not nonreal shifts with real perturbations.
The explicit last index satisfies $k + 1 = \lvert n \rvert$, so these singular-value statements
require a positive dimension without adding a redundant `Nonempty` instance.

## Main results

* `NLAlib.exists_specNorm_le_and_mem_spectrum_add_iff`: closed perturbation equivalence.
* `NLAlib.exists_rank_le_one_and_mem_spectrum_add`: an attained minimum of rank at most one.
* `NLAlib.exists_norm_eq_one_and_norm_mulVec_le_iff`: unit approximate eigenvectors.
* `NLAlib.singularValues_le_iff_mem_spectrum_or_le_specNorm_inv`: the resolvent description.
* `IsStarNormal.exists_specNorm_le_and_mem_spectrum_add_iff`: closed spectral disks.

The mathematical scope and rank-one construction follow the `tchen-research/NLAlib` development at
`77514ce42a0e437d837797a063ac161f41022730`, consolidated here through the native matrix APIs.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Transport the distance-to-singularity lower bound to a prescribed eigenvalue. -/
private theorem singularValues_le_specNorm_of_mem_spectrum_add (A E : Matrix n n 𝕜)
    (z : 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n) (hz : z ∈ spectrum 𝕜 (A + E)) :
    singularValues (z • 1 - A) k ≤ specNorm E := by
  have hE : ¬ Function.Injective ((z • 1 - A) + -E).mulVec := by
    rw [Matrix.mulVec_injective_iff_isUnit]
    simpa only [Algebra.algebraMap_eq_smul_one, sub_eq_add_neg, neg_add, add_assoc]
      using spectrum.mem_iff.mp hz
  simpa only [specNorm_neg] using
    singularValues_last_le_specNorm_of_not_injective_add (z • 1 - A) hk hE

/-- **Attained eigenvalue backward error.** For a square matrix $\mathbf{A}$ over $\Bbbk$, a
shift $z \in \Bbbk$, and $k + 1 = \lvert n \rvert$, a perturbation $\mathbf{E}$ of rank at most
one makes $z$ an eigenvalue and has norm $\sigma_k(z\mathbf{I} - \mathbf{A})$, the least norm
among all such perturbations over the same field. This includes a zero minimum and rank zero.
[TrefethenEmbree2005, Theorem 2.1 and discussion, pp. 16–17]; the attained endpoint form of
the rank-one construction, generalized from complex matrices to an `RCLike` field.
Result: pseudospectrum-perturbation-equivalence -/
theorem exists_rank_le_one_and_mem_spectrum_add (A : Matrix n n 𝕜) (z : 𝕜)
    {k : ℕ} (hk : k + 1 = Fintype.card n) :
    ∃ E : Matrix n n 𝕜, E.rank ≤ 1 ∧ z ∈ spectrum 𝕜 (A + E) ∧
      specNorm E = singularValues (z • 1 - A) k ∧
      ∀ F : Matrix n n 𝕜, z ∈ spectrum 𝕜 (A + F) → specNorm E ≤ specNorm F := by
  obtain ⟨v, hv, hres⟩ :=
    exists_norm_eq_one_and_norm_mulVec_eq_singularValues (z • 1 - A) (k := k) (by omega)
  let u := (z • 1 - A) *ᵥ v
  let E := Matrix.vecMulVec u (star v)
  have hdot : star v ⬝ᵥ v = (1 : 𝕜) := by
    have h : inner 𝕜 (WithLp.toLp 2 v) (WithLp.toLp 2 v) = (1 : 𝕜) := by
      rw [inner_self_eq_norm_sq_to_K, hv]
      simp only [RCLike.ofReal_one, one_pow]
    simpa only [EuclideanSpace.inner_toLp_toLp, dotProduct_comm] using h
  have hv0 : v ≠ 0 := by
    intro h
    simp only [h, WithLp.toLp_zero, norm_zero, zero_ne_one] at hv
  have heig : (A + E) *ᵥ v = z • v := by
    simp only [Matrix.add_mulVec, E, Matrix.vecMulVec_mulVec, hdot, MulOpposite.op_one,
      one_smul]
    dsimp [u]
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    abel
  have hspec : z ∈ spectrum 𝕜 (A + E) := by
    rw [spectrum.mem_iff, ← Matrix.mulVec_injective_iff_isUnit]
    intro hinj
    apply hv0
    apply hinj
    simp only [Matrix.sub_mulVec, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec,
      Matrix.one_mulVec, heig, sub_self, Matrix.mulVec_zero]
  have heq : specNorm E = singularValues (z • 1 - A) k := by
    rw [specNorm_vecMulVec, EuclideanSpace.norm_toLp_star, hv, mul_one]
    exact hres
  refine ⟨E, Matrix.rank_vecMulVec_le _ _, hspec, heq, ?_⟩
  intro F hF
  rw [heq]
  exact singularValues_le_specNorm_of_mem_spectrum_add A F z hk hF

/-- **Pseudospectrum–perturbation equivalence.** For a square matrix $\mathbf{A}$ over
$\Bbbk$, a shift $z \in \Bbbk$, and $k + 1 = \lvert n \rvert$, there is a perturbation over
the same field with $\|\mathbf{E}\|_2 \le \varepsilon$ and $z$ in the spectrum of
$\mathbf{A} + \mathbf{E}$ exactly when $\sigma_k(z\mathbf{I} - \mathbf{A}) \le \varepsilon$.
This is the eigenvalue backward error characterization. The radius is any real number;
in particular the closed radius-zero endpoint is included.
[EmbreeTrefethen2001, Definition, p. 583]; generalized from complex matrices to an `RCLike`
field. [TrefethenEmbree2005, Theorem 2.1] prints the open-radius variant.
Result: pseudospectrum-perturbation-equivalence -/
theorem exists_specNorm_le_and_mem_spectrum_add_iff (A : Matrix n n 𝕜) (z : 𝕜)
    {k : ℕ} (hk : k + 1 = Fintype.card n) (ε : ℝ) :
    (∃ E : Matrix n n 𝕜, specNorm E ≤ ε ∧ z ∈ spectrum 𝕜 (A + E)) ↔
      singularValues (z • 1 - A) k ≤ ε := by
  constructor
  · rintro ⟨E, hE, hz⟩
    exact (singularValues_le_specNorm_of_mem_spectrum_add A E z hk hz).trans hE
  · intro hε
    obtain ⟨E, -, hz, hnorm, -⟩ := exists_rank_le_one_and_mem_spectrum_add A z hk
    exact ⟨E, hnorm ▸ hε, hz⟩

/-- **Unit-residual characterization of the closed pseudospectrum.** For a square matrix
$\mathbf{A}$ over $\Bbbk$, a shift $z \in \Bbbk$, and $k + 1 = \lvert n \rvert$, some unit
vector $\mathbf{v}$ satisfies $\|(z\mathbf{I} - \mathbf{A})\mathbf{v}\| \le \varepsilon$
exactly when $\sigma_k(z\mathbf{I} - \mathbf{A}) \le \varepsilon$. The radius is any real
number, including zero, and the matrix, shift, and vector use the same field.
[EmbreeTrefethen2001, Definition, p. 583]; generalized from complex matrices to an `RCLike`
field. [TrefethenEmbree2005, Theorem 2.1] prints the open-radius variant.
Result: pseudospectrum-perturbation-equivalence -/
theorem exists_norm_eq_one_and_norm_mulVec_le_iff (A : Matrix n n 𝕜) (z : 𝕜)
    {k : ℕ} (hk : k + 1 = Fintype.card n) (ε : ℝ) :
    (∃ v : n → 𝕜, ‖WithLp.toLp 2 v‖ = 1 ∧
      ‖WithLp.toLp 2 ((z • 1 - A) *ᵥ v)‖ ≤ ε) ↔
      singularValues (z • 1 - A) k ≤ ε := by
  constructor
  · rintro ⟨v, hv, hbound⟩
    have h := singularValues_last_mul_norm_le (z • 1 - A) hk v
    rw [hv, mul_one] at h
    exact h.trans hbound
  · intro hε
    obtain ⟨v, hv, he⟩ :=
      exists_norm_eq_one_and_norm_mulVec_eq_singularValues (z • 1 - A) (k := k) (by omega)
    exact ⟨v, hv, he ▸ hε⟩

/-- **Resolvent characterization of the closed pseudospectrum.** For a square matrix
$\mathbf{A}$ over $\Bbbk$, $z \in \Bbbk$, $k + 1 = \lvert n \rvert$, and
$\varepsilon > 0$, the inequality $\sigma_k(z\mathbf{I} - \mathbf{A}) \le \varepsilon$ is
equivalent to $z$ being an eigenvalue or
$$\frac{1}{\varepsilon} \le \|(z\mathbf{I} - \mathbf{A})^{-1}\|_2.$$
Eigenvalues are explicit because the total matrix inverse is zero at singular inputs.
[EmbreeTrefethen2001, Definition, p. 583]; generalized to an `RCLike` field with the same-field
spectrum. [TrefethenEmbree2005, Theorem 2.1] prints the open-radius variant.
Result: pseudospectrum-perturbation-equivalence -/
theorem singularValues_le_iff_mem_spectrum_or_le_specNorm_inv (A : Matrix n n 𝕜)
    (z : 𝕜) {k : ℕ} (hk : k + 1 = Fintype.card n) {ε : ℝ} (hε : 0 < ε) :
    singularValues (z • 1 - A) k ≤ ε ↔
      z ∈ spectrum 𝕜 A ∨ 1 / ε ≤ specNorm (z • 1 - A)⁻¹ := by
  by_cases hz : z ∈ spectrum 𝕜 A
  · have hn : ¬ Function.Injective (z • (1 : Matrix n n 𝕜) - A).mulVec := by
      rw [Matrix.mulVec_injective_iff_isUnit]
      simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.mem_iff.mp hz
    have hs : singularValues (z • 1 - A) k = 0 :=
      le_antisymm (not_lt.mp ((singularValues_last_pos_iff_injective _ hk).not.mpr hn))
        (singularValues_nonneg _ _)
    simp only [hs, hε.le, hz, true_or]
  · have hu : IsUnit (z • (1 : Matrix n n 𝕜) - A) := by
      simpa only [Algebra.algebraMap_eq_smul_one] using spectrum.notMem_iff.mp hz
    have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hu
    have hs := (singularValues_last_pos_iff_injective _ hk).mpr hinj
    rw [or_iff_right hz, ← pinv_of_isUnit hu, specNorm_pinv_of_injective hinj hk,
      ← one_div, one_div_le_one_div hε hs]

/-- **Closed spectral disks for a normal matrix.** For a normal complex square matrix
$\mathbf{A}$ and any real radius $\varepsilon$, a perturbation with
$\|\mathbf{E}\|_2 \le \varepsilon$ makes $z$ an eigenvalue exactly when some
$\mu \in \operatorname{spec}(\mathbf{A})$ satisfies $\lvert z - \mu \rvert \le \varepsilon$.
This includes zero radius and empty index types.
[TrefethenEmbree2005, Theorem 2.2]; the closed-radius variant of its normal-matrix assertion.
No converse characterization of normality is asserted.
Result: pseudospectrum-perturbation-equivalence -/
theorem _root_.IsStarNormal.exists_specNorm_le_and_mem_spectrum_add_iff
    {A : Matrix n n ℂ} (hA : IsStarNormal A) (z : ℂ) (ε : ℝ) :
    (∃ E : Matrix n n ℂ, specNorm E ≤ ε ∧ z ∈ spectrum ℂ (A + E)) ↔
      ∃ μ ∈ spectrum ℂ A, ‖z - μ‖ ≤ ε := by
  constructor
  · rintro ⟨E, hE, hz⟩
    obtain ⟨x, hx, heig⟩ := exists_mulVec_eq_smul_of_mem_spectrum hz
    have : Nonempty n := not_isEmpty_iff.mp fun h => hx (Subsingleton.elim _ _)
    obtain ⟨U, d, hU, hAeq⟩ :=
      isStarNormal_iff_exists_eq_mul_diagonal_mul_conjTranspose.mp hA
    have hAU : A * U = U * Matrix.diagonal d := by
      rw [hAeq, Matrix.mul_assoc, Matrix.mul_assoc, hU.conjTranspose_mul_self, Matrix.mul_one]
    obtain ⟨i, hi⟩ := exists_norm_sub_le_pseudoConditionNumber_mul_specNorm hU.isUnit hAU hx heig
    rw [hU.pseudoConditionNumber_eq_one, one_mul] at hi
    exact ⟨d i, mem_spectrum_of_mul_eq_mul_diagonal hU.isUnit hAU i,
      (norm_sub_rev z (d i)).le.trans (hi.trans hE)⟩
  · rintro ⟨μ, hμ, hdist⟩
    refine ⟨(z - μ) • 1, ?_, ?_⟩
    · rw [specNorm_smul]
      exact (mul_le_mul_of_nonneg_left specNorm_one_le (norm_nonneg _)).trans
        (by simpa only [mul_one] using hdist)
    · have h := (spectrum.add_mem_add_iff (a := A) (r := μ) (s := z - μ)).mpr hμ
      rw [Algebra.algebraMap_eq_smul_one, add_comm μ, sub_add_cancel, add_comm] at h
      exact h

end NLAlib
