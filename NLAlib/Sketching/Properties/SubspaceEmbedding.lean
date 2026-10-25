/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Norms.Loewner
public import NLAlib.Matrix.Spectral.SingularValues
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.ForMathlib.LinearAlgebra.Matrix.PosDef
public import NLAlib.ForMathlib.MeasureTheory.Matrix

/-!
# Subspace embeddings and subspace injections

A sketch $\mathbf{S} \in \Bbbk^{k \times n}$ is a *subspace injection* for the column space of
$\mathbf{U} \in \Bbbk^{n \times p}$ with constant $a$ when
$a \|\mathbf{y}\|^2 \le \|\mathbf{S}\mathbf{y}\|^2$ for every
$\mathbf{y} \in \operatorname{range}\mathbf{U}$, and a *subspace embedding* with constants $a$, $b$
when moreover $\|\mathbf{S}\mathbf{y}\|^2 \le b \|\mathbf{y}\|^2$. Both are stated in Loewner form
on Gram matrices, $a\,\mathbf{U}^{\mathsf{H}}\mathbf{U} \preceq
(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U}
\preceq b\,\mathbf{U}^{\mathsf{H}}\mathbf{U}$,
so they are about $\operatorname{range}\mathbf{U}$ for $\mathbf{U}$ of any shape and rank. The
$\varepsilon$ form of the literature is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$, written so. A
one-sided upper statement is `IsSubspaceEmbedding S U 0 b` (`NLAlib.isSubspaceInjection_of_nonpos`
fills the lower half).

Degenerate cases: for empty $p$ every predicate holds; for empty $k$ or $\mathbf{S} = \mathbf{0}$
the injection holds iff $a \le 0$ or $\mathbf{U} = \mathbf{0}$, the upper half iff $0 \le b$ or
$\mathbf{U} = \mathbf{0}$; for $a \le 0$ the injection is vacuous. Design:
`docs/design/Sketching-S0.md`.

## Main definitions

* `NLAlib.IsSubspaceInjection S U a`: the lower half.
* `NLAlib.IsSubspaceEmbedding S U a b`: both halves.

## Main results

* `NLAlib.isSubspaceInjection_iff_forall_mem_range`,
  `NLAlib.isSubspaceEmbedding_iff_forall_mem_range`: the vector forms.
* `NLAlib.HasOrthonormalCols.isSubspaceEmbedding_iff_specNorm_le`: the Gram-error form.
* `NLAlib.HasOrthonormalCols.isSubspaceInjection_iff_le_singularValues_sq`: the
  $\sigma_{\min}$ form.
* `NLAlib.IsSubspaceEmbedding.pos_right_of_injective`: a positive lower constant on a nonzero
  range forces a positive upper constant.
* `NLAlib.IsSubspaceEmbedding.of_range_le`, `NLAlib.IsSubspaceEmbedding.mul_right`,
  `NLAlib.IsSubspaceEmbedding.smul`, `NLAlib.IsSubspaceEmbedding.mul`: subspaces, scaling and
  composition.
* `NLAlib.HasOrthonormalCols.isSubspaceEmbedding_mul_iff`: a factor with orthonormal columns
  moves from the sketch to the subspace.
* `NLAlib.IsSubspaceInjection.rank_mul_eq`: an injection keeps the rank of $\mathbf{U}$.
* `NLAlib.isClosed_setOf_isSubspaceEmbedding`, `NLAlib.measurableSet_setOf_isSubspaceEmbedding`.
-/

@[expose] public section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k l n p q : Type*} [Fintype k] [Fintype l] [Fintype n]
  {S : Matrix k n 𝕜} {U : Matrix n p 𝕜} {V : Matrix n q 𝕜}
  {a a' a₂ b b' b₂ ε : ℝ}

/-- **Subspace injection** for $\operatorname{range}\mathbf{U}$ with constant $a$:
$a\,\mathbf{U}^{\mathsf{H}}\mathbf{U} \preceq
(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U}$, that is
$a \|\mathbf{U}\mathbf{x}\|^2 \le \|\mathbf{S}\mathbf{U}\mathbf{x}\|^2$ for every $\mathbf{x}$
(`NLAlib.isSubspaceInjection_iff_forall_mem_range`). Vacuous for $a \le 0$.
[CamanoEpperlyMeyerTropp2025, Definition 1.2 (1.3)]; there $\alpha \in (0, 1]$ and $\mathbf{U}$
with orthonormal columns, here any real $a$ and any $\mathbf{U}$. -/
def IsSubspaceInjection (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (a : ℝ) : Prop :=
  a • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)

/-- **Subspace embedding** for $\operatorname{range}\mathbf{U}$ with lower constant $a$ and upper
constant $b$: $a \|\mathbf{y}\|^2 \le \|\mathbf{S}\mathbf{y}\|^2 \le b \|\mathbf{y}\|^2$ for
$\mathbf{y} \in \operatorname{range}\mathbf{U}$, in Loewner form on Gram matrices.
[Woodruff2014, Definition 1], there $1 \mp \varepsilon$ and squared norms;
[CamanoEpperlyMeyerTropp2025, Definition 1.1], there $\alpha$, $\beta$;
[MartinssonTropp2020, §8.1], there unsquared norms. -/
structure IsSubspaceEmbedding (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (a b : ℝ) : Prop where
  /-- The lower half: $\mathbf{S}$ is a subspace injection with constant $a$. -/
  lower : IsSubspaceInjection S U a
  /-- The upper half: $\|\mathbf{S}\mathbf{y}\|^2 \le b \|\mathbf{y}\|^2$ on
  $\operatorname{range}\mathbf{U}$. -/
  upper : (S * U)ᴴ * (S * U) ≤ b • (Uᴴ * U)

/-! ### Proof-local Loewner facts for an index type of any size -/

section Aux

open scoped ComplexOrder

/-- A Gram matrix is positive semidefinite, for any column index type. -/
private theorem posSemidef_conjTranspose_mul_self (U : Matrix n p 𝕜) : (Uᴴ * U).PosSemidef := by
  classical
  simpa only [Matrix.mul_one] using
    (Matrix.PosSemidef.one (n := n) (R := 𝕜)).conjTranspose_mul_mul_same' U

/-- Real multiples of a Gram matrix are ordered as their scalars. -/
private theorem smul_gram_le_smul_gram (U : Matrix n p 𝕜) {c d : ℝ} (h : c ≤ d) :
    c • (Uᴴ * U) ≤ d • (Uᴴ * U) := by
  rw [Matrix.le_iff, ← sub_smul]
  exact (posSemidef_conjTranspose_mul_self U).smul (sub_nonneg.mpr h)

/-- The Gram matrix of $c\mathbf{X}$ is $\lvert c \rvert^2$ times that of $\mathbf{X}$. -/
private theorem conjTranspose_smul_mul_smul (c : 𝕜) (X : Matrix k p 𝕜) :
    (c • X)ᴴ * (c • X) = (‖c‖ ^ 2) • (Xᴴ * X) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, RCLike.star_def,
    RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]

/-- A Loewner bound
$a\,\mathbf{U}^{\mathsf{H}}\mathbf{U} \preceq \mathbf{T}^{\mathsf{H}}\mathbf{T}$ in vector form. -/
private theorem smul_gram_le_iff [Fintype p] {T : Matrix l p 𝕜} {U : Matrix n p 𝕜} {a : ℝ} :
    a • (Uᴴ * U) ≤ Tᴴ * T ↔
      ∀ z, a * ‖WithLp.toLp 2 (U *ᵥ z)‖ ^ 2 ≤ ‖WithLp.toLp 2 (T *ᵥ z)‖ ^ 2 := by
  classical
  have e : a • (Uᴴ * U) = Uᴴ * (a • (1 : Matrix n n 𝕜)) * U := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [e, (Matrix.isHermitian_conjTranspose_mul_mul U
    (isHermitian_real_smul_one a)).le_iff_re_quadForm_le
    (Matrix.isHermitian_conjTranspose_mul_self T)]
  simp only [quadForm_conjTranspose_mul_mul, re_quadForm_real_smul_one,
    quadForm_conjTranspose_mul_self, RCLike.ofReal_re]

/-- A Loewner bound
$\mathbf{T}^{\mathsf{H}}\mathbf{T} \preceq b\,\mathbf{U}^{\mathsf{H}}\mathbf{U}$ in vector form. -/
private theorem gram_le_smul_gram_iff [Fintype p] {T : Matrix l p 𝕜} {U : Matrix n p 𝕜}
    {b : ℝ} : Tᴴ * T ≤ b • (Uᴴ * U) ↔
      ∀ z, ‖WithLp.toLp 2 (T *ᵥ z)‖ ^ 2 ≤ b * ‖WithLp.toLp 2 (U *ᵥ z)‖ ^ 2 := by
  classical
  have e : b • (Uᴴ * U) = Uᴴ * (b • (1 : Matrix n n 𝕜)) * U := by
    rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  rw [e, (Matrix.isHermitian_conjTranspose_mul_self T).le_iff_re_quadForm_le
    (Matrix.isHermitian_conjTranspose_mul_mul U (isHermitian_real_smul_one b))]
  simp only [quadForm_conjTranspose_mul_mul, re_quadForm_real_smul_one,
    quadForm_conjTranspose_mul_self, RCLike.ofReal_re]

omit [Fintype n] in
/-- A statement about every $\mathbf{U}\mathbf{z}$ is a statement about every vector of
$\operatorname{range}\mathbf{U}$. -/
private theorem forall_mem_range_iff [Fintype p] {U : Matrix n p 𝕜} {P : (n → 𝕜) → Prop} :
    (∀ y ∈ LinearMap.range U.mulVecLin, P y) ↔ ∀ z, P (U *ᵥ z) := by
  simp only [LinearMap.mem_range, Matrix.mulVecLin_apply, forall_exists_index,
    forall_apply_eq_imp_iff]

/-- A subspace injection for $\operatorname{range}\mathbf{U}$ is one for
$\operatorname{range}(\mathbf{U}\mathbf{C})$. -/
theorem IsSubspaceInjection.mul_right [Fintype p] (h : IsSubspaceInjection S U a)
    (C : Matrix p q 𝕜) :
    IsSubspaceInjection S (U * C) a := by
  have h' := conjTranspose_mul_mul_le_conjTranspose_mul_mul h C
  have e₁ : (U * C)ᴴ * (U * C) = Cᴴ * (Uᴴ * U) * C := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e₂ : (S * (U * C))ᴴ * (S * (U * C)) = Cᴴ * ((S * U)ᴴ * (S * U)) * C := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.mul_smul, Matrix.smul_mul] at h'
  rw [IsSubspaceInjection, e₁, e₂]
  exact h'

/-- Right multiplication of the subspace basis, upper half. -/
private theorem upper_mul_right [Fintype p]
    (h : (S * U)ᴴ * (S * U) ≤ b • (Uᴴ * U)) (C : Matrix p q 𝕜) :
    (S * (U * C))ᴴ * (S * (U * C)) ≤ b • ((U * C)ᴴ * (U * C)) := by
  have h' := conjTranspose_mul_mul_le_conjTranspose_mul_mul h C
  have e₁ : (U * C)ᴴ * (U * C) = Cᴴ * (Uᴴ * U) * C := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have e₂ : (S * (U * C))ᴴ * (S * (U * C)) = Cᴴ * ((S * U)ᴴ * (S * U)) * C := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [Matrix.mul_smul, Matrix.smul_mul] at h'
  rw [e₁, e₂]
  exact h'

end Aux

/-! ### Vector, Gram-error and singular-value forms -/

/-- A subspace injection in vector form: $a \|\mathbf{y}\|^2 \le \|\mathbf{S}\mathbf{y}\|^2$ for
every $\mathbf{y}$ in the column space of $\mathbf{U}$. -/
theorem isSubspaceInjection_iff_forall_mem_range [Fintype p] :
    IsSubspaceInjection S U a ↔
    ∀ y ∈ LinearMap.range U.mulVecLin,
      a * ‖WithLp.toLp 2 y‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 := by
  rw [IsSubspaceInjection, smul_gram_le_iff, forall_mem_range_iff]
  simp only [Matrix.mulVec_mulVec]

/-- A subspace embedding in vector form:
$a \|\mathbf{y}\|^2 \le \|\mathbf{S}\mathbf{y}\|^2 \le b \|\mathbf{y}\|^2$ for every $\mathbf{y}$
in the column space of $\mathbf{U}$. -/
theorem isSubspaceEmbedding_iff_forall_mem_range [Fintype p] :
    IsSubspaceEmbedding S U a b ↔
    ∀ y ∈ LinearMap.range U.mulVecLin,
      a * ‖WithLp.toLp 2 y‖ ^ 2 ≤ ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 ∧
        ‖WithLp.toLp 2 (S *ᵥ y)‖ ^ 2 ≤ b * ‖WithLp.toLp 2 y‖ ^ 2 := by
  rw [forall_mem_range_iff]
  simp only [Matrix.mulVec_mulVec]
  refine ⟨fun h z => ⟨smul_gram_le_iff.mp h.lower z, gram_le_smul_gram_iff.mp h.upper z⟩,
    fun h => ⟨smul_gram_le_iff.mpr fun z => (h z).1, gram_le_smul_gram_iff.mpr fun z => (h z).2⟩⟩

/-- For $\mathbf{U}$ with orthonormal columns the injection is the Loewner bound
$a\mathbf{I} \preceq (\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U}$. -/
theorem HasOrthonormalCols.isSubspaceInjection_iff [DecidableEq p] (hU : HasOrthonormalCols U) :
    IsSubspaceInjection S U a ↔ a • (1 : Matrix p p 𝕜) ≤ (S * U)ᴴ * (S * U) := by
  rw [IsSubspaceInjection, hU.conjTranspose_mul_self]

/-- For $\mathbf{U}$ with orthonormal columns and $0 \le \varepsilon$, the
$\varepsilon$-embedding is the Gram-error bound
$\|(\mathbf{S}\mathbf{U})^{\mathsf{H}}\mathbf{S}\mathbf{U} - \mathbf{I}\|_2 \le \varepsilon$.
The hypothesis $0 \le \varepsilon$ is needed only for empty $p$, where the left side always holds
and the right side says $0 \le \varepsilon$. -/
theorem HasOrthonormalCols.isSubspaceEmbedding_iff_specNorm_le [Fintype p] [DecidableEq p]
    (hU : HasOrthonormalCols U) (hε : 0 ≤ ε) :
    IsSubspaceEmbedding S U (1 - ε) (1 + ε) ↔ specNorm ((S * U)ᴴ * (S * U) - 1) ≤ ε := by
  have hH : ((S * U)ᴴ * (S * U) - 1).IsHermitian :=
    (Matrix.isHermitian_conjTranspose_mul_self _).sub Matrix.isHermitian_one
  constructor
  · rintro ⟨h₁, h₂⟩
    rw [IsSubspaceInjection, hU.conjTranspose_mul_self, sub_smul, one_smul] at h₁
    rw [hU.conjTranspose_mul_self, add_smul, one_smul] at h₂
    refine hH.specNorm_le_of_le_smul_one hε ?_ ?_
    · rwa [le_sub_iff_add_le, neg_add_eq_sub]
    · rwa [sub_le_iff_le_add, add_comm]
  · intro h
    refine ⟨?_, ?_⟩
    · rw [hU.isSubspaceInjection_iff]
      exact one_sub_smul_one_le_conjTranspose_mul_self_of_specNorm_le h
    · rw [hU.conjTranspose_mul_self]
      exact conjTranspose_mul_self_le_one_add_smul_one_of_specNorm_le h

/-- For $\mathbf{U}$ with orthonormal columns the injection is
$a \le \sigma_{\min}(\mathbf{S}\mathbf{U})^2$, the smallest singular value being index $j$ with
$j + 1 = \lvert p \rvert$. The upper half is `NLAlib.specNorm_sq_le_iff_conjTranspose_mul_self_le`
after `hU`. -/
theorem HasOrthonormalCols.isSubspaceInjection_iff_le_singularValues_sq [Fintype p] [DecidableEq p]
    (hU : HasOrthonormalCols U) {j : ℕ} (hj : j + 1 = Fintype.card p) :
    IsSubspaceInjection S U a ↔ a ≤ singularValues (S * U) j ^ 2 := by
  rw [hU.isSubspaceInjection_iff]
  exact ⟨le_singularValues_last_sq_of_smul_one_le hj, fun h =>
    (smul_one_le_smul_one h).trans (singularValues_last_sq_smul_one_le _ hj)⟩

/-- An approximate-matrix-multiplication bound at $\mathbf{A} = \mathbf{B} = \mathbf{U}$,
$\|\mathbf{U}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{U} -
\mathbf{U}^{\mathsf{H}}\mathbf{U}\|_{\mathsf{F}} \le \varepsilon$ for $\mathbf{U}$ with
orthonormal columns, gives the $\varepsilon$-embedding, since the spectral norm is at most the
Frobenius norm (`docs/PORT_SKETCHING.md` D7). -/
theorem HasOrthonormalCols.isSubspaceEmbedding_of_frobNorm_le [Fintype p] [DecidableEq p]
    (hU : HasOrthonormalCols U) (h : frobNorm (Uᴴ * Sᴴ * S * U - Uᴴ * U) ≤ ε) :
    IsSubspaceEmbedding S U (1 - ε) (1 + ε) := by
  have e : Uᴴ * Sᴴ * S * U - Uᴴ * U = (S * U)ᴴ * (S * U) - 1 := by
    rw [hU.conjTranspose_mul_self, Matrix.conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_assoc]
  rw [e] at h
  exact (hU.isSubspaceEmbedding_iff_specNorm_le ((frobNorm_nonneg _).trans h)).mpr
    ((specNorm_le_frobNorm _).trans h)

/-! ### Monotonicity, subspaces, scaling and composition -/

/-- A subspace injection with constant $a$ is one with any smaller constant. -/
theorem IsSubspaceInjection.mono (h : IsSubspaceInjection S U a) (ha : a' ≤ a) :
    IsSubspaceInjection S U a' := by
  exact (smul_gram_le_smul_gram U ha).trans h

/-- A subspace embedding with constants $a$, $b$ is one with any $a' \le a$ and $b \le b'$. -/
theorem IsSubspaceEmbedding.mono (h : IsSubspaceEmbedding S U a b) (ha : a' ≤ a) (hb : b ≤ b') :
    IsSubspaceEmbedding S U a' b' := by
  exact ⟨h.lower.mono ha, h.upper.trans (smul_gram_le_smul_gram U hb)⟩

/-- The upper constant of an embedding is positive: if $\mathbf{S}$ is a subspace embedding
of $\operatorname{range}\mathbf{A}$ with constants $a > 0$, $b$ (squared norms,
$a\|\mathbf{y}\|^2 \le \|\mathbf{S}\mathbf{y}\|^2 \le b\|\mathbf{y}\|^2$ on the range),
$\mathbf{A}$ has full column rank and at least one column, then $0 < b$. -/
theorem IsSubspaceEmbedding.pos_right_of_injective [Fintype q] [Nonempty q] {A : Matrix n q 𝕜}
    (h : IsSubspaceEmbedding S A a b) (ha : 0 < a) (hA : Function.Injective A.mulVec) : 0 < b := by
  classical
  obtain ⟨i⟩ := ‹Nonempty q›
  have hv : A *ᵥ Pi.single i (1 : 𝕜) ≠ 0 := by
    intro h0
    have h1 : Pi.single i (1 : 𝕜) = 0 := hA (by rw [h0, Matrix.mulVec_zero])
    simpa using congrFun h1 i
  have hpos : 0 < ‖WithLp.toLp 2 (A *ᵥ Pi.single i (1 : 𝕜))‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr (by simpa using hv)) 2
  obtain ⟨h1, h2⟩ :=
    isSubspaceEmbedding_iff_forall_mem_range.mp h _ ⟨Pi.single i (1 : 𝕜), rfl⟩
  simp only [Matrix.mulVecLin_apply] at h1 h2
  nlinarith

/-- A subspace injection for $\operatorname{range}\mathbf{U}$ is one for every subspace
$\operatorname{range}\mathbf{V} \subseteq \operatorname{range}\mathbf{U}$. -/
theorem IsSubspaceInjection.of_range_le [Fintype p] [Fintype q] (h : IsSubspaceInjection S U a)
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    IsSubspaceInjection S V a := by
  obtain ⟨C, rfl⟩ := range_le_iff_exists_mul.mp hVU
  exact h.mul_right C

/-- A subspace embedding for $\operatorname{range}\mathbf{U}$ is one for every subspace
$\operatorname{range}\mathbf{V} \subseteq \operatorname{range}\mathbf{U}$. -/
theorem IsSubspaceEmbedding.of_range_le [Fintype p] [Fintype q] (h : IsSubspaceEmbedding S U a b)
    (hVU : LinearMap.range V.mulVecLin ≤ LinearMap.range U.mulVecLin) :
    IsSubspaceEmbedding S V a b := by
  obtain ⟨C, rfl⟩ := range_le_iff_exists_mul.mp hVU
  exact ⟨h.lower.mul_right C, upper_mul_right h.upper C⟩

/-- A subspace embedding for $\operatorname{range}\mathbf{U}$ is one for
$\operatorname{range}(\mathbf{U}\mathbf{C})$. -/
theorem IsSubspaceEmbedding.mul_right [Fintype p] (h : IsSubspaceEmbedding S U a b)
    (C : Matrix p q 𝕜) :
    IsSubspaceEmbedding S (U * C) a b := by
  exact ⟨h.lower.mul_right C, upper_mul_right h.upper C⟩

/-- Scaling the sketch by $c$ scales the injection constant by $\lvert c \rvert^2$. -/
theorem IsSubspaceInjection.smul (h : IsSubspaceInjection S U a) (c : 𝕜) :
    IsSubspaceInjection (c • S) U (‖c‖ ^ 2 * a) := by
  rw [IsSubspaceInjection, Matrix.smul_mul, conjTranspose_smul_mul_smul, mul_smul]
  exact smul_le_smul_of_nonneg h (sq_nonneg _)

/-- Scaling the sketch by $c$ scales both embedding constants by $\lvert c \rvert^2$. -/
theorem IsSubspaceEmbedding.smul (h : IsSubspaceEmbedding S U a b) (c : 𝕜) :
    IsSubspaceEmbedding (c • S) U (‖c‖ ^ 2 * a) (‖c‖ ^ 2 * b) := by
  refine ⟨h.lower.smul c, ?_⟩
  rw [Matrix.smul_mul, conjTranspose_smul_mul_smul, mul_smul]
  exact smul_le_smul_of_nonneg h.upper (sq_nonneg _)

/-- Scaling the sketch by a real $c$ scales the injection constant by $c^2$: the form a
sketching family normalised by $1/\sqrt{\lvert k \rvert}$ uses. -/
theorem IsSubspaceInjection.smul_real (h : IsSubspaceInjection S U a) (c : ℝ) :
    IsSubspaceInjection (c • S) U (c ^ 2 * a) := by
  have h' := h.smul (c : 𝕜)
  rwa [RCLike.norm_ofReal, sq_abs, ← RCLike.real_smul_eq_coe_smul] at h'

/-- Scaling the sketch by a real $c$ scales both embedding constants by $c^2$. -/
theorem IsSubspaceEmbedding.smul_real (h : IsSubspaceEmbedding S U a b) (c : ℝ) :
    IsSubspaceEmbedding (c • S) U (c ^ 2 * a) (c ^ 2 * b) := by
  have h' := h.smul (c : 𝕜)
  rwa [RCLike.norm_ofReal, sq_abs, ← RCLike.real_smul_eq_coe_smul] at h'

/-- Composition of subspace injections: if $\mathbf{S}$ injects
$\operatorname{range}\mathbf{U}$ with constant $a$ and $\mathbf{S}_2$ injects
$\operatorname{range}(\mathbf{S}\mathbf{U})$ with constant $a_2 \ge 0$, then
$\mathbf{S}_2\mathbf{S}$ injects $\operatorname{range}\mathbf{U}$ with constant $a_2 a$. -/
theorem IsSubspaceInjection.mul {S₂ : Matrix l k 𝕜} (h₂ : IsSubspaceInjection S₂ (S * U) a₂)
    (h : IsSubspaceInjection S U a) (ha₂ : 0 ≤ a₂) : IsSubspaceInjection (S₂ * S) U (a₂ * a) := by
  rw [IsSubspaceInjection, mul_smul, Matrix.mul_assoc S₂ S U]
  exact (smul_le_smul_of_nonneg h ha₂).trans h₂

/-- Composition of subspace embeddings: if $\mathbf{S}$ embeds
$\operatorname{range}\mathbf{U}$ with constants $a$, $b$ and $\mathbf{S}_2$ embeds
$\operatorname{range}(\mathbf{S}\mathbf{U})$ with constants $a_2, b_2 \ge 0$, then
$\mathbf{S}_2\mathbf{S}$ embeds $\operatorname{range}\mathbf{U}$ with constants $a_2 a$, $b_2 b$. -/
theorem IsSubspaceEmbedding.mul {S₂ : Matrix l k 𝕜} (h₂ : IsSubspaceEmbedding S₂ (S * U) a₂ b₂)
    (h : IsSubspaceEmbedding S U a b) (ha₂ : 0 ≤ a₂) (hb₂ : 0 ≤ b₂) :
    IsSubspaceEmbedding (S₂ * S) U (a₂ * a) (b₂ * b) := by
  refine ⟨h₂.lower.mul h.lower ha₂, ?_⟩
  rw [mul_smul, Matrix.mul_assoc S₂ S U]
  exact h₂.upper.trans (smul_le_smul_of_nonneg h.upper hb₂)

/-- A factor with orthonormal columns moves to the subspace: for $\mathbf{B}$ with orthonormal
columns, $\mathbf{A}\mathbf{B}$ is a subspace injection for $\operatorname{range}\mathbf{U}$ with
constant $a$ exactly when $\mathbf{A}$ is one for $\operatorname{range}(\mathbf{B}\mathbf{U})$,
since $(\mathbf{B}\mathbf{U})^{\mathsf{H}}\mathbf{B}\mathbf{U} =
\mathbf{U}^{\mathsf{H}}\mathbf{U}$. It reduces a randomly rotated sketch
$\mathbf{P}\mathbf{T}$ to its second stage $\mathbf{P}$ on the rotated subspace. -/
theorem HasOrthonormalCols.isSubspaceInjection_mul_iff {m : Type*} [Fintype m] [DecidableEq n]
    {A : Matrix k m 𝕜} {B : Matrix m n 𝕜} (hB : HasOrthonormalCols B) (U : Matrix n p 𝕜) :
    IsSubspaceInjection (A * B) U a ↔ IsSubspaceInjection A (B * U) a := by
  rw [IsSubspaceInjection, IsSubspaceInjection, Matrix.mul_assoc A B U,
    hB.conjTranspose_mul_mul U U]

/-- A factor with orthonormal columns moves to the subspace, the embedding form of
`NLAlib.HasOrthonormalCols.isSubspaceInjection_mul_iff`. -/
theorem HasOrthonormalCols.isSubspaceEmbedding_mul_iff {m : Type*} [Fintype m] [DecidableEq n]
    {A : Matrix k m 𝕜} {B : Matrix m n 𝕜} (hB : HasOrthonormalCols B) (U : Matrix n p 𝕜) :
    IsSubspaceEmbedding (A * B) U a b ↔ IsSubspaceEmbedding A (B * U) a b := by
  have hU : (B * U)ᴴ * (B * U) = Uᴴ * U := hB.conjTranspose_mul_mul U U
  refine ⟨fun h => ⟨(hB.isSubspaceInjection_mul_iff U).1 h.lower, ?_⟩,
    fun h => ⟨(hB.isSubspaceInjection_mul_iff U).2 h.lower, ?_⟩⟩
  · rw [hU, ← Matrix.mul_assoc A B U]
    exact h.upper
  · rw [Matrix.mul_assoc A B U, ← hU]
    exact h.upper

/-- Every sketch is a subspace injection with a nonpositive constant. -/
theorem isSubspaceInjection_of_nonpos (S : Matrix k n 𝕜) (U : Matrix n p 𝕜) (ha : a ≤ 0) :
    IsSubspaceInjection S U a := by
  refine (smul_gram_le_smul_gram U ha).trans ?_
  rw [zero_smul]
  exact (posSemidef_conjTranspose_mul_self _).nonneg

/-! ### Injectivity -/

/-- A subspace injection with a positive constant is injective on
$\operatorname{range}\mathbf{U}$. -/
theorem IsSubspaceInjection.injOn [Fintype p] (h : IsSubspaceInjection S U a) (ha : 0 < a) :
    Set.InjOn S.mulVec (LinearMap.range U.mulVecLin) := by
  intro y₁ hy₁ y₂ hy₂ hS
  have hmem : y₁ - y₂ ∈ LinearMap.range U.mulVecLin := sub_mem hy₁ hy₂
  have key := isSubspaceInjection_iff_forall_mem_range.mp h _ hmem
  rw [Matrix.mulVec_sub, hS, sub_self, WithLp.toLp_zero, norm_zero] at key
  have h0 : ‖WithLp.toLp 2 (y₁ - y₂)‖ ^ 2 ≤ 0 := by
    nlinarith [sq_nonneg ‖WithLp.toLp 2 (y₁ - y₂)‖]
  have h1 : ‖WithLp.toLp 2 (y₁ - y₂)‖ = 0 := pow_eq_zero_iff (n := 2) two_ne_zero |>.mp
    (le_antisymm h0 (sq_nonneg _))
  rw [norm_eq_zero, ← WithLp.toLp_zero 2, WithLp.toLp_injective 2 |>.eq_iff, sub_eq_zero] at h1
  exact h1

/-- A subspace injection with a positive constant preserves full column rank:
$\mathbf{S}\mathbf{U}$ has full column rank when $\mathbf{U}$ does. -/
theorem IsSubspaceInjection.injective_mulVec [Fintype p] (h : IsSubspaceInjection S U a)
    (ha : 0 < a) (hU : Function.Injective U.mulVec) : Function.Injective (S * U).mulVec := by
  intro z₁ z₂ hz
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hz
  exact hU (h.injOn ha ⟨z₁, rfl⟩ ⟨z₂, rfl⟩ hz)

/-- A subspace injection keeps the rank: for a positive constant,
$\operatorname{rank}(\mathbf{S}\mathbf{U}) = \operatorname{rank}\mathbf{U}$. This is the rank
hypothesis of the oblique projector $\mathbf{\Pi}_{\mathbf{U},\mathbf{S}}$ (LowRank stage S0),
so every statement about that projector applies under an injection. -/
theorem IsSubspaceInjection.rank_mul_eq [Fintype p] (h : IsSubspaceInjection S U a) (ha : 0 < a) :
    (S * U).rank = U.rank := by
  have hker : LinearMap.ker (S * U).mulVecLin = LinearMap.ker U.mulVecLin := by
    ext x
    simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec]
    refine ⟨fun hx => ?_, fun hx => by rw [hx, Matrix.mulVec_zero]⟩
    exact h.injOn ha ⟨x, rfl⟩ (Submodule.zero_mem _) (by rw [Matrix.mulVec_zero]; exact hx)
  have h1 := LinearMap.finrank_range_add_finrank_ker (S * U).mulVecLin
  have h2 := LinearMap.finrank_range_add_finrank_ker U.mulVecLin
  rw [hker] at h1
  change Module.finrank 𝕜 (LinearMap.range (S * U).mulVecLin) =
    Module.finrank 𝕜 (LinearMap.range U.mulVecLin)
  omega

/-! ### Closedness and measurability of the events -/

/-- The pairs $(\mathbf{S}, \mathbf{U})$ with $\mathbf{S}$ a subspace injection for
$\operatorname{range}\mathbf{U}$ form a closed set. -/
theorem isClosed_setOf_isSubspaceInjection (a : ℝ) :
    IsClosed {x : Matrix k n 𝕜 × Matrix n p 𝕜 | IsSubspaceInjection x.1 x.2 a} := by
  refine isClosed_le ?_ ?_
  · exact (continuous_snd.matrix_conjTranspose.matrix_mul continuous_snd).const_smul a
  · exact ((continuous_fst.matrix_mul continuous_snd).matrix_conjTranspose).matrix_mul
      (continuous_fst.matrix_mul continuous_snd)

/-- The pairs $(\mathbf{S}, \mathbf{U})$ with $\mathbf{S}$ a subspace embedding for
$\operatorname{range}\mathbf{U}$ form a closed set. -/
theorem isClosed_setOf_isSubspaceEmbedding (a b : ℝ) :
    IsClosed {x : Matrix k n 𝕜 × Matrix n p 𝕜 | IsSubspaceEmbedding x.1 x.2 a b} := by
  have e : {x : Matrix k n 𝕜 × Matrix n p 𝕜 | IsSubspaceEmbedding x.1 x.2 a b} =
      {x | IsSubspaceInjection x.1 x.2 a} ∩
        {x | (x.1 * x.2)ᴴ * (x.1 * x.2) ≤ b • (x.2ᴴ * x.2)} :=
    Set.ext fun x =>
      ⟨fun (h : IsSubspaceEmbedding x.1 x.2 a b) => ⟨h.lower, h.upper⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [e]
  refine (isClosed_setOf_isSubspaceInjection a).inter (isClosed_le ?_ ?_)
  · exact ((continuous_fst.matrix_mul continuous_snd).matrix_conjTranspose).matrix_mul
      (continuous_fst.matrix_mul continuous_snd)
  · exact (continuous_snd.matrix_conjTranspose.matrix_mul continuous_snd).const_smul b

/-- For fixed $\mathbf{U}$, the sketches that are subspace injections for
$\operatorname{range}\mathbf{U}$ form a measurable set. -/
theorem measurableSet_setOf_isSubspaceInjection (U : Matrix n p 𝕜) (a : ℝ) :
    MeasurableSet {S : Matrix k n 𝕜 | IsSubspaceInjection S U a} := by
  have hc : Continuous fun S : Matrix k n 𝕜 => (S, U) := continuous_id.prodMk continuous_const
  exact ((isClosed_setOf_isSubspaceInjection a).preimage hc).measurableSet

/-- For fixed $\mathbf{U}$, the sketches that are subspace embeddings for
$\operatorname{range}\mathbf{U}$ form a measurable set. -/
theorem measurableSet_setOf_isSubspaceEmbedding (U : Matrix n p 𝕜) (a b : ℝ) :
    MeasurableSet {S : Matrix k n 𝕜 | IsSubspaceEmbedding S U a b} := by
  have hc : Continuous fun S : Matrix k n 𝕜 => (S, U) := continuous_id.prodMk continuous_const
  exact ((isClosed_setOf_isSubspaceEmbedding a b).preimage hc).measurableSet

end NLAlib
