/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.Pinv
public import NLAlib.Matrix.Norms.UnitarilyInvariant

/-!
# Oblique projectors from a basis and a sketch

For a basis $\mathbf{X} \in \Bbbk^{m \times r}$ and a sketch $\mathbf{S} \in \Bbbk^{k \times m}$,
`NLAlib.obliqueProjector X S` is
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} = \mathbf{X}(\mathbf{S}\mathbf{X})^{+}\mathbf{S}$: the fitted
values of the least-squares problem
$\min_{\mathbf{C}} \|\mathbf{S}(\mathbf{X}\mathbf{C} - \mathbf{B})\|_{\mathsf{F}}$, as a matrix
acting on $\mathbf{B}$. It is defined for every shape and rank and is always idempotent. It projects
onto $\operatorname{range}\mathbf{X}$ exactly when the sketch keeps the rank of $\mathbf{X}$,
written `(S * X).rank = X.rank` in every statement (`NLAlib.rank_mul_eq_iff_injOn`: $\mathbf{S}$ is
injective on $\operatorname{range}\mathbf{X}$). Randomized SVD, generalized Nyström and
sketch-and-solve are all this projector applied to a matrix
(`NLAlib.Matrix.Factorizations.SketchedLowRank`).

The exact error split: under the rank hypothesis,
$$(\mathbf{I} - \mathbf{\Pi})\mathbf{B} = (\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{B} -
\mathbf{\Pi}(\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{B}$$
with orthogonal terms, so the squared Frobenius error is the orthogonal-projection error plus a
sketched term, and the Gram matrices add. `NLAlib.sketchAndSolve A S B` is the sketched
least-squares solution $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{B}$ and
$\mathbf{A}\hat{\mathbf{X}} = \mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{B}$.

Degenerate cases: for $\mathbf{S}\mathbf{X} = \mathbf{0}$ (empty `k`, $\mathbf{S} = \mathbf{0}$,
$\mathbf{X} = \mathbf{0}$, empty `r`) the projector is $\mathbf{0}$, and the rank hypothesis holds
iff $\mathbf{X} = \mathbf{0}$. Without the hypothesis the projector still has range inside
$\operatorname{range}\mathbf{X}$, but it does not fix $\mathbf{X}$ and depends on more than the
range of $\mathbf{X}$. Design: `docs/design/LowRank-S0.md` §3.1, §8.

## Main definitions

* `NLAlib.obliqueProjector`: $\mathbf{X}(\mathbf{S}\mathbf{X})^{+}\mathbf{S}$.
* `NLAlib.sketchAndSolve`: $(\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{B}$.

## Main results

* `NLAlib.rank_mul_eq_iff_injOn`: the rank hypothesis is injectivity on the range.
* `NLAlib.isIdempotentElem_obliqueProjector`, `NLAlib.rank_obliqueProjector`,
  `NLAlib.obliqueProjector_mul_self_iff`, `NLAlib.range_obliqueProjector`: the projector.
* `NLAlib.obliqueProjector_eq_of_range_eq`: it depends on $\mathbf{X}$ only through its range.
* `NLAlib.obliqueProjector_one`, `NLAlib.obliqueProjector_conjTranspose_self`,
  `NLAlib.obliqueProjector_of_isUnit`: the orthogonal and the invertible cases.
* `NLAlib.HasOrthonormalCols.obliqueProjector_mul_mul_conjTranspose`,
  `NLAlib.HasOrthonormalCols.obliqueProjector_mul_left`: equivariance and sketch invariance.
* `NLAlib.one_sub_obliqueProjector_mul`,
  `NLAlib.conjTranspose_mul_self_one_sub_obliqueProjector_mul`,
  `NLAlib.frobNorm_one_sub_obliqueProjector_mul_sq`,
  `NLAlib.SymmetricGauge.matrixNorm_conjTranspose_mul_self_one_sub_obliqueProjector_mul_le`: the
  exact error split.
* `NLAlib.mul_sketchAndSolve`, `NLAlib.sketchAndSolve_eq_pinv_mul_add`,
  `NLAlib.HasOrthonormalCols.sketchAndSolve_eq_add`: sketch-and-solve and its core noise.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {k m n p q r : Type*} [Fintype k] [Fintype m] [Fintype r]

/-! ### The oblique projector -/

/-- The **oblique projector**
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} = \mathbf{X}(\mathbf{S}\mathbf{X})^{+}\mathbf{S}$ defined by a
basis $\mathbf{X}$ and a sketch $\mathbf{S}$: the fitted values of the least-squares problem
sketched by $\mathbf{S}$. Total: always idempotent (`NLAlib.isIdempotentElem_obliqueProjector`),
with range $\mathbf{X}\operatorname{range}((\mathbf{S}\mathbf{X})^{\mathsf{H}})$ inside
$\operatorname{range}\mathbf{X}$; it projects onto $\operatorname{range}\mathbf{X}$ exactly when
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$, and its junk value is
$\mathbf{0}$ when $\mathbf{S}\mathbf{X} = \mathbf{0}$. It is unchanged by
$\mathbf{X} \mapsto \mathbf{X}\mathbf{M}$ for invertible $\mathbf{M}$ (under the rank hypothesis),
by $\mathbf{S} \mapsto c\,\mathbf{S}$ for $c \ne 0$ and by $\mathbf{S} \mapsto \mathbf{W}\mathbf{S}$
for $\mathbf{W}$ with orthonormal columns, but not by $\mathbf{S} \mapsto \mathbf{M}\mathbf{S}$ for
a general invertible $\mathbf{M}$, even under the rank hypothesis: it depends on
$\mathbf{S}^{\mathsf{H}}\mathbf{S}$, not only on the row space of $\mathbf{S}$. The two-bases
formula $\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$ is
`obliqueProjector X Yᴴ` (`NLAlib.obliqueProjector_of_isUnit`).
[EpperlyWebber2026, Lemma 5.1, proof]; [TroppYurtseverUdellCevher2017, (4.2), (4.3)];
[CamanoEpperlyMeyerTropp2025, §2.4]; there with a basis of full or equal rank, here total, every
shape and rank. -/
noncomputable def obliqueProjector (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) : Matrix m m 𝕜 :=
  X * pinv (S * X) * S

variable {X : Matrix m r 𝕜} {S : Matrix k m 𝕜}

omit [Fintype k] in
/-- **The rank interface**: the sketch $\mathbf{S}$ keeps the rank of $\mathbf{X}$,
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$, exactly when it is
injective on $\operatorname{range}\mathbf{X}$. This is the form `NLAlib.IsSubspaceInjection.injOn`
concludes. -/
theorem rank_mul_eq_iff_injOn :
    (S * X).rank = X.rank ↔ Set.InjOn S.mulVec (LinearMap.range X.mulVecLin) := by
  set V := LinearMap.range X.mulVecLin
  set g := S.mulVecLin.domRestrict V
  have hr : LinearMap.range g = LinearMap.range (S * X).mulVecLin := by
    rw [LinearMap.range_domRestrict, Matrix.mulVecLin_mul, LinearMap.range_comp]
  have hn := LinearMap.finrank_range_add_finrank_ker g
  rw [hr] at hn
  have hinj : Set.InjOn S.mulVec V ↔ Function.Injective g := by
    constructor
    · intro h a b hab
      exact Subtype.ext (h a.2 b.2 (by simpa [g] using hab))
    · intro h a ha b hb hab
      exact congrArg Subtype.val (@h ⟨a, ha⟩ ⟨b, hb⟩ (by simpa [g] using hab))
  rw [hinj, ← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  change Module.finrank 𝕜 (LinearMap.range (S * X).mulVecLin) = Module.finrank 𝕜 V ↔ _
  omega

/-- Under the rank hypothesis the row space of $\mathbf{S}\mathbf{X}$ is the row space of
$\mathbf{X}$. -/
private theorem range_conjTranspose_mul_eq (h : (S * X).rank = X.rank) :
    LinearMap.range (S * X)ᴴ.mulVecLin = LinearMap.range Xᴴ.mulVecLin := by
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨Sᴴ, Matrix.conjTranspose_mul S X⟩
  · change (S * X)ᴴ.rank = Xᴴ.rank
    rw [Matrix.rank_conjTranspose, Matrix.rank_conjTranspose, h]

/-- The oblique projector is **idempotent**, for every basis and sketch:
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}^2 = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$. -/
theorem isIdempotentElem_obliqueProjector (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    IsIdempotentElem (obliqueProjector X S) := by
  unfold IsIdempotentElem obliqueProjector
  calc X * pinv (S * X) * S * (X * pinv (S * X) * S)
      = X * (pinv (S * X) * (S * X) * pinv (S * X)) * S := by simp only [Matrix.mul_assoc]
    _ = X * pinv (S * X) * S := by rw [pinv_mul_mul_pinv]

/-- The range of the oblique projector lies in the range of the basis, for every basis and sketch:
$$\operatorname{range}\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} \subseteq
\operatorname{range}\mathbf{X}\,.$$ -/
theorem range_obliqueProjector_le (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    LinearMap.range (obliqueProjector X S).mulVecLin ≤ LinearMap.range X.mulVecLin :=
  range_mulVecLin_le_iff_exists_mul.mpr ⟨pinv (S * X) * S, Matrix.mul_assoc _ _ _⟩

/-- The orthogonal projector onto $\operatorname{range}\mathbf{X}$ fixes the oblique projector:
$(\mathbf{I} - \mathbf{P}_{\mathbf{X}})\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} = \mathbf{0}$, for every
basis and sketch. -/
theorem one_sub_rangeProjector_mul_obliqueProjector [DecidableEq m] (X : Matrix m r 𝕜)
    (S : Matrix k m 𝕜) : (1 - rangeProjector X) * obliqueProjector X S = 0 := by
  rw [obliqueProjector, Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.sub_mul, Matrix.one_mul,
    rangeProjector_mul_self, sub_self, Matrix.zero_mul]

/-- The rank of the oblique projector is the rank of the sketched basis, for every basis and sketch:
$$\operatorname{rank}\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} =
\operatorname{rank}(\mathbf{S}\mathbf{X})\,.$$ -/
theorem rank_obliqueProjector (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    (obliqueProjector X S).rank = (S * X).rank := by
  refine le_antisymm ?_ ?_
  · calc (obliqueProjector X S).rank ≤ (X * pinv (S * X)).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (pinv (S * X)).rank := Matrix.rank_mul_le_right _ _
      _ = (S * X).rank := rank_pinv _
  · have h : S * X = S * obliqueProjector X S * X := by
      have := mul_pinv_mul_self (S * X)
      simp only [obliqueProjector, ← Matrix.mul_assoc] at this ⊢
      exact this.symm
    calc (S * X).rank = (S * obliqueProjector X S * X).rank := by rw [← h]
      _ ≤ (S * obliqueProjector X S).rank := Matrix.rank_mul_le_left _ _
      _ ≤ (obliqueProjector X S).rank := Matrix.rank_mul_le_right _ _

/-- **The oblique projector fixes its basis exactly under the rank hypothesis**:
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{X} = \mathbf{X}$ iff
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$. -/
theorem obliqueProjector_mul_self_iff :
    obliqueProjector X S * X = X ↔ (S * X).rank = X.rank := by
  constructor
  · intro h
    refine le_antisymm (Matrix.rank_mul_le_right _ _) ?_
    calc X.rank = (obliqueProjector X S * X).rank := by rw [h]
      _ ≤ (obliqueProjector X S).rank := Matrix.rank_mul_le_left _ _
      _ = (S * X).rank := rank_obliqueProjector X S
  · intro h
    have hP : rangeProjector (S * X)ᴴ = rangeProjector Xᴴ :=
      rangeProjector_inj.mpr (range_conjTranspose_mul_eq h)
    calc obliqueProjector X S * X = X * (pinv (S * X) * (S * X)) := by
          simp only [obliqueProjector, Matrix.mul_assoc]
      _ = X := by rw [pinv_mul, hP, ← pinv_mul, ← Matrix.mul_assoc, mul_pinv_mul_self]

/-- **Exactness at low rank**: under the rank hypothesis
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$, the oblique projector
fixes every $\mathbf{B}$ with
$\operatorname{range}\mathbf{B} \subseteq \operatorname{range}\mathbf{X}$:
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{B} = \mathbf{B}$. -/
theorem obliqueProjector_mul_eq_self_of_range_le [Fintype n] {B : Matrix m n 𝕜}
    (h : (S * X).rank = X.rank) (hB : LinearMap.range B.mulVecLin ≤ LinearMap.range X.mulVecLin) :
    obliqueProjector X S * B = B := by
  obtain ⟨C, rfl⟩ := range_mulVecLin_le_iff_exists_mul.mp hB
  rw [← Matrix.mul_assoc, obliqueProjector_mul_self_iff.mpr h]

/-- Under the rank hypothesis the oblique projector fixes the orthogonal projector onto the same
range: $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{P}_{\mathbf{X}} = \mathbf{P}_{\mathbf{X}}$. -/
theorem obliqueProjector_mul_rangeProjector (h : (S * X).rank = X.rank) :
    obliqueProjector X S * rangeProjector X = rangeProjector X :=
  obliqueProjector_mul_eq_self_of_range_le h (range_mulVecLin_rangeProjector X).le

/-- Under the rank hypothesis the oblique projector projects onto the range of its basis:
$\operatorname{range}\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} = \operatorname{range}\mathbf{X}$. -/
theorem range_obliqueProjector (h : (S * X).rank = X.rank) :
    LinearMap.range (obliqueProjector X S).mulVecLin = LinearMap.range X.mulVecLin := by
  refine le_antisymm (range_obliqueProjector_le X S) ?_
  exact range_mulVecLin_le_iff_exists_mul.mpr ⟨X, (obliqueProjector_mul_self_iff.mpr h).symm⟩

/-- **Range invariance**: under the rank hypothesis $\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ depends
on $\mathbf{X}$ only through its range,
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}} = \mathbf{\Pi}_{\mathbf{X}',\mathbf{S}}$ when
$\operatorname{range}\mathbf{X} = \operatorname{range}\mathbf{X}'$, whatever the widths. Without the
hypothesis it is false: for $\mathbf{X} = \mathbf{I}_2$, $\mathbf{S} = \mathbf{e}_1^{\mathsf{H}}$
and $\mathbf{X}' = \mathbf{X}\mathbf{M}$ with $\mathbf{M}$ upper triangular with unit entries, the
two projectors differ. -/
theorem obliqueProjector_eq_of_range_eq [Fintype q] {X' : Matrix m q 𝕜} (h : (S * X).rank = X.rank)
    (hX : LinearMap.range X.mulVecLin = LinearMap.range X'.mulVecLin) :
    obliqueProjector X S = obliqueProjector X' S := by
  obtain ⟨C, hC⟩ := range_mulVecLin_le_iff_exists_mul.mp hX.ge
  obtain ⟨D, hD⟩ := range_mulVecLin_le_iff_exists_mul.mp hX.le
  have hSX : rangeProjector (S * X') = rangeProjector (S * X) := by
    refine rangeProjector_inj.mpr (le_antisymm ?_ ?_)
    · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨C, by rw [Matrix.mul_assoc, ← hC]⟩
    · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨D, by rw [Matrix.mul_assoc, ← hD]⟩
  have hP : obliqueProjector X S * obliqueProjector X' S = obliqueProjector X' S :=
    obliqueProjector_mul_eq_self_of_range_le h ((range_obliqueProjector_le X' S).trans hX.ge)
  refine Eq.trans ?_ hP
  symm
  calc obliqueProjector X S * obliqueProjector X' S
      = X * pinv (S * X) * (S * X' * pinv (S * X')) * S := by
        simp only [obliqueProjector, Matrix.mul_assoc]
    _ = X * (pinv (S * X) * (S * X) * pinv (S * X)) * S := by
        rw [mul_pinv, hSX, ← mul_pinv]
        simp only [Matrix.mul_assoc]
    _ = obliqueProjector X S := by rw [pinv_mul_mul_pinv, obliqueProjector, Matrix.mul_assoc]

/-- Under the rank hypothesis, changing the basis by an invertible matrix does not change the
oblique projector:
$\mathbf{\Pi}_{\mathbf{X}\mathbf{M},\mathbf{S}} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$. -/
theorem obliqueProjector_mul_of_isUnit [DecidableEq r] {M : Matrix r r 𝕜}
    (h : (S * X).rank = X.rank) (hM : IsUnit M) :
    obliqueProjector (X * M) S = obliqueProjector X S := by
  refine (obliqueProjector_eq_of_range_eq h ?_).symm
  rw [Matrix.mulVecLin_mul]
  refine (LinearMap.range_comp_of_range_eq_top _ ?_).symm
  rw [LinearMap.range_eq_top, Matrix.coe_mulVecLin]
  exact Matrix.mulVec_surjective_iff_isUnit.mpr hM

/-- With the identity as sketch the oblique projector is the orthogonal projector:
$\mathbf{\Pi}_{\mathbf{X},\mathbf{I}} = \mathbf{P}_{\mathbf{X}}$. -/
@[simp]
theorem obliqueProjector_one [DecidableEq m] (X : Matrix m r 𝕜) :
    obliqueProjector X (1 : Matrix m m 𝕜) = rangeProjector X := by
  rw [obliqueProjector, Matrix.one_mul, Matrix.mul_one, mul_pinv]

/-- With the sketch $\mathbf{X}^{\mathsf{H}}$ the oblique projector is the orthogonal projector:
$$\mathbf{\Pi}_{\mathbf{X},\mathbf{X}^{\mathsf{H}}} =
\mathbf{X}(\mathbf{X}^{\mathsf{H}}\mathbf{X})^{+}\mathbf{X}^{\mathsf{H}} =
\mathbf{P}_{\mathbf{X}}\,.$$ -/
@[simp]
theorem obliqueProjector_conjTranspose_self (X : Matrix m r 𝕜) :
    obliqueProjector X Xᴴ = rangeProjector X :=
  mul_pinv_conjTranspose_mul_self_mul_conjTranspose X

/-- **Rescaling the sketch** does not change the projector:
$\mathbf{\Pi}_{\mathbf{X},c\mathbf{S}} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ for $c \ne 0$ (the
normalisation of Gaussian sketches); a real scalar is the case `RCLike.real_smul_eq_coe_smul`. -/
theorem obliqueProjector_smul_right (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) {c : 𝕜} (hc : c ≠ 0) :
    obliqueProjector X (c • S) = obliqueProjector X S := by
  simp only [obliqueProjector, Matrix.smul_mul, Matrix.mul_smul, pinv_smul, smul_smul,
    mul_inv_cancel₀ hc, one_smul]

/-- **The invertible case**: when $\mathbf{T}\mathbf{X}$ is invertible,
$\mathbf{\Pi}_{\mathbf{X},\mathbf{T}} = \mathbf{X}(\mathbf{T}\mathbf{X})^{-1}\mathbf{T}$; with
$\mathbf{T} = \mathbf{Y}^{\mathsf{H}}$ this is the two-bases formula
$\mathbf{X}(\mathbf{Y}^{\mathsf{H}}\mathbf{X})^{-1}\mathbf{Y}^{\mathsf{H}}$. -/
theorem obliqueProjector_of_isUnit [DecidableEq r] {T : Matrix r m 𝕜} (h : IsUnit (T * X)) :
    obliqueProjector X T = X * (T * X)⁻¹ * T := by
  rw [obliqueProjector, pinv_of_isUnit h]

/-- The oblique projector annihilates the kernel of the sketch:
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{B} = \mathbf{0}$ when
$\mathbf{S}\mathbf{B} = \mathbf{0}$, for every basis. -/
theorem obliqueProjector_mul_eq_zero_of_mul_eq_zero {B : Matrix m n 𝕜} (X : Matrix m r 𝕜)
    (h : S * B = 0) : obliqueProjector X S * B = 0 := by
  rw [obliqueProjector, Matrix.mul_assoc, h, Matrix.mul_zero]

/-- **Equivariance under an isometry** $\mathbf{U}$ with
$\mathbf{U}^{\mathsf{H}}\mathbf{U} = \mathbf{I}$, for every basis and sketch,
$$\mathbf{\Pi}_{\mathbf{U}\mathbf{X},\mathbf{S}\mathbf{U}^{\mathsf{H}}} =
\mathbf{U}\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{U}^{\mathsf{H}}\,.$$ -/
theorem HasOrthonormalCols.obliqueProjector_mul_mul_conjTranspose [Fintype n] [DecidableEq m]
    {U : Matrix n m 𝕜} (hU : HasOrthonormalCols U) (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    obliqueProjector (U * X) (S * Uᴴ) = U * obliqueProjector X S * Uᴴ := by
  have e : S * Uᴴ * (U * X) = S * X := by
    rw [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]
  rw [obliqueProjector, obliqueProjector, e]
  simp only [Matrix.mul_assoc]

/-- **Sketch invariance**: a factor with orthonormal columns on the left of the sketch does not
change the projector,
$\mathbf{\Pi}_{\mathbf{X},\mathbf{W}\mathbf{S}} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ for
$\mathbf{W}^{\mathsf{H}}\mathbf{W} = \mathbf{I}$; for laws invariant under
$\mathbf{S} \mapsto \mathbf{W}\mathbf{S}$. -/
theorem HasOrthonormalCols.obliqueProjector_mul_left [DecidableEq k] {k' : Type*} [Fintype k']
    {W : Matrix k' k 𝕜} (hW : HasOrthonormalCols W) (X : Matrix m r 𝕜) (S : Matrix k m 𝕜) :
    obliqueProjector X (W * S) = obliqueProjector X S := by
  rw [obliqueProjector, obliqueProjector, Matrix.mul_assoc W, hW.pinv_mul_left]
  simp only [Matrix.mul_assoc, hW.conjTranspose_mul_cancel_left]

/-! ### The exact error split -/

/-- **The exact error split, linear form**: under the rank hypothesis,
$$(\mathbf{I}-\mathbf{\Pi})\mathbf{B} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B} -
\mathbf{\Pi}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$$
with $\mathbf{\Pi} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$: the error of the oblique projection is
the error of the orthogonal one minus the oblique projection of that error.
[EpperlyWebber2026, Lemma 5.1, (5.2)]; [CamanoEpperlyMeyerTropp2025, Lemma 2.6];
[TroppYurtseverUdellCevher2017, Lemmas A.3, A.4]; there a trace identity in a basis, here a matrix
identity. -/
theorem one_sub_obliqueProjector_mul [DecidableEq m] (h : (S * X).rank = X.rank)
    (B : Matrix m n 𝕜) :
    (1 - obliqueProjector X S) * B =
      (1 - rangeProjector X) * B - obliqueProjector X S * ((1 - rangeProjector X) * B) := by
  have hP := obliqueProjector_mul_rangeProjector h
  rw [← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hP]
  simp only [Matrix.sub_mul, Matrix.one_mul]
  abel

/-- **The exact error split, Gram form**: under the rank hypothesis the two terms of
`NLAlib.one_sub_obliqueProjector_mul` have orthogonal ranges, so the Gram matrix of the error is the
sum of their Gram matrices: with $\mathbf{\Pi} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ and
$\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$,
$$((\mathbf{I}-\mathbf{\Pi})\mathbf{B})^{\mathsf{H}}(\mathbf{I}-\mathbf{\Pi})\mathbf{B} =
\mathbf{E}^{\mathsf{H}}\mathbf{E} + (\mathbf{\Pi}\mathbf{E})^{\mathsf{H}}\mathbf{\Pi}\mathbf{E}\,.$$
[EpperlyWebber2026, Lemma 5.1, (5.2)]; [CamanoEpperlyMeyerTropp2025, Lemma 2.6];
[TroppYurtseverUdellCevher2017, Lemmas A.3, A.4]; there a trace identity in a basis.
Result: oblique-projection-error-split -/
theorem conjTranspose_mul_self_one_sub_obliqueProjector_mul [DecidableEq m]
    (h : (S * X).rank = X.rank) (B : Matrix m n 𝕜) :
    ((1 - obliqueProjector X S) * B)ᴴ * ((1 - obliqueProjector X S) * B) =
      ((1 - rangeProjector X) * B)ᴴ * ((1 - rangeProjector X) * B) +
        (obliqueProjector X S * ((1 - rangeProjector X) * B))ᴴ *
          (obliqueProjector X S * ((1 - rangeProjector X) * B)) := by
  set E := (1 - rangeProjector X) * B
  set P := obliqueProjector X S
  have hR : (1 - rangeProjector X)ᴴ = 1 - rangeProjector X := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, conjTranspose_rangeProjector]
  have h0 : Eᴴ * (P * E) = 0 := by
    rw [Matrix.conjTranspose_mul, hR, Matrix.mul_assoc, ← Matrix.mul_assoc (1 - rangeProjector X),
      one_sub_rangeProjector_mul_obliqueProjector, Matrix.zero_mul, Matrix.mul_zero]
  have h0' : (P * E)ᴴ * E = 0 := by
    rw [← Matrix.conjTranspose_conjTranspose E, ← Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, h0, Matrix.conjTranspose_zero]
  rw [one_sub_obliqueProjector_mul h B, Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub,
    Matrix.mul_sub, h0, h0']
  abel

/-- **The exact error split** in squared Frobenius norm: under the rank hypothesis,
$$\|(\mathbf{I}-\mathbf{\Pi})\mathbf{B}\|_{\mathsf{F}}^2 =
\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2 +
\|\mathbf{\Pi}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2$$
with $\mathbf{\Pi} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$, the trace of the Gram form.
[EpperlyWebber2026, Lemma 5.1, (5.2)]; [CamanoEpperlyMeyerTropp2025, Lemma 2.6];
[TroppYurtseverUdellCevher2017, Lemma A.4]; there in a basis.
Result: oblique-projection-error-split -/
theorem frobNorm_one_sub_obliqueProjector_mul_sq [Fintype n] [DecidableEq m]
    (h : (S * X).rank = X.rank) (B : Matrix m n 𝕜) :
    frobNorm ((1 - obliqueProjector X S) * B) ^ 2 =
      frobNorm ((1 - rangeProjector X) * B) ^ 2 +
        frobNorm (obliqueProjector X S * ((1 - rangeProjector X) * B)) ^ 2 := by
  rw [frobNorm_sq_eq_re_trace, frobNorm_sq_eq_re_trace, frobNorm_sq_eq_re_trace,
    conjTranspose_mul_self_one_sub_obliqueProjector_mul h B, Matrix.trace_add, map_add]

/-- **The exact error split in every unitarily invariant norm**, in the Gram form that quadratic
norms use: under the rank hypothesis, with $\mathbf{\Pi} = \mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ and
$\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$,
$$\|((\mathbf{I}-\mathbf{\Pi})\mathbf{B})^{\mathsf{H}}(\mathbf{I}-\mathbf{\Pi})\mathbf{B}\|_{\Phi}
\le \|\mathbf{E}^{\mathsf{H}}\mathbf{E}\|_{\Phi} +
\|(\mathbf{\Pi}\mathbf{E})^{\mathsf{H}}\mathbf{\Pi}\mathbf{E}\|_{\Phi}\,.$$
[EpperlyWebber2026, Lemma 5.1, (5.2)]; there the trace, here every gauge. -/
theorem SymmetricGauge.matrixNorm_conjTranspose_mul_self_one_sub_obliqueProjector_mul_le
    [Fintype n] [DecidableEq m] (Φ : SymmetricGauge) (h : (S * X).rank = X.rank)
    (B : Matrix m n 𝕜) :
    Φ.matrixNorm (((1 - obliqueProjector X S) * B)ᴴ * ((1 - obliqueProjector X S) * B)) ≤
      Φ.matrixNorm (((1 - rangeProjector X) * B)ᴴ * ((1 - rangeProjector X) * B)) +
        Φ.matrixNorm ((obliqueProjector X S * ((1 - rangeProjector X) * B))ᴴ *
          (obliqueProjector X S * ((1 - rangeProjector X) * B))) := by
  rw [conjTranspose_mul_self_one_sub_obliqueProjector_mul h B]
  exact Φ.matrixNorm_add_le _ _

/-! ### Sketch-and-solve -/

section SketchAndSolve

variable [Fintype n]

/-- The **sketch-and-solve solution**
$\hat{\mathbf{X}} = (\mathbf{S}\mathbf{A})^{+}\mathbf{S}\mathbf{B}$, the minimum-norm minimizer of
$\|\mathbf{S}(\mathbf{A}\mathbf{X} - \mathbf{B})\|_{\mathsf{F}}$, column by column
(`NLAlib.isLeastSquaresSolution_pinv_mulVec`). Total; its junk value is $\mathbf{0}$ when
$\mathbf{S}\mathbf{A} = \mathbf{0}$. The argument order is system, sketch, right-hand side, as in
`NLAlib.obliqueProjector`.
[EpperlyWebber2026, §2]; there with $\mathbf{S} = \mathbf{\Omega}^{\mathsf{H}}$. -/
noncomputable def sketchAndSolve (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜) :
    Matrix n p 𝕜 :=
  pinv (S * A) * (S * B)

/-- The fitted values of sketch-and-solve are the oblique projection of the right-hand side:
$\mathbf{A}\hat{\mathbf{X}} = \mathbf{\Pi}_{\mathbf{A},\mathbf{S}}\mathbf{B}$. -/
theorem mul_sketchAndSolve (A : Matrix m n 𝕜) (S : Matrix k m 𝕜) (B : Matrix m p 𝕜) :
    A * sketchAndSolve A S B = obliqueProjector A S * B := by
  rw [sketchAndSolve, obliqueProjector]
  simp only [Matrix.mul_assoc]

/-- **Sketch-and-solve error decomposition**: when
$\operatorname{rank}(\mathbf{S}\mathbf{A}) = \operatorname{rank}\mathbf{A}$,
$$\hat{\mathbf{X}} = \mathbf{A}^{+}\mathbf{B} +
(\mathbf{S}\mathbf{A})^{+}\mathbf{S}(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}\,:$$
the sketched solution is the exact minimum-norm solution plus the sketch-and-solve solution for the
optimal residual. This is the exact identity beside the bound `sketch-and-solve-ls`
(`NLAlib.IsSubspaceInjection.frobNorm_sub_mul_pinv_mul_sq_le`).
[EpperlyWebber2026, Lemma 5.1, (5.1)]; there in a factorization $\mathbf{A} = \mathbf{Q}\mathbf{R}$,
here basis-free.
Result: sketch-and-solve-error-decomposition -/
theorem sketchAndSolve_eq_pinv_mul_add [DecidableEq m] {A : Matrix m n 𝕜}
    (h : (S * A).rank = A.rank) (B : Matrix m p 𝕜) :
    sketchAndSolve A S B = pinv A * B + sketchAndSolve A S ((1 - rangeProjector A) * B) := by
  have hP : rangeProjector (S * A)ᴴ = rangeProjector Aᴴ :=
    rangeProjector_inj.mpr (range_conjTranspose_mul_eq h)
  have key : pinv (S * A) * (S * (rangeProjector A * B)) = pinv A * B := by
    calc pinv (S * A) * (S * (rangeProjector A * B))
        = pinv (S * A) * (S * A) * pinv A * B := by
          rw [← mul_pinv]
          simp only [Matrix.mul_assoc]
      _ = pinv A * B := by
          rw [pinv_mul, hP, ← pinv_mul, pinv_mul_mul_pinv]
  rw [sketchAndSolve, sketchAndSolve, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub,
    Matrix.mul_sub, key]
  abel

/-- **Core noise**: for $\mathbf{Q}$ with orthonormal columns and
$\operatorname{rank}(\mathbf{S}\mathbf{Q}) = \operatorname{rank}\mathbf{Q}$ (full column rank of
$\mathbf{S}\mathbf{Q}$), the sketched core is the exact core plus noise,
$$(\mathbf{S}\mathbf{Q})^{+}\mathbf{S}\mathbf{B} = \mathbf{Q}^{\mathsf{H}}\mathbf{B} +
(\mathbf{S}\mathbf{Q})^{+}\mathbf{S}(\mathbf{I}-\mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{B}\,.$$
[TroppYurtseverUdellCevher2017, Lemma A.4]; [CamanoEpperlyMeyerTropp2025, Lemma 2.6]; there with a
complement frame.
Result: sketch-and-solve-error-decomposition -/
theorem HasOrthonormalCols.sketchAndSolve_eq_add [Fintype q] [DecidableEq m] [DecidableEq q]
    {Q : Matrix m q 𝕜} (hQ : HasOrthonormalCols Q) (h : (S * Q).rank = Q.rank)
    (B : Matrix m p 𝕜) :
    sketchAndSolve Q S B = Qᴴ * B + sketchAndSolve Q S ((1 - Q * Qᴴ) * B) := by
  rw [sketchAndSolve_eq_pinv_mul_add h B, hQ.pinv_eq, hQ.rangeProjector_eq]

end SketchAndSolve

end NLAlib
