/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.Selection
public import NLAlib.Matrix.Factorizations.Nystrom
public import NLAlib.Matrix.Factorizations.SketchedLowRank
public import NLAlib.Matrix.Functions.AbsoluteValue

/-!
# The Nyström approximation and the Gram correspondence

For a square $\mathbf{A}$ and a test matrix $\mathbf{\Omega}$, `NLAlib.nystrom A Ω` is the Nyström
approximation $\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega})$, generalized Nyström with
$\mathbf{\Psi} = \mathbf{\Omega}$ (formula: `NLAlib.nystrom_def`). Its residual
$\mathbf{A} - \mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega})$ is the Schur complement of $\mathbf{A}$
with respect to $\mathbf{\Omega}$ and has no definition.

**The Gram correspondence**: the Nyström approximation of a Gram matrix
$\mathbf{F}^{\mathsf{H}}\mathbf{F}$ is the Gram matrix of the randomized SVD approximation of
$\mathbf{F}$, and the Nyström error is the Gram matrix of the randomized SVD error, for every
factor, test matrix and rank. Its singular values are the squared singular values of the randomized
SVD error, so every bound on the randomized SVD transfers to Nyström. For positive semidefinite
$\mathbf{A}$ the factor is $\mathbf{A}^{1/2}$ (`CFC.sqrt`).

The order and exactness theorems take `A.PosSemidef`; the general-factor, selection and equivariance
statements do not. Degenerate cases: for a Hermitian $\mathbf{A}$ that is not positive semidefinite
the rank lemma fails ($\mathbf{A} = \operatorname{diag}(1, -1)$,
$\mathbf{\Omega} = (1, 1)^{\mathsf{T}}$); for empty `l` the approximation is $\mathbf{0}$.

This file holds the LowRank stage S0 additions to `NLAlib.Matrix.Factorizations.Nystrom` and merges
into it at the round's wrap-up. Design: `docs/design/LowRank-S0.md` §3.4, §8.

## Main definitions

* `NLAlib.nystrom`: $\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega})$.

## Main results

* `NLAlib.nystrom_def`, `NLAlib.nystrom_selectionMatrix`: the source formulas.
* `NLAlib.nystrom_conjTranspose_mul_self`, `NLAlib.conjTranspose_mul_self_sub_nystrom`,
  `NLAlib.singularValues_conjTranspose_mul_self_sub_nystrom`,
  `NLAlib.nuclearNorm_conjTranspose_mul_self_sub_nystrom`: the Gram correspondence.
* `Matrix.PosSemidef.nystrom_eq`, `Matrix.PosSemidef.sub_nystrom_eq`,
  `Matrix.PosSemidef.singularValues_sub_nystrom`: the square-root forms.
* `Matrix.PosSemidef.nystrom`, `Matrix.PosSemidef.nystrom_le`:
  $\mathbf{0} \preceq \mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) \preceq \mathbf{A}$.
* `Matrix.PosSemidef.rank_conjTranspose_mul_mul`: Nyström always keeps the rank of the sketch.
* `Matrix.PosSemidef.nystrom_eq_self_of_rank_eq`, `Matrix.PosSemidef.nystrom_eq_of_range_eq`:
  exactness and representation invariance.
* `NLAlib.HasOrthonormalCols.nystrom_mul_mul_conjTranspose`: equivariance.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p q : Type*} [Fintype l] [Fintype m] [Fintype n]

/-- The **Nyström approximation**
$$\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) :=
\mathbf{A}\mathbf{\Omega}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}$$
(`NLAlib.nystrom_def`), the generalized Nyström approximation with
$\mathbf{\Psi} = \mathbf{\Omega}$. Defined for every square $\mathbf{A}$; the order and exactness
theorems take `A.PosSemidef`, the general-factor, selection and equivariance statements do not. For
Hermitian $\mathbf{A}$ it is
$$(\mathbf{A}\mathbf{\Omega})(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
(\mathbf{A}\mathbf{\Omega})^{\mathsf{H}}\,.$$
It is $\mathbf{0}$ when $\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega} = \mathbf{0}$.
[MartinssonTropp2020, (2.3), (14.1)]; [EpperlyWebber2026, Definition 3.4];
[HalkoMartinssonTropp2011, Algorithm 5.5]; there for positive semidefinite $\mathbf{A}$ and a random
test matrix. -/
noncomputable def nystrom (A : Matrix n n 𝕜) (Ω : Matrix n l 𝕜) : Matrix n n 𝕜 :=
  generalizedNystrom A Ω Ω

/-- The source formula of the Nyström approximation:
$$\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) =
\mathbf{A}\mathbf{\Omega}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\,.$$
[MartinssonTropp2020, (2.3)]; [EpperlyWebber2026, Definition 3.4]. -/
theorem nystrom_def (A : Matrix n n 𝕜) (Ω : Matrix n l 𝕜) :
    nystrom A Ω = A * Ω * pinv (Ωᴴ * A * Ω) * Ωᴴ * A :=
  generalizedNystrom_def A Ω Ω

/-! ### The Gram correspondence -/

/-- **The Gram correspondence**: the Nyström approximation of $\mathbf{F}^{\mathsf{H}}\mathbf{F}$ is
the Gram matrix of the randomized SVD approximation of $\mathbf{F}$,
$$\mathsf{nystrom}(\mathbf{F}^{\mathsf{H}}\mathbf{F}, \mathbf{\Omega}) =
(\mathsf{rsvd}(\mathbf{F}, \mathbf{\Omega}))^{\mathsf{H}}
\mathsf{rsvd}(\mathbf{F}, \mathbf{\Omega})\,,$$
for every factor, test matrix and rank.
[MartinssonTropp2020, Proposition 11.1, §14.2]; [EpperlyWebber2026, Fact 3.5];
[CamanoEpperlyMeyerTropp2025, Imported Theorem 2.4]; [TroppWebber2023, §5.4]; there with
$\mathbf{F} = \mathbf{A}^{1/2}$ or in trace form only.
Result: gram-correspondence -/
theorem nystrom_conjTranspose_mul_self (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    nystrom (Fᴴ * F) Ω = (rsvd F Ω)ᴴ * rsvd F Ω := by
  have hP := isStarProjection_rangeProjector (F * Ω)
  have e : Fᴴ * F * Ω * pinv (Ωᴴ * (Fᴴ * F) * Ω) * Ωᴴ * (Fᴴ * F) =
      Fᴴ * (F * Ω * pinv ((F * Ω)ᴴ * (F * Ω)) * (F * Ω)ᴴ) * F := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  have hPF : rangeProjector (F * Ω) * (rangeProjector (F * Ω) * F) =
      rangeProjector (F * Ω) * F := by
    rw [← Matrix.mul_assoc, hP.mul_self]
  rw [nystrom_def, e, mul_pinv_conjTranspose_mul_self_mul_conjTranspose, rsvd,
    Matrix.conjTranspose_mul, hP.conjTranspose_eq]
  simp only [Matrix.mul_assoc, hPF]

/-- **The Gram correspondence, error form**: the Nyström error of
$\mathbf{H} = \mathbf{F}^{\mathsf{H}}\mathbf{F}$ is the Gram matrix of the randomized SVD error,
$$\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega}) = \mathbf{E}^{\mathsf{H}}\mathbf{E},
\qquad \mathbf{E} = \mathbf{F} - \mathsf{rsvd}(\mathbf{F}, \mathbf{\Omega})\,.$$
[MartinssonTropp2020, Proposition 11.1]; [EpperlyWebber2026, Fact 3.5]; there with
$\mathbf{F} = \mathbf{A}^{1/2}$.
Result: gram-correspondence -/
theorem conjTranspose_mul_self_sub_nystrom (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    Fᴴ * F - nystrom (Fᴴ * F) Ω = (F - rsvd F Ω)ᴴ * (F - rsvd F Ω) := by
  classical
  have hP := isStarProjection_rangeProjector (F * Ω)
  have h1 : (1 - rangeProjector (F * Ω)) * ((1 - rangeProjector (F * Ω)) * F) =
      (1 - rangeProjector (F * Ω)) * F := by
    rw [← Matrix.mul_assoc, hP.one_sub.mul_self]
  have hPF : rangeProjector (F * Ω) * (rangeProjector (F * Ω) * F) =
      rangeProjector (F * Ω) * F := by
    rw [← Matrix.mul_assoc, hP.mul_self]
  rw [nystrom_conjTranspose_mul_self, sub_rsvd, rsvd, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    hP.conjTranspose_eq]
  simp only [Matrix.mul_assoc, h1, hPF]
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul]

/-- The singular values of the Nyström error of $\mathbf{F}^{\mathsf{H}}\mathbf{F}$ are the squared
singular values of the randomized SVD error of $\mathbf{F}$:
$$\sigma_k(\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})) =
\sigma_k(\mathbf{F} - \mathsf{rsvd}(\mathbf{F}, \mathbf{\Omega}))^2$$
for every index $k$, so every unitarily invariant norm of the one is a quadratic norm of the other.
[MartinssonTropp2020, Proposition 11.1]; [TroppWebber2023, §5.4]; there for the norms. -/
theorem singularValues_conjTranspose_mul_self_sub_nystrom (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (k : ℕ) :
    singularValues (Fᴴ * F - nystrom (Fᴴ * F) Ω) k = singularValues (F - rsvd F Ω) k ^ 2 := by
  rw [conjTranspose_mul_self_sub_nystrom, singularValues_conjTranspose_mul_self]

/-- **The Gram correspondence, trace form**: the nuclear norm of the Nyström error of
$\mathbf{F}^{\mathsf{H}}\mathbf{F}$ is the squared Frobenius error of the randomized SVD,
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_* =
\|\mathbf{F} - \mathsf{rsvd}(\mathbf{F}, \mathbf{\Omega})\|_{\mathsf{F}}^2\,.$$
[CamanoEpperlyMeyerTropp2025, Imported Theorem 2.4]; [EpperlyWebber2026, Fact 3.5]; there as a trace
with $\mathbf{F} = \mathbf{A}^{1/2}$.
Result: gram-correspondence -/
theorem nuclearNorm_conjTranspose_mul_self_sub_nystrom (F : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    nuclearNorm (Fᴴ * F - nystrom (Fᴴ * F) Ω) = frobNorm (F - rsvd F Ω) ^ 2 := by
  rw [conjTranspose_mul_self_sub_nystrom,
    (Matrix.posSemidef_conjTranspose_mul_self _).nuclearNorm_eq_re_trace, frobNorm_sq_eq_re_trace]

/-! ### Positive semidefinite matrices -/

section PosSemidef

variable {A : Matrix n n 𝕜}

open scoped Classical in
/-- For positive semidefinite $\mathbf{A}$, the square root is a Hermitian factor of $\mathbf{A}$:
$\mathbf{A} = (\mathbf{A}^{1/2})^{\mathsf{H}}\mathbf{A}^{1/2}$. -/
private theorem eq_conjTranspose_sqrt_mul_sqrt (hA : A.PosSemidef) :
    (CFC.sqrt A)ᴴ = CFC.sqrt A ∧ A = (CFC.sqrt A)ᴴ * CFC.sqrt A := by
  have hR : (CFC.sqrt A)ᴴ = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  exact ⟨hR, by rw [hR, CFC.sqrt_mul_sqrt_self A hA.nonneg]⟩

open scoped Classical in
/-- **The square-root form of Nyström**: for positive semidefinite $\mathbf{A}$,
$$\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) =
\mathbf{A}^{1/2}\mathsf{rsvd}(\mathbf{A}^{1/2}, \mathbf{\Omega})\,.$$
[MartinssonTropp2020, §14.2]; [TroppWebber2023, §5.4]; stated there without proof. -/
theorem _root_.Matrix.PosSemidef.nystrom_eq (hA : A.PosSemidef)
    (Ω : Matrix n l 𝕜) :
    nystrom A Ω = CFC.sqrt A * rangeProjector (CFC.sqrt A * Ω) * CFC.sqrt A := by
  obtain ⟨hR, hA'⟩ := eq_conjTranspose_sqrt_mul_sqrt hA
  have hP := isStarProjection_rangeProjector (CFC.sqrt A * Ω)
  conv_lhs => rw [hA']
  have hPR : rangeProjector (CFC.sqrt A * Ω) * (rangeProjector (CFC.sqrt A * Ω) * CFC.sqrt A) =
      rangeProjector (CFC.sqrt A * Ω) * CFC.sqrt A := by
    rw [← Matrix.mul_assoc, hP.mul_self]
  rw [nystrom_conjTranspose_mul_self, rsvd, Matrix.conjTranspose_mul, hP.conjTranspose_eq, hR]
  simp only [Matrix.mul_assoc, hPR]

open scoped Classical in
/-- **The Gram correspondence for a positive semidefinite matrix**: the Nyström error is the Gram
matrix of the randomized SVD error of the square root,
$$\mathbf{A} - \mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) = \mathbf{E}^{\mathsf{H}}\mathbf{E},
\qquad \mathbf{E} = \mathbf{A}^{1/2} - \mathsf{rsvd}(\mathbf{A}^{1/2}, \mathbf{\Omega})\,.$$
[MartinssonTropp2020, Proposition 11.1]; [EpperlyWebber2026, Fact 3.5]; [TroppWebber2023, §5.4].
Result: gram-correspondence -/
theorem _root_.Matrix.PosSemidef.sub_nystrom_eq (hA : A.PosSemidef)
    (Ω : Matrix n l 𝕜) :
    A - nystrom A Ω =
      (CFC.sqrt A - rsvd (CFC.sqrt A) Ω)ᴴ * (CFC.sqrt A - rsvd (CFC.sqrt A) Ω) := by
  obtain ⟨-, hA'⟩ := eq_conjTranspose_sqrt_mul_sqrt hA
  conv_lhs => rw [hA']
  exact conjTranspose_mul_self_sub_nystrom (CFC.sqrt A) Ω

open scoped Classical in
/-- The singular values of the Nyström error of a positive semidefinite $\mathbf{A}$ are the squared
singular values of the randomized SVD error of $\mathbf{A}^{1/2}$, at every index:
$$\sigma_k(\mathbf{A} - \mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega})) =
\sigma_k(\mathbf{A}^{1/2} - \mathsf{rsvd}(\mathbf{A}^{1/2}, \mathbf{\Omega}))^2\,.$$
[MartinssonTropp2020, Proposition 11.1]; [TroppWebber2023, §5.4]. -/
theorem _root_.Matrix.PosSemidef.singularValues_sub_nystrom (hA : A.PosSemidef)
    (Ω : Matrix n l 𝕜) (k : ℕ) :
    singularValues (A - nystrom A Ω) k =
      singularValues (CFC.sqrt A - rsvd (CFC.sqrt A) Ω) k ^ 2 := by
  rw [hA.sub_nystrom_eq, singularValues_conjTranspose_mul_self]

/-- The Nyström approximation of a positive semidefinite matrix is positive semidefinite:
$\mathbf{0} \preceq \mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega})$.
[MartinssonTropp2020, §2.7]; [EpperlyWebber2026, Fact 6.1(a)]. -/
theorem _root_.Matrix.PosSemidef.nystrom (hA : A.PosSemidef) (Ω : Matrix n l 𝕜) :
    (nystrom A Ω).PosSemidef := by
  classical
  obtain ⟨-, hA'⟩ := eq_conjTranspose_sqrt_mul_sqrt hA
  rw [hA', nystrom_conjTranspose_mul_self]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The Nyström approximation of a positive semidefinite matrix lies below it:
$\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) \preceq \mathbf{A}$.
[MartinssonTropp2020, §2.7]; [EpperlyWebber2026, Fact 6.1(a)]. -/
theorem _root_.Matrix.PosSemidef.nystrom_le (hA : A.PosSemidef) (Ω : Matrix n l 𝕜) :
    nystrom A Ω ≤ A := by
  classical
  rw [Matrix.le_iff, hA.sub_nystrom_eq]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- **Nyström keeps the rank of the sketch**: for positive semidefinite $\mathbf{A}$ and every
$\mathbf{\Omega}$, $\operatorname{rank}(\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})$
equals $\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$: the rank hypothesis of the oblique
projector $\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Omega}^{\mathsf{H}}}$. False for
Hermitian $\mathbf{A}$ that is not positive semidefinite. -/
theorem _root_.Matrix.PosSemidef.rank_conjTranspose_mul_mul (hA : A.PosSemidef)
    (Ω : Matrix n l 𝕜) : (Ωᴴ * (A * Ω)).rank = (A * Ω).rank := by
  classical
  obtain ⟨hR, -⟩ := eq_conjTranspose_sqrt_mul_sqrt hA
  have hRR : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have e1 : Ωᴴ * (A * Ω) = (CFC.sqrt A * Ω)ᴴ * (CFC.sqrt A * Ω) := by
    rw [Matrix.conjTranspose_mul, hR]
    conv_lhs => rw [← hRR]
    simp only [Matrix.mul_assoc]
  have e2 : A * Ω = CFC.sqrt A * (CFC.sqrt A * Ω) := by
    conv_lhs => rw [← hRR]
    rw [Matrix.mul_assoc]
  refine le_antisymm (Matrix.rank_mul_le_right _ _) ?_
  rw [e1, Matrix.rank_conjTranspose_mul_self]
  conv_lhs => rw [e2]
  exact Matrix.rank_mul_le_right _ _

/-- **Exactness of Nyström at low rank**: for positive semidefinite $\mathbf{A}$ with
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) = \operatorname{rank}\mathbf{A}$,
$\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) = \mathbf{A}$. -/
theorem _root_.Matrix.PosSemidef.nystrom_eq_self_of_rank_eq (hA : A.PosSemidef)
    {Ω : Matrix n l 𝕜} (h : (A * Ω).rank = A.rank) : nystrom A Ω = A :=
  generalizedNystrom_eq_self_of_rank_eq h (hA.rank_conjTranspose_mul_mul Ω)

/-- **Representation invariance**: for positive semidefinite $\mathbf{A}$ the Nyström approximation
depends on the test matrix only through its range,
$\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}) = \mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega}')$
when
$\operatorname{range}\mathbf{\Omega} = \operatorname{range}\mathbf{\Omega}'$, whatever the widths;
the invertible case is $\mathbf{\Omega}' = \mathbf{\Omega}\mathbf{M}$.
[EpperlyWebber2026, Fact 6.1(b)]; there for invertible $\mathbf{M}$. -/
theorem _root_.Matrix.PosSemidef.nystrom_eq_of_range_eq [Fintype q] (hA : A.PosSemidef)
    {Ω : Matrix n l 𝕜} {Ω' : Matrix n q 𝕜}
    (h : LinearMap.range Ω.mulVecLin = LinearMap.range Ω'.mulVecLin) :
    nystrom A Ω = nystrom A Ω' := by
  classical
  rw [hA.nystrom_eq, hA.nystrom_eq]
  obtain ⟨C, hC⟩ := range_mulVecLin_le_iff_exists_mul.mp h.ge
  obtain ⟨D, hD⟩ := range_mulVecLin_le_iff_exists_mul.mp h.le
  have hP : rangeProjector (CFC.sqrt A * Ω) = rangeProjector (CFC.sqrt A * Ω') := by
    refine rangeProjector_inj.mpr (le_antisymm ?_ ?_)
    · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨D, by rw [Matrix.mul_assoc, ← hD]⟩
    · exact range_mulVecLin_le_iff_exists_mul.mpr ⟨C, by rw [Matrix.mul_assoc, ← hC]⟩
  rw [hP]

end PosSemidef

/-! ### Selection and equivariance -/

/-- **The selection case**: the Nyström approximation along `selectionMatrix e` is
$\mathbf{A}_{:,e}(\mathbf{A}_{e,e})^{+}\mathbf{A}_{e,:}$, the matrix whose residual
`Matrix.PosSemidef.sub_submatrix_mul_pinv_mul` and its neighbours study. Repeated indices are
allowed. -/
theorem nystrom_selectionMatrix [Fintype p] [DecidableEq n] (A : Matrix n n 𝕜) (e : p → n) :
    nystrom A (selectionMatrix e) =
      A.submatrix id e * pinv (A.submatrix e e) * A.submatrix e id := by
  rw [nystrom_def, conjTranspose_selectionMatrix_mul_mul_selectionMatrix, mul_selectionMatrix,
    Matrix.mul_assoc (A.submatrix id e * pinv (A.submatrix e e)),
    conjTranspose_selectionMatrix_mul]

/-- **Equivariance of Nyström**: for $\mathbf{U}$ with orthonormal columns,
$$\mathsf{nystrom}(\mathbf{U}\mathbf{A}\mathbf{U}^{\mathsf{H}}, \mathbf{U}\mathbf{\Omega}) =
\mathbf{U}\,\mathsf{nystrom}(\mathbf{A}, \mathbf{\Omega})\mathbf{U}^{\mathsf{H}}\,,$$
for every square $\mathbf{A}$. -/
theorem HasOrthonormalCols.nystrom_mul_mul_conjTranspose [DecidableEq n] {n' : Type*}
    [Fintype n'] {U : Matrix n' n 𝕜} (hU : HasOrthonormalCols U) (A : Matrix n n 𝕜)
    (Ω : Matrix n l 𝕜) : nystrom (U * A * Uᴴ) (U * Ω) = U * nystrom A Ω * Uᴴ :=
  hU.generalizedNystrom_mul_mul_conjTranspose hU A Ω Ω

end NLAlib
