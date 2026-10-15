/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Subspaces.ObliqueProjector

/-!
# Low-rank approximations from a range sketch and a co-range sketch

For $\mathbf{A} \in \Bbbk^{m \times n}$, a test matrix $\mathbf{\Omega} \in \Bbbk^{n \times l}$ and
a co-range test matrix $\mathbf{\Psi} \in \Bbbk^{m \times p}$, all deterministic here:

* the **randomized SVD approximation** (range finder) `NLAlib.rsvd A Ω` is
  $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$, two passes over $\mathbf{A}$;
* the **generalized Nyström approximation** `NLAlib.generalizedNystrom A Ω Ψ` is
  $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle$ (formula:
  `NLAlib.generalizedNystrom_def`), one pass, the oblique projector
  $\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}$ applied to $\mathbf{A}$.

The randomized SVD is the case $\mathbf{\Psi} = \mathbf{I}$. When
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})$ equals
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, the squared Frobenius error of generalized Nyström
is the error of the randomized SVD plus a sketch-and-solve excess, exactly; no full rank of
$\mathbf{A}\mathbf{\Omega}$ is assumed. Truncated variants have no names:
`truncatedSVD (rsvd A Ω) k` (late), `rangeProjector (truncatedSVD (A * Ω) k) * A` and
`obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ * A` (early).

Degenerate cases: for empty `l`, $\mathbf{\Omega} = \mathbf{0}$ or $\mathbf{A} = \mathbf{0}$ both
approximations are $\mathbf{0}$, and `NLAlib.generalizedNystrom_eq_self_of_rank_eq` then needs
$\mathbf{A} = \mathbf{0}$, which its hypothesis says. Design: `docs/design/LowRank-S0.md` §3.3, §8.

## Main definitions

* `NLAlib.rsvd`: $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$.
* `NLAlib.generalizedNystrom`: $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle$.

## Main results

* `NLAlib.rsvd_eq_obliqueProjector`, `NLAlib.generalizedNystrom_def`,
  `NLAlib.generalizedNystrom_one`, `NLAlib.sub_rsvd`, `NLAlib.sub_generalizedNystrom`: the source
  formulas and the residual bridges.
* `NLAlib.frobNorm_sub_generalizedNystrom_sq`: generalized Nyström error = randomized SVD error +
  sketch-and-solve excess.
* `NLAlib.rsvd_eq_self_of_rank_eq`, `NLAlib.generalizedNystrom_eq_self_of_rank_eq`: exactness at low
  rank.
* `NLAlib.generalizedNystrom_eq_mul_sketchAndSolve`: the core form through any basis of
  $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$.
* `NLAlib.HasOrthonormalCols.rsvd_mul_mul_conjTranspose`,
  `NLAlib.HasOrthonormalCols.generalizedNystrom_mul_mul_conjTranspose`: equivariance.
-/

@[expose] public section

open scoped Matrix ComplexOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p q : Type*} [Fintype l] [Fintype m] [Fintype n]

/-! ### The randomized SVD approximation -/

/-- The **randomized SVD approximation** (range-finder approximation)
$\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$ of $\mathbf{A}$ for a test matrix
$\mathbf{\Omega}$, here deterministic: the projection of $\mathbf{A}$ onto the range of the sketch
$\mathbf{A}\mathbf{\Omega}$, two passes over $\mathbf{A}$. Its rank is at most
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \le \lvert l \rvert$ (`NLAlib.rank_rsvd_le`); it is
$\mathbf{0}$ when $\mathbf{A}\mathbf{\Omega} = \mathbf{0}$.
[HalkoMartinssonTropp2011, Algorithm 4.1]; [MartinssonTropp2020, Algorithm 8]; there with a random
test matrix and an orthonormal basis of the sketch. -/
noncomputable def rsvd (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) : Matrix m n 𝕜 :=
  rangeProjector (A * Ω) * A

/-- The randomized SVD is the oblique projector with the identity sketch:
$$\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A} =
\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{I}}\mathbf{A}\,.$$ -/
theorem rsvd_eq_obliqueProjector [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    rsvd A Ω = obliqueProjector (A * Ω) (1 : Matrix m m 𝕜) * A := by
  rw [obliqueProjector_one, rsvd]

/-- The residual of the randomized SVD is the projection residual:
$$\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A} =
(\mathbf{I} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}})\mathbf{A}\,.$$ -/
theorem sub_rsvd [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    A - rsvd A Ω = (1 - rangeProjector (A * Ω)) * A := by
  rw [rsvd, Matrix.sub_mul, Matrix.one_mul]

/-- The randomized SVD has rank at most the rank of the sketch:
$$\operatorname{rank}(\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}) \le
\operatorname{rank}(\mathbf{A}\mathbf{\Omega})\,;$$
with Mathlib's `Matrix.rank_le_card_width`, at most $\lvert l \rvert$. -/
theorem rank_rsvd_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) : (rsvd A Ω).rank ≤ (A * Ω).rank :=
  (Matrix.rank_mul_le_left _ _).trans_eq (rank_rangeProjector _)

/-- The range of the randomized SVD lies in the range of the sketch:
$$\operatorname{range}(\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}) \subseteq
\operatorname{range}(\mathbf{A}\mathbf{\Omega})\,.$$ -/
theorem range_rsvd_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    LinearMap.range (rsvd A Ω).mulVecLin ≤ LinearMap.range (A * Ω).mulVecLin :=
  range_mulVecLin_le_iff_exists_mul.mpr
    ⟨pinv (A * Ω) * A, by rw [rsvd, ← mul_pinv, Matrix.mul_assoc]⟩

omit [Fintype m] in
/-- When the sketch keeps the rank of $\mathbf{A}$ its range is the range of $\mathbf{A}$. -/
private theorem range_mul_eq_of_rank_eq {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    (h : (A * Ω).rank = A.rank) :
    LinearMap.range (A * Ω).mulVecLin = LinearMap.range A.mulVecLin :=
  Submodule.eq_of_le_of_finrank_eq (range_mulVecLin_le_iff_exists_mul.mpr ⟨Ω, rfl⟩) h

/-- **Exactness of the randomized SVD at low rank**: if
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) = \operatorname{rank}\mathbf{A}$ then
$\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A} = \mathbf{A}$. -/
theorem rsvd_eq_self_of_rank_eq {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    (h : (A * Ω).rank = A.rank) : rsvd A Ω = A :=
  rangeProjector_mul_eq_self_iff.mpr (range_mul_eq_of_rank_eq h).ge

/-- **Equivariance of the randomized SVD**: for $\mathbf{U}$, $\mathbf{V}$ with orthonormal columns,
the approximation of $\mathbf{U}\mathbf{A}\mathbf{V}^{\mathsf{H}}$ with the test matrix
$\mathbf{V}\mathbf{\Omega}$ is
$\mathbf{U}(\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}) \mathbf{V}^{\mathsf{H}}$. This reduces
$\mathbf{A} = \mathbf{U}\mathbf{\Sigma}\mathbf{V}^{\mathsf{H}}$ to $\mathbf{\Sigma}$ under an
orthogonally invariant law of $\mathbf{\Omega}$. -/
theorem HasOrthonormalCols.rsvd_mul_mul_conjTranspose [DecidableEq m] [DecidableEq n]
    {m' n' : Type*} [Fintype m'] [Fintype n'] {U : Matrix m' m 𝕜} {V : Matrix n' n 𝕜}
    (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V) (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) :
    rsvd (U * A * Vᴴ) (V * Ω) = U * rsvd A Ω * Vᴴ := by
  have e : U * A * Vᴴ * (V * Ω) = U * (A * Ω) := by
    rw [Matrix.mul_assoc (U * A), hV.conjTranspose_mul_cancel_left, Matrix.mul_assoc]
  rw [rsvd, rsvd, e, hU.rangeProjector_mul]
  simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]

/-! ### The generalized Nyström approximation -/

variable [Fintype p]

/-- The **generalized Nyström approximation**
$$\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle =
\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A} =
\mathbf{A}\mathbf{\Omega}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$$
(`NLAlib.generalizedNystrom_def`): one pass, both sketches $\mathbf{A}\mathbf{\Omega}$ and
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$ linear in $\mathbf{A}$. Total; it is $\mathbf{0}$ when
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega} = \mathbf{0}$.
[EpperlyWebber2026, Definition 4.1]; [TroppYurtseverUdellCevher2017, (4.1)–(4.3)]; there with random
test matrices, and in TYUC through an orthonormal basis of the sketch. -/
noncomputable def generalizedNystrom (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
    Matrix m n 𝕜 :=
  obliqueProjector (A * Ω) Ψᴴ * A

/-- The source formula of the generalized Nyström approximation:
$$\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle =
\mathbf{A}\mathbf{\Omega}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}
\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\,.$$
[EpperlyWebber2026, Definition 4.1]. -/
theorem generalizedNystrom_def (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
    generalizedNystrom A Ω Ψ = A * Ω * pinv (Ψᴴ * A * Ω) * Ψᴴ * A := by
  rw [generalizedNystrom, obliqueProjector, Matrix.mul_assoc Ψᴴ A Ω]

/-- With $\mathbf{\Psi} = \mathbf{I}$ generalized Nyström is the randomized SVD:
$$\mathbf{A}\langle\mathbf{\Omega},\mathbf{I}\rangle =
\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\,.$$ -/
theorem generalizedNystrom_one [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) :
    generalizedNystrom A Ω (1 : Matrix m m 𝕜) = rsvd A Ω := by
  rw [generalizedNystrom, Matrix.conjTranspose_one, obliqueProjector_one, rsvd]

/-- The residual of generalized Nyström is an oblique projection residual:
$$\mathbf{A} - \mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle =
(\mathbf{I} - \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}})\mathbf{A}\,.$$ -/
theorem sub_generalizedNystrom [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) :
    A - generalizedNystrom A Ω Ψ = (1 - obliqueProjector (A * Ω) Ψᴴ) * A := by
  rw [generalizedNystrom, Matrix.sub_mul, Matrix.one_mul]

/-- Generalized Nyström has rank at most the rank of the core:
$$\operatorname{rank}\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle \le
\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})\,;$$
at most $\min(\lvert l \rvert, \lvert p \rvert)$ by Mathlib's `Matrix.rank_le_card_width` and
`Matrix.rank_le_card_height`. -/
theorem rank_generalizedNystrom_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
    (generalizedNystrom A Ω Ψ).rank ≤ (Ψᴴ * (A * Ω)).rank :=
  (Matrix.rank_mul_le_left _ _).trans_eq (rank_obliqueProjector _ _)

/-- The range of generalized Nyström lies in the range of the sketch:
$$\operatorname{range}\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle \subseteq
\operatorname{range}(\mathbf{A}\mathbf{\Omega})\,.$$ -/
theorem range_generalizedNystrom_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
    LinearMap.range (generalizedNystrom A Ω Ψ).mulVecLin ≤ LinearMap.range (A * Ω).mulVecLin :=
  range_mulVecLin_le_iff_exists_mul.mpr ⟨pinv (Ψᴴ * (A * Ω)) * Ψᴴ * A, by
    rw [generalizedNystrom, obliqueProjector]
    simp only [Matrix.mul_assoc]⟩

/-- **Generalized Nyström error = randomized SVD error + sketch-and-solve excess**, exactly, in
squared Frobenius norm: if
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})$ equals
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, then
$$\|\mathbf{A} - \mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A})\|_{\mathsf{F}}^2\,,$$
with no full rank of $\mathbf{A}\mathbf{\Omega}$ assumed. Without the rank hypothesis it is false.
[EpperlyWebber2026, proof of Theorem 4.2]; [TroppYurtseverUdellCevher2017, Lemma A.3]; there with
random test matrices of full rank. -/
theorem frobNorm_sub_generalizedNystrom_sq {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜} (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) :
    frobNorm (A - generalizedNystrom A Ω Ψ) ^ 2 =
      frobNorm (A - rsvd A Ω) ^ 2 +
        frobNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 2 := by
  classical
  rw [sub_generalizedNystrom, sub_rsvd]
  exact frobNorm_one_sub_obliqueProjector_mul_sq h A

/-- **Exactness of generalized Nyström at low rank**: if
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) = \operatorname{rank}\mathbf{A}$ and
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})$ equals
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$, then
$\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle = \mathbf{A}$. -/
theorem generalizedNystrom_eq_self_of_rank_eq {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Ψ : Matrix m p 𝕜} (hΩ : (A * Ω).rank = A.rank) (hΨ : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) :
    generalizedNystrom A Ω Ψ = A :=
  obliqueProjector_mul_eq_self_of_range_le hΨ (range_mul_eq_of_rank_eq hΩ).ge

/-- **Core form of generalized Nyström**: for any $\mathbf{Q}$ with
$\operatorname{range}\mathbf{Q} = \operatorname{range}(\mathbf{A}\mathbf{\Omega})$, for instance an
orthonormal basis, and when
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})$ equals
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$,
$$\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle =
\mathbf{Q}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\,,$$
the basis times the sketch-and-solve core. Orthonormality of $\mathbf{Q}$ is not needed.
[TroppYurtseverUdellCevher2017, (4.1)–(4.3)]; there with $\mathbf{Q}$ from a QR factorization of the
sketch $\mathbf{A}\mathbf{\Omega}$. -/
theorem generalizedNystrom_eq_mul_sketchAndSolve [Fintype q] {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜} {Q : Matrix m q 𝕜}
    (hQY : LinearMap.range Q.mulVecLin = LinearMap.range (A * Ω).mulVecLin)
    (hΨ : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) :
    generalizedNystrom A Ω Ψ = Q * sketchAndSolve Q Ψᴴ A := by
  rw [mul_sketchAndSolve, generalizedNystrom, obliqueProjector_eq_of_range_eq hΨ hQY.symm]

/-- **Equivariance of generalized Nyström**: for $\mathbf{U}$, $\mathbf{V}$ with orthonormal
columns,
$$(\mathbf{U}\mathbf{A}\mathbf{V}^{\mathsf{H}})\langle\mathbf{V}\mathbf{\Omega},
\mathbf{U}\mathbf{\Psi}\rangle = \mathbf{U}\,\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle
\mathbf{V}^{\mathsf{H}}\,.$$ -/
theorem HasOrthonormalCols.generalizedNystrom_mul_mul_conjTranspose [DecidableEq m]
    [DecidableEq n] {m' n' : Type*} [Fintype m'] [Fintype n'] {U : Matrix m' m 𝕜}
    {V : Matrix n' n 𝕜} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) :
    generalizedNystrom (U * A * Vᴴ) (V * Ω) (U * Ψ) = U * generalizedNystrom A Ω Ψ * Vᴴ := by
  have e : U * A * Vᴴ * (V * Ω) = U * (A * Ω) := by
    rw [Matrix.mul_assoc (U * A), hV.conjTranspose_mul_cancel_left, Matrix.mul_assoc]
  rw [generalizedNystrom, generalizedNystrom, e, Matrix.conjTranspose_mul,
    hU.obliqueProjector_mul_mul_conjTranspose]
  simp only [Matrix.mul_assoc, hU.conjTranspose_mul_cancel_left]

end NLAlib
