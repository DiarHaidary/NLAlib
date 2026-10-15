/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Pseudoinverse.LeastSquares

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
$\mathbf{A}\mathbf{\Omega}$ is assumed.

Truncation. Late truncation is spelled `truncatedSVD (rsvd A Ω) k`, and likewise for the other
outputs (`truncatedSVD (generalizedNystrom A Ω Ψ) k`); it has no name of its own. Early truncation,
which replaces the sketch $\mathbf{A}\mathbf{\Omega}$ by its truncated SVD
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ before projecting, is named:
`NLAlib.earlyTruncatedRSVD A Ω k` is
$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}$ and
`NLAlib.earlyTruncatedGeneralizedNystrom A Ω Ψ k` is
$$\mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,\mathbf{\Psi}^{\mathsf{H}}}
\mathbf{A}\,.$$
Errors are written as $\mathbf{A}$ minus the named output.

Degenerate cases: for empty `l`, $\mathbf{\Omega} = \mathbf{0}$ or $\mathbf{A} = \mathbf{0}$ all
approximations are $\mathbf{0}$, and `NLAlib.generalizedNystrom_eq_self_of_rank_eq` then needs
$\mathbf{A} = \mathbf{0}$, which its hypothesis says; for $k = 0$ the early-truncated outputs are
$\mathbf{0}$. Design: `docs/design/LowRank-S0.md` §3.3, §8; `docs/design/LowRank-S2b.md` §3.1, §8.

## Main definitions

* `NLAlib.rsvd`: $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$.
* `NLAlib.generalizedNystrom`: $\mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle$.
* `NLAlib.earlyTruncatedRSVD`, `NLAlib.earlyTruncatedGeneralizedNystrom`: early truncation.

## Main results

* `NLAlib.rsvd_eq_obliqueProjector`, `NLAlib.generalizedNystrom_def`,
  `NLAlib.generalizedNystrom_one`, `NLAlib.sub_rsvd`, `NLAlib.sub_generalizedNystrom`: the source
  formulas and the residual bridges.
* `NLAlib.singularValues_sub_rsvd_le`, `NLAlib.singularValues_sub_rsvd_le_sub_mul`: the error of
  the randomized SVD has singular values at most those of $\mathbf{A}$, and of the error of every
  approximation $\mathbf{A}\mathbf{\Omega}\mathbf{X}$ built from the sketch.
* `NLAlib.frobNorm_sub_generalizedNystrom_sq`: generalized Nyström error = randomized SVD error +
  sketch-and-solve excess.
* `NLAlib.rsvd_eq_self_of_rank_eq`, `NLAlib.generalizedNystrom_eq_self_of_rank_eq`: exactness at low
  rank.
* `NLAlib.generalizedNystrom_eq_mul_sketchAndSolve`: the core form through any basis of
  $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$.
* `NLAlib.HasOrthonormalCols.rsvd_mul_mul_conjTranspose`,
  `NLAlib.HasOrthonormalCols.generalizedNystrom_mul_mul_conjTranspose`: equivariance.
* `NLAlib.earlyTruncatedRSVD_mul`, `NLAlib.rank_earlyTruncatedRSVD_le`,
  `NLAlib.rank_earlyTruncatedGeneralizedNystrom_le`, `NLAlib.earlyTruncatedRSVD_of_rank_le`,
  `NLAlib.earlyTruncatedGeneralizedNystrom_of_rank_le`, `NLAlib.sub_earlyTruncatedRSVD`,
  `NLAlib.sub_earlyTruncatedGeneralizedNystrom`: the early-truncation API.
* `NLAlib.frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq`: early-truncated generalized Nyström
  error = early-truncated randomized SVD error + sketch-and-solve excess.
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

/-- The singular values of the error of the randomized SVD are at most those of $\mathbf{A}$:
$\sigma_i(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}) \le \sigma_i(\mathbf{A})$
for every test matrix $\mathbf{\Omega}$ and every $i$. -/
theorem singularValues_sub_rsvd_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (i : ℕ) :
    singularValues (A - rsvd A Ω) i ≤ singularValues A i := by
  classical
  rw [sub_rsvd]
  exact singularValues_one_sub_rangeProjector_mul_le (A * Ω) A i

/-- **The randomized SVD beats every approximation built from the sketch**, singular value by
singular value:
$\sigma_i(\mathbf{A} - \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}) \le
\sigma_i(\mathbf{A} - \mathbf{A}\mathbf{\Omega}\mathbf{X})$ for every $\mathbf{X}$ and every $i$;
at $\mathbf{X} = \mathbf{0}$ this is `NLAlib.singularValues_sub_rsvd_le`. -/
theorem singularValues_sub_rsvd_le_sub_mul (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (X : Matrix l n 𝕜) (i : ℕ) :
    singularValues (A - rsvd A Ω) i ≤ singularValues (A - A * Ω * X) i := by
  classical
  rw [sub_rsvd, ← one_sub_rangeProjector_mul_sub_mul (A * Ω) A X]
  exact singularValues_one_sub_rangeProjector_mul_le (A * Ω) _ i

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

/-! ### Early truncation -/

/-- The **early-truncated randomized SVD**
$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}$: the projection of
$\mathbf{A}$ onto the range of the truncated SVD of the sketch $\mathbf{A}\mathbf{\Omega}$, that is
onto $k$ dominant left singular vectors of the sketch. Rank at most $k$
(`NLAlib.rank_earlyTruncatedRSVD_le`); $\lvert l \rvert$ products with $\mathbf{A}$ and at most $k$
with $\mathbf{A}^{\mathsf{H}}$. Under ties
$\sigma_{k-1}(\mathbf{A}\mathbf{\Omega}) = \sigma_k(\mathbf{A}\mathbf{\Omega})$ it depends on the
choice `truncatedSVD` makes, and so does its error.
[Woodruff2014, Theorem 61]; there transposed, with the sketch on the left.
[CohenElderMuscoMuscoPersu2015, §10.1], there transposed; [CohenElderMuscoMuscoPersu2015, §7.2], a
remark in this orientation. -/
noncomputable def earlyTruncatedRSVD (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    Matrix m n 𝕜 :=
  rangeProjector (truncatedSVD (A * Ω) k) * A

/-- The early-truncated randomized SVD reproduces the truncated sketch:
$$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}\mathbf{\Omega} =
\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k\,.$$ -/
theorem earlyTruncatedRSVD_mul (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    earlyTruncatedRSVD A Ω k * Ω = truncatedSVD (A * Ω) k := by
  rw [earlyTruncatedRSVD, Matrix.mul_assoc, rangeProjector_truncatedSVD_mul]

/-- The residual of the early-truncated randomized SVD is a projection residual:
$$\mathbf{A} - \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A} =
(\mathbf{I} - \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k})\mathbf{A}\,.$$ -/
theorem sub_earlyTruncatedRSVD [DecidableEq m] (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    A - earlyTruncatedRSVD A Ω k = (1 - rangeProjector (truncatedSVD (A * Ω) k)) * A := by
  rw [earlyTruncatedRSVD, Matrix.sub_mul, Matrix.one_mul]

/-- The early-truncated randomized SVD has rank at most $k$:
$$\operatorname{rank}(\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A})
\le k\,.$$ -/
theorem rank_earlyTruncatedRSVD_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    (earlyTruncatedRSVD A Ω k).rank ≤ k :=
  ((Matrix.rank_mul_le_left _ _).trans_eq (rank_rangeProjector _)).trans
    (rank_truncatedSVD_le _ k)

/-- With $k$ at least the rank of the sketch nothing is truncated: when
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \le k$,
$$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A} =
\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\,.$$ -/
theorem earlyTruncatedRSVD_of_rank_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {k : ℕ}
    (hk : (A * Ω).rank ≤ k) : earlyTruncatedRSVD A Ω k = rsvd A Ω := by
  rw [earlyTruncatedRSVD, truncatedSVD_of_rank_le _ hk, rsvd]

/-- The **early-truncated generalized Nyström approximation**
$$\mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,\mathbf{\Psi}^{\mathsf{H}}}
\mathbf{A}\,:$$
generalized Nyström with the range sketch $\mathbf{A}\mathbf{\Omega}$ replaced by its truncated SVD.
One pass; rank at most $k$ (`NLAlib.rank_earlyTruncatedGeneralizedNystrom_le`). Under ties of the
singular values of the sketch it depends on the choice `truncatedSVD` makes.
[TroppYurtseverUdellCevher2017, §7.3.1, (7.3)]; there through a basis of $k$ dominant left singular
vectors of the sketch, a QR factorization, and a final truncation that is the identity. TYUC state
the algorithm and report, from CEMMP, a high-probability $(1+\varepsilon)$ bound at
$\Theta(r/\varepsilon^2)$ for both sketch sizes with unspecified constants; no bound is taken from
it. The bounds on this output compose `NLAlib.frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq`
with a bound on the sketch-and-solve term and an early-truncated randomized SVD bound. -/
noncomputable def earlyTruncatedGeneralizedNystrom (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ * A

/-- The residual of early-truncated generalized Nyström is an oblique projection residual:
$$\mathbf{A} - \mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,
\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A} = (\mathbf{I} -
\mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,\mathbf{\Psi}^{\mathsf{H}}})
\mathbf{A}\,.$$ -/
theorem sub_earlyTruncatedGeneralizedNystrom [DecidableEq m] (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) (k : ℕ) :
    A - earlyTruncatedGeneralizedNystrom A Ω Ψ k =
      (1 - obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ) * A := by
  rw [earlyTruncatedGeneralizedNystrom, Matrix.sub_mul, Matrix.one_mul]

/-- Early-truncated generalized Nyström has rank at most $k$:
$$\operatorname{rank}(\mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,
\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A}) \le k\,.$$ -/
theorem rank_earlyTruncatedGeneralizedNystrom_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) (k : ℕ) : (earlyTruncatedGeneralizedNystrom A Ω Ψ k).rank ≤ k :=
  (((Matrix.rank_mul_le_left _ _).trans_eq (rank_obliqueProjector _ _)).trans
    (Matrix.rank_mul_le_right _ _)).trans (rank_truncatedSVD_le _ k)

/-- With $k$ at least the rank of the sketch nothing is truncated: when
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \le k$,
$$\mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,\mathbf{\Psi}^{\mathsf{H}}}
\mathbf{A} = \mathbf{A}\langle\mathbf{\Omega},\mathbf{\Psi}\rangle\,.$$ -/
theorem earlyTruncatedGeneralizedNystrom_of_rank_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {k : ℕ} (hk : (A * Ω).rank ≤ k) (Ψ : Matrix m p 𝕜) :
    earlyTruncatedGeneralizedNystrom A Ω Ψ k = generalizedNystrom A Ω Ψ := by
  rw [earlyTruncatedGeneralizedNystrom, truncatedSVD_of_rank_le _ hk, generalizedNystrom]

/-- **Early-truncated generalized Nyström error = early-truncated randomized SVD error +
sketch-and-solve excess**, exactly, in squared Frobenius norm: with
$\mathbf{X} = \llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$ and
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{X}) = \operatorname{rank}\mathbf{X}$,
$$\|\mathbf{A} - \mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A}\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \mathbf{P}_{\mathbf{X}}\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{P}_{\mathbf{X}}\mathbf{A})\|_{\mathsf{F}}^2\,.$$
The deterministic half of every bound on early-truncated generalized Nyström: the last term is the
one a completion identity or a subspace injection bounds. The rank hypothesis is at the actual rank
of $\mathbf{X}$, which may be below $k$. Without it the identity fails
($\mathbf{\Psi} = \mathbf{0}$, $\mathbf{A} = \mathbf{\Omega} = \mathbf{I}_2$, $k = 2$). -/
theorem frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Ψ : Matrix m p 𝕜} {k : ℕ}
    (h : (Ψᴴ * truncatedSVD (A * Ω) k).rank = (truncatedSVD (A * Ω) k).rank) :
    frobNorm (A - earlyTruncatedGeneralizedNystrom A Ω Ψ k) ^ 2 =
      frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 +
        frobNorm (obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ *
          (A - earlyTruncatedRSVD A Ω k)) ^ 2 := by
  classical
  rw [sub_earlyTruncatedGeneralizedNystrom, sub_earlyTruncatedRSVD]
  exact frobNorm_one_sub_obliqueProjector_mul_sq h A

end NLAlib
