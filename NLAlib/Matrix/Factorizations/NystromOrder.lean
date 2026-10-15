/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.NystromGram
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Matrix.Spectral.SingularValueInequalities
public import NLAlib.Matrix.Spectral.Weyl

/-!
# The Nyström residual in the Loewner order

For positive semidefinite $\mathbf{H}$ and a test matrix $\mathbf{\Omega}$, the Nyström residual
$\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$ is the Schur complement of $\mathbf{H}$
with
respect to $\mathbf{\Omega}$, written $\mathbf{H}/\mathbf{\Omega}$ in docstrings and
`H - nystrom H Ω` in Lean, with no definition. Its quadratic form at $\mathbf{x}$ is the least value
of the quadratic form of $\mathbf{H}$ over the affine space
$\mathbf{x} + \operatorname{range}\mathbf{\Omega}$. Consequences: $\mathbf{H}/\mathbf{\Omega}$ is
monotone and superadditive (hence concave) in $\mathbf{H}$, the approximation improves as
$\operatorname{range}\mathbf{\Omega}$ grows, and Nyström is at least as accurate as projecting
$\mathbf{H}$ onto the complement of $\operatorname{range}\mathbf{\Omega}$ ("Nyström helps"), in
every unitarily invariant norm. Loewner antitonicity of the inverse is
`Matrix.PosDef.inv_le_inv_of_le`.

Degenerate cases: for empty `l` both sides of the variational form are
$\operatorname{Re}\langle\mathbf{x}, \mathbf{H}\mathbf{x}\rangle$; for
$\mathbf{\Omega} = \mathbf{0}$ "Nyström helps" is an equality; an empty sum in the superadditivity
is $\mathbf{0}$ on both sides.

Design: `docs/design/LowRank-S0.md` §3.5, §8.

## Main results

* `Matrix.PosSemidef.isLeast_re_quadForm_sub_mulVec`: the variational form.
* `Matrix.PosSemidef.sub_nystrom_le_sub_nystrom`: monotonicity.
* `NLAlib.sum_smul_sub_nystrom_le`: superadditivity with nonnegative weights.
* `Matrix.PosSemidef.nystrom_le_nystrom_of_range_le`: more samples, better approximation.
* `Matrix.PosSemidef.singularValues_sub_nystrom_le`,
  `NLAlib.SymmetricGauge.matrixNorm_sub_nystrom_le`: Nyström helps.
* `Matrix.PosSemidef.singularValues_nystrom_le`: Nyström does not increase singular values.
* `Matrix.PosSemidef.truncatedSVD_nystrom_le`: truncated Nyström stays below the matrix.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l n q : Type*} [Fintype l] [Fintype n]

/-- **Variational form of the Schur complement**
$\mathbf{H}/\mathbf{\Omega} = \mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$: for
positive
semidefinite $\mathbf{H}$,
$$\operatorname{Re}\langle\mathbf{x}, (\mathbf{H}/\mathbf{\Omega})\mathbf{x}\rangle =
\min_{\mathbf{y}} \operatorname{Re}\langle\mathbf{x}-\mathbf{\Omega}\mathbf{y},
\mathbf{H}(\mathbf{x}-\mathbf{\Omega}\mathbf{y})\rangle\,,$$
the minimum attained. An instance of `NLAlib.isLeast_re_quadForm_fromBlocks`.
[MartinssonTropp2020, §2.7]; [HornJohnson2013, §7.7]. -/
theorem _root_.Matrix.PosSemidef.isLeast_re_quadForm_sub_mulVec {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (x : n → 𝕜) :
    IsLeast (Set.range fun y : l → 𝕜 => RCLike.re (quadForm H (x - Ω *ᵥ y)))
      (RCLike.re (quadForm (H - nystrom H Ω) x)) := by
  classical
  have hblk : (Matrix.fromCols Ω (1 : Matrix n n 𝕜))ᴴ * H * Matrix.fromCols Ω 1 =
      Matrix.fromBlocks (Ωᴴ * H * Ω) (Ωᴴ * H) (Ωᴴ * H)ᴴ H := by
    rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul,
      Matrix.fromRows_mul_fromCols, Matrix.conjTranspose_mul, hH.isHermitian.eq,
      Matrix.conjTranspose_conjTranspose, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one, Matrix.mul_one]
  have hPSD : (Matrix.fromBlocks (Ωᴴ * H * Ω) (Ωᴴ * H) (Ωᴴ * H)ᴴ H).PosSemidef := by
    rw [← hblk]
    exact hH.conjTranspose_mul_mul_same _
  have hL := isLeast_re_quadForm_fromBlocks hPSD x
  have hschur : H - (Ωᴴ * H)ᴴ * pinv (Ωᴴ * H * Ω) * (Ωᴴ * H) = H - nystrom H Ω := by
    rw [nystrom_def, Matrix.conjTranspose_mul, hH.isHermitian.eq,
      Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have hq : ∀ y : l → 𝕜, quadForm (Matrix.fromBlocks (Ωᴴ * H * Ω) (Ωᴴ * H) (Ωᴴ * H)ᴴ H)
      (Sum.elim y x) = quadForm H (x - Ω *ᵥ (-y)) := by
    intro y
    rw [← hblk, quadForm_conjTranspose_mul_mul, Matrix.fromCols_mulVec_sumElim,
      Matrix.one_mulVec, Matrix.mulVec_neg, sub_neg_eq_add, add_comm]
  have hset : (Set.range fun y : l → 𝕜 => RCLike.re
      (quadForm (Matrix.fromBlocks (Ωᴴ * H * Ω) (Ωᴴ * H) (Ωᴴ * H)ᴴ H) (Sum.elim y x))) =
      Set.range fun y : l → 𝕜 => RCLike.re (quadForm H (x - Ω *ᵥ y)) := by
    ext t
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨-y, by simp only [hq]⟩
    · rintro ⟨y, rfl⟩
      exact ⟨-y, by simp only [hq, neg_neg]⟩
  rwa [hset, hschur] at hL

/-- **Monotonicity of the Schur complement** $\mathbf{H} \mapsto \mathbf{H}/\mathbf{\Omega}$: for
positive semidefinite $\mathbf{H} \preceq \mathbf{H}'$,
$$\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega}) \preceq
\mathbf{H}' - \mathsf{nystrom}(\mathbf{H}', \mathbf{\Omega})\,.$$
[MartinssonTropp2020, Corollary 11.2]; [EpperlyWebber2026, Fact 6.1(d)].
Result: schur-complement-monotone -/
theorem _root_.Matrix.PosSemidef.sub_nystrom_le_sub_nystrom {H H' : Matrix n n 𝕜}
    (hH : H.PosSemidef) (h : H ≤ H') (Ω : Matrix n l 𝕜) :
    H - nystrom H Ω ≤ H' - nystrom H' Ω := by
  have hH' : H'.PosSemidef := by simpa using hH.add (Matrix.le_iff.mp h)
  have hE := Matrix.le_iff.mp (hH.nystrom_le Ω)
  have hE' := Matrix.le_iff.mp (hH'.nystrom_le Ω)
  rw [hE.isHermitian.le_iff_re_quadForm_le hE'.isHermitian]
  intro x
  obtain ⟨y, hy⟩ := (hH'.isLeast_re_quadForm_sub_mulVec Ω x).1
  rw [← hy]
  exact ((hH.isLeast_re_quadForm_sub_mulVec Ω x).2 ⟨y, rfl⟩).trans
    (re_quadForm_le_re_quadForm_of_le h _)

/-- The real part of the quadratic form of a real combination of matrices is the combination of the
real parts. -/
private theorem re_quadForm_sum_smul {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (M : ι → Matrix n n 𝕜) (z : n → 𝕜) :
    RCLike.re (quadForm (∑ i ∈ s, w i • M i) z) = ∑ i ∈ s, w i * RCLike.re (quadForm (M i) z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, quadForm_zero_left, map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, quadForm_add_left, map_add, ih,
      quadForm_def, quadForm_def, Matrix.smul_mulVec, dotProduct_smul, RCLike.smul_re]

/-- **Concavity of the Schur complement** $\mathbf{H} \mapsto \mathbf{H}/\mathbf{\Omega}$, as
superadditivity with nonnegative weights: for positive semidefinite $\mathbf{H}_i$ and $w_i \ge 0$,
$$\sum_i w_i (\mathbf{H}_i/\mathbf{\Omega}) \preceq
\Bigl(\sum_i w_i \mathbf{H}_i\Bigr)/\mathbf{\Omega}\,.$$
Weights summing to one give concavity, equal weights the group average of a symmetrisation.
[EpperlyWebber2026, Fact 6.1(c)]; there with weights summing to one.
Result: schur-complement-concave -/
theorem sum_smul_sub_nystrom_le {ι : Type*} (s : Finset ι) {H : ι → Matrix n n 𝕜} {w : ι → ℝ}
    (hH : ∀ i ∈ s, (H i).PosSemidef) (hw : ∀ i ∈ s, 0 ≤ w i) (Ω : Matrix n l 𝕜) :
    ∑ i ∈ s, w i • (H i - nystrom (H i) Ω) ≤
      (∑ i ∈ s, w i • H i) - nystrom (∑ i ∈ s, w i • H i) Ω := by
  have hG : (∑ i ∈ s, w i • H i).PosSemidef :=
    Matrix.posSemidef_sum s fun i hi => (hH i hi).smul (hw i hi)
  have hL : (∑ i ∈ s, w i • (H i - nystrom (H i) Ω)).PosSemidef :=
    Matrix.posSemidef_sum s fun i hi =>
      (Matrix.le_iff.mp ((hH i hi).nystrom_le Ω)).smul (hw i hi)
  have hR := Matrix.le_iff.mp (hG.nystrom_le Ω)
  rw [hL.isHermitian.le_iff_re_quadForm_le hR.isHermitian]
  intro x
  obtain ⟨y, hy⟩ := (hG.isLeast_re_quadForm_sub_mulVec Ω x).1
  rw [← hy]
  change _ ≤ RCLike.re (quadForm (∑ i ∈ s, w i • H i) (x - Ω *ᵥ y))
  rw [re_quadForm_sum_smul, re_quadForm_sum_smul]
  refine Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ?_ (hw i hi)
  exact ((hH i hi).isLeast_re_quadForm_sub_mulVec Ω x).2 ⟨y, rfl⟩

/-- **More samples, better approximation**: for positive semidefinite $\mathbf{H}$ the Nyström
approximation is monotone in $\operatorname{range}\mathbf{\Omega}$, that is
$$\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega}) \preceq
\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega}')$$
when
$\operatorname{range}\mathbf{\Omega} \subseteq \operatorname{range}\mathbf{\Omega}'$.
[MartinssonTropp2020, §14.2]; there through the square-root form. -/
theorem _root_.Matrix.PosSemidef.nystrom_le_nystrom_of_range_le [Fintype q] {H : Matrix n n 𝕜}
    (hH : H.PosSemidef) {Ω : Matrix n l 𝕜} {Ω' : Matrix n q 𝕜}
    (h : LinearMap.range Ω.mulVecLin ≤ LinearMap.range Ω'.mulVecLin) :
    nystrom H Ω ≤ nystrom H Ω' := by
  classical
  rw [hH.nystrom_eq, hH.nystrom_eq]
  have hR : (CFC.sqrt H)ᴴ = CFC.sqrt H :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg H)).isHermitian.eq
  obtain ⟨C, hC⟩ := range_mulVecLin_le_iff_exists_mul.mp h
  have hP : rangeProjector (CFC.sqrt H * Ω) ≤ rangeProjector (CFC.sqrt H * Ω') :=
    rangeProjector_mono (range_mulVecLin_le_iff_exists_mul.mpr
      ⟨C, by rw [Matrix.mul_assoc, ← hC]⟩)
  have := conjTranspose_mul_mul_le_conjTranspose_mul_mul hP (CFC.sqrt H)
  rwa [hR] at this

/-- **Nyström helps**, singular-value form: for positive semidefinite $\mathbf{H}$,
$$\sigma_k(\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})) \le
\sigma_k((\mathbf{I} - \mathbf{P}_{\mathbf{\Omega}})\mathbf{H})$$
at every index $k$: the Nyström error is at most the error of projecting $\mathbf{H}$ onto the
orthogonal complement of the test space. At $\mathbf{\Omega} = \mathbf{H}\mathbf{\Omega}_0$ this
compares Nyström from the sample $\mathbf{H}\mathbf{\Omega}_0$ with the randomized SVD of
$\mathbf{H}$ (`NLAlib.sub_rsvd`).
[TroppWebber2023, Lemma 5.2]; there for unitarily invariant norms and by a block computation, here
basis-free through
$$\mathbf{H}/\mathbf{\Omega} \preceq (\mathbf{I} - \mathbf{P}_{\mathbf{\Omega}})\mathbf{H}
(\mathbf{I} - \mathbf{P}_{\mathbf{\Omega}})\,.$$
Result: nystrom-helps -/
theorem _root_.Matrix.PosSemidef.singularValues_sub_nystrom_le [DecidableEq n]
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) (k : ℕ) :
    singularValues (H - nystrom H Ω) k ≤ singularValues ((1 - rangeProjector Ω) * H) k := by
  have hR : IsStarProjection (1 - rangeProjector Ω) := (isStarProjection_rangeProjector Ω).one_sub
  have hE : (H - nystrom H Ω).PosSemidef := Matrix.le_iff.mp (hH.nystrom_le Ω)
  have hRHR : ((1 - rangeProjector Ω) * H * (1 - rangeProjector Ω)).PosSemidef := by
    have := hH.conjTranspose_mul_mul_same (1 - rangeProjector Ω)
    rwa [hR.conjTranspose_eq] at this
  have hle : H - nystrom H Ω ≤ (1 - rangeProjector Ω) * H * (1 - rangeProjector Ω) := by
    rw [hE.isHermitian.le_iff_re_quadForm_le hRHR.isHermitian]
    intro x
    have hmin := (hH.isLeast_re_quadForm_sub_mulVec Ω x).2 ⟨pinv Ω *ᵥ x, rfl⟩
    have e : x - Ω *ᵥ (pinv Ω *ᵥ x) = (1 - rangeProjector Ω) *ᵥ x := by
      rw [Matrix.mulVec_mulVec, mul_pinv, Matrix.sub_mulVec, Matrix.one_mulVec]
    have e2 : quadForm ((1 - rangeProjector Ω) * H * (1 - rangeProjector Ω)) x =
        quadForm H ((1 - rangeProjector Ω) *ᵥ x) := by
      have := quadForm_conjTranspose_mul_mul H (1 - rangeProjector Ω) x
      rwa [hR.conjTranspose_eq] at this
    rw [e2, ← e]
    exact hmin
  calc singularValues (H - nystrom H Ω) k = eigenvalue (H - nystrom H Ω) k := by
        rw [hE.singularValues_eq_eigenvalue]
    _ ≤ eigenvalue ((1 - rangeProjector Ω) * H * (1 - rangeProjector Ω)) k :=
        eigenvalue_le_eigenvalue_of_le hle hE.isHermitian k
    _ = singularValues ((1 - rangeProjector Ω) * H * (1 - rangeProjector Ω)) k := by
        rw [hRHR.singularValues_eq_eigenvalue]
    _ ≤ singularValues ((1 - rangeProjector Ω) * H) k := by
        rw [← singularValues_conjTranspose ((1 - rangeProjector Ω) * H * (1 - rangeProjector Ω)),
          Matrix.conjTranspose_mul, hR.conjTranspose_eq,
          ← singularValues_conjTranspose ((1 - rangeProjector Ω) * H)]
        exact hR.singularValues_mul_le _ k

/-- **Nyström does not increase any singular value**: for positive semidefinite $\mathbf{H}$,
$\sigma_i(\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})) \le \sigma_i(\mathbf{H})$ at every index
$i$,
since $\mathbf{0} \preceq \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega}) \preceq \mathbf{H}$. It is
the
domination hypothesis of the constant-one truncation lemma. False for Hermitian $\mathbf{H}$ that
is not positive semidefinite, where $\|\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_2$ can be
unbounded.
[MartinssonTropp2020, §14.3]; [EpperlyWebber2026, Fact 6.1(a)]; there the order
$\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega}) \preceq \mathbf{H}$, here its singular-value form. -/
theorem _root_.Matrix.PosSemidef.singularValues_nystrom_le {H : Matrix n n 𝕜} (hH : H.PosSemidef)
    (Ω : Matrix n l 𝕜) (i : ℕ) : singularValues (nystrom H Ω) i ≤ singularValues H i := by
  rw [(hH.nystrom Ω).singularValues_eq_eigenvalue, hH.singularValues_eq_eigenvalue]
  exact eigenvalue_le_eigenvalue_of_le (hH.nystrom_le Ω) (hH.nystrom Ω).isHermitian i

/-- **Nyström helps** in every unitarily invariant norm: for positive semidefinite $\mathbf{H}$,
$$\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\|_{\Phi} \le
\|(\mathbf{I} - \mathbf{P}_{\mathbf{\Omega}})\mathbf{H}\|_{\Phi}\,.$$
[TroppWebber2023, Lemma 5.2].
Result: nystrom-helps -/
theorem SymmetricGauge.matrixNorm_sub_nystrom_le [DecidableEq n] (Φ : SymmetricGauge)
    {H : Matrix n n 𝕜} (hH : H.PosSemidef) (Ω : Matrix n l 𝕜) :
    Φ.matrixNorm (H - nystrom H Ω) ≤ Φ.matrixNorm ((1 - rangeProjector Ω) * H) :=
  Φ.matrixNorm_le_of_singularValues_le (hH.singularValues_sub_nystrom_le Ω)

/-- **Truncated Nyström stays below the matrix**: for positive semidefinite $\mathbf{H}$,
$\llbracket\mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})\rrbracket_k \preceq \mathbf{H}$, so the
trace of
the error is its nuclear norm.
[MartinssonTropp2020, §14.3]; there the positive semidefiniteness of the approximation, here the
order. -/
theorem _root_.Matrix.PosSemidef.truncatedSVD_nystrom_le {H : Matrix n n 𝕜} (hH : H.PosSemidef)
    (Ω : Matrix n l 𝕜) (k : ℕ) : truncatedSVD (nystrom H Ω) k ≤ H :=
  ((hH.nystrom Ω).truncatedSVD_le k).trans (hH.nystrom_le Ω)

end NLAlib
