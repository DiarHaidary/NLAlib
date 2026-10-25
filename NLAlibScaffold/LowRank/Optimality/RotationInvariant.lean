/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.GeneralizedNystrom
public import NLAlib.LowRank.Gaussian.RotationInvariant
public import NLAlibScaffold.LowRank.Gaussian.RotationInvariantFactor

/-!
# Epperly and Webber's factors are sharp for rotation-invariant test matrices

For a test matrix with a left unitarily invariant law and full column rank almost surely
(Gaussian, Haar, ...), the library proves Epperly and Webber's sharp upper bounds: Nyström and the
randomized SVD with the factor <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$ over matrices of rank at most $r$, and
generalized Nyström with that factor times the co-range completion factor. This file shows the
factors cannot be lowered: for every constant below the factor some matrix of rank $r$ has a
larger expected error. The instance is $\operatorname{diag}(a\mathbf{I}_q, \mathbf{I}_{r-q},
\mathbf{0})$
for large $a$
(`NLAlib.tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant`).
These are Epperly and Webber's Theorems 3.3, 3.6(b) and 4.2(b) for rotation-invariant laws; their
versions for an arbitrary full-rank law (an extra Haar rotation of the instance) are deferred
(design note, §4). Real. Design: `docs/design/LowRank-EstimatorLowerBounds.md` §3.3. Proofs
deferred.

## Main results

* `NLAlib.exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant`: Nyström.
* `NLAlib.exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant`: the randomized SVD.
* generalized Nyström,
  [Gaussian co-range](https://nla-lib.org/explore/#d/NLAlib.exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix)
  and
  [Haar co-range](https://nla-lib.org/explore/#d/NLAlib.exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n l p : Type*} [Fintype m]
  [Fintype n] [Fintype l] [Fintype p] {X : Ω → Matrix n l ℝ} {Ψ : Ω → Matrix m p ℝ}
  [DecidableEq n] {ν : Measure (Matrix n l ℝ)} [IsProbabilityMeasure ν]
  [IsLeftUnitarilyInvariant ν]

/-- The two-level diagonal $\operatorname{diag}(a\mathbf{I}_q, \mathbf{I}_d)$ of the hard
instance. -/
private abbrev twoLevel (q d : ℕ) (a : ℝ) : Matrix (Fin q ⊕ Fin d) (Fin q ⊕ Fin d) ℝ :=
  Matrix.fromBlocks (a • (1 : Matrix (Fin q) (Fin q) ℝ)) 0 0
    ((1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ))

omit [Fintype n] [DecidableEq n] in
/-- The two-level block diagonal as a diagonal matrix. -/
private theorem twoLevel_eq_diagonal (q d : ℕ) (a : ℝ) :
    twoLevel q d a = Matrix.diagonal (Sum.elim (fun _ => a) fun _ => 1) := by
  rw [twoLevel, Matrix.smul_one_eq_diagonal, Matrix.smul_one_eq_diagonal,
    Matrix.fromBlocks_diagonal]

omit [Fintype m] [Fintype l] [Fintype p] [DecidableEq n] in
/-- The hard instance $\mathbf{V}\operatorname{diag}(a\mathbf{I}_q, \mathbf{I}_d)
\mathbf{V}^{\mathsf{H}}$ is positive semidefinite for $a \ge 0$. -/
private theorem posSemidef_twoLevel {q d : ℕ} (V : Matrix n (Fin q ⊕ Fin d) ℝ) {a : ℝ}
    (ha : 0 ≤ a) : (V * twoLevel q d a * Vᴴ).PosSemidef := by
  refine Matrix.PosSemidef.mul_mul_conjTranspose_same ?_ V
  rw [twoLevel_eq_diagonal]
  exact Matrix.PosSemidef.diagonal fun i => by cases i <;> simp [ha]

omit [Fintype m] [Fintype l] [Fintype p] [DecidableEq n] in
/-- The hard instance has rank $q + d$ for $a > 0$. -/
private theorem rank_twoLevel {q d : ℕ} {V : Matrix n (Fin q ⊕ Fin d) ℝ}
    (hV : HasOrthonormalCols V) {a : ℝ} (ha : 0 < a) : (V * twoLevel q d a * Vᴴ).rank = q + d := by
  have hDr : (twoLevel q d a).rank = q + d := by
    rw [twoLevel_eq_diagonal, Matrix.rank_diagonal,
      Fintype.card_congr (Equiv.subtypeUnivEquiv fun i => by cases i <;> simp [ha.ne']),
      Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
  refine le_antisymm (hDr ▸ (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _))
    ?_
  have h : Vᴴ * (V * twoLevel q d a * Vᴴ) * V = twoLevel q d a := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.one_mul,
      Matrix.mul_assoc, hV.conjTranspose_mul_self, Matrix.mul_one]
  calc q + d = (Vᴴ * (V * twoLevel q d a * Vᴴ) * V).rank := by rw [h, hDr]
    _ ≤ _ := (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_mul_le_right _ _)

omit [Fintype m] [Fintype l] [Fintype p] [DecidableEq n] in
/-- The optimal rank-$q$ trace error of the hard instance is at most $d$. -/
private theorem nuclearNorm_sub_truncatedSVD_twoLevel_le {q d : ℕ}
    {V : Matrix n (Fin q ⊕ Fin d) ℝ} (hV : HasOrthonormalCols V) (a : ℝ) :
    nuclearNorm (V * twoLevel q d a * Vᴴ - truncatedSVD (V * twoLevel q d a * Vᴴ) q) ≤ d := by
  set B := V * Matrix.fromBlocks (a • (1 : Matrix (Fin q) (Fin q) ℝ)) 0 0 0 * Vᴴ
  have hB : B.rank ≤ q := by
    refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal,
      Matrix.rank_diagonal]
    have hl : ∀ i : Fin q ⊕ Fin d, Sum.elim (fun _ => a) (fun _ => (0 : ℝ)) i ≠ 0 →
        i.isLeft := by
      rintro (i | i) hi <;> simp at hi ⊢
    refine (Fintype.card_le_of_injective (fun i => i.1.getLeft (hl i.1 i.2)) ?_).trans_eq
      (Fintype.card_fin q)
    rintro ⟨i | i, hi⟩ ⟨j | j, hj⟩ h <;>
      first | exact Subtype.ext (congrArg Sum.inl h) | simp at hi hj
  have h := (lpGauge 1).matrixNorm_sub_truncatedSVD_le_of_rank_le (V * twoLevel q d a * Vᴴ) hB
  rw [lpGauge_one_matrixNorm, lpGauge_one_matrixNorm] at h
  refine h.trans (le_of_eq ?_)
  have hsub : V * twoLevel q d a * Vᴴ - B =
      V * Matrix.fromBlocks 0 0 0 ((1 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℝ)) * Vᴴ := by
    rw [← Matrix.sub_mul, ← Matrix.mul_sub, sub_eq_add_neg, Matrix.fromBlocks_neg,
      Matrix.fromBlocks_add]
    simp only [add_neg_cancel, neg_zero, add_zero]
  rw [hsub, hV.nuclearNorm_mul_conjTranspose_right, hV.nuclearNorm_mul_left,
    Matrix.PosSemidef.nuclearNorm_eq_re_trace ?_]
  · simp [Matrix.trace_fromBlocks]
  · rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_zero, Matrix.fromBlocks_diagonal]
    exact Matrix.PosSemidef.diagonal fun i => by cases i <;> simp

omit [Fintype m] [Fintype p] in
/-- The expected Nyström error on the hard instance is the Gaussian one on the diagonal. -/
private theorem integral_nuclearNorm_sub_nystrom_twoLevel (hX : HasLaw X ν μ)
    (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {q d : ℕ}
    {V : Matrix n (Fin q ⊕ Fin d) ℝ} (hV : HasOrthonormalCols V) {a : ℝ} (ha : 0 ≤ a) :
    ∫ ω, nuclearNorm (V * twoLevel q d a * Vᴴ - nystrom (V * twoLevel q d a * Vᴴ) (X ω)) ∂μ =
      ∫ G, nuclearNorm (twoLevel q d a - nystrom (twoLevel q d a) (Vᴴ * G))
        ∂(gaussianMatrix n l) := by
  obtain ⟨S, hS⟩ : ∃ S : Matrix n n ℝ, ∀ G : Matrix n l ℝ,
      nystrom (V * twoLevel q d a * Vᴴ) G = S * rangeProjector (S * G) * S :=
    ⟨_, (posSemidef_twoLevel V ha).nystrom_eq⟩
  have hg : Measurable fun P : Matrix n n ℝ => nuclearNorm (V * twoLevel q d a * Vᴴ - S * P * S) :=
    continuous_nuclearNorm.measurable.comp (measurable_const.sub
      ((measurable_const.matrix_mul measurable_id).matrix_mul measurable_const))
  rw [integral_eq_integral_gaussianMatrix_of_isLeftUnitarilyInvariant S hX hXr
    (f := fun Y => nuclearNorm (V * twoLevel q d a * Vᴴ - nystrom (V * twoLevel q d a * Vᴴ) Y))
    hg fun Y => by rw [hS]]
  refine integral_congr_ae (ae_of_all _ fun G => ?_)
  have h := nystrom_conjTranspose_mul_mul Vᴴ (twoLevel q d a) G
  rw [Matrix.conjTranspose_conjTranspose] at h
  simp only [h, ← Matrix.sub_mul, ← Matrix.mul_sub, hV.nuclearNorm_mul_conjTranspose_right,
    hV.nuclearNorm_mul_left]

/-- **Epperly and Webber's Nyström factor is sharp**: for a test matrix $\mathbf{X}$ with a left
unitarily invariant law and full column rank almost surely, $q + 2 \le \ell \le r \le n$ and every
$c$ below the factor, <!-- value rotationInvariantFactor r \ell q -->
$$c < \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is a positive semidefinite $\mathbf{H}$ of rank $r$ with
$$c\,\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_* <
\mathbb{E}\|\mathbf{H} - \mathsf{nystrom}(\mathbf{H}, \mathbf{X})\|_*\,.$$
The matching upper bound is
`Matrix.PosSemidef.integral_nuclearNorm_sub_nystrom_le_of_isLeftUnitarilyInvariant_of_rank_le`.
[EpperlyWebber2026, Theorem 3.6(b)]; there for every full-rank law (with a Haar rotation of the
instance), here for left unitarily invariant laws, which need none.
Proof: M, about 70 lines. Take $s = $ `Fin q`, $t = $ `Fin (r - q)`, an isometry
$\mathbf{V} \in \mathbb{R}^{n \times (s \oplus t)}$ (`exists_hasOrthonormalCols_range_eq` or a
selection matrix after `Fintype.equivFin`) and $\mathbf{H}_a =
\mathbf{V}\mathbf{D}_a\mathbf{V}^{\mathsf{H}}$,
$\mathbf{D}_a = \operatorname{diag}(a\mathbf{I}_s, \mathbf{I}_t)$. Then
$\mathsf{nystrom}(\mathbf{H}_a, \mathbf{X}) = \mathbf{V}\mathsf{nystrom}(\mathbf{D}_a,
\mathbf{V}^{\mathsf{H}}\mathbf{X})\mathbf{V}^{\mathsf{H}}$ (`nystrom_conjTranspose_mul_mul`), the
trace
norm is unchanged, $\mathbf{V}^{\mathsf{H}}\mathbf{X}$ has a left unitarily invariant law (extend an
orthogonal map of $s \oplus t$ to $n$) and full column rank a.s. (through the polar factor,
`ae_rank_mul_eq_min_of_hasLaw_haarFrame`). The limit
`tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant` at $b = 1$ and
$\|\mathbf{H}_a - \llbracket\mathbf{H}_a\rrbracket_q\|_* = \lvert t\rvert > 0$ for $a \ge 1$ give
$a$ with the strict inequality (`Filter.Tendsto.eventually_gt_atTop`-type, `eventually_ge_atTop`);
$\operatorname{rank}\mathbf{H}_a = r$ for $a > 0$.
Result: randomized-nystrom-lower-bound -/
theorem exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrn : r ≤ Fintype.card n) {c : ℝ}
    (hc : c < rotationInvariantFactor r (Fintype.card l) q) :
    ∃ H : Matrix n n ℝ, H.PosSemidef ∧ H.rank = r ∧
      c * nuclearNorm (H - truncatedSVD H q) < ∫ ω, nuclearNorm (H - nystrom H (X ω)) ∂μ := by
  classical
  set d := r - q with hd_def
  have hd : q + d = r := by omega
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  obtain ⟨V, hV⟩ := exists_hasOrthonormalCols_of_card_le (n := n) (p := Fin q ⊕ Fin d) ℝ
    (by simp only [Fintype.card_sum, Fintype.card_fin]; omega)
  have hY : HasLaw (fun G : Matrix n l ℝ => Vᴴ * G) (gaussianMatrix (Fin q ⊕ Fin d) l)
      (gaussianMatrix n l) :=
    hasLaw_const_mul_of_hasLaw_gaussianMatrix HasLaw.id
      (by rwa [Matrix.conjTranspose_conjTranspose])
  have hYr : ∀ᵐ G ∂(gaussianMatrix n l), Function.Injective (Vᴴ * G).mulVec := by
    filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hY] with G hG
    rw [mulVec_injective_iff_rank_eq, hG, Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]
    exact min_eq_right (by omega)
  have hlim := tendsto_integral_nuclearNorm_fromBlocks_sub_nystrom_of_isLeftUnitarilyInvariant hY
    hYr (by simp only [Fintype.card_fin]; exact hq) zero_le_one
  simp only [Fintype.card_fin, hd, one_mul] at hlim
  rcases lt_or_ge c 0 with hc0 | hc0
  · refine ⟨V * twoLevel q d 1 * Vᴴ, posSemidef_twoLevel V zero_le_one,
      hd ▸ rank_twoLevel hV one_pos, ?_⟩
    have hpos : 0 < nuclearNorm (V * twoLevel q d 1 * Vᴴ -
        truncatedSVD (V * twoLevel q d 1 * Vᴴ) q) := by
      refine (nuclearNorm_nonneg _).lt_of_ne fun h => ?_
      have h' := sub_eq_zero.mp (nuclearNorm_eq_zero_iff.mp h.symm)
      have := rank_truncatedSVD_le (V * twoLevel q d 1 * Vᴴ) q
      rw [← h', rank_twoLevel hV one_pos] at this
      omega
    exact (mul_neg_of_neg_of_pos hc0 hpos).trans_le
      (integral_nonneg fun ω => nuclearNorm_nonneg _)
  · obtain ⟨a, ha, ha1⟩ := ((hlim.eventually (lt_mem_nhds (mul_lt_mul_of_pos_right hc hd0))).and
      (Filter.eventually_ge_atTop 1)).exists
    refine ⟨V * twoLevel q d a * Vᴴ, posSemidef_twoLevel V (by linarith),
      hd ▸ rank_twoLevel hV (by linarith), ?_⟩
    rw [integral_nuclearNorm_sub_nystrom_twoLevel hX hXr hV (by linarith)]
    exact (mul_le_mul_of_nonneg_left (nuclearNorm_sub_truncatedSVD_twoLevel_le hV a) hc0).trans_lt
      ha

/-- **Epperly and Webber's randomized SVD factor is sharp**: for a test matrix $\mathbf{X}$ with a
left unitarily invariant law and full column rank almost surely, $q + 2 \le \ell \le r$,
$r \le \min(m, n)$ and every $c$ below the factor, <!-- value rotationInvariantFactor r \ell q -->
$$c < \frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{rsvd}(\mathbf{A}, \mathbf{X})\|_{\mathsf{F}}^2\,.$$
The matching upper bound is
`NLAlib.integral_frobNorm_sub_rsvd_sq_le_of_isLeftUnitarilyInvariant_of_rank_le`.
[EpperlyWebber2026, Theorem 3.3]; there for every full-rank law, here for left unitarily
invariant laws.
Proof: S, about 30 lines. The Gram correspondence: for $\mathbf{H}$ from
`exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant` write
$\mathbf{H} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ with $\mathbf{A} \in \mathbb{R}^{m \times n}$ of
rank $r$
($r \le m$: an isometry $\mathbb{R}^{r} \to \mathbb{R}^m$ times $\mathbf{H}^{1/2}$ compressed to its
range, `CFC.sqrt`, `exists_hasOrthonormalCols_range_eq`); then
`nuclearNorm_conjTranspose_mul_self_sub_nystrom` and
`nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD` turn both sides into the Frobenius ones.
Result: randomized-svd-lower-bound -/
theorem exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) {c : ℝ} (hc : c < rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 < ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
  obtain ⟨H, hH, hrank, hineq⟩ :=
    exists_lt_integral_nuclearNorm_sub_nystrom_of_isLeftUnitarilyInvariant hX hXr hq hlr hrn hc
  have hSH : (CFC.sqrt H)ᴴ * CFC.sqrt H = H := hH.conjTranspose_sqrt_mul_sqrt
  have hrS : (CFC.sqrt H).rank = r := by
    rw [← Matrix.rank_conjTranspose_mul_self, hSH, hrank]
  obtain ⟨Z, hZ, hZP⟩ :=
    (isStarProjection_rangeProjector (CFC.sqrt H)).exists_hasOrthonormalCols_mul_conjTranspose_eq
      (p := Fin r) (by rw [rank_rangeProjector, hrS, Fintype.card_fin])
  obtain ⟨J, hJ⟩ := exists_hasOrthonormalCols_of_card_le (p := Fin r) ℝ (by simpa using hrm)
  have hAH : (J * (Zᴴ * CFC.sqrt H))ᴴ * (J * (Zᴴ * CFC.sqrt H)) = H := by
    have hZZ : Z * Zᴴ * CFC.sqrt H = CFC.sqrt H := by
      rw [hZP, rangeProjector_mul_self]
    have hJJ : Jᴴ * J = 1 := hJ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Jᴴ J, hJJ, Matrix.one_mul, ← Matrix.mul_assoc Z, hZZ]
    exact hSH
  refine ⟨J * (Zᴴ * CFC.sqrt H), ?_, ?_⟩
  · rw [← Matrix.rank_conjTranspose_mul_self, hAH, hrank]
  · rw [← nuclearNorm_conjTranspose_mul_self_sub_truncatedSVD]
    simp only [← nuclearNorm_conjTranspose_mul_self_sub_nystrom]
    rw [hAH]
    exact hineq

-- A docstring line and the declaration name exceed 100 characters.
set_option linter.style.longLine false in
/-- **Epperly and Webber's generalized Nyström factor is sharp, Gaussian co-range**: for a test
matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely, an
independent standard Gaussian $\mathbf{\Psi}$ ($m \times p$), $q + 2 \le \ell \le r$,
$r \le \min(m, n)$, $\ell + 2 \le p$ and every $c$ below the factor, that
is <!-- value gaussianProjectionFactor \ell p --> <!-- value rotationInvariantFactor r \ell q -->
$$c < \Bigl(1 + \frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{X}, \mathbf{\Psi})\|_{\mathsf{F}}^2\,.$$
So generalized Nyström needs $k' + \ell = \Theta(q/\varepsilon^2)$ for relative error
$1 + \varepsilon$ (Epperly and Webber, §4.2). The matching upper bound is
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix_of_rank_le`.
[EpperlyWebber2026, Theorem 4.2(b)]; there for every full-rank pair of laws and an orthonormal
co-range, here for a left unitarily invariant range law and a Gaussian co-range ($\gamma = 1$).
Proof: S, about 30 lines. The identity
`integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix` (any law of
$\mathbf{X}$) with $\operatorname{rank}(\mathbf{A}\mathbf{X}) = \ell$ a.s. for
$\operatorname{rank}\mathbf{A} \ge \ell$
(polar factor and `ae_rank_mul_eq_min_of_hasLaw_haarFrame`) gives the factor
`gaussianProjectionFactor ℓ p` times the randomized SVD error; apply
`exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant` at
$c / (1 + \ell/(p - \ell - 1))$ (`one_le_gaussianProjectionFactor`).
Result: generalized-nystrom-lower-bound -/
theorem
    exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_gaussianMatrix
    (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hΨ : HasLaw Ψ (gaussianMatrix m p) μ) (hXΨ : IndepFun X Ψ μ) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (hlp : Fintype.card l + 2 ≤ Fintype.card p) {c : ℝ}
    (hc : c < gaussianProjectionFactor (Fintype.card l) (Fintype.card p) *
      rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 <
        ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ := by
  classical
  set g := gaussianProjectionFactor (Fintype.card l) (Fintype.card p) with hg_def
  have hg0 : 0 < g := zero_lt_one.trans_le (one_le_gaussianProjectionFactor hlp)
  have hc' : c / g < rotationInvariantFactor r (Fintype.card l) q := by
    rw [div_lt_iff₀ hg0, mul_comm]
    exact hc
  obtain ⟨A, hA, hlt⟩ :=
    exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant hX hXr hq hlr hrm hrn hc'
  have hrank : ∀ᵐ ω ∂μ, (A * X ω).rank = Fintype.card l := by
    filter_upwards [ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant A hX hXr] with ω hω
    rw [hω, hA, min_eq_right hlr]
  have hr : ∀ᵐ ω ∂μ, (A * X ω).rank + 2 ≤ Fintype.card p :=
    hrank.mono fun ω hω => by rw [hω]; exact hlp
  have heq : ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      g * ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
    rw [integral_frobNorm_sub_generalizedNystrom_sq_eq_integral_of_hasLaw_gaussianMatrix A
      hX.aemeasurable hΨ hXΨ hr, ← integral_const_mul]
    exact integral_congr_ae (hrank.mono fun ω hω => by
      change gaussianProjectionFactor (A * X ω).rank (Fintype.card p) * _ = g * _
      rw [hω])
  refine ⟨A, hA, ?_⟩
  rw [heq]
  have hcg : c * frobNorm (A - truncatedSVD A q) ^ 2 =
      g * (c / g * frobNorm (A - truncatedSVD A q) ^ 2) := by
    field_simp
  rw [hcg]
  exact mul_lt_mul_of_pos_left hlt hg0

-- A docstring line and the declaration name exceed 100 characters.
set_option linter.style.longLine false in
/-- **Epperly and Webber's generalized Nyström factor is sharp, random orthonormal co-range**: for
a test matrix $\mathbf{X}$ with a left unitarily invariant law and full column rank almost surely,
an independent $m \times p$ Haar frame $\mathbf{\Psi}$, $q + 2 \le \ell \le r$, $r \le \min(m, n)$,
$\ell + 2 \le p \le m$ and every $c$ below the
factor, <!-- value haarProjectionFactor m p \ell --> <!-- value rotationInvariantFactor r \ell q -->
$$c < \Bigl(1 + \frac{m - p}{m - \ell}\cdot\frac{\ell}{p - \ell - 1}\Bigr)
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,,$$
there is $\mathbf{A} \in \mathbb{R}^{m \times n}$ of rank $r$ with
$$c\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_q\|_{\mathsf{F}}^2 <
\mathbb{E}\|\mathbf{A} - \mathsf{gn}(\mathbf{A}, \mathbf{X}, \mathbf{\Psi})\|_{\mathsf{F}}^2\,.$$
The matching upper bound is
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_le_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame_of_rank_le`.
[EpperlyWebber2026, Theorem 4.2(b)]; there for every full-rank pair of laws, here for a left
unitarily invariant range law and a Haar co-range ($\gamma = (d - k)/(d - \ell)$ in their letters).
Proof: S, about 30 lines. As the Gaussian co-range version, with
`integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_haarFrame`'s conditional
form (`integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame` for a fixed range test
matrix, integrated) and `one_le_haarProjectionFactor`.
Result: generalized-nystrom-lower-bound -/
theorem
    exists_lt_integral_frobNorm_sub_generalizedNystrom_sq_of_isLeftUnitarilyInvariant_of_hasLaw_haarFrame
    [DecidableEq p] (hX : HasLaw X ν μ) (hXr : ∀ᵐ ω ∂μ, Function.Injective (X ω).mulVec)
    (hΨ : HasLaw Ψ (haarFrame m p) μ) (hXΨ : IndepFun X Ψ μ) {r q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) (hlr : Fintype.card l ≤ r) (hrm : r ≤ Fintype.card m)
    (hrn : r ≤ Fintype.card n) (hlp : Fintype.card l + 2 ≤ Fintype.card p)
    (hpm : Fintype.card p ≤ Fintype.card m) {c : ℝ}
    (hc : c < haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
      rotationInvariantFactor r (Fintype.card l) q) :
    ∃ A : Matrix m n ℝ, A.rank = r ∧
      c * frobNorm (A - truncatedSVD A q) ^ 2 <
        ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ := by
  have := hΨ.isProbabilityMeasure
  have hf := one_le_haarProjectionFactor hlp hpm
  obtain ⟨A, hA, hlt⟩ := exists_lt_integral_frobNorm_sub_rsvd_sq_of_isLeftUnitarilyInvariant
    hX hXr hq hlr hrm hrn (c := c / haarProjectionFactor (Fintype.card m) (Fintype.card p)
      (Fintype.card l)) (by rwa [div_lt_iff₀' (by linarith)])
  refine ⟨A, hA, ?_⟩
  have hk : ∀ᵐ ω ∂μ, (A * X ω).rank = Fintype.card l :=
    (ae_rank_mul_eq_min_of_isLeftUnitarilyInvariant A hX hXr).mono fun ω hω => by
      rw [hω, hA, min_eq_right hlr]
  have hid : HasLaw (fun ψ : Matrix m p ℝ => ψ) (haarFrame m p) (haarFrame m p) := HasLaw.id
  -- The Haar identity, integrated over the range test matrix: the fixed-`X` form inside.
  have hlin := hXΨ.lintegral_ofReal_comp_eq_lintegral_ofReal_integral hX.aemeasurable hΨ
    (F := fun q : Matrix n l ℝ × Matrix m p ℝ => frobNorm (A - generalizedNystrom A q.1 q.2) ^ 2)
    ((continuous_frobNorm.measurable.comp
      (measurable_const.sub (measurable_generalizedNystrom A))).pow_const 2)
    (fun _ => sq_nonneg _) (hk.mono fun ω hω =>
      integrable_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame A aemeasurable_const hid
        hpm (indepFun_const_left _ _) (ae_of_all _ fun _ => hω ▸ hlp))
  have hgm : AEStronglyMeasurable
      (fun ω => frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2) μ :=
    (((continuous_frobNorm.measurable.comp (measurable_const.sub
      (measurable_generalizedNystrom A))).pow_const 2).comp_aemeasurable
        (hX.aemeasurable.prodMk hΨ.aemeasurable)).aestronglyMeasurable
  have hR := (integrable_frobNorm_sub_rsvd_sq A hX.aemeasurable).const_mul
    (haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l))
  have heq : ∫ ω, frobNorm (A - generalizedNystrom A (X ω) (Ψ ω)) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) (Fintype.card l) *
        ∫ ω, frobNorm (A - rsvd A (X ω)) ^ 2 ∂μ := by
    rw [← integral_const_mul,
      integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ => sq_nonneg _) hgm,
      integral_eq_lintegral_of_nonneg_ae
        (ae_of_all _ fun _ => mul_nonneg (by linarith) (sq_nonneg _))
        hR.aestronglyMeasurable, hlin]
    refine congrArg ENNReal.toReal (lintegral_congr_ae (hk.mono fun ω hω => ?_))
    refine congrArg ENNReal.ofReal ?_
    rw [← hω]
    exact integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_haarFrame A (X ω) hid hpm
      (hω ▸ hlp)
  rw [heq]
  rw [div_mul_eq_mul_div, div_lt_iff₀' (by linarith)] at hlt
  exact hlt

end NLAlib
