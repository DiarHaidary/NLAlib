/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowerBounds.LowRank.FewPasses
public import NLAlibScaffold.LowerBounds.QueryModel.Yao
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlibScaffold.LowerBounds.QueryModel.HiddenRotation
public import NLAlibScaffold.Polynomial.Interpolation.DividedDifference

/-!
# Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ products (scaffold)

Every randomized algorithm that makes its matrix–vector products in two passes (two blocks, the
second chosen from the responses to the first) and returns a rank-$k$ approximation within
$(1 + \varepsilon)$ of the best in Frobenius norm needs more than $k/(6400\varepsilon)$ products in
the worst case; one pass is a special case, and in spectral norm two passes need a number of
products proportional to the dimension. Randomized SVD meets the Frobenius rate with two passes,
so it is rate-optimal among two-pass algorithms. Stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.6; research note OP5
(`~/nlalib-harness/reports/OP5-TwoPassMinimax.md`, Theorems A and C, Corollary B).

The hard instance is $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$, $\mathbf{U}$ Haar,
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$
(`NLAlib.equispacedLevelSpectrum k m 2`). Three steps: the error is at least the optimum
$14m$ plus $7(k - t)$, $t$ the head mass captured by the output range; by the Krylov coupling the
rotated output range lies in $\mathcal{K}_3(\mathbf{D}, \mathbf{G})$ for a Gaussian $\mathbf{G}$
with $q + k$ columns; a vector of that space is $\mathbf{G}_\lambda\mathbf{p}(\lambda)$ on level
$\lambda$ with $\deg\mathbf{p} \le 2$, and $\mathbf{p}(4) = \mathbf{p}(1) - 3\mathbf{p}(2) +
3\mathbf{p}(3)$, so the head part is small unless $q + k$ is of the order of $m$.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`,
  `NLAlib.HasOrthonormalCols.singularValues_mul_diagonal_mul_card`: the optimum.
* `NLAlib.le_frobNorm_diagonal_sub_mul_sq`, `NLAlib.le_specNorm_diagonal_sub_mul_sq`: error from
  head capture.
* `NLAlib.mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace`: the interpolation bound.
* `NLAlib.measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix`: Gaussian
  head capture.
* one deterministic two-pass algorithm, Frobenius and spectral:
  `NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
  `NLAlib.QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
* `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`: randomized, worst case.
* `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`,
  `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one`,
  `NLAlib.lt_of_forall_le_measureReal_specNorm_sub_mul_le`: the query counts.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k m : Type*} [Fintype k]
  [Fintype m] [DecidableEq k] [DecidableEq m]

/-- **The optimum of the two-pass hard instance**: for orthogonal $\mathbf{U}$ and
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$,
$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2 = 14\lvert m \rvert$.
Proof: `NLAlib.frobNorm_sub_truncatedSVD_sq`; the singular values of $\mathbf{A}$ are those of the
diagonal (unitary invariance) sorted, $4$ ($\lvert k \rvert$ times), then $3, 2, 1$
($\lvert m \rvert$ times each), so the tail sum is $(9 + 4 + 1)\lvert m \rvert$. M, about 50
lines. -/
theorem HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U) :
    frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
        truncatedSVD (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ)
          (Fintype.card k)) ^ 2 = 14 * Fintype.card m := by
  sorry

/-- The kernel of a coordinate restriction has dimension at least the number of the other
coordinates. -/
private theorem card_le_finrank_ker_funLeft {ι τ : Type*} [Fintype ι] [Fintype τ] (f : τ → ι) :
    Fintype.card ι ≤
      Module.finrank ℝ (LinearMap.ker (LinearMap.funLeft ℝ ℝ f)) + Fintype.card τ := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (LinearMap.funLeft ℝ ℝ f)
  have h2 := Submodule.finrank_le (LinearMap.range (LinearMap.funLeft ℝ ℝ f))
  rw [Module.finrank_fintype_fun_eq_card] at h1 h2
  omega

/-- The squared norm of a diagonal action is a weighted sum of squares. -/
private theorem sq_norm_diagonal_mulVec {n : Type*} [Fintype n] [DecidableEq n] (d x : n → ℝ) :
    ‖WithLp.toLp 2 (Matrix.diagonal d *ᵥ x)‖ ^ 2 = ∑ i, (d i * x i) ^ 2 := by
  rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq]
  simp only [Matrix.mulVec_diagonal]

/-- The $(k + 1)$-st singular value of the two-pass hard instance is $3$: for orthogonal
$\mathbf{U}$ and $m$ nonempty, $\sigma_k(\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}) = 3$
(indices from $0$).
Proof: as `NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`, the sorted
singular values. M, about 30 lines. -/
theorem HasOrthonormalCols.singularValues_mul_diagonal_mul_card [Nonempty m]
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U) :
    singularValues (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ) (Fintype.card k) =
      3 := by
  rw [Matrix.mul_assoc, hU.singularValues_mul_left, hU.singularValues_mul_conjTranspose_right]
  apply le_antisymm
  · -- upper bound: the codimension-`k` subspace of tail coordinates
    refine singularValues_le_of_forall_mem _
      (LinearMap.ker (LinearMap.funLeft ℝ ℝ (Sum.inl : k → k ⊕ (Fin 3 × m)))) ?_ (by norm_num) ?_
    · exact card_le_finrank_ker_funLeft (Sum.inl : k → k ⊕ (Fin 3 × m))
    intro x hx
    have hx' : ∀ a, x (Sum.inl a) = 0 := fun a => congrFun (LinearMap.mem_ker.mp hx) a
    apply (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp
    rw [mul_pow, sq_norm_diagonal_mulVec, EuclideanSpace.norm_toLp_sq_eq_sum_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases i with a | ⟨l, j⟩
    · simp [hx' a]
    · have hl : ((l : ℕ) : ℝ) ≤ 2 := by exact_mod_cast (by have := l.isLt; omega : (l : ℕ) ≤ 2)
      have h0 : (0 : ℝ) ≤ (l : ℕ) + 1 := by positivity
      have h3 : ((l : ℕ) : ℝ) + 1 ≤ 3 := by linarith
      simp only [equispacedLevelSpectrum, Sum.elim_inr]
      nlinarith [mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h3 2)
        (sq_nonneg (x (Sum.inr (l, j))))]
  · -- lower bound: the subspace killing the levels 0 and 1 has dimension above `k`
    refine le_singularValues_of_forall_mem _ (LinearMap.ker (LinearMap.funLeft ℝ ℝ
      (fun p : Fin 2 × m => (Sum.inr (Fin.castSucc p.1, p.2) : k ⊕ (Fin 3 × m))))) ?_ ?_
    · have := card_le_finrank_ker_funLeft
        (fun p : Fin 2 × m => (Sum.inr (Fin.castSucc p.1, p.2) : k ⊕ (Fin 3 × m)))
      have hm : 0 < Fintype.card m := Fintype.card_pos
      simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin] at this ⊢
      omega
    intro x hx
    have hx' : ∀ (a : Fin 2) (j : m), x (Sum.inr (Fin.castSucc a, j)) = 0 :=
      fun a j => congrFun (LinearMap.mem_ker.mp hx) (a, j)
    apply (pow_le_pow_iff_left₀ (by positivity) (norm_nonneg _) two_ne_zero).mp
    rw [mul_pow, sq_norm_diagonal_mulVec, EuclideanSpace.norm_toLp_sq_eq_sum_sq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rcases i with a | ⟨l, j⟩
    · have hd : equispacedLevelSpectrum k m 2 (Sum.inl a) = 4 := by
        simp [equispacedLevelSpectrum]; norm_num
      rw [hd]
      nlinarith [sq_nonneg (x (Sum.inl a))]
    · by_cases hl : (l : ℕ) < 2
      · have h0 : x (Sum.inr (l, j)) = 0 := by
          have := hx' ⟨l, hl⟩ j
          rwa [show Fin.castSucc (⟨l, hl⟩ : Fin 2) = l from Fin.ext rfl] at this
        simp [h0]
      · have hl2 : ((l : ℕ) : ℝ) = 2 := by
          have := l.isLt
          exact_mod_cast (by omega : (l : ℕ) = 2)
        simp only [equispacedLevelSpectrum, Sum.elim_inr, hl2]
        nlinarith [sq_nonneg (x (Sum.inr (l, j)))]

/-- A real star projection is symmetric. -/
private lemma isStarProjection_entry_symm {n : Type*} [Fintype n]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) (i j : n) : P i j = P j i := by
  have h := congrFun (congrFun hP.isSelfAdjoint j) i
  simpa [Matrix.star_apply] using h

/-- The squared norm of the `j`-th column of a real star projection is its `(j, j)` entry. -/
private lemma norm_sq_mulVec_single_eq {n : Type*} [Fintype n] [DecidableEq n]
    {P : Matrix n n ℝ} (hP : IsStarProjection P) (j : n) :
    ‖WithLp.toLp 2 (P *ᵥ Pi.single j 1)‖ ^ 2 = P j j := by
  have h := congrFun (congrFun hP.mul_self j) j
  rw [Matrix.mul_apply] at h
  rw [EuclideanSpace.norm_sq_eq, ← h]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec_single_one, Matrix.col_apply, Real.norm_eq_abs, sq_abs]
  rw [isStarProjection_entry_symm hP j i]
  ring

/-- **Frobenius error from head capture**: for every $\mathbf{W} \in \mathbb{R}^{n \times k}$ and
$\mathbf{M} \in \mathbb{R}^{k \times n}$, $n = k \oplus (\{0, 1, 2\} \times m)$ and
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \ge 14\lvert m \rvert + 7\bigl(\lvert k
\rvert - t\bigr) \,, \qquad t = \sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \,,$$
$t$ the head mass captured by the range of $\mathbf{W}$.
OP5, Step 1 (eq. (1)).
Proof: $(\mathbf{I} - \mathbf{P}_{\mathbf{W}})(\mathbf{D} - \mathbf{W}\mathbf{M}) =
(\mathbf{I} - \mathbf{P}_{\mathbf{W}})\mathbf{D}$ (`NLAlib.rangeProjector_mul_self`), so the error
is at least $\|\mathbf{D}\|_{\mathsf{F}}^2 - \operatorname{tr}(\mathbf{P}_{\mathbf{W}}
\mathbf{D}^2)$; the diagonal of $\mathbf{P}_{\mathbf{W}}$ sums to its rank, at most $\lvert k
\rvert$ (`NLAlib.rank_rangeProjector`), and $d_i^2 \le 9$ off the head, so
$\operatorname{tr}(\mathbf{P}_{\mathbf{W}}\mathbf{D}^2) \le 16t + 9(\lvert k \rvert - t)$. M,
about 50 lines. -/
theorem le_frobNorm_diagonal_sub_mul_sq (W : Matrix (k ⊕ (Fin 3 × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin 3 × m)) ℝ) :
    14 * Fintype.card m + 7 * (Fintype.card k -
        ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) ≤
      frobNorm (Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M) ^ 2 := by
  set P := rangeProjector W with hPdef
  set Q : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ := 1 - P with hQdef
  set d := equispacedLevelSpectrum k m 2 with hd
  have hP : IsStarProjection P := isStarProjection_rangeProjector W
  have hQ : IsStarProjection Q := isStarProjection_one_sub_rangeProjector W
  -- Step 1: `Q (D - W M) = Q D` since `Q W = 0`, and `Q` contracts.
  have hcontr : frobNorm (Q * Matrix.diagonal d) ^ 2 ≤
      frobNorm (Matrix.diagonal d - W * M) ^ 2 := by
    have h : Q * Matrix.diagonal d = Q * (Matrix.diagonal d - W * M) := by
      have hQW : Q * W = 0 := by
        rw [hQdef, Matrix.sub_mul, Matrix.one_mul, rangeProjector_mul_self, sub_self]
      rw [Matrix.mul_sub, ← Matrix.mul_assoc, hQW, Matrix.zero_mul, sub_zero]
    rw [h]
    exact pow_le_pow_left₀ (frobNorm_nonneg _) (hQ.frobNorm_mul_le _) 2
  -- Step 2: `‖Q D‖_F² = ∑ d_j² Q_jj`, as `∑ᵢ Q_ij² = Q_jj`.
  have hcol : ∀ j, ∑ i, Q i j ^ 2 = Q j j := by
    intro j
    refine Eq.trans ?_ (congrFun (congrFun hQ.mul_self j) j)
    rw [Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [isStarProjection_entry_symm hQ j i]
    ring
  have hfrob : frobNorm (Q * Matrix.diagonal d) ^ 2 = ∑ j, d j ^ 2 * Q j j := by
    rw [frobNorm_sq_eq_sum_sq, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hcol j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mul_diagonal]
    ring
  have hQjj : ∀ j, Q j j = 1 - P j j := fun j => by rw [hQdef]; simp
  -- Step 3: `P_jj = ‖P e_j‖²` is nonnegative, and `∑ P_jj = rank P ≤ k`.
  have hPnn : ∀ j, 0 ≤ P j j := fun j => by rw [← norm_sq_mulVec_single_eq hP j]; positivity
  have ht : ∑ a : k, ‖WithLp.toLp 2 (P *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2 =
      ∑ a : k, P (Sum.inl a) (Sum.inl a) :=
    Finset.sum_congr rfl fun a _ => norm_sq_mulVec_single_eq hP _
  have htr : ∑ j, P j j ≤ Fintype.card k := by
    have h1 : ∑ j, P j j = P.trace := rfl
    have h2 : P.trace = (W.rank : ℝ) := trace_rangeProjector W
    have h3 : (W.rank : ℝ) ≤ Fintype.card k := by exact_mod_cast Matrix.rank_le_card_width W
    linarith
  rw [Fintype.sum_sum_type] at htr
  -- Step 4: split the head (`d = 4`) from the tail (`d = 1, 2, 3`, where `d² ≤ 9`).
  have hd_inl : ∀ a : k, d (Sum.inl a) = 4 := fun a => by
    simp [hd, equispacedLevelSpectrum]; norm_num
  have hd_inr : ∀ x : Fin 3 × m, d (Sum.inr x) = ((x.1 : ℕ) : ℝ) + 1 := fun x => by
    simp [hd, equispacedLevelSpectrum]
  have hB : ∑ x : Fin 3 × m, (((x.1 : ℕ) : ℝ) + 1) ^ 2 * P (Sum.inr x) (Sum.inr x) ≤
      9 * ∑ x : Fin 3 × m, P (Sum.inr x) (Sum.inr x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h3 : ((x.1 : ℕ) : ℝ) ≤ 2 := by exact_mod_cast Fin.is_le x.1
    have h0 : (0 : ℝ) ≤ ((x.1 : ℕ) : ℝ) := Nat.cast_nonneg _
    have h9 : (0 : ℝ) ≤ 9 - (((x.1 : ℕ) : ℝ) + 1) ^ 2 := by nlinarith
    nlinarith [mul_nonneg h9 (hPnn (Sum.inr x))]
  have hA : ∑ a : k, d (Sum.inl a) ^ 2 * Q (Sum.inl a) (Sum.inl a) =
      16 * Fintype.card k - 16 * ∑ a : k, P (Sum.inl a) (Sum.inl a) := by
    have h16 : ∀ a : k, d (Sum.inl a) ^ 2 * Q (Sum.inl a) (Sum.inl a) =
        16 - 16 * P (Sum.inl a) (Sum.inl a) := fun a => by
      rw [hd_inl, hQjj]; ring
    rw [Finset.sum_congr rfl fun a _ => h16 a, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hX : ∑ x : Fin 3 × m, (((x.1 : ℕ) : ℝ) + 1) ^ 2 = 14 * (Fintype.card m : ℝ) := by
    rw [Fintype.sum_prod_type]
    simp [Fin.sum_univ_three, Finset.sum_const, Finset.card_univ]
    ring
  have hBt : ∑ x : Fin 3 × m, d (Sum.inr x) ^ 2 * Q (Sum.inr x) (Sum.inr x) =
      14 * (Fintype.card m : ℝ) -
        ∑ x : Fin 3 × m, (((x.1 : ℕ) : ℝ) + 1) ^ 2 * P (Sum.inr x) (Sum.inr x) := by
    rw [← hX, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hd_inr, hQjj]
    ring
  have hmain : 14 * (Fintype.card m : ℝ) + 7 * (Fintype.card k -
      ∑ a : k, P (Sum.inl a) (Sum.inl a)) ≤ ∑ j, d j ^ 2 * Q j j := by
    rw [Fintype.sum_sum_type, hA, hBt]
    linarith
  rw [ht]
  linarith [hcontr, hfrob, hmain]

/-- **Spectral error from head capture**: with the notation of
`NLAlib.le_frobNorm_diagonal_sub_mul_sq` and $k$ nonempty,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_2^2 \ge
\frac{16(\lvert k \rvert - t)}{\lvert k \rvert} \,.$$
OP5, Step 1 (eq. (1')).
Proof: $\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_2 \ge \|(\mathbf{I} - \mathbf{P}_{\mathbf{W}})
\mathbf{D}\mathbf{P}_*\|_2 = 4\|(\mathbf{I} - \mathbf{P}_{\mathbf{W}})\mathbf{P}_*\|_2$, and the
spectral norm of a matrix of rank at most $\lvert k \rvert$ is at least its Frobenius norm over
$\sqrt{\lvert k \rvert}$ (`NLAlib.frobNorm_le_sqrt_rank_mul_specNorm` or the singular-value sum),
with $\|(\mathbf{I} - \mathbf{P}_{\mathbf{W}})\mathbf{P}_*\|_{\mathsf{F}}^2 = \lvert k \rvert - t$.
M, about 40 lines. -/
theorem le_specNorm_diagonal_sub_mul_sq [Nonempty k] (W : Matrix (k ⊕ (Fin 3 × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin 3 × m)) ℝ) :
    16 * (Fintype.card k -
        ∑ a : k, ‖WithLp.toLp 2 (rangeProjector W *ᵥ Pi.single (Sum.inl a) 1)‖ ^ 2) /
        Fintype.card k ≤
      specNorm (Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M) ^ 2 := by
  classical
  set P := rangeProjector W with hPdef
  have hP : IsStarProjection P := isStarProjection_rangeProjector W
  set X := Matrix.diagonal (equispacedLevelSpectrum k m 2) - W * M with hXdef
  set e : k → (k ⊕ (Fin 3 × m) → ℝ) := fun a => Pi.single (Sum.inl a) 1 with he
  have hnorm1 : ∀ a : k, ‖WithLp.toLp 2 (e a)‖ = 1 := by
    intro a
    simp [he]
  have hpy : ∀ a : k,
      ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ ^ 2 = 1 - ‖WithLp.toLp 2 (P *ᵥ e a)‖ ^ 2 := by
    intro a
    have h := hP.norm_toLp_sq_eq_add (e a)
    rw [hnorm1 a] at h
    linarith
  have hDe : ∀ a : k, Matrix.diagonal (equispacedLevelSpectrum k m 2) *ᵥ e a = (4 : ℝ) • e a := by
    intro a
    ext i
    rcases i with i | ⟨j, i⟩
    · by_cases h : i = a
      · subst h
        simp [he, equispacedLevelSpectrum, Matrix.mulVec_diagonal]
        norm_num
      · simp [he, equispacedLevelSpectrum, Matrix.mulVec_diagonal, h]
    · simp [he, equispacedLevelSpectrum, Matrix.mulVec_diagonal]
  have hPW : (1 - P) * W = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hPdef, rangeProjector_mul_self, sub_self]
  have hWM : (1 - P) * (W * M) = 0 := by rw [← Matrix.mul_assoc, hPW, Matrix.zero_mul]
  have hsq : ∀ a : k, 16 * ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ ^ 2 ≤ specNorm X ^ 2 := by
    intro a
    have hXe : X *ᵥ e a = Matrix.diagonal (equispacedLevelSpectrum k m 2) *ᵥ e a -
        (W * M) *ᵥ e a := by
      rw [hXdef, Matrix.sub_mulVec]
    have hw : (1 - P) *ᵥ (X *ᵥ e a) = (4 : ℝ) • ((1 - P) *ᵥ e a) := by
      have hWMv : (1 - P) *ᵥ ((W * M) *ᵥ e a) = 0 := by
        rw [Matrix.mulVec_mulVec, hWM, Matrix.zero_mulVec]
      rw [hXe, Matrix.mulVec_sub, hWMv, sub_zero, hDe, Matrix.mulVec_smul]
    have hA := hP.norm_toLp_sq_eq_add (X *ᵥ e a)
    have hB := norm_toLp_mulVec_le X (e a)
    rw [hnorm1 a, mul_one] at hB
    have hC : ‖WithLp.toLp 2 ((1 - P) *ᵥ (X *ᵥ e a))‖ = 4 * ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ := by
      rw [hw, WithLp.toLp_smul, norm_smul]
      norm_num
    rw [hC, mul_pow] at hA
    nlinarith [sq_nonneg ‖WithLp.toLp 2 (P *ᵥ (X *ᵥ e a))‖, pow_le_pow_left₀ (norm_nonneg _) hB 2]
  have hsum : ∑ a : k, 16 * ‖WithLp.toLp 2 ((1 - P) *ᵥ e a)‖ ^ 2 ≤
      ∑ a : k, specNorm X ^ 2 := Finset.sum_le_sum fun a _ => hsq a
  rw [← Finset.mul_sum] at hsum
  simp only [hpy, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one] at hsum
  have hk : (0 : ℝ) < Fintype.card k := Nat.cast_pos.mpr Fintype.card_pos
  rw [div_le_iff₀ hk]
  nlinarith [hsum]

/-- **Interpolation bound for depth-3 Krylov vectors**: let
$\mathbf{G} \in \mathbb{R}^{n \times b}$ with tail blocks $\mathbf{G}_j$ (rows of level $j + 1$)
and head block $\mathbf{G}_h$, $s^2\mathbf{I} \preceq \mathbf{G}_j^{\mathsf{H}}\mathbf{G}_j$ for
$j = 0, 1, 2$ and $\|\mathbf{G}_h\|_2 \le S$. Every $\mathbf{z} \in \mathcal{K}_3(\mathbf{D},
\mathbf{G})$ has
$$s^2\sum_{a \in k} z_a^2 \le 19\,S^2\,\|\mathbf{z}\|^2 \,.$$
OP5, Step 3 (eq. (2)).
Proof: `NLAlib.mem_blockKrylovSpace_iff`: on level $\lambda$ the block of $\mathbf{z}$ is
$\mathbf{G}_\lambda\mathbf{p}(\lambda)$ for a vector polynomial of degree at most $2$; by
`NLAlib.sum_neg_one_pow_mul_choose_mul_eval_eq_zero` ($n = 3$, $x = h = 1$, coordinatewise)
$\mathbf{p}(4) = \mathbf{p}(1) - 3\mathbf{p}(2) + 3\mathbf{p}(3)$, so
$\|\mathbf{p}(4)\|^2 \le 19\sum_{j}\|\mathbf{p}(j)\|^2$ (Cauchy–Schwarz); then
$\|\mathbf{G}_h\mathbf{p}(4)\| \le S\|\mathbf{p}(4)\|$
(`NLAlib.norm_toLp_mulVec_le`) and
$s^2\|\mathbf{p}(j)\|^2 \le \|\mathbf{G}_j\mathbf{p}(j)\|^2$ (`NLAlib.quadForm` of the Loewner
bound). M, about 70 lines. -/
theorem mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace {b : Type*} [Fintype b]
    [DecidableEq b] {G : Matrix (k ⊕ (Fin 3 × m)) b ℝ} {s S : ℝ}
    (hs : ∀ j : Fin 3, s ^ 2 • (1 : Matrix b b ℝ) ≤
      (G.submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        G.submatrix (fun i : m => Sum.inr (j, i)) id)
    (hS : specNorm (G.submatrix Sum.inl id) ≤ S) {z : k ⊕ (Fin 3 × m) → ℝ}
    (hz : z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3) :
    s ^ 2 * ∑ a : k, z (Sum.inl a) ^ 2 ≤ 19 * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
  sorry

/-- **Gaussian head capture of a depth-3 Krylov space**: let $\mathbf{G}$ be a standard Gaussian
$n \times b$ matrix, $n = k \oplus (\{0, 1, 2\} \times m)$, $\gamma > 2$, $\lvert k \rvert \le
\lvert b \rvert$ and $\gamma^2\lvert b \rvert \le \lvert m \rvert$. Then
$$\mathbb{P}\Bigl[\exists\,\mathbf{z} \in \mathcal{K}_3(\mathbf{D}, \mathbf{G}):\
\sum_{a \in k} z_a^2 > \frac{171}{(\gamma - 2)^2}\|\mathbf{z}\|^2\Bigr] \le
4\exp\Bigl(-\frac{\lvert m \rvert}{2\gamma^2}\Bigr) \,.$$
OP5, Step 3; there $\rho(\gamma) = 19(3/\gamma)^2/(1 - 2/\gamma)^2$, at $\gamma = 20$ and $26$.
Proof: on the event that $\sigma_{\min}(\mathbf{G}_j) > \sqrt{\lvert m \rvert}(1 - 2/\gamma)$ for
the three tail blocks and $\|\mathbf{G}_h\|_2 < 3\sqrt{\lvert m \rvert}/\gamma$ (blocks Gaussian,
`NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix`; tails
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix` and
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix` with
$t = \sqrt{\lvert m \rvert}/\gamma$, $\sqrt{\lvert k \rvert} \le \sqrt{\lvert b \rvert} \le t$),
apply `NLAlib.mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace`; the Loewner bound from the
smallest singular value is `NLAlib.smul_one_le_conjTranspose_mul_self_iff`-type. Union bound
`MeasureTheory.measureReal_union_le`. If $b$ is empty the space is $\{\mathbf{0}\}$. M, about 60
lines. -/
theorem measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    {b : Type*} [Fintype b] {G : Ω → Matrix (k ⊕ (Fin 3 × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin 3 × m)) b) μ) {γ : ℝ} (hγ : 2 < γ)
    (hkb : Fintype.card k ≤ Fintype.card b) (hbm : γ ^ 2 * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) (G ω) 3,
        171 / (γ - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ≤
      4 * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  sorry

/-- **Two-pass Frobenius lower bound for one deterministic algorithm**: let $\mathbf{U}$ be Haar,
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, and let a measurable algorithm make $q$ queries in at most
two passes to $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$ and
output $\mathbf{W} \in \mathbb{R}^{n \times k}$, $\mathbf{M} \in \mathbb{R}^{k \times n}$. If
$400(q + \lvert k \rvert) \le \lvert m \rvert$, then
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 < 14\lvert m \rvert +
3.3\lvert k \rvert\Bigr] \le 4e^{-\lvert m \rvert/800} \,,$$
and $14\lvert m \rvert = \|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$.
OP5, Theorem A.
Proof: extend the space by an independent standard Gaussian $n \times (q + k)$ matrix; apply
`NLAlib.QueryAlgorithm.IsPassStructured.exists_isKrylovCoupling_of_hasLaw_haarFrame` to
`alg.mapOutput Prod.fst` with no initial block (`Fin 0` columns,
`NLAlib.IsKrylovCoupling.ae_range_le_of_isEmpty`), depth $3$. On orthogonal $\mathbf{U}$,
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}} = \|\mathbf{D} - (\mathbf{U}^{\mathsf{H}}
\mathbf{W})(\mathbf{M}\mathbf{U})\|_{\mathsf{F}}$; by `NLAlib.le_frobNorm_diagonal_sub_mul_sq` the
error is at least $14\lvert m \rvert + 7(\lvert k \rvert - t)$, and $t$ is the sum over an
orthonormal basis of the range of $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ (at most $\lvert k \rvert$
vectors, in $\mathcal{K}_3$) of their head mass, at most $\tfrac{19}{36}\lvert k \rvert$ outside
the event of `NLAlib.measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix`
with $\gamma = 20$; $7 \cdot \tfrac{17}{36} > 3.3$. M, about 80 lines. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | frobNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 <
        14 * Fintype.card m + 33 / 10 * Fintype.card k} ≤
      4 * Real.exp (-(Fintype.card m / 800)) := by
  sorry

/-- **Two-pass spectral lower bound for one deterministic algorithm**: in the setting of
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
($\mathbf{U}$ Haar, $\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m,
2\mathbf{I}_m, 3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$, a measurable algorithm with $q$ queries in at
most two passes to the hidden-rotation oracle, output $\mathbf{W}\mathbf{M}$ of rank at most
$\lvert k \rvert$), with $k$ nonempty and $676(q + \lvert k \rvert) \le \lvert m \rvert$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2^2 < \tfrac{45}{4}\Bigr] \le
4e^{-\lvert m \rvert/1352} \,,$$
while $\sigma_{k+1}(\mathbf{A})^2 = 9$: no $(1 + \varepsilon)\sigma_{k+1}$ approximation for
$\varepsilon \le 0.1$.
OP5, Theorem C.
Proof: as the Frobenius form, with `NLAlib.le_specNorm_diagonal_sub_mul_sq` and $\gamma = 26$
($t \le \tfrac{19}{64}\lvert k \rvert$, $16 \cdot \tfrac{45}{64} = \tfrac{45}{4}$). M, about 60
lines. -/
theorem QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame
    [Nonempty k] {q : ℕ} {alg : QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ)
      ((k ⊕ (Fin 3 × m) → ℝ) × (k ⊕ (Fin 3 × m) → ℝ)) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)} {pass : ℕ → ℕ}
    (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < 2) (halg : alg.IsMeasurable)
    (hm : 676 * (q + Fintype.card k) ≤ Fintype.card m)
    {U : Ω → Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m))) μ) :
    μ.real {ω | specNorm (U ω * Matrix.diagonal (equispacedLevelSpectrum k m 2) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω) (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m 2)))).2) ^ 2 < 45 / 4} ≤
      4 * Real.exp (-(Fintype.card m / 1352)) := by
  sorry

/-- **Two-pass Frobenius lower bound, randomized worst case**: for every randomized algorithm (a
measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at most two passes
(per seed) with output $\mathbf{W}\mathbf{M}$, $\mathbf{W} \in \mathbb{R}^{n \times k}$, and
$400(q + \lvert k \rvert) \le \lvert m \rvert$, there is an orthogonal $\mathbf{U}$ such that for
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$
$$\mathbb{P}_s\Bigl[\|\mathbf{A} - \mathbf{W}_s\mathbf{M}_s\|_{\mathsf{F}}^2 \ge
14\lvert m \rvert + 3.3\lvert k \rvert\Bigr] \ge 1 - 4e^{-\lvert m \rvert/800} \,.$$
OP5, Corollary B(i).
Proof: Yao's principle for a class of algorithms,
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall`, for the
family `fun s => (alg s).comapResponse Prod.fst` against the hidden-rotation oracle
(`NLAlib.QueryAlgorithm.run_comapResponse`,
`NLAlib.QueryAlgorithm.IsMeasurableFamily.comapResponse`,
`NLAlib.Measurable.hiddenRotationOracle`), failure set restricted to orthogonal $\mathbf{U}$
(`NLAlib.isClosed_setOf_hasOrthonormalCols`); each deterministic member fails by
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`
(`NLAlib.QueryAlgorithm.IsPassStructured.comapResponse`). M, about 40 lines. -/
theorem exists_le_measureReal_frobNorm_sub_mul_sq_ge {q : ℕ}
    (hm : 400 * (q + Fintype.card k) ≤ Fintype.card m) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ∃ U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, HasOrthonormalCols U ∧
      1 - 4 * Real.exp (-(Fintype.card m / 800)) ≤
        ρ.real {s | 14 * Fintype.card m + 33 / 10 * Fintype.card k ≤
          frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).1 *
            ((alg s).run (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ).mulVec).2) ^ 2}
    := by
  sorry

omit [DecidableEq k] [DecidableEq m] in
/-- **Two-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: let
$k$ be nonempty, $0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, so the dimension is
$n = \lvert k \rvert + 3\lvert m \rvert < \lvert k \rvert/(2\varepsilon)$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with
$\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \le (1 + \varepsilon)
\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2$ with probability at least
$\tfrac12$ for every symmetric $\mathbf{A}$, then
$$q > \frac{\lvert k \rvert}{6400\,\varepsilon} \,.$$
Two passes of randomized SVD with $O(k/\varepsilon)$ products achieve this accuracy in
expectation, so the rate $k/\varepsilon$ is optimal for two-pass algorithms.
No printed source; research note OP5, Corollary B(i), there $q \ge k/(3200\varepsilon) - k$.
Proof: suppose $q \le \lvert k \rvert/(6400\varepsilon)$; then $400(q + \lvert k \rvert) \le
\lvert m \rvert$ and $\lvert m \rvert \ge 1750$ (`Nat.floor` bounds, `Nat.lt_floor_add_one`). Take
the $\mathbf{U}$ of `NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`; the optimum is
$14\lvert m \rvert$ (`NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`)
and $14\varepsilon\lvert m \rvert \le 1.75\lvert k \rvert < 3.3\lvert k \rvert$, so success and
failure are disjoint, while $1 - 4e^{-1750/800} > \tfrac12$ (`Real.exp_le_exp`, numerical bound on
$e^{-2}$). S, about 40 lines.
Result: two-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q := by
  sorry

omit [DecidableEq k] [DecidableEq m] in
/-- **One-pass low-rank approximation needs $\Omega(k/\varepsilon)$ matrix–vector products**: the
statement of `NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le` for algorithms whose
products are all chosen in advance (one pass): with $k$ nonempty,
$0 < \varepsilon \le \min\{1/6500, \lvert k \rvert/14000\}$ and
$\lvert m \rvert = \lfloor \lvert k \rvert/(8\varepsilon) \rfloor$, an algorithm that is within
$(1 + \varepsilon)$ of the best rank-$k$ Frobenius error with probability at least $\tfrac12$ on
every symmetric input makes $q > \lvert k \rvert/(6400\varepsilon)$ products. The best one-pass
upper bound is $O(k/\varepsilon^2)$ (generalized Nyström); the gap is open.
No printed source; research note OP5, Corollary B(iii).
Proof: a one-pass algorithm is a two-pass one (`Nat.lt_succ_of_lt`); apply
`NLAlib.div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le`. S, 3 lines.
Result: one-pass-low-rank-lower-bound -/
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_lt_one [Nonempty k] {ε : ℝ}
    {q : ℕ} (hε : 0 < ε) (hε₁ : ε ≤ 1 / 6500) (hεk : ε ≤ Fintype.card k / 14000)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) / (8 * ε)⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 1)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
        (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (6400 * ε) < q := by
  sorry

omit [DecidableEq k] [DecidableEq m] in
/-- **Two-pass spectral low-rank approximation needs products proportional to the dimension**:
let $k$ be nonempty, $\lvert m \rvert \ge 2812$ and $0 \le \varepsilon \le 1/10$. If a randomized
algorithm (a measurable seeded family, seed law $\rho$) making $q$ matrix–vector products in at
most two passes (per seed) returns $\mathbf{W}\mathbf{M}$ ($\mathbf{W} \in \mathbb{R}^{n \times
k}$) with $\|\mathbf{A} - \mathbf{W}\mathbf{M}\|_2 \le (1 + \varepsilon)\sigma_{k+1}(\mathbf{A})$
with probability at least $\tfrac12$ for every symmetric $\mathbf{A} \in \mathbb{R}^{n \times n}$,
$n = \lvert k \rvert + 3\lvert m \rvert$, then
$$\lvert m \rvert < 676\,(q + \lvert k \rvert) \,,$$
i.e. $q > (n - \lvert k \rvert)/2028 - \lvert k \rvert$, whatever $\varepsilon \le 0.1$.
OP5, Theorem C.
Proof: by contradiction with Yao's principle
`NLAlib.QueryAlgorithm.IsMeasurableFamily.exists_le_measureReal_run_mem_of_forall` as in
`NLAlib.exists_le_measureReal_frobNorm_sub_mul_sq_ge`, from
`NLAlib.QueryAlgorithm.IsPassStructured.measureReal_specNorm_sub_mul_sq_lt_le_of_hasLaw_haarFrame`;
$\sigma_{k+1} = 3$ (`NLAlib.HasOrthonormalCols.singularValues_mul_diagonal_mul_card`),
$(1.1 \cdot 3)^2 = 10.89 < 11.25$, and $1 - 4e^{-2812/1352} > \tfrac12$. M, about 50 lines. -/
theorem lt_of_forall_le_measureReal_specNorm_sub_mul_le [Nonempty k] {ε : ℝ} {q : ℕ}
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1 / 10) (hm : 2812 ≤ Fintype.card m) {S : Type*}
    [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin 3 × m) → ℝ) (k ⊕ (Fin 3 × m) → ℝ) q
      (Matrix (k ⊕ (Fin 3 × m)) k ℝ × Matrix k (k ⊕ (Fin 3 × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < 2)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ, A.IsHermitian →
      1 / 2 ≤ ρ.real {s | specNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ≤
        (1 + ε) * singularValues A (Fintype.card k)}) :
    Fintype.card m < 676 * (q + Fintype.card k) := by
  sorry

end NLAlib
