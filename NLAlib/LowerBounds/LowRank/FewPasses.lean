/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Real.Basic
public import NLAlib.LowerBounds.QueryModel.HiddenRotation
public import NLAlib.LowerBounds.QueryModel.Yao
public import NLAlib.Matrix.Spectral.LowRank
public import NLAlib.Polynomial.Interpolation.DividedDifference
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues

/-!
# Lower bounds for few-pass low-rank approximation: the hard spectrum

The hard instances of the pass lower bounds for rank-$k$ approximation are
$\mathbf{A} = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ with $\mathbf{U}$
Haar and $\mathbf{d}$ = `equispacedLevelSpectrum k m p`: a head of $k$ eigenvalues $p + 2$ and a
tail of $p + 1$ equispaced levels $1, \dots, p + 1$ with $m$ eigenvalues each. A $p$-pass
algorithm sees $\mathbf{U}$ only through polynomials of degree at most $p$ in
$\operatorname{diag}(\mathbf{d})$, and such a polynomial is fixed at the head by its values on the
tail levels (finite differences), so the head cannot be captured unless the number of products is
of the order of $m$. This file has the deterministic and Gaussian steps; the two-pass
algorithmic lower bounds ($p = 2$), which go through the Krylov coupling, are in the scaffold.
Design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.6, research note OP5.

## Main definitions

* `NLAlib.equispacedLevelSpectrum`.

## Main results

* `NLAlib.HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq`,
  `NLAlib.HasOrthonormalCols.singularValues_mul_diagonal_mul_card`: the optimum.
* `NLAlib.le_frobNorm_diagonal_sub_mul_sq`, `NLAlib.le_specNorm_diagonal_sub_mul_sq`: error from
  head capture.
* `NLAlib.mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace`: the interpolation bound.
* `NLAlib.measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix`: Gaussian
  head capture.
-/

@[expose] public section

namespace NLAlib

/-- The **equispaced-level spectrum** with head $k$ and tail $m$ for $p$ passes, on
$k \oplus (\{0, \dots, p\} \times m)$: the value $p + 2$ on the head coordinates and $j + 1$ on
the tail level $j$. For $p = 2$ it is
$\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$, whose best
rank-$\lvert k \rvert$ Frobenius error is $14\lvert m \rvert$. -/
def equispacedLevelSpectrum (k m : Type*) (p : ℕ) : k ⊕ (Fin (p + 1) × m) → ℝ :=
  Sum.elim (fun _ => (p : ℝ) + 2) fun x => (x.1 : ℝ) + 1

end NLAlib

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {k m : Type*} [Fintype k]
  [Fintype m] [DecidableEq k] [DecidableEq m]

/-- The optimum of the two-pass hard instance: for orthogonal $\mathbf{U}$ and
$\mathbf{A} = \mathbf{U}\operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m,
3\mathbf{I}_m)\mathbf{U}^{\mathsf{H}}$,
$\|\mathbf{A} - \llbracket \mathbf{A} \rrbracket_k\|_{\mathsf{F}}^2 = 14\lvert m \rvert$. -/
theorem HasOrthonormalCols.frobNorm_mul_diagonal_mul_sub_truncatedSVD_sq
    {U : Matrix (k ⊕ (Fin 3 × m)) (k ⊕ (Fin 3 × m)) ℝ} (hU : HasOrthonormalCols U) :
    frobNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ -
        truncatedSVD (U * Matrix.diagonal (equispacedLevelSpectrum k m 2) * Uᴴ)
          (Fintype.card k)) ^ 2 = 14 * Fintype.card m := by
  set d := equispacedLevelSpectrum k m 2
  set A := U * Matrix.diagonal d * Uᴴ
  set h : k ⊕ (Fin 3 × m) → ℝ := Sum.elim (fun _ => 4) 0
  have hcard : Fintype.card (k ⊕ (Fin 3 × m)) = Fintype.card k + 3 * Fintype.card m := by
    simp
  -- the squared Frobenius norm of the diagonal pieces
  have hD : frobNorm (Matrix.diagonal d) ^ 2 = 16 * Fintype.card k + 14 * Fintype.card m := by
    rw [frobNorm_diagonal_sq]
    simp [d, equispacedLevelSpectrum, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_three]
    ring
  have hT : frobNorm (Matrix.diagonal (d - h)) ^ 2 = 14 * Fintype.card m := by
    rw [frobNorm_diagonal_sq]
    simp [d, h, equispacedLevelSpectrum, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_three]
    ring
  have hrank : (U * Matrix.diagonal h * Uᴴ).rank ≤ Fintype.card k := by
    refine (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans ?_)
    rw [Matrix.rank_diagonal]
    refine Fintype.card_le_of_surjective (fun a : k => ⟨Sum.inl a, by norm_num [h]⟩) ?_
    rintro ⟨a | x, hx⟩
    · exact ⟨a, rfl⟩
    · exact (hx rfl).elim
  have hσ : ∀ i, singularValues A i ≤ 4 := by
    intro i
    refine (singularValues_le_specNorm A i).trans ?_
    rw [hU.specNorm_mul_conjTranspose_right, hU.specNorm_mul_left]
    refine specNorm_diagonal_le (by norm_num) fun i => ?_
    rcases i with a | ⟨j, b⟩
    · norm_num [d, equispacedLevelSpectrum]
    · fin_cases j <;> norm_num [d, equispacedLevelSpectrum]
  refine le_antisymm ?_ ?_
  · -- Eckart–Young against the head part `U diag(h) Uᴴ`
    rw [← hT]
    refine pow_le_pow_left₀ (frobNorm_nonneg _)
      ((frobNorm_sub_truncatedSVD_le_of_rank_le A hrank).trans_eq ?_) 2
    rw [show A - U * Matrix.diagonal h * Uᴴ = U * Matrix.diagonal (d - h) * Uᴴ by
      rw [show d - h = fun i => d i - h i from rfl, ← Matrix.diagonal_sub, Matrix.mul_sub,
        Matrix.sub_mul],
      hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left]
  · -- the head singular values are at most `4`, so the tail carries at least `14 |m|`
    have hA : frobNorm A ^ 2 = 16 * Fintype.card k + 14 * Fintype.card m := by
      rw [hU.frobNorm_mul_conjTranspose_right, hU.frobNorm_mul_left, hD]
    have hhead : ∑ i ∈ Finset.range (Fintype.card k), singularValues A i ^ 2 ≤
        16 * Fintype.card k := by
      calc _ ≤ ∑ i ∈ Finset.range (Fintype.card k), (4 : ℝ) ^ 2 :=
            Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (singularValues_nonneg A i) (hσ i) 2
        _ = _ := by simp; ring
    rw [frobNorm_sub_truncatedSVD_sq, min_self]
    rw [frobNorm_sq_eq_sum_singularValues_sq, ← Finset.sum_range_add_sum_Ico _
      (hcard ▸ Nat.le_add_right _ _ : Fintype.card k ≤ _)] at hA
    linarith

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
(indices from $0$). -/
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

/-- Frobenius error from head capture: for every $\mathbf{W} \in \mathbb{R}^{n \times k}$ and
$\mathbf{M} \in \mathbb{R}^{k \times n}$, $n = k \oplus (\{0, 1, 2\} \times m)$ and
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_{\mathsf{F}}^2 \ge 14\lvert m \rvert + 7\bigl(\lvert k
\rvert - t\bigr) \,, \qquad t = \sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \,,$$
$t$ the head mass captured by the range of $\mathbf{W}$.
OP5, Step 1 (eq. (1)). -/
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

/-- Spectral error from head capture: for every $\mathbf{W} \in \mathbb{R}^{n \times k}$ and
$\mathbf{M} \in \mathbb{R}^{k \times n}$, $k$ nonempty, $n = k \oplus (\{0, 1, 2\} \times m)$ and
$\mathbf{D} = \operatorname{diag}(4\mathbf{I}_k, \mathbf{I}_m, 2\mathbf{I}_m, 3\mathbf{I}_m)$,
$$\|\mathbf{D} - \mathbf{W}\mathbf{M}\|_2^2 \ge
\frac{16(\lvert k \rvert - t)}{\lvert k \rvert} \,, \qquad
t = \sum_{a \in k}\|\mathbf{P}_{\mathbf{W}}\mathbf{e}_a\|^2 \,.$$
OP5, Step 1 (eq. (1')). -/
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

/-- A real polynomial of degree below $3$ satisfies $P(4) = P(1) - 3P(2) + 3P(3)$. -/
private lemma eval_four_eq_of_natDegree_lt {P : Polynomial ℝ} (hP : P.natDegree < 3) :
    P.eval 4 = P.eval 1 - 3 * P.eval 2 + 3 * P.eval 3 := by
  have h := sum_neg_one_pow_mul_choose_mul_eval_eq_zero hP 1 1
  norm_num [Finset.sum_range_succ] at h
  linarith

/-- Summed over the columns, $P(4)^2 \le 19\bigl(P(1)^2 + P(2)^2 + P(3)^2\bigr)$ for polynomials
of degree below $3$ (Cauchy–Schwarz on the coefficients $(1, -3, 3)$). -/
private lemma sum_eval_four_sq_le_of_natDegree_lt {b : Type*} [Fintype b] {f : b → Polynomial ℝ}
    (hdeg : ∀ c, (f c).natDegree < 3) :
    ∑ c, (f c).eval 4 ^ 2 ≤
      19 * (∑ c, (f c).eval 1 ^ 2 + ∑ c, (f c).eval 2 ^ 2 + ∑ c, (f c).eval 3 ^ 2) := by
  have hN1 : ∀ c, (f c).eval 4 ^ 2 ≤
      19 * ((f c).eval 1 ^ 2 + (f c).eval 2 ^ 2 + (f c).eval 3 ^ 2) := by
    intro c
    rw [eval_four_eq_of_natDegree_lt (hdeg c)]
    nlinarith [sq_nonneg (3 * (f c).eval 1 + (f c).eval 2),
      sq_nonneg (3 * (f c).eval 1 - (f c).eval 3),
      sq_nonneg (3 * (f c).eval 2 + 3 * (f c).eval 3)]
  have := Finset.sum_le_sum fun c (_ : c ∈ Finset.univ) => hN1 c
  simpa only [← Finset.mul_sum, Finset.sum_add_distrib] using this

/-- The Loewner lower bound $s^2\mathbf{I} \preceq \mathbf{M}^{\mathsf{H}}\mathbf{M}$ gives
$s^2\|\mathbf{v}\|^2 \le \|\mathbf{M}\mathbf{v}\|^2$. -/
private lemma sq_mul_sum_sq_le_sum_sq_mulVec {m' b : Type*} [Fintype m'] [Fintype b]
    [DecidableEq b] (M : Matrix m' b ℝ) {s : ℝ} (hM : s ^ 2 • (1 : Matrix b b ℝ) ≤ Mᴴ * M)
    (v : b → ℝ) : s ^ 2 * ∑ c, v c ^ 2 ≤ ∑ i, (M *ᵥ v) i ^ 2 := by
  have h := (Matrix.le_iff.1 hM).dotProduct_mulVec_nonneg v
  have e : star v ⬝ᵥ ((Mᴴ * M - s ^ 2 • (1 : Matrix b b ℝ)) *ᵥ v) =
      ∑ i, (M *ᵥ v) i ^ 2 - s ^ 2 * ∑ c, v c ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec,
      dotProduct_sub, Matrix.dotProduct_mulVec, ← Matrix.star_mulVec, dotProduct_smul,
      star_trivial, smul_eq_mul]
    simp only [dotProduct, star_trivial, pow_two, Finset.mul_sum]
  linarith

/-- Interpolation bound for depth-3 Krylov vectors: let
$\mathbf{G} \in \mathbb{R}^{n \times b}$ with tail blocks $\mathbf{G}_j$ (rows of level $j + 1$)
and head block $\mathbf{G}_h$, $s^2\mathbf{I} \preceq \mathbf{G}_j^{\mathsf{H}}\mathbf{G}_j$ for
$j = 0, 1, 2$ and $\|\mathbf{G}_h\|_2 \le S$. Every $\mathbf{z} \in \mathcal{K}_3(\mathbf{D},
\mathbf{G})$ has
$$s^2\sum_{a \in k} z_a^2 \le 19\,S^2\,\|\mathbf{z}\|^2 \,.$$
OP5, Step 3 (eq. (2)). -/
theorem mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace {b : Type*} [Fintype b]
    [DecidableEq b] {G : Matrix (k ⊕ (Fin 3 × m)) b ℝ} {s S : ℝ}
    (hs : ∀ j : Fin 3, s ^ 2 • (1 : Matrix b b ℝ) ≤
      (G.submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        G.submatrix (fun i : m => Sum.inr (j, i)) id)
    (hS : specNorm (G.submatrix Sum.inl id) ≤ S) {z : k ⊕ (Fin 3 × m) → ℝ}
    (hz : z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) G 3) :
    s ^ 2 * ∑ a : k, z (Sum.inl a) ^ 2 ≤ 19 * S ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 := by
  obtain ⟨f, hf, hz'⟩ := mem_blockKrylovSpace_iff.1 hz
  have hzi : ∀ x, z x = ∑ c, (f c).eval (equispacedLevelSpectrum k m 2 x) * G x c := by
    intro x
    rw [← hz']
    simp [Finset.sum_apply, aeval_diagonal_self, Matrix.mulVec_diagonal]
  have hdeg : ∀ c, (f c).natDegree < 3 := by
    intro c
    by_cases h0 : f c = 0
    · simp [h0]
    · exact (Polynomial.natDegree_lt_iff_degree_lt h0).2 (by exact_mod_cast hf c)
  -- head block: `‖G_h v‖ ≤ S ‖v‖` with `v = P(4)`
  have hH : ∑ a : k, z (Sum.inl a) ^ 2 ≤ S ^ 2 * ∑ c, (f c).eval 4 ^ 2 := by
    have hw : ∀ a : k, z (Sum.inl a) =
        (G.submatrix (fun a : k => Sum.inl a) id *ᵥ fun c => (f c).eval 4) a := by
      intro a
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    have h1 : ‖WithLp.toLp 2 (G.submatrix (fun a : k => Sum.inl a) id *ᵥ fun c => (f c).eval 4)‖ ≤
        S * ‖WithLp.toLp 2 (fun c => (f c).eval 4)‖ :=
      (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hS (norm_nonneg _))
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [mul_pow, EuclideanSpace.norm_toLp_sq_eq_sum_sq, EuclideanSpace.norm_toLp_sq_eq_sum_sq] at h2
    simp only [hw]
    exact h2
  -- the three tail levels
  have hL0 : s ^ 2 * ∑ c, (f c).eval 1 ^ 2 ≤ ∑ i, z (Sum.inr ((0 : Fin 3), i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr ((0 : Fin 3), i)) =
        (G.submatrix (fun i : m => Sum.inr ((0 : Fin 3), i)) id *ᵥ fun c => (f c).eval 1) i := by
      intro i
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs 0) _
  have hL1 : s ^ 2 * ∑ c, (f c).eval 2 ^ 2 ≤ ∑ i, z (Sum.inr ((1 : Fin 3), i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr ((1 : Fin 3), i)) =
        (G.submatrix (fun i : m => Sum.inr ((1 : Fin 3), i)) id *ᵥ fun c => (f c).eval 2) i := by
      intro i
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs 1) _
  have hL2 : s ^ 2 * ∑ c, (f c).eval 3 ^ 2 ≤ ∑ i, z (Sum.inr ((2 : Fin 3), i)) ^ 2 := by
    have hw : ∀ i : m, z (Sum.inr ((2 : Fin 3), i)) =
        (G.submatrix (fun i : m => Sum.inr ((2 : Fin 3), i)) id *ᵥ fun c => (f c).eval 3) i := by
      intro i
      rw [hzi]
      norm_num [equispacedLevelSpectrum, Matrix.mulVec, dotProduct, mul_comm]
    simp only [hw]
    exact sq_mul_sum_sq_le_sum_sq_mulVec _ (hs 2) _
  have hN := sum_eval_four_sq_le_of_natDegree_lt hdeg
  -- the norm of `z` splits into head and tails
  have hnorm : ‖WithLp.toLp 2 z‖ ^ 2 = ∑ a : k, z (Sum.inl a) ^ 2 +
      (∑ i, z (Sum.inr ((0 : Fin 3), i)) ^ 2 + ∑ i, z (Sum.inr ((1 : Fin 3), i)) ^ 2 +
        ∑ i, z (Sum.inr ((2 : Fin 3), i)) ^ 2) := by
    rw [EuclideanSpace.norm_toLp_sq_eq_sum_sq, Fintype.sum_sum_type, Fintype.sum_prod_type,
      Fin.sum_univ_three]
  have hHnn : 0 ≤ ∑ a : k, z (Sum.inl a) ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  rw [hnorm]
  have h1 := mul_le_mul_of_nonneg_left hH (sq_nonneg s)
  have h2 := mul_le_mul_of_nonneg_left hN (by positivity : (0 : ℝ) ≤ s ^ 2 * S ^ 2)
  have h3 := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hL0 hL1) hL2)
    (by positivity : (0 : ℝ) ≤ 19 * S ^ 2)
  have h4 := mul_nonneg (by positivity : (0 : ℝ) ≤ 19 * S ^ 2) hHnn
  nlinarith [h1, h2, h3, h4]

/-- Algebra of the final step: a Krylov vector with head mass $\Sigma > 171 N/(\gamma - 2)^2$ is
impossible when $s \ge (\gamma - 2)t > 0$ and $s^2\Sigma \le 19(3t)^2 N$. -/
private theorem false_of_mul_sum_sq_le_of_lt {γ t s N sumH : ℝ} (hγ : 2 < γ) (ht : 0 < t)
    (hs : (γ - 2) * t ≤ s) (hN : 0 ≤ N) (key : s ^ 2 * sumH ≤ 19 * (3 * t) ^ 2 * N)
    (hlt : 171 / (γ - 2) ^ 2 * N < sumH) : False := by
  have hγ2 : 0 < γ - 2 := by linarith
  have hsp : 0 < s := lt_of_lt_of_le (mul_pos hγ2 ht) hs
  have h1 := mul_lt_mul_of_pos_left hlt (pow_pos hsp 2)
  have hs2 := pow_le_pow_left₀ (mul_nonneg hγ2.le ht.le) hs 2
  have h3 : t ^ 2 ≤ s ^ 2 / (γ - 2) ^ 2 := by
    rw [le_div_iff₀ (pow_pos hγ2 2)]; rw [mul_pow] at hs2; linarith [hs2]
  have h2 : 171 * t ^ 2 * N ≤ s ^ 2 * (171 / (γ - 2) ^ 2 * N) := by
    calc 171 * t ^ 2 * N = 171 * N * t ^ 2 := by ring
      _ ≤ 171 * N * (s ^ 2 / (γ - 2) ^ 2) := by gcongr
      _ = s ^ 2 * (171 / (γ - 2) ^ 2 * N) := by ring
  have key' : 19 * (3 * t) ^ 2 * N = 171 * t ^ 2 * N := by ring
  linarith [h1, key, h2, key']

omit [DecidableEq k] [DecidableEq m] in
/-- Lower Gram bound for one tail block of a Gaussian matrix (rows of level `j + 1`). -/
private theorem measureReal_not_gram_tail_le {b : Type*} [Fintype b] [DecidableEq b]
    {G : Ω → Matrix (k ⊕ (Fin 3 × m)) b ℝ} (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin 3 × m)) b) μ)
    (j : Fin 3) {t : ℝ} (ht : 0 ≤ t)
    (htn : t ≤ √(Fintype.card m : ℝ) - √(Fintype.card b : ℝ)) :
    μ.real {ω | ¬ (√(Fintype.card m : ℝ) - √(Fintype.card b : ℝ) - t) ^ 2 • (1 : Matrix b b ℝ) ≤
      ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id} ≤ Real.exp (-t ^ 2 / 2) :=
  measureReal_not_smul_one_le_conjTranspose_mul_self_le_of_hasLaw_gaussianMatrix
    (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG (fun i i' h => by simpa using h)
      Function.injective_id) ht htn

/-- Gaussian head capture of a depth-3 Krylov space: let $\mathbf{G}$ be a standard Gaussian
$n \times b$ matrix, $n = k \oplus (\{0, 1, 2\} \times m)$, $\gamma > 2$, $\lvert k \rvert \le
\lvert b \rvert$ and $\gamma^2\lvert b \rvert \le \lvert m \rvert$. Then
$$\mathbb{P}\Bigl[\exists\,\mathbf{z} \in \mathcal{K}_3(\mathbf{D}, \mathbf{G}):\
\sum_{a \in k} z_a^2 > \frac{171}{(\gamma - 2)^2}\|\mathbf{z}\|^2\Bigr] \le
4\exp\Bigl(-\frac{\lvert m \rvert}{2\gamma^2}\Bigr) \,.$$
OP5, Step 3; there $\rho(\gamma) = 19(3/\gamma)^2/(1 - 2/\gamma)^2$, at $\gamma = 20$ and $26$. -/
theorem measureReal_exists_mem_blockKrylovSpace_lt_sum_sq_le_of_hasLaw_gaussianMatrix
    {b : Type*} [Fintype b] {G : Ω → Matrix (k ⊕ (Fin 3 × m)) b ℝ}
    (hG : HasLaw G (gaussianMatrix (k ⊕ (Fin 3 × m)) b) μ) {γ : ℝ} (hγ : 2 < γ)
    (hkb : Fintype.card k ≤ Fintype.card b) (hbm : γ ^ 2 * Fintype.card b ≤ Fintype.card m) :
    μ.real {ω | ∃ z ∈ blockKrylovSpace (Matrix.diagonal (equispacedLevelSpectrum k m 2)) (G ω) 3,
        171 / (γ - 2) ^ 2 * ‖WithLp.toLp 2 z‖ ^ 2 < ∑ a : k, z (Sum.inl a) ^ 2} ≤
      4 * Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
  classical
  have hP : IsProbabilityMeasure μ := hG.isProbabilityMeasure
  have hγ0 : 0 < γ := by linarith
  set a : ℝ := √(Fintype.card m : ℝ) with ha_def
  set c : ℝ := √(Fintype.card b : ℝ) with hc_def
  set d : ℝ := √(Fintype.card k : ℝ) with hd_def
  set t : ℝ := a / γ with ht_def
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hc0 : 0 ≤ c := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = Fintype.card m := Real.sq_sqrt (Nat.cast_nonneg _)
  have hc2 : c ^ 2 = Fintype.card b := Real.sq_sqrt (Nat.cast_nonneg _)
  have ht0 : 0 ≤ t := div_nonneg ha0 hγ0.le
  have hat : a = γ * t := by rw [ht_def]; field_simp
  have hct : c ≤ t := by
    have h1 : (c * γ) ^ 2 ≤ a ^ 2 := by
      rw [mul_pow, ha2, hc2]; linarith [hbm]
    rw [ht_def, le_div_iff₀ hγ0]
    nlinarith [mul_nonneg hc0 hγ0.le]
  have htn : t ≤ a - c := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ γ - 2) ht0]
  have hdc : d ≤ c := Real.sqrt_le_sqrt (Nat.cast_le.mpr hkb)
  have hexp : Real.exp (-t ^ 2 / 2) = Real.exp (-(Fintype.card m / (2 * γ ^ 2))) := by
    congr 1
    rw [ht_def, div_pow, ha2]
    ring
  -- tail blocks: the lower Gram bound fails with probability at most `exp (-t^2/2)` each
  have hA : μ.real (⋃ j : Fin 3, {ω | ¬ (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
      ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ≤ 3 * Real.exp (-t ^ 2 / 2) := by
    refine (measureReal_iUnion_fintype_le _).trans ((Finset.sum_le_sum fun j _ =>
      measureReal_not_gram_tail_le hG j ht0 htn).trans ?_)
    simp
  -- head block: the spectral norm is large with probability at most `exp (-t^2/2)`
  have hB : μ.real {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)} ≤
      Real.exp (-t ^ 2 / 2) :=
    measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix
      (hasLaw_submatrix_of_hasLaw_gaussianMatrix hG Sum.inl_injective Function.injective_id) ht0
  refine le_trans (measureReal_mono (s₂ := (⋃ j : Fin 3, {ω | ¬ (a - c - t) ^ 2 •
      (1 : Matrix b b ℝ) ≤ ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
        (G ω).submatrix (fun i : m => Sum.inr (j, i)) id}) ∪
      {ω | d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id)}) (fun ω hω => ?_))
    ((measureReal_union_le _ _).trans ?_)
  · obtain ⟨z, hz, hlt⟩ := hω
    by_contra hnot
    have hs : ∀ j : Fin 3, (a - c - t) ^ 2 • (1 : Matrix b b ℝ) ≤
        ((G ω).submatrix (fun i : m => Sum.inr (j, i)) id)ᴴ *
          (G ω).submatrix (fun i : m => Sum.inr (j, i)) id := by
      intro j
      by_contra h
      exact hnot (Or.inl (Set.mem_iUnion.2 ⟨j, h⟩))
    have hS : specNorm ((G ω).submatrix Sum.inl id) ≤ 3 * t := by
      by_contra h
      have hB' : d + c + t ≤ specNorm ((G ω).submatrix Sum.inl id) := by
        linarith [not_le.1 h]
      exact hnot (Or.inr hB')
    have key := mul_sum_sq_le_mul_norm_sq_of_mem_blockKrylovSpace hs hS hz
    have hsum : 0 < ∑ a : k, z (Sum.inl a) ^ 2 := lt_of_le_of_lt (by positivity) hlt
    have hne : Nonempty k := by
      by_contra h
      rw [not_nonempty_iff] at h
      simp at hsum
    have hb1 : 1 ≤ Fintype.card b := le_trans (Fintype.card_pos (α := k)) hkb
    have hb1' : (1 : ℝ) ≤ Fintype.card b := by exact_mod_cast hb1
    have hm : (0 : ℝ) < Fintype.card m :=
      lt_of_lt_of_le (pow_pos hγ0 2) ((le_mul_of_one_le_right (sq_nonneg γ) hb1').trans hbm)
    have ha_pos : 0 < a := Real.sqrt_pos.2 hm
    have ht_pos : 0 < t := div_pos ha_pos hγ0
    have hs_lb : (γ - 2) * t ≤ a - c - t := by linarith [hat, hct]
    exact false_of_mul_sum_sq_le_of_lt hγ ht_pos hs_lb (sq_nonneg _) key hlt
  · rw [← hexp]
    linarith [hA, hB]

end NLAlib
