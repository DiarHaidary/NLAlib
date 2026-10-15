/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Data.NNReal.Basic
public import NLAlib.Matrix.Basic.Orthonormal
public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Basic.Projector
public import NLAlib.Matrix.Subspaces.ProjectorPair

/-!
# Leverage scores and coherence

The leverage score of row $i$ of a matrix `A : Matrix m n 𝕜`, $\mathbf{A} \in \Bbbk^{m \times n}$,
is the $i$-th diagonal entry of the orthogonal projector $\mathbf{P}_{\mathbf{A}}$ onto its column
space, `NLAlib.leverageScore A i = re (rangeProjector A i i)`. It is defined for every shape and
rank, depends only on the column space of $\mathbf{A}$, lies in $[0, 1]$, and the scores sum to
$\operatorname{rank} \mathbf{A}$; for $\mathbf{A}$ with orthonormal columns it is the squared norm
of row $i$. The coherence is $\lvert m \rvert$ times the largest score, and the leverage-score
distribution is the score vector divided by the rank (junk value $0$ when
$\mathbf{A} = \mathbf{0}$).

These are the quantities of the domination hypothesis `∀ i, leverageScore U i ≤ L * p i` of the
row-sampling theorems (`NLAlib.Sketching.Sampling.RowSampling`): exact leverage sampling has
$L = \operatorname{rank} \mathbf{U}$, uniform sampling has $L$ equal to the coherence of
$\mathbf{U}$. Design: `docs/design/Sketching-S4.md` §3.1, §8 (moved from `Sketching/Sampling/` to
the Matrix layer on 2026-10-15).

## Main definitions

* `NLAlib.leverageScore`, `NLAlib.coherence`, `NLAlib.leverageScoreDistribution`.

## Main results

* `NLAlib.leverageScore_nonneg`, `NLAlib.leverageScore_le_one`, `NLAlib.sum_leverageScore`.
* `NLAlib.leverageScore_eq_norm_sq`, `NLAlib.HasOrthonormalCols.leverageScore_eq`: norm forms.
* `NLAlib.leverageScore_eq_of_range_eq`, `NLAlib.leverageScore_le_of_range_le`: the scores
  depend only on the column space, monotonically.
* `NLAlib.leverageScore_eq_zero_iff`: a score vanishes exactly on a zero row.
* `NLAlib.leverageScore_le_coherence_mul_inv`, `NLAlib.rank_le_coherence`,
  `NLAlib.coherence_le_card`.
* `NLAlib.sum_leverageScoreDistribution`,
  `NLAlib.leverageScore_le_rank_mul_leverageScoreDistribution`.
* `NLAlib.exists_hasOrthonormalCols_of_leverageScore_le`, `NLAlib.rank_le_of_leverageScore_le`:
  the reduction to orthonormal columns and the bound on the rank under a domination
  $\ell_i(\mathbf{U}) \le L p_i$; `NLAlib.leverageScore_le_mul_const_inv_card`,
  `NLAlib.pos_of_leverageScore_le_mul_inv_card`: domination by uniform weights.
-/

@[expose] public section

open scoped Matrix MatrixOrder NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m n q r : Type*} [Fintype m] [Fintype n] [Fintype q]
  {A : Matrix m n 𝕜} {B : Matrix m q 𝕜}

/-! ### Leverage scores -/

/-- The **leverage score** of row $i$ of $\mathbf{A}$: the $i$-th diagonal entry of the orthogonal
projector onto the column space of $\mathbf{A}$, for every shape and rank ($0$ on every row when
$\mathbf{A} = \mathbf{0}$). [Woodruff2014, Definition 16 and the paragraph after it] (there
$\ell_i^2$, the squared row norm of a basis of the range); [MartinssonTropp2020, §9.6.1] (there
$\lVert \mathbf{P}_L \boldsymbol{\delta}_i \rVert^2$, with $\mathbf{P}_L$ the projector onto the
column space).
Result: leverage-scores -/
noncomputable def leverageScore (A : Matrix m n 𝕜) (i : m) : ℝ :=
  RCLike.re (rangeProjector A i i)

/-- Leverage scores are nonnegative. -/
theorem leverageScore_nonneg (A : Matrix m n 𝕜) (i : m) : 0 ≤ leverageScore A i :=
  ((isStarProjection_rangeProjector A).re_apply_self_mem_Icc i).1

/-- Leverage scores are at most one. -/
theorem leverageScore_le_one (A : Matrix m n 𝕜) (i : m) : leverageScore A i ≤ 1 :=
  ((isStarProjection_rangeProjector A).re_apply_self_mem_Icc i).2

/-- The leverage scores sum to the rank of $\mathbf{A}$.
[Woodruff2014, after Definition 16];
[MartinssonTropp2020, §9.6.1]. -/
theorem sum_leverageScore (A : Matrix m n 𝕜) : ∑ i, leverageScore A i = A.rank := by
  simp only [leverageScore]
  rw [(isStarProjection_rangeProjector A).sum_re_apply_self, rank_rangeProjector]

/-- The leverage score of row $i$ is $\lVert \mathbf{P} \mathbf{e}_i \rVert^2$ for the projector
$\mathbf{P}$ onto the column space. [MartinssonTropp2020, §9.6.1]. -/
theorem leverageScore_eq_norm_sq (A : Matrix m n 𝕜) (i : m) :
    leverageScore A i = ‖WithLp.toLp 2 ((rangeProjector A).col i)‖ ^ 2 :=
  (isStarProjection_rangeProjector A).re_apply_self_eq_norm_sq i

/-- For $\mathbf{U}$ with orthonormal columns, the leverage score of row $i$ is the squared norm
of that row. [Woodruff2014, Definition 16]. -/
theorem HasOrthonormalCols.leverageScore_eq [Fintype r] [DecidableEq r] {U : Matrix m r 𝕜}
    (hU : HasOrthonormalCols U) (i : m) : leverageScore U i = ‖WithLp.toLp 2 (U i)‖ ^ 2 := by
  rw [leverageScore, hU.rangeProjector_eq, EuclideanSpace.norm_sq_eq]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, RCLike.star_def,
    RCLike.mul_conj]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← RCLike.ofReal_pow, RCLike.ofReal_re]

/-- Leverage scores depend only on the column space (basis independence). [Woodruff2014, after
Definition 16]. -/
theorem leverageScore_eq_of_range_eq
    (h : LinearMap.range A.mulVecLin = LinearMap.range B.mulVecLin) :
    leverageScore A = leverageScore B := by
  funext i
  simp only [leverageScore, rangeProjector_inj.2 h]

open scoped ComplexOrder in
/-- Leverage scores are monotone in the column space: if the column space of $\mathbf{B}$ is
contained in that of $\mathbf{A}$ (`range B ≤ range A`), every score of $\mathbf{B}$ is at most the
corresponding score of $\mathbf{A}$. This is how a domination hypothesis for
$[\mathbf{A}, \mathbf{y}]$ passes to $\mathbf{A}$. -/
theorem leverageScore_le_of_range_le
    (h : LinearMap.range B.mulVecLin ≤ LinearMap.range A.mulVecLin) (i : m) :
    leverageScore B i ≤ leverageScore A i := by
  classical
  have h' := (RCLike.nonneg_iff.mp ((Matrix.le_iff.mp (rangeProjector_mono h)).diag_nonneg
    (i := i))).1
  rw [Matrix.sub_apply, map_sub] at h'
  simp only [leverageScore]
  linarith

/-- A leverage score vanishes exactly on a zero row of $\mathbf{A}$. -/
theorem leverageScore_eq_zero_iff (A : Matrix m n 𝕜) (i : m) :
    leverageScore A i = 0 ↔ A i = 0 := by
  classical
  have hcol : (rangeProjector A).col i = rangeProjector A *ᵥ Pi.single i 1 := by
    rw [Matrix.mulVec_single_one]
  have hA : Aᴴ *ᵥ Pi.single i 1 = star (A i) := by
    rw [Matrix.mulVec_single_one]
    ext j
    simp [Matrix.conjTranspose_apply]
  rw [leverageScore_eq_norm_sq, sq_eq_zero_iff, norm_eq_zero, WithLp.toLp_eq_zero, hcol,
    rangeProjector_mulVec_eq_zero_iff, hA, star_eq_zero]

/-! ### Coherence -/

/-- The **coherence** of $\mathbf{A}$: $\lvert m \rvert$ times its largest leverage score, between
$\operatorname{rank} \mathbf{A}$ and $\lvert m \rvert$ (`NLAlib.rank_le_coherence`,
`NLAlib.coherence_le_card`). Junk value $0$ for empty `m`.
[MartinssonTropp2020, §9.6.1]. -/
noncomputable def coherence (A : Matrix m n 𝕜) : ℝ :=
  Fintype.card m * ⨆ i, leverageScore A i

/-- Every leverage score is at most the coherence divided by $\lvert m \rvert$: the domination
hypothesis of uniform sampling, with $L$ the coherence. -/
theorem leverageScore_le_coherence_mul_inv (A : Matrix m n 𝕜) (i : m) :
    leverageScore A i ≤ coherence A * (Fintype.card m : ℝ)⁻¹ := by
  have : Nonempty m := ⟨i⟩
  have hc : (Fintype.card m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [coherence, mul_comm, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  exact le_ciSup (Set.finite_range _).bddAbove i

/-- The coherence is at least the rank. [MartinssonTropp2020, §9.6.1]. -/
theorem rank_le_coherence (A : Matrix m n 𝕜) : (A.rank : ℝ) ≤ coherence A := by
  rw [← sum_leverageScore, coherence]
  calc ∑ i, leverageScore A i ≤ ∑ _i : m, ⨆ j, leverageScore A j :=
        Finset.sum_le_sum fun i _ => le_ciSup (Set.finite_range _).bddAbove i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The coherence is at most the number of rows, $\lvert m \rvert$. [MartinssonTropp2020, §9.6.1].
-/
theorem coherence_le_card (A : Matrix m n 𝕜) : coherence A ≤ Fintype.card m := by
  rw [coherence]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _)
    (Real.iSup_le (fun i => leverageScore_le_one A i) zero_le_one)

/-! ### The leverage-score distribution -/

/-- The **leverage-score distribution** of $\mathbf{A}$: the scores divided by the rank, a
probability vector when $\mathbf{A} \ne \mathbf{0}$ (`NLAlib.sum_leverageScoreDistribution`). Junk
value $0$ on every row when $\mathbf{A} = \mathbf{0}$. [Woodruff2014, Definition 16] (the case
$\beta = 1$); [MartinssonTropp2020, §9.6.1]. -/
noncomputable def leverageScoreDistribution (A : Matrix m n 𝕜) (i : m) : ℝ≥0 :=
  ‖leverageScore A i‖₊ / A.rank

/-- The leverage-score distribution as a real number. -/
theorem coe_leverageScoreDistribution (A : Matrix m n 𝕜) (i : m) :
    (leverageScoreDistribution A i : ℝ) = leverageScore A i / A.rank := by
  rw [leverageScoreDistribution, NNReal.coe_div, coe_nnnorm,
    Real.norm_of_nonneg (leverageScore_nonneg A i), NNReal.coe_natCast]

/-- All leverage scores of a rank-zero matrix vanish. -/
private theorem leverageScore_eq_zero_of_rank_eq_zero (h : A.rank = 0) (i : m) :
    leverageScore A i = 0 := by
  have hs := sum_leverageScore A
  rw [h, Nat.cast_zero] at hs
  exact (Finset.sum_eq_zero_iff_of_nonneg fun j _ => leverageScore_nonneg A j).1 hs i
    (Finset.mem_univ i)

/-- The leverage-score distribution of a nonzero matrix sums to one. -/
theorem sum_leverageScoreDistribution (hA : A ≠ 0) : ∑ i, leverageScoreDistribution A i = 1 := by
  have hr : (A.rank : ℝ) ≠ 0 := by
    intro h0
    refine hA (Matrix.ext fun i j => ?_)
    have hi := (leverageScore_eq_zero_iff A i).1
      (leverageScore_eq_zero_of_rank_eq_zero (by exact_mod_cast h0) i)
    rw [hi, Pi.zero_apply, Matrix.zero_apply]
  rw [← NNReal.coe_inj, NNReal.coe_sum, NNReal.coe_one]
  simp only [coe_leverageScoreDistribution]
  rw [← Finset.sum_div, sum_leverageScore, div_self hr]

/-- Each leverage score is at most $\operatorname{rank} \mathbf{A}$ times its weight in the
leverage-score distribution: the domination hypothesis of exact leverage sampling, with
$L = \operatorname{rank} \mathbf{A}$. Holds also for $\mathbf{A} = \mathbf{0}$, where every score is
$0$. -/
theorem leverageScore_le_rank_mul_leverageScoreDistribution (A : Matrix m n 𝕜) (i : m) :
    leverageScore A i ≤ A.rank * leverageScoreDistribution A i := by
  rw [coe_leverageScoreDistribution]
  rcases eq_or_ne (A.rank : ℝ) 0 with h | h
  · rw [leverageScore_eq_zero_of_rank_eq_zero (by exact_mod_cast h) i, zero_div, mul_zero]
  · rw [mul_div_cancel₀ _ h]

/-! ### Domination by weights

The hypothesis of the row-sampling theorems is a domination $\ell_i(\mathbf{U}) \le L p_i$ of the
leverage scores by weights $p : n \to \mathbb{R}_{\ge 0}$. -/

section Domination

variable [Fintype r] {U : Matrix n r 𝕜} {p : n → ℝ≥0} {L : ℝ}

/-- **Reduction to orthonormal columns.** Under the domination
$\ell_i(\mathbf{U}) \le L p_i$ of the leverage scores of $\mathbf{U}$ (any shape and rank),
there is a $\mathbf{Q}$ with $\operatorname{rank}\mathbf{U}$ orthonormal columns whose range
contains that of $\mathbf{U}$ and whose rows inherit the domination,
$\|\mathbf{q}_i\|^2 \le L p_i$. It reduces every fixed-$\mathbf{U}$ row-sampling tail, with or
without replacement, to orthonormal columns, through `NLAlib.HasSubspaceEmbedding.of_range_le`. -/
theorem exists_hasOrthonormalCols_of_leverageScore_le
    (hdom : ∀ i, leverageScore U i ≤ L * p i) :
    ∃ Q : Matrix n (Fin U.rank) 𝕜, HasOrthonormalCols Q ∧
      LinearMap.range U.mulVecLin ≤ LinearMap.range Q.mulVecLin ∧
      ∀ i, ‖WithLp.toLp 2 (Q i)‖ ^ 2 ≤ L * p i := by
  obtain ⟨Q, hQ, hR⟩ := exists_hasOrthonormalCols_range_eq U (Fintype.card_fin _)
  refine ⟨Q, hQ, hR.ge, fun i => ?_⟩
  rw [← hQ.leverageScore_eq, leverageScore_eq_of_range_eq hR]
  exact hdom i

/-- Under leverage domination $\ell_i(\mathbf{U}) \le L p_i$ with weights summing to one, the
rank is at most the domination constant: $\operatorname{rank}\mathbf{U} \le L$ (the leverage
scores sum to the rank). It gives $L > 0$ for the Chernoff call when $\mathbf{U} \ne
\mathbf{0}$. -/
theorem rank_le_of_leverageScore_le (hp : ∑ i, p i = 1)
    (hdom : ∀ i, leverageScore U i ≤ L * p i) : (U.rank : ℝ) ≤ L := by
  calc (U.rank : ℝ) = ∑ i, leverageScore U i := (sum_leverageScore U).symm
    _ ≤ ∑ i, L * p i := Finset.sum_le_sum fun i _ => hdom i
    _ = L := by rw [← Finset.mul_sum, ← NNReal.coe_sum, hp, NNReal.coe_one, mul_one]

/-- **Uniform weights, in the form of the sketch.** The domination
$\ell_i(\mathbf{U}) \le L / \lvert n \rvert$ by uniform weights, as stated by uniform sampling
with and without replacement and the SRHT, is the domination $\ell_i(\mathbf{U}) \le L p_i$ at
the weights $p_i = 1/\lvert n \rvert$ of `NLAlib.samplingSketch`. -/
theorem leverageScore_le_mul_const_inv_card
    (hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) (i : n) :
    leverageScore U i ≤ L * ((fun _ : n => (Fintype.card n : ℝ≥0)⁻¹) i : ℝ) := by
  simp only [NNReal.coe_inv, NNReal.coe_natCast]
  exact hdom i

/-- Under domination by uniform weights, $\ell_i(\mathbf{U}) \le L / \lvert n \rvert$, a matrix
of positive rank has $L > 0$ (`NLAlib.rank_le_of_leverageScore_le`). -/
theorem pos_of_leverageScore_le_mul_inv_card
    (hdom : ∀ i, leverageScore U i ≤ L * (Fintype.card n : ℝ)⁻¹) (hd : 0 < U.rank) : 0 < L := by
  have : Nonempty n := by
    by_contra h
    rw [not_nonempty_iff] at h
    rw [show U = 0 from Matrix.ext fun i => isEmptyElim i, Matrix.rank_zero] at hd
    exact lt_irrefl 0 hd
  exact (Nat.cast_pos.2 hd).trans_le
    (rank_le_of_leverageScore_le NNReal.sum_const_inv_card
      (leverageScore_le_mul_const_inv_card hdom))

end Domination

end NLAlib
