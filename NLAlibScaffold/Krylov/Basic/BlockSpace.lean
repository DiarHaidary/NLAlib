/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.BlockSpace
public import NLAlib.Matrix.Basic.Projector

/-!
# Block Krylov spaces of a diagonal matrix: the level decomposition (scaffold)

Statement for `NLAlib/Krylov/Basic/BlockSpace.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.4). For a diagonal
$\mathbf{D} = \operatorname{diag}(\mathbf{d})$ the block Krylov space of $[\mathbf{g}, \mathbf{G}]$
splits over the levels $t$ of $\mathbf{d}$: on the coordinates $\{i : d_i = t\}$ a vector of the
space is $f_0(t)\mathbf{g}_t + \mathbf{G}_t\mathbf{f}(t)$. So the residual
$\mathbf{g} - \mathbf{D}\mathbf{x}$ of $\mathbf{x} \in \mathcal{K}_s$ is at least, on each level,
the residual polynomial at $t$ times the part of $\mathbf{g}_t$ orthogonal to the columns of
$\mathbf{G}_t$.

## Main results

* `NLAlib.exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq`.
* `NLAlib.blockKrylovSpace_le_of_range_le`,
  `NLAlib.sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two`: the depth count of the Krylov
  coupling (design note §3.2).
-/

@[expose] public section

open Polynomial
open scoped Matrix

namespace NLAlib

/-- One level of the residual: if `w i = r * g i - ∑ j, y j * G i j`, then `r ^ 2` times the squared
norm of the part of `g` orthogonal to the columns of `G` is at most the squared norm of `w`.
Proof: `1 - P` kills `G y` (`rangeProjector_mulVec_mulVec`), so `(1 - P) w = r • (1 - P) g`, and
`‖w‖² = ‖P w‖² + ‖(1 - P) w‖²` (`IsStarProjection.norm_toLp_sq_eq_add`). -/
private lemma norm_sq_mul_le_norm_sq_of_residual {m c : Type*} [Fintype m] [DecidableEq m]
    [Fintype c] (G : Matrix m c ℝ) (g w : m → ℝ) (r : ℝ) (y : c → ℝ)
    (hw : ∀ i, w i = r * g i - ∑ j, y j * G i j) :
    r ^ 2 * ‖WithLp.toLp 2 ((1 - rangeProjector G) *ᵥ g)‖ ^ 2 ≤ ‖WithLp.toLp 2 w‖ ^ 2 := by
  have hGy : (1 - rangeProjector G) *ᵥ (G *ᵥ y) = 0 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, rangeProjector_mulVec_mulVec, sub_self]
  have hwv : w = r • g - G *ᵥ y := by
    funext i
    simp [hw i, Matrix.mulVec, dotProduct, mul_comm]
  have hw' : (1 - rangeProjector G) *ᵥ w = r • ((1 - rangeProjector G) *ᵥ g) := by
    rw [hwv, Matrix.mulVec_sub, hGy, sub_zero, Matrix.mulVec_smul]
  have hsc : ∀ v : m → ℝ, ‖WithLp.toLp 2 (r • v)‖ ^ 2 = r ^ 2 * ‖WithLp.toLp 2 v‖ ^ 2 := by
    intro v
    rw [WithLp.toLp_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  have hpy := (isStarProjection_rangeProjector G).norm_toLp_sq_eq_add w
  rw [← hsc, ← hw']
  linarith [sq_nonneg ‖WithLp.toLp 2 (rangeProjector G *ᵥ w)‖]

/-- **Level decomposition of a Krylov residual**: let
$\mathbf{D} = \operatorname{diag}(\mathbf{d})$, $\mathbf{g} \in \mathbb{R}^n$ and
$\mathbf{G} \in \mathbb{R}^{n \times c}$. For every $\mathbf{x}$ in
$\mathcal{K}_s(\mathbf{D}, [\mathbf{g}, \mathbf{G}])$ there is a real $r$ with $\deg r \le s$ and
$r(0) = 1$ such that
$$\sum_{t} r(t)^2\,\bigl\|(\mathbf{I} - \mathbf{P}_{\mathbf{G}_t})\,\mathbf{g}_t\bigr\|^2 \le
\|\mathbf{g} - \mathbf{D}\mathbf{x}\|^2 \,,$$
the sum over the distinct values $t$ of $\mathbf{d}$, with $\mathbf{g}_t$, $\mathbf{G}_t$ the rows
$\{i : d_i = t\}$ of $\mathbf{g}$, $\mathbf{G}$ and $\mathbf{P}_{\mathbf{G}_t}$ the projector onto
the range of $\mathbf{G}_t$.
[Shamir2026, Section 3.3]; there in the proof of Theorem 1, with $r = 1 - p_0$.
Proof: `NLAlib.mem_blockKrylovSpace_iff` writes $\mathbf{x} = f_0(\mathbf{D})\mathbf{g} +
\sum_j f_j(\mathbf{D})\mathbf{G}_{:,j}$ with $\deg f_j < s$; set $r = 1 - X f_0$
(`Polynomial.degree_sub_le`, `Polynomial.eval_mul_X`). On level $t$, $(\mathbf{g} -
\mathbf{D}\mathbf{x})_t = r(t)\mathbf{g}_t - \mathbf{G}_t\mathbf{y}_t$
(`Matrix.mulVec_diagonal`, `NLAlib.aeval_diagonal_self`); its norm is at least that of its
projection by $\mathbf{I} - \mathbf{P}_{\mathbf{G}_t}$ (`NLAlib.rangeProjector_mulVec_mulVec`,
`NLAlib.isStarProjection_rangeProjector`), and $\|\mathbf{v}\|^2$ is the sum over the levels of
the squared norms of the blocks (`Finset.sum_fiberwise`). M, about 60 lines. -/
theorem exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq {n c : Type*} [Fintype n]
    [DecidableEq n] [Fintype c] (d g : n → ℝ) (G : Matrix n c ℝ) {s : ℕ} {x : n → ℝ}
    (hx : x ∈ blockKrylovSpace (Matrix.diagonal d)
      (Matrix.fromCols (Matrix.replicateCol Unit g) G) s) :
    ∃ r : ℝ[X], r.degree ≤ s ∧ r.eval 0 = 1 ∧
      ∑ t ∈ Finset.univ.image d, r.eval t ^ 2 *
          ‖WithLp.toLp 2 ((1 - rangeProjector (G.submatrix (Subtype.val : {i // d i = t} → n) id))
            *ᵥ fun i => g i.1)‖ ^ 2 ≤
        ‖WithLp.toLp 2 (g - Matrix.diagonal d *ᵥ x)‖ ^ 2 := by
  obtain ⟨f, hf, hsum⟩ := mem_blockKrylovSpace_iff.1 hx
  have hxi : ∀ i, x i = (f (Sum.inl ())).eval (d i) * g i +
      ∑ j, (f (Sum.inr j)).eval (d i) * G i j := by
    intro i
    rw [← hsum]
    simp [Fintype.sum_sum_type, aeval_diagonal_self, Matrix.mulVec_diagonal]
  have hdeg : (1 - X * f (Sum.inl ())).degree ≤ (s : WithBot ℕ) := by
    refine (degree_sub_le _ _).trans (max_le ?_ ?_)
    · simp
    · rw [degree_mul, degree_X, add_comm]
      have h := hf (Sum.inl ())
      rcases hd : (f (Sum.inl ())).degree with _ | k
      · exact le_trans (le_of_eq (WithBot.bot_add _)) bot_le
      · rw [hd] at h
        have hk : k < s := WithBot.coe_lt_coe.mp h
        exact WithBot.coe_le_coe.mpr (Nat.succ_le_of_lt hk)
  have hres : ∀ i, (g - Matrix.diagonal d *ᵥ x) i = (1 - X * f (Sum.inl ())).eval (d i) * g i -
      ∑ j, (X * f (Sum.inr j)).eval (d i) * G i j := by
    intro i
    rw [Pi.sub_apply, Matrix.mulVec_diagonal, hxi i]
    simp only [eval_sub, eval_mul, eval_X, eval_one, Finset.mul_sum, sub_mul, one_mul, mul_add]
    simp only [mul_assoc]
    ring
  refine ⟨1 - X * f (Sum.inl ()), hdeg, by simp, ?_⟩
  rw [EuclideanSpace.real_norm_sq_eq, ← Finset.sum_fiberwise_of_maps_to (g := d)
    (t := Finset.univ.image d) (fun i _ => Finset.mem_image_of_mem d (Finset.mem_univ i))]
  refine Finset.sum_le_sum fun t _ => ?_
  have hfib := norm_sq_mul_le_norm_sq_of_residual
    (G.submatrix (Subtype.val : {i // d i = t} → n) id) (fun i => g i.1)
    (fun i => (g - Matrix.diagonal d *ᵥ x) i.1) ((1 - X * f (Sum.inl ())).eval t)
    (fun j => (X * f (Sum.inr j)).eval t)
    (fun i => by simp only [hres i.1, i.2, Matrix.submatrix_apply, id_eq])
  refine hfib.trans (le_of_eq ?_)
  rw [EuclideanSpace.real_norm_sq_eq]
  exact (Finset.sum_subtype (Finset.univ.filter fun i => d i = t) (by simp)
    (fun i => (WithLp.toLp 2 (g - Matrix.diagonal d *ᵥ x)).ofLp i ^ 2)).symm

/-- A block Krylov space depends on its starting block only through the range: if the range of
$\mathbf{B}$ lies in that of $\mathbf{B}'$, then $\mathcal{K}_q(\mathbf{A}, \mathbf{B}) \subseteq
\mathcal{K}_q(\mathbf{A}, \mathbf{B}')$ for every $q$.
Proof: by `NLAlib.blockKrylovSpace_eq_iSup_krylovSpace` and `iSup_le` it suffices that
$\mathcal{K}_q(\mathbf{A}, \mathbf{b}_c) \subseteq \mathcal{K}_q(\mathbf{A}, \mathbf{B}')$ for each
column; write $\mathbf{b}_c = \mathbf{B}'\mathbf{y}$ (`LinearMap.mem_range`) and a vector of
the left side as $f(\mathbf{A})\mathbf{B}'\mathbf{y}$ (`NLAlib.mem_krylovSpace_iff`); it is
$\sum_{c'} (y_{c'} f)(\mathbf{A})\mathbf{b}'_{c'}$ (`Matrix.mulVec_sum`-type expansion,
`Polynomial.aeval_smul`), in the right side by `NLAlib.mem_blockKrylovSpace_iff`
(`Polynomial.degree_smul_le`). S, about 15 lines. -/
theorem blockKrylovSpace_le_of_range_le {𝕜 : Type*} [RCLike 𝕜] {n p p' : Type*} [Fintype n]
    [DecidableEq n] [Fintype p] [Fintype p'] {A : Matrix n n 𝕜} {B : Matrix n p 𝕜}
    {B' : Matrix n p' 𝕜} (h : LinearMap.range B.mulVecLin ≤ LinearMap.range B'.mulVecLin)
    (q : ℕ) : blockKrylovSpace A B q ≤ blockKrylovSpace A B' q := by
  classical
  rw [blockKrylovSpace_eq_iSup_krylovSpace]
  refine iSup_le fun c => ?_
  intro x hx
  obtain ⟨f, hf, rfl⟩ := mem_krylovSpace_iff.1 hx
  have hc : B.col c ∈ LinearMap.range B'.mulVecLin := h (by
    refine ⟨Pi.single c 1, ?_⟩
    rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_single_one B c])
  obtain ⟨y, hy⟩ := hc
  rw [Matrix.mulVecLin_apply] at hy
  have hsum : B' *ᵥ y = ∑ c', y c' • B'.col c' := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  refine mem_blockKrylovSpace_iff.2 ⟨fun c' => y c' • f, fun c' => ?_, ?_⟩
  · exact (Polynomial.degree_smul_le _ _).trans_lt hf
  · rw [← hy, hsum, Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun c' _ => ?_
    rw [map_smul, Matrix.smul_mulVec, Matrix.mulVec_smul]

/-- **One pass raises the Krylov depth by one**: if a subspace $\mathcal{L}$ lies in
$\mathcal{K}_{s+1}(\mathbf{A}, \mathbf{B})$ and $\mathcal{V} \subseteq \mathcal{L} +
\operatorname{range}\mathbf{B}$, then
$$\mathcal{L} + \mathcal{V} + \mathbf{A}\mathcal{V} \subseteq \mathcal{K}_{s+2}(\mathbf{A},
\mathbf{B}) \,.$$
The depth count of the Krylov coupling: $\mathcal{L}$ is what the earlier passes revealed,
$\mathcal{V}$ the rotated queries of the next pass and $\mathbf{A}\mathcal{V}$ their products.
Proof: $\mathcal{L} \le \mathcal{K}_{s+2}$ by `NLAlib.blockKrylovSpace_mono`;
$\operatorname{range}\mathbf{B} = \mathcal{K}_1 \le \mathcal{K}_{s+2}$
(`NLAlib.blockKrylovSpace_one`); for $\mathbf{A}\mathcal{V}$, `Submodule.map_le_iff_le_comap` and
`NLAlib.mulVec_mem_blockKrylovSpace_succ` on $\mathcal{K}_{s+1}$, which contains both
$\mathcal{L}$ and $\operatorname{range}\mathbf{B}$ (`sup_le`). S, about 12 lines. -/
theorem sup_sup_map_mulVecLin_le_blockKrylovSpace_add_two {𝕜 : Type*} [RCLike 𝕜] {n p : Type*}
    [Fintype n] [DecidableEq n] [Fintype p] {A : Matrix n n 𝕜} {B : Matrix n p 𝕜} {s : ℕ}
    {L V : Submodule 𝕜 (n → 𝕜)} (hL : L ≤ blockKrylovSpace A B (s + 1))
    (hV : V ≤ L ⊔ LinearMap.range B.mulVecLin) :
    L ⊔ V ⊔ V.map A.mulVecLin ≤ blockKrylovSpace A B (s + 2) := by
  have h1 : blockKrylovSpace A B (s + 1) ≤ blockKrylovSpace A B (s + 2) :=
    blockKrylovSpace_mono A B (by omega)
  have hB : LinearMap.range B.mulVecLin ≤ blockKrylovSpace A B (s + 1) := by
    rw [← blockKrylovSpace_one A B]
    exact blockKrylovSpace_mono A B (by omega)
  have hV' : V ≤ blockKrylovSpace A B (s + 1) := hV.trans (sup_le hL hB)
  refine sup_le (sup_le (hL.trans h1) (hV'.trans h1)) ?_
  rw [Submodule.map_le_iff_le_comap]
  intro x hx
  exact mulVec_mem_blockKrylovSpace_succ (hV' hx)

end NLAlib
