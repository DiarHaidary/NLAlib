/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.Dilation

/-!
# Residual bounds for the Lanczos dilation

The exchange identities bound the residual of the orthonormal dilation in terms of the original
recurrence residual and Gram commutator. Stacked estimates retain the isometry of the dilation.

## Main results

* `NLAlib.LanczosData.frobNorm_dilatedResidual_le_of_frobNorm_gramCommutator_le`: the stacked
  Frobenius-commutator estimate.
* `NLAlib.LanczosData.frobNorm_dilatedResidual_le_of_le`: its operator-commutator corollary.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

/-- The squared Frobenius norm of a matrix with rows indexed by blocks is the sum over the
blocks. -/
private theorem frobNorm_sq_eq_sum_submatrix {n m : ℕ} {p : Type*} [Fintype p]
    (M : Matrix (Fin n × Fin m) p ℝ) :
    frobNorm M ^ 2 = ∑ r, frobNorm (M.submatrix (fun i => (i, r)) id) ^ 2 := by
  simp only [frobNorm_sq_eq_sum_sq, Fintype.sum_prod_type, Matrix.submatrix_apply, id]
  exact Finset.sum_comm

namespace LanczosData

variable {n k : ℕ} (D : LanczosData n k)

private noncomputable def leadingC : Matrix (Fin k) (Fin k) ℝ :=
  (dilationC D.basisSucc).submatrix Fin.castSucc Fin.castSucc

private noncomputable def leadingK : Matrix (Fin k) (Fin k) ℝ :=
  (dilationK D.basisSucc).submatrix Fin.castSucc Fin.castSucc

private noncomputable def exchangeSource : Matrix (Fin (k + 1)) (Fin k) ℝ :=
  (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id Fin.castSucc *
    D.gramCommutator * leadingC D

private noncomputable def dilationBlock (r : ℕ) : Matrix (Fin n) (Fin (k + 1)) ℝ :=
  D.basisSucc * dilationC D.basisSucc * dilationK D.basisSucc ^ r

private noncomputable def shiftedDilation (s : ℕ) :
    Matrix (Fin n × Fin (k + 1)) (Fin (k + 1)) ℝ :=
  fun p j => if h : s < (p.2 : ℕ) then
    D.dilatedBasisSucc (p.1, ⟨(p.2 : ℕ) - s - 1, by omega⟩) j else 0

private theorem frobNorm_shiftedDilation_mul_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (s : ℕ)
    (B : Matrix (Fin (k + 1)) (Fin k) ℝ) :
    frobNorm (shiftedDilation D s * B) ≤ frobNorm B := by
  let f : Fin n × Fin (k + 1) → Fin n × Fin (k + 1) :=
    fun p => (p.1, ⟨(p.2 : ℕ) - s - 1, by omega⟩)
  let rows := Finset.univ.filter fun p : Fin n × Fin (k + 1) => s < (p.2 : ℕ)
  have hf : Set.InjOn f (rows : Set (Fin n × Fin (k + 1))) := by
    intro a ha b hb hab
    have ha' : s < (a.2 : ℕ) := (Finset.mem_filter.mp ha).2
    have hb' : s < (b.2 : ℕ) := (Finset.mem_filter.mp hb).2
    have h1 := congrArg (fun p : Fin n × Fin (k + 1) => p.1) hab
    change a.1 = b.1 at h1
    have h2 : a.2 = b.2 := by
      apply Fin.ext
      have := congrArg (fun p : Fin n × Fin (k + 1) => (p.2 : ℕ)) hab
      dsimp [f] at this
      omega
    exact Prod.ext h1 h2
  have hrow : ∀ i ∈ rows, ∀ j,
      (shiftedDilation D s * B) i j = (D.dilatedBasisSucc * B) (f i) j := by
    intro i hi j
    have hi' : s < (i.2 : ℕ) := (Finset.mem_filter.mp hi).2
    simp only [Matrix.mul_apply, shiftedDilation, dif_pos hi', f]
  have hzero : ∀ i ∉ rows, ∀ j, (shiftedDilation D s * B) i j = 0 := by
    intro i hi j
    have hi' : ¬s < (i.2 : ℕ) := by
      simpa only [rows, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    simp only [Matrix.mul_apply, shiftedDilation, dif_neg hi', zero_mul, Finset.sum_const_zero]
  exact (frobNorm_le_of_row_eq _ _ rows f hf hrow hzero).trans_eq
    ((D.hasOrthonormalCols_dilatedBasisSucc hW).frobNorm_mul_left B)

private theorem exchangeDefect_eq_sum (r : ℕ) :
    D.exchangeDefect r = ∑ s ∈ Finset.range r,
      dilationK D.basisSucc ^ (r - 1 - s) * D.exchangeDefect 1 *
        ((dilationK D.basisSucc).submatrix Fin.castSucc Fin.castSucc) ^ s := by
  have hK := isUpperTriangular_dilationK D.basisSucc
  induction r with
  | zero => simp only [D.exchangeDefect_zero, Finset.range_zero, Finset.sum_empty]
  | succ r ih =>
    rw [D.exchangeDefect_succ_eq_mul_add, ih, Matrix.mul_sum, hK.submatrix_castSucc_pow,
      Finset.sum_range_succ]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Matrix.one_mul]
    congr 1
    refine Finset.sum_congr rfl fun s hs => ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, ← pow_succ']
    have hs' := Finset.mem_range.mp hs
    have he : r - 1 - s + 1 = r - s := by omega
    rw [he]

private theorem specNorm_leadingC_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) : specNorm (leadingC D) ≤ 2 :=
  (specNorm_submatrix_le _ (Fin.castSucc_injective k) (Fin.castSucc_injective k)).trans
    (specNorm_dilationC_le_two hW)

private theorem specNorm_leadingK_pow_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) (r : ℕ) :
    specNorm (leadingK D ^ r) ≤ 1 := by
  have hK : specNorm (leadingK D) ≤ 1 :=
    (specNorm_submatrix_le _ (Fin.castSucc_injective k) (Fin.castSucc_injective k)).trans
      (specNorm_dilationK_le_one hW)
  exact (specNorm_pow_le _ r).trans (pow_le_one₀ (specNorm_nonneg _) hK)

private theorem frobNorm_exchangeSource_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    frobNorm (exchangeSource D) ≤ 2 * frobNorm D.gramCommutator := by
  have hJ : HasOrthonormalCols ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix
      id Fin.castSucc) :=
    hasOrthonormalCols_one.submatrix (Equiv.refl _) (Fin.castSucc_injective k)
  unfold exchangeSource
  refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans ?_
  rw [hJ.frobNorm_mul_left]
  have hC := specNorm_leadingC_le D hW
  nlinarith [frobNorm_nonneg D.gramCommutator]

private theorem basisSucc_mul_exchangeDefect (r : ℕ) :
    D.basisSucc * D.exchangeDefect r = ∑ s ∈ Finset.range r,
      dilationBlock D (r - 1 - s) * (exchangeSource D * leadingK D ^ s) := by
  rw [exchangeDefect_eq_sum, Matrix.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [D.exchangeDefect_one, D.tridiagonalSucc_mul_sub_eq]
  have hCK := ((commute_dilationC_dilationK D.basisSucc).pow_right (r - 1 - s)).eq
  change D.basisSucc * (dilationK D.basisSucc ^ (r - 1 - s) *
      (dilationC D.basisSucc *
        ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id Fin.castSucc *
          D.gramCommutator) * leadingC D) * leadingK D ^ s) = _
  calc _ = (D.basisSucc * (dilationK D.basisSucc ^ (r - 1 - s) *
        dilationC D.basisSucc)) * (exchangeSource D * leadingK D ^ s) := by
          simp only [exchangeSource, Matrix.mul_assoc]
    _ = (D.basisSucc * (dilationC D.basisSucc *
        dilationK D.basisSucc ^ (r - 1 - s))) * (exchangeSource D * leadingK D ^ s) := by
          rw [hCK]
    _ = _ := by simp only [dilationBlock, Matrix.mul_assoc]

private theorem leadingC_eq_one_sub : leadingC D = 1 - leadingK D := by
  ext i j
  by_cases hij : i = j <;>
    simp [leadingC, leadingK, dilationK, Matrix.submatrix_apply, Matrix.sub_apply,
      hij, Fin.castSucc_inj]

private theorem basisSucc_mul_exchangeDefect_sub (r : ℕ) :
    D.basisSucc * (D.exchangeDefect r - D.exchangeDefect (r + 1)) =
      (∑ s ∈ Finset.range r, dilationBlock D (r - 1 - s) *
        (exchangeSource D * leadingK D ^ s * leadingC D)) -
      dilationBlock D r * exchangeSource D := by
  have hCK := ((commute_dilationC_dilationK D.basisSucc).pow_right r).eq
  have hY : D.basisSucc * (dilationK D.basisSucc ^ r * D.exchangeDefect 1) =
      dilationBlock D r * exchangeSource D := by
    rw [D.exchangeDefect_one, D.tridiagonalSucc_mul_sub_eq]
    change D.basisSucc * (dilationK D.basisSucc ^ r *
      (dilationC D.basisSucc *
        ((1 : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ).submatrix id Fin.castSucc *
          D.gramCommutator) * leadingC D)) = _
    calc _ = (D.basisSucc * (dilationK D.basisSucc ^ r * dilationC D.basisSucc)) *
        exchangeSource D := by simp only [exchangeSource, Matrix.mul_assoc]
      _ = _ := by rw [← hCK]; simp only [dilationBlock, Matrix.mul_assoc]
  calc _ = (D.basisSucc * D.exchangeDefect r) * leadingC D -
        dilationBlock D r * exchangeSource D := by
          rw [D.exchangeDefect_succ, Matrix.mul_sub, Matrix.mul_add, hY]
          change D.basisSucc * D.exchangeDefect r -
            (D.basisSucc * (D.exchangeDefect r * leadingK D) +
              dilationBlock D r * exchangeSource D) = _
          rw [leadingC_eq_one_sub, Matrix.mul_sub, Matrix.mul_one]
          simp only [Matrix.mul_assoc]
          abel
    _ = _ := by
      rw [basisSucc_mul_exchangeDefect, Matrix.sum_mul]
      simp only [Matrix.mul_assoc]

private noncomputable def residualStack : Matrix (Fin n × Fin (k + 1)) (Fin k) ℝ :=
  fun p j => (D.residual * (dilationC D.basisSucc *
    dilationK D.basisSucc ^ (p.2 : ℕ)).submatrix Fin.castSucc Fin.castSucc) p.1 j

private theorem frobNorm_residualStack_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1) :
    frobNorm (residualStack D) ≤ 2 * Real.sqrt (k + 1) * frobNorm D.residual := by
  have hb (r : Fin (k + 1)) :
      frobNorm ((residualStack D).submatrix (fun i => (i, r)) id) ≤
        2 * frobNorm D.residual := by
    have hCK : specNorm ((dilationC D.basisSucc *
        dilationK D.basisSucc ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc) ≤ 2 := by
      refine (specNorm_submatrix_le _ (Fin.castSucc_injective k)
        (Fin.castSucc_injective k)).trans ((specNorm_mul_le _ _).trans ?_)
      have hp : specNorm (dilationK D.basisSucc ^ (r : ℕ)) ≤ 1 :=
        (specNorm_pow_le _ _).trans (pow_le_one₀ (specNorm_nonneg _)
          (specNorm_dilationK_le_one hW))
      nlinarith [specNorm_dilationC_le_two hW, specNorm_nonneg (dilationC D.basisSucc)]
    change frobNorm (D.residual * (dilationC D.basisSucc *
      dilationK D.basisSucc ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc) ≤ _
    exact (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (by nlinarith [frobNorm_nonneg D.residual])
  apply (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).mp
  rw [frobNorm_sq_eq_sum_submatrix]
  calc _ ≤ ∑ _r : Fin (k + 1), (2 * frobNorm D.residual) ^ 2 :=
      Finset.sum_le_sum fun r _ => pow_le_pow_left₀ (frobNorm_nonneg _) (hb r) 2
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      simp only [mul_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (k : ℝ) + 1)]
      push_cast
      ring

private theorem shiftedDilation_mul_apply (s : ℕ) (r : Fin (k + 1))
    (B : Matrix (Fin (k + 1)) (Fin k) ℝ) (i : Fin n) (j : Fin k) :
    (shiftedDilation D s * B) (i, r) j =
      if s < (r : ℕ) then (dilationBlock D ((r : ℕ) - 1 - s) * B) i j else 0 := by
  by_cases h : s < (r : ℕ)
  · have he : (r : ℕ) - s - 1 = (r : ℕ) - 1 - s := by omega
    simp [Matrix.mul_apply, shiftedDilation, h, dilatedBasisSucc,
      orthonormalDilation, dilationBlock, he]
  · simp [Matrix.mul_apply, shiftedDilation, h]

private theorem dilatedResidual_eq_sum :
    D.dilatedResidual = residualStack D +
      (∑ s ∈ Finset.range k, shiftedDilation D s *
        (exchangeSource D * leadingK D ^ s * leadingC D)) -
      D.dilatedBasisSucc * exchangeSource D := by
  ext ⟨i, r⟩ j
  have hr : (r : ℕ) ≤ k := Nat.lt_succ_iff.mp r.2
  have hsum :
      ∑ s ∈ Finset.range k, (shiftedDilation D s *
        (exchangeSource D * leadingK D ^ s * leadingC D)) (i, r) j =
      ∑ s ∈ Finset.range (r : ℕ), (dilationBlock D ((r : ℕ) - 1 - s) *
        (exchangeSource D * leadingK D ^ s * leadingC D)) i j := by
    simp_rw [shiftedDilation_mul_apply]
    rw [← Finset.sum_filter]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  have hb := congrArg (fun A : Matrix (Fin n) (Fin k) ℝ => A i j)
    (D.dilatedResidual_submatrix r)
  rw [basisSucc_mul_exchangeDefect_sub] at hb
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.sum_apply]
  rw [hsum]
  have htail : (D.dilatedBasisSucc * exchangeSource D) (i, r) j =
      (dilationBlock D (r : ℕ) * exchangeSource D) i j := rfl
  rw [htail]
  simp only [Matrix.submatrix_apply, id, Matrix.add_apply, Matrix.sub_apply,
    Matrix.sum_apply] at hb
  change D.dilatedResidual (i, r) j =
    (D.residual * (dilationC D.basisSucc *
      dilationK D.basisSucc ^ (r : ℕ)).submatrix Fin.castSucc Fin.castSucc) i j + _ - _
  rw [hb]
  abel


/-- **The stacked dilated recurrence**: for unit columns,
$\|\mathbf{F}_k\|_{\mathsf{F}} \le F$ and
$\|\mathbf{M}_k\|_{\mathsf{F}} \le G$ imply
$$\|\hat{\mathbf{E}}\|_{\mathsf{F}}
\le 2\sqrt{k+1}\,F + (4k+2)G \,.$$
No printed source. A shifted-stack estimate for the orthonormal dilation. -/
theorem frobNorm_dilatedResidual_le_of_frobNorm_gramCommutator_le
    (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1)
    {F G : ℝ} (hF : frobNorm D.residual ≤ F) (hG : frobNorm D.gramCommutator ≤ G) :
    frobNorm D.dilatedResidual ≤
      2 * Real.sqrt (k + 1) * F + (4 * k + 2) * G := by
  have hterm (s : ℕ) : frobNorm (shiftedDilation D s *
      (exchangeSource D * leadingK D ^ s * leadingC D)) ≤
      4 * frobNorm D.gramCommutator := by
    refine (frobNorm_shiftedDilation_mul_le D hW s
      (exchangeSource D * leadingK D ^ s * leadingC D)).trans ?_
    have h1 := frobNorm_mul_le_frobNorm_mul_specNorm
      (exchangeSource D) (leadingK D ^ s)
    have h2 := frobNorm_mul_le_frobNorm_mul_specNorm
      (exchangeSource D * leadingK D ^ s) (leadingC D)
    have hb := frobNorm_exchangeSource_le D hW
    have hk := specNorm_leadingK_pow_le D hW s
    have hc := specNorm_leadingC_le D hW
    have he : frobNorm (exchangeSource D * leadingK D ^ s) ≤
        frobNorm (exchangeSource D) :=
      h1.trans (by nlinarith only [hk, frobNorm_nonneg (exchangeSource D)])
    calc _ ≤ frobNorm (exchangeSource D * leadingK D ^ s) * 2 :=
        h2.trans (mul_le_mul_of_nonneg_left hc (frobNorm_nonneg _))
      _ ≤ _ := by linarith only [he, hb]
  have hsum : frobNorm (∑ s ∈ Finset.range k, shiftedDilation D s *
      (exchangeSource D * leadingK D ^ s * leadingC D)) ≤
      k * (4 * frobNorm D.gramCommutator) := by
    refine (frobNorm_sum_le (Finset.range k) (fun s => shiftedDilation D s *
      (exchangeSource D * leadingK D ^ s * leadingC D))).trans ?_
    calc _ ≤ ∑ _s ∈ Finset.range k, 4 * frobNorm D.gramCommutator :=
        Finset.sum_le_sum fun s _ => hterm s
      _ = _ := by simp
  have htail : frobNorm (D.dilatedBasisSucc * exchangeSource D) ≤
      2 * frobNorm D.gramCommutator := by
    rw [(D.hasOrthonormalCols_dilatedBasisSucc hW).frobNorm_mul_left]
    exact frobNorm_exchangeSource_le D hW
  let S := ∑ s ∈ Finset.range k, shiftedDilation D s *
    (exchangeSource D * leadingK D ^ s * leadingC D)
  let T := D.dilatedBasisSucc * exchangeSource D
  have htri := frobNorm_sub_le (residualStack D + S) T
  have hadd := frobNorm_add_le (residualStack D) S
  have hid : D.dilatedResidual = residualStack D + S - T := dilatedResidual_eq_sum D
  rw [hid]
  change frobNorm S ≤ _ at hsum
  change frobNorm T ≤ _ at htail
  have hraw := frobNorm_residualStack_le D hW
  have hF' : 2 * Real.sqrt (k + 1) * frobNorm D.residual ≤
      2 * Real.sqrt (k + 1) * F := by gcongr
  have hG' : (4 * (k : ℝ) + 2) * frobNorm D.gramCommutator ≤
      (4 * k + 2) * G := by gcongr
  nlinarith only [htri, hadd, hraw, hsum, htail, hF', hG']

/-- **The dilated recurrence, from the residual and the Gram commutator**: for unit vectors,
$\|\mathbf{F}_k\|_{\mathsf{F}} \le F$ and $\|\mathbf{M}_k\|_2 \le G$,
$$\|\hat{\mathbf{E}}\|_{\mathsf{F}} \le 2\sqrt{k+1}\,F + 4(k+1)(2k+1)\,G \,.$$
No printed source; the maintainer's draft, `lem:exchange` and `lem:dilated-recurrence`. -/
theorem frobNorm_dilatedResidual_le_of_le (hW : ∀ j, (D.basisSuccᵀ * D.basisSucc) j j = 1)
    {F G : ℝ} (hF : frobNorm D.residual ≤ F) (hG : specNorm D.gramCommutator ≤ G) :
    frobNorm D.dilatedResidual ≤
      2 * Real.sqrt (k + 1) * F + 4 * ((k + 1) * (2 * k + 1)) * G := by
  have hG0 : 0 ≤ G := (specNorm_nonneg _).trans hG
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast D.k_pos
  have hs : Real.sqrt (k : ℝ) ≤ k := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith
  have hGF := frobNorm_le_sqrt_card_mul_specNorm D.gramCommutator
  simp only [Fintype.card_fin] at hGF
  have hGF' : frobNorm D.gramCommutator ≤ Real.sqrt k * G :=
    hGF.trans (mul_le_mul_of_nonneg_left hG (Real.sqrt_nonneg _))
  have hE := D.frobNorm_dilatedResidual_le_of_frobNorm_gramCommutator_le hW hF hGF'
  refine hE.trans ?_
  have hc : (4 * (k : ℝ) + 2) * k ≤ 4 * ((k + 1) * (2 * k + 1)) := by
    nlinarith
  have hc' : (4 * (k : ℝ) + 2) * (Real.sqrt k * G) ≤
      4 * ((k + 1) * (2 * k + 1)) * G := by
    calc _ ≤ ((4 * k + 2) * k) * G := by nlinarith [mul_le_mul_of_nonneg_right hs hG0]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc hG0
  linarith

end LanczosData

end NLAlib
