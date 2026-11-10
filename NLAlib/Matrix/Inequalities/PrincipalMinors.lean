/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Inequalities.Determinant

/-!
# Principal minors of positive semidefinite matrices

For a positive semidefinite matrix, the products of all principal minors
(`NLAlib.principalMinor`) of a given size satisfy Szász's chain of inequalities, which
interpolates between $\det \mathbf{A}$ and Hadamard's bound $\prod_i \mathbf{A}_{i,i}$. The
determinant of a compression $\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V}$ by a matrix with
orthonormal columns, of which a principal minor is the case of a coordinate selection, is at most
the product of the leading eigenvalues.

## Main results

* `Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase`: a minor against its sub-minors of one
  size less.
* `Matrix.PosSemidef.prod_re_principalMinor_succ_pow_le`,
  `Matrix.PosSemidef.prod_re_principalMinor_rpow_le`: integer-power and normalized Szász bounds.
* `Matrix.PosDef.prod_re_principalMinor_rpow_eq_iff`: equality between consecutive normalized
  products for positive definite matrices.
* `NLAlib.principalMinor_erase_univ_eq_adjugate`, `NLAlib.principalMinor_erase_univ_eq`:
  complementary minors as the diagonal of the adjugate and of the inverse.
* `Matrix.PosSemidef.re_det_conjTranspose_mul_mul_le_prod_range_eigenvalue`: the determinant of a
  compression against the leading eigenvalues.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- **A complementary minor is a diagonal entry of the adjugate.** Over any commutative ring, the
principal minor on the complement of an index $i$ is $(\operatorname{adj} \mathbf{A})_{i,i}$.
[HornJohnson2013, §0.8.2]. -/
theorem principalMinor_erase_univ_eq_adjugate {R : Type*} [CommRing R] (A : Matrix n n R)
    (i : n) : principalMinor A (Finset.univ.erase i) = A.adjugate i i := by
  rw [Matrix.adjugate_apply, principalMinor, ← Matrix.det_piecewise_one_eq_submatrix_det]
  congr 1
  ext a b
  by_cases ha : a = i
  · subst ha
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  · simp [ha]

/-- **Complementary minors and the inverse.** For an invertible matrix over a field, the
principal minor on the complement of an index $i$ is $\det \mathbf{A} \cdot
(\mathbf{A}^{-1})_{i,i}$.
[HornJohnson2013, §0.8.4]. -/
theorem principalMinor_erase_univ_eq {K : Type*} [Field K] {A : Matrix n n K} (hA : IsUnit A)
    (i : n) : principalMinor A (Finset.univ.erase i) = A.det * A⁻¹ i i := by
  have hdet : A.det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det A).mp hA).ne_zero
  rw [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ hdet, one_mul, principalMinor_erase_univ_eq_adjugate]

/-- The case of the whole index set of `Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase`,
for a positive definite matrix: Hadamard's inequality for the inverse. -/
private theorem re_det_pow_le_prod_erase_and_eq_iff {A : Matrix n n 𝕜} (hA : A.PosDef) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    RCLike.re A.det ^ k ≤ ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) ∧
      (RCLike.re A.det ^ k = ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) ↔
        A.IsDiag) := by
  have hd : 0 < RCLike.re A.det := (RCLike.pos_iff.mp hA.det_pos).1
  have hinv : RCLike.re A⁻¹.det = (RCLike.re A.det)⁻¹ := by
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv', hA.isHermitian.det_eq_re_det,
      ← RCLike.ofReal_inv, RCLike.ofReal_re, RCLike.ofReal_re]
  have hterm (i : n) : RCLike.re (principalMinor A (Finset.univ.erase i)) =
      RCLike.re A.det * RCLike.re (A⁻¹ i i) := by
    rw [principalMinor_erase_univ_eq hA.isUnit, hA.isHermitian.det_eq_re_det,
      RCLike.re_ofReal_mul, RCLike.ofReal_re]
  simp only [hterm]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← hk]
  have hdet : RCLike.re A.det ^ k = RCLike.re A.det ^ (k + 1) * RCLike.re A⁻¹.det := by
    rw [hinv, pow_succ, mul_assoc, mul_inv_cancel₀ hd.ne', mul_one]
  rw [hdet, mul_le_mul_iff_right₀ (pow_pos hd _), mul_right_inj' (pow_pos hd _).ne',
    hA.inv.re_det_eq_prod_re_diag_iff]
  refine ⟨hA.inv.posSemidef.re_det_le_prod_re_diag, ?_⟩
  have hinvDiag {M : Matrix n n 𝕜} (h : M.IsDiag) : M⁻¹.IsDiag := by
    rw [← h.diagonal_diag, Matrix.inv_diagonal]
    exact Matrix.isDiag_diagonal _
  have hinv := Matrix.nonsing_inv_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).1 hA.isUnit)
  exact ⟨fun h => hinv ▸ hinvDiag h, hinvDiag⟩

/-- The case of the whole index set of `Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase`,
by continuity from the positive definite case. -/
private theorem re_det_pow_le_prod_erase {A : Matrix n n 𝕜} (hA : A.PosSemidef) {k : ℕ}
    (hk : k + 1 = Fintype.card n) :
    RCLike.re A.det ^ k ≤ ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) :=
  Matrix.PosSemidef.le_of_forall_posDef_le
    (f := fun A : Matrix n n 𝕜 => RCLike.re A.det ^ k)
    (g := fun A : Matrix n n 𝕜 => ∏ i, RCLike.re
      (A.submatrix (Subtype.val : ↥(Finset.univ.erase i) → n) Subtype.val).det)
    (by fun_prop) (by fun_prop) (fun _ hM => (re_det_pow_le_prod_erase_and_eq_iff hM hk).1) hA

omit [Fintype n] in
private theorem principalMinor_submatrix_erase (A : Matrix n n 𝕜) (t : Finset n) (i : t) :
    principalMinor (A.submatrix (Subtype.val : ↥t → n) Subtype.val) (Finset.univ.erase i) =
      principalMinor A (t.erase i) := by
  rw [principalMinor, Matrix.submatrix_submatrix]
  refine det_submatrix_eq_principalMinor A
    (Subtype.val_injective.comp Subtype.val_injective) (Set.ext fun x => ?_)
  simp only [Finset.coe_erase, Set.mem_sdiff, Finset.mem_coe, Set.mem_singleton_iff,
    Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    exact ⟨y.2, fun h => (Finset.mem_erase.mp hy).1 (Subtype.ext h)⟩
  · rintro ⟨hxt, hx⟩
    exact ⟨⟨⟨x, hxt⟩, by simpa [Subtype.ext_iff] using hx⟩, rfl⟩

omit [Fintype n] in
/-- **A minor against its sub-minors.** For a positive semidefinite matrix $\mathbf{A}$ and an
index set $t$ with $k + 1$ elements, writing $\det \mathbf{A}_{s,s}$ for the principal minor on $s$,
$$(\operatorname{Re} \det \mathbf{A}_{t,t})^k
  \le \prod_{i \in t} \operatorname{Re} \det \mathbf{A}_{t \setminus \{i\}, t \setminus \{i\}}\,.$$
[HornJohnson2013, Theorem 7.8.11 (step)]. -/
theorem _root_.Matrix.PosSemidef.re_principalMinor_pow_le_prod_erase {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {t : Finset n} {k : ℕ} (hk : t.card = k + 1) :
    RCLike.re (principalMinor A t) ^ k ≤ ∏ i ∈ t, RCLike.re (principalMinor A (t.erase i)) := by
  have h := re_det_pow_le_prod_erase (hA.submatrix (Subtype.val : ↥t → n)) (k := k)
    (by rw [Fintype.card_coe, hk])
  simp only [principalMinor_submatrix_erase] at h
  rw [Finset.prod_coe_sort t fun i => RCLike.re (principalMinor A (t.erase i))] at h
  exact h

omit [Fintype n] in
/-- Equality in the deletion inequality for a principal block of size $k+1$ in a positive
definite matrix holds exactly when that block is diagonal. [HornJohnson2013, Lemma 7.8.8]. -/
theorem _root_.Matrix.PosDef.re_principalMinor_pow_eq_prod_erase_iff {A : Matrix n n 𝕜}
    (hA : A.PosDef) {t : Finset n} {k : ℕ} (hk : t.card = k + 1) :
    RCLike.re (principalMinor A t) ^ k = ∏ i ∈ t, RCLike.re (principalMinor A (t.erase i)) ↔
      (A.submatrix (Subtype.val : t → n) Subtype.val).IsDiag := by
  have hpd := hA.submatrix (Subtype.val_injective (p := (· ∈ t)))
  have h := (re_det_pow_le_prod_erase_and_eq_iff hpd (k := k) (by rw [Fintype.card_coe, hk])).2
  simp only [principalMinor_submatrix_erase] at h
  rw [Finset.prod_coe_sort t fun i => RCLike.re (principalMinor A (t.erase i))] at h
  exact h

/-- Multiplying a function over every one-element deletion of every subset with $k + 1$
elements counts each subset with $k$ elements once for each element outside it. -/
private theorem prod_powersetCard_prod_erase {M : Type*} [CommMonoid M] (f : Finset n → M)
    {k d : ℕ} (hkd : k + d = Fintype.card n) :
    ∏ t ∈ Finset.univ.powersetCard (k + 1), ∏ i ∈ t, f (t.erase i) =
      (∏ s ∈ Finset.univ.powersetCard k, f s) ^ d := by
  have hprod : ∏ u ∈ (Finset.univ.powersetCard (k + 1)).sigma (fun t : Finset n => t),
      f (u.1.erase u.2) =
      ∏ v ∈ (Finset.univ.powersetCard k).sigma (fun s : Finset n => Finset.univ \ s), f v.1 := by
    refine Finset.prod_bij' (fun u _ => ⟨u.1.erase u.2, u.2⟩)
      (fun v _ => ⟨insert v.2 v.1, v.2⟩) ?_ ?_ ?_ ?_ ?_
    · intro u hu
      obtain ⟨ht, hi⟩ := Finset.mem_sigma.mp hu
      have hcard := (Finset.mem_powersetCard.mp ht).2
      refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩, ?_⟩
      · rw [Finset.card_erase_of_mem hi, hcard, Nat.add_sub_cancel]
      · simp
    · intro v hv
      obtain ⟨hs, hi⟩ := Finset.mem_sigma.mp hv
      have hcard := (Finset.mem_powersetCard.mp hs).2
      have hnot : v.2 ∉ v.1 := (Finset.mem_sdiff.mp hi).2
      refine Finset.mem_sigma.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩,
        Finset.mem_insert_self _ _⟩
      rw [Finset.card_insert_of_notMem hnot, hcard]
    · intro u hu
      exact Sigma.ext (Finset.insert_erase (Finset.mem_sigma.mp hu).2) HEq.rfl
    · intro v hv
      exact Sigma.ext
        (Finset.erase_insert (Finset.mem_sdiff.mp (Finset.mem_sigma.mp hv).2).2) HEq.rfl
    · intro u _
      rfl
  rw [Finset.prod_sigma', hprod, Finset.prod_sigma, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun s hs => ?_
  change ∏ _i ∈ Finset.univ \ s, f s = _
  rw [Finset.prod_const, Finset.card_sdiff_of_subset (Finset.subset_univ s), Finset.card_univ,
    (Finset.mem_powersetCard.mp hs).2, ← hkd, Nat.add_sub_cancel_left]

/-- **Szász's inequality.** For a positive semidefinite $N \times N$ matrix $\mathbf{A}$, let
$P_k$ be the product of the principal minors $\operatorname{Re} \det \mathbf{A}_{s,s}$ over all
index sets $s$ with $k$ elements ($P_0 = 1$). Then $P_{k+1}^k \le P_k^{N-k}$ for $k \le N$, stated
with $k + d = N$ and exponent $d$.
[HornJohnson2013, Theorem 7.8.11].
Result: szasz-inequality -/
theorem _root_.Matrix.PosSemidef.prod_re_principalMinor_succ_pow_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k d : ℕ} (hkd : k + d = Fintype.card n) :
    (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^ k ≤
      (∏ s ∈ Finset.univ.powersetCard k, RCLike.re (principalMinor A s)) ^ d := by
  rw [← Finset.prod_pow, ← prod_powersetCard_prod_erase _ hkd]
  exact Finset.prod_le_prod (fun s _ => pow_nonneg (hA.re_principalMinor_nonneg s) k)
    fun s hs => hA.re_principalMinor_pow_le_prod_erase (Finset.mem_powersetCard.mp hs).2

/-- The case $k + 1 = N$ of Szász's inequality, for positive semidefinite $\mathbf{A}$ of size
$N$: $(\operatorname{Re} \det \mathbf{A})^{N-1}
\le \prod_i \operatorname{Re} \det \mathbf{A}_{\{i\}^{c}, \{i\}^{c}}$, with $\{i\}^{c}$ the
complement of $i$.
[HornJohnson2013, Theorem 7.8.11]. -/
theorem _root_.Matrix.PosSemidef.re_det_pow_le_prod_re_principalMinor_erase {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {k : ℕ} (hk : k + 1 = Fintype.card n) :
    RCLike.re A.det ^ k ≤ ∏ i, RCLike.re (principalMinor A (Finset.univ.erase i)) :=
  re_det_pow_le_prod_erase hA hk

/-- A positive definite matrix attains equality between consecutive nontrivial orders in
Szász's product inequality exactly when it is diagonal. [HornJohnson2013, Theorem 7.8.11]. -/
theorem _root_.Matrix.PosDef.prod_re_principalMinor_succ_pow_eq_iff {A : Matrix n n 𝕜}
    (hA : A.PosDef) {k d : ℕ} (hk : 0 < k) (hd : 0 < d) (hkd : k + d = Fintype.card n) :
    (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^ k =
      (∏ s ∈ Finset.univ.powersetCard k, RCLike.re (principalMinor A s)) ^ d ↔ A.IsDiag := by
  rw [← Finset.prod_pow, ← prod_powersetCard_prod_erase _ hkd]
  have hloc (t : Finset n) (ht : t ∈ (Finset.univ : Finset n).powersetCard (k + 1)) :=
    hA.re_principalMinor_pow_eq_prod_erase_iff (Finset.mem_powersetCard.mp ht).2
  constructor
  · intro he i j hij
    obtain ⟨t, hpair, -, hcard⟩ := Finset.exists_subsuperset_card_eq
      (Finset.subset_univ ({i, j} : Finset n))
      (show ({i, j} : Finset n).card ≤ k + 1 by simp [hij]; omega)
      (show k + 1 ≤ (Finset.univ : Finset n).card by rw [Finset.card_univ]; omega)
    have ht : t ∈ (Finset.univ : Finset n).powersetCard (k + 1) :=
      Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hcard⟩
    have heq : (A.submatrix (Subtype.val : t → n) Subtype.val).IsDiag := by
      by_contra hnot
      have hlt := lt_of_le_of_ne (hA.posSemidef.re_principalMinor_pow_le_prod_erase hcard)
        (fun h => hnot ((hloc t ht).mp h))
      exact (Finset.prod_lt_prod (fun s _ => pow_pos (hA.re_principalMinor_pos s) k)
        (fun s hs => hA.posSemidef.re_principalMinor_pow_le_prod_erase
          (Finset.mem_powersetCard.mp hs).2) ⟨t, ht, hlt⟩).ne he
    exact heq (i := ⟨i, hpair (by simp)⟩) (j := ⟨j, hpair (by simp)⟩)
      fun h => hij (congrArg Subtype.val h)
  · intro h
    exact Finset.prod_congr rfl fun t ht => (hloc t ht).mpr (h.submatrix Subtype.val_injective)

/-- The binomial coefficients convert consecutive normalized products to integer powers. -/
private theorem rpow_inv_choose_compare {d k l : ℕ} (hd : k + 1 + l = d)
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (y ^ ((d.choose (k + 1) : ℝ)⁻¹) ≤ x ^ ((d.choose k : ℝ)⁻¹) ↔
      y ^ (k + 1) ≤ x ^ (l + 1)) ∧
    (y ^ ((d.choose (k + 1) : ℝ)⁻¹) = x ^ ((d.choose k : ℝ)⁻¹) ↔
      y ^ (k + 1) = x ^ (l + 1)) := by
  have hp : (0 : ℝ) < d.choose k := by exact_mod_cast Nat.choose_pos (show k ≤ d by omega)
  have hq : (0 : ℝ) < d.choose (k + 1) := by
    exact_mod_cast Nat.choose_pos (show k + 1 ≤ d by omega)
  have hratio : ((k + 1 : ℕ) : ℝ) * (d.choose (k + 1) : ℝ) =
      ((l + 1 : ℕ) : ℝ) * (d.choose k : ℝ) := by
    have h := Nat.choose_succ_right_eq d k
    rw [show d - k = l + 1 by omega] at h
    have hnat : (k + 1) * d.choose (k + 1) = (l + 1) * d.choose k := by
      simpa only [mul_comm] using h
    exact_mod_cast hnat
  let e := ((k + 1 : ℕ) : ℝ) * (d.choose (k + 1) : ℝ)
  have he : 0 < e := mul_pos (by positivity) hq
  have hy' : (y ^ ((d.choose (k + 1) : ℝ)⁻¹)) ^ e = y ^ (k + 1) := by
    rw [← Real.rpow_mul hy]
    have : ((d.choose (k + 1) : ℝ)⁻¹) * e = ((k + 1 : ℕ) : ℝ) := by dsimp [e]; field_simp
    rw [this, Real.rpow_natCast]
  have hx' : (x ^ ((d.choose k : ℝ)⁻¹)) ^ e = x ^ (l + 1) := by
    rw [← Real.rpow_mul hx]
    have : ((d.choose k : ℝ)⁻¹) * e = ((l + 1 : ℕ) : ℝ) := by
      dsimp only [e]
      rw [hratio]
      field_simp
    rw [this, Real.rpow_natCast]
  have hle := Real.rpow_le_rpow_iff (Real.rpow_nonneg hy (d.choose (k + 1) : ℝ)⁻¹)
    (Real.rpow_nonneg hx (d.choose k : ℝ)⁻¹) he
  have heq := Real.rpow_left_inj (Real.rpow_nonneg hy (d.choose (k + 1) : ℝ)⁻¹)
    (Real.rpow_nonneg hx (d.choose k : ℝ)⁻¹) he.ne'
  rw [hy', hx'] at hle heq
  exact ⟨hle.symm, heq.symm⟩

/-- **Normalized Szász inequality.** For a positive semidefinite matrix of dimension $d+1$,
the product of principal minors of order $j+1$, raised to $1/\binom{d}{j}$, decreases with
$j$ throughout $0\le j\le d$. [HornJohnson2013, Theorem 7.8.11].
Result: szasz-inequality -/
theorem _root_.Matrix.PosSemidef.prod_re_principalMinor_rpow_le {A : Matrix n n 𝕜}
    (hA : A.PosSemidef) {d k l : ℕ} (hd : Fintype.card n = d + 1) (hkl : k ≤ l) (hl : l ≤ d) :
    (∏ s ∈ Finset.univ.powersetCard (l + 1), RCLike.re (principalMinor A s)) ^
        ((d.choose l : ℝ)⁻¹) ≤
      (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^
        ((d.choose k : ℝ)⁻¹) := by
  revert hl
  induction l, hkl using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ l hkl ih =>
    intro hl
    obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hl
    refine le_trans ?_ (ih (by omega))
    apply (rpow_inv_choose_compare hr.symm
      (Finset.prod_nonneg fun s _ => hA.re_principalMinor_nonneg s)
      (Finset.prod_nonneg fun s _ => hA.re_principalMinor_nonneg s)).1.mpr
    exact hA.prod_re_principalMinor_succ_pow_le (k := l + 1) (d := r + 1) (by omega)

/-- For positive definite input, consecutive normalized Szász products at orders $k+1$ and
$k+2$ coincide precisely when the matrix is diagonal. [HornJohnson2013, Theorem 7.8.11]. -/
theorem _root_.Matrix.PosDef.prod_re_principalMinor_rpow_eq_iff {A : Matrix n n 𝕜}
    (hA : A.PosDef) {d k : ℕ} (hd : Fintype.card n = d + 1) (hk : k < d) :
    (∏ s ∈ Finset.univ.powersetCard (k + 2), RCLike.re (principalMinor A s)) ^
        ((d.choose (k + 1) : ℝ)⁻¹) =
      (∏ s ∈ Finset.univ.powersetCard (k + 1), RCLike.re (principalMinor A s)) ^
        ((d.choose k : ℝ)⁻¹) ↔ A.IsDiag := by
  obtain ⟨r, hr⟩ := Nat.exists_eq_add_of_le hk
  rw [(rpow_inv_choose_compare hr.symm
    (Finset.prod_nonneg fun s _ => hA.posSemidef.re_principalMinor_nonneg s)
    (Finset.prod_nonneg fun s _ => hA.posSemidef.re_principalMinor_nonneg s)).2]
  exact hA.prod_re_principalMinor_succ_pow_eq_iff (k := k + 1) (d := r + 1) (by omega)
    (by omega) (by omega)

/-! ### Compressions -/

omit [DecidableEq n] in
/-- **The determinant of a compression is at most the product of the leading eigenvalues.** For
positive semidefinite $\mathbf{A}$ and $\mathbf{V}$ with orthonormal columns indexed by $p$,
$$\operatorname{Re} \det(\mathbf{V}^{\mathsf{H}}\mathbf{A}\mathbf{V})
  \le \prod_{i < \lvert p \rvert} \lambda_i(\mathbf{A})\,,$$
eigenvalues non-increasing and indexed from $0$. With no columns both sides are $1$.
[HornJohnson2013, Corollary 4.3.37]; a consequence of the Poincaré separation theorem. -/
theorem _root_.Matrix.PosSemidef.re_det_conjTranspose_mul_mul_le_prod_range_eigenvalue
    {p : Type*} [Fintype p] [DecidableEq p] {A : Matrix n n 𝕜} (hA : A.PosSemidef)
    {V : Matrix n p 𝕜} (hV : HasOrthonormalCols V) :
    RCLike.re (Vᴴ * A * V).det ≤ ∏ i ∈ Finset.range (Fintype.card p), eigenvalue A i := by
  have hB : (Vᴴ * A * V).PosSemidef := hA.conjTranspose_mul_mul_same V
  rw [hB.isHermitian.det_eq_prod_range_eigenvalue, RCLike.ofReal_re]
  exact Finset.prod_le_prod (fun i _ => hB.eigenvalue_nonneg i) fun i hi =>
    hA.isHermitian.eigenvalue_conjTranspose_mul_mul_le hV (Finset.mem_range.mp hi)

end NLAlib
