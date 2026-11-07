/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Matrix.QRIteration.ShiftedQR
public import NLAlibScaffold.Matrix.Factorizations.GivensHessenberg

/-!
# The potential and the shifted QR step (scaffold)

Statements for `NLAlib/Matrix/QRIteration/ShiftedQR.lean` (stage SHIFTED-QR, waves W0–W1, design
note `docs/design/Eigensolvers-ShiftedQR.md` §3.1–§3.2): the last row of $p(\mathbf{H})$ for an
upper Hessenberg $\mathbf{H}$, the variational formula for the potential
[BanksGarzaVargasSrivastava2021, Lemma 2.3], the shifted QR step as a unitary similarity that
keeps the Hessenberg form and factors $p(\mathbf{H})$ ([BanksGarzaVargasSrivastava2022,
Lemma 3.2]), the bound $\psi_k(\widehat{\mathbf{H}}) \le \tau_p(\mathbf{H})$
([BanksGarzaVargasSrivastava2021, Lemma 2.5]), and the singular case, which the paper treats in
one line: a singular shift decouples exactly, and an exact zero on the subdiagonal persists.

## Main results

* `NLAlib.IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq`: the variational formula.
* `NLAlib.IsUpperHessenberg.exists_isQR_aeval_shiftPoly`: the step is a QR step of
  $p(\mathbf{H})$.
* `NLAlib.IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le`: the potential
  after the step is at most $\tau_p(\mathbf{H})$.
* `NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero`: a singular shift
  polynomial decouples.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-! ### The potential and the last row of a polynomial in a Hessenberg matrix -/

/-- **The $k$-th power of the potential is the product of the last $k$ subdiagonal moduli**:
for $k \ge 1$,
$\psi_k(\mathbf{H})^k = \prod_{n - k \le i < n}\lvert\mathbf{H}_{i+1,i}\rvert$.
Proof: `Real.rpow_inv_natCast_pow` on the nonnegative product (`Finset.prod_nonneg`).
S, about 5 lines. -/
theorem hessenbergPotential_pow {k : ℕ} (hk : 0 < k) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    hessenbergPotential k H ^ k =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ := by
  unfold hessenbergPotential
  exact Real.rpow_inv_natCast_pow (Finset.prod_nonneg fun i _ => norm_nonneg _) hk.ne'

/-- Helper: the last row of $\mathbf{H}^i$ vanishes at columns $j$ with $j + i < n$. -/
private theorem pow_apply_last_eq_zero {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (i : ℕ) :
    ∀ j : Fin (n + 1), (j : ℕ) + i < n → (H ^ i) (Fin.last n) j = 0 := by
  induction i with
  | zero =>
    intro j hj
    rw [pow_zero, Matrix.one_apply_ne]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  | succ i ih =>
    intro j hj
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : (j : ℕ) + 1 < (m : ℕ)
    · rw [hH m j hm, mul_zero]
    · rw [ih m (by omega), zero_mul]

/-- **The last row of $p(\mathbf{H})$ is supported on the last $k + 1$ columns**: for upper
Hessenberg $\mathbf{H}$ and a polynomial $p$ of degree at most $k$,
$p(\mathbf{H})_{n,j} = 0$ for $j + k < n$. [BanksGarzaVargasSrivastava2021, proof of
Lemma 2.3].
Proof: by linearity (`Polynomial.aeval_eq_sum_range`) reduce to $\mathbf{H}^i$, $i \le k$; show
by induction on $i$ that $(\mathbf{H}^i)_{a,j} = 0$ for $j + i < a$ (`pow_succ`,
`Matrix.mul_apply`, the Hessenberg zero pattern `NLAlib.IsUpperHessenberg`).
M, about 35 lines. -/
theorem IsUpperHessenberg.aeval_apply_last_eq_zero {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) {p : Polynomial ℂ} {k : ℕ} (hp : p.natDegree ≤ k)
    {j : Fin (n + 1)} (hj : (j : ℕ) + k < n) : Polynomial.aeval H p (Fin.last n) j = 0 := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [Matrix.smul_apply, pow_apply_last_eq_zero hH i j (by omega), smul_zero]

/-- Helper: the last row of $\mathbf{H}^i$ vanishes at columns $j$ with $j + i < n$ (a copy for
`aeval_apply_last_eq_prod`). -/
private theorem pow_apply_last_eq_zero_of_add_lt {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (i : ℕ) :
    ∀ j : Fin (n + 1), (j : ℕ) + i < n → (H ^ i) (Fin.last n) j = 0 := by
  induction i with
  | zero =>
    intro j hj
    rw [pow_zero, Matrix.one_apply_ne]
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_last] at this
    omega
  | succ i ih =>
    intro j hj
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : (j : ℕ) + 1 < (m : ℕ)
    · rw [hH m j hm, mul_zero]
    · rw [ih m (by omega), zero_mul]

/-- Helper: the corner entries of the last row of $\mathbf{H}^i$ are the products of the last $i$
subdiagonal entries. -/
private theorem pow_apply_last_eq_prod {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (i : ℕ) :
    ∀ j : Fin (n + 1), (j : ℕ) + i = n →
      (H ^ i) (Fin.last n) j =
        ∏ l ∈ Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + i), H l.succ l.castSucc := by
  induction i with
  | zero =>
    intro j hj
    have hj' : j = Fin.last n := Fin.ext (by simpa using hj)
    subst hj'
    have hempty : Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + 0) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun l _ => ?_
      have := l.isLt
      omega
    rw [hempty, Finset.prod_empty, pow_zero, Matrix.one_apply_eq]
  | succ i ih =>
    intro j hj
    have hjn : (j : ℕ) < n := by omega
    have hfilt : Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + (i + 1)) =
        insert ⟨j, hjn⟩ (Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + i)) := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
      omega
    have hnotin : (⟨j, hjn⟩ : Fin n) ∉
        Finset.univ.filter (fun l : Fin n => n ≤ (l : ℕ) + i) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hfilt, Finset.prod_insert hnotin, pow_succ, Matrix.mul_apply,
      Finset.sum_eq_single (⟨j + 1, by omega⟩ : Fin (n + 1))]
    · rw [ih ⟨j + 1, by omega⟩ (by change (j : ℕ) + 1 + i = n; omega), mul_comm]
      rfl
    · intro m _ hm
      have hmv : (m : ℕ) ≠ j + 1 := fun h => hm (Fin.ext h)
      by_cases hc : (j : ℕ) + 1 < m
      · rw [hH m j hc, mul_zero]
      · rw [pow_apply_last_eq_zero_of_add_lt hH i m (by omega), zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h

/-- **The corner entry of the last row of $p(\mathbf{H})$ is the product of subdiagonals**: for
upper Hessenberg $\mathbf{H}$, monic $p$ of degree $k$ and the column $j$ with $j + k = n$,
$$p(\mathbf{H})_{n,j} = \prod_{n - k \le i < n}\mathbf{H}_{i+1,i}\,.$$
[BanksGarzaVargasSrivastava2021, proof of Lemma 2.3].
Proof: with the induction of `NLAlib.IsUpperHessenberg.aeval_apply_last_eq_zero` strengthened to
$(\mathbf{H}^i)_{a,a-i} = \prod_{a - i \le l < a}\mathbf{H}_{l+1,l}$; the terms of degree below
$k$ vanish at that column, and the leading coefficient is $1$
(`Polynomial.Monic.coeff_natDegree`). M, about 45 lines. -/
theorem IsUpperHessenberg.aeval_apply_last_eq_prod {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) {p : Polynomial ℂ} (hp : p.Monic) {k : ℕ} (hpk : p.natDegree = k)
    {j : Fin (n + 1)} (hj : (j : ℕ) + k = n) :
    Polynomial.aeval H p (Fin.last n) j =
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), H i.succ i.castSucc := by
  rw [Polynomial.aeval_eq_sum_range, Matrix.sum_apply, hpk, Finset.sum_range_succ,
    Finset.sum_eq_zero fun i hi => ?_, zero_add]
  · have hc : p.coeff k = 1 := by rw [← hpk]; exact hp.coeff_natDegree
    rw [Matrix.smul_apply, hc, one_smul]
    exact pow_apply_last_eq_prod hH k j hj
  · rw [Finset.mem_range] at hi
    rw [Matrix.smul_apply, pow_apply_last_eq_zero_of_add_lt hH i j (by omega), smul_zero]

/-- **The potential bounds every monic polynomial's last row from below**: for upper Hessenberg
$\mathbf{H}$, $1 \le k \le n$ and monic $p$ of degree $k$,
$\psi_k(\mathbf{H})^k \le \|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$.
[BanksGarzaVargasSrivastava2021, Lemma 2.3], the lower bound.
Proof: the norm of the row is at least the modulus of its entry at column $n - k$
(`EuclideanSpace.norm_eq`, `Finset.single_le_sum`), which is the product of
`NLAlib.IsUpperHessenberg.aeval_apply_last_eq_prod`; then `NLAlib.hessenbergPotential_pow` and
`norm_prod`. S, about 15 lines. -/
theorem IsUpperHessenberg.hessenbergPotential_pow_le_norm_aeval
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {p : Polynomial ℂ}
    (hp : p.Monic) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) (hpk : p.natDegree = k) :
    hessenbergPotential k H ^ k ≤ ‖WithLp.toLp 2 (Polynomial.aeval H p (Fin.last n))‖ := by
  have h1 := PiLp.norm_apply_le (WithLp.toLp 2 (Polynomial.aeval H p (Fin.last n)))
    ⟨n - k, by omega⟩
  have h2 := IsUpperHessenberg.aeval_apply_last_eq_prod hH hp hpk (j := ⟨n - k, by omega⟩)
    (by change n - k + k = n; omega)
  rw [hessenbergPotential_pow hk H, ← norm_prod, ← h2]
  exact h1

/-- The last row of $\mathbf{H}^i$, $i \le k$, on the last $k$ columns is the last row of
$\mathbf{H}_{(k)}^i$. -/
private theorem IsUpperHessenberg.pow_apply_last_trailing
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) {i : ℕ} (hi : i ≤ k) (j : Fin k) :
    (H ^ i) (Fin.last n) ⟨min (n + 1 - k + j) n, Nat.lt_succ_of_le (min_le_right _ _)⟩ =
      (trailingBlock k H ^ i) ⟨k - 1, by omega⟩ j := by
  induction i generalizing j with
  | zero =>
    simp only [pow_zero, Matrix.one_apply, Fin.ext_iff, Fin.val_last]
    congr 1
    apply propext
    omega
  | succ i ih =>
    rw [pow_succ, pow_succ, Matrix.mul_apply, Matrix.mul_apply]
    symm
    refine Fintype.sum_of_injective
      (fun j' : Fin k => (⟨min (n + 1 - k + j') n, Nat.lt_succ_of_le (min_le_right _ _)⟩ :
        Fin (n + 1))) ?_ _ _ ?_ ?_
    · intro a b hab
      simp only [Fin.mk.injEq] at hab
      ext; omega
    · intro c hc
      have hc' : (c : ℕ) + k ≤ n := by
        by_contra hcon
        exact hc ⟨⟨c - (n + 1 - k), by omega⟩, Fin.ext (by simp only; omega)⟩
      have := hH.aeval_apply_last_eq_zero (p := Polynomial.X ^ i) (k := i)
        (by rw [Polynomial.natDegree_X_pow]) (j := c) (by omega)
      rw [Polynomial.aeval_X_pow] at this
      rw [this, zero_mul]
    · intro j'
      rw [ih (by omega) j']
      rfl

/-- **The variational formula for the potential**: for upper Hessenberg $\mathbf{H}$ and
$1 \le k \le n$, the characteristic polynomial $\chi_k$ of the trailing block
$\mathbf{H}_{(k)}$ attains the lower bound,
$$\|\mathbf{e}_n^{\mathsf{H}}\chi_k(\mathbf{H})\| = \psi_k(\mathbf{H})^k\,,$$
so $\psi_k(\mathbf{H})^k = \min_p \|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$ over monic $p$ of
degree $k$. [BanksGarzaVargasSrivastava2021, Lemma 2.3]; [TrefethenBau1997, Theorem 34.1].
Proof: for $i \le k$ the last row of $\mathbf{H}^i$, restricted to the last $k$ columns, is the
last row of $\mathbf{H}_{(k)}^i$ (induction on $i$: for $i < k$ the row of $\mathbf{H}^i$ is
supported on the last $k$ columns, and there right multiplication by $\mathbf{H}$ only uses the
trailing block); so for $\deg p \le k$ the last $k$ entries of the row of $p(\mathbf{H})$ are
those of $\mathbf{e}_k^{\mathsf{H}}p(\mathbf{H}_{(k)})$. With Cayley–Hamilton
(`Matrix.aeval_self_charpoly`) they vanish for $\chi_k$; the entries before column $n - k$ vanish by
`NLAlib.IsUpperHessenberg.aeval_apply_last_eq_zero`, and the remaining one is the product of
`NLAlib.IsUpperHessenberg.aeval_apply_last_eq_prod` (`Matrix.charpoly_monic`,
`Matrix.charpoly_natDegree_eq_dim`). L, about 90 lines (split the restriction lemma off). -/
theorem IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {k : ℕ} (hk : 0 < k)
    (hkn : k ≤ n) :
    ‖WithLp.toLp 2 (Polynomial.aeval H (trailingBlock k H).charpoly (Fin.last n))‖ =
      hessenbergPotential k H ^ k := by
  set T := trailingBlock k H
  have hdeg : T.charpoly.natDegree = k := by
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  set v := Polynomial.aeval H T.charpoly (Fin.last n)
  have htrail : ∀ c : Fin (n + 1), n + 1 - k ≤ (c : ℕ) → v c = 0 := by
    intro c hc
    have hc' : c = ⟨min (n + 1 - k + (⟨c - (n + 1 - k), by omega⟩ : Fin k)) n,
        Nat.lt_succ_of_le (min_le_right _ _)⟩ := Fin.ext (by simp only; omega)
    have hT := congrFun (congrFun (Matrix.aeval_self_charpoly T) ⟨k - 1, by omega⟩)
      ⟨c - (n + 1 - k), by omega⟩
    rw [Polynomial.aeval_eq_sum_range] at hT
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.zero_apply] at hT
    rw [hc', ← hT]
    simp only [v, Polynomial.aeval_eq_sum_range, Matrix.sum_apply, Matrix.smul_apply]
    refine Finset.sum_congr rfl fun i hi => ?_
    exact congrArg _ (hH.pow_apply_last_trailing hk hkn (j := ⟨c - (n + 1 - k), by omega⟩)
      (by rw [Finset.mem_range] at hi; omega))
  set c₀ : Fin (n + 1) := ⟨n - k, by omega⟩
  have hv : v = Pi.single c₀ (v c₀) := by
    funext c
    by_cases hc : c = c₀
    · subst hc; simp
    · rw [Pi.single_eq_of_ne hc]
      rcases lt_or_ge ((c : ℕ) + k) n with h | h
      · exact hH.aeval_apply_last_eq_zero hdeg.le h
      · exact htrail c (by have : (c : ℕ) ≠ n - k := fun h' => hc (Fin.ext h'); omega)
  rw [hv, PiLp.toLp_single, PiLp.norm_single, show v c₀ = Polynomial.aeval H T.charpoly
    (Fin.last n) c₀ from rfl,
    hH.aeval_apply_last_eq_prod (Matrix.charpoly_monic T) hdeg (by simp only [c₀]; omega),
    norm_prod, hessenbergPotential_pow hk]

/-- **The potential is at most the norm**: for $1 \le k \le n$,
$\psi_k(\mathbf{H}) \le \|\mathbf{H}\|_2$. [BanksGarzaVargasSrivastava2021, proof of
Theorem 1.6].
Proof: each entry is at most the spectral norm (`NLAlib.norm_apply_le_specNorm` or the row
bound); the product of $k$ such factors is at most $\|\mathbf{H}\|_2^k$ (`Finset.prod_le_pow_card`
with the filter of card $k$), and take $k$-th roots (`Real.rpow_le_rpow`). S, about 20 lines. -/
theorem hessenbergPotential_le_specNorm {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : hessenbergPotential k H ≤ specNorm H := by
  have hcard : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).card = k := by
    have hmap : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).map Fin.valEmbedding =
        Finset.Ico (n - k) n := by
      ext m
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, i.isLt⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨m, h2⟩, by change n ≤ m + k; omega, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ico]
    omega
  have hS : 0 ≤ specNorm H := specNorm_nonneg H
  have hP : ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ ≤
      specNorm H ^ k := by
    calc _ ≤ ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), specNorm H :=
          Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i _ => norm_apply_le_specNorm _ _ _
      _ = specNorm H ^ k := by rw [Finset.prod_const, hcard]
  unfold hessenbergPotential
  calc _ ≤ (specNorm H ^ k) ^ ((k : ℝ)⁻¹) :=
        Real.rpow_le_rpow (Finset.prod_nonneg fun i _ => norm_nonneg _) hP (by positivity)
    _ = specNorm H := Real.pow_rpow_inv_natCast hS hk.ne'

/-- **A small potential means decoupling**: for $1 \le k \le n$ and $\delta \ge 0$, if
$\psi_k(\mathbf{H}) \le \delta\|\mathbf{H}\|_2$ then some subdiagonal entry has
$\lvert\mathbf{H}_{i+1,i}\rvert \le \delta\|\mathbf{H}\|_2$. [BanksGarzaVargasSrivastava2021,
proof of Theorem 1.6].
Proof: the geometric mean of the $k$ factors is at least their minimum (take the minimising
index `Finset.exists_min_image`; `Finset.pow_card_le_prod`), then `NLAlib.hessenbergPotential_pow`.
S, about 20 lines. -/
theorem isDecoupled_of_hessenbergPotential_le {k : ℕ} (hk : 0 < k) (hkn : k ≤ n) {δ : ℝ}
    (hδ : 0 ≤ δ) {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (h : hessenbergPotential k H ≤ δ * specNorm H) : IsDecoupled δ H := by
  have hcard : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).card = k := by
    have hmap : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).map Fin.valEmbedding =
        Finset.Ico (n - k) n := by
      ext m
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Fin.valEmbedding_apply, Finset.mem_Ico]
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨by omega, i.isLt⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨m, h2⟩, by change n ≤ m + k; omega, rfl⟩
    rw [← Finset.card_map Fin.valEmbedding, hmap, Nat.card_Ico]
    omega
  have hne : (Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k)).Nonempty :=
    ⟨⟨n - k, by omega⟩, by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega⟩
  obtain ⟨i0, hi0, hmin⟩ :=
    Finset.exists_min_image _ (fun i : Fin n => ‖H i.succ i.castSucc‖) hne
  have hδS : 0 ≤ δ * specNorm H := mul_nonneg hδ (specNorm_nonneg H)
  have hψ0 : 0 ≤ hessenbergPotential k H := by
    unfold hessenbergPotential
    positivity
  have hmk : ∏ _i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i0.succ i0.castSucc‖ ≤
      ∏ i ∈ Finset.univ.filter (fun i : Fin n => n ≤ (i : ℕ) + k), ‖H i.succ i.castSucc‖ :=
    Finset.prod_le_prod (fun i _ => norm_nonneg _) fun i hi => hmin i hi
  rw [Finset.prod_const, hcard] at hmk
  have h3 : ‖H i0.succ i0.castSucc‖ ^ k ≤ (δ * specNorm H) ^ k :=
    hmk.trans ((hessenbergPotential_pow hk H).symm ▸ pow_le_pow_left₀ hψ0 h k)
  exact ⟨i0, (pow_le_pow_iff_left₀ (norm_nonneg _) hδS hk.ne').mp h3⟩

/-! ### The shifted QR step -/

/-- **The shifted QR step keeps the Hessenberg form**: for upper Hessenberg $\mathbf{H}$ and any
shift $s$, `NLAlib.shiftedQRStep` $\mathbf{H}$ $s$ is upper Hessenberg, also when
$\mathbf{H} - s\mathbf{I}$ is singular.
Proof: with $\mathbf{Q}$, $\mathbf{R}$ the Givens factors of $\mathbf{H} - s\mathbf{I}$,
$\mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q} = \mathbf{R}\mathbf{Q} + s\mathbf{I}$
(`NLAlib.IsQR.mul_add_smul_one_eq` with `NLAlib.isQR_givensHessenberg`), $\mathbf{R}$
upper triangular
(`NLAlib.isUpperTrapezoidal_givensHessenbergR`) and $\mathbf{Q}$ upper Hessenberg
(`NLAlib.isUpperHessenberg_givensHessenbergQ`); `NLAlib.IsUpperHessenberg.isUpperTriangular_mul`.
S, about 20 lines. -/
theorem IsUpperHessenberg.isUpperHessenberg_shiftedQRStep {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (s : ℂ) : IsUpperHessenberg (shiftedQRStep H s) := by
  unfold shiftedQRStep
  set M := H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hMdef
  have hM : IsUpperHessenberg M := by
    intro i j hij
    rw [hMdef, Matrix.sub_apply, hH i j hij, Matrix.smul_apply,
      Matrix.one_apply_ne (fun h => by subst h; omega), smul_zero, sub_zero]
  have hQR : IsQR M (givensHessenbergQ M) (givensHessenbergR M) := by
    have h := isQR_givensHessenberg hM le_rfl
    have e : Fin.castLE (le_refl (n + 1)) = id := funext fun i => Fin.ext rfl
    rw [e, Matrix.submatrix_id_id, Matrix.submatrix_id_id] at h
    exact h
  rw [← hQR.mul_add_smul_one_eq]
  have h1 : IsUpperHessenberg (givensHessenbergR M * givensHessenbergQ M) :=
    IsUpperHessenberg.isUpperTriangular_mul hQR.isUpperTriangular
      (isUpperHessenberg_givensHessenbergQ M)
  intro i j hij
  rw [Matrix.add_apply, h1 i j hij, Matrix.smul_apply,
    Matrix.one_apply_ne (fun h => by subst h; omega), smul_zero, add_zero]

/-- **The multi-shift QR step keeps the Hessenberg form**: for upper Hessenberg $\mathbf{H}$
and any list of shifts, `NLAlib.multiShiftedQRStep` $\mathbf{H}$ `ss` is upper Hessenberg.
Proof: induction on `ss` (`List.foldl_cons`) with
`NLAlib.IsUpperHessenberg.isUpperHessenberg_shiftedQRStep`.
S, about 6 lines. -/
theorem IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (ss : List ℂ) :
    IsUpperHessenberg (multiShiftedQRStep H ss) := by
  sorry

/-- **The multi-shift QR step is a QR step of the shift polynomial**: for upper Hessenberg
$\mathbf{H}$ and shifts $s_1, \dots, s_k$, there are $\mathbf{Q}$ unitary and $\mathbf{R}$
upper triangular with $p(\mathbf{H}) = \mathbf{Q}\mathbf{R}$, $p(z) = \prod_i (z - s_i)$, and
`NLAlib.multiShiftedQRStep` $\mathbf{H}$ `ss` $= \mathbf{Q}^{\mathsf{H}}\mathbf{H}\mathbf{Q}$. No
invertibility is assumed. [BanksGarzaVargasSrivastava2022, Lemma 3.2], there for invertible
$p(\mathbf{H})$ with the positive-diagonal factorization.
Proof: induction on the list, generalising $\mathbf{H}$. With $\mathbf{H} - s_1\mathbf{I} =
\mathbf{Q}_1\mathbf{R}_1$ (`NLAlib.isQR_givensHessenberg`) and
$\mathbf{H}_2 = \mathbf{Q}_1^{\mathsf{H}}\mathbf{H}\mathbf{Q}_1$ Hessenberg, the hypothesis gives
$q(\mathbf{H}_2) = \mathbf{Q}'\mathbf{R}'$ for the remaining shifts; then
$p(\mathbf{H}) = q(\mathbf{H})(\mathbf{H} - s_1\mathbf{I}) =
\mathbf{Q}_1 q(\mathbf{H}_2)\mathbf{Q}_1^{\mathsf{H}}\mathbf{Q}_1\mathbf{R}_1 =
(\mathbf{Q}_1\mathbf{Q}')(\mathbf{R}'\mathbf{R}_1)$ (`Polynomial.aeval_algHom_apply` for the
conjugation, commutativity of polynomials in $\mathbf{H}$, `Matrix.IsUpperTriangular.mul`,
`NLAlib.HasOrthonormalCols.mul`). M, about 50 lines. -/
theorem IsUpperHessenberg.exists_isQR_aeval_shiftPoly {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    (hH : IsUpperHessenberg H) (ss : List ℂ) :
    ∃ Q R : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ,
      IsQR (Polynomial.aeval H (shiftPoly ss)) Q R ∧ multiShiftedQRStep H ss = Qᴴ * H * Q := by
  sorry

/-- Helper: a single shifted QR step is a unitary similarity, so it preserves the spectral norm. -/
private theorem specNorm_shiftedQRStep_aux (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (s : ℂ) :
    specNorm (shiftedQRStep H s) = specNorm H := by
  unfold shiftedQRStep
  have hQ : HasOrthonormalCols (givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1))
      (Fin (n + 1)) ℂ))) := by
    unfold givensHessenbergQ
    exact hasOrthonormalCols_givensHessenbergState_fst _ _
  rw [hQ.specNorm_mul_right, ← specNorm_conjTranspose, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, hQ.specNorm_mul_right, specNorm_conjTranspose]

/-- **The multi-shift QR step preserves the norm**:
$\|\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})\|_2 = \|\mathbf{H}\|_2$.
Proof: each single step is a unitary similarity
(`NLAlib.hasOrthonormalCols_givensHessenbergState_fst`; unitary invariance of `NLAlib.specNorm`);
induction on the list. S, about 12 lines. -/
theorem specNorm_multiShiftedQRStep (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    specNorm (multiShiftedQRStep H ss) = specNorm H := by
  induction ss generalizing H with
  | nil => rfl
  | cons s ss ih =>
    change specNorm (ss.foldl shiftedQRStep (shiftedQRStep H s)) = specNorm H
    exact (ih (shiftedQRStep H s)).trans (specNorm_shiftedQRStep_aux H s)

/-- Helper: the pseudo-condition number is invariant under a left unitary factor. -/
private theorem pseudoConditionNumber_conjTranspose_mul_aux
    {Q V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hQ : HasOrthonormalCols Q) (hV : IsUnit V) :
    pseudoConditionNumber (Qᴴ * V) = pseudoConditionNumber V := by
  classical
  have hVdet : IsUnit V.det := (Matrix.isUnit_iff_isUnit_det V).mp hV
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ.conjTranspose_mul_self
  have hU : IsUnit Qᴴ := ⟨⟨Qᴴ, Q, hQ.conjTranspose_mul_self, hQQ⟩, rfl⟩
  have hinv : (Qᴴ * V)⁻¹ = V⁻¹ * Q := by
    refine Matrix.inv_eq_right_inv ?_
    calc Qᴴ * V * (V⁻¹ * Q) = Qᴴ * (V * V⁻¹) * Q := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Matrix.mul_nonsing_inv V hVdet, Matrix.mul_one, hQ.conjTranspose_mul_self]
  have hn1 : specNorm (Qᴴ * V) = specNorm V := by
    rw [← specNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      hQ.specNorm_mul_right, specNorm_conjTranspose]
  rw [pseudoConditionNumber_of_isUnit (hU.mul hV), pseudoConditionNumber_of_isUnit hV, hinv,
    hn1, hQ.specNorm_mul_right]

/-- Helper: one shifted QR step carries an eigenvector matrix, with the same pseudo-condition
number. -/
private theorem exists_isUnit_mul_eq_mul_diagonal_shiftedQRStep_aux
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (s : ℂ) :
    ∃ V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnit V' ∧
      shiftedQRStep H s * V' = V' * Matrix.diagonal d ∧
      pseudoConditionNumber V' = pseudoConditionNumber V := by
  have hQ : HasOrthonormalCols (givensHessenbergQ
      (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))) := by
    unfold givensHessenbergQ
    exact hasOrthonormalCols_givensHessenbergState_fst _ _
  unfold shiftedQRStep
  set Q := givensHessenbergQ (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)) with hQdef
  have hQQ : Q * Qᴴ = 1 := mul_eq_one_comm.mp hQ.conjTranspose_mul_self
  have hU : IsUnit Qᴴ := ⟨⟨Qᴴ, Q, hQ.conjTranspose_mul_self, hQQ⟩, rfl⟩
  refine ⟨Qᴴ * V, hU.mul hV, ?_, pseudoConditionNumber_conjTranspose_mul_aux hQ hV⟩
  calc Qᴴ * H * Q * (Qᴴ * V) = Qᴴ * H * (Q * Qᴴ) * V := by simp only [Matrix.mul_assoc]
    _ = Qᴴ * (H * V) := by rw [hQQ]; simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = Qᴴ * V * Matrix.diagonal d := by rw [hHV, Matrix.mul_assoc]

/-- **The multi-shift QR step carries the eigenvector matrix**: if
$\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$ with $\mathbf{V}$ invertible,
then $\widehat{\mathbf{H}} = \mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has
$\widehat{\mathbf{H}}\mathbf{V}' = \mathbf{V}'\operatorname{diag}(\mathbf{d})$ for an invertible
$\mathbf{V}'$ with the same condition number, $\|\mathbf{V}'\|_2\|\mathbf{V}'^{-1}\|_2 =
\|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$; so $\kappa_V$ is invariant along the iteration.
[BanksGarzaVargasSrivastava2021, §4].
Proof: $\mathbf{V}' = \mathbf{Q}^{\mathsf{H}}\mathbf{V}$ for the accumulated unitary
$\mathbf{Q}$; `NLAlib.pseudoConditionNumber_of_isUnit` and unitary invariance of the norm; induction
on the list. S, about 25 lines. -/
theorem exists_isUnit_mul_eq_mul_diagonal_multiShiftedQRStep
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} {d : Fin (n + 1) → ℂ} (hV : IsUnit V)
    (hHV : H * V = V * Matrix.diagonal d) (ss : List ℂ) :
    ∃ V' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ, IsUnit V' ∧
      multiShiftedQRStep H ss * V' = V' * Matrix.diagonal d ∧
      pseudoConditionNumber V' = pseudoConditionNumber V := by
  induction ss generalizing H V with
  | nil => exact ⟨V, hV, hHV, rfl⟩
  | cons s ss ih =>
    obtain ⟨V1, h1, e1, p1⟩ := exists_isUnit_mul_eq_mul_diagonal_shiftedQRStep_aux hV hHV s
    obtain ⟨V2, h2, e2, p2⟩ := ih h1 e1
    exact ⟨V2, h2, e2, p2.trans p1⟩

/-- **The potential after a QR step is at most $\tau_p$**: for upper Hessenberg $\mathbf{H}$,
shifts $s_1, \dots, s_k$ with $1 \le k \le n$ and $p(\mathbf{H})$ invertible,
$p(z) = \prod_i (z - s_i)$,
$$\psi_k(\widehat{\mathbf{H}})^k\,\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1}\| \le 1\,,
\qquad \widehat{\mathbf{H}} = \mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})\,,$$
that is $\psi_k(\widehat{\mathbf{H}}) \le \tau_p(\mathbf{H}) =
\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1}\|^{-1/k}$.
[BanksGarzaVargasSrivastava2021, Lemma 2.5], the invertible case.
Proof: with $p(\mathbf{H}) = \mathbf{Q}\mathbf{R}$ from
`NLAlib.IsUpperHessenberg.exists_isQR_aeval_shiftPoly`, $p(\widehat{\mathbf{H}}) =
\mathbf{Q}^{\mathsf{H}}p(\mathbf{H})\mathbf{Q} = \mathbf{R}\mathbf{Q}$, so
$\|\mathbf{e}_n^{\mathsf{H}}p(\widehat{\mathbf{H}})\| = \|\mathbf{e}_n^{\mathsf{H}}\mathbf{R}\| =
\lvert\mathbf{R}_{n,n}\rvert$ ($\mathbf{R}$ triangular, $\mathbf{Q}$ unitary), and
$\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})^{-1} = \mathbf{R}_{n,n}^{-1}\mathbf{e}_n^{\mathsf{H}}
\mathbf{Q}^{\mathsf{H}}$ has norm $\lvert\mathbf{R}_{n,n}\rvert^{-1}$; the potential of
$\widehat{\mathbf{H}}$ (Hessenberg,
`NLAlib.IsUpperHessenberg.isUpperHessenberg_multiShiftedQRStep`) is bounded by
`NLAlib.IsUpperHessenberg.hessenbergPotential_pow_le_norm_aeval` (`shiftPoly` is monic of degree
$k$: `Polynomial.monic_multiset_prod_of_monic`, `Polynomial.natDegree_multiset_prod_of_monic`).
M, about 50 lines. -/
theorem IsUpperHessenberg.hessenbergPotential_multiShiftedQRStep_pow_mul_le
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {ss : List ℂ}
    (hk : 0 < ss.length) (hkn : ss.length ≤ n) (hp : IsUnit (Polynomial.aeval H (shiftPoly ss))) :
    hessenbergPotential ss.length (multiShiftedQRStep H ss) ^ ss.length *
      ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss))⁻¹ (Fin.last n))‖ ≤ 1 := by
  sorry

/-- The first $j \le i$ steps of Givens QR leave row $i + 1$ alone. -/
private theorem givensHessenbergState_snd_apply_of_eq_add_one {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) ℂ) {i j : ℕ} (hj : j ≤ i) {a : Fin m} (ha : (a : ℕ) = i + 1)
    (b : Fin p) : (givensHessenbergState A j).2 a b = A a b := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [givensHessenbergState_succ_snd, givensHessenbergStep_mul_apply_of_ne _ _ (by omega)
      (by omega)]
    exact ih (by omega)

/-- The first $j \le i$ steps of Givens QR keep the coordinates up to $i$ of a vector zero. -/
private theorem givensHessenbergState_fst_mulVec_apply_eq_zero_of_le {m p : ℕ}
    (A : Matrix (Fin m) (Fin p) ℂ) {v : Fin m → ℂ} {i : ℕ} (hv : ∀ a : Fin m, (a : ℕ) ≤ i → v a = 0)
    {j : ℕ} (hj : j ≤ i) (a : Fin m) (ha : (a : ℕ) ≤ i) :
    ((givensHessenbergState A j).1ᴴ *ᵥ v) a = 0 := by
  induction j generalizing a with
  | zero =>
    simp only [givensHessenbergState, Matrix.conjTranspose_one, Matrix.one_mulVec]
    exact hv a ha
  | succ j ih =>
    rw [conjTranspose_givensHessenbergState_succ_fst_mulVec]
    exact (givensHessenbergStep_mul_apply_of_apply_eq_zero _
      (Matrix.of fun i (_ : Unit) => ((givensHessenbergState A j).1ᴴ *ᵥ v) i) (b := ())
      (fun a' ha' => ih (by omega) a' (by omega)) a).trans (ih (by omega) a ha)

/-- **A zero subdiagonal entry persists under a shifted QR step**: for upper Hessenberg
$\mathbf{H}$ with $\mathbf{H}_{i+1,i} = 0$ and any shift $s$, the step has
$(\mathsf{shiftedQRStep}(\mathbf{H}, s))_{i+1,i} = 0$.
Proof: in Givens QR of $\mathbf{H} - s\mathbf{I}$, row $i + 1$ is untouched before step $i$, so
step $i$ rotates the pair $(u, 0)$ and its rotation is diagonal (`NLAlib.givensCoeffs_snd_zero`);
hence the unitary factor has $\mathbf{Q}_{i+1,i} = 0$ besides being Hessenberg, and
$(\mathbf{R}\mathbf{Q})_{i+1,i} = \sum_{l \ge i+1}\mathbf{R}_{i+1,l}\mathbf{Q}_{l,i} = 0$.
M, about 50 lines. -/
theorem IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {i : Fin n}
    (hi : H i.succ i.castSucc = 0) (s : ℂ) : shiftedQRStep H s i.succ i.castSucc = 0 := by
  set A := H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) with hA
  have hAH : IsUpperHessenberg A := fun a b hab => by
    rw [hA, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne (fun h => by rw [h] at hab; omega), smul_zero, sub_zero]
    exact hH a b hab
  have hAi : A i.succ i.castSucc = 0 := by
    rw [hA, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply_ne (fun h => by simpa using congrArg Fin.val h), smul_zero, sub_zero, hi]
  set Q := givensHessenbergQ A
  set R := givensHessenbergR A
  have hQR : Q * R = A := givensHessenbergState_fst_mul_snd A (n + 1)
  have hQQ : Qᴴ * Q = 1 :=
    (hasOrthonormalCols_givensHessenbergState_fst A (n + 1)).conjTranspose_mul_self
  have hstep : shiftedQRStep H s = R * Q + s • 1 := by
    change Qᴴ * H * Q = _
    calc Qᴴ * H * Q = Qᴴ * (A + s • 1) * Q := by rw [hA, sub_add_cancel]
      _ = (Qᴴ * Q) * R * Q + s • (Qᴴ * Q) := by
        rw [← hQR]
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
          Matrix.mul_one, Matrix.mul_assoc]
      _ = R * Q + s • 1 := by rw [hQQ, Matrix.one_mul]
  have key : ((givensHessenbergState A (n + 1)).1ᴴ *ᵥ Pi.single i.succ 1) i.castSucc = 0 := by
    rw [(givensHessenbergState_apply_of_lt A _ (k := i + 1) (j := n + 1) (by omega)
      (a := i.castSucc) (by simp)).2, conjTranspose_givensHessenbergState_succ_fst_mulVec,
      givensHessenbergStep_of_lt _ (by omega) (by omega) (by omega),
      givensHessenbergState_snd_apply_of_eq_add_one A le_rfl (a := ⟨i + 1, by omega⟩) rfl,
      show (⟨i + 1, by omega⟩ : Fin (n + 1)) = i.succ from rfl,
      show (⟨i, by omega⟩ : Fin (n + 1)) = i.castSucc from rfl, hAi, givensCoeffs_snd_zero,
      givens_mulVec_apply_left (Fin.ne_of_val_ne (by simp)),
      givensHessenbergState_fst_mulVec_apply_eq_zero_of_le A (i := i)
        (fun a ha => Pi.single_eq_of_ne (Fin.ne_of_val_ne (by simp; omega)) _) le_rfl _ (by simp)]
    ring
  have hQ0 : Q i.succ i.castSucc = 0 := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply, Matrix.conjTranspose_apply,
      star_eq_zero] at key
    exact key
  rw [hstep, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_ne (fun h => by simpa using congrArg Fin.val h), smul_zero, add_zero,
    Matrix.mul_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rcases lt_trichotomy (l : ℕ) (i + 1) with h | h | h
  · rw [show R i.succ l = 0 from isUpperTrapezoidal_givensHessenbergR hAH i.succ l
      (by simp; omega), zero_mul]
  · rw [show l = i.succ from Fin.ext (by simp; omega), hQ0, mul_zero]
  · rw [show Q l i.castSucc = 0 from isUpperHessenberg_givensHessenbergQ A l i.castSucc
      (by simp; omega), mul_zero]

/-- **A reduced Hessenberg matrix stays reduced under multi-shift QR steps**: for upper
Hessenberg $\mathbf{H}$ with a zero subdiagonal entry, every
$\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has one (at the same index).
Proof: induction on `ss` with
`NLAlib.IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero` and
`NLAlib.IsUpperHessenberg.isUpperHessenberg_shiftedQRStep`; `IsDecoupled 0` is a zero entry
(`norm_le_zero_iff`).
S, about 12 lines. -/
theorem IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (h : IsDecoupled 0 H)
    (ss : List ℂ) : IsDecoupled 0 (multiShiftedQRStep H ss) := by
  sorry

/-- **A singular shift decouples exactly**: for upper Hessenberg $\mathbf{H}$ of size at least
$2$ and a shift $s$ with $\det(\mathbf{H} - s\mathbf{I}) = 0$, the step
$\mathsf{shiftedQRStep}(\mathbf{H}, s)$ has a zero subdiagonal entry.
[BanksGarzaVargasSrivastava2021, proof of Lemma 2.5], where the claim that $\mathbf{R}_{n,n} = 0$
for every QR factorization is used without the unreduced hypothesis it needs.
Proof: if $\mathbf{H}$ is already reduced, by
`NLAlib.IsUpperHessenberg.shiftedQRStep_apply_succ_castSucc_eq_zero`. Otherwise the first $n$
columns of $\mathbf{H} - s\mathbf{I}$ are independent (nonzero subdiagonal), so the Givens
pivots $\mathbf{R}_{i,i}$, $i < n$, are nonzero
(`NLAlib.forall_givensHessenbergR_apply_self_ne_zero_iff` on the leading columns) and
$\det = 0$ forces $\mathbf{R}_{n,n} = 0$; then the last row of $\mathbf{R}\mathbf{Q}$ is
$\mathbf{R}_{n,n}\mathbf{e}_n^{\mathsf{H}}\mathbf{Q} = \mathbf{0}$, so the entry $(n, n - 1)$ of
$\mathbf{R}\mathbf{Q} + s\mathbf{I}$ vanishes. L, about 70 lines (the leading-block rank step). -/
theorem IsUpperHessenberg.isDecoupled_zero_shiftedQRStep_of_det_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (hn : 0 < n) {s : ℂ}
    (hs : (H - s • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0) :
    IsDecoupled 0 (shiftedQRStep H s) := by
  sorry

/-- **A singular shift polynomial decouples exactly**: for upper Hessenberg $\mathbf{H}$ of size
at least $2$ and shifts with $\det p(\mathbf{H}) = 0$, $p(z) = \prod_i (z - s_i)$, the step
$\mathsf{multiShiftedQRStep}(\mathbf{H}, \mathrm{ss})$ has a zero subdiagonal entry. This is the
singular case of [BanksGarzaVargasSrivastava2021, Lemma 2.5], where it reads
$\psi_k(\widehat{\mathbf{H}}) = 0$.
Proof: $\det p(\mathbf{H}) = \prod_i \det(\mathbf{H} - s_i\mathbf{I})$ (`Matrix.det_mul`,
`List.prod`), so some $s_j$ is an eigenvalue; the intermediate matrix before shift $s_j$ is
unitarily similar to $\mathbf{H}$, so its shift is singular too
(`NLAlib.IsUpperHessenberg.isDecoupled_zero_shiftedQRStep_of_det_eq_zero`), and the zero persists
(`NLAlib.IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep`). Induction on the list.
M, about 40 lines. -/
theorem IsUpperHessenberg.isDecoupled_zero_multiShiftedQRStep_of_det_eq_zero
    {H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) (hn : 0 < n)
    {ss : List ℂ} (h : (Polynomial.aeval H (shiftPoly ss)).det = 0) :
    IsDecoupled 0 (multiShiftedQRStep H ss) := by
  sorry

end NLAlib
