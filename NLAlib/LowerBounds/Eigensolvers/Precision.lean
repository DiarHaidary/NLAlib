/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Structured.Walsh
public import NLAlib.Matrix.Norms.Spectral
public import NLAlib.ForMathlib.Algebra.Order.Round
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# A lower bound on the precision of Hermitian diagonalization

A method
that sees its input only after rounding cannot distinguish a $\pm1$ matrix $\mathbf{H}$ from
$\mathbf{H} \pm \delta\mathbf{J}$ ($\mathbf{J}$ the all-ones matrix) when the rounding absorbs
$\delta$; one of the two has residual at least $\delta n$ against any diagonalization, so a
backward error $\varepsilon\|\mathbf{A}\|_2$ forces $\delta n \le \varepsilon(\|\mathbf{H}\|_2 +
\delta n)$. For a Walsh–Hadamard $\mathbf{H}$ ($\|\mathbf{H}\|_2 = \sqrt n$) and rounding to
nearest with $t$ bits, $t \ge \log_2(1/\varepsilon) + \tfrac12\log_2 n - 2 + \log_2(1 -
\varepsilon)$ ([Shah2024, Proposition 1.1]).

## Main results

* `NLAlib.exists_mul_card_le_specNorm_add_smul`: one sign of $\pm\delta\mathbf{J}$ is far from any
  matrix.
* `NLAlib.mul_card_le_of_forall_specNorm_sub_le`: the abstract lower bound.
* `NLAlib.logb_inv_add_le_of_forall_specNorm_sub_le`: Proposition 1.1.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : Type*} [Fintype n]

/-- **One of $\mathbf{M} \pm \delta\mathbf{J}$ has norm at least $\delta n$**: for every square
complex $\mathbf{M}$ and $\delta \ge 0$, with $\mathbf{J}$ the all-ones matrix, there is a sign
$s \in \{1, -1\}$ with $\delta\lvert n \rvert \le \|\mathbf{M} + s\delta\mathbf{J}\|_2$. No
printed source; [Shah2024, proof of Proposition 1.1] argues with the signs of the entries, which
bounds the Frobenius norm only. -/
theorem exists_mul_card_le_specNorm_add_smul (M : Matrix n n ℂ) {δ : ℝ} (hδ : 0 ≤ δ) :
    ∃ s ∈ ({1, -1} : Set ℝ),
      δ * Fintype.card n ≤ specNorm (M + (s * δ) • Matrix.of fun _ _ : n => (1 : ℂ)) := by
  have _ := hδ
  classical
  rcases isEmpty_or_nonempty n with hn | hn
  · exact ⟨1, by simp, by simp [specNorm_nonneg]⟩
  set c : ℝ := (Fintype.card n : ℝ) with hc
  have hcpos : 0 < c := Nat.cast_pos.mpr Fintype.card_pos
  set v : n → ℂ := fun _ => 1 with hv
  have hvn : ‖WithLp.toLp 2 v‖ * ‖WithLp.toLp 2 v‖ = c := by
    rw [← sq, EuclideanSpace.norm_sq_eq]; simp [v, c, hc]
  have hq : ∀ s : ℝ, star v ⬝ᵥ ((M + (s * δ) • Matrix.of fun _ _ : n => (1 : ℂ)) *ᵥ v)
      = star v ⬝ᵥ (M *ᵥ v) + ((s * δ * c ^ 2 : ℝ) : ℂ) := by
    intro s
    rw [Matrix.add_mulVec, dotProduct_add]
    congr 1
    simp [Matrix.mulVec, dotProduct, v, Complex.real_smul, Finset.sum_const, hc]
    ring
  set q := star v ⬝ᵥ (M *ᵥ v) with hqdef
  have main : ∀ s : ℝ, δ * c ^ 2 ≤ |q.re + s * δ * c ^ 2| →
      δ * c ≤ specNorm (M + (s * δ) • Matrix.of fun _ _ : n => (1 : ℂ)) := by
    intro s hs
    set B := M + (s * δ) • Matrix.of fun _ _ : n => (1 : ℂ) with hB
    have h1 := norm_star_dotProduct_mulVec_le B v v
    have h2 : ‖star v ⬝ᵥ (B *ᵥ v)‖ ≤ specNorm B * c :=
      h1.trans_eq (by rw [← hvn]; ring)
    rw [hB, hq s] at h2
    have h3 := Complex.abs_re_le_norm (q + ((s * δ * c ^ 2 : ℝ) : ℂ))
    simp only [Complex.add_re, Complex.ofReal_re] at h3
    have h4 : δ * c * c ≤ specNorm B * c := by
      linarith [h3, h2, hs]
    exact le_of_mul_le_mul_right h4 hcpos
  rcases le_total 0 q.re with h | h
  · refine ⟨1, by simp, main 1 (le_abs.mpr (Or.inl ?_))⟩
    nlinarith [sq_nonneg c]
  · refine ⟨-1, by simp, main (-1) (le_abs.mpr (Or.inr ?_))⟩
    nlinarith [sq_nonneg c]

/-- The spectral norm of the real all-ones matrix is the number of indices. -/
private theorem specNorm_allOnes_eq_card :
    specNorm (Matrix.of fun _ _ : n => (1 : ℝ)) = Fintype.card n := by
  have hJ : (Matrix.of fun _ _ : n => (1 : ℝ)) =
      Matrix.vecMulVec (fun _ : n => (1 : ℝ)) (fun _ : n => (1 : ℝ)) := by
    ext i j; simp [Matrix.vecMulVec]
  rw [hJ, specNorm_vecMulVec, ← sq, EuclideanSpace.norm_sq_eq]
  simp

/-- **A lower bound for diagonalization from rounded input**: let $\mathrm{fl}$ be a rounding of
reals and $\mathcal{A}$ any method that maps the rounded input $\mathrm{fl}(\mathbf{A})$
(entrywise) of a real symmetric $\mathbf{A}$ to $(\mathbf{U}, \mathbf{d})$, with
$\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le
\varepsilon\|\mathbf{A}\|_2$ for every real symmetric $\mathbf{A}$. If $\mathbf{H}$ is real
symmetric and $\delta \ge 0$ with $\mathrm{fl}(\mathbf{H}_{i,j} \pm \delta) =
\mathrm{fl}(\mathbf{H}_{i,j})$ for all entries and both signs, then
$$\delta\lvert n \rvert \le \varepsilon\bigl(\|\mathbf{H}\|_2 + \delta\lvert n \rvert\bigr) \,.$$
[Shah2024, proof of Proposition 1.1]. -/
theorem mul_card_le_of_forall_specNorm_sub_le [DecidableEq n] {fl : ℝ → ℝ} {δ ε : ℝ} (hδ : 0 ≤ δ)
    (alg : Matrix n n ℝ → Matrix n n ℂ × (n → ℝ))
    (halg : ∀ A : Matrix n n ℝ, A.IsSymm →
      specNorm (A.map (fun x : ℝ => (x : ℂ)) - (alg (A.map fl)).1 *
        Matrix.diagonal (fun i => ((alg (A.map fl)).2 i : ℂ)) * (alg (A.map fl)).1ᴴ) ≤
        ε * specNorm A)
    {H : Matrix n n ℝ} (hH : H.IsSymm)
    (hfl : ∀ i j, ∀ s ∈ ({1, -1} : Set ℝ), fl (H i j + s * δ) = fl (H i j)) :
    δ * Fintype.card n ≤ ε * (specNorm H + δ * Fintype.card n) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have hH : H = 0 := Subsingleton.elim _ _
    simp [hH, specNorm_zero]
  have hε : 0 ≤ ε := by
    have h0 : 0 ≤ ε * specNorm (1 : Matrix n n ℝ) :=
      (specNorm_nonneg _).trans (halg 1 Matrix.isSymm_one)
    rw [specNorm_one] at h0
    linarith
  have hJs : (Matrix.of fun _ _ : n => (1 : ℝ)).IsSymm := by
    ext i j; simp
  obtain ⟨s, hs, hle⟩ := exists_mul_card_le_specNorm_add_smul
    (H.map (fun x : ℝ => (x : ℂ)) - (alg (H.map fl)).1 *
      Matrix.diagonal (fun i => ((alg (H.map fl)).2 i : ℂ)) * (alg (H.map fl)).1ᴴ) hδ
  have hfl' : (H + (s * δ) • Matrix.of fun _ _ : n => (1 : ℝ)).map fl = H.map fl := by
    ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
      smul_eq_mul, mul_one]
    exact hfl i j s hs
  have hmain := halg (H + (s * δ) • Matrix.of fun _ _ : n => (1 : ℝ))
    (hH.add (hJs.smul _))
  rw [hfl'] at hmain
  have hM : (H + (s * δ) • Matrix.of fun _ _ : n => (1 : ℝ)).map (fun x : ℝ => (x : ℂ)) -
      (alg (H.map fl)).1 * Matrix.diagonal (fun i => ((alg (H.map fl)).2 i : ℂ)) *
        (alg (H.map fl)).1ᴴ =
      (H.map (fun x : ℝ => (x : ℂ)) - (alg (H.map fl)).1 *
        Matrix.diagonal (fun i => ((alg (H.map fl)).2 i : ℂ)) * (alg (H.map fl)).1ᴴ) +
        (s * δ) • Matrix.of fun _ _ : n => (1 : ℂ) := by
    ext i j
    simp [Matrix.map_apply, Matrix.add_apply, Complex.real_smul]
    ring
  rw [hM] at hmain
  have hsJ : specNorm (H + (s * δ) • Matrix.of fun _ _ : n => (1 : ℝ)) ≤
      specNorm H + δ * Fintype.card n := by
    refine (specNorm_add_le _ _).trans ?_
    rw [specNorm_real_smul, specNorm_allOnes_eq_card]
    have habs : |s * δ| = δ := by
      rcases hs with rfl | rfl <;> simp [abs_of_nonneg hδ]
    rw [habs]
  calc δ * Fintype.card n ≤ specNorm _ := hle
    _ ≤ ε * specNorm (H + (s * δ) • Matrix.of fun _ _ : n => (1 : ℝ)) := hmain
    _ ≤ ε * (specNorm H + δ * Fintype.card n) := mul_le_mul_of_nonneg_left hsJ hε

/-- Rounding near `±1` (helper): for `|y - 1| ≤ 2^{-(s+1)}/4`, rounding to `s+1` bits
sends `y` to `1` and `-y` to `-1`. -/
private theorem roundNearest_near_one {s : ℕ} {y : ℝ} (hy : |y - 1| ≤ 2⁻¹ ^ (s + 1) / 4) :
    Real.roundNearest (s + 1) y = 1 ∧ Real.roundNearest (s + 1) (-y) = -1 := by
  have hy' := abs_le.mp hy
  have hsm : (2 : ℝ)⁻¹ ^ (s + 1) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hy0 : y ≠ 0 := by intro h; rw [h] at hy'; linarith [hy'.1, hy'.2]
  rcases le_or_gt 1 y with h1 | h1
  · have hlog : Int.log 2 |y| = 0 := by
      apply le_antisymm
      · have := (Int.lt_zpow_iff_log_lt one_lt_two (x := 1) (r := |y|)
          (abs_pos.mpr hy0)).mp (by rw [abs_of_nonneg (by linarith)]; norm_num; linarith)
        omega
      · have := (Int.zpow_le_iff_le_log one_lt_two (x := 0) (r := |y|)
          (abs_pos.mpr hy0)).mp (by rw [abs_of_nonneg (by linarith)]; norm_num; linarith)
        omega
    have hQ : (0 : ℝ) < 2 ^ s := by positivity
    have hE : (2 : ℝ) ^ ((0 : ℤ) + 1 - ((s + 1 : ℕ) : ℤ)) = ((2 : ℝ) ^ s)⁻¹ := by
      rw [show (0 : ℤ) + 1 - ((s + 1 : ℕ) : ℤ) = -(s : ℤ) by push_cast; ring, zpow_neg,
        zpow_natCast]
    have hqQ : (2 : ℝ)⁻¹ ^ (s + 1) * 2 ^ s = 1 / 2 := by
      rw [pow_succ, inv_pow]; field_simp
    have hdev : |(y - 1) * 2 ^ s| ≤ 1 / 8 := by
      have := mul_le_mul_of_nonneg_right hy hQ.le
      rw [show (2 : ℝ)⁻¹ ^ (s + 1) / 4 * 2 ^ s = ((2 : ℝ)⁻¹ ^ (s + 1) * 2 ^ s) / 4 by ring,
        hqQ] at this
      rw [abs_mul, abs_of_pos hQ]
      linarith
    have hd := abs_le.mp hdev
    unfold Real.roundNearest
    have hlog' : Int.log 2 |-y| = 0 := by rw [abs_neg, hlog]
    rw [hlog, hlog', hE]
    constructor
    · have hr : round (y / ((2 : ℝ) ^ s)⁻¹) = (2 : ℤ) ^ s := by
        rw [round_eq_iff, div_inv_eq_mul]; push_cast
        constructor <;> nlinarith [hd.1, hd.2]
      rw [hr]; push_cast; field_simp
    · have hr : round (-y / ((2 : ℝ) ^ s)⁻¹) = -(2 : ℤ) ^ s := by
        rw [round_eq_iff, div_inv_eq_mul]; push_cast
        constructor <;> nlinarith [hd.1, hd.2]
      rw [hr]; push_cast; field_simp
  · have hlog : Int.log 2 |y| = -1 := by
      apply le_antisymm
      · have := (Int.lt_zpow_iff_log_lt one_lt_two (x := 0) (r := |y|)
          (abs_pos.mpr (by linarith))).mp (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
        omega
      · have := (Int.zpow_le_iff_le_log one_lt_two (x := -1) (r := |y|)
          (abs_pos.mpr (by linarith))).mp (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
        omega
    have hQ : (0 : ℝ) < 2 ^ (s + 1) := by positivity
    have hE : (2 : ℝ) ^ ((-1 : ℤ) + 1 - ((s + 1 : ℕ) : ℤ)) = ((2 : ℝ) ^ (s + 1))⁻¹ := by
      rw [show (-1 : ℤ) + 1 - ((s + 1 : ℕ) : ℤ) = -((s + 1 : ℕ) : ℤ) by ring, zpow_neg,
        zpow_natCast]
    have hqQ : (2 : ℝ)⁻¹ ^ (s + 1) * 2 ^ (s + 1) = 1 := by
      rw [← mul_pow]; norm_num
    have hdev : |(y - 1) * 2 ^ (s + 1)| ≤ 1 / 4 := by
      have := mul_le_mul_of_nonneg_right hy hQ.le
      rw [show (2 : ℝ)⁻¹ ^ (s + 1) / 4 * 2 ^ (s + 1) = ((2 : ℝ)⁻¹ ^ (s + 1) * 2 ^ (s + 1)) / 4 by
        ring, hqQ] at this
      rw [abs_mul, abs_of_pos hQ]
      linarith
    have hd := abs_le.mp hdev
    unfold Real.roundNearest
    have hlog' : Int.log 2 |-y| = -1 := by rw [abs_neg, hlog]
    rw [hlog, hlog', hE]
    constructor
    · have hr : round (y / ((2 : ℝ) ^ (s + 1))⁻¹) = (2 : ℤ) ^ (s + 1) := by
        rw [round_eq_iff, div_inv_eq_mul]; push_cast
        constructor <;> nlinarith [hd.1, hd.2]
      rw [hr]; push_cast; field_simp
    · have hr : round (-y / ((2 : ℝ) ^ (s + 1))⁻¹) = -(2 : ℤ) ^ (s + 1) := by
        rw [round_eq_iff, div_inv_eq_mul]; push_cast
        constructor <;> nlinarith [hd.1, hd.2]
      rw [hr]; push_cast; field_simp

/-- **Hermitian diagonalization needs $\log_2(1/\varepsilon) + \tfrac12\log_2 n - 2$ bits**
(Proposition 1.1): for $t \ge 1$, $0 < \varepsilon < 1$ and $n = 2^b$, any method that maps the
input rounded to nearest with $t$ significant bits (`Real.roundNearest`) of every real symmetric
$n \times n$ matrix $\mathbf{A}$ to $(\mathbf{U}, \mathbf{d})$ with
$\|\mathbf{A} - \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}\|_2 \le
\varepsilon\|\mathbf{A}\|_2$ has
$$t \ge \log_2\frac1\varepsilon + \frac b2 - 2 + \log_2(1 - \varepsilon) \,.$$
[Shah2024, Proposition 1.1], there without the term $\log_2(1 - \varepsilon)$, which comes from
$\|\mathbf{H} \pm \delta\mathbf{J}\|_2 \ne \|\mathbf{H}\|_2$. -/
theorem logb_inv_add_le_of_forall_specNorm_sub_le {t b : ℕ} (ht : 1 ≤ t) {ε : ℝ} (hε : 0 < ε)
    (hε₁ : ε < 1)
    (alg : Matrix (Fin b → ZMod 2) (Fin b → ZMod 2) ℝ →
      Matrix (Fin b → ZMod 2) (Fin b → ZMod 2) ℂ × ((Fin b → ZMod 2) → ℝ))
    (halg : ∀ A : Matrix (Fin b → ZMod 2) (Fin b → ZMod 2) ℝ, A.IsSymm →
      specNorm (A.map (fun x : ℝ => (x : ℂ)) - (alg (A.map (Real.roundNearest t))).1 *
        Matrix.diagonal (fun i => ((alg (A.map (Real.roundNearest t))).2 i : ℂ)) *
          (alg (A.map (Real.roundNearest t))).1ᴴ) ≤ ε * specNorm A) :
    Real.logb 2 ε⁻¹ + b / 2 - 2 + Real.logb 2 (1 - ε) ≤ t := by
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = 2⁻¹ ^ (s + 1) / 4 := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hsym : (walshHadamard ℝ b).IsSymm := transpose_walshHadamard b
  have hone : Real.roundNearest (s + 1) 1 = 1 ∧ Real.roundNearest (s + 1) (-1) = -1 :=
    roundNearest_near_one (y := 1) (by simp only [sub_self, abs_zero]; positivity)
  have hfl : ∀ i j, ∀ σ ∈ ({1, -1} : Set ℝ),
      Real.roundNearest (s + 1) (walshHadamard ℝ b i j + σ * δ) =
        Real.roundNearest (s + 1) (walshHadamard ℝ b i j) := by
    intro i j σ hσ
    have hσδ : |σ * δ| ≤ δ := by rcases hσ with rfl | rfl <;> simp [abs_of_pos hδpos]
    have hpm : walshHadamard ℝ b i j = 1 ∨ walshHadamard ℝ b i j = -1 := by
      rw [walshHadamard_apply]; split_ifs <;> simp
    rcases hpm with h | h <;> rw [h]
    · have hy : |(1 + σ * δ) - 1| ≤ 2⁻¹ ^ (s + 1) / 4 := by
        rw [add_sub_cancel_left, ← hδdef]; exact hσδ
      rw [(roundNearest_near_one hy).1, hone.1]
    · have hy : |(1 + -(σ * δ)) - 1| ≤ 2⁻¹ ^ (s + 1) / 4 := by
        rw [add_sub_cancel_left, abs_neg, ← hδdef]; exact hσδ
      rw [show -1 + σ * δ = -(1 + -(σ * δ)) by ring, (roundNearest_near_one hy).2, hone.2]
  have hmain := mul_card_le_of_forall_specNorm_sub_le hδpos.le alg halg hsym hfl
  have hcard : (Fintype.card (Fin b → ZMod 2) : ℝ) = 2 ^ b := by
    simp [ZMod.card]
  rw [hcard] at hmain
  have hS2 : specNorm (walshHadamard ℝ b) ^ 2 = 2 ^ b := by
    have h1 := specNorm_conjTranspose_mul_self (walshHadamard ℝ b)
    rw [conjTranspose_walshHadamard, walshHadamard_mul_self, specNorm_real_smul, specNorm_one,
      abs_of_pos (by positivity : (0 : ℝ) < 2 ^ b), mul_one] at h1
    exact h1.symm
  have hSpos : 0 < specNorm (walshHadamard ℝ b) := by
    have h2b : (0 : ℝ) < 2 ^ b := by positivity
    nlinarith [specNorm_nonneg (walshHadamard ℝ b)]
  have h1 : δ * 2 ^ b * (1 - ε) ≤ ε * specNorm (walshHadamard ℝ b) := by
    nlinarith [hmain]
  have hP1 : 0 < δ * 2 ^ b * (1 - ε) := mul_pos (by positivity) (sub_pos.2 hε₁)
  have hlog := Real.log_le_log hP1 h1
  have hL : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hδlog : Real.log δ = -((s : ℝ) + 1) * Real.log 2 - 2 * Real.log 2 := by
    rw [hδdef, Real.log_div (by positivity) (by norm_num), Real.log_pow, Real.log_inv,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have hSlog : 2 * Real.log (specNorm (walshHadamard ℝ b)) = b * Real.log 2 := by
    have h := congrArg Real.log hS2
    rw [Real.log_pow, Real.log_pow] at h
    push_cast at h
    linarith
  rw [Real.log_mul (mul_pos hδpos (by positivity)).ne' (sub_pos.2 hε₁).ne',
    Real.log_mul hδpos.ne' (by positivity), Real.log_pow, hδlog,
    Real.log_mul hε.ne' hSpos.ne'] at hlog
  unfold Real.logb
  rw [Real.log_inv]
  have key : (-Real.log ε + Real.log (1 - ε)) / Real.log 2 ≤
      ((s : ℝ) + 1) - b / 2 + 2 := by
    rw [div_le_iff₀ hL]
    nlinarith [hlog, hSlog]
  have e : -Real.log ε / Real.log 2 + b / 2 - 2 + Real.log (1 - ε) / Real.log 2 =
      (-Real.log ε + Real.log (1 - ε)) / Real.log 2 + b / 2 - 2 := by ring
  rw [e]
  push_cast
  linarith [key]

end NLAlib
