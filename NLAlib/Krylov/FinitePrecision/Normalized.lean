/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.Paige

/-!
# The normalised vectors of a finite-precision Lanczos run

For a run `L : NLAlib.LanczosRun n k`, the computed vectors rescaled to unit length,
$\bar{\mathbf{v}}_j = \mathbf{v}_j/\|\mathbf{v}_j\|$, with the computed coefficients
(`NLAlib.LanczosRun.normalized`, a `NLAlib.LanczosData`), still satisfy the three-term
recurrence up to residuals of order $j\varepsilon\|\mathbf{H}\|_2$, consecutive normalised
vectors are nearly orthogonal in the same sense, and their Gram commutator is of order
$k^2\varepsilon\|\mathbf{H}\|_2$. At a terminal last step ($\beta_k = 0$) the vector
$\bar{\mathbf{v}}_{k+1}$, which is multiplied by $\beta_k$ wherever it enters, is taken to be
$\bar{\mathbf{v}}_1$ (the maintainer's draft allows any unit vector). The backward model
(`NLAlib/Krylov/FinitePrecision/Backward.lean`) dilates these vectors.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `sec:normalized`, `lem:normalized-errors`, `cor:normalized-commutator`.

## Main definitions

* `NLAlib.LanczosRun.normalizedV`, `NLAlib.LanczosRun.normalized`: the normalised run.

## Main results

* `NLAlib.LanczosRun.norm_normalized_recurrenceError_le`,
  `NLAlib.LanczosRun.abs_normalized_adjacentInner_le`: normalised local errors.
* `NLAlib.LanczosRun.specNorm_normalized_gramCommutator_le`: the normalised Gram commutator.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-! ### The normalised run -/

/-- The **normalised Lanczos vectors** $\bar{\mathbf{v}}_j = \mathbf{v}_j/\|\mathbf{v}_j\|$
($\bar{\mathbf{v}}_0 = \mathbf{0}$); at a terminal last step ($\beta_k = 0$) the vector
$\bar{\mathbf{v}}_{k+1}$, which does not enter the recurrence, is taken to be
$\bar{\mathbf{v}}_1$. -/
noncomputable def normalizedV (j : ℕ) : Fin n → ℝ :=
  if j = k + 1 ∧ L.β k = 0 then ‖WithLp.toLp 2 (L.v 1)‖⁻¹ • L.v 1
  else ‖WithLp.toLp 2 (L.v j)‖⁻¹ • L.v j

/-- The **normalised run**: the computed coefficients with the normalised vectors. -/
noncomputable def normalized : LanczosData n k where
  H := L.H
  v := L.normalizedV
  α := L.α
  β := L.β
  transpose_H := L.transpose_H
  k_pos := L.k_pos
  v_zero := by
    have h : ¬(0 = k + 1 ∧ L.β k = 0) := fun h => by omega
    simp only [normalizedV, if_neg h, L.v_zero, smul_zero]
  β_zero := L.β_zero

/-- The computed vectors up to step $k$ are nonzero: $\|\mathbf{v}_j\| > 0$ for
$1 \le j \le k$. -/
theorem norm_v_pos {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k) : 0 < ‖WithLp.toLp 2 (L.v j)‖ := by
  have h := (abs_le.mp (L.abs_norm_v_sq_sub_one_le j h1 h2)).1
  have hε := L.ε_le
  by_contra h0
  have : ‖WithLp.toLp 2 (L.v j)‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
  rw [this] at h
  linarith

/-- The next vector is nonzero when the last step is not terminal. -/
theorem norm_v_succ_pos (hβ : L.β k ≠ 0) : 0 < ‖WithLp.toLp 2 (L.v (k + 1))‖ := by
  have h := (abs_le.mp (L.abs_norm_v_succ_sq_sub_one_le hβ)).1
  have hε := L.ε_le
  by_contra h0
  have : ‖WithLp.toLp 2 (L.v (k + 1))‖ = 0 := le_antisymm (not_lt.mp h0) (norm_nonneg _)
  rw [this] at h
  linarith

/-- The vector after step $j < k$ is nearly unit when $\beta_{j+1} \neq 0$. -/
theorem abs_norm_v_add_two_sq_sub_one_le {j : ℕ} (hj : j < k) (hβ : L.β (j + 1) ≠ 0) :
    |‖WithLp.toLp 2 (L.v (j + 2))‖ ^ 2 - 1| ≤ L.ε := by
  rcases (show j + 1 < k ∨ j + 1 = k by omega) with h | h
  · exact L.abs_norm_v_sq_sub_one_le (j + 2) (by omega) (by omega)
  · subst h
    exact L.abs_norm_v_succ_sq_sub_one_le hβ

/-- Away from the terminal exception, $\bar{\mathbf{v}}_j = \mathbf{v}_j/\|\mathbf{v}_j\|$. -/
theorem normalizedV_of_le {j : ℕ} (hj : j ≤ k) :
    L.normalizedV j = ‖WithLp.toLp 2 (L.v j)‖⁻¹ • L.v j := by
  rw [normalizedV, if_neg (fun h => by omega)]

/-- $\beta_{j+1}\bar{\mathbf{v}}_{j+2} = \beta_{j+1}\mathbf{v}_{j+2}/\|\mathbf{v}_{j+2}\|$ for every
$j$ (at a terminal step both sides vanish). -/
theorem β_smul_normalizedV (j : ℕ) :
    L.β (j + 1) • L.normalizedV (j + 2) =
      L.β (j + 1) • (‖WithLp.toLp 2 (L.v (j + 2))‖⁻¹ • L.v (j + 2)) := by
  unfold normalizedV
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rw [show j + 1 = k by omega, h2, zero_smul, zero_smul]
  · rfl

/-- Ratios of nearly unit lengths: if $\lvert a^2 - 1\rvert \le \varepsilon$ and
$\lvert b^2 - 1\rvert \le \varepsilon$ with $a, b \ge 0$ and $\varepsilon \le 1/100$, then
$\lvert b/a - 1\rvert \le 2\varepsilon$ and $a \ge 99/100$. -/
private theorem nearUnit {a b ε : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hε : ε ≤ 1 / 100)
    (ha : |a ^ 2 - 1| ≤ ε) (hb : |b ^ 2 - 1| ≤ ε) : 99 / 100 ≤ a ∧ |b / a - 1| ≤ 2 * ε := by
  have ha' := abs_le.mp ha
  have hb' := abs_le.mp hb
  have ha1 : 99 / 100 ≤ a := by nlinarith
  have hb1 : 99 / 100 ≤ b := by nlinarith
  refine ⟨ha1, ?_⟩
  have hapos : 0 < a := by linarith
  rw [show b / a - 1 = (b - a) / a by field_simp, abs_div, abs_of_pos hapos,
    div_le_iff₀ hapos]
  have hab : |b - a| * (a + b) ≤ 2 * ε := by
    rw [← abs_of_pos (show 0 < a + b by linarith), ← abs_mul,
      show (b - a) * (a + b) = (b ^ 2 - 1) - (a ^ 2 - 1) by ring]
    exact (abs_sub _ _).trans (by linarith)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans ha
  nlinarith [abs_nonneg (b - a)]

/-- The normalised vectors $\bar{\mathbf{v}}_1, \dots, \bar{\mathbf{v}}_{k+1}$ are unit vectors. -/
theorem norm_normalizedV {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k + 1) :
    ‖WithLp.toLp 2 (L.normalizedV j)‖ = 1 := by
  have hunit : ∀ x : Fin n → ℝ, 0 < ‖WithLp.toLp 2 x‖ →
      ‖WithLp.toLp 2 (‖WithLp.toLp 2 x‖⁻¹ • x)‖ = 1 := fun x hx => by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hx,
      inv_mul_cancel₀ hx.ne']
  unfold normalizedV
  split_ifs with h
  · exact hunit _ (L.norm_v_pos le_rfl L.k_pos)
  · rcases (show j ≤ k ∨ j = k + 1 by omega) with hj | hj
    · exact hunit _ (L.norm_v_pos h1 hj)
    · subst hj
      exact hunit _ (L.norm_v_succ_pos (fun hβ => h ⟨rfl, hβ⟩))

/-- **Normalised local errors**: the normalised vectors satisfy the computed recurrence up to
$\|\bar{\mathbf{f}}_j\| \le 12(j + 1)\varepsilon\|\mathbf{H}\|_2$, $j < k$.
No printed source; the maintainer's draft, `lem:normalized-errors`, states
$\lesssim_k \varepsilon\|\mathbf{A}\|_2$. -/
theorem norm_normalized_recurrenceError_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.normalized.recurrenceError j)‖ ≤ 12 * (j + 1) * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  set d := ‖WithLp.toLp 2 (L.v (j + 1))‖ with hd
  set dj := ‖WithLp.toLp 2 (L.v j)‖ with hdj
  set d2 := ‖WithLp.toLp 2 (L.v (j + 2))‖ with hd2
  have hdsq : |d ^ 2 - 1| ≤ L.ε := L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
  have hd1 : 99 / 100 ≤ d := (nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hdsq hdsq).1
  have hdpos : 0 < d := by linarith
  have heq : L.normalized.recurrenceError j = d⁻¹ • L.recurrenceError j +
      (L.β j * (d⁻¹ - dj⁻¹)) • L.v j + (L.β (j + 1) * (d⁻¹ - d2⁻¹)) • L.v (j + 2) := by
    have h1 := L.normalizedV_of_le (j := j + 1) (by omega)
    have h0 := L.normalizedV_of_le (j := j) (by omega)
    have h2 := L.β_smul_normalizedV j
    simp only [LanczosData.recurrenceError, normalized, recurrenceError, toLanczosData]
    rw [h2, h1, h0, Matrix.mulVec_smul]
    module
  -- each correction term is at most `2 ε β`
  have hterm : ∀ (c : ℝ) (i : ℕ), (i = 0 ∨ |‖WithLp.toLp 2 (L.v i)‖ ^ 2 - 1| ≤ L.ε) →
      (i = 0 → L.v i = 0) →
      ‖WithLp.toLp 2 ((c * (d⁻¹ - ‖WithLp.toLp 2 (L.v i)‖⁻¹)) • L.v i)‖ ≤ |c| * (2 * L.ε) := by
    intro c i hi hi0
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_mul, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    rcases hi with hi | hi
    · rw [hi0 hi, WithLp.toLp_zero, norm_zero, mul_zero]
      positivity
    · set e := ‖WithLp.toLp 2 (L.v i)‖
      obtain ⟨he1, hratio⟩ := nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hi hi
      obtain ⟨-, hr⟩ := nearUnit (norm_nonneg _) (norm_nonneg (WithLp.toLp 2 (L.v i))) hε1 hdsq hi
      have hepos : 0 < e := by linarith
      calc |d⁻¹ - e⁻¹| * e = |e / d - 1| := by
            rw [← abs_of_pos hepos, ← abs_mul, abs_of_pos hepos]
            congr 1
            field_simp
        _ ≤ 2 * L.ε := hr
  have hA : ‖WithLp.toLp 2 ((L.β j * (d⁻¹ - dj⁻¹)) • L.v j)‖ ≤
      5 / 4 * j * specNorm L.H * (2 * L.ε) := by
    refine (hterm (L.β j) j ?_ ?_).trans ?_
    · rcases Nat.eq_zero_or_pos j with h | h
      · exact Or.inl h
      · exact Or.inr (L.abs_norm_v_sq_sub_one_le j h hj.le)
    · intro h; rw [h]; exact L.v_zero
    · rw [abs_of_nonneg (L.β_nonneg j hj.le)]
      gcongr
      exact L.β_le hj.le
  have hB : ‖WithLp.toLp 2 ((L.β (j + 1) * (d⁻¹ - d2⁻¹)) • L.v (j + 2))‖ ≤
      5 / 4 * (j + 1) * specNorm L.H * (2 * L.ε) := by
    by_cases hβ : L.β (j + 1) = 0
    · rw [hβ, zero_mul, zero_smul, WithLp.toLp_zero, norm_zero]
      positivity
    refine (hterm (L.β (j + 1)) (j + 2) (Or.inr (L.abs_norm_v_add_two_sq_sub_one_le hj hβ))
      (fun h => by omega)).trans ?_
    rw [abs_of_nonneg (L.β_nonneg (j + 1) (by omega))]
    gcongr
    have := L.β_le (j := j + 1) (by omega)
    push_cast at this
    exact this
  have hF : ‖WithLp.toLp 2 (d⁻¹ • L.recurrenceError j)‖ ≤
      100 / 99 * (6 * (j + 1) * L.ε * specNorm L.H) := by
    rw [WithLp.toLp_smul, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hdpos]
    gcongr
    · rw [inv_le_comm₀ hdpos (by norm_num)]
      linarith
    · simpa only [lanczosRecurrenceErrorFactor_def] using L.norm_recurrenceError_le hj
  rw [heq, WithLp.toLp_add, WithLp.toLp_add]
  refine (norm_add_le _ _).trans ?_
  refine (add_le_add_left (norm_add_le _ _) _).trans ?_
  have hj0 : (0 : ℝ) ≤ j := j.cast_nonneg
  have h0 : 0 ≤ L.ε * specNorm L.H := by positivity
  nlinarith [mul_nonneg hj0 h0]

/-- **Normalised local orthogonality**:
$\lvert\bar p_j\rvert \le 8(j + 1)\varepsilon\|\mathbf{H}\|_2$, $j < k$. No printed source; the
maintainer's draft, `lem:normalized-errors`. -/
theorem abs_normalized_adjacentInner_le {j : ℕ} (hj : j < k) :
    |L.normalized.adjacentInner j| ≤ 8 * (j + 1) * L.ε * specNorm L.H := by
  have hε1 := L.ε_le
  have hH := specNorm_nonneg L.H
  set d := ‖WithLp.toLp 2 (L.v (j + 1))‖
  set d2 := ‖WithLp.toLp 2 (L.v (j + 2))‖
  have heq : L.normalized.adjacentInner j = d⁻¹ * d2⁻¹ * L.adjacentInner j := by
    have h1 := L.normalizedV_of_le (j := j + 1) (by omega)
    have h2 := L.β_smul_normalizedV j
    simp only [LanczosData.adjacentInner, normalized, adjacentInner, toLanczosData]
    rw [h2, h1, smul_comm (L.β (j + 1)), dotProduct_smul, smul_dotProduct, smul_eq_mul,
      smul_eq_mul]
    ring
  by_cases hβ : L.β (j + 1) = 0
  · have : L.normalized.adjacentInner j = 0 := by
      simp only [LanczosData.adjacentInner, normalized, hβ, zero_smul, dotProduct_zero]
    rw [this, abs_zero]
    have := L.ε_nonneg
    positivity
  have hdsq : |d ^ 2 - 1| ≤ L.ε := L.abs_norm_v_sq_sub_one_le (j + 1) (by omega) (by omega)
  have hd2sq : |d2 ^ 2 - 1| ≤ L.ε := L.abs_norm_v_add_two_sq_sub_one_le hj hβ
  have hd1 := (nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hdsq hdsq).1
  have hd21 := (nearUnit (norm_nonneg _) (norm_nonneg _) hε1 hd2sq hd2sq).1
  have hp := L.abs_adjacentInner_le hj
  rw [lanczosAdjacentInnerFactor_def] at hp
  have hinv : d⁻¹ * d2⁻¹ ≤ 100 / 99 * (100 / 99) := by
    have h1 : d⁻¹ ≤ 100 / 99 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    have h2 : d2⁻¹ ≤ 100 / 99 := by rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
    exact mul_le_mul h1 h2 (by positivity) (by norm_num)
  rw [heq, abs_mul, abs_of_pos (by positivity : 0 < d⁻¹ * d2⁻¹)]
  calc d⁻¹ * d2⁻¹ * |L.adjacentInner j|
      ≤ 100 / 99 * (100 / 99) * (7 * (j + 1) * L.ε * specNorm L.H) := by
        gcongr
    _ ≤ 8 * (j + 1) * L.ε * specNorm L.H := by
        have : 0 ≤ (j + 1) * L.ε * specNorm L.H := by have := L.ε_nonneg; positivity
        nlinarith

/-- The normalised residual is small:
$\|\bar{\mathbf{F}}_k\|_{\mathsf{F}} \le 12k\sqrt{k}\,\varepsilon\|\mathbf{H}\|_2$. -/
theorem frobNorm_normalized_residual_le :
    frobNorm L.normalized.residual ≤ 12 * k * Real.sqrt k * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hcol : ∀ j : Fin k, ‖WithLp.toLp 2 (L.normalized.residual.col j)‖ ≤
      12 * k * L.ε * specNorm L.H := by
    intro j
    have hjk : ((j : ℕ) : ℝ) + 1 ≤ k := by exact_mod_cast j.2
    refine (L.norm_normalized_recurrenceError_le j.2).trans ?_
    gcongr
  have hsq : frobNorm L.normalized.residual ^ 2 ≤
      (12 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
    rw [frobNorm_sq_eq_sum_col]
    calc ∑ j, ‖WithLp.toLp 2 (L.normalized.residual.col j)‖ ^ 2
        ≤ ∑ _j : Fin k, (12 * k * L.ε * specNorm L.H) ^ 2 :=
          Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hcol j) 2
      _ = (12 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            show (12 * k * Real.sqrt k * L.ε * specNorm L.H) ^ 2 =
              (12 * k * L.ε * specNorm L.H) ^ 2 * Real.sqrt k ^ 2 by ring,
            Real.sq_sqrt (Nat.cast_nonneg k)]
          ring
  exact (sq_le_sq₀ (frobNorm_nonneg _) (by positivity)).1 hsq

/-- **The normalised Gram commutator is small**:
$\|\bar{\mathbf{M}}_k\|_2 \le 40k^2\varepsilon\|\mathbf{H}\|_2$. No printed source; the
maintainer's draft, `cor:normalized-commutator`. -/
theorem specNorm_normalized_gramCommutator_le :
    specNorm L.normalized.gramCommutator ≤ 40 * k ^ 2 * L.ε * specNorm L.H := by
  have hε0 := L.ε_nonneg
  have hH := specNorm_nonneg L.H
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast L.k_pos
  have ha : ∀ j < k, |L.normalized.adjacentInner j| ≤ 8 * k * L.ε * specNorm L.H :=
    fun j hj => (L.abs_normalized_adjacentInner_le hj).trans (by
      have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hj
      gcongr)
  have hb : ∀ j < k, |L.normalized.β j| ≤ 5 / 4 * k * specNorm L.H := fun j hj => by
    change |L.β j| ≤ _
    rw [abs_of_nonneg (L.β_nonneg j hj.le)]
    refine (L.β_le hj.le).trans ?_
    have : (j : ℝ) ≤ k := by exact_mod_cast hj.le
    gcongr
  have hg : ∀ i, |L.normalized.normSqDefect i| ≤ 0 := fun i => by
    simp only [LanczosData.normSqDefect, normalized]
    rw [L.norm_normalizedV (by omega) (by omega)]
    norm_num
  have hV : frobNorm L.normalized.basis = Real.sqrt k := by
    rw [← Real.sqrt_sq (frobNorm_nonneg _), frobNorm_sq_eq_sum_col]
    congr 1
    have : ∀ j : Fin k, ‖WithLp.toLp 2 (L.normalized.basis.col j)‖ = 1 := fun j =>
      L.norm_normalizedV (j := (j : ℕ) + 1) (by omega) (by omega)
    simp only [this, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  have hF := L.frobNorm_normalized_residual_le
  have h := L.normalized.specNorm_gramCommutator_le ha hb hg
  rw [hV, mul_zero, mul_zero, mul_zero, add_zero] at h
  refine h.trans ?_
  have hsk : Real.sqrt k * Real.sqrt k = k := Real.mul_self_sqrt (Nat.cast_nonneg k)
  have h2 : 2 * (Real.sqrt k * frobNorm L.normalized.residual) ≤
      24 * k ^ 2 * L.ε * specNorm L.H := by
    calc 2 * (Real.sqrt k * frobNorm L.normalized.residual)
        ≤ 2 * (Real.sqrt k * (12 * k * Real.sqrt k * L.ε * specNorm L.H)) := by gcongr
      _ = 24 * (Real.sqrt k * Real.sqrt k) * k * L.ε * specNorm L.H := by ring
      _ = 24 * k ^ 2 * L.ε * specNorm L.H := by rw [hsk]; ring
  have h0 : 0 ≤ L.ε * specNorm L.H := by positivity
  nlinarith [mul_le_mul_of_nonneg_right (show (k : ℝ) ≤ k ^ 2 by nlinarith) h0]

end LanczosRun

end NLAlib
