/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounds on $s \log s$

$\lvert s \log s \rvert \le s^2 + 1$ for $s \ge 0$: the domination that makes $g^2 \log g^2$
integrable once $g^4$ is, used for entropies of squares.
$\lvert G s \log(G s) \rvert \le \lvert G \log G \rvert + G$ for $G \ge 0$ and $s \in [0, 1]$:
the domination of $x \log x$ along a shrinking of $x$, used to pass to the limit in an entropy
under a truncation or a cutoff. $\varepsilon/2 \le \log(1 + \varepsilon)$ on $(0, 1]$, and the
threshold arithmetic of depth bounds of the form $q \ge C\log(N/\varepsilon)/s$ (the asymptotic
forms of the block Krylov bounds). Upstream candidates for
`Mathlib.Analysis.SpecialFunctions.Log.Basic`.

## Main results

* `Real.abs_mul_log_le_sq_add_one`.
* `Real.abs_mul_mul_log_mul_le`.
* `Real.div_two_le_log_one_add`: $\varepsilon/2 \le \log(1 + \varepsilon)$ for
  $0 < \varepsilon \le 1$.
* `Real.one_half_le_log_div`, `Real.le_add_mul_of_le_add_mul_exp`,
  `Real.one_le_and_log_div_le_sub_one_mul`, `Real.two_le_and_exp_log_four_mul_sq_div_le_one_add`,
  `Real.mul_pow_le_of_mul_log_le`, `Real.one_sub_pow_le_of_log_le_mul`: depth and iteration
  thresholds.
-/

@[expose] public section

namespace Real

/-- $\lvert s \log s \rvert \le s^2 + 1$ for $s \ge 0$. -/
theorem abs_mul_log_le_sq_add_one {s : ℝ} (hs : 0 ≤ s) : |s * log s| ≤ s ^ 2 + 1 := by
  rcases hs.eq_or_lt with rfl | hs'
  · simp
  rcases le_or_gt s 1 with h1 | h1
  · have := abs_log_mul_self_lt s hs' h1
    rw [mul_comm]
    nlinarith [sq_nonneg s]
  · have hl : 0 ≤ log s := log_nonneg h1.le
    have hl2 : log s ≤ s - 1 := log_le_sub_one_of_pos hs'
    rw [abs_of_nonneg (mul_nonneg hs hl)]
    nlinarith

/-- $\lvert G s \log(G s) \rvert \le \lvert G \log G \rvert + G$ for $G \ge 0$ and
$s \in [0, 1]$: shrinking $x \ge 0$ by a factor in $[0, 1]$ makes $\lvert x \log x \rvert$ exceed
its old value by at most $x$. -/
theorem abs_mul_mul_log_mul_le {G s : ℝ} (hG : 0 ≤ G) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    |G * s * log (G * s)| ≤ |G * log G| + G := by
  rcases hG.eq_or_lt with rfl | hG'
  · simp
  rcases hs0.eq_or_lt with rfl | hs'
  · simp only [mul_zero, zero_mul, abs_zero]; positivity
  rw [log_mul hG'.ne' hs'.ne']
  have e : G * s * (log G + log s) = s * (G * log G) + G * (log s * s) := by
    ring
  rw [e]
  have h1 := abs_log_mul_self_lt s hs' hs1
  calc |s * (G * log G) + G * (log s * s)|
      ≤ |s * (G * log G)| + |G * (log s * s)| := abs_add_le _ _
    _ = s * |G * log G| + G * |log s * s| := by
        rw [abs_mul s (G * log G), abs_mul G (log s * s), abs_of_nonneg hs0, abs_of_nonneg hG]
    _ ≤ 1 * |G * log G| + G * 1 := by gcongr
    _ = |G * log G| + G := by ring

/-- The logarithm in the depth thresholds of the asymptotic forms is at least $1/2$: for
$N \ge 1$ and $0 < \varepsilon \le 1/2$, $\log(N/\varepsilon) \ge \log 2 \ge 1/2$. -/
theorem one_half_le_log_div {N ε : ℝ} (hN : 1 ≤ N) (hε : 0 < ε) (hε₀ : ε ≤ 1 / 2) :
    1 / 2 ≤ Real.log (N / ε) := by
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h ⊢
    linarith
  exact hlog2.trans (Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hε]; linarith))

/-- The threshold arithmetic of the asymptotic forms of the Krylov bounds: if
$E \le aO + c\,e^{y}\kappa T$ with $0 \le c \le 4$, $\kappa T \le N^2 O$ and $O \ge 0$, then for
$N \ge 1$, $0 < \varepsilon \le 1/2$ and $y \le -4\log(N/\varepsilon)$,
$$E \le (a + \varepsilon)\,O\,,$$
since then $4N^2e^{y} \le \varepsilon$. -/
theorem le_add_mul_of_le_add_mul_exp {E O T κ a c y N ε : ℝ}
    (hE : E ≤ a * O + c * Real.exp y * κ * T) (hO : 0 ≤ O) (hc0 : 0 ≤ c) (hc : c ≤ 4)
    (hT : κ * T ≤ N ^ 2 * O) (hN : 1 ≤ N) (hε : 0 < ε) (hε₀ : ε ≤ 1 / 2)
    (hy : y ≤ -(4 * Real.log (N / ε))) : E ≤ (a + ε) * O := by
  have hL : Real.log (N / ε) = Real.log N - Real.log ε := Real.log_div (by positivity) hε.ne'
  have hlogε : Real.log ε ≤ -Real.log 2 := by
    rw [← Real.log_inv]
    exact Real.log_le_log hε (by linarith)
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hN
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hNe : 4 * N ^ 2 * Real.exp y ≤ ε := by
    have h : 4 * N ^ 2 = Real.exp (Real.log 4 + 2 * Real.log N) := by
      rw [Real.exp_add, Real.exp_log (by norm_num), two_mul, Real.exp_add,
        Real.exp_log (by positivity)]
      ring
    rw [h, ← Real.exp_add]
    calc Real.exp (Real.log 4 + 2 * Real.log N + y) ≤ Real.exp (Real.log ε) :=
          Real.exp_le_exp.2 (by rw [hL] at hy; linarith)
      _ = ε := Real.exp_log hε
  have hce : 0 ≤ c * Real.exp y := mul_nonneg hc0 (Real.exp_pos y).le
  have h1 : c * Real.exp y * κ * T ≤ c * Real.exp y * (N ^ 2 * O) := by
    rw [mul_assoc (c * Real.exp y)]
    exact mul_le_mul_of_nonneg_left hT hce
  have h2 : c * Real.exp y * N ^ 2 ≤ ε :=
    calc c * Real.exp y * N ^ 2 = c * (Real.exp y * N ^ 2) := by ring
      _ ≤ 4 * (Real.exp y * N ^ 2) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = 4 * N ^ 2 * Real.exp y := by ring
      _ ≤ ε := hNe
  have h3 : c * Real.exp y * (N ^ 2 * O) ≤ ε * O := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right h2 hO
  linarith

/-- The depth threshold of the gapped asymptotic forms of block Krylov iteration: for $N \ge 1$,
$0 < \varepsilon \le 1/2$, $0 < s \le 1$ and $q \ge 3\log(N/\varepsilon)/s$, both $q \ge 1$ and
$(q - 1)s \ge \log(N/\varepsilon)$. -/
theorem one_le_and_log_div_le_sub_one_mul {N ε s : ℝ} {q : ℕ} (hN : 1 ≤ N) (hε : 0 < ε)
    (hε₀ : ε ≤ 1 / 2) (hs : 0 < s) (hs1 : s ≤ 1) (hq : 3 * Real.log (N / ε) / s ≤ q) :
    1 ≤ q ∧ Real.log (N / ε) ≤ ((q : ℝ) - 1) * s := by
  have hL := one_half_le_log_div hN hε hε₀
  have hqs : 3 * Real.log (N / ε) ≤ q * s := by rwa [div_le_iff₀ hs] at hq
  refine ⟨?_, by nlinarith⟩
  have h : (0 : ℝ) < q := lt_of_lt_of_le (div_pos (by linarith) hs) hq
  exact_mod_cast h

/-- $\varepsilon/2 \le \log(1 + \varepsilon)$ for $0 < \varepsilon \le 1$. -/
theorem div_two_le_log_one_add {ε : ℝ} (hε : 0 < ε) (hε₁ : ε ≤ 1) :
    ε / 2 ≤ Real.log (1 + ε) := by
  have h := Real.one_sub_inv_le_log_of_pos (x := 1 + ε) (by linarith)
  have hinv : (1 + ε)⁻¹ * (1 + ε) = 1 := inv_mul_cancel₀ (by positivity)
  have hpos : 0 < (1 + ε)⁻¹ := inv_pos.2 (by positivity)
  nlinarith

/-- The depth threshold of the Tropp–Webber form of the gapless bound for block Krylov
iteration: for $N \ge 1$, $0 < \varepsilon \le 1$ and $q \ge 4\log(N + 1)/\sqrt{\varepsilon}$,
$q \ge 2$, and every $R$ with $1 \le R \le 1 + N^2$ has
$$\exp\Bigl(\frac{\log^2(4R)}{16(q - 1)^2}\Bigr) \le 1 + \varepsilon\,,$$
since $\log(4R) \le 4\log(N + 1) \le 2(q - 1)\sqrt{\varepsilon}$. -/
theorem two_le_and_exp_log_four_mul_sq_div_le_one_add {N ε : ℝ} {q : ℕ} (hN : 1 ≤ N)
    (hε : 0 < ε) (hε₁ : ε ≤ 1) (hq : 4 * Real.log (N + 1) / Real.sqrt ε ≤ q) :
    2 ≤ q ∧ ∀ R : ℝ, 1 ≤ R → R ≤ 1 + N ^ 2 →
      Real.exp (Real.log (4 * R) ^ 2 / (16 * ((q : ℝ) - 1) ^ 2)) ≤ 1 + ε := by
  set M := Real.log (N + 1) with hM
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (x := 2) (by norm_num)
    norm_num at h ⊢
    linarith
  have hM2 : 1 / 2 ≤ M := hlog2.trans (Real.log_le_log (by norm_num) (by linarith))
  have hs : 0 < Real.sqrt ε := Real.sqrt_pos.2 hε
  have hs1 : Real.sqrt ε ≤ 1 := Real.sqrt_le_one.2 hε₁
  have hqs : 4 * M ≤ q * Real.sqrt ε := by rwa [div_le_iff₀ hs] at hq
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hq2 : (2 : ℝ) ≤ q := by nlinarith
  refine ⟨by exact_mod_cast hq2, fun R hR1 hR => ?_⟩
  have hq1 : 2 * M ≤ ((q : ℝ) - 1) * Real.sqrt ε := by nlinarith
  have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
  have hq1' : 4 * M ^ 2 ≤ ((q : ℝ) - 1) ^ 2 * ε := by
    rw [← hsq]
    nlinarith
  have hlog4R0 : 0 ≤ Real.log (4 * R) := Real.log_nonneg (by linarith)
  have hlog4R : Real.log (4 * R) ≤ 4 * M := by
    have h4 : 4 * R ≤ (N + 1) ^ 4 := by nlinarith [sq_nonneg (N - 1), sq_nonneg N]
    calc Real.log (4 * R) ≤ Real.log ((N + 1) ^ 4) := Real.log_le_log (by linarith) h4
      _ = 4 * M := by rw [Real.log_pow, ← hM]; norm_num
  have hden : 0 < 16 * ((q : ℝ) - 1) ^ 2 := by nlinarith
  have hratio : Real.log (4 * R) ^ 2 / (16 * ((q : ℝ) - 1) ^ 2) ≤ Real.log (1 + ε) := by
    rw [div_le_iff₀ hden]
    have := div_two_le_log_one_add hε hε₁
    nlinarith
  calc Real.exp (Real.log (4 * R) ^ 2 / (16 * ((q : ℝ) - 1) ^ 2))
      ≤ Real.exp (Real.log (1 + ε)) := Real.exp_le_exp.2 hratio
    _ = 1 + ε := Real.exp_log (by linarith)

/-- The iteration threshold of a squared error contracting by $1/4$ per step: for
$0 < \tau \le 1/2$ and $q \ge 4\log(1/\tau)$, $16 \cdot (1/2)^{2q+1} \le \tau$. -/
theorem mul_pow_le_of_mul_log_le {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 2) {q : ℕ}
    (hq : 4 * Real.log (1 / τ) ≤ q) : 16 * (1 / 2 : ℝ) ^ (2 * q + 1) ≤ τ := by
  have hl2 : 1 / 2 ≤ Real.log 2 := by
    have := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    linarith
  have hL : Real.log 2 ≤ Real.log (1 / τ) :=
    Real.log_le_log (by norm_num) (by rw [le_div_iff₀ hτ]; linarith)
  rw [← Real.log_le_log_iff (by positivity) hτ, Real.log_mul (by norm_num) (by positivity),
    Real.log_pow, show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow, one_div, Real.log_inv]
  rw [one_div, Real.log_inv] at hL hq
  push_cast
  nlinarith

/-- The iteration threshold of a contraction factor: for $c \le 1$, $\varepsilon > 0$ and
$\log(1/\varepsilon) \le c q$, $(1 - c)^q \le \varepsilon$. With $c = 1/\kappa^2$ it is the
iteration count $q \ge \kappa^2 \log(1/\varepsilon)$ of a method contracting by $1 - c$ per
step. -/
theorem one_sub_pow_le_of_log_le_mul {c ε : ℝ} (hc1 : c ≤ 1) (hε : 0 < ε) {q : ℕ}
    (hq : Real.log (1 / ε) ≤ c * q) : (1 - c) ^ q ≤ ε := by
  calc (1 - c) ^ q ≤ Real.exp (-c) ^ q :=
        pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-c)]) q
    _ = Real.exp (-(c * q)) := by rw [← Real.exp_nat_mul]; ring_nf
    _ ≤ Real.exp (Real.log ε) := by
        refine Real.exp_le_exp.mpr ?_
        rw [one_div, Real.log_inv] at hq
        linarith
    _ = ε := Real.exp_log hε

end Real
