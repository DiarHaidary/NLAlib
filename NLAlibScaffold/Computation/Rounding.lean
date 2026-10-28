/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Accumulated rounding errors

The constant $\gamma_n = nu/(1 - nu)$ of the standard model of floating-point arithmetic,
`NLAlib.Computation.roundingFactor n u`, and its algebra: a product of $n$ factors
$(1 + \delta_i)^{\pm 1}$ with $\lvert \delta_i \rvert \le u$ is $1 + \theta_n$ with
$\lvert \theta_n \rvert \le \gamma_n$, and the rules that combine such $\theta$'s. The relation
`NLAlib.Computation.RelErr u a z` says that $z$ is $a$ with relative error at most $u$, the error
clause of the model (2.4) of [Higham2002]. Every lemma assumes $nu < 1$, under which
$\gamma_n$ is finite. Design: `docs/design/Computation-Rounding.md` (R1, R2).

## Main definitions

* `NLAlib.Computation.roundingFactor`: $\gamma_n$.
* `NLAlib.Computation.RelErr`: relative error at most $u$.

## Main results

* `NLAlib.Computation.abs_prod_one_add_zpow_sub_one_le`: the product of $n$ factors
  $(1 + \delta_i)^{\pm 1}$ is $1 + \theta_n$, $\lvert \theta_n \rvert \le \gamma_n$.
* `NLAlib.Computation.roundingFactor_add_add_mul_le`:
  $\gamma_k + \gamma_j + \gamma_k\gamma_j \le \gamma_{k+j}$.
* `NLAlib.Computation.abs_one_add_mul_one_add_sub_one_le`: $(1 + \theta_k)(1 + \theta_j) =
  1 + \theta_{k+j}$.
-/

@[expose] public section

namespace NLAlib.Computation

/-- **The accumulated rounding factor** $\gamma_n = nu/(1 - nu)$ of [Higham2002, §3.1], the
bound on $n$ accumulated relative errors of size at most $u$. It is meaningful for $nu < 1$, which
every lemma about it assumes. -/
noncomputable def roundingFactor (n : ℕ) (u : ℝ) : ℝ := n * u / (1 - n * u)

/-- `RelErr u a z`: $z = a(1 + \delta)$ for some $\lvert \delta \rvert \le u$; the error clause of
the standard model [Higham2002, §2.2], (2.4) there. -/
def RelErr (u a z : ℝ) : Prop := ∃ δ : ℝ, |δ| ≤ u ∧ z = a * (1 + δ)

variable {u : ℝ} {n k j : ℕ}

/-- **$\gamma_0 = 0$.** [Higham2002, §3.1]. -/
theorem roundingFactor_zero : roundingFactor 0 u = 0 := by
  simp [roundingFactor]

/-- **$1 + \gamma_n = (1 - nu)^{-1}$** for $nu < 1$. [Higham2002, §3.1]. -/
theorem one_add_roundingFactor (hn : n * u < 1) : 1 + roundingFactor n u = (1 - n * u)⁻¹ := by
  have : 1 - n * u ≠ 0 := by linarith
  rw [roundingFactor]
  field_simp
  ring

/-- **$\gamma_n \ge nu$** for $0 \le u$ and $nu < 1$. [Higham2002, §3.1]. -/
theorem le_roundingFactor (hu : 0 ≤ u) (hn : n * u < 1) : n * u ≤ roundingFactor n u :=
  le_div_self (by positivity) (by linarith) (by linarith [show 0 ≤ (n : ℝ) * u by positivity])

/-- **$\gamma_n \ge 0$** for $0 \le u$ and $nu < 1$. [Higham2002, §3.1]. -/
theorem roundingFactor_nonneg (hu : 0 ≤ u) (hn : n * u < 1) : 0 ≤ roundingFactor n u :=
  (show 0 ≤ (n : ℝ) * u by positivity).trans (le_roundingFactor hu hn)

/-- **$\gamma_1 \ge u$**, so a single rounding error is within $\gamma_1$: for $0 \le u < 1$,
$u \le \gamma_1$. [Higham2002, §3.1]. -/
theorem le_roundingFactor_one (hu : 0 ≤ u) (hu1 : u < 1) : u ≤ roundingFactor 1 u := by
  simpa using le_roundingFactor (n := 1) hu (by simpa using hu1)

/-- **$\gamma_n$ is monotone in $n$**: for $0 \le u$, $k \le n$ and $nu < 1$,
$\gamma_k \le \gamma_n$. [Higham2002, §3.1]. -/
theorem roundingFactor_le_roundingFactor (hu : 0 ≤ u) (hkn : k ≤ n) (hn : n * u < 1) :
    roundingFactor k u ≤ roundingFactor n u := by
  have hk : (k : ℝ) * u ≤ n * u := by gcongr
  have h := inv_anti₀ (by linarith) (by linarith : 1 - n * u ≤ 1 - k * u)
  rw [← one_add_roundingFactor hn, ← one_add_roundingFactor (hk.trans_lt hn)] at h
  linarith

/-- **Products of rounding errors** [Higham2002, Lemma 3.1]: for $\lvert \delta_i \rvert \le u$,
exponents $\rho_i = \pm 1$ ($i$ in a finite set $s$ of $n$ elements) and $nu < 1$,
$$\Bigl\lvert \prod_{i \in s} (1 + \delta_i)^{\rho_i} - 1 \Bigr\rvert \le \gamma_n\,.$$ -/
theorem abs_prod_one_add_zpow_sub_one_le {ι : Type} (s : Finset ι) (δ : ι → ℝ) (ρ : ι → ℤ)
    (hδ : ∀ i ∈ s, |δ i| ≤ u) (hρ : ∀ i ∈ s, ρ i = 1 ∨ ρ i = -1) (hn : s.card * u < 1) :
    |∏ i ∈ s, (1 + δ i) ^ ρ i - 1| ≤ roundingFactor s.card u := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨i₀, hi₀⟩
  · simp [roundingFactor]
  have hu : 0 ≤ u := (abs_nonneg _).trans (hδ i₀ hi₀)
  have hcard : (1 : ℝ) ≤ s.card := by exact_mod_cast Finset.card_pos.mpr ⟨i₀, hi₀⟩
  have h1u : 0 < 1 - u := by nlinarith
  -- each factor lies in `[1 - u, (1 - u)⁻¹]`, as `1 + u ≤ (1 - u)⁻¹`
  have hinv : 1 + u ≤ (1 - u)⁻¹ := by
    rw [← one_div, le_div_iff₀ h1u]; nlinarith
  have hfac : ∀ i ∈ s, 1 - u ≤ (1 + δ i) ^ ρ i ∧ (1 + δ i) ^ ρ i ≤ (1 - u)⁻¹ := by
    intro i hi
    obtain ⟨hlo, hhi⟩ := abs_le.mp (hδ i hi)
    have hpos : 0 < 1 + δ i := by linarith
    rcases hρ i hi with h | h <;> simp only [h, zpow_one, zpow_neg]
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨(le_inv_comm₀ h1u hpos).mpr (by linarith), inv_anti₀ h1u (by linarith)⟩
  have hlo : (1 - u) ^ s.card ≤ ∏ i ∈ s, (1 + δ i) ^ ρ i := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun _ _ => h1u.le) (fun i hi => (hfac i hi).1)
  have hhi : ∏ i ∈ s, (1 + δ i) ^ ρ i ≤ ((1 - u) ^ s.card)⁻¹ := by
    rw [← inv_pow, ← Finset.prod_const]
    exact Finset.prod_le_prod (fun i hi => h1u.le.trans (hfac i hi).1) (fun i hi => (hfac i hi).2)
  -- Bernoulli's inequality: `1 - nu ≤ (1 - u)^n`
  have hbern : 1 - s.card * u ≤ (1 - u) ^ s.card := by
    simpa [sub_eq_add_neg] using one_add_mul_le_pow (a := -u) (by linarith) s.card
  have hup := inv_anti₀ (by linarith) hbern
  rw [← one_add_roundingFactor hn] at hup
  have := le_roundingFactor hu hn
  rw [abs_le]
  constructor <;> linarith

/-- **Adding accumulated errors** [Higham2002, Lemma 3.3]: for $0 \le u$ and $(k + j)u < 1$,
$\gamma_k + \gamma_j + \gamma_k\gamma_j \le \gamma_{k+j}$. -/
theorem roundingFactor_add_add_mul_le (hu : 0 ≤ u) (hkj : (k + j : ℕ) * u < 1) :
    roundingFactor k u + roundingFactor j u + roundingFactor k u * roundingFactor j u ≤
      roundingFactor (k + j) u := by
  have hk : (k : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; omega) hkj
  have hj : (j : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; omega) hkj
  have hle : 1 - (k + j : ℕ) * u ≤ (1 - k * u) * (1 - j * u) := by
    push_cast; nlinarith [show 0 ≤ (k : ℝ) * u * (j * u) by positivity]
  have h := inv_anti₀ (by linarith) hle
  rw [mul_inv, ← one_add_roundingFactor hk, ← one_add_roundingFactor hj,
    ← one_add_roundingFactor hkj] at h
  linarith

/-- **Composing accumulated errors** [Higham2002, Lemma 3.3]: if
$\lvert \theta \rvert \le \gamma_k$ and $\lvert \theta' \rvert \le \gamma_j$, $0 \le u$ and
$(k + j)u < 1$, then $\lvert (1 + \theta)(1 + \theta') - 1 \rvert \le \gamma_{k+j}$. -/
theorem abs_one_add_mul_one_add_sub_one_le (hu : 0 ≤ u) (hkj : (k + j : ℕ) * u < 1)
    {θ θ' : ℝ} (hθ : |θ| ≤ roundingFactor k u) (hθ' : |θ'| ≤ roundingFactor j u) :
    |(1 + θ) * (1 + θ') - 1| ≤ roundingFactor (k + j) u := by
  calc |(1 + θ) * (1 + θ') - 1| = |θ + θ' + θ * θ'| := by ring_nf
    _ ≤ |θ| + |θ'| + |θ| * |θ'| := by
      rw [← abs_mul]; exact (abs_add_le _ _).trans (by gcongr; exact abs_add_le _ _)
    _ ≤ roundingFactor k u + roundingFactor j u + roundingFactor k u * roundingFactor j u := by
      gcongr; exact (abs_nonneg _).trans hθ
    _ ≤ roundingFactor (k + j) u := roundingFactor_add_add_mul_le hu hkj

/-- **Inverting an accumulated error**: if $\lvert \theta \rvert \le \gamma_j$, $0 \le u$ and
$2ju < 1$, then $\lvert (1 + \theta)^{-1} - 1 \rvert \le \gamma_{2j}$. [Higham2002, Lemma 3.3]
states the sharper $\gamma_{k+j}$ for a ratio $(1 + \theta_k)/(1 + \theta_j)$ of products of
rounding errors with $j \le k$; this form needs only the bound on $\theta$. -/
theorem abs_inv_one_add_sub_one_le (hu : 0 ≤ u) (hj : (2 * j : ℕ) * u < 1) {θ : ℝ}
    (hθ : |θ| ≤ roundingFactor j u) : |(1 + θ)⁻¹ - 1| ≤ roundingFactor (2 * j) u := by
  push_cast at hj
  have hju0 : 0 ≤ (j : ℝ) * u := by positivity
  have hju : (j : ℝ) * u < 1 := by linarith
  have h1 : 0 < 1 - j * u := by linarith
  have h2 : 0 < 1 - 2 * j * u := by linarith
  -- `1 - γ_j = (1 - 2ju)/(1 - ju) > 0`
  have hγ : 1 - roundingFactor j u = (1 - 2 * j * u) / (1 - j * u) := by
    rw [roundingFactor]; field_simp; ring
  have hγ1 : 0 < 1 - roundingFactor j u := by rw [hγ]; positivity
  have hθ1 : 1 - roundingFactor j u ≤ 1 + θ := by linarith [neg_abs_le θ]
  have hpos : 0 < 1 + θ := hγ1.trans_le hθ1
  calc |(1 + θ)⁻¹ - 1| = |θ| / (1 + θ) := by
        rw [show (1 + θ)⁻¹ - 1 = -θ / (1 + θ) by field_simp; ring, abs_div, abs_neg,
          abs_of_pos hpos]
    _ ≤ roundingFactor j u / (1 - roundingFactor j u) :=
        div_le_div₀ (roundingFactor_nonneg hu hju) hθ hγ1 hθ1
    _ = j * u / (1 - 2 * j * u) := by
        rw [hγ, roundingFactor]; field_simp
    _ ≤ roundingFactor (2 * j) u := by
        rw [roundingFactor]; push_cast
        gcongr
        linarith

/-- **Scaling the index** [Higham2002, Lemma 3.3]: for $0 \le u$ and $iku < 1$,
$i\gamma_k \le \gamma_{ik}$. -/
theorem mul_roundingFactor_le (i : ℕ) (hu : 0 ≤ u) (hik : (i * k : ℕ) * u < 1) :
    i * roundingFactor k u ≤ roundingFactor (i * k) u := by
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp [roundingFactor]
  have hi1 : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hku0 : 0 ≤ (k : ℝ) * u := by positivity
  push_cast at hik
  have hle : (k : ℝ) * u ≤ i * k * u := by nlinarith
  rw [roundingFactor, roundingFactor, mul_div_assoc']
  push_cast
  rw [← mul_assoc]
  gcongr

/-- **One more rounding** [Higham2002, Lemma 3.3]: for $0 \le u$ and $(k + 1)u < 1$,
$\gamma_k + u \le \gamma_{k+1}$. -/
theorem roundingFactor_add_le (hu : 0 ≤ u) (hk : (k + 1 : ℕ) * u < 1) :
    roundingFactor k u + u ≤ roundingFactor (k + 1) u := by
  have hk' : (k : ℝ) * u < 1 := lt_of_le_of_lt (by gcongr; omega) hk
  have hu1 : u < 1 := lt_of_le_of_lt (le_mul_of_one_le_left hu (by simp)) hk
  have h1 := le_roundingFactor_one hu hu1
  have := mul_nonneg (roundingFactor_nonneg hu hk') (roundingFactor_nonneg (n := 1) hu (by simpa))
  linarith [roundingFactor_add_add_mul_le (k := k) (j := 1) hu hk]

end NLAlib.Computation
