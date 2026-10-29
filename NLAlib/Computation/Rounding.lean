/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Pow
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Accumulated rounding errors

The constant <!-- value Computation.roundingFactor n u --> $\gamma_n = nu/(1 - nu)$ of the
standard model of floating-point arithmetic, `NLAlib.Computation.roundingFactor n u`, and its
algebra: a product of $n$ factors $(1 + \delta_i)^{\pm 1}$ with $\lvert \delta_i \rvert \le u$
is $1 + \theta_n$ with $\lvert \theta_n \rvert \le \gamma_n$, and the rules that combine such
$\theta$'s [Higham2002]. The relation `NLAlib.Computation.RelErr u a z` says that $z$ is $a$ with
relative error at most $u$, the error clause of the standard model. Every lemma assumes
$nu < 1$, under which $\gamma_n$ is finite. Design: `docs/design/Computation-Rounding.md` (R1, R2).

## Main definitions

* `NLAlib.Computation.roundingFactor`: $\gamma_n$.
* `NLAlib.Computation.RelErr`: relative error at most $u$.
* `NLAlib.Computation.IsRoundingProduct`: $1 + \theta$ is a product of $j$ factors
  $(1 + \delta_i)^{\pm 1}$, $\lvert \delta_i \rvert \le u$ (Higham's $\theta_j$).

## Main results

* `NLAlib.Computation.abs_prod_one_add_zpow_sub_one_le`: the product of $n$ factors
  $(1 + \delta_i)^{\pm 1}$ is $1 + \theta_n$, $\lvert \theta_n \rvert \le \gamma_n$.
* `NLAlib.Computation.roundingFactor_add_add_mul_le`:
  $\gamma_k + \gamma_j + \gamma_k\gamma_j \le \gamma_{k+j}$.
* `NLAlib.Computation.abs_one_add_mul_one_add_sub_one_le`: $(1 + \theta_k)(1 + \theta_j) =
  1 + \theta_{k+j}$.
* `NLAlib.Computation.IsRoundingProduct.abs_le`, `NLAlib.Computation.IsRoundingProduct.mul`,
  `NLAlib.Computation.IsRoundingProduct.inv`, `NLAlib.Computation.IsRoundingProduct.div`:
  [Higham2002, Lemma 3.3] for products of rounding errors, with the ratio rule
  $(1 + \theta_k)/(1 + \theta_j) = 1 + \theta_{k+j}$ for all $j$, $k$.
* `NLAlib.Computation.isRoundingProduct_iff`: the values $1 + \theta_j$ fill the interval
  $[(1 - u)^j, (1 - u)^{-j}]$.
* `NLAlib.Computation.exists_isRoundingProduct_sum_mul_one_add_eq`: a weighted mean of
  $1 + \theta_j$'s is a $1 + \theta_j$.
-/

@[expose] public section

namespace NLAlib.Computation

/-- **The accumulated rounding factor** <!-- value Computation.roundingFactor n u -->
$\gamma_n = nu/(1 - nu)$ of [Higham2002, §3.1], the bound on $n$ accumulated relative errors of
size at most $u$. It is meaningful for $nu < 1$, which
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
rounding errors with $j \le k$; this form needs only the bound on $\theta$. For products of
rounding errors, `NLAlib.Computation.IsRoundingProduct.inv` keeps the index $j$ and
`NLAlib.Computation.IsRoundingProduct.div` gives the ratio rule with $\gamma_{k+j}$. -/
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

/-! ### Products of rounding errors -/

/-- `IsRoundingProduct u j θ`: $1 + \theta = \prod_{i<j} (1 + \delta_i)^{\rho_i}$ for some
$\lvert \delta_i \rvert \le u$ and $\rho_i = \pm 1$, the quantity $\theta_j$ of
[Higham2002, Lemma 3.1]. Unlike the bound $\lvert \theta \rvert \le \gamma_j$
(`NLAlib.Computation.IsRoundingProduct.abs_le`), the predicate is closed under inversion with
the same $j$. -/
def IsRoundingProduct (u : ℝ) (j : ℕ) (θ : ℝ) : Prop :=
  ∃ (δ : Fin j → ℝ) (ρ : Fin j → ℤ), (∀ i, |δ i| ≤ u) ∧ (∀ i, ρ i = 1 ∨ ρ i = -1) ∧
    ∏ i, (1 + δ i) ^ ρ i = 1 + θ

variable {θ θ' : ℝ}

/-- **The empty product**: $\theta_0 = 0$. [Higham2002, Lemma 3.1]. -/
theorem isRoundingProduct_zero : IsRoundingProduct u 0 0 :=
  ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, by simp⟩

/-- **One rounding error** is a product of one factor: $\lvert \delta \rvert \le u$ gives
$\theta_1 = \delta$. [Higham2002, Lemma 3.1]. -/
theorem isRoundingProduct_one_of_abs_le (hθ : |θ| ≤ u) : IsRoundingProduct u 1 θ :=
  ⟨fun _ => θ, fun _ => 1, fun _ => hθ, fun _ => Or.inl rfl, by simp⟩

/-- **Products of rounding errors are bounded by $\gamma_j$** [Higham2002, Lemma 3.1]: if
$1 + \theta$ is a product of $j$ factors $(1 + \delta_i)^{\pm 1}$, $\lvert \delta_i \rvert \le u$,
and $ju < 1$, then $\lvert \theta \rvert \le \gamma_j$. -/
theorem IsRoundingProduct.abs_le (h : IsRoundingProduct u j θ) (hj : j * u < 1) :
    |θ| ≤ roundingFactor j u := by
  obtain ⟨δ, ρ, hδ, hρ, he⟩ := h
  have := abs_prod_one_add_zpow_sub_one_le Finset.univ δ ρ (fun i _ => hδ i) (fun i _ => hρ i)
    (by simpa using hj)
  simpa [he] using this

/-- **Multiplying products of rounding errors** [Higham2002, Lemma 3.3]:
$(1 + \theta_k)(1 + \theta_j) = 1 + \theta_{k+j}$. -/
theorem IsRoundingProduct.mul (h : IsRoundingProduct u k θ) (h' : IsRoundingProduct u j θ') :
    IsRoundingProduct u (k + j) ((1 + θ) * (1 + θ') - 1) := by
  obtain ⟨δ, ρ, hδ, hρ, he⟩ := h
  obtain ⟨δ', ρ', hδ', hρ', he'⟩ := h'
  refine ⟨Fin.append δ δ', Fin.append ρ ρ', fun i => ?_, fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hδ, hδ']
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [hρ, hρ']
  · rw [Fin.prod_univ_add]
    simp [he, he']

/-- **Inverting a product of rounding errors** keeps its length:
$(1 + \theta_j)^{-1} = 1 + \theta_j$ [Higham2002, Lemma 3.3]. Compare
`NLAlib.Computation.abs_inv_one_add_sub_one_le`, which from the bound on $\theta$ alone gives
$\gamma_{2j}$. -/
theorem IsRoundingProduct.inv (h : IsRoundingProduct u j θ) :
    IsRoundingProduct u j ((1 + θ)⁻¹ - 1) := by
  obtain ⟨δ, ρ, hδ, hρ, he⟩ := h
  refine ⟨δ, -ρ, hδ, fun i => by rcases hρ i with h | h <;> simp [h], ?_⟩
  simp [zpow_neg, Finset.prod_inv_distrib, he]

/-- **The ratio of products of rounding errors** [Higham2002, Lemma 3.3]:
$(1 + \theta_k)/(1 + \theta_j) = 1 + \theta_{k+j}$, for all $j$ and $k$. -/
theorem IsRoundingProduct.div (h : IsRoundingProduct u k θ) (h' : IsRoundingProduct u j θ') :
    IsRoundingProduct u (k + j) ((1 + θ) / (1 + θ') - 1) := by
  simpa [div_eq_mul_inv] using h.mul h'.inv

/-- **A shorter product is a longer one**: for $0 \le u$ and $j \le k$, $1 + \theta_j$ is a
$1 + \theta_k$ (pad with factors $1 + 0$). [Higham2002, Lemma 3.1]. -/
theorem IsRoundingProduct.mono (h : IsRoundingProduct u j θ) (hu : 0 ≤ u) (hjk : j ≤ k) :
    IsRoundingProduct u k θ := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hjk
  have h0 : IsRoundingProduct u m 0 :=
    ⟨fun _ => 0, fun _ => 1, fun _ => by simpa using hu, fun _ => Or.inl rfl, by simp⟩
  simpa using h.mul h0

/-- A factor $(1 + \delta)^{\pm 1}$ with $\lvert \delta \rvert \le u < 1$ lies in
$[1 - u, (1 - u)^{-1}]$. -/
private theorem one_add_zpow_mem_Icc {δ : ℝ} {ρ : ℤ} (hδ : |δ| ≤ u) (hu1 : u < 1)
    (hρ : ρ = 1 ∨ ρ = -1) : 1 - u ≤ (1 + δ) ^ ρ ∧ (1 + δ) ^ ρ ≤ (1 - u)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  have hu : 0 ≤ u := (abs_nonneg _).trans hδ
  have hinv : 1 + u ≤ (1 - u)⁻¹ := by
    rw [← one_div, le_div_iff₀ h1u]; nlinarith
  obtain ⟨hlo, hhi⟩ := abs_le.mp hδ
  have hpos : 0 < 1 + δ := by linarith
  rcases hρ with h | h <;> simp only [h, zpow_one, zpow_neg]
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨(le_inv_comm₀ h1u hpos).mpr (by linarith), inv_anti₀ h1u (by linarith)⟩

/-- **The values of a product of rounding errors** [Higham2002, Lemma 3.1]: for
$0 \le u < 1$, $1 + \theta$ is a product of $j$ factors $(1 + \delta_i)^{\pm 1}$ with
$\lvert \delta_i \rvert \le u$ exactly when $(1 - u)^j \le 1 + \theta \le (1 - u)^{-j}$. -/
theorem isRoundingProduct_iff (hu : 0 ≤ u) (hu1 : u < 1) :
    IsRoundingProduct u j θ ↔ (1 - u) ^ j ≤ 1 + θ ∧ 1 + θ ≤ ((1 - u) ^ j)⁻¹ := by
  have h1u : 0 < 1 - u := by linarith
  constructor
  · rintro ⟨δ, ρ, hδ, hρ, he⟩
    rw [← he]
    have hfac := fun i => one_add_zpow_mem_Icc (hδ i) hu1 (hρ i)
    constructor
    · simpa using Finset.prod_le_prod (s := Finset.univ) (fun _ _ => h1u.le)
        (fun i _ => (hfac i).1)
    · rw [← inv_pow]
      simpa using Finset.prod_le_prod (s := Finset.univ) (fun i _ => h1u.le.trans (hfac i).1)
        (fun i _ => (hfac i).2)
  rintro ⟨hlo, hhi⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · have : θ = 0 := by simp at hlo hhi; linarith
    exact this ▸ isRoundingProduct_zero
  have hpj : 0 < (1 - u) ^ j := pow_pos h1u j
  have hj0 : j ≠ 0 := hj.ne'
  -- a `y ∈ [(1 - u)^j, 1]` is `r^j` with `r = y^{1/j} ∈ [1 - u, 1]`
  have root : ∀ y, (1 - u) ^ j ≤ y → y ≤ 1 → ∃ r, |r - 1| ≤ u ∧ r ^ j = y := by
    intro y hy1 hy2
    have hy0 : 0 ≤ y := hpj.le.trans hy1
    refine ⟨y ^ (j⁻¹ : ℝ), abs_le.mpr ⟨?_, ?_⟩, Real.rpow_inv_natCast_pow hy0 hj0⟩
    · have := Real.rpow_le_rpow hpj.le hy1 (by positivity : (0 : ℝ) ≤ (j : ℝ)⁻¹)
      rw [Real.pow_rpow_inv_natCast h1u.le hj0] at this
      linarith
    · have := Real.rpow_le_rpow hy0 hy2 (by positivity : (0 : ℝ) ≤ (j : ℝ)⁻¹)
      rw [Real.one_rpow] at this
      linarith
  rcases le_or_gt (1 + θ) 1 with hle | hgt
  · obtain ⟨r, hr, hrj⟩ := root (1 + θ) hlo hle
    exact ⟨fun _ => r - 1, fun _ => 1, fun _ => hr, fun _ => Or.inl rfl, by simp [hrj]⟩
  · have hpos : 0 < 1 + θ := by linarith
    obtain ⟨r, hr, hrj⟩ := root (1 + θ)⁻¹ (by rw [le_inv_comm₀ hpj hpos]; exact hhi)
      (inv_le_one_of_one_le₀ hgt.le)
    exact ⟨fun _ => r - 1, fun _ => -1, fun _ => hr, fun _ => Or.inr rfl,
      by simp [hrj]⟩

/-- **A weighted mean of products of rounding errors** is one: for $0 \le u < 1$, weights
$w_i \ge 0$ and $1 + \theta_i$ products of $j$ factors $(1 + \delta)^{\pm 1}$,
$\sum_i w_i(1 + \theta_i) = \bigl(\sum_i w_i\bigr)(1 + \theta)$ with $1 + \theta$ again such a
product, as the values fill an interval (`NLAlib.Computation.isRoundingProduct_iff`). This is
how [Higham2002, §3.1] passes from (3.4) to a single $\theta_j$ for a sum of nonnegative
terms. -/
theorem exists_isRoundingProduct_sum_mul_one_add_eq {ι : Type} (hu : 0 ≤ u) (hu1 : u < 1)
    (s : Finset ι) (w θs : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hθ : ∀ i ∈ s, IsRoundingProduct u j (θs i)) :
    ∃ θ, IsRoundingProduct u j θ ∧ ∑ i ∈ s, w i * (1 + θs i) = (∑ i ∈ s, w i) * (1 + θ) := by
  have hpj : 0 < (1 - u) ^ j := pow_pos (by linarith) j
  have hb := fun i hi => (isRoundingProduct_iff hu hu1).mp (hθ i hi)
  have hW : 0 ≤ ∑ i ∈ s, w i := Finset.sum_nonneg hw
  rcases hW.eq_or_lt with hW0 | hWpos
  · refine ⟨0, isRoundingProduct_zero.mono hu (Nat.zero_le j), ?_⟩
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hw).mp hW0.symm
    rw [← hW0, zero_mul]
    exact Finset.sum_eq_zero fun i hi => by rw [hz i hi, zero_mul]
  refine ⟨(∑ i ∈ s, w i * (1 + θs i)) / ∑ i ∈ s, w i - 1,
    (isRoundingProduct_iff hu hu1).mpr ⟨?_, ?_⟩, ?_⟩
  · rw [add_sub_cancel, le_div_iff₀ hWpos, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (hb i hi).1 (hw i hi)
  · rw [add_sub_cancel, div_le_iff₀ hWpos, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    rw [mul_comm ((1 - u) ^ j)⁻¹]
    exact mul_le_mul_of_nonneg_left (hb i hi).2 (hw i hi)
  · rw [add_sub_cancel, mul_div_cancel₀ _ hWpos.ne']

end NLAlib.Computation
