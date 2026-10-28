/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Positivity

/-!
# Accumulated rounding errors

The constant $\gamma_n = nu/(1 - nu)$ of the standard model of floating-point arithmetic,
`NLAlib.Computation.roundingFactor n u`, and its algebra: a product of $n$ factors
$(1 + \delta_i)^{\pm 1}$ with $\lvert \delta_i \rvert \le u$ is $1 + \theta_n$ with
$\lvert \theta_n \rvert \le \gamma_n$, and the rules that combine such $\theta$'s. The relation
`NLAlib.Computation.relErr u a z` says that $z$ is $a$ with relative error at most $u$, the error
clause of the model (2.4) of [Higham2002]. Every lemma assumes $nu < 1$, under which
$\gamma_n$ is finite. Design: `docs/design/Computation-Rounding.md` (R1, R2).

## Main definitions

* `NLAlib.Computation.roundingFactor`: $\gamma_n$.
* `NLAlib.Computation.relErr`: relative error at most $u$.

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

/-- `relErr u a z`: $z = a(1 + \delta)$ for some $\lvert \delta \rvert \le u$; the error clause of
the standard model [Higham2002, §2.2], (2.4) there. -/
def relErr (u a z : ℝ) : Prop := ∃ δ : ℝ, |δ| ≤ u ∧ z = a * (1 + δ)

variable {u : ℝ} {n k j : ℕ}

/-- **$\gamma_0 = 0$.** [Higham2002, §3.1]. -/
theorem roundingFactor_zero : roundingFactor 0 u = 0 := by
  sorry

/-- **$\gamma_n \ge 0$** for $0 \le u$ and $nu < 1$. [Higham2002, §3.1]. -/
theorem roundingFactor_nonneg (hu : 0 ≤ u) (hn : n * u < 1) : 0 ≤ roundingFactor n u := by
  sorry

/-- **$\gamma_1 \ge u$**, so a single rounding error is within $\gamma_1$: for $0 \le u < 1$,
$u \le \gamma_1$. [Higham2002, §3.1]. -/
theorem le_roundingFactor_one (hu : 0 ≤ u) (hu1 : u < 1) : u ≤ roundingFactor 1 u := by
  sorry

/-- **$\gamma_n$ is monotone in $n$**: for $0 \le u$, $k \le n$ and $nu < 1$,
$\gamma_k \le \gamma_n$. [Higham2002, §3.1]. -/
theorem roundingFactor_le_roundingFactor (hu : 0 ≤ u) (hkn : k ≤ n) (hn : n * u < 1) :
    roundingFactor k u ≤ roundingFactor n u := by
  sorry

/-- **Products of rounding errors** [Higham2002, Lemma 3.1]: for $\lvert \delta_i \rvert \le u$,
exponents $\rho_i = \pm 1$ ($i$ in a finite set $s$ of $n$ elements) and $nu < 1$,
$$\Bigl\lvert \prod_{i \in s} (1 + \delta_i)^{\rho_i} - 1 \Bigr\rvert \le \gamma_n\,.$$ -/
theorem abs_prod_one_add_zpow_sub_one_le {ι : Type} (s : Finset ι) (δ : ι → ℝ) (ρ : ι → ℤ)
    (hδ : ∀ i ∈ s, |δ i| ≤ u) (hρ : ∀ i ∈ s, ρ i = 1 ∨ ρ i = -1) (hn : s.card * u < 1) :
    |∏ i ∈ s, (1 + δ i) ^ ρ i - 1| ≤ roundingFactor s.card u := by
  sorry

/-- **Adding accumulated errors** [Higham2002, Lemma 3.3]: for $0 \le u$ and $(k + j)u < 1$,
$\gamma_k + \gamma_j + \gamma_k\gamma_j \le \gamma_{k+j}$. -/
theorem roundingFactor_add_add_mul_le (hu : 0 ≤ u) (hkj : (k + j : ℕ) * u < 1) :
    roundingFactor k u + roundingFactor j u + roundingFactor k u * roundingFactor j u ≤
      roundingFactor (k + j) u := by
  sorry

/-- **Composing accumulated errors** [Higham2002, Lemma 3.3]: if
$\lvert \theta \rvert \le \gamma_k$ and $\lvert \theta' \rvert \le \gamma_j$, $0 \le u$ and
$(k + j)u < 1$, then $\lvert (1 + \theta)(1 + \theta') - 1 \rvert \le \gamma_{k+j}$. -/
theorem abs_one_add_mul_one_add_sub_one_le (hu : 0 ≤ u) (hkj : (k + j : ℕ) * u < 1)
    {θ θ' : ℝ} (hθ : |θ| ≤ roundingFactor k u) (hθ' : |θ'| ≤ roundingFactor j u) :
    |(1 + θ) * (1 + θ') - 1| ≤ roundingFactor (k + j) u := by
  sorry

/-- **Inverting an accumulated error**: if $\lvert \theta \rvert \le \gamma_j$, $0 \le u$ and
$2ju < 1$, then $\lvert (1 + \theta)^{-1} - 1 \rvert \le \gamma_{2j}$. [Higham2002, Lemma 3.3]
states the sharper $\gamma_{k+j}$ for a ratio $(1 + \theta_k)/(1 + \theta_j)$ of products of
rounding errors with $j \le k$; this form needs only the bound on $\theta$. -/
theorem abs_inv_one_add_sub_one_le (hu : 0 ≤ u) (hj : (2 * j : ℕ) * u < 1) {θ : ℝ}
    (hθ : |θ| ≤ roundingFactor j u) : |(1 + θ)⁻¹ - 1| ≤ roundingFactor (2 * j) u := by
  sorry

/-- **Scaling the index** [Higham2002, Lemma 3.3]: for $0 \le u$ and $iku < 1$,
$i\gamma_k \le \gamma_{ik}$. -/
theorem mul_roundingFactor_le (i : ℕ) (hu : 0 ≤ u) (hik : (i * k : ℕ) * u < 1) :
    i * roundingFactor k u ≤ roundingFactor (i * k) u := by
  sorry

/-- **One more rounding** [Higham2002, Lemma 3.3]: for $0 \le u$ and $(k + 1)u < 1$,
$\gamma_k + u \le \gamma_{k+1}$. -/
theorem roundingFactor_add_le (hu : 0 ≤ u) (hk : (k + 1 : ℕ) * u < 1) :
    roundingFactor k u + u ≤ roundingFactor (k + 1) u := by
  sorry

end NLAlib.Computation
