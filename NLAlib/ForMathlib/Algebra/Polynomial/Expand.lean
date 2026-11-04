/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Evaluation and degree of `Polynomial.contract`

The even part of a polynomial through Mathlib's `Polynomial.contract`:
$2\,(\operatorname{contract}_2 p)(x^2) = p(x) + p(-x)$, and the degree and the value at $0$ of a
contraction. These turn a polynomial bound on a symmetric set $[-b, -a] \cup [a, b]$ into one on
$[a^2, b^2]$. Upstream candidates for `Mathlib/Algebra/Polynomial/Expand.lean`.


## Main results

* `Polynomial.two_mul_eval_contract_two_sq`: the even part.
* `Polynomial.degree_contract_le_of_degree_le`, `Polynomial.eval_zero_contract`: degree and value
  at zero.
-/

@[expose] public section

namespace Polynomial

/-- A sum over $i < 2m$ in consecutive pairs. -/
private theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), f i = ∑ i ∈ Finset.range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- The even part of a polynomial: $2\,(\operatorname{contract}_2 p)(x^2) = p(x) + p(-x)$.
Upstream candidate. -/
theorem two_mul_eval_contract_two_sq {R : Type*} [CommRing R] (p : R[X]) (x : R) :
    2 * (contract 2 p).eval (x ^ 2) = p.eval x + p.eval (-x) := by
  have hp1 : p.natDegree < 2 * (p.natDegree + 1) := by omega
  have hc : (contract 2 p).natDegree < p.natDegree + 1 := by
    refine Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_)
    rw [coeff_contract two_ne_zero]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [eval_eq_sum_range' hc, eval_eq_sum_range' hp1, eval_eq_sum_range' hp1,
    ← Finset.sum_add_distrib, sum_range_two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_contract two_ne_zero, Nat.mul_comm i 2, pow_succ x (2 * i), pow_succ (-x) (2 * i),
    pow_mul x 2 i, pow_mul (-x) 2 i, neg_sq]
  ring

/-- A contraction divides the degree: if $\deg f \le q$ then
$\deg \operatorname{contract}_n f \le \lfloor q/n \rfloor$, for $n \ne 0$. Upstream candidate. -/
theorem degree_contract_le_of_degree_le {R : Type*} [CommSemiring R] {n : ℕ} (hn : n ≠ 0)
    {f : R[X]} {q : ℕ} (hf : f.degree ≤ q) : (contract n f).degree ≤ (q / n : ℕ) := by
  refine (degree_le_iff_coeff_zero _ _).mpr fun m hm => ?_
  rw [coeff_contract hn]
  have hkm : q / n < m := by exact_mod_cast hm
  exact coeff_eq_zero_of_degree_lt (hf.trans_lt (by
    exact_mod_cast (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hn)).1 hkm))

/-- A contraction keeps the value at zero: $(\operatorname{contract}_n f)(0) = f(0)$, for
$n \ne 0$. Upstream candidate. -/
theorem eval_zero_contract {R : Type*} [CommSemiring R] {n : ℕ} (hn : n ≠ 0) (f : R[X]) :
    (contract n f).eval 0 = f.eval 0 := by
  rw [← coeff_zero_eq_eval_zero, coeff_contract hn, zero_mul, coeff_zero_eq_eval_zero]

end Polynomial
