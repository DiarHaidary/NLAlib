/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Degree-controlled residual factorization

Factoring a polynomial equal to one at zero gives a lower-degree correction polynomial.
This is an upstream candidate for Mathlib's polynomial division API.

## Main results

* `Polynomial.exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one`:
  factor a normalized residual without losing its degree bound.
-/

@[expose] public section

namespace Polynomial

/-- If $\deg p\le q$ and $p(0)=1$, then $1-p=Xs$ for a polynomial of degree less than $q$.
The `WithBot` degree includes the case $q=0$, when the correction is zero. This combines
Mathlib's `X_dvd_iff` and `degree_mul_X` for residual-polynomial consumers. -/
theorem exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one
    {R : Type*} [Ring R] [Nontrivial R] {p : R[X]} {q : ℕ}
    (hp : p.degree ≤ (q : WithBot ℕ)) (hp0 : p.eval 0 = 1) :
    ∃ s : R[X], s.degree < (q : WithBot ℕ) ∧ 1 - p = X * s := by
  have hdvd : X ∣ 1 - p := by
    rw [X_dvd_iff, coeff_zero_eq_eval_zero, eval_sub, hp0, eval_one, sub_self]
  obtain ⟨s, hs⟩ := hdvd
  refine ⟨s, ?_, hs⟩
  rcases eq_or_ne s 0 with h0 | h0
  · rw [h0, degree_zero]
    exact WithBot.bot_lt_coe _
  · have hdeg : (1 - p).degree ≤ (q : WithBot ℕ) :=
      (degree_sub_le _ _).trans
        (max_le (degree_one_le.trans (by exact_mod_cast Nat.zero_le q)) hp)
    rw [hs, X_mul, degree_mul_X] at hdeg
    rw [degree_eq_natDegree h0] at hdeg ⊢
    have hn : s.natDegree + 1 ≤ q := by exact_mod_cast hdeg
    exact_mod_cast (Nat.lt_of_succ_le hn : s.natDegree < q)

end Polynomial
