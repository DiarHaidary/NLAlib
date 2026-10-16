/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.ChebyshevCoefficients
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.Topology.Algebra.Polynomial

/-!
# Finite Chebyshev truncation

The canonical degree-$N$ truncation includes terms zero through $N$, using full coefficients.
It reproduces every polynomial within its degree budget, over either real or complex scalars.
Analytic reconstruction and quantitative errors require additional hypotheses in later results.

## Main results

* `NLAlib.chebyshevTrunc`: inclusive degree-$N$ truncation.
* `NLAlib.degree_chebyshevTrunc_le`: unconditional degree bound.
* `NLAlib.chebyshevTrunc_eval_eq`: exact reproduction of polynomials.
-/

@[expose] public section

open MeasureTheory Polynomial Polynomial.Chebyshev

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The degree-$N$ Chebyshev truncation is
$$p_N=\sum_{k=0}^N a_kT_k,$$
with the full coefficients `chebyshevCoeff`, including the unhalved constant term.
[Trefethen2019, Eq. (4.3)], generalized to RCLike values. At $N=0$ it is the constant
coefficient. For arbitrary functions it is a total finite polynomial, without any unconditional
reconstruction claim; each coefficient retains its own Bochner-integral convention. -/
noncomputable def chebyshevTrunc (f : ℝ → 𝕜) (N : ℕ) : 𝕜[X] :=
  ∑ k ∈ Finset.range (N + 1),
    Polynomial.C (chebyshevCoeff f k) * Polynomial.Chebyshev.T 𝕜 (k : ℤ)

/-- Evaluate a finite Chebyshev truncation term by term. -/
theorem eval_chebyshevTrunc (f : ℝ → 𝕜) (N : ℕ) (x : 𝕜) :
    (chebyshevTrunc f N).eval x = ∑ k ∈ Finset.range (N + 1),
      chebyshevCoeff f k * (Polynomial.Chebyshev.T 𝕜 (k : ℤ)).eval x := by
  simp only [chebyshevTrunc, eval_finsetSum, eval_mul, eval_C]

/-- The inclusive degree-$N$ truncation has degree at most $N$, even if coefficients vanish. -/
theorem degree_chebyshevTrunc_le (f : ℝ → 𝕜) (N : ℕ) :
    (chebyshevTrunc f N).degree ≤ (N : WithBot ℕ) := by
  unfold chebyshevTrunc
  refine (degree_sum_le _ _).trans (Finset.sup_le fun k hk => ?_)
  rw [C_mul']
  refine (degree_smul_le _ _).trans ?_
  rw [degree_T, Int.natAbs_natCast]
  exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hk)

private lemma exists_finite_T_expansion {p : 𝕜[X]} {N : ℕ}
    (hp : p.degree ≤ (N : WithBot ℕ)) :
    ∃ c : ℕ → 𝕜, (∑ j ∈ Finset.range (N + 1), c j • T 𝕜 (j : ℤ)) = p := by
  let S := chebyshevTsequence 𝕜
  have hCoeff : ∀ i ≤ N, IsUnit (S i).leadingCoeff := by
    intro i hi
    exact isUnit_iff_ne_zero.mpr (leadingCoeff_ne_zero.mpr (S.ne_zero i))
  have hmem : p ∈ Polynomial.degreeLE 𝕜 N := Polynomial.mem_degreeLE.mpr hp
  rw [← S.span_degreeLE hCoeff] at hmem
  have hset : Set.Iic N = (Finset.range (N + 1) : Set ℕ) := by
    ext i
    simp only [Set.mem_Iic, Finset.mem_coe, Finset.mem_range, Nat.lt_succ_iff]
  rw [hset] at hmem
  exact (Submodule.mem_span_image_finset_iff_exists_fun' 𝕜).mp hmem

/-- Every polynomial of degree at most $N$ is recovered by its degree-$N$ Chebyshev truncation.
This finite-basis consequence of [Trefethen2019, p. 16 and Exercise 3.7] is generalized to
RCLike coefficients using Mathlib's polynomial-sequence span and Chebyshev orthogonality.
It includes zero polynomials and $N=0$; polynomial continuity supplies integrability.

Result: chebyshev-polynomial-reproduction
-/
theorem chebyshevTrunc_eval_eq {p : 𝕜[X]} {N : ℕ}
    (hp : p.degree ≤ (N : WithBot ℕ)) :
    chebyshevTrunc (fun x : ℝ => p.eval (x : 𝕜)) N = p := by
  obtain ⟨c, hc⟩ := exists_finite_T_expansion hp
  unfold chebyshevTrunc
  rw [← hc]
  apply Finset.sum_congr rfl
  intro k hk
  rw [chebyshevCoeff_sum_smul_T]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hk, if_true]
  exact C_mul' _ _

end NLAlib
