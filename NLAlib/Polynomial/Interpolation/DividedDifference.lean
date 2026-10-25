/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.ForMathlib.LinearAlgebra.Lagrange

/-!
# Divided differences

The divided difference of values $r_i$ at distinct nodes $v_i$, $i \in s$, is
$$r[s] = \sum_{i \in s} w_i\,r_i \,, \qquad w_i = \prod_{j \in s,\ j \ne i}(v_i - v_j)^{-1} \,,$$
with Mathlib's nodal (barycentric) weights $w_i$ = `Lagrange.nodalWeight s v i`. On $q + 1$
nodes it is the coefficient of $X^q$ of the interpolant (`dividedDifference_eq_coeff_interpolate`,
from Mathlib's `Lagrange.coeff_eq_sum`), so it is the leading coefficient of every polynomial
of degree at most $q$ and annihilates every polynomial of degree less than $q$. Conversely a
vector of values orthogonal, in the plain sum, to every polynomial of degree less than $q$ on
the nodes is a multiple of the nodal weights (`Lagrange.exists_eq_mul_nodalWeight`). With positive
weights $u_i$ the weighted least-squares distance from $r$ to the polynomials of degree less
than $q$ is $r[s]^2 / \sum_i w_i^2/u_i$ (`isLeast_sum_mul_sq_sub_eval`).

These are the facts behind the lower bounds for Krylov methods on matrices with $q + 1$
distinct eigenvalues (`NLAlib.Krylov.Functions.Optimality`): the residual polynomial of a
Galerkin method is orthogonal to the polynomials of degree less than $q$ in the spectral
weights of the starting vector, so its values on the eigenvalues are prescribed by the nodal
weights.

Junk value: for nodes that are not distinct the nodal weights contain $0^{-1} = 0$ and the
definition is still the sum; every theorem assumes `Set.InjOn v s`.

## Main definitions

* `NLAlib.dividedDifference`: $r[s] = \sum_i w_i r_i$.

## Main results

* `NLAlib.dividedDifference_eq_coeff_interpolate`: the coefficient of $X^q$ of the interpolant.
* `NLAlib.dividedDifference_eval_eq_coeff`, `NLAlib.dividedDifference_eval_eq_zero`: on the
  values of a polynomial.
* `NLAlib.isLeast_sum_mul_sq_sub_eval`: the weighted least-squares distance.
-/

@[expose] public section

open Polynomial Finset

namespace NLAlib

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- The **divided difference** of the values $r_i$ at the nodes $v_i$, $i \in s$:
$r[s] := \sum_{i \in s} w_i\,r_i$ with the nodal weights
$w_i = \prod_{j \ne i}(v_i - v_j)^{-1}$ (`Lagrange.nodalWeight`). For distinct nodes and
$\lvert s \rvert = q + 1$ it is the coefficient of $X^q$ of the interpolant
(`dividedDifference_eq_coeff_interpolate`). Junk value: for repeated nodes the weights
contain $0^{-1} = 0$. [Higham2008, (1.10)]; locator to verify. -/
noncomputable def dividedDifference (s : Finset ι) (v : ι → F) (r : ι → F) : F :=
  ∑ i ∈ s, Lagrange.nodalWeight s v i * r i

/-- The divided difference is a coefficient of the interpolant: on $q + 1$ distinct nodes,
$r[s]$ is the coefficient of $X^q$ of `Lagrange.interpolate s v r`; this is Mathlib's
`Lagrange.coeff_eq_sum`, whose count is `#s - 1`, for the interpolant. -/
theorem dividedDifference_eq_coeff_interpolate {s : Finset ι} {v : ι → F}
    (hvs : Set.InjOn v s) {q : ℕ} (hs : #s = q + 1) (r : ι → F) :
    dividedDifference s v r = (Lagrange.interpolate s v r).coeff q := by
  have hq : q = #s - 1 := by omega
  rw [hq, Lagrange.coeff_eq_sum hvs (Lagrange.degree_interpolate_lt r hvs), dividedDifference]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Lagrange.eval_interpolate_at_node r hvs hi, Lagrange.nodalWeight, Finset.prod_inv_distrib,
    div_eq_inv_mul]

/-- **The divided difference of a polynomial of degree at most $q$** on $q + 1$ distinct nodes
is its coefficient of $X^q$. [Higham2008, (1.10)]; locator to verify. -/
theorem dividedDifference_eval_eq_coeff {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
    {q : ℕ} (hs : #s = q + 1) {p : F[X]} (hp : p.degree ≤ q) :
    dividedDifference s v (fun i => p.eval (v i)) = p.coeff q := by
  have hp' : p.degree < #s := hp.trans_lt (by rw [hs]; exact_mod_cast Nat.lt_succ_self q)
  conv_rhs => rw [Lagrange.eq_interpolate hvs hp']
  exact dividedDifference_eq_coeff_interpolate hvs hs _

/-- The divided difference annihilates lower degrees: on $q + 1$ distinct nodes, a
polynomial of degree less than $q$ has divided difference $0$. -/
theorem dividedDifference_eval_eq_zero {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s)
    {q : ℕ} (hs : #s = q + 1) {p : F[X]} (hp : p.degree < q) :
    dividedDifference s v (fun i => p.eval (v i)) = 0 := by
  rw [dividedDifference_eval_eq_coeff hvs hs hp.le, coeff_eq_zero_of_degree_lt hp]

/-- A polynomial of degree at most $q$ whose coefficient of $X^q$ vanishes has degree less than
$q$. -/
private theorem degree_lt_of_degree_le_of_coeff_eq_zero {p : F[X]} {q : ℕ} (hp : p.degree ≤ q)
    (hq : p.coeff q = 0) : p.degree < q := by
  refine (degree_lt_iff_coeff_zero p q).mpr fun m hm => ?_
  rcases hm.eq_or_lt with rfl | hm
  · exact hq
  · exact coeff_eq_zero_of_degree_lt (hp.trans_lt (by exact_mod_cast hm))

/-- **Weighted least squares on $q + 1$ nodes**: for distinct real nodes $v_i$, $i \in s$,
$\lvert s \rvert = q + 1$, weights $u_i > 0$ and values $r_i$,
$$\min_{\deg p < q}\ \sum_{i \in s} u_i\,\bigl(r_i - p(v_i)\bigr)^2 =
\frac{r[s]^2}{\sum_{i \in s} w_i^2/u_i} \,,$$
$w_i$ the nodal weights; the minimum is attained at the interpolant of
$r - t\,w/u$, $t = r[s]/\sum_{i \in s} w_i^2/u_i$. [ChenPersson2026, Lemma 9]. -/
theorem isLeast_sum_mul_sq_sub_eval {s : Finset ι} {v : ι → ℝ} (hvs : Set.InjOn v s) {q : ℕ}
    (hs : #s = q + 1) {u : ι → ℝ} (hu : ∀ i ∈ s, 0 < u i) (r : ι → ℝ) :
    IsLeast ((fun p : ℝ[X] => ∑ i ∈ s, u i * (r i - p.eval (v i)) ^ 2) '' {p | p.degree < q})
      (dividedDifference s v r ^ 2 / ∑ i ∈ s, Lagrange.nodalWeight s v i ^ 2 / u i) := by
  set W := Lagrange.nodalWeight s v
  set D := ∑ i ∈ s, W i ^ 2 / u i
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  have hD : 0 < D := by
    obtain ⟨i₀, hi₀⟩ := hne
    refine Finset.sum_pos' (fun i hi => div_nonneg (sq_nonneg _) (hu i hi).le)
      ⟨i₀, hi₀, div_pos (sq_pos_of_ne_zero (Lagrange.nodalWeight_ne_zero hvs hi₀)) (hu i₀ hi₀)⟩
  refine ⟨?_, ?_⟩
  · -- attained by the interpolant of `r - t W / u`
    set t := dividedDifference s v r / D
    set r' : ι → ℝ := fun i => r i - t * W i / u i
    refine ⟨Lagrange.interpolate s v r', ?_, ?_⟩
    · refine degree_lt_of_degree_le_of_coeff_eq_zero ?_ ?_
      · have := Lagrange.degree_interpolate_lt r' hvs
        rw [hs] at this
        exact Order.le_of_lt_succ (by exact_mod_cast this)
      · rw [← dividedDifference_eq_coeff_interpolate hvs hs, dividedDifference]
        simp only [r', mul_sub, Finset.sum_sub_distrib]
        rw [← dividedDifference, sub_eq_zero]
        have : ∑ i ∈ s, W i * (t * W i / u i) = t * D := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, div_mul_cancel₀ _ hD.ne']
    · simp only
      rw [Finset.sum_congr rfl fun i hi => by
        rw [Lagrange.eval_interpolate_at_node r' hvs hi]]
      have : ∀ i ∈ s, u i * (r i - r' i) ^ 2 = t ^ 2 * (W i ^ 2 / u i) := fun i hi => by
        have := (hu i hi).ne'
        simp only [r']
        field_simp
        ring
      rw [Finset.sum_congr rfl this, ← Finset.mul_sum, div_pow]
      field_simp
      rfl
  · -- Cauchy–Schwarz
    rintro _ ⟨p, hp, rfl⟩
    have hp : p.degree < q := hp
    have hrp : dividedDifference s v r = ∑ i ∈ s, W i * (r i - p.eval (v i)) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      rw [← dividedDifference, ← dividedDifference, dividedDifference_eval_eq_zero hvs hs hp,
        sub_zero]
    rw [div_le_iff₀ hD, hrp, mul_comm]
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s
      (fun i hi => div_nonneg (sq_nonneg _) (hu i hi).le)
      (fun i hi => mul_nonneg (hu i hi).le (sq_nonneg _)) fun i hi => le_of_eq ?_
    have := (hu i hi).ne'
    field_simp

end NLAlib
