/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Tactic.Ring

/-!
# Nodal weights: ring homomorphisms and orthogonality to low degrees

Mathlib's nodal (barycentric) weights $w_i = \prod_{j \in s,\ j \ne i}(v_i - v_j)^{-1}$
(`Lagrange.nodalWeight s v i`) commute with ring homomorphisms between fields, and on $q + 1$
distinct nodes they span the vectors of values that are orthogonal, in the plain sum, to every
polynomial of degree less than $q$. Upstream candidates for `Mathlib.LinearAlgebra.Lagrange`.

## Main results

* `Lagrange.nodalWeight_map`: nodal weights commute with ring homomorphisms.
* `Lagrange.exists_eq_mul_nodalWeight`: the orthogonal complement of the polynomials of degree
  less than $q$ on $q + 1$ nodes is spanned by the nodal weights.
-/

@[expose] public section

open Polynomial Finset

namespace Lagrange

variable {F : Type*} [Field F] {ι : Type*} [DecidableEq ι]

/-- **Nodal weights commute with ring homomorphisms**: for a ring homomorphism $f$ between
fields, the nodal weights of the nodes $f(v_i)$ are the images of those of $v_i$. Used with
`algebraMap ℝ 𝕜` for real nodes viewed in $\Bbbk$. -/
theorem nodalWeight_map {K : Type*} [Field K] (f : F →+* K) (s : Finset ι) (v : ι → F) (i : ι) :
    nodalWeight s (fun j => f (v j)) i = f (nodalWeight s v i) := by
  simp only [nodalWeight, map_prod, map_inv₀, map_sub]

/-- **Orthogonality to low degrees forces the nodal weights**: on $q + 1$ distinct nodes, if
$\sum_{i \in s} z_i\,p(v_i) = 0$ for every $p$ with $\deg p < q$, then $z_i = c\,w_i$ for some
$c$ and every $i \in s$, $w_i$ the nodal weights.
The constant is $c = \sum_{i \in s} z_i v_i^q$.
This is the content of [ChenPersson2026, Lemma 8] (the Ritz polynomial of a prescribed
weighting) and of the proof of [ChenPersson2026, Lemma 9]. -/
theorem exists_eq_mul_nodalWeight {s : Finset ι} {v : ι → F} (hvs : Set.InjOn v s) {q : ℕ}
    (hs : #s = q + 1) {z : ι → F}
    (hz : ∀ p : F[X], p.degree < q → ∑ i ∈ s, z i * p.eval (v i) = 0) :
    ∃ c : F, ∀ i ∈ s, z i = c * nodalWeight s v i := by
  refine ⟨∑ i ∈ s, z i * v i ^ q, fun j hj => ?_⟩
  set b := Lagrange.basis s v j
  have hb : b.degree ≤ q := by
    rw [degree_basis hvs hj, hs, Nat.add_sub_cancel]
  -- the values of the basis polynomial are a Kronecker delta
  have hval : ∀ i ∈ s, b.eval (v i) = if i = j then 1 else 0 := by
    intro i hi
    split_ifs with hij
    · rw [hij]; exact eval_basis_self hvs hj
    · exact eval_basis_of_ne (Ne.symm hij) hi
  -- its coefficient of `X ^ q` is its leading coefficient, the nodal weight of `j`
  have hcoeff : b.coeff q = nodalWeight s v j := by
    have hq : q = b.natDegree := by rw [natDegree_basis hvs hj, hs, Nat.add_sub_cancel]
    rw [hq, ← leadingCoeff, leadingCoeff_basis hvs hj, nodalWeight, prod_inv_distrib]
  have hlow : (b - C (b.coeff q) * X ^ q).degree < (q : WithBot ℕ) := by
    have hle : (b - C (b.coeff q) * X ^ q).degree ≤ (q : WithBot ℕ) :=
      (degree_sub_le _ _).trans (max_le hb (degree_C_mul_X_pow_le _ _))
    refine (degree_lt_iff_coeff_zero _ q).mpr fun m hm => ?_
    rcases hm.eq_or_lt with rfl | hm
    · rw [coeff_sub, coeff_C_mul_X_pow, if_pos rfl, sub_self]
    · exact coeff_eq_zero_of_degree_lt (hle.trans_lt (by exact_mod_cast hm))
  have h0 := hz _ hlow
  simp only [eval_sub, eval_mul, eval_C, eval_X, eval_pow, mul_sub, Finset.sum_sub_distrib] at h0
  rw [Finset.sum_congr rfl fun i hi => by rw [hval i hi], Finset.sum_eq_single_of_mem j hj
    fun i _ hij => by rw [if_neg hij, mul_zero], if_pos rfl, mul_one, sub_eq_zero] at h0
  rw [h0, hcoeff, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

end Lagrange
