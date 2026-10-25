/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlibScaffold.ForMathlib.Algebra.Polynomial.Derivative
public import NLAlibScaffold.ForMathlib.Analysis.Calculus.Deriv.Polynomial
public import NLAlibScaffold.ForMathlib.Analysis.Calculus.LocalExtr.Rolle

/-!
# Hermite interpolation and the interpolation remainder

Nodes with multiplicity are a multiset $m$: a node $y$ of multiplicity $r$ prescribes the values
$p(y), p'(y), \dots, p^{(r-1)}(y)$. For any such data there is exactly one polynomial of degree
less than $\lvert m\rvert$ matching it (confluent Hermite interpolation). If $f$ is smooth and
$H$ matches the jets of $f$, the error is
$$f(x) - H(x) = \frac{f^{(\lvert m\rvert)}(\xi)}{\lvert m\rvert!}\,\omega_m(x)\,,\qquad
\omega_m = \prod_{y\in m}(x - y)\,,$$
for some $\xi$ in the interval. Simple nodes give the Lagrange interpolation remainder for
Mathlib's `Lagrange.interpolate`; doubled Gauss nodes and simple endpoints give the Gauss, Radau
and Lobatto remainders (`NLAlib.Polynomial.Orthogonal.Gauss`,
`NLAlib.Polynomial.Orthogonal.RadauLobatto`).

There is no Hermite interpolant definition: the remainder is stated for any polynomial matching
the jets, and the existence theorem supplies one (`docs/design/Polynomial-QuadratureRemainder.md`,
OQ1).

## Main results

* `NLAlib.exists_degree_lt_forall_iterate_derivative_eval_eq`: existence of the Hermite
  interpolant.
* `NLAlib.eq_of_degree_lt_of_forall_iterate_derivative_eval_eq`: its uniqueness.
* `NLAlib.exists_sub_eval_eq_iteratedDeriv_mul`: the Hermite interpolation remainder.
* `NLAlib.exists_sub_eval_interpolate_eq_iteratedDeriv_mul`: the Lagrange interpolation
  remainder.
-/

@[expose] public section

open Polynomial

namespace NLAlib

/-! ### Existence and uniqueness -/

section Algebra

variable {F : Type*} [Field F] [CharZero F] [DecidableEq F]

/-- **Uniqueness of Hermite interpolation**: over a field of characteristic $0$, two polynomials
of degree less than $\lvert m\rvert$ whose derivatives of order below the multiplicity of $y$
agree at every $y$ of the multiset $m$ are equal.
[Davis1975, Theorem 2.7.1] (locator to check).
Proof: M, about 30 lines. Let $d = p - q$ (`iterate_derivative_sub`). If $d \ne 0$, every
$y \in m$ has `rootMultiplicity y d ≥ count y m`
(`lt_rootMultiplicity_iff_isRoot_iterate_derivative`, characteristic $0$), so
$m \le d.\mathrm{roots}$ (`Multiset.le_iff_count`, `count_roots`) and
$\lvert m\rvert \le \deg d < \lvert m\rvert$ (`Multiset.card_le_card`, `card_roots'`). -/
theorem eq_of_degree_lt_of_forall_iterate_derivative_eval_eq {m : Multiset F} {p q : F[X]}
    (hp : p.degree < m.card) (hq : q.degree < m.card)
    (h : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] p).eval y = (derivative^[k] q).eval y) :
    p = q := by
  by_contra hne
  have hd : p - q ≠ 0 := sub_ne_zero.mpr hne
  have hle : m ≤ (p - q).roots := by
    rw [Multiset.le_iff_count]
    intro y
    by_cases hy : y ∈ m
    · rw [count_roots]
      have hpos : 0 < m.count y := Multiset.count_pos.mpr hy
      have hroot : ∀ j ≤ m.count y - 1, (derivative^[j] (p - q)).IsRoot y := by
        intro j hj
        rw [iterate_derivative_sub, IsRoot, eval_sub, sub_eq_zero]
        exact h y hy j (by omega)
      have := (lt_rootMultiplicity_iff_isRoot_iterate_derivative hd).mpr hroot
      omega
    · simp [Multiset.count_eq_zero.mpr hy]
  have hdeg : (p - q).degree < m.card := (degree_sub_le p q).trans_lt (max_lt hp hq)
  have hcard := Multiset.card_le_card hle
  have hcard' := card_roots' (p - q)
  have hnat : (p - q).natDegree < m.card := (natDegree_lt_iff_degree_lt hd).mpr hdeg
  omega

/-- **Hermite interpolation**: over a field of characteristic $0$, for every multiset $m$ of
nodes and all prescribed values $r(y, k)$, there is a polynomial $H$ of degree less than
$\lvert m\rvert$ with $H^{(k)}(y) = r(y, k)$ for every $y \in m$ and every $k$ below the
multiplicity of $y$. [Davis1975, Theorem 2.7.1] (locator to check).
Proof: M, about 45 lines. The jet map from `degreeLT F m.card` (dimension $\lvert m\rvert$,
`Polynomial.degreeLT` with `dim_degreeLT`) to
$\prod_{y \in m.\mathrm{toFinset}}F^{\mathrm{count}\,y}$
(dimension $\sum_y \mathrm{count}\,y = \lvert m\rvert$, `Multiset.toFinset_sum_count_eq`) is
linear and injective by `eq_of_degree_lt_of_forall_iterate_derivative_eval_eq`, hence surjective
(`LinearMap.injective_iff_surjective_of_finrank_eq_finrank`). Alternatively, the Chinese
remainder theorem for the pairwise coprime $(X - y)^{\mathrm{count}\,y}$ and the Taylor
polynomials of the data, reduced modulo $\omega_m$. -/
theorem exists_degree_lt_forall_iterate_derivative_eval_eq (m : Multiset F) (r : F → ℕ → F) :
    ∃ H : F[X], H.degree < m.card ∧
      ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] H).eval y = r y k := by
  let J : degreeLT F m.card →ₗ[F] (∀ y : m.toFinset, Fin (m.count (y : F)) → F) :=
    { toFun := fun p y k => (derivative^[(k : ℕ)] (p : F[X])).eval (y : F)
      map_add' := by
        intro p q
        funext y k
        simp only [Pi.add_apply, Submodule.coe_add, iterate_map_add, eval_add]
      map_smul' := by
        intro c p
        funext y k
        simp only [Pi.smul_apply, Submodule.coe_smul, iterate_derivative_smul, eval_smul,
          smul_eq_mul, RingHom.id_apply] }
  have hdimV : Module.finrank F (degreeLT F m.card) = m.card :=
    (Polynomial.degreeLTEquiv F m.card).finrank_eq.trans (Module.finrank_fin_fun F)
  have : Module.Finite F (degreeLT F m.card) :=
    Module.Finite.equiv (Polynomial.degreeLTEquiv F m.card).symm
  have hdimW : Module.finrank F (∀ y : m.toFinset, Fin (m.count (y : F)) → F) = m.card := by
    rw [Module.finrank_pi_fintype]
    simp only [Module.finrank_fin_fun]
    exact (Finset.sum_coe_sort _ _).trans (Multiset.toFinset_sum_count_eq m)
  have hinj : Function.Injective J := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro p hp
    have hp0 : J p = 0 := hp
    apply Subtype.ext
    apply eq_of_degree_lt_of_forall_iterate_derivative_eval_eq
    · exact p.2 |> Polynomial.mem_degreeLT.mp
    · simp
    · intro y hy k hk
      have h1 : (derivative^[k] (p : F[X])).eval (y : F) = 0 :=
        congrFun (congrFun hp0 ⟨y, Multiset.mem_toFinset.mpr hy⟩) ⟨k, hk⟩
      simpa using h1
  have hsurj : Function.Surjective J := by
    let e : (∀ y : m.toFinset, Fin (m.count (y : F)) → F) ≃ₗ[F] degreeLT F m.card :=
      LinearEquiv.ofFinrankEq _ _ (hdimW.trans hdimV.symm)
    have hs := LinearMap.surjective_of_injective
      (f := J.comp e.toLinearMap) (hinj.comp e.injective)
    intro w
    obtain ⟨u, hu⟩ := hs w
    exact ⟨e u, by simpa using hu⟩
  obtain ⟨p, hp⟩ := hsurj (fun y k => r y k)
  refine ⟨p, Polynomial.mem_degreeLT.mp p.2, fun y hy k hk => ?_⟩
  exact congrFun (congrFun hp ⟨y, Multiset.mem_toFinset.mpr hy⟩) ⟨k, hk⟩

end Algebra

/-! ### The remainder -/

/-- On an open set where $f$ is $C^n$, the derivatives of order at most $n$ of $f - P$, $P$ a
polynomial, are those of $f$ minus the formal derivatives of $P$. -/
private lemma iteratedDerivWithin_sub_eval_eqOn {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {n : ℕ}
    (hf : ContDiffOn ℝ n f s) (P : ℝ[X]) :
    ∀ j ≤ n, Set.EqOn (iteratedDerivWithin j (fun t => f t - P.eval t) s)
      (fun t => iteratedDerivWithin j f s t - (derivative^[j] P).eval t) s := by
  intro j hj
  induction j with
  | zero => intro t _; simp
  | succ j ih =>
    intro t ht
    have hft : DifferentiableWithinAt ℝ (iteratedDerivWithin j f s) s t :=
      hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hj) hs.uniqueDiffOn t ht
    have hPt : DifferentiableWithinAt ℝ (fun t => (derivative^[j] P).eval t) s t :=
      (derivative^[j] P).differentiable.differentiableAt.differentiableWithinAt
    simp only [iteratedDerivWithin_succ]
    rw [derivWithin_congr (ih (by omega)) (ih (by omega) ht),
      derivWithin_fun_sub hft hPt,
      derivWithin_of_isOpen hs ht (f := fun t => (derivative^[j] P).eval t), Polynomial.deriv,
      Function.iterate_succ_apply']

/-- On an open set, $f - P$ is $C^n$ when $f$ is, for a polynomial $P$. -/
private lemma contDiffOn_sub_eval {f : ℝ → ℝ} {s : Set ℝ} (hs : IsOpen s) {n : ℕ}
    (hf : ContDiffOn ℝ n f s) (P : ℝ[X]) : ContDiffOn ℝ n (fun t => f t - P.eval t) s := by
  have hf' := (contDiffOn_iff_continuousOn_differentiableOn_deriv hs.uniqueDiffOn).mp hf
  refine (contDiffOn_iff_continuousOn_differentiableOn_deriv hs.uniqueDiffOn).mpr
    ⟨fun j hj => ?_, fun j hj => ?_⟩
  · refine ContinuousOn.congr ?_
      (iteratedDerivWithin_sub_eval_eqOn hs hf P j (by exact_mod_cast hj))
    exact (hf'.1 j hj).sub (derivative^[j] P).differentiable.continuous.continuousOn
  · refine DifferentiableOn.congr ?_
      (iteratedDerivWithin_sub_eval_eqOn hs hf P j (by exact_mod_cast hj.le))
    exact (hf'.2 j hj).sub (derivative^[j] P).differentiable.differentiableOn

/-- **The Hermite interpolation remainder**: let $a < b$, $m$ a nonempty multiset of points of
$[a, b]$ with every point of multiplicity at least $2$ in $(a, b)$, $f$ continuous on $[a, b]$
and $C^{\lvert m\rvert}$ on $(a, b)$, and $H$ a real polynomial of degree less than
$\lvert m\rvert$ with $H^{(k)}(y) = f^{(k)}(y)$ for every $y \in m$ and every $k$ below the
multiplicity of $y$. Then for every $x \in [a, b]$ there is $\xi \in (a, b)$ with
$$f(x) - H(x) = \frac{f^{(\lvert m\rvert)}(\xi)}{\lvert m\rvert!}\prod_{y\in m}(x - y)\,.$$
[Davis1975, Theorem 3.5.1]; [Gautschi2004, §1.4.2] (locators to check); there for distinct
nodes of multiplicity at most $2$ with $\xi$ in the hull of the nodes and $x$; here any
multiplicities, simple nodes allowed at the endpoints.
Proof: L, about 120 lines; the prototype proves it
(`NLAlib.exists_sub_eval_eq_iteratedDeriv_mul_of_multiset`,
`NLAlib/Polynomial/Quadrature/HermiteRemainder.lean`). If $\omega_m(x) = 0$ then $x \in m$ and
both sides vanish (`hjet` at $k = 0$; take $\xi = (a + b)/2$). Otherwise set
$K = (f(x) - H(x))/\omega_m(x)$ and $g = f - (H + K\omega_m)$: $g$ has the jets of $0$ on $m$
and $g(x) = 0$, so the multiset $m + \{x\}$ of $\lvert m\rvert + 1$ zeros, through
`exists_iteratedDeriv_eq_zero_of_multiset` with $q = \lvert m\rvert - 1$, gives
$g^{(\lvert m\rvert)}(\xi) = 0$. The polynomial part is `Polynomial.iteratedDeriv` (as an
`EqOn` on the open interval; the prototype's `iteratedDeriv_sub_eval_eqOn`), $H^{(\lvert
m\rvert)} = 0$ (`iterate_derivative_eq_zero_of_degree_lt`) and
$\omega_m^{(\lvert m\rvert)} = \lvert m\rvert!$ (`Polynomial.iterate_derivative_natDegree`,
`natDegree_multiset_prod_X_sub_C_eq_card`, `monic_multiset_prod_of_monic`). The jets of
$\omega_m$ vanish on $m$ because $(X - y)^{\mathrm{count}\,y}$ divides it
(`isRoot_iterate_derivative_of_lt_rootMultiplicity`, `count_roots`,
`roots_multiset_prod_X_sub_C`).
Result: hermite-interpolation-remainder -/
theorem exists_sub_eval_eq_iteratedDeriv_mul {a b : ℝ} (hab : a < b) {m : Multiset ℝ}
    (hm : m ≠ 0) (hmem : ∀ y ∈ m, y ∈ Set.Icc a b)
    (hrep : ∀ y ∈ m, 1 < m.count y → y ∈ Set.Ioo a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ m.card f (Set.Ioo a b)) {H : ℝ[X]}
    (hH : H.degree < m.card)
    (hjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] H).eval y = iteratedDeriv k f y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - H.eval x =
      iteratedDeriv m.card f ξ / m.card.factorial * ((m.map fun y => X - C y).prod).eval x := by
  set ω : ℝ[X] := (m.map fun y => X - C y).prod with hω
  have hωjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] ω).eval y = 0 := by
    intro y hy k hk
    refine isRoot_iterate_derivative_of_lt_rootMultiplicity ?_
    rwa [← count_roots, hω, roots_multiset_prod_X_sub_C]
  by_cases hωx : ω.eval x = 0
  · have hxm : x ∈ m := by
      rw [hω, eval_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.map_map] at hωx
      simpa [sub_eq_zero, eq_comm] using hωx
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    have := hjet x hxm 0 (Multiset.count_pos.mpr hxm)
    simp only [Function.iterate_zero, id, iteratedDeriv_zero] at this
    rw [hωx, this, sub_self, mul_zero]
  set K := (f x - H.eval x) / ω.eval x with hK
  set p : ℝ[X] := H + C K * ω with hp
  set g : ℝ → ℝ := fun t => f t - p.eval t with hg
  have hgD : ∀ t ∈ Set.Ioo a b, ∀ j ≤ m.card,
      iteratedDeriv j g t = iteratedDeriv j f t - (derivative^[j] p).eval t := by
    intro t ht j hj
    rw [← iteratedDerivWithin_of_isOpen isOpen_Ioo ht,
      ← iteratedDerivWithin_of_isOpen isOpen_Ioo ht]
    exact iteratedDerivWithin_sub_eval_eqOn isOpen_Ioo hf' p j hj ht
  have hpjet : ∀ y ∈ m, ∀ k < m.count y, (derivative^[k] p).eval y = iteratedDeriv k f y := by
    intro y hy k hk
    rw [hp, iterate_map_add, iterate_derivative_C_mul, eval_add, eval_mul,
      hωjet y hy k hk, mul_zero, add_zero, hjet y hy k hk]
  have hgx : g x = 0 := by
    simp only [hg, hp, eval_add, eval_mul, eval_C, hK, div_mul_cancel₀ _ hωx]
    ring
  have hxm : x ∉ m := fun hxm => hωx (by simpa using hωjet x hxm 0 (Multiset.count_pos.mpr hxm))
  have hn : m.card - 1 + 1 = m.card := Nat.succ_pred_eq_of_pos (Multiset.card_pos.mpr hm)
  obtain ⟨ξ, hξ, hgξ⟩ : ∃ ξ ∈ Set.Ioo a b, iteratedDeriv (m.card - 1 + 1) g ξ = 0 := by
    refine exists_iteratedDeriv_eq_zero_of_multiset (m := x ::ₘ m) (by simp; omega) ?_ ?_
      (hf.sub p.differentiable.continuous.continuousOn)
      (by rw [hn]; exact contDiffOn_sub_eval isOpen_Ioo hf' p) ?_
    · rintro y hy
      rcases Multiset.mem_cons.mp hy with rfl | hy
      exacts [hx, hmem y hy]
    · rintro y hy hy1
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · simp [Multiset.count_eq_zero.mpr hxm] at hy1
      · have hyx : y ≠ x := fun h => hxm (h ▸ hy)
        rw [Multiset.count_cons_of_ne hyx] at hy1
        exact hrep y hy hy1
    · rintro y hy j hj
      rcases Multiset.mem_cons.mp hy with rfl | hy
      · simp only [Multiset.count_cons_self, Multiset.count_eq_zero.mpr hxm] at hj
        rw [Nat.lt_one_iff.mp hj, iteratedDeriv_zero, hgx]
      have hyx : y ≠ x := fun h => hxm (h ▸ hy)
      rw [Multiset.count_cons_of_ne hyx] at hj
      rcases Nat.eq_zero_or_pos j with rfl | hj0
      · simpa [hg, sub_eq_zero] using (hpjet y hy 0 hj).symm
      rw [hgD y (hrep y hy (by omega)) j ((hj.le).trans (Multiset.count_le_card y m)),
        hpjet y hy j hj, sub_self]
  have hpn : (derivative^[m.card] p).eval ξ = K * m.card.factorial := by
    have hωdeg : ω.natDegree = m.card := natDegree_multiset_prod_X_sub_C_eq_card m
    rw [hp, iterate_map_add, iterate_derivative_eq_zero_of_degree_lt hH,
      iterate_derivative_C_mul, ← hωdeg, iterate_derivative_natDegree,
      (monic_multiset_prod_of_monic _ _ fun y _ => monic_X_sub_C y).leadingCoeff]
    simp
  refine ⟨ξ, hξ, ?_⟩
  rw [hn, hgD ξ hξ _ le_rfl, hpn, sub_eq_zero] at hgξ
  rw [hgξ, hK]
  field_simp

/-- **The Lagrange interpolation remainder**: for $a < b$, a nonempty finite set $s$ of nodes
in $[a, b]$, $f$ continuous on $[a, b]$ and $C^{\lvert s\rvert}$ on $(a, b)$, and every
$x \in [a, b]$, there is $\xi \in (a, b)$ with
$$f(x) - p_s(x) = \frac{f^{(\lvert s\rvert)}(\xi)}{\lvert s\rvert!}\prod_{y\in s}(x - y)\,,$$
$p_s$ the Lagrange interpolant of $f$ at $s$ (Mathlib's `Lagrange.interpolate s id f`).
[Davis1975, Theorem 3.1.1]; [Trefethen2019, Ch. 11] (locators to check); there with $\xi$ in
the hull of $s$ and $x$.
Proof: S, about 15 lines. `exists_sub_eval_eq_iteratedDeriv_mul` with $m = s.\mathrm{val}$
(`Finset.card_val`, every count is $1$ by `Multiset.count_eq_one_of_mem` and `s.nodup`, so
`hrep` is vacuous and only $k = 0$ occurs in the jets): `Lagrange.degree_interpolate_lt`,
`Lagrange.eval_interpolate_at_node`, and `Lagrange.nodal` is the multiset product
(`Lagrange.nodal`, `Finset.prod_eq_multiset_prod`).
Result: lagrange-interpolation-remainder -/
theorem exists_sub_eval_interpolate_eq_iteratedDeriv_mul {a b : ℝ} (hab : a < b) {s : Finset ℝ}
    (hs : s.Nonempty) (hsab : (s : Set ℝ) ⊆ Set.Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ s.card f (Set.Ioo a b)) {x : ℝ}
    (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - (Lagrange.interpolate s id f).eval x =
      iteratedDeriv s.card f ξ / s.card.factorial * (Lagrange.nodal s id).eval x := by
  have hnodup : s.val.Nodup := s.nodup
  have hcount : ∀ y ∈ s.val, s.val.count y = 1 := fun y hy =>
    Multiset.count_eq_one_of_mem hnodup hy
  have hm : s.val ≠ 0 := by
    intro h
    obtain ⟨y, hy⟩ := hs
    rw [Finset.val_eq_zero] at h
    simp_all
  have hmem : ∀ y ∈ s.val, y ∈ Set.Icc a b := fun y hy => hsab (Finset.mem_coe.mpr hy)
  have hrep : ∀ y ∈ s.val, 1 < s.val.count y → y ∈ Set.Ioo a b := fun y hy h => by
    rw [hcount y hy] at h
    exact absurd h (by norm_num)
  have hH : (Lagrange.interpolate s id f).degree < (s.val).card :=
    Lagrange.degree_interpolate_lt _ (Set.injOn_id _)
  have hjet : ∀ y ∈ s.val, ∀ k < s.val.count y,
      (derivative^[k] (Lagrange.interpolate s id f)).eval y = iteratedDeriv k f y := by
    intro y hy k hk
    rw [hcount y hy] at hk
    obtain rfl : k = 0 := by omega
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero]
    exact Lagrange.eval_interpolate_at_node _ (Set.injOn_id _) (Finset.mem_val.mp hy)
  obtain ⟨ξ, hξ, heq⟩ := exists_sub_eval_eq_iteratedDeriv_mul (m := s.val) hab hm hmem hrep hf hf'
    hH hjet hx
  refine ⟨ξ, hξ, ?_⟩
  rw [heq, Lagrange.nodal, Finset.prod_eq_multiset_prod]
  simp

end NLAlib
