/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlibScaffold.ForMathlib.MeasureTheory.Integral.MeanValue
public import NLAlibScaffold.Polynomial.Interpolation.Hermite
public import NLAlibScaffold.Polynomial.Orthogonal.Zeros

/-!
# The Gauss-rule remainder: the theorems of stage KS8

Statements for `NLAlib/Polynomial/Orthogonal/Gauss.lean` whose proofs are deferred
(`docs/design/Polynomial-QuadratureRemainder.md`, G1–G5). An interpolatory rule whose nodal
polynomial is orthogonal to the polynomials of degree less than $m$ is exact below degree
$\lvert s\rvert + m$ (the Gauss case is $m = \lvert s\rvert$, Radau $m = \lvert s\rvert - 1$,
Lobatto $m = \lvert s\rvert - 2$). For $f$ continuous on $[a, b]$ and $C^{2k}$ on $(a, b)$ the
$k$-point Gauss rule has the remainder
$$\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k) =
\frac{f^{(2k)}(\xi)}{(2k)!}\int\pi_k^2\,d\mu\,,\qquad \xi \in (a, b)\,,$$
so it is a lower bound when $f^{(2k)} \ge 0$ and an upper bound when $f^{(2k)} \le 0$.

## Main results

* `NLAlib.IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add`: the exactness
  degree of an interpolatory rule.
* `NLAlib.gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`: the terminating
  case.
* `NLAlib.exists_integral_sub_integral_gaussQuadrature_eq`: the Gauss remainder.
* `NLAlib.integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg`,
  `NLAlib.integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos`: one-sided bounds.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-- **The exactness degree of an interpolatory rule**: if the nodal polynomial of distinct real
nodes $s$ is orthogonal in $L^2(\mu)$ to the polynomials of degree less than $m$, for a finite
measure $\mu$ supported in $[a, b]$, then
$$\int p\,d\mu = \sum_{x\in s}\Bigl(\int\ell_x\,d\mu\Bigr)p(x)$$
for every real polynomial $p$ of degree less than $\lvert s\rvert + m$, $\ell_x$ the Lagrange
basis polynomial of $x$. [Gautschi2004, Theorem 1.45] (locator to check); there as an
equivalence for $m \le \lvert s\rvert$; here the direction used, for every $m$.
Proof: M, about 35 lines. As `IsOrthogonalPolynomial.integral_eval_eq_sum` (the case
$m = \lvert s\rvert$), with the degree bookkeeping generalised: $p = w(p /ₘ w) + p \% w$ for the
monic nodal $w$ of degree $\lvert s\rvert$ (`modByMonic_add_div`), $\deg(p /ₘ w) < m$
(`natDegree_divByMonic`), so its integral against $w$ vanishes by `hs`; the remainder has
degree less than $\lvert s\rvert$ and is integrated exactly
(`integral_eval_eq_sum_of_degree_lt`, KS7's helper, made public for this second consumer); $w$
vanishes at the nodes (`Lagrange.eval_nodal_at_node`). -/
theorem IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add {μ : Measure ℝ}
    {s : Finset ℝ} {m : ℕ} (hs : IsOrthogonalPolynomial μ m (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]}
    (hp : p.degree < (s.card + m : ℕ)) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x := by
  set w := Lagrange.nodal s id with hwdef
  have hw : w.Monic := Lagrange.nodal_monic
  have hsplit := modByMonic_add_div p w
  have hmod : (p %ₘ w).degree < s.card := by
    have := degree_modByMonic_lt p hw
    rwa [Lagrange.degree_nodal] at this
  have hdiv : (p /ₘ w).degree < m := by
    by_cases hq : p /ₘ w = 0
    · rw [hq, degree_zero]
      exact WithBot.bot_lt_coe _
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hq (zero_divByMonic w)
    have hle : w.degree ≤ p.degree :=
      not_lt.mp fun h => hq ((divByMonic_eq_zero_iff hw).mpr h)
    have hle' : s.card ≤ p.natDegree := by
      have := natDegree_le_natDegree hle
      rwa [Lagrange.natDegree_nodal] at this
    rw [degree_eq_natDegree hq, Nat.cast_lt, natDegree_divByMonic p hw, Lagrange.natDegree_nodal]
    rw [degree_eq_natDegree hp0] at hp
    have : p.natDegree < s.card + m := by exact_mod_cast hp
    omega
  have hint1 := integrable_eval_of_ae_mem_Icc hμ (p %ₘ w)
  have hint2 := integrable_eval_of_ae_mem_Icc hμ (w * (p /ₘ w))
  calc ∫ x, p.eval x ∂μ = ∫ x, ((p %ₘ w).eval x + (w * (p /ₘ w)).eval x) ∂μ := by
        conv_lhs => rw [← hsplit]
        simp only [eval_add]
    _ = ∫ x, (p %ₘ w).eval x ∂μ := by
        rw [integral_add hint1 hint2]
        simp only [eval_mul]
        rw [hs _ hdiv, add_zero]
    _ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * (p %ₘ w).eval x :=
        integral_eval_eq_sum_of_degree_lt hμ hmod
    _ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x := by
        refine Finset.sum_congr rfl fun x hx => ?_
        congr 1
        conv_rhs => rw [← hsplit]
        have h0 : w.eval x = 0 := Lagrange.eval_nodal_at_node (v := id) hx
        rw [eval_add, eval_mul, h0, zero_mul, add_zero]

section Finite

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- The terminating case: if the orthogonal polynomial $\pi_k$ of a finite measure $\mu$
supported in $[a, b]$ has norm $0$ in $L^2(\mu)$ ($\mu$ has at most $k$ support points), then
the $k$-point Gauss rule of $\mu$ is $\mu$ itself.
Proof: S, about 12 lines. `ae_eval_eq_zero_of_integral_sq_eq_zero` gives $\pi_k = 0$
$\mu$-a.e., so $\mu$ is carried by the roots of the monic $\pi_k$, the Gauss nodes
(`gaussNodes`, `Multiset.mem_toFinset`, `mem_roots`); then
`interpolatoryQuadrature_eq_self_of_ae_mem`. -/
theorem gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0) : gaussQuadrature μ k = μ := by
  have hzero := ae_eval_eq_zero_of_integral_sq_eq_zero hμ h
  have hne : orthogonalPolynomial μ k ≠ 0 := (monic_orthogonalPolynomial μ k).ne_zero
  unfold gaussQuadrature
  refine interpolatoryQuadrature_eq_self_of_ae_mem ?_
  filter_upwards [hzero] with x hx
  unfold gaussNodes
  rw [Multiset.mem_toFinset, mem_roots hne]
  exact hx

/-- The pointwise Hermite remainder at doubled nodes: for a nonempty finite set $G \subseteq (a, b)$
and $H$ of degree less than $2\lvert G\rvert$ matching the values and first derivatives of $f$ on
$G$, $f(x) - H(x) = \frac{f^{(2\lvert G\rvert)}(\xi)}{(2\lvert G\rvert)!}\omega_G(x)^2$. -/
private theorem exists_sub_eval_eq_iteratedDeriv_mul_nodal_sq {a b : ℝ} (hab : a < b)
    {G : Finset ℝ} (hG : G.Nonempty) (hGab : (G : Set ℝ) ⊆ Set.Ioo a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * G.card : ℕ) f (Set.Ioo a b))
    {H : ℝ[X]} (hH : H.degree < (G.val + G.val).card)
    (hjet : ∀ y ∈ G.val + G.val, ∀ k < (G.val + G.val).count y,
      (derivative^[k] H).eval y = iteratedDeriv k f y)
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    ∃ ξ ∈ Set.Ioo a b, f x - H.eval x =
      iteratedDeriv (2 * G.card) f ξ / (2 * G.card).factorial *
        (Lagrange.nodal G id).eval x ^ 2 := by
  have hcard : (G.val + G.val).card = 2 * G.card := by
    rw [Multiset.card_add, Finset.card_val]; ring
  have hmem : ∀ y ∈ G.val + G.val, y ∈ Set.Ioo a b := fun y hy => by
    rcases Multiset.mem_add.mp hy with h | h <;> exact hGab h
  obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul hab
    (by simpa using hG.ne_empty) (fun y hy => Set.Ioo_subset_Icc_self (hmem y hy))
    (fun y hy _ => hmem y hy) hf (hcard ▸ hf') hH hjet hx
  refine ⟨ξ, hξ, h.trans ?_⟩
  rw [hcard, Multiset.map_add, Multiset.prod_add, Lagrange.nodal, Finset.prod_eq_multiset_prod]
  rw [sq, eval_mul]; rfl

/-- **The Gauss quadrature remainder**: for a finite measure $\mu$ supported in $[a, b]$,
$a < b$, $k > 0$, and $f$ continuous on $[a, b]$ and $C^{2k}$ on $(a, b)$, there is
$\xi \in (a, b)$ with
$$\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k) =
\frac{f^{(2k)}(\xi)}{(2k)!}\int\pi_k^2\,d\mu\,,$$
$\pi_k$ the monic orthogonal polynomial of degree $k$. When $\mu$ has at most $k$ support
points both sides are $0$. [Gautschi2004, Theorem 1.48]; [GolubMeurant2010, Ch. 6] (locators to
check); there for $f \in C^{2k}[a, b]$.
Proof: L, about 70 lines; the prototype proves the nondegenerate case
(`NLAlib.exists_integral_sub_quadrature_eq_iteratedDeriv_mul_nodal_sq`,
`NLAlib/Polynomial/Quadrature/GaussDerivativeRemainder.lean`). If
$\int\pi_k^2\,d\mu = 0$: `gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`,
both sides $0$, $\xi = (a + b)/2$. Otherwise $\mu$ is definite up to degree $k + 1$
(`isMomentPosDef_succ_iff`), the Gauss nodes $G$ are $k$ distinct points of $(a, b)$
(`IsMomentPosDef.card_gaussNodes`, `IsMomentPosDef.gaussNodes_subset_Ioo`) and
$\pi_k = \prod_{x\in G}(X - x)$ (`IsMomentPosDef.nodal_gaussNodes`). Take $H$ of degree less
than $2k$ with the values and first derivatives of $f$ on $G$
(`exists_degree_lt_forall_iterate_derivative_eval_eq` for $m = G + G$). The rule is exact on
$H$ and $H = f$ on $G$ (`matchesMoments_gaussQuadrature`, `integral_gaussQuadrature_eq_sum`), so
the error is $\int(f - H)\,d\mu$. Pointwise `exists_sub_eval_eq_iteratedDeriv_mul` on
$m = G + G$ gives $f - H = \frac{f^{(2k)}(\xi_x)}{(2k)!}\pi_k(x)^2$, and
`exists_integral_eq_mul_integral_of_ae_nonneg` with $W = \pi_k^2$ and $s = (a, b)$ (the $2k$-th
derivative is continuous there, from `hf'`) gives one $\xi$. Integrability:
`ContinuousOn.integrableOn_Icc` and `integrable_eval_of_ae_mem_Icc`.
Result: gauss-quadrature-remainder -/
theorem exists_integral_sub_integral_gaussQuadrature_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) {k : ℕ} (hk : 0 < k) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ k =
      iteratedDeriv (2 * k) f ξ / (2 * k).factorial *
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ := by
  have hfi : Integrable f μ := by
    have h := hf.integrableOn_Icc (μ := μ)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h
  set π := orthogonalPolynomial μ k
  rcases (integral_nonneg fun x => sq_nonneg (π.eval x) : 0 ≤ ∫ x, π.eval x ^ 2 ∂μ).eq_or_lt
    with h0 | hpos
  · refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [← h0, gaussQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero hμ h0.symm,
      sub_self, mul_zero]
  have hPD := (isMomentPosDef_succ_iff hμ k).mpr hpos
  set G := gaussNodes μ k
  have hcard : G.card = k := (hPD.mono k.le_succ).card_gaussNodes hμ
  have hGab : (G : Set ℝ) ⊆ Set.Ioo a b := hPD.gaussNodes_subset_Ioo hμ
  have hnodal : Lagrange.nodal G id = π := (hPD.mono k.le_succ).nodal_gaussNodes hμ
  have hG : G.Nonempty := Finset.card_pos.mp (hcard ▸ hk)
  obtain ⟨H, hHdeg, hHjet⟩ :=
    exists_degree_lt_forall_iterate_derivative_eval_eq (G.val + G.val)
      fun y j => iteratedDeriv j f y
  have hm : (G.val + G.val).card = 2 * k := by
    rw [Multiset.card_add, Finset.card_val, hcard]; ring
  -- the rule integrates `f` as it integrates `H`, exactly
  have hquad : ∫ x, f x ∂gaussQuadrature μ k = ∫ x, H.eval x ∂μ := by
    rw [matchesMoments_gaussQuadrature hμ k H (by rw [← hm]; exact_mod_cast hHdeg),
      integral_gaussQuadrature_eq_sum, integral_gaussQuadrature_eq_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : y ∈ G.val + G.val := Multiset.mem_add.mpr (Or.inl hy)
    have := hHjet y hy' 0 (Multiset.count_pos.mpr hy')
    simp only [Function.iterate_zero, id_eq, iteratedDeriv_zero] at this
    rw [this]
  rw [hquad, ← integral_sub hfi (integrable_eval_of_ae_mem_Icc hμ H)]
  have hD : ContinuousOn (fun t => iteratedDeriv (2 * k) f t / (2 * k).factorial)
      (Set.Ioo a b) :=
    (hf'.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ioo a b)).congr
      (fun t ht => (iteratedDerivWithin_of_isOpen isOpen_Ioo ht).symm) |>.div_const _
  refine exists_integral_eq_mul_integral_of_ae_nonneg
    (hfi.sub (integrable_eval_of_ae_mem_Icc hμ H))
    ((integrable_eval_of_ae_mem_Icc hμ (π ^ 2)).congr (ae_of_all _ fun x => by simp))
    (ae_of_all _ fun x => sq_nonneg _) (isConnected_Ioo hab) hD ?_
  filter_upwards [hμ] with x hx
  obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul_nodal_sq hab hG hGab hf
    (hcard ▸ hf') hHdeg hHjet hx
  rw [hcard, hnodal] at h
  exact ⟨ξ, hξ, h⟩

/-- **Gauss quadrature is a lower bound** for $f$ with nonnegative derivative of order $2k$: for
a finite measure $\mu$ supported in $[a, b]$, $a < b$, $k > 0$, and $f$ continuous on $[a, b]$,
$C^{2k}$ on $(a, b)$ with $f^{(2k)} \ge 0$ there,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) \le \int f\,d\mu\,.$$
[Gautschi2004, Theorem 1.48]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 8 lines. `exists_integral_sub_integral_gaussQuadrature_eq`; the right side is
a product of $f^{(2k)}(\xi)/(2k)! \ge 0$ and $\int\pi_k^2\,d\mu \ge 0$ (`integral_nonneg`,
`sq_nonneg`, `Nat.cast_nonneg`, `div_nonneg`); `sub_nonneg`. -/
theorem integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {k : ℕ} (hk : 0 < k) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k) f x) :
    ∫ x, f x ∂gaussQuadrature μ k ≤ ∫ x, f x ∂μ := by
  sorry

/-- **Gauss quadrature is an upper bound** for $f$ with nonpositive derivative of order $2k$:
for a finite measure $\mu$ supported in $[a, b]$, $a < b$, $k > 0$, and $f$ continuous on
$[a, b]$, $C^{2k}$ on $(a, b)$ with $f^{(2k)} \le 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{gaussQuadrature}(\mu, k)\,.$$
[Gautschi2004, Theorem 1.48]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 8 lines. As `integral_gaussQuadrature_le_integral_of_iteratedDeriv_nonneg`,
with `mul_nonpos_of_nonpos_of_nonneg` (or apply it to $-f$: `iteratedDeriv_neg`,
`integral_neg`). -/
theorem integral_le_integral_gaussQuadrature_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {k : ℕ} (hk : 0 < k) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k) f x ≤ 0) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂gaussQuadrature μ k := by
  sorry

end Finite

end NLAlib
