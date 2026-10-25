/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.RadauLobatto
public import NLAlibScaffold.Polynomial.Orthogonal.Gauss

/-!
# Gauss–Radau and Gauss–Lobatto rules: the theorems of stage KS8

Statements for `NLAlib/Polynomial/Orthogonal/RadauLobatto.lean` whose proofs are deferred
(`docs/design/Polynomial-QuadratureRemainder.md`, R1–R17, L1–L14, J1–J3). For a finite measure
$\mu$ supported in $[a, b]$ and $c \in \{a, b\}$, the Radau rule with prescribed node $c$ and $k$
free nodes matches the first $2k + 1$ moments of $\mu$, is the only measure on $c$ and at most
$k$ further points that does, and has the remainder
$$\int f\,d\mu - \int f\,d\,\mathsf{radauQuadrature}(\mu, c, k) =
\frac{f^{(2k+1)}(\xi)}{(2k+1)!}\int(x - c)\,\tilde\pi_k(x)^2\,d\mu(x)\,,$$
$\tilde\pi_k$ the orthogonal polynomial of `radauMeasure μ c`. At $c = a$ the weight is
nonnegative and at $c = b$ nonpositive, which gives the four one-sided bounds. For $a < b$ the
Lobatto rule matches $2k + 2$ moments and has the remainder with
$\frac{f^{(2k+2)}(\xi)}{(2k+2)!}\int(x - a)(x - b)\hat\pi_k(x)^2\,d\mu(x)$, nonpositive weight.
The Radau Jacobi matrix has $c$ as an eigenvalue and the moments of the Jacobi matrix through
degree $2k$.

## Main results

* `NLAlib.matchesMoments_radauQuadrature`, `NLAlib.MatchesMoments.eq_radauQuadrature`: Radau
  exactness and uniqueness.
* `NLAlib.integral_eval_basis_radauNodes_nonneg`, `NLAlib.integral_eval_basis_lobattoNodes_nonneg`:
  nonnegative weights.
* `NLAlib.exists_integral_sub_integral_radauQuadrature_eq`: the Radau remainder.
* `NLAlib.integral_radauQuadrature_le_integral_of_iteratedDeriv_nonneg` and its three siblings:
  the Radau bounds.
* `NLAlib.matchesMoments_lobattoQuadrature`,
  `NLAlib.exists_integral_sub_integral_lobattoQuadrature_eq`: Lobatto exactness and remainder,
  with two bounds.
* `NLAlib.IsMomentPosDef.radauJacobiMatrix_mulVec_eq`,
  `NLAlib.radauJacobiMatrix_pow_apply_zero_zero`: the Radau Jacobi matrix.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix

namespace NLAlib

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b c : ℝ}

/-! ### The Radau modified measure -/

/-- Integrals against the Radau modified measure: for every measure $\mu$ on $\mathbb{R}$, every
$c$ and every $g : \mathbb{R} \to \mathbb{R}$,
$\int g\,d\,\mathsf{radauMeasure}(\mu, c) = \int\lvert x - c\rvert\,g(x)\,d\mu(x)$.
Proof: S, about 8 lines. `radauMeasure`; `‖x - c‖ₑ` is the coercion of the measurable
`fun x => ‖x - c‖₊` (`enorm_eq_nnnorm`), so `integral_withDensity_eq_integral_smul`
(`measurable_nnnorm` composed with `measurable_id.sub_const`); `NNReal.smul_def`,
`Real.coe_nnnorm`, `Real.norm_eq_abs`. -/
theorem integral_radauMeasure (μ : Measure ℝ) (c : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂radauMeasure μ c = ∫ x, |x - c| * g x ∂μ := by
  unfold radauMeasure
  have hd : (fun x : ℝ => ‖x - c‖ₑ) = fun x => ((‖x - c‖₊ : NNReal) : ENNReal) :=
    funext fun x => enorm_eq_nnnorm _
  rw [hd, integral_withDensity_eq_integral_smul
    (f := fun x : ℝ => ‖x - c‖₊) (measurable_nnnorm.comp (measurable_id.sub_const c))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [NNReal.smul_def, smul_eq_mul, coe_nnnorm, Real.norm_eq_abs, mul_comm]

/-- The Radau modified measure of a finite measure supported in $[a, b]$ is finite.
Proof: S, about 12 lines. `isFiniteMeasure_withDensity_ofReal`-style: the density is at most
$\max(\lvert a - c\rvert, \lvert b - c\rvert)$ $\mu$-a.e. (`hμ`), so
`withDensity_apply_le`/`lintegral_mono_ae` bounds the mass by that constant times
$\mu(\mathbb{R}) < \infty$ (`measure_lt_top`). -/
theorem isFiniteMeasure_radauMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (c : ℝ) :
    IsFiniteMeasure (radauMeasure μ c) :=
  isFiniteMeasure_withDensity ((integrable_eval_of_ae_mem_Icc hμ (X - C c)).congr
    (ae_of_all μ fun x => by simp) : Integrable (fun x => x - c) μ).2.ne

/-- The Radau modified measure lives where $\mu$ does: for $\mu$ supported in $[a, b]$ and every
$c$, almost every point of `radauMeasure μ c` lies in $[a, b]$.
Proof: S, about 4 lines. `withDensity_absolutelyContinuous` and `Measure.AbsolutelyContinuous.ae_le`
applied to `hμ`. -/
theorem ae_mem_Icc_radauMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (c : ℝ) :
    ∀ᵐ x ∂radauMeasure μ c, x ∈ Set.Icc a b := by
  unfold radauMeasure
  exact (withDensity_absolutelyContinuous μ _).ae_le hμ

/-! ### Radau exactness -/

omit [IsFiniteMeasure μ] in
/-- Membership in the Gauss nodes: $x$ is a Gauss node of order $k$ of $\mu$ iff it is a zero
of $\pi_k$. -/
private theorem mem_gaussNodes_iff_isRoot {k : ℕ} {x : ℝ} :
    x ∈ gaussNodes μ k ↔ (orthogonalPolynomial μ k).IsRoot x := by
  rw [gaussNodes, Multiset.mem_toFinset, mem_roots (monic_orthogonalPolynomial μ k).ne_zero]

omit [IsFiniteMeasure μ] in
/-- A Gauss node splits off a linear factor: if $t$ is a Gauss node of order $k$ of $\mu$, then
$\pi_k = (X - t)g$ with $g \ne 0$ of degree less than $k$. -/
private theorem exists_orthogonalPolynomial_eq_X_sub_C_mul {k : ℕ} {t : ℝ}
    (ht : t ∈ gaussNodes μ k) :
    ∃ g : ℝ[X], g ≠ 0 ∧ g.degree < k ∧ orthogonalPolynomial μ k = (X - C t) * g := by
  have hπ := (mul_divByMonic_eq_iff_isRoot.mpr (mem_gaussNodes_iff_isRoot.mp ht)).symm
  set g := orthogonalPolynomial μ k /ₘ (X - C t)
  have hg : g ≠ 0 := fun h0 => (monic_orthogonalPolynomial μ k).ne_zero (by rw [hπ, h0, mul_zero])
  have hdeg := natDegree_mul (X_sub_C_ne_zero t) hg
  rw [← hπ, natDegree_orthogonalPolynomial, natDegree_X_sub_C] at hdeg
  exact ⟨g, hg, degree_le_natDegree.trans_lt (by exact_mod_cast (by omega : g.natDegree < k)), hπ⟩

/-- A one-signed factor at an endpoint: for $\mu$ supported in $[a, b]$, $t \in \{a, b\}$ and a
continuous $F \ge 0$ with $F(t) = 0$, if $\int F(x)(x - t)\,d\mu = 0$ then $F = 0$
$\mu$-almost everywhere. -/
private theorem ae_eq_zero_of_integral_mul_sub_eq_zero (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {t : ℝ} (ht : t = a ∨ t = b) {F : ℝ → ℝ} (hF : Continuous F) (hF0 : ∀ x, 0 ≤ F x)
    (hFt : F t = 0) (h : ∫ x, F x * (x - t) ∂μ = 0) :
    ∀ᵐ x ∂μ, F x = 0 := by
  have hint : Integrable (fun x => F x * (x - t)) μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμ]
    exact (by fun_prop : Continuous fun x => F x * (x - t)).continuousOn.integrableOn_Icc
  have hz : ∀ᵐ x ∂μ, F x * (x - t) = 0 := by
    rcases ht with rfl | rfl
    · refine (integral_eq_zero_iff_of_nonneg_ae ?_ hint).mp h
      filter_upwards [hμ] with x hx using mul_nonneg (hF0 x) (sub_nonneg.2 hx.1)
    · have hn : ∀ᵐ x ∂μ, 0 ≤ -(F x * (x - t)) := by
        filter_upwards [hμ] with x hx
        exact neg_nonneg.2 (mul_nonpos_of_nonneg_of_nonpos (hF0 x) (sub_nonpos.2 hx.2))
      filter_upwards [(integral_eq_zero_iff_of_nonneg_ae hn hint.neg).mp
        (by rw [integral_neg, h, neg_zero])] with x hx
      exact neg_eq_zero.mp hx
  filter_upwards [hz] with x hx
  rcases mul_eq_zero.mp hx with hx | hx
  · exact hx
  · rwa [sub_eq_zero.mp hx]

/-- The prescribed node is not a free node: if $\mu$, finite and supported in $[a, b]$, has a
Radau modified measure at $c \in \{a, b\}$ that is positive definite up to degree $k$, then $c$
is not a Gauss node of order $k$ of `radauMeasure μ c`.
Proof: M, about 40 lines. Let $\tilde\pi = \tilde\pi_k$ (`isFiniteMeasure_radauMeasure`,
`ae_mem_Icc_radauMeasure` for its API). If $\tilde\pi(c) = 0$ then $\tilde\pi = (x - c)r$ with
$\deg r = k - 1$, and orthogonality (`isOrthogonalPolynomial_orthogonalPolynomial`) with
`integral_radauMeasure` gives $0 = \int\lvert x - c\rvert(x - c)r^2\,d\mu$, whose integrand is
$\pm((x - c)r)^2$ of one sign on $[a, b]$ (as $c$ is an endpoint). So $(x - c)r = 0$ $\mu$-a.e.
(`integral_eq_zero_iff_of_nonneg_ae`), hence $\int r^2\,d\,\mathsf{radauMeasure}(\mu, c) =
\int\lvert x - c\rvert r^2\,d\mu = 0$, contradicting definiteness at $r \ne 0$ of degree
$k - 1 < k$. At $k = 0$ there are no Gauss nodes. -/
theorem IsMomentPosDef.notMem_gaussNodes_radauMeasure {k : ℕ}
    (h : IsMomentPosDef (radauMeasure μ c) k) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hc : c = a ∨ c = b) : c ∉ gaussNodes (radauMeasure μ c) k := by
  have := isFiniteMeasure_radauMeasure hμ c
  intro hmem
  obtain ⟨g, hg0, hgdeg, hπ⟩ := exists_orthogonalPolynomial_eq_X_sub_C_mul hmem
  have hO := isOrthogonalPolynomial_orthogonalPolynomial (ae_mem_Icc_radauMeasure hμ c) k g hgdeg
  rw [integral_radauMeasure, hπ] at hO
  refine (h g hg0 hgdeg).ne' ?_
  rw [integral_radauMeasure]
  refine integral_eq_zero_of_ae (ae_eq_zero_of_integral_mul_sub_eq_zero hμ hc
    (F := fun x => |x - c| * g.eval x ^ 2) (by fun_prop) (fun x => by positivity) (by simp) ?_)
  rw [← hO]
  congr 1 with x
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  ring

/-- The number of Radau nodes: if $\mu$, finite and supported in $[a, b]$, has a Radau modified
measure at $c \in \{a, b\}$ positive definite up to degree $k$, then the Radau rule has
$k + 1$ nodes.
Proof: S, about 6 lines. `radauNodes`, `Finset.card_insert_of_notMem` with
`IsMomentPosDef.notMem_gaussNodes_radauMeasure`, and `IsMomentPosDef.card_gaussNodes` for the
modified measure (`isFiniteMeasure_radauMeasure`, `ae_mem_Icc_radauMeasure`). -/
theorem IsMomentPosDef.card_radauNodes {k : ℕ} (h : IsMomentPosDef (radauMeasure μ c) k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) : (radauNodes μ c k).card = k + 1 := by
  have := isFiniteMeasure_radauMeasure hμ c
  unfold radauNodes
  rw [Finset.card_insert_of_notMem (h.notMem_gaussNodes_radauMeasure hμ hc),
    IsMomentPosDef.card_gaussNodes h (ae_mem_Icc_radauMeasure hμ c)]

omit [IsFiniteMeasure μ] in
/-- The sign of $x - c$: for $\mu$ supported in $[a, b]$ and $c \in \{a, b\}$ there is a constant
$s$ ($1$ at $c = a$, $-1$ at $c = b$) with
$\int(x - c)g(x)\,d\mu = s\int g\,d\,\mathsf{radauMeasure}(\mu, c)$ for every $g$. -/
private theorem exists_integral_sub_mul_eq_mul_integral_radauMeasure
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) :
    ∃ s : ℝ, ∀ g : ℝ → ℝ, ∫ x, (x - c) * g x ∂μ = s * ∫ x, g x ∂radauMeasure μ c := by
  simp only [integral_radauMeasure]
  rcases hc with rfl | rfl
  · refine ⟨1, fun g => ?_⟩
    rw [one_mul]
    refine integral_congr_ae ?_
    filter_upwards [hμ] with x hx
    rw [abs_of_nonneg (sub_nonneg.2 hx.1)]
  · refine ⟨-1, fun g => ?_⟩
    rw [neg_one_mul, ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hμ] with x hx
    rw [abs_of_nonpos (sub_nonpos.2 hx.2)]
    ring

/-- **The Radau nodal polynomial is orthogonal**: if $\mu$, finite and supported in $[a, b]$,
has a Radau modified measure at $c \in \{a, b\}$ positive definite up to degree $k$, then
$\prod_{x\in R}(x - y)$ over the Radau nodes $R$ is orthogonal in $L^2(\mu)$ to the polynomials
of degree less than $k$. [Gautschi2004, Theorem 3.2] (locator to check).
Proof: S, about 15 lines. `radauNodes`, `Lagrange.nodal_insert_eq_nodal` (with
`IsMomentPosDef.notMem_gaussNodes_radauMeasure`) gives $(X - c)\tilde\pi_k$
(`IsMomentPosDef.nodal_gaussNodes`); then $\int(x - c)\tilde\pi_k r\,d\mu =
\pm\int\tilde\pi_k r\,d\,\mathsf{radauMeasure}(\mu, c) = 0$ (`integral_radauMeasure`, the sign
of $x - c$ on $[a, b]$ a.e., `isOrthogonalPolynomial_orthogonalPolynomial` for the modified
measure). -/
theorem isOrthogonalPolynomial_nodal_radauNodes (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hc : c = a ∨ c = b) {k : ℕ} (h : IsMomentPosDef (radauMeasure μ c) k) :
    IsOrthogonalPolynomial μ k (Lagrange.nodal (radauNodes μ c k) id) := by
  have hν := ae_mem_Icc_radauMeasure hμ c
  have := isFiniteMeasure_radauMeasure hμ c
  have hnodal : Lagrange.nodal (radauNodes μ c k) id =
      (X - C c) * orthogonalPolynomial (radauMeasure μ c) k := by
    rw [radauNodes, Lagrange.nodal_insert_eq_nodal (h.notMem_gaussNodes_radauMeasure hμ hc),
      h.nodal_gaussNodes hν]
    rfl
  obtain ⟨s, hs⟩ := exists_integral_sub_mul_eq_mul_integral_radauMeasure hμ hc
  intro r hr
  simp only [hnodal, eval_mul, eval_sub, eval_X, eval_C, mul_assoc]
  rw [hs, isOrthogonalPolynomial_orthogonalPolynomial hν k r hr, mul_zero]

omit [IsFiniteMeasure μ] in
/-- Where the Radau density vanishes: if `radauMeasure μ c` is carried by its Gauss nodes of
order $k$, then $\mu$ is carried by the Radau nodes (the density vanishes only at $c$). -/
private theorem ae_mem_radauNodes_of_ae_mem_gaussNodes {k : ℕ}
    (hG : ∀ᵐ x ∂radauMeasure μ c, x ∈ gaussNodes (radauMeasure μ c) k) :
    ∀ᵐ x ∂μ, x ∈ radauNodes μ c k := by
  filter_upwards [(ae_withDensity_iff (by fun_prop)).mp hG] with x hx
  by_cases hxc : x = c
  · simp [radauNodes, hxc]
  · exact Finset.mem_insert_of_mem (hx (by simpa [sub_eq_zero] using hxc))

/-- The terminating case of the Radau rule: if the orthogonal polynomial $\tilde\pi_k$ of the
Radau modified measure of $\mu$ at $c$ has norm $0$ there, for $\mu$ finite and supported in
$[a, b]$, then the Radau rule is $\mu$ itself. Covers the case that the modified measure is not
positive definite up to degree $k$ (then $\tilde\pi_k$ has norm $0$ by `isMomentPosDef_succ_iff`
and `IsMomentPosDef.mono`).
Proof: M, about 25 lines. `ae_eval_eq_zero_of_integral_sq_eq_zero` for the modified measure:
`radauMeasure μ c` is carried by the zeros of $\tilde\pi_k$, the Gauss nodes $G$. Where
$x \ne c$ the density $\lvert x - c\rvert$ is positive, so $\mu$ is carried by $G \cup \{c\}$
(`withDensity_apply_eq_zero'` or `ae_withDensity_iff`, with `enorm_pos`); then
`interpolatoryQuadrature_eq_self_of_ae_mem`. -/
theorem radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ∫ x, (orthogonalPolynomial (radauMeasure μ c) k).eval x ^ 2 ∂radauMeasure μ c = 0) :
    radauQuadrature μ c k = μ := by
  have := isFiniteMeasure_radauMeasure hμ c
  refine interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_radauNodes_of_ae_mem_gaussNodes ?_)
  filter_upwards [ae_eval_eq_zero_of_integral_sq_eq_zero (ae_mem_Icc_radauMeasure hμ c) h]
    with x hx
  exact mem_gaussNodes_iff_isRoot.mpr hx

/-- The degenerate Radau case: if `radauMeasure μ c` is not positive definite up to degree $k$,
then $\mu$, finite and supported in $[a, b]$, is carried by the Radau nodes. -/
private theorem ae_mem_radauNodes_of_not_isMomentPosDef (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {k : ℕ} (h : ¬IsMomentPosDef (radauMeasure μ c) k) : ∀ᵐ x ∂μ, x ∈ radauNodes μ c k := by
  have := isFiniteMeasure_radauMeasure hμ c
  exact ae_mem_radauNodes_of_ae_mem_gaussNodes
    (ae_mem_gaussNodes_of_not_isMomentPosDef (ae_mem_Icc_radauMeasure hμ c) h)

/-- Exactness at a node: if $p$ is nonnegative on $[a, b]$, vanishes at the other nodes of $s$
and is positive at $x \in s$, and the nodal polynomial of $s$ is orthogonal of order $m$ with
$\deg p < \lvert s\rvert + m$, then $\int\ell_x\,d\mu \ge 0$. -/
private theorem integral_eval_basis_nonneg_of_exact (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {s : Finset ℝ} {m : ℕ} (hs : IsOrthogonalPolynomial μ m (Lagrange.nodal s id))
    {x : ℝ} (hx : x ∈ s) {p : ℝ[X]} (hdeg : p.natDegree < s.card + m)
    (hp : ∀ t ∈ Set.Icc a b, 0 ≤ p.eval t) (h0 : ∀ y ∈ s, y ≠ x → p.eval y = 0)
    (hpos : 0 < p.eval x) : 0 ≤ ∫ t, (Lagrange.basis s id x).eval t ∂μ := by
  have hex := hs.integral_eval_eq_sum_of_degree_lt_card_add hμ
    (degree_le_natDegree.trans_lt (by exact_mod_cast hdeg))
  rw [Finset.sum_eq_single x (fun y hy hne => by rw [h0 y hy hne, mul_zero])
    (fun hn => absurd hx hn)] at hex
  have hnn : 0 ≤ ∫ t, p.eval t ∂μ := integral_nonneg_of_ae (hμ.mono fun t ht => hp t ht)
  rw [hex] at hnn
  exact nonneg_of_mul_nonneg_left hnn hpos

/-- **The Radau weights are nonnegative**: for a finite measure $\mu$ supported in $[a, b]$,
$c \in \{a, b\}$ and every $k$, the interpolatory weight $\int\ell_x\,d\mu$ of every Radau
node $x$ is nonnegative, $\ell_x$ its Lagrange basis polynomial. [Gautschi2004, Theorem 3.2]
(locator to check); there positive, for $\mu$ with more than $k$ support points.
Proof: M, about 30 lines. By cases on definiteness of `radauMeasure μ c` up to degree $k$.
Definite: $\deg\ell_x^2 = 2k < 2k + 1 = \lvert R\rvert + k$, so
`IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add` (with
`isOrthogonalPolynomial_nodal_radauNodes`, `IsMomentPosDef.card_radauNodes`) and
`Lagrange.eval_basis_self`, `Lagrange.eval_basis_of_ne` give
$\int\ell_x^2\,d\mu = \int\ell_x\,d\mu$, as in
`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`; the left side is $\ge 0$
(`integral_nonneg`, `sq_nonneg`). Otherwise the rule is $\mu$
(`radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`), $\mu$ is carried by
the nodes, and the weight is the mass $\mu\{x\} \ge 0$ (`integral_eval_basis_of_ae_mem`). -/
theorem integral_eval_basis_radauNodes_nonneg (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hc : c = a ∨ c = b) (k : ℕ) {x : ℝ} (hx : x ∈ radauNodes μ c k) :
    0 ≤ ∫ t, (Lagrange.basis (radauNodes μ c k) id x).eval t ∂μ := by
  by_cases hp : IsMomentPosDef (radauMeasure μ c) k
  · -- $p = \ell_x^2$, of degree $2k < \lvert R\rvert + k$
    set ℓ := Lagrange.basis (radauNodes μ c k) id x
    have hℓ : ℓ.natDegree = (radauNodes μ c k).card - 1 :=
      Lagrange.natDegree_basis (Set.injOn_id _) hx
    have hℓx : ℓ.eval x = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hx
    refine integral_eval_basis_nonneg_of_exact hμ (isOrthogonalPolynomial_nodal_radauNodes hμ hc hp)
      hx (p := ℓ ^ 2) ?_ (fun t _ => by rw [eval_pow]; positivity) (fun y hy hyx => ?_)
      (by rw [eval_pow, hℓx]; norm_num)
    · have := natDegree_pow_le (p := ℓ) (n := 2)
      have := hp.card_radauNodes hμ hc
      omega
    · have hℓy : ℓ.eval y = 0 := Lagrange.eval_basis_of_ne (v := id) hyx.symm hy
      rw [eval_pow, hℓy, zero_pow two_ne_zero]
  · rw [integral_eval_basis_of_ae_mem (ae_mem_radauNodes_of_not_isMomentPosDef hμ hp) hx]
    exact measureReal_nonneg

/-- The Radau rule with the interpolatory weights: for a finite measure $\mu$ supported in
$[a, b]$, $c \in \{a, b\}$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu, c, k) =
\sum_{x\in R}\Bigl(\int\ell_x\,d\mu\Bigr)f(x)\,,$$
$R$ the Radau nodes and $\ell_x$ their Lagrange basis polynomials.
Proof: S, about 8 lines. The rule is a sum of Dirac masses with weights
$\max(\int\ell_x\,d\mu, 0)$ (`interpolatoryQuadrature`, `integral_finsetSum_measure`,
`integral_smul_measure`, `integral_dirac`), and the truncation is inert by
`integral_eval_basis_radauNodes_nonneg` (`ENNReal.toReal_ofReal`). -/
theorem integral_radauQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) (k : ℕ)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂radauQuadrature μ c k =
      ∑ x ∈ radauNodes μ c k, (∫ t, (Lagrange.basis (radauNodes μ c k) id x).eval t ∂μ) * f x := by
  unfold radauQuadrature interpolatoryQuadrature
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun x hx => ?_
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (integral_eval_basis_radauNodes_nonneg hμ hc k hx)]
  · intro x _
    exact (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- **Gauss–Radau quadrature**: for a finite measure $\mu$ supported in $[a, b]$,
$c \in \{a, b\}$ and every $k$, the Radau rule with prescribed node $c$ and $k$ free nodes
matches the first $2k + 1$ moments of $\mu$: it integrates every real polynomial of degree at
most $2k$ exactly. [Gautschi2004, Theorem 3.2]; [GolubMeurant2010, Ch. 6] (locators to check);
there for $\mu$ with more than $k$ support points; otherwise the rule is $\mu$ itself.
Proof: S, about 15 lines. By cases on definiteness of `radauMeasure μ c` up to degree $k$.
Definite: `integral_radauQuadrature` and
`IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add` with
`isOrthogonalPolynomial_nodal_radauNodes` and `IsMomentPosDef.card_radauNodes`
($\lvert R\rvert + k = 2k + 1$). Not definite: the norm of $\tilde\pi_k$ is $0$
(`isMomentPosDef_succ_iff`, `IsMomentPosDef.mono`) and
`radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`, `MatchesMoments.refl`.
Result: gauss-radau-quadrature -/
theorem matchesMoments_radauQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : MatchesMoments μ (radauQuadrature μ c k) (2 * k + 1) := by
  by_cases h : IsMomentPosDef (radauMeasure μ c) k
  · have hs := isOrthogonalPolynomial_nodal_radauNodes hμ hc h
    intro p hp
    rw [integral_radauQuadrature hμ hc k (fun x => p.eval x)]
    exact hs.integral_eval_eq_sum_of_degree_lt_card_add hμ
      (by rwa [h.card_radauNodes hμ hc, show k + 1 + k = 2 * k + 1 by ring])
  · rw [radauQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_radauNodes_of_not_isMomentPosDef hμ h)]
    exact MatchesMoments.refl _ _

/-- The Radau rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$, $c \in \{a, b\}$ and every $k$, almost every point of the Radau rule lies
in $[a, b]$.
Proof: S, about 12 lines. Definite case (`radauMeasure μ c` definite up to degree $k$): the
rule lives on its nodes (`ae_mem_interpolatoryQuadrature`) and the free nodes lie in $[a, b]$
(`IsMomentPosDef.gaussNodes_subset_Icc` for the modified measure). For $c$: if $k \ge 1$,
definiteness forces `radauMeasure μ c ≠ 0`, hence $\mu \ne 0$, hence $a \le b$ (from `hμ`) and
$c \in [a, b]$ by `hc`. Only at $k = 0$ (always definite) can $b < a$ occur; then $\mu = 0$
and the rule is $0$ (its one weight is $\int 1\,d\mu = 0$). Not definite: the rule is $\mu$
(`radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`). -/
theorem ae_mem_Icc_radauQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : ∀ᵐ x ∂radauQuadrature μ c k, x ∈ Set.Icc a b := by
  by_cases h0 : μ = 0
  · subst h0
    simp [radauQuadrature, interpolatoryQuadrature]
  have : (ae μ).NeBot := ae_neBot.mpr h0
  obtain ⟨x0, hx0⟩ := hμ.exists
  have hab : a ≤ b := hx0.1.trans hx0.2
  have hcI : c ∈ Set.Icc a b := by
    rcases hc with h | h <;> rw [h] <;> simp [hab]
  by_cases h : IsMomentPosDef (radauMeasure μ c) k
  · have := isFiniteMeasure_radauMeasure hμ c
    filter_upwards [ae_mem_interpolatoryQuadrature μ (radauNodes μ c k)] with x hx
    simp only [radauNodes, Finset.mem_insert] at hx
    rcases hx with rfl | hx
    · exact hcI
    · exact h.gaussNodes_subset_Icc (ae_mem_Icc_radauMeasure hμ c) (Finset.mem_coe.mpr hx)
  · rw [radauQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_radauNodes_of_not_isMomentPosDef hμ h)]
    exact hμ

/-- The mass of the Radau rule: for a finite measure $\mu$ supported in $[a, b]$,
$c \in \{a, b\}$ and every $k$, the Radau rule has mass $\mu(\mathbb{R})$.
Proof: S, about 3 lines. `MatchesMoments.measureReal_univ_eq` on
`matchesMoments_radauQuadrature` ($2k + 1 > 0$). -/
theorem radauQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : (radauQuadrature μ c k).real Set.univ = μ.real Set.univ :=
  ((matchesMoments_radauQuadrature hμ hc k).measureReal_univ_eq (by omega)).symm

/-- **Uniqueness of the Radau rule**: if a finite measure $\nu$ carried by $c$ and at most $k$
further points matches the first $2k + 1$ moments of a finite measure $\mu$ supported in
$[a, b]$, $c \in \{a, b\}$, then $\nu$ is the Radau rule of $\mu$ with prescribed node $c$ and
$k$ free nodes. [Gautschi2004, §3.1.1] (locator to check); there among rules with positive
weights.
Proof: M, about 20 lines. As `MatchesMoments.eq_gaussQuadrature`: both $\nu$ and the Radau rule
are carried by $T = \{c\} \cup s \cup G$ (`ae_mem_interpolatoryQuadrature`, `radauNodes`),
$\lvert T\rvert \le 2k + 1$ (`Finset.card_insert_le`, `Finset.card_union_le`,
`card_gaussNodes_le`), and they match $2k + 1$ moments
(`MatchesMoments.symm`, `MatchesMoments.trans`, `matchesMoments_radauQuadrature`); then
`MatchesMoments.eq_of_ae_mem`.
Result: gauss-radau-quadrature-uniqueness -/
theorem MatchesMoments.eq_radauQuadrature [IsFiniteMeasure ν] {k : ℕ}
    (h : MatchesMoments μ ν (2 * k + 1)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    {s : Finset ℝ} (hν : ∀ᵐ x ∂ν, x ∈ insert c s) (hs : s.card ≤ k) :
    ν = radauQuadrature μ c k := by
  have hM : MatchesMoments ν (radauQuadrature μ c k) (2 * k + 1) :=
    h.symm.trans (matchesMoments_radauQuadrature hμ hc k)
  have hνT : ∀ᵐ x ∂ν, x ∈ insert c (s ∪ gaussNodes (radauMeasure μ c) k) :=
    hν.mono fun x hx => Finset.insert_subset_insert c Finset.subset_union_left hx
  have hρT : ∀ᵐ x ∂radauQuadrature μ c k, x ∈ insert c (s ∪ gaussNodes (radauMeasure μ c) k) :=
    (ae_mem_interpolatoryQuadrature μ (radauNodes μ c k)).mono fun x hx =>
      Finset.insert_subset_insert c Finset.subset_union_right hx
  have hcard : (insert c (s ∪ gaussNodes (radauMeasure μ c) k)).card ≤ 2 * k + 1 :=
    (Finset.card_insert_le _ _).trans (by
      have := (Finset.card_union_le s _).trans (Nat.add_le_add_left
        (card_gaussNodes_le (radauMeasure μ c) k) s.card)
      omega)
  exact MatchesMoments.eq_of_ae_mem (hM.mono hcard) hνT hρT

/-! ### The Radau remainder and bounds -/

/-- The last step of the Radau and Lobatto remainders: for $\mu$, finite and supported in
$[a, b]$, if $f(x) - H(x) = \frac{f^{(n)}(\xi_x)}{n!}W(x)$ for every $x \in [a, b]$ and some
$\xi_x \in (a, b)$, with $W$ integrable and of one sign, then one $\xi$ serves the integral. -/
private theorem exists_integral_sub_integral_eval_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) {n : ℕ} {f W : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ n f (Set.Ioo a b)) (hW : Integrable W μ)
    (hWs : (∀ᵐ x ∂μ, 0 ≤ W x) ∨ ∀ᵐ x ∂μ, W x ≤ 0) {H : ℝ[X]}
    (hpt : ∀ x ∈ Set.Icc a b, ∃ ξ ∈ Set.Ioo a b,
      f x - H.eval x = iteratedDeriv n f ξ / n.factorial * W x) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, H.eval x ∂μ =
      iteratedDeriv n f ξ / n.factorial * ∫ x, W x ∂μ := by
  have hfint : Integrable f μ := by
    rw [← Measure.restrict_eq_self_of_ae_mem hμ]
    exact hf.integrableOn_Icc
  have hD : ContinuousOn (fun ξ => iteratedDeriv n f ξ / n.factorial) (Set.Ioo a b) :=
    ((hf'.continuousOn_iteratedDerivWithin le_rfl (uniqueDiffOn_Ioo a b)).congr
      fun x hx => (iteratedDerivWithin_of_isOpen isOpen_Ioo hx).symm).div_const _
  have hint := hfint.sub (integrable_eval_of_ae_mem_Icc hμ H)
  rw [← integral_sub hfint (integrable_eval_of_ae_mem_Icc hμ H)]
  rcases hWs with hWs | hWs
  · exact exists_integral_eq_mul_integral_of_ae_nonneg hint hW hWs (isConnected_Ioo hab) hD
      (hμ.mono hpt)
  · exact exists_integral_eq_mul_integral_of_ae_nonpos hint hW hWs (isConnected_Ioo hab) hD
      (hμ.mono hpt)

/-- **The Gauss–Radau remainder**: for a finite measure $\mu$ supported in $[a, b]$, $a < b$,
$c \in \{a, b\}$, every $k$, and $f$ continuous on $[a, b]$ and $C^{2k+1}$ on $(a, b)$, there
is $\xi \in (a, b)$ with
$$\int f\,d\mu - \int f\,d\,\mathsf{radauQuadrature}(\mu, c, k) =
\frac{f^{(2k+1)}(\xi)}{(2k+1)!}\int(x - c)\,\tilde\pi_k(x)^2\,d\mu(x)\,,$$
$\tilde\pi_k$ the monic orthogonal polynomial of degree $k$ of `radauMeasure μ c`.
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: L, about 80 lines; the prototype proves the nondegenerate case
(`NLAlib.exists_integral_sub_endpoint_quadrature_eq_iteratedDeriv_mul`,
`NLAlib/Polynomial/Quadrature/EndpointMeasureRemainder.lean`, with
`exists_sub_eval_hermiteEndpointInterpolate_eq`). If $\tilde\pi_k$ has norm $0$ in
`radauMeasure μ c`: the rule is $\mu$
(`radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`) and
$\int(x - c)\tilde\pi_k^2\,d\mu = \pm\int\tilde\pi_k^2\,d\,\mathsf{radauMeasure}(\mu, c) = 0$
(`integral_radauMeasure`, sign of $x - c$ a.e.); take $\xi = (a + b)/2$. Otherwise the modified
measure is definite up to degree $k + 1$, so its Gauss nodes $G$ are $k$ points of $(a, b)$
(`IsMomentPosDef.gaussNodes_subset_Ioo`, `IsMomentPosDef.card_gaussNodes`). With
$m = \{c\} + G + G$: $H$ of degree less than $2k + 1$ matching $f$ on $m$
(`exists_degree_lt_forall_iterate_derivative_eval_eq`), the rule integrates $H$ exactly
(`matchesMoments_radauQuadrature`) and $H = f$ on the nodes (`integral_radauQuadrature`), the
pointwise remainder is `exists_sub_eval_eq_iteratedDeriv_mul` with
$\omega_m = (x - c)\tilde\pi_k^2$ (`IsMomentPosDef.nodal_gaussNodes`), and
`exists_integral_eq_mul_integral_of_ae_nonneg` (at $c = a$) or
`exists_integral_eq_mul_integral_of_ae_nonpos` (at $c = b$) gives one $\xi$.
Result: gauss-radau-remainder -/
theorem exists_integral_sub_integral_radauQuadrature_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) (hc : c = a ∨ c = b) (k : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂radauQuadrature μ c k =
      iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial *
        ∫ x, (x - c) * (orthogonalPolynomial (radauMeasure μ c) k).eval x ^ 2 ∂μ := by
  set μc := radauMeasure μ c
  have := isFiniteMeasure_radauMeasure hμ c
  have hμc : ∀ᵐ x ∂μc, x ∈ Set.Icc a b := ae_mem_Icc_radauMeasure hμ c
  set π := orthogonalPolynomial μc k
  have hπint : Integrable (fun x => (x - c) * π.eval x ^ 2) μ :=
    (integrable_eval_of_ae_mem_Icc hμ ((X - C c) * π ^ 2)).congr (ae_of_all μ fun x => by simp)
  rcases (integral_nonneg fun x => sq_nonneg (π.eval x) : 0 ≤ ∫ x, π.eval x ^ 2 ∂μc).eq_or_lt
    with h0 | hpos
  · obtain ⟨s, hs⟩ := exists_integral_sub_mul_eq_mul_integral_radauMeasure hμ hc
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero hμ h0.symm, sub_self,
      hs, ← h0, mul_zero, mul_zero]
  · have hpd : IsMomentPosDef μc (k + 1) := (isMomentPosDef_succ_iff hμc k).mpr hpos
    set G := gaussNodes μc k
    have hGI : (G : Set ℝ) ⊆ Set.Ioo a b := hpd.gaussNodes_subset_Ioo hμc
    have hcI : c ∈ Set.Icc a b := by rcases hc with rfl | rfl <;> constructor <;> linarith
    have hcG : c ∉ G := fun h => by
      rcases hc with rfl | rfl
      · exact lt_irrefl _ (hGI h).1
      · exact lt_irrefl _ (hGI h).2
    set m : Multiset ℝ := c ::ₘ (G.val + G.val)
    have hcard : m.card = 2 * k + 1 := by
      have hGk : G.card = k := (hpd.mono k.le_succ).card_gaussNodes hμc
      simp only [m, Multiset.card_cons, Multiset.card_add, Finset.card_val, hGk]
      ring
    have hmem : ∀ y ∈ m, y = c ∨ y ∈ G := fun y hy => by simpa [m] using hy
    obtain ⟨H, hHdeg, hjet⟩ :=
      exists_degree_lt_forall_iterate_derivative_eval_eq m (fun y j => iteratedDeriv j f y)
    rw [hcard] at hHdeg
    have hexact : ∫ x, f x ∂radauQuadrature μ c k = ∫ x, H.eval x ∂μ := by
      rw [matchesMoments_radauQuadrature hμ hc k H hHdeg, integral_radauQuadrature hμ hc,
        integral_radauQuadrature hμ hc]
      refine Finset.sum_congr rfl fun y hy => ?_
      have hy' : y ∈ m := by simpa [m, radauNodes] using hy
      rw [show f y = H.eval y by simpa using (hjet y hy' 0 (Multiset.count_pos.2 hy')).symm]
    have hprod : (m.map fun y => X - C y).prod = (X - C c) * π ^ 2 := by
      have hnod : Lagrange.nodal G id = π := (hpd.mono k.le_succ).nodal_gaussNodes hμc
      rw [← hnod]
      simp only [m, Lagrange.nodal, Multiset.map_cons, Multiset.prod_cons, Multiset.map_add,
        Multiset.prod_add, Finset.prod_eq_multiset_prod, id, sq]
    rw [hexact]
    refine exists_integral_sub_integral_eval_eq hμ hab hf hf' hπint ?_ fun x hx => ?_
    · rcases hc with rfl | rfl
      · exact .inl (hμ.mono fun x hx => mul_nonneg (sub_nonneg.2 hx.1) (sq_nonneg _))
      · exact .inr (hμ.mono fun x hx =>
          mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 hx.2) (sq_nonneg _))
    obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul hab (Multiset.cons_ne_zero)
      (fun y hy => (hmem y hy).elim (fun h => h ▸ hcI) fun h => Set.Ioo_subset_Icc_self (hGI h))
      (fun y hy h => by
        rcases hmem y hy with rfl | hyG
        · simp [Multiset.count_eq_zero.mpr (show y ∉ G.val from hcG)] at h
        · exact hGI hyG) hf (hcard ▸ hf') (hcard ▸ hHdeg) hjet hx
    refine ⟨ξ, hξ, ?_⟩
    rw [h, hprod, hcard]
    simp

/-- **The left Radau rule is a lower bound** for $f$ with nonnegative derivative of order
$2k + 1$: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$
continuous on $[a, b]$, $C^{2k+1}$ on $(a, b)$ with $f^{(2k+1)} \ge 0$ there,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu, a, k) \le \int f\,d\mu\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 10 lines. `exists_integral_sub_integral_radauQuadrature_eq` at $c = a$; the
weight $(x - a)\tilde\pi_k^2 \ge 0$ a.e. (`hμ`, `integral_nonneg_of_ae`), so the right side is
nonnegative. -/
theorem integral_radauQuadrature_le_integral_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k + 1) f x) :
    ∫ x, f x ∂radauQuadrature μ a k ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, h⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inl rfl) k hf hf'
  have hW : 0 ≤ ∫ x, (x - a) * (orthogonalPolynomial (radauMeasure μ a) k).eval x ^ 2 ∂μ :=
    integral_nonneg_of_ae (by
      filter_upwards [hμ] with x hx
      exact mul_nonneg (by linarith [hx.1]) (sq_nonneg _))
  have hR : 0 ≤ iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial *
      ∫ x, (x - a) * (orthogonalPolynomial (radauMeasure μ a) k).eval x ^ 2 ∂μ :=
    mul_nonneg (div_nonneg (hD ξ hξ) (Nat.cast_nonneg _)) hW
  linarith

/-- **The left Radau rule is an upper bound** for $f$ with nonpositive derivative of order
$2k + 1$ (such as $x \mapsto x^{-1}$ on $[a, b]$, $a > 0$): for a finite measure $\mu$
supported in $[a, b]$, $a < b$, every $k$, and $f$ continuous on $[a, b]$, $C^{2k+1}$ on
$(a, b)$ with $f^{(2k+1)} \le 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{radauQuadrature}(\mu, a, k)\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 10 lines. As `integral_radauQuadrature_le_integral_of_iteratedDeriv_nonneg`,
with `mul_nonpos_of_nonpos_of_nonneg`. -/
theorem integral_le_integral_radauQuadrature_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k + 1) f x ≤ 0) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂radauQuadrature μ a k := by
  obtain ⟨ξ, hξ, heq⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inl rfl) k hf hf'
  have hW : 0 ≤ ∫ x, (x - a) * (orthogonalPolynomial (radauMeasure μ a) k).eval x ^ 2 ∂μ :=
    integral_nonneg_of_ae (hμ.mono fun x hx => mul_nonneg (sub_nonneg.mpr hx.1) (sq_nonneg _))
  have hq : iteratedDeriv (2 * k + 1) f ξ / (2 * k + 1).factorial ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hD ξ hξ) (Nat.cast_nonneg _)
  have hprod := mul_nonpos_of_nonpos_of_nonneg hq hW
  linarith

/-- **The right Radau rule is an upper bound** for $f$ with nonnegative derivative of order
$2k + 1$: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$
continuous on $[a, b]$, $C^{2k+1}$ on $(a, b)$ with $f^{(2k+1)} \ge 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{radauQuadrature}(\mu, b, k)\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 10 lines. `exists_integral_sub_integral_radauQuadrature_eq` at $c = b$; the
weight $(x - b)\tilde\pi_k^2 \le 0$ a.e. (`integral_nonpos_of_ae`). -/
theorem integral_le_integral_radauQuadrature_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k + 1) f x) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂radauQuadrature μ b k := by
  obtain ⟨ξ, hξ, h⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inr rfl) k hf hf'
  have hW : ∫ x, (x - b) * (orthogonalPolynomial (radauMeasure μ b) k).eval x ^ 2 ∂μ ≤ 0 :=
    integral_nonpos_of_ae (hμ.mono fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _))
  linarith [mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 1).factorial)) hW]

/-- **The right Radau rule is a lower bound** for $f$ with nonpositive derivative of order
$2k + 1$ (such as $x \mapsto x^{-1}$ on $[a, b]$, $a > 0$): for a finite measure $\mu$
supported in $[a, b]$, $a < b$, every $k$, and $f$ continuous on $[a, b]$, $C^{2k+1}$ on
$(a, b)$ with $f^{(2k+1)} \le 0$ there,
$$\int f\,d\,\mathsf{radauQuadrature}(\mu, b, k) \le \int f\,d\mu\,.$$
[Gautschi2004, Theorem 3.3]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 10 lines. As `integral_le_integral_radauQuadrature_of_iteratedDeriv_nonneg`,
with `mul_nonneg_of_nonpos_of_nonpos`. -/
theorem integral_radauQuadrature_le_integral_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 1 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k + 1) f x ≤ 0) :
    ∫ x, f x ∂radauQuadrature μ b k ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, h⟩ :=
    exists_integral_sub_integral_radauQuadrature_eq hμ hab (Or.inr rfl) k hf hf'
  have hW : ∫ x, (x - b) * (orthogonalPolynomial (radauMeasure μ b) k).eval x ^ 2 ∂μ ≤ 0 :=
    integral_nonpos_of_ae (hμ.mono fun x hx =>
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx.2) (sq_nonneg _))
  linarith [mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 1).factorial)) hW]

/-! ### The Lobatto rule -/

/-- Integrals against the Lobatto modified measure: for every measure $\mu$ on $\mathbb{R}$,
all $a, b$ and every $g : \mathbb{R} \to \mathbb{R}$,
$\int g\,d\,\mathsf{lobattoMeasure}(\mu, a, b) = \int\lvert(x - a)(x - b)\rvert\,g(x)\,d\mu(x)$.
Proof: S, about 8 lines. As `integral_radauMeasure`. -/
theorem integral_lobattoMeasure (μ : Measure ℝ) (a b : ℝ) (g : ℝ → ℝ) :
    ∫ x, g x ∂lobattoMeasure μ a b = ∫ x, |(x - a) * (x - b)| * g x ∂μ := by
  unfold lobattoMeasure
  rw [show (fun x : ℝ => ‖(x - a) * (x - b)‖ₑ) =
      fun x => ((‖(x - a) * (x - b)‖₊ : NNReal) : ENNReal) from funext fun x => enorm_eq_nnnorm _,
    integral_withDensity_eq_integral_smul (f := fun x : ℝ => ‖(x - a) * (x - b)‖₊) (by fun_prop)]
  simp [NNReal.smul_def, Real.norm_eq_abs, abs_mul, smul_eq_mul, mul_comm]

/-- The Lobatto modified measure of a finite measure supported in $[a, b]$ is finite.
Proof: S, about 12 lines. As `isFiniteMeasure_radauMeasure`, with the bound
$(b - a)^2$ on $[a, b]$. -/
theorem isFiniteMeasure_lobattoMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    IsFiniteMeasure (lobattoMeasure μ a b) :=
  isFiniteMeasure_withDensity ((integrable_eval_of_ae_mem_Icc hμ ((X - C a) * (X - C b))).congr
    (ae_of_all μ fun x => by simp) : Integrable (fun x => (x - a) * (x - b)) μ).2.ne

/-- The Lobatto modified measure lives where $\mu$ does: for $\mu$ supported in $[a, b]$, almost
every point of `lobattoMeasure μ a b` lies in $[a, b]$.
Proof: S, about 4 lines. As `ae_mem_Icc_radauMeasure`. -/
theorem ae_mem_Icc_lobattoMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    ∀ᵐ x ∂lobattoMeasure μ a b, x ∈ Set.Icc a b :=
  (withDensity_absolutelyContinuous μ _).ae_le hμ

/-- The endpoints are not free Lobatto nodes: if $\mu$, finite and supported in $[a, b]$, has a
Lobatto modified measure positive definite up to degree $k$, then neither endpoint
$t \in \{a, b\}$ is a Gauss node of order $k$ of `lobattoMeasure μ a b`.
Proof: M, about 40 lines. As `IsMomentPosDef.notMem_gaussNodes_radauMeasure`: if
$\hat\pi_k(t) = 0$, $\hat\pi_k = (x - t)r$, orthogonality to $r$ gives
$\int\lvert(x - a)(x - b)\rvert(x - t)r^2\,d\mu = 0$ with an integrand of one sign on
$[a, b]$, so $\lvert(x - a)(x - b)\rvert^{1/2}(x - t)r$ vanishes a.e. and
$\int r^2\,d\,\mathsf{lobattoMeasure}(\mu, a, b)$ vanishes (the factor $x - t$ only vanishes at
$t$, where the density does too), contradicting definiteness. -/
theorem IsMomentPosDef.notMem_gaussNodes_lobattoMeasure {k : ℕ}
    (h : IsMomentPosDef (lobattoMeasure μ a b) k) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {t : ℝ}
    (ht : t = a ∨ t = b) : t ∉ gaussNodes (lobattoMeasure μ a b) k := by
  have := isFiniteMeasure_lobattoMeasure hμ
  intro hmem
  obtain ⟨r, hr0, hrdeg, hπ⟩ := exists_orthogonalPolynomial_eq_X_sub_C_mul hmem
  have hO := isOrthogonalPolynomial_orthogonalPolynomial (ae_mem_Icc_lobattoMeasure hμ) k r hrdeg
  rw [integral_lobattoMeasure, hπ] at hO
  refine (h r hr0 hrdeg).ne' ?_
  rw [integral_lobattoMeasure]
  refine integral_eq_zero_of_ae (ae_eq_zero_of_integral_mul_sub_eq_zero hμ ht
    (F := fun x => |(x - a) * (x - b)| * r.eval x ^ 2) (by fun_prop) (fun x => by positivity)
    (by rcases ht with rfl | rfl <;> simp) ?_)
  rw [← hO]
  congr 1 with x
  simp only [eval_mul, eval_sub, eval_X, eval_C]
  ring

/-- The endpoints are not free Lobatto nodes, in the form the node count needs. -/
private theorem IsMomentPosDef.notMem_insert_gaussNodes_lobattoMeasure {k : ℕ}
    (h : IsMomentPosDef (lobattoMeasure μ a b) k) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) :
    a ∉ insert b (gaussNodes (lobattoMeasure μ a b) k) ∧ b ∉ gaussNodes (lobattoMeasure μ a b) k :=
  ⟨Finset.mem_insert.not.2 (not_or.2 ⟨hab.ne, h.notMem_gaussNodes_lobattoMeasure hμ (.inl rfl)⟩),
    h.notMem_gaussNodes_lobattoMeasure hμ (.inr rfl)⟩

/-- The number of Lobatto nodes: if $\mu$, finite and supported in $[a, b]$, $a < b$, has a
Lobatto modified measure positive definite up to degree $k$, the Lobatto rule has $k + 2$
nodes.
Proof: S, about 8 lines. `lobattoNodes`, `Finset.card_insert_of_notMem` twice
(`IsMomentPosDef.notMem_gaussNodes_lobattoMeasure`, `hab.ne`), `IsMomentPosDef.card_gaussNodes`
for the modified measure. -/
theorem IsMomentPosDef.card_lobattoNodes {k : ℕ} (h : IsMomentPosDef (lobattoMeasure μ a b) k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) : (lobattoNodes μ a b k).card = k + 2 := by
  have := isFiniteMeasure_lobattoMeasure hμ
  obtain ⟨ha, hb⟩ := h.notMem_insert_gaussNodes_lobattoMeasure hμ hab
  rw [lobattoNodes, Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb,
    h.card_gaussNodes (ae_mem_Icc_lobattoMeasure hμ)]

omit [IsFiniteMeasure μ] in
/-- The sign of $(x - a)(x - b)$: for $\mu$ supported in $[a, b]$ and every $g$,
$\int(x - a)(x - b)g(x)\,d\mu = -\int g\,d\,\mathsf{lobattoMeasure}(\mu, a, b)$. -/
private theorem integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (g : ℝ → ℝ) :
    ∫ x, (x - a) * (x - b) * g x ∂μ = -∫ x, g x ∂lobattoMeasure μ a b := by
  rw [integral_lobattoMeasure, ← integral_neg]
  refine integral_congr_ae ?_
  filter_upwards [hμ] with x hx
  rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hx.1) (sub_nonpos.2 hx.2))]
  ring

/-- **The Lobatto nodal polynomial is orthogonal**: if $\mu$, finite and supported in $[a, b]$,
$a < b$, has a Lobatto modified measure positive definite up to degree $k$, then the nodal
polynomial of the Lobatto nodes is orthogonal in $L^2(\mu)$ to the polynomials of degree less
than $k$. [Gautschi2004, Theorem 3.6] (locator to check).
Proof: S, about 15 lines. As `isOrthogonalPolynomial_nodal_radauNodes`: the nodal polynomial is
$(X - a)(X - b)\hat\pi_k$ and $(x - a)(x - b) = -\lvert(x - a)(x - b)\rvert$ on $[a, b]$
(`integral_lobattoMeasure`). -/
theorem isOrthogonalPolynomial_nodal_lobattoNodes (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b)
    {k : ℕ} (h : IsMomentPosDef (lobattoMeasure μ a b) k) :
    IsOrthogonalPolynomial μ k (Lagrange.nodal (lobattoNodes μ a b k) id) := by
  have := isFiniteMeasure_lobattoMeasure hμ
  have hν := ae_mem_Icc_lobattoMeasure hμ
  obtain ⟨ha, hb⟩ := h.notMem_insert_gaussNodes_lobattoMeasure hμ hab
  have hnodal : Lagrange.nodal (lobattoNodes μ a b k) id =
      (X - C a) * ((X - C b) * orthogonalPolynomial (lobattoMeasure μ a b) k) := by
    rw [lobattoNodes, Lagrange.nodal_insert_eq_nodal ha, Lagrange.nodal_insert_eq_nodal hb,
      h.nodal_gaussNodes hν]
    rfl
  intro r hr
  have hs := integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ
    fun x => (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x * r.eval x
  simp only [mul_assoc] at hs
  simp only [hnodal, eval_mul, eval_sub, eval_X, eval_C, mul_assoc]
  rw [hs, isOrthogonalPolynomial_orthogonalPolynomial hν k r hr, neg_zero]

omit [IsFiniteMeasure μ] in
/-- Where the Lobatto density vanishes: if `lobattoMeasure μ a b` is carried by its Gauss nodes
of order $k$, then $\mu$ is carried by the Lobatto nodes (the density vanishes only at $a$
and $b$). -/
private theorem ae_mem_lobattoNodes_of_ae_mem_gaussNodes {k : ℕ}
    (hG : ∀ᵐ x ∂lobattoMeasure μ a b, x ∈ gaussNodes (lobattoMeasure μ a b) k) :
    ∀ᵐ x ∂μ, x ∈ lobattoNodes μ a b k := by
  filter_upwards [(ae_withDensity_iff (by fun_prop)).mp hG] with x hx
  by_cases hxab : x = a ∨ x = b
  · rcases hxab with rfl | rfl <;> simp [lobattoNodes]
  · have hne : ‖(x - a) * (x - b)‖ₑ ≠ 0 := by
      simpa [sub_eq_zero] using hxab
    simp [lobattoNodes, hx hne]

/-- The terminating case of the Lobatto rule: if the orthogonal polynomial $\hat\pi_k$ of the
Lobatto modified measure has norm $0$ there, for $\mu$ finite and supported in $[a, b]$, then
the Lobatto rule is $\mu$ itself.
Proof: M, about 25 lines. As
`radauQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`: $\mu$ is carried by the
zeros of $\hat\pi_k$ and $\{a, b\}$. -/
theorem lobattoQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h : ∫ x, (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂lobattoMeasure μ a b =
      0) :
    lobattoQuadrature μ a b k = μ := by
  have := isFiniteMeasure_lobattoMeasure hμ
  refine interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_lobattoNodes_of_ae_mem_gaussNodes ?_)
  filter_upwards [ae_eval_eq_zero_of_integral_sq_eq_zero (ae_mem_Icc_lobattoMeasure hμ) h]
    with x hx
  exact mem_gaussNodes_iff_isRoot.mpr hx

/-- The degenerate Lobatto case: if `lobattoMeasure μ a b` is not positive definite up to degree
$k$, then $\mu$, finite and supported in $[a, b]$, is carried by the Lobatto nodes. -/
private theorem ae_mem_lobattoNodes_of_not_isMomentPosDef (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    {k : ℕ} (h : ¬IsMomentPosDef (lobattoMeasure μ a b) k) :
    ∀ᵐ x ∂μ, x ∈ lobattoNodes μ a b k := by
  have := isFiniteMeasure_lobattoMeasure hμ
  exact ae_mem_lobattoNodes_of_ae_mem_gaussNodes
    (ae_mem_gaussNodes_of_not_isMomentPosDef (ae_mem_Icc_lobattoMeasure hμ) h)

/-- The degree of $\prod_{y\in s}(X - y)^2$ is at most $2\lvert s\rvert$. -/
private theorem natDegree_prod_X_sub_C_sq_le (s : Finset ℝ) :
    (∏ y ∈ s, (X - C y) ^ 2).natDegree ≤ 2 * s.card := by
  refine (natDegree_prod_le _ _).trans ?_
  calc _ ≤ ∑ _y ∈ s, 2 := Finset.sum_le_sum fun y _ => natDegree_pow_le.trans (by simp)
    _ = 2 * s.card := by simp [mul_comm]

/-- A Lobatto weight from a factor: if $\mu$, finite and supported in $[a, b]$, has a Lobatto
modified measure definite up to degree $k$, $x$ is a Lobatto node, and $q \ge 0$ on $[a, b]$ is
positive at $x$, vanishes at the endpoints other than $x$ and has
$\deg q + 2\lvert G \setminus \{x\}\rvert < 2k + 2$ ($G$ the free nodes), then the weight of $x$
is nonnegative: apply `integral_eval_basis_nonneg_of_exact` to
$q\prod_{y\in G\setminus\{x\}}(X - y)^2$. -/
private theorem integral_eval_basis_lobattoNodes_nonneg_of_factor
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {k : ℕ}
    (h : IsMomentPosDef (lobattoMeasure μ a b) k) {x : ℝ} (hx : x ∈ lobattoNodes μ a b k)
    {q : ℝ[X]}
    (hdeg : q.natDegree + 2 * ((gaussNodes (lobattoMeasure μ a b) k).erase x).card < 2 * k + 2)
    (hq : ∀ t ∈ Set.Icc a b, 0 ≤ q.eval t) (hqx : 0 < q.eval x) (hqa : x ≠ a → q.eval a = 0)
    (hqb : x ≠ b → q.eval b = 0) :
    0 ≤ ∫ t, (Lagrange.basis (lobattoNodes μ a b k) id x).eval t ∂μ := by
  set G := gaussNodes (lobattoMeasure μ a b) k
  refine integral_eval_basis_nonneg_of_exact hμ (isOrthogonalPolynomial_nodal_lobattoNodes hμ hab h)
    hx (p := q * ∏ y ∈ G.erase x, (X - C y) ^ 2) ?_ (fun t ht => ?_) (fun y hy hyx => ?_) ?_
  · have := natDegree_mul_le (p := q) (q := ∏ y ∈ G.erase x, (X - C y) ^ 2)
    have := natDegree_prod_X_sub_C_sq_le (G.erase x)
    rw [h.card_lobattoNodes hμ hab]
    omega
  · rw [eval_mul, eval_prod]
    exact mul_nonneg (hq t ht) (Finset.prod_nonneg fun y _ => by rw [eval_pow]; positivity)
  · rw [eval_mul]
    simp only [lobattoNodes, Finset.mem_insert] at hy
    rcases hy with rfl | rfl | hy
    · rw [hqa hyx.symm, zero_mul]
    · rw [hqb hyx.symm, zero_mul]
    · rw [eval_prod, Finset.prod_eq_zero (Finset.mem_erase.2 ⟨hyx, hy⟩) (by simp), mul_zero]
  · rw [eval_mul, eval_prod]
    refine mul_pos hqx (Finset.prod_pos fun y hy => ?_)
    have hxy : x - y ≠ 0 := sub_ne_zero.2 (Finset.ne_of_mem_erase hy).symm
    simp only [eval_pow, eval_sub, eval_X, eval_C]
    positivity

/-- **The Lobatto weights are nonnegative**: for a finite measure $\mu$ supported in $[a, b]$,
$a < b$, and every $k$, the interpolatory weight $\int\ell_x\,d\mu$ of every Lobatto node $x$ is
nonnegative, $\ell_x$ its Lagrange basis polynomial. [Gautschi2004, Theorem 3.6] (locator to
check); there positive, for $\mu$ with more than $k$ interior support points.
Proof: M, about 45 lines; the prototype proves the positivity
(`NLAlib.twoEndpoint_quadrature_weight_pos_of_exact`,
`NLAlib/Polynomial/Quadrature/EndpointWeightPositivity.lean`). As
`integral_eval_basis_radauNodes_nonneg`, but $\ell_x^2$ has degree $2k + 2$, one too many: in
the definite case apply exactness
(`IsOrthogonalPolynomial.integral_eval_eq_sum_of_degree_lt_card_add`, degree less than
$2k + 2$) to $p = (x - a)(b - x)\prod_{y\in G\setminus\{x\}}(x - y)^2$ for a free node $x$ and
to $p = (b - x)\prod_{y\in G}(x - y)^2$ (resp. $(x - a)\prod_{y \in G}(x - y)^2$) for $x = a$
(resp. $b$): $p \ge 0$ on $[a, b]$, vanishes at every other node and $p(x) > 0$, so
$\int\ell_x\,d\mu = \int p\,d\mu/p(x) \ge 0$. Otherwise the rule is $\mu$
(`lobattoQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`), $\mu$ is carried by
the nodes and the weight is the mass $\mu\{x\} \ge 0$ (`integral_eval_basis_of_ae_mem`). -/
theorem integral_eval_basis_lobattoNodes_nonneg (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b)
    (k : ℕ) {x : ℝ} (hx : x ∈ lobattoNodes μ a b k) :
    0 ≤ ∫ t, (Lagrange.basis (lobattoNodes μ a b k) id x).eval t ∂μ := by
  by_cases h : IsMomentPosDef (lobattoMeasure μ a b) k
  · have := isFiniteMeasure_lobattoMeasure hμ
    set G := gaussNodes (lobattoMeasure μ a b) k with hG
    have hGk : G.card = k := h.card_gaussNodes (ae_mem_Icc_lobattoMeasure hμ)
    have hGa := Finset.card_erase_le (s := G) (a := x)
    have hXa : (X - C a : ℝ[X]).natDegree ≤ 1 := by compute_degree!
    have hbX : (C b - X : ℝ[X]).natDegree ≤ 1 := by compute_degree!
    have hx' : x = a ∨ x = b ∨ x ∈ G := by simpa [lobattoNodes] using hx
    rcases hx' with hxa | hxb | hxG
    · -- the endpoint $a$: $q = b - X$
      refine integral_eval_basis_lobattoNodes_nonneg_of_factor hμ hab h hx (q := C b - X)
        (by rw [← hG]; omega) (fun t ht => by simpa using ht.2) (by simpa [hxa] using hab)
        (fun h' => absurd hxa h') (fun _ => by simp)
    · -- the endpoint $b$: $q = X - a$
      refine integral_eval_basis_lobattoNodes_nonneg_of_factor hμ hab h hx (q := X - C a)
        (by rw [← hG]; omega) (fun t ht => by simpa using ht.1) (by simpa [hxb] using hab)
        (fun _ => by simp) (fun h' => absurd hxb h')
    · -- a free node: $q = (X - a)(b - X)$
      have hxI := h.gaussNodes_subset_Icc (ae_mem_Icc_lobattoMeasure hμ)
        (Finset.mem_coe.2 hxG)
      have hxa : x ≠ a := fun e => h.notMem_gaussNodes_lobattoMeasure hμ (.inl e) hxG
      have hxb : x ≠ b := fun e => h.notMem_gaussNodes_lobattoMeasure hμ (.inr e) hxG
      have hE : (G.erase x).card = k - 1 := by rw [Finset.card_erase_of_mem hxG, hGk]
      have hk : 0 < k := hGk ▸ Finset.card_pos.2 ⟨x, hxG⟩
      have hq := natDegree_mul_le (p := X - C a) (q := C b - X)
      refine integral_eval_basis_lobattoNodes_nonneg_of_factor hμ hab h hx
        (q := (X - C a) * (C b - X)) (by rw [← hG]; omega) (fun t ht => ?_) ?_ (fun _ => by simp)
        (fun _ => by simp)
      · simp only [eval_mul, eval_sub, eval_X, eval_C]
        exact mul_nonneg (sub_nonneg.2 ht.1) (sub_nonneg.2 ht.2)
      · simp only [eval_mul, eval_sub, eval_X, eval_C]
        exact mul_pos (sub_pos.2 (hxI.1.lt_of_ne' hxa)) (sub_pos.2 (hxI.2.lt_of_ne hxb))
  · rw [integral_eval_basis_of_ae_mem (ae_mem_lobattoNodes_of_not_isMomentPosDef hμ h) hx]
    exact measureReal_nonneg

/-- The Lobatto rule with the interpolatory weights: for a finite measure $\mu$ supported in
$[a, b]$, $a < b$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k) =
\sum_{x\in L}\Bigl(\int\ell_x\,d\mu\Bigr)f(x)\,,$$
$L$ the Lobatto nodes and $\ell_x$ their Lagrange basis polynomials.
Proof: S, about 8 lines. As `integral_radauQuadrature`, with
`integral_eval_basis_lobattoNodes_nonneg`. -/
theorem integral_lobattoQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ)
    (f : ℝ → ℝ) :
    ∫ x, f x ∂lobattoQuadrature μ a b k =
      ∑ x ∈ lobattoNodes μ a b k,
        (∫ t, (Lagrange.basis (lobattoNodes μ a b k) id x).eval t ∂μ) * f x := by
  unfold lobattoQuadrature interpolatoryQuadrature
  rw [integral_finsetSum_measure fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul,
    ENNReal.toReal_ofReal (integral_eval_basis_lobattoNodes_nonneg hμ hab k hx)]

/-- **Gauss–Lobatto quadrature**: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, and
every $k$, the Lobatto rule with $k$ free nodes matches the first $2k + 2$ moments of $\mu$: it
integrates every real polynomial of degree at most $2k + 1$ exactly. [Gautschi2004,
Theorem 3.6]; [GolubMeurant2010, Ch. 6] (locators to check); there for $\mu$ with more than
$k$ interior support points; otherwise the rule is $\mu$ itself.
Proof: S, about 15 lines. As `matchesMoments_radauQuadrature`, with
`isOrthogonalPolynomial_nodal_lobattoNodes`, `IsMomentPosDef.card_lobattoNodes`
($\lvert L\rvert + k = 2k + 2$), `integral_lobattoQuadrature` and
`lobattoQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero`.
Result: gauss-lobatto-quadrature -/
theorem matchesMoments_lobattoQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    MatchesMoments μ (lobattoQuadrature μ a b k) (2 * k + 2) := by
  by_cases h : IsMomentPosDef (lobattoMeasure μ a b) k
  · have hs := isOrthogonalPolynomial_nodal_lobattoNodes hμ hab h
    intro p hp
    rw [integral_lobattoQuadrature hμ hab k]
    exact hs.integral_eval_eq_sum_of_degree_lt_card_add hμ
      (by rwa [h.card_lobattoNodes hμ hab, show k + 2 + k = 2 * k + 2 by ring])
  · rw [lobattoQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_lobattoNodes_of_not_isMomentPosDef hμ h)]
    exact MatchesMoments.refl _ _

/-- The Lobatto rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$, $a < b$, and every $k$, almost every point of the Lobatto rule lies in
$[a, b]$.
Proof: S, about 10 lines. As `ae_mem_Icc_radauQuadrature`. -/
theorem ae_mem_Icc_lobattoQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    ∀ᵐ x ∂lobattoQuadrature μ a b k, x ∈ Set.Icc a b := by
  by_cases h : IsMomentPosDef (lobattoMeasure μ a b) k
  · have := isFiniteMeasure_lobattoMeasure hμ
    filter_upwards [ae_mem_interpolatoryQuadrature μ (lobattoNodes μ a b k)] with x hx
    simp only [lobattoNodes, Finset.mem_insert] at hx
    rcases hx with rfl | rfl | hx
    · exact ⟨le_rfl, hab.le⟩
    · exact ⟨hab.le, le_rfl⟩
    · exact h.gaussNodes_subset_Icc (ae_mem_Icc_lobattoMeasure hμ) (Finset.mem_coe.mpr hx)
  · rw [lobattoQuadrature, interpolatoryQuadrature_eq_self_of_ae_mem
      (ae_mem_lobattoNodes_of_not_isMomentPosDef hμ h)]
    exact hμ

/-- The mass of the Lobatto rule: for a finite measure $\mu$ supported in $[a, b]$, $a < b$,
and every $k$, the Lobatto rule has mass $\mu(\mathbb{R})$.
Proof: S, about 3 lines. `MatchesMoments.measureReal_univ_eq` on
`matchesMoments_lobattoQuadrature`. -/
theorem lobattoQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    (lobattoQuadrature μ a b k).real Set.univ = μ.real Set.univ :=
  ((matchesMoments_lobattoQuadrature hμ hab k).measureReal_univ_eq (by omega)).symm

/-- The Lobatto interpolation multiset $\{a, b\} + G + G$, for $a < b$ and $G \subseteq (a, b)$,
lies in $[a, b]$, and its repeated points lie in $(a, b)$. -/
private theorem mem_Icc_and_mem_Ioo_of_one_lt_count_cons_cons {a b : ℝ} (hab : a < b)
    {G : Finset ℝ} (hGI : (G : Set ℝ) ⊆ Set.Ioo a b) :
    (∀ y ∈ a ::ₘ b ::ₘ (G.val + G.val), y ∈ Set.Icc a b) ∧
      ∀ y ∈ a ::ₘ b ::ₘ (G.val + G.val),
        1 < (a ::ₘ b ::ₘ (G.val + G.val)).count y → y ∈ Set.Ioo a b := by
  have haG : a ∉ G := fun h => lt_irrefl a (hGI h).1
  have hbG : b ∉ G := fun h => lt_irrefl b (hGI h).2
  refine ⟨fun y hy => ?_, fun y hy hc => ?_⟩ <;>
    simp only [Multiset.mem_cons, Multiset.mem_add, Finset.mem_val, or_self] at hy <;>
    rcases hy with rfl | rfl | hy
  · exact ⟨le_rfl, hab.le⟩
  · exact ⟨hab.le, le_rfl⟩
  · exact Set.Ioo_subset_Icc_self (hGI hy)
  · simp [hab.ne, Multiset.count_eq_zero.mpr haG] at hc
  · simp [hab.ne', Multiset.count_eq_zero.mpr hbG] at hc
  · exact hGI hy

/-- **The Gauss–Lobatto remainder**: for a finite measure $\mu$ supported in $[a, b]$, $a < b$,
every $k$, and $f$ continuous on $[a, b]$ and $C^{2k+2}$ on $(a, b)$, there is $\xi \in (a, b)$
with
$$\int f\,d\mu - \int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k) =
\frac{f^{(2k+2)}(\xi)}{(2k+2)!}\int(x - a)(x - b)\,\hat\pi_k(x)^2\,d\mu(x)\,,$$
$\hat\pi_k$ the monic orthogonal polynomial of degree $k$ of `lobattoMeasure μ a b`.
[Gautschi2004, Theorem 3.7]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: L, about 80 lines; the prototype proves the nondegenerate case
(`NLAlib.exists_integral_sub_twoEndpoint_quadrature_eq_iteratedDeriv_mul`,
`NLAlib/Polynomial/Quadrature/EndpointMeasureRemainder.lean`, with
`exists_sub_eval_hermiteTwoEndpointInterpolate_eq`). As
`exists_integral_sub_integral_radauQuadrature_eq` with $m = \{a, b\} + G + G$ and the
nonpositive weight $(x - a)(x - b)\hat\pi_k^2$
(`exists_integral_eq_mul_integral_of_ae_nonpos`).
Result: gauss-lobatto-remainder -/
theorem exists_integral_sub_integral_lobattoQuadrature_eq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b)
    (hab : a < b) (k : ℕ) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hf' : ContDiffOn ℝ (2 * k + 2 : ℕ) f (Set.Ioo a b)) :
    ∃ ξ ∈ Set.Ioo a b, ∫ x, f x ∂μ - ∫ x, f x ∂lobattoQuadrature μ a b k =
      iteratedDeriv (2 * k + 2) f ξ / (2 * k + 2).factorial *
        ∫ x, (x - a) * (x - b) * (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂μ := by
  set μ' := lobattoMeasure μ a b
  have := isFiniteMeasure_lobattoMeasure hμ
  have hμ'I := ae_mem_Icc_lobattoMeasure hμ
  set π := orthogonalPolynomial μ' k
  set W : ℝ → ℝ := fun x => (x - a) * (x - b) * π.eval x ^ 2 with hW
  have hWint : Integrable W μ :=
    (integrable_eval_of_ae_mem_Icc hμ ((X - C a) * (X - C b) * π ^ 2)).congr
      (ae_of_all μ fun x => by simp [hW])
  rcases (integral_nonneg fun x => sq_nonneg (π.eval x) : 0 ≤ ∫ x, π.eval x ^ 2 ∂μ').eq_or_lt
    with h0 | hpos
  · -- degenerate case: the rule is `μ` and the weight vanishes
    refine ⟨(a + b) / 2, ⟨by linarith, by linarith⟩, ?_⟩
    rw [lobattoQuadrature_eq_self_of_integral_orthogonalPolynomial_sq_eq_zero hμ h0.symm, sub_self,
      integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ, ← h0, neg_zero, mul_zero]
  -- nondegenerate case: Hermite interpolation on `m = {a, b} + G + G`
  have hpd : IsMomentPosDef μ' (k + 1) := (isMomentPosDef_succ_iff hμ'I k).mpr hpos
  set G := gaussNodes μ' k
  have hGI : (G : Set ℝ) ⊆ Set.Ioo a b := hpd.gaussNodes_subset_Ioo hμ'I
  have hGc : G.card = k := (hpd.mono k.le_succ).card_gaussNodes hμ'I
  have hGπ : Lagrange.nodal G id = π := (hpd.mono k.le_succ).nodal_gaussNodes hμ'I
  set m : Multiset ℝ := a ::ₘ b ::ₘ (G.val + G.val) with hm
  have hmc : m.card = 2 * k + 2 := by
    simp only [hm, Multiset.card_cons, Multiset.card_add, Finset.card_val, hGc]
    ring
  obtain ⟨hmem, hrep⟩ := mem_Icc_and_mem_Ioo_of_one_lt_count_cons_cons hab hGI
  have hprod : ∀ x, ((m.map fun y => X - C y).prod).eval x = W x := by
    intro x
    have : (G.val.map fun y => X - C y).prod = π := by
      rw [← hGπ, Lagrange.nodal]
      rfl
    simp only [hm, Multiset.map_cons, Multiset.prod_cons, Multiset.map_add, Multiset.prod_add,
      this, hW, eval_mul, eval_sub, eval_X, eval_C]
    ring
  obtain ⟨H, hHdeg, hHjet⟩ :=
    exists_degree_lt_forall_iterate_derivative_eval_eq m fun y j => iteratedDeriv j f y
  have hHf : ∀ x ∈ lobattoNodes μ a b k, H.eval x = f x := by
    intro x hx
    have hxm : x ∈ m := by simpa [hm, lobattoNodes] using hx
    simpa using hHjet x hxm 0 (Multiset.count_pos.mpr hxm)
  have hQ : ∫ x, f x ∂lobattoQuadrature μ a b k = ∫ x, H.eval x ∂μ := by
    rw [matchesMoments_lobattoQuadrature hμ hab k H (by exact_mod_cast hmc ▸ hHdeg),
      integral_lobattoQuadrature hμ hab k f, integral_lobattoQuadrature hμ hab k]
    exact Finset.sum_congr rfl fun x hx => by rw [hHf x hx]
  rw [hQ]
  refine exists_integral_sub_integral_eval_eq hμ hab hf hf' hWint (.inr ?_) fun x hx => ?_
  · filter_upwards [hμ] with x hx
    exact mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hx.1) (sub_nonpos.2 hx.2)) (sq_nonneg _)
  obtain ⟨ξ, hξ, h⟩ := exists_sub_eval_eq_iteratedDeriv_mul hab (by simp) hmem hrep hf
    (hmc ▸ hf') (hmc ▸ hHdeg) hHjet hx
  exact ⟨ξ, hξ, by rw [h, hprod, hmc]⟩

/-- **The Lobatto rule is an upper bound** for $f$ with nonnegative derivative of order $2k + 2$:
for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$ continuous on
$[a, b]$, $C^{2k+2}$ on $(a, b)$ with $f^{(2k+2)} \ge 0$ there,
$$\int f\,d\mu \le \int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k)\,.$$
[Gautschi2004, Theorem 3.7]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 10 lines. `exists_integral_sub_integral_lobattoQuadrature_eq`; the weight
$(x - a)(x - b)\hat\pi_k^2 \le 0$ a.e. (`integral_nonpos_of_ae`). -/
theorem integral_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 2 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, 0 ≤ iteratedDeriv (2 * k + 2) f x) :
    ∫ x, f x ∂μ ≤ ∫ x, f x ∂lobattoQuadrature μ a b k := by
  obtain ⟨ξ, hξ, h⟩ := exists_integral_sub_integral_lobattoQuadrature_eq hμ hab k hf hf'
  have hW : ∫ x, (x - a) * (x - b) * (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂μ
      ≤ 0 := by
    rw [integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ, neg_nonpos]
    exact integral_nonneg fun x => sq_nonneg _
  linarith [mul_nonpos_of_nonneg_of_nonpos
    (div_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 2).factorial)) hW]

/-- **The Lobatto rule is a lower bound** for $f$ with nonpositive derivative of order
$2k + 2$: for a finite measure $\mu$ supported in $[a, b]$, $a < b$, every $k$, and $f$
continuous on $[a, b]$, $C^{2k+2}$ on $(a, b)$ with $f^{(2k+2)} \le 0$ there,
$$\int f\,d\,\mathsf{lobattoQuadrature}(\mu, a, b, k) \le \int f\,d\mu\,.$$
[Gautschi2004, Theorem 3.7]; [GolubMeurant2010, Ch. 6] (locators to check).
Proof: S, about 10 lines. As `integral_le_integral_lobattoQuadrature_of_iteratedDeriv_nonneg`,
with `mul_nonneg_of_nonpos_of_nonpos`. -/
theorem integral_lobattoQuadrature_le_integral_of_iteratedDeriv_nonpos
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (hf' : ContDiffOn ℝ (2 * k + 2 : ℕ) f (Set.Ioo a b))
    (hD : ∀ x ∈ Set.Ioo a b, iteratedDeriv (2 * k + 2) f x ≤ 0) :
    ∫ x, f x ∂lobattoQuadrature μ a b k ≤ ∫ x, f x ∂μ := by
  obtain ⟨ξ, hξ, h⟩ := exists_integral_sub_integral_lobattoQuadrature_eq hμ hab k hf hf'
  have hW : ∫ x, (x - a) * (x - b) * (orthogonalPolynomial (lobattoMeasure μ a b) k).eval x ^ 2 ∂μ
      ≤ 0 := by
    rw [integral_sub_mul_sub_mul_eq_neg_integral_lobattoMeasure hμ, neg_nonpos]
    exact integral_nonneg fun x => sq_nonneg _
  linarith [mul_nonneg_of_nonpos_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (hD ξ hξ) (Nat.cast_nonneg (2 * k + 2).factorial)) hW]

/-! ### The Radau Jacobi matrix -/

/-- A row of the Radau Jacobi matrix times a vector: the diagonal term and the two entries
beside it. -/
private theorem radauJacobiMatrix_mulVec_apply {k : ℕ} (μ : Measure ℝ) (c : ℝ)
    (w : Fin (k + 1) → ℝ) (i : Fin (k + 1)) :
    (radauJacobiMatrix μ c k *ᵥ w) i =
      (if i = Fin.last k then radauJacobiAlpha μ c k else jacobiAlpha μ i) * w i +
        (if h : 0 < (i : ℕ) then √(jacobiBeta μ i) * w ⟨i - 1, by omega⟩ else 0) +
        (if h : (i : ℕ) < k then √(jacobiBeta μ (i + 1)) * w ⟨i + 1, by omega⟩ else 0) := by
  obtain ⟨i, hi⟩ := i
  have hterm : ∀ j : Fin (k + 1), radauJacobiMatrix μ c k ⟨i, hi⟩ j * w j =
      (if j = ⟨i, hi⟩ then (if (⟨i, hi⟩ : Fin (k + 1)) = Fin.last k then radauJacobiAlpha μ c k
          else jacobiAlpha μ i) * w j else 0) +
        (if (j : ℕ) + 1 = i then √(jacobiBeta μ i) * w j else 0) +
        (if i + 1 = (j : ℕ) then √(jacobiBeta μ j) * w j else 0) := by
    intro j
    obtain ⟨j, hj⟩ := j
    unfold radauJacobiMatrix jacobiMatrix
    simp only [Matrix.of_apply, Fin.ext_iff, Fin.val_last]
    split_ifs <;> first | omega | (subst_vars; ring)
  have hsub : ∑ x : Fin (k + 1), (if (x : ℕ) + 1 = i then √(jacobiBeta μ i) * w x else 0) =
      if h : 0 < i then √(jacobiBeta μ i) * w ⟨i - 1, by omega⟩ else 0 := by
    split_ifs with h0
    · rw [Finset.sum_eq_single ⟨i - 1, by omega⟩ (fun x _ hx => if_neg fun e => hx (Fin.ext
        (by simp only; omega))) (by simp), if_pos (by simp only; omega)]
    · exact Finset.sum_eq_zero fun x _ => if_neg (by omega)
  have hsup : ∑ x : Fin (k + 1), (if i + 1 = (x : ℕ) then √(jacobiBeta μ x) * w x else 0) =
      if h : i < k then √(jacobiBeta μ (i + 1)) * w ⟨i + 1, by omega⟩ else 0 := by
    split_ifs with h0
    · rw [Finset.sum_eq_single ⟨i + 1, by omega⟩ (fun x _ hx => if_neg fun e => hx (Fin.ext
        (by simp only; omega))) (by simp), if_pos rfl]
    · exact Finset.sum_eq_zero fun x _ => if_neg (by omega)
  simp only [Matrix.mulVec, dotProduct, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [hsub, hsup]

/-- **The prescribed node is an eigenvalue of the Radau Jacobi matrix**: if a finite measure
$\mu$ supported in $[a, b]$ is positive definite up to degree $k + 1$ and $\pi_k(c) \ne 0$, then
$\tilde{\mathbf{J}}\mathbf{v} = c\,\mathbf{v}$ for the Radau Jacobi matrix $\tilde{\mathbf{J}}$
of order $k + 1$ and $\mathbf{v}_i = \pi_i(c)/\|\pi_i\|$ (the orthonormal polynomials at $c$;
$\mathbf{v}_0 > 0$). [Golub1973, §7] (locator to check).
Proof: M, about 45 lines. Rows $i < k$: the three-term recurrence
(`orthogonalPolynomial_add_two`, `orthogonalPolynomial_one`) divided by $\|\pi_i\|$, with
$\sqrt{\beta_i} = \|\pi_i\|/\|\pi_{i-1}\|$ (`jacobiBeta`, `integral_orthogonalPolynomial_succ_sq`,
positive norms from `isMomentPosDef_succ_iff` and `IsMomentPosDef.mono`) and the entries of
`jacobiMatrix`. Row $k$: the corner `radauJacobiAlpha μ c k` was chosen so that
$\beta_k\pi_{k-1}(c) + \tilde\alpha_k\pi_k(c) = c\,\pi_k(c)$ (`radauJacobiAlpha_succ`,
`field_simp` with `hc0`; `radauJacobiAlpha_zero` at $k = 0$). -/
theorem IsMomentPosDef.radauJacobiMatrix_mulVec_eq {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc0 : (orthogonalPolynomial μ k).eval c ≠ 0) :
    radauJacobiMatrix μ c k *ᵥ (fun i : Fin (k + 1) => (orthogonalPolynomial μ i).eval c /
        √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ)) =
      c • fun i : Fin (k + 1) => (orthogonalPolynomial μ i).eval c /
        √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ) := by
  have hs : ∀ j ≤ k, √(∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ) ≠ 0 := fun j hj =>
    (Real.sqrt_pos.mpr ((isMomentPosDef_succ_iff hμ j).mp (h.mono (by omega)))).ne'
  have hsqrtβ : ∀ m, m + 1 ≤ k → √(jacobiBeta μ (m + 1)) =
      √(∫ x, (orthogonalPolynomial μ (m + 1)).eval x ^ 2 ∂μ) /
        √(∫ x, (orthogonalPolynomial μ m).eval x ^ 2 ∂μ) := fun m _ =>
    Real.sqrt_div (integral_nonneg fun x => sq_nonneg _) _
  have hβ : ∀ m, m + 1 ≤ k → jacobiBeta μ (m + 1) =
      (√(∫ x, (orthogonalPolynomial μ (m + 1)).eval x ^ 2 ∂μ)) ^ 2 /
        (√(∫ x, (orthogonalPolynomial μ m).eval x ^ 2 ∂μ)) ^ 2 := fun m _ => by
    rw [Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
      Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _)]
    rfl
  have hrec : ∀ m, (orthogonalPolynomial μ (m + 2)).eval c =
      (c - jacobiAlpha μ (m + 1)) * (orthogonalPolynomial μ (m + 1)).eval c -
        jacobiBeta μ (m + 1) * (orthogonalPolynomial μ m).eval c := fun m => by
    simp [orthogonalPolynomial_add_two]
  funext i
  rw [radauJacobiMatrix_mulVec_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  obtain ⟨i, hi⟩ := i
  rcases Nat.lt_or_ge i k with hik | hik
  · rw [if_neg (fun h' => by simp [Fin.ext_iff] at h'; omega), dif_pos hik]
    dsimp only
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · have e0 : (orthogonalPolynomial μ 0).eval c = 1 := by simp [orthogonalPolynomial_zero]
      have e1 : (orthogonalPolynomial μ 1).eval c = c - jacobiAlpha μ 0 := by
        simp [orthogonalPolynomial_one]
      have h0 := hs 0 (by omega)
      have h1 := hs 1 (by omega)
      rw [dif_neg (lt_irrefl 0), add_zero, hsqrtβ 0 hik, e0, e1]
      field_simp
      ring
    · obtain ⟨m, rfl⟩ : ∃ m, i = m + 1 := ⟨i - 1, by omega⟩
      rw [dif_pos (by omega : 0 < m + 1)]
      simp only [Nat.add_sub_cancel]
      have h0 := hs m (by omega)
      have h1 := hs (m + 1) (by omega)
      have h2 := hs (m + 1 + 1) hik
      rw [hsqrtβ m (by omega), hsqrtβ (m + 1) hik, hrec m, hβ m (by omega)]
      field_simp
      ring
  · have hik' : i = k := by omega
    subst i
    dsimp only
    rw [if_pos (show (⟨k, hi⟩ : Fin (k + 1)) = Fin.last k from rfl), dif_neg (lt_irrefl _)]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [radauJacobiAlpha_zero]
    · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      rw [dif_pos (by omega : 0 < m + 1)]
      simp only [Nat.add_sub_cancel]
      have h0 := hs m (by omega)
      have h1 := hs (m + 1) (by omega)
      rw [radauJacobiAlpha_succ, hsqrtβ m le_rfl, hβ m le_rfl]
      field_simp
      ring

/-- The endpoint is an eigenvalue of the Radau Jacobi matrix: if a finite measure $\mu$ supported
in $[a, b]$ is positive definite up to degree $k + 1$ and $c \in \{a, b\}$, then $c$ is in the
spectrum of the Radau Jacobi matrix of order $k + 1$.
Proof: S, about 15 lines. $\pi_k(c) \ne 0$ since the zeros of $\pi_k$ lie in $(a, b)$
(`IsMomentPosDef.gaussNodes_subset_Ioo`, `gaussNodes`, `mem_roots`); then
`IsMomentPosDef.radauJacobiMatrix_mulVec_eq` with $\mathbf{v}_0 = 1/\sqrt{\mu(\mathbb{R})} \ne 0$
(`orthogonalPolynomial_zero`, `IsMomentPosDef` at the constant $1$), and
`Matrix.mulVec`-eigenvector to spectrum (`Module.End.hasEigenvalue_of_hasEigenvector`,
`Module.End.hasEigenvalue_iff_mem_spectrum`, `Matrix.spectrum_toLin'`). -/
theorem IsMomentPosDef.mem_spectrum_radauJacobiMatrix {k : ℕ} (h : IsMomentPosDef μ (k + 1))
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) :
    c ∈ spectrum ℝ (radauJacobiMatrix μ c k) := by
  have hcI : c ∉ Set.Ioo a b := by
    rcases hc with rfl | rfl <;> simp
  have hc0 : (orthogonalPolynomial μ k).eval c ≠ 0 := fun h0 =>
    hcI (h.gaussNodes_subset_Ioo hμ (mem_gaussNodes_iff_isRoot.mpr h0))
  have hpos : 0 < ∫ x, (1 : ℝ[X]).eval x ^ 2 ∂μ :=
    h 1 one_ne_zero (by simp only [degree_one, Nat.cast_add, Nat.cast_one]; positivity)
  set v : Fin (k + 1) → ℝ := fun i => (orthogonalPolynomial μ i).eval c /
    √(∫ x, (orthogonalPolynomial μ i).eval x ^ 2 ∂μ)
  have hv0 : v ≠ 0 := fun hz => by
    have h0 : v 0 = 0 := congrFun hz 0
    simp only [v, Fin.val_zero, orthogonalPolynomial_zero, eval_one, one_pow] at h0 hpos
    exact (div_ne_zero one_ne_zero (Real.sqrt_pos.mpr hpos).ne') h0
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_not,
    ← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨v, hv0, ?_⟩
  rw [Algebra.algebraMap_eq_smul_one, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    h.radauJacobiMatrix_mulVec_eq hμ hc0, sub_self]

/-- A banded matrix has zero powers off a band of width `i`. -/
private theorem matrix_pow_apply_eq_zero_of_band {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ a b : Fin n, (a : ℕ) + 2 ≤ b ∨ (b : ℕ) + 2 ≤ a → N a b = 0) (i : ℕ) :
    ∀ a b : Fin n, (b : ℕ) + i < a ∨ (a : ℕ) + i < b → (N ^ i) a b = 0 := by
  induction i with
  | zero =>
    intro a b h
    rw [pow_zero, Matrix.one_apply_ne]
    rintro rfl
    omega
  | succ i ih =>
    intro a b h
    rw [pow_succ', Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    by_cases hac : (a : ℕ) + 2 ≤ c ∨ (c : ℕ) + 2 ≤ a
    · rw [hN a c hac, zero_mul]
    · rw [ih c b (by omega), mul_zero]

/-- The powers of the Radau Jacobi matrix agree with those of the Jacobi matrix on the entries
$(a, b)$ with $i + a + b \le 2k$: the only changed entry is the $(k, k)$ loop, which such a walk
never uses. -/
private theorem radauJacobiMatrix_pow_apply_eq (μ : Measure ℝ) (c : ℝ) (k i : ℕ) :
    ∀ a b : Fin (k + 1), (i : ℕ) + a + b ≤ 2 * k →
      (radauJacobiMatrix μ c k ^ i) a b = (jacobiMatrix μ (k + 1) ^ i) a b := by
  have hJ : ∀ a b : Fin (k + 1), (a : ℕ) + 2 ≤ b ∨ (b : ℕ) + 2 ≤ a →
      jacobiMatrix μ (k + 1) a b = 0 := by
    intro a b h
    have h1 : a ≠ b := by rintro rfl; omega
    simp only [jacobiMatrix, Matrix.of_apply]
    rw [if_neg h1, if_neg (by omega), if_neg (by omega)]
  have hM : ∀ a b : Fin (k + 1), ¬(a = Fin.last k ∧ b = Fin.last k) →
      radauJacobiMatrix μ c k a b = jacobiMatrix μ (k + 1) a b := by
    intro a b h
    simp only [radauJacobiMatrix, Matrix.of_apply]
    rw [if_neg h]
  have hMb : ∀ a b : Fin (k + 1), (a : ℕ) + 2 ≤ b ∨ (b : ℕ) + 2 ≤ a →
      radauJacobiMatrix μ c k a b = 0 := by
    intro a b h
    rw [hM a b (by rintro ⟨rfl, rfl⟩; omega), hJ a b h]
  induction i with
  | zero => intro a b _; simp
  | succ i ih =>
    intro a b hab
    rw [pow_succ', Matrix.mul_apply, pow_succ', Matrix.mul_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    by_cases hac : (a : ℕ) + 2 ≤ c ∨ (c : ℕ) + 2 ≤ a
    · rw [hMb a c hac, hJ a c hac, zero_mul, zero_mul]
    by_cases hl : a = Fin.last k ∧ c = Fin.last k
    · obtain ⟨rfl, rfl⟩ := hl
      have hlast : ((Fin.last k : Fin (k + 1)) : ℕ) = k := Fin.val_last k
      rw [matrix_pow_apply_eq_zero_of_band (radauJacobiMatrix μ c k) hMb i (Fin.last k) b
          (Or.inl (by omega)),
        matrix_pow_apply_eq_zero_of_band (jacobiMatrix μ (k + 1)) hJ i (Fin.last k) b
          (Or.inl (by omega))]
      simp
    · rw [hM a c hl, ih c b (by omega)]

/-- The Radau Jacobi matrix keeps the moments of the Jacobi matrix through degree $2k$: for every
measure $\mu$, every $c$ and every $j \le 2k$,
$(\tilde{\mathbf{J}}^j)_{0,0} = (\mathbf{J}_{k+1}^j)_{0,0}$, $\tilde{\mathbf{J}}$ the Radau Jacobi
matrix and $\mathbf{J}_{k+1}$ the Jacobi matrix of order $k + 1$ (they differ only in the
$(k, k)$ entry, which a walk of length at most $2k$ from $0$ to $0$ never reaches).
Proof: M, about 45 lines. Both matrices are tridiagonal (entries of `jacobiMatrix`) and differ by
$d\,\mathbf{E}_{k,k}$. By induction, $\mathbf{J}^i\mathbf{e}_0$ is supported on indices
$\le i$ and $\tilde{\mathbf{J}}^i\mathbf{e}_0 = \mathbf{J}^i\mathbf{e}_0$ for $i \le k$ (the
correction acts only on index $k$); likewise for the rows (`Matrix.transpose`, both symmetric,
`isHermitian_jacobiMatrix`). Split $j = j_1 + j_2$ with $j_1, j_2 \le k$ (`pow_add`,
`Matrix.mul_apply`). -/
theorem radauJacobiMatrix_pow_apply_zero_zero (μ : Measure ℝ) (c : ℝ) {k j : ℕ}
    (hj : j ≤ 2 * k) : (radauJacobiMatrix μ c k ^ j) 0 0 = (jacobiMatrix μ (k + 1) ^ j) 0 0 :=
  radauJacobiMatrix_pow_apply_eq μ c k j 0 0 (by simpa using hj)

end NLAlib
