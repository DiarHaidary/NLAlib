/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Orthogonal.Basic
public import NLAlib.Polynomial.Orthogonal.Zeros
public import NLAlib.Polynomial.Approximation.Jackson

/-!
# Gauss quadrature

The interpolatory quadrature rule of a measure $\mu$ at distinct nodes $s \subseteq \mathbb{R}$
puts at each node $x$ the weight $\int\ell_x\,d\mu$, $\ell_x$ the Lagrange basis polynomial of
$x$ (Mathlib's `Lagrange.basis s id x`); it integrates every polynomial of degree less than
$\lvert s\rvert$ exactly. When the nodal polynomial $\pi_s(z) = \prod_{x\in s}(z - x)$ is
orthogonal to the polynomials of degree less than $\lvert s\rvert$ (the nodes are the zeros of
the degree-$\lvert s\rvert$ orthogonal polynomial of $\mu$), it is the Gauss rule: its weights
are nonnegative, $\int\ell_x\,d\mu = \int\ell_x^2\,d\mu$, and it integrates every polynomial of
degree less than $2\lvert s\rvert$ exactly, so it matches the first $2\lvert s\rvert$ moments of
$\mu$.

The canonical $k$-point Gauss rule of $\mu$, `gaussQuadrature μ k`, is the interpolatory rule at
the Gauss nodes `gaussNodes μ k`, the distinct real zeros of the monic orthogonal polynomial
`orthogonalPolynomial μ k` (`NLAlib.Polynomial.Orthogonal.Zeros`). It is defined for every
measure and every $k$; past the number of support points of $\mu$ it is $\mu$ itself. For
spectral measures the Ritz values of the Lanczos method are Gauss nodes
(`NLAlib.HasOrthonormalCols.isOrthogonalPolynomial_nodal`).

## Main definitions

* `NLAlib.interpolatoryQuadrature`: the interpolatory rule as a measure.
* `NLAlib.gaussQuadrature`: the canonical Gauss rule of a measure.

## Main results

* `NLAlib.IsOrthogonalPolynomial.integral_eval_eq_sum`: Gauss quadrature is exact through degree
  $2\lvert s\rvert - 1$.
* `NLAlib.IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`: the weights are
  nonnegative.
* `NLAlib.IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature`: the rule matches
  $2\lvert s\rvert$ moments.
* `NLAlib.integral_gaussQuadrature_eq_sum`, `NLAlib.integral_gaussQuadrature`: the rule as a
  finite sum, in both weight forms.
* `NLAlib.matchesMoments_gaussQuadrature`: Gauss quadrature, for every $k$.
* `NLAlib.ae_mem_Icc_gaussQuadrature`, `NLAlib.gaussQuadrature_real_univ`: support and mass.
* `NLAlib.gaussQuadrature_real_singleton`: the mass at a node is $\int\ell_x\,d\mu$.
* `NLAlib.IsMomentPosDef.gaussQuadrature_real_singleton_pos`: positive weights.
* `NLAlib.MatchesMoments.eq_gaussQuadrature`: uniqueness of the Gauss rule.
* `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn`,
  `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith`: error bounds.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped NNReal

namespace NLAlib

/-- The **interpolatory quadrature rule** of $\mu$ at the nodes $s$, as a measure: weight
$\int \ell_x\,d\mu$ at each node $x$, $\ell_x$ the Lagrange basis polynomial. At Gauss nodes the
weights are nonnegative (`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq`), and the
rule is the Gauss rule. Junk: negative weights are truncated at $0$, so at nodes that are not
Gauss nodes the measure need not be the interpolatory rule. -/
noncomputable def interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) : Measure ℝ :=
  ∑ x ∈ s, ENNReal.ofReal (∫ t, (Lagrange.basis s id x).eval t ∂μ) • Measure.dirac x

/-- An interpolatory quadrature rule is a finite measure. -/
instance isFiniteMeasure_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    IsFiniteMeasure (interpolatoryQuadrature μ s) := by
  unfold interpolatoryQuadrature
  have : ∀ x : ℝ, IsFiniteMeasure (ENNReal.ofReal (∫ t, (Lagrange.basis s id x).eval t ∂μ) •
      Measure.dirac x) := fun x => Measure.smul_finite _ ENNReal.ofReal_ne_top
  infer_instance

/-- Interpolatory quadrature is exact below degree $\lvert s\rvert$. -/
private theorem integral_eval_eq_sum_of_degree_lt {μ : Measure ℝ} {s : Finset ℝ}
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {r : ℝ[X]}
    (hr : r.degree < s.card) :
    ∫ x, r.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * r.eval x := by
  have hint : ∀ x ∈ s, Integrable (fun t => r.eval x * (Lagrange.basis s id x).eval t) μ :=
    fun x _ => (integrable_eval_of_ae_mem_Icc hμ _).const_mul _
  have hr' := Lagrange.eq_interpolate (v := id) (Set.injOn_id _) hr
  rw [Lagrange.interpolate_apply] at hr'
  calc ∫ x, r.eval x ∂μ
      = ∫ t, ∑ x ∈ s, r.eval x * (Lagrange.basis s id x).eval t ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
        dsimp only
        conv_lhs => rw [hr']
        simp only [eval_finsetSum, eval_mul, eval_C, id]
    _ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * r.eval x := by
        rw [integral_finsetSum _ hint]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [integral_const_mul, mul_comm]

/-- **Gauss quadrature**: if the nodal polynomial $\pi_s$ of distinct real nodes $s$ is
orthogonal in $L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite
measure $\mu$ supported in $[a, b]$, then
$$\int p\,d\mu = \sum_{x\in s}\Bigl(\int\ell_x\,d\mu\Bigr)p(x)$$
for every real polynomial $p$ of degree less than $2\lvert s\rvert$, $\ell_x$ the Lagrange basis
polynomial of $x$. [Gautschi2004, Theorems 1.45 and 1.46]; [GolubMeurant2010, Ch. 6];
there at the zeros of the orthogonal polynomial of a positive measure; here at any nodes whose
nodal polynomial is orthogonal.
Result: gauss-quadrature -/
theorem IsOrthogonalPolynomial.integral_eval_eq_sum {μ : Measure ℝ} {s : Finset ℝ}
    (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id)) [IsFiniteMeasure μ] {a b : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : p.degree < 2 * s.card) :
    ∫ x, p.eval x ∂μ = ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * p.eval x := by
  set w := Lagrange.nodal s id
  have hw : w.Monic := Lagrange.nodal_monic
  have hsplit := modByMonic_add_div p w
  have hmod : (p %ₘ w).degree < s.card := by
    have := degree_modByMonic_lt p hw
    rwa [Lagrange.degree_nodal] at this
  have hdiv : (p /ₘ w).degree < s.card := by
    by_cases hq : p /ₘ w = 0
    · rw [hq, degree_zero]
      exact WithBot.bot_lt_coe _
    have hp0 : p ≠ 0 := by
      rintro rfl
      exact hq (zero_divByMonic w)
    rw [degree_eq_natDegree hq, Nat.cast_lt, natDegree_divByMonic p hw, Lagrange.natDegree_nodal]
    rw [degree_eq_natDegree hp0] at hp
    have : p.natDegree < 2 * s.card := by exact_mod_cast hp
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

/-- The Gauss weights are nonnegative: if the nodal polynomial of $s$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite measure $\mu$
supported in $[a, b]$, then the weight of each node $x \in s$ is
$\int\ell_x\,d\mu = \int\ell_x^2\,d\mu \ge 0$, $\ell_x$ the Lagrange basis polynomial of $x$:
$\ell_x^2 - \ell_x$ vanishes at the nodes and has degree less than $2\lvert s\rvert$. -/
theorem IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ s) :
    ∫ t, (Lagrange.basis s id x).eval t ∂μ = ∫ t, (Lagrange.basis s id x).eval t ^ 2 ∂μ := by
  set ℓ := Lagrange.basis s id x
  have hcard : 0 < s.card := Finset.card_pos.mpr ⟨x, hx⟩
  have hdeg : (ℓ ^ 2).degree < 2 * s.card := by
    have h1 : (ℓ ^ 2).natDegree < 2 * s.card := by
      have := natDegree_pow_le (p := ℓ) (n := 2)
      rw [Lagrange.natDegree_basis (Set.injOn_id _) hx] at this
      omega
    have h2 : (ℓ ^ 2).degree < ((2 * s.card : ℕ) : WithBot ℕ) :=
      degree_le_natDegree.trans_lt (by exact_mod_cast h1)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using h2
  have h := hs.integral_eval_eq_sum hμ hdeg
  simp only [eval_pow] at h
  rw [h, Finset.sum_eq_single x]
  · have : ℓ.eval x = 1 := Lagrange.eval_basis_self (v := id) (Set.injOn_id _) hx
    rw [this, one_pow, mul_one]
  · intro y hy hyx
    have : ℓ.eval y = 0 := Lagrange.eval_basis_of_ne (v := id) (Ne.symm hyx) hy
    rw [this]
    ring
  · intro hx'
    exact absurd hx hx'

/-- The integral against the Gauss rule (stated as `integral_interpolatoryQuadrature` below). -/
private theorem integral_interpolatoryQuadrature_of_isOrthogonalPolynomial {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (f : ℝ → ℝ) :
    ∫ x, f x ∂interpolatoryQuadrature μ s =
      ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * f x := by
  unfold interpolatoryQuadrature
  rw [integral_finsetSum_measure fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal]
  rw [hs.integral_eval_basis_eq_integral_sq hμ hx]
  exact integral_nonneg fun t => sq_nonneg _

/-- **The Gauss rule matches $2\lvert s\rvert$ moments**: if the nodal polynomial of $s$ is
orthogonal in $L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite
measure $\mu$ supported in $[a, b]$, then $\mu$ and its interpolatory rule at $s$ match their
first $2\lvert s\rvert$ moments.
[Gautschi2004, Theorems 1.45 and 1.46]; [GolubMeurant2010, Ch. 6].
Result: gauss-quadrature -/
theorem IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) :
    MatchesMoments μ (interpolatoryQuadrature μ s) (2 * s.card) := by
  intro p hp
  rw [integral_interpolatoryQuadrature_of_isOrthogonalPolynomial hs hμ,
    hs.integral_eval_eq_sum hμ (by exact_mod_cast hp)]

/-- The integral against the Gauss rule: if the nodal polynomial of $s$ is orthogonal in
$L^2(\mu)$ to the polynomials of degree less than $\lvert s\rvert$, for a finite measure $\mu$
supported in $[a, b]$, then for every $f : \mathbb{R} \to \mathbb{R}$ the integral of $f$ against
the interpolatory rule at $s$ is $\sum_{x\in s}\bigl(\int\ell_x\,d\mu\bigr)f(x)$, $\ell_x$ the
Lagrange basis polynomial of $x$; the truncation of the weights at $0$ does not act. -/
theorem IsOrthogonalPolynomial.integral_interpolatoryQuadrature {μ : Measure ℝ}
    {s : Finset ℝ} (hs : IsOrthogonalPolynomial μ s.card (Lagrange.nodal s id))
    [IsFiniteMeasure μ] {a b : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (f : ℝ → ℝ) :
    ∫ x, f x ∂interpolatoryQuadrature μ s =
      ∑ x ∈ s, (∫ t, (Lagrange.basis s id x).eval t ∂μ) * f x :=
  integral_interpolatoryQuadrature_of_isOrthogonalPolynomial hs hμ f

/-! ### The canonical Gauss rule -/

/-- The **$k$-point Gauss rule** of $\mu$: the interpolatory rule at the Gauss nodes. It matches
the first $2k$ moments of $\mu$ for every $k$; past the number of support points it is $\mu$
itself. -/
noncomputable def gaussQuadrature (μ : Measure ℝ) (k : ℕ) : Measure ℝ :=
  interpolatoryQuadrature μ (gaussNodes μ k)

/-- The Gauss rule is a finite measure (the definition is not reducible, so
`isFiniteMeasure_interpolatoryQuadrature` is not found through it). -/
instance isFiniteMeasure_gaussQuadrature (μ : Measure ℝ) (k : ℕ) :
    IsFiniteMeasure (gaussQuadrature μ k) := by
  unfold gaussQuadrature
  infer_instance

/-! ### Every measure -/

/-- An interpolatory rule lives on its nodes: for every measure $\mu$ on $\mathbb{R}$ and every
finite set $s$, almost every point of the interpolatory rule of $\mu$ at $s$ lies in $s$. -/
theorem ae_mem_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    ∀ᵐ x ∂interpolatoryQuadrature μ s, x ∈ s := by
  unfold interpolatoryQuadrature
  rw [ae_finsetSum_measure_iff]
  exact fun x hx => Measure.ae_smul_measure (by simpa using hx) _

/-- Every real function is integrable against the Gauss rule: for every measure $\mu$ on
$\mathbb{R}$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$, $f$ is integrable against
`gaussQuadrature μ k`, a finite sum of Dirac masses. -/
theorem integrable_gaussQuadrature (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    Integrable f (gaussQuadrature μ k) := by
  unfold gaussQuadrature interpolatoryQuadrature
  exact integrable_finsetSum_measure.mpr fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-- **The Gauss rule as a sum of point masses**: for every measure $\mu$ on $\mathbb{R}$, every
$k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) = \sum_{x\in G}w_x f(x)\,,$$
with $G$ the Gauss nodes of order $k$ and $w_x$ the mass of the rule at $x$. No support
hypothesis: the rule is a finite sum of Dirac masses. -/
theorem integral_gaussQuadrature_eq_sum (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k = ∑ x ∈ gaussNodes μ k, (gaussQuadrature μ k).real {x} * f x := by
  conv_lhs => rw [← Measure.restrict_eq_self_of_ae_mem (μ := gaussQuadrature μ k)
    (s := gaussNodes μ k) (ae_mem_interpolatoryQuadrature μ (gaussNodes μ k))]
  rw [setIntegral_finset _ (integrable_gaussQuadrature μ k f).integrableOn]
  simp only [smul_eq_mul]

/-! ### Finite measures with compact support -/

section Finite

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- A measure carried by the nodes is its own interpolatory rule: if a finite measure $\mu$ is
carried by a finite set $s$, then the interpolatory rule of $\mu$ at $s$ is $\mu$ (its weights
$\int\ell_x\,d\mu$ are the masses $\mu\{x\}$). -/
theorem interpolatoryQuadrature_eq_self_of_ae_mem {s : Finset ℝ} (hs : ∀ᵐ x ∂μ, x ∈ s) :
    interpolatoryQuadrature μ s = μ := by
  refine Eq.trans ?_ (Measure.ae_mem_finset_iff.mp hs).symm
  simp only [interpolatoryQuadrature]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [integral_eval_basis_of_ae_mem hs hx, ofReal_measureReal]

/-- **Gauss quadrature**: for a finite measure $\mu$ supported in $[a, b]$ and every $k$, the
$k$-point Gauss rule matches the first $2k$ moments of $\mu$: it integrates every real polynomial
of degree less than $2k$ exactly. [Gautschi2004, Theorem 1.45]; [GolubMeurant2010, Ch. 6];
there for $k$ at most the number of support points; past it the rule is $\mu$ itself.
Result: gauss-quadrature -/
theorem matchesMoments_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    MatchesMoments μ (gaussQuadrature μ k) (2 * k) := by
  by_cases h : IsMomentPosDef μ k
  · have := (isOrthogonalPolynomial_nodal_gaussNodes hμ k).matchesMoments_interpolatoryQuadrature hμ
    rwa [h.card_gaussNodes hμ] at this
  · unfold gaussQuadrature
    rw [interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_gaussNodes_of_not_isMomentPosDef hμ h)]
    exact MatchesMoments.refl _ _

/-- The integral against the Gauss rule with the interpolatory weights: for a finite measure
$\mu$ supported in $[a, b]$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) = \sum_{x\in G}\Bigl(\int\ell_x\,d\mu\Bigr)f(x)\,,$$
$G$ the Gauss nodes of order $k$ and $\ell_x$ the Lagrange basis polynomial of $x$. -/
theorem integral_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k =
      ∑ x ∈ gaussNodes μ k, (∫ t, (Lagrange.basis (gaussNodes μ k) id x).eval t ∂μ) * f x :=
  IsOrthogonalPolynomial.integral_interpolatoryQuadrature
    (isOrthogonalPolynomial_nodal_gaussNodes hμ k) hμ f

/-- The Gauss rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$ and every $k$, almost every point of the $k$-point Gauss rule lies in
$[a, b]$. With `matchesMoments_gaussQuadrature`, the two hypotheses moment-matching error bounds
need. -/
theorem ae_mem_Icc_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∀ᵐ x ∂gaussQuadrature μ k, x ∈ Set.Icc a b := by
  by_cases h : IsMomentPosDef μ k
  · unfold gaussQuadrature
    filter_upwards [ae_mem_interpolatoryQuadrature μ (gaussNodes μ k)] with x hx
    exact h.gaussNodes_subset_Icc hμ (Finset.mem_coe.mpr hx)
  · unfold gaussQuadrature
    rw [interpolatoryQuadrature_eq_self_of_ae_mem (ae_mem_gaussNodes_of_not_isMomentPosDef hμ h)]
    exact hμ

/-- The mass of the Gauss rule: for a finite measure $\mu$ supported in $[a, b]$ and $k > 0$,
the $k$-point Gauss rule has mass $\mu(\mathbb{R})$. -/
theorem gaussQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ} (hk : 0 < k) :
    (gaussQuadrature μ k).real Set.univ = μ.real Set.univ :=
  ((matchesMoments_gaussQuadrature hμ k).measureReal_univ_eq (by omega)).symm

/-- The mass of the Gauss rule at a node is the interpolatory weight: for a finite measure $\mu$
supported in $[a, b]$, every $k$ and every Gauss node $x$ of order $k$,
$$\mathsf{gaussQuadrature}(\mu, k)(\{x\}) = \int\ell_x\,d\mu\,,$$
$\ell_x$ the Lagrange basis polynomial of $x$ at the Gauss nodes; by
`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq` this is also $\int\ell_x^2\,d\mu$.
The link between the two weight forms of `integral_gaussQuadrature_eq_sum` and
`integral_gaussQuadrature`. -/
theorem gaussQuadrature_real_singleton (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ} {x : ℝ}
    (hx : x ∈ gaussNodes μ k) :
    (gaussQuadrature μ k).real {x} = ∫ t, (Lagrange.basis (gaussNodes μ k) id x).eval t ∂μ := by
  -- integrate the indicator of $\{x\}$ in both weight forms
  have h := (integral_gaussQuadrature_eq_sum μ k fun t => if t = x then (1 : ℝ) else 0).symm
    |>.trans (integral_gaussQuadrature hμ k _)
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', hx, if_true] using h

/-- The Gauss weights are positive: if a finite measure $\mu$ supported in $[a, b]$ is positive
definite up to degree $k$, then the $k$-point Gauss rule gives every Gauss node positive mass.
[Gautschi2004, Theorem 1.46] (locator to check). -/
theorem IsMomentPosDef.gaussQuadrature_real_singleton_pos {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ gaussNodes μ k) :
    0 < (gaussQuadrature μ k).real {x} := by
  have hG : (gaussNodes μ k).card = k := h.card_gaussNodes hμ
  rw [gaussQuadrature_real_singleton hμ hx,
    (isOrthogonalPolynomial_nodal_gaussNodes hμ k).integral_eval_basis_eq_integral_sq hμ hx]
  refine h _ (Lagrange.basis_ne_zero (Set.injOn_id _) hx) ?_
  rw [Lagrange.degree_basis (Set.injOn_id _) hx, hG]
  exact_mod_cast Nat.sub_lt (hG ▸ Finset.card_pos.mpr ⟨x, hx⟩) one_pos

/-- **Uniqueness of the Gauss rule**: if a finite measure $\nu$ carried by a set of at most $k$
points matches the first $2k$ moments of a finite measure $\mu$ supported in $[a, b]$, then $\nu$
is the $k$-point Gauss rule of $\mu$. [Gautschi2004, §1.4] (locator to check); there among
interpolatory rules with $k$ distinct nodes and positive weights; here any measure on at most $k$
points.
Result: gauss-quadrature-uniqueness -/
theorem MatchesMoments.eq_gaussQuadrature [IsFiniteMeasure ν] {k : ℕ}
    (h : MatchesMoments μ ν (2 * k)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {s : Finset ℝ}
    (hν : ∀ᵐ x ∂ν, x ∈ s) (hs : s.card ≤ k) : ν = gaussQuadrature μ k := by
  have hM : MatchesMoments ν (gaussQuadrature μ k) (2 * k) :=
    h.symm.trans (matchesMoments_gaussQuadrature hμ k)
  have hνT : ∀ᵐ x ∂ν, x ∈ s ∪ gaussNodes μ k :=
    hν.mono fun x hx => Finset.mem_union_left _ hx
  have hGT : ∀ᵐ x ∂gaussQuadrature μ k, x ∈ s ∪ gaussNodes μ k := by
    exact (ae_mem_interpolatoryQuadrature μ (gaussNodes μ k)).mono fun x hx =>
      Finset.mem_union_right _ hx
  have hcard : (s ∪ gaussNodes μ k).card ≤ 2 * k :=
    (Finset.card_union_le _ _).trans (by have := card_gaussNodes_le μ k; omega)
  exact MatchesMoments.eq_of_ae_mem (hM.mono hcard) hνT hGT

/-- **The Gauss-rule error from uniform approximation**: for a finite measure $\mu$ supported in
$[a, b]$, $f$ integrable against $\mu$, and a real polynomial $p$ of degree less than $2k$ within
$\varepsilon$ of $f$ on $[a, b]$,
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k)\Bigr\rvert \le
2\varepsilon\,\mu(\mathbb{R})\,.$$
[GolubMeurant2010, Ch. 6]; the composition of exactness with the moment-matching transfer. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {f : ℝ → ℝ} (hf : Integrable f μ) {k : ℕ} {p : ℝ[X]}
    (hp : p.degree < 2 * k) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ k| ≤ 2 * ε * μ.real Set.univ := by
  have h := MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn
    (matchesMoments_gaussQuadrature hμ k) hμ (ae_mem_Icc_gaussQuadrature hμ k) hf
    (integrable_gaussQuadrature μ k f) hp hε
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · -- at $k = 0$ the rule is $0$, and the bound $\mu(\mathbb{R})\varepsilon$ is nonnegative
    have hnu : (gaussQuadrature μ 0).real Set.univ = 0 := by
      simp only [gaussQuadrature, interpolatoryQuadrature, gaussNodes, orthogonalPolynomial_zero,
        roots_one, Multiset.empty_eq_zero, Multiset.toFinset_zero, Finset.sum_empty,
        measureReal_zero, Pi.zero_apply]
    rw [hnu, add_zero] at h
    linarith [abs_nonneg (∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ 0)]
  · rw [gaussQuadrature_real_univ hμ hk] at h
    linarith

/-- **The Gauss-rule error for Lipschitz functions**: for a finite measure $\mu$ supported in
$[a, b]$, $a < b$, and $f$ $L$-Lipschitz on $[a, b]$, the $(k + 1)$-point Gauss rule
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k + 1)\Bigr\rvert \le
\frac{\pi L(b - a)}{2k + 3}\mu(\mathbb{R})\,,$$
from Jackson's theorem on $[a, b]$ in degree $2k + 1$ (the constant is
`jacksonApproximationConstant`). [GolubMeurant2010, Ch. 6]; the approximation step is
[ChenTrogdonUbaru2022, Appendix C, Theorem 38]; constants composed here. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) (k : ℕ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * k + 3) * μ.real Set.univ := by
  have hint : Integrable f μ := by
    have h := hf.continuousOn.integrableOn_Icc (μ := μ)
    rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμ] at h
  obtain ⟨p, hp, hε⟩ :=
    exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith (𝕜 := ℝ) hab hf (2 * k + 1)
  have hp' : p.degree < 2 * ((k + 1 : ℕ) : WithBot ℕ) :=
    hp.trans_lt (by exact_mod_cast (by omega : 2 * k + 1 < 2 * (k + 1)))
  have h := abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn hμ hint hp' hε
  refine h.trans_eq ?_
  push_cast
  field_simp
  ring

end Finite

end NLAlib
