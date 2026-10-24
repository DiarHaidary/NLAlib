/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import NLAlib.Polynomial.Orthogonal.Basic
public import NLAlib.Polynomial.Orthogonal.Zeros

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
-/

@[expose] public section

open MeasureTheory Polynomial

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

end NLAlib
