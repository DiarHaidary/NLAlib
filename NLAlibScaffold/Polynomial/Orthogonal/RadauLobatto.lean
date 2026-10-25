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
    IsFiniteMeasure (radauMeasure μ c) := by
  have hbound : ∀ᵐ x ∂μ, ‖x - c‖ₑ ≤ ENNReal.ofReal (|a - c| + |b - c|) := by
    filter_upwards [hμ] with x hx
    rw [Real.enorm_eq_ofReal_abs]
    apply ENNReal.ofReal_le_ofReal
    rw [abs_le]
    constructor <;>
      linarith [hx.1, hx.2, le_abs_self (a - c), neg_abs_le (a - c), le_abs_self (b - c),
        neg_abs_le (b - c), abs_nonneg (a - c), abs_nonneg (b - c)]
  have hint : ∫⁻ x, ‖x - c‖ₑ ∂μ ≤ ENNReal.ofReal (|a - c| + |b - c|) * μ Set.univ :=
    (lintegral_mono_ae hbound).trans_eq (lintegral_const _)
  constructor
  rw [radauMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact lt_of_le_of_lt hint (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ _))

/-- The Radau modified measure lives where $\mu$ does: for $\mu$ supported in $[a, b]$ and every
$c$, almost every point of `radauMeasure μ c` lies in $[a, b]$.
Proof: S, about 4 lines. `withDensity_absolutelyContinuous` and `Measure.AbsolutelyContinuous.ae_le`
applied to `hμ`. -/
theorem ae_mem_Icc_radauMeasure (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (c : ℝ) :
    ∀ᵐ x ∂radauMeasure μ c, x ∈ Set.Icc a b := by
  unfold radauMeasure
  exact (withDensity_absolutelyContinuous μ _).ae_le hμ

/-! ### Radau exactness -/

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
  sorry

/-- The number of Radau nodes: if $\mu$, finite and supported in $[a, b]$, has a Radau modified
measure at $c \in \{a, b\}$ positive definite up to degree $k$, then the Radau rule has
$k + 1$ nodes.
Proof: S, about 6 lines. `radauNodes`, `Finset.card_insert_of_notMem` with
`IsMomentPosDef.notMem_gaussNodes_radauMeasure`, and `IsMomentPosDef.card_gaussNodes` for the
modified measure (`isFiniteMeasure_radauMeasure`, `ae_mem_Icc_radauMeasure`). -/
theorem IsMomentPosDef.card_radauNodes {k : ℕ} (h : IsMomentPosDef (radauMeasure μ c) k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b) : (radauNodes μ c k).card = k + 1 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The mass of the Radau rule: for a finite measure $\mu$ supported in $[a, b]$,
$c \in \{a, b\}$ and every $k$, the Radau rule has mass $\mu(\mathbb{R})$.
Proof: S, about 3 lines. `MatchesMoments.measureReal_univ_eq` on
`matchesMoments_radauQuadrature` ($2k + 1 > 0$). -/
theorem radauQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hc : c = a ∨ c = b)
    (k : ℕ) : (radauQuadrature μ c k).real Set.univ = μ.real Set.univ := by
  sorry

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
  sorry

/-! ### The Radau remainder and bounds -/

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
    IsFiniteMeasure (lobattoMeasure μ a b) := by
  sorry

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
  sorry

/-- The number of Lobatto nodes: if $\mu$, finite and supported in $[a, b]$, $a < b$, has a
Lobatto modified measure positive definite up to degree $k$, the Lobatto rule has $k + 2$
nodes.
Proof: S, about 8 lines. `lobattoNodes`, `Finset.card_insert_of_notMem` twice
(`IsMomentPosDef.notMem_gaussNodes_lobattoMeasure`, `hab.ne`), `IsMomentPosDef.card_gaussNodes`
for the modified measure. -/
theorem IsMomentPosDef.card_lobattoNodes {k : ℕ} (h : IsMomentPosDef (lobattoMeasure μ a b) k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) : (lobattoNodes μ a b k).card = k + 2 := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The Lobatto rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$, $a < b$, and every $k$, almost every point of the Lobatto rule lies in
$[a, b]$.
Proof: S, about 10 lines. As `ae_mem_Icc_radauQuadrature`. -/
theorem ae_mem_Icc_lobattoQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    ∀ᵐ x ∂lobattoQuadrature μ a b k, x ∈ Set.Icc a b := by
  sorry

/-- The mass of the Lobatto rule: for a finite measure $\mu$ supported in $[a, b]$, $a < b$,
and every $k$, the Lobatto rule has mass $\mu(\mathbb{R})$.
Proof: S, about 3 lines. `MatchesMoments.measureReal_univ_eq` on
`matchesMoments_lobattoQuadrature`. -/
theorem lobattoQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) (k : ℕ) :
    (lobattoQuadrature μ a b k).real Set.univ = μ.real Set.univ := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-! ### The Radau Jacobi matrix -/

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
  sorry

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
  sorry

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
    (hj : j ≤ 2 * k) : (radauJacobiMatrix μ c k ^ j) 0 0 = (jacobiMatrix μ (k + 1) ^ j) 0 0 := by
  sorry

end NLAlib
