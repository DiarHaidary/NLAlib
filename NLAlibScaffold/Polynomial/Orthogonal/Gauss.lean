/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Approximation.Jackson
public import NLAlib.Polynomial.Orthogonal.Gauss
public import NLAlibScaffold.Polynomial.Orthogonal.Zeros

/-!
# The canonical Gauss rule: the theorems of stage KS7

Statements for `NLAlib/Polynomial/Orthogonal/Gauss.lean` whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.6 and "Interface for SLQ" items 1–3). For a
finite measure $\mu$ supported in $[a, b]$ and every $k$, the $k$-point Gauss rule
`gaussQuadrature μ k` matches the first $2k$ moments of $\mu$, lives in $[a, b]$, has the mass of
$\mu$ for $k > 0$ and positive weights under definiteness, and is the only measure on at most $k$
points matching $2k$ moments. Its error on a function within $\varepsilon$ of a polynomial of
degree less than $2k$ is at most $2\varepsilon\mu(\mathbb{R})$, with a Lipschitz corollary.

## Main results

* `NLAlib.integral_gaussQuadrature_eq_sum`, `NLAlib.integral_gaussQuadrature`: the rule as a
  finite sum, in both weight forms.
* `NLAlib.matchesMoments_gaussQuadrature`: Gauss quadrature, for every $k$.
* `NLAlib.ae_mem_Icc_gaussQuadrature`, `NLAlib.gaussQuadrature_real_univ`: support and mass.
* `NLAlib.IsMomentPosDef.gaussQuadrature_real_singleton_pos`: positive weights.
* `NLAlib.MatchesMoments.eq_gaussQuadrature`: uniqueness of the Gauss rule.
* `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn`,
  `NLAlib.abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith`: error bounds.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped NNReal

namespace NLAlib

/-! ### Every measure -/

/-- An interpolatory rule lives on its nodes: for every measure $\mu$ on $\mathbb{R}$ and every
finite set $s$, almost every point of the interpolatory rule of $\mu$ at $s$ lies in $s$.
Proof: S, about 15 lines. Unfold `interpolatoryQuadrature`; a.e. over the finite sum of scaled
Dirac masses (`Measure.ae_sum_iff`-style, or `measure_compl` with `Measure.coe_finsetSum`),
`ae_dirac_iff`, `Measure.ae_smul_measure`. -/
theorem ae_mem_interpolatoryQuadrature (μ : Measure ℝ) (s : Finset ℝ) :
    ∀ᵐ x ∂interpolatoryQuadrature μ s, x ∈ s := by
  unfold interpolatoryQuadrature
  rw [ae_finsetSum_measure_iff]
  exact fun x hx => Measure.ae_smul_measure (by simpa using hx) _

/-- **The Gauss rule as a sum of point masses**: for every measure $\mu$ on $\mathbb{R}$, every
$k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) = \sum_{x\in G}w_x f(x)\,,$$
with $G$ the Gauss nodes of order $k$ and $w_x$ the mass of the rule at $x$. No support
hypothesis: the rule is a finite sum of Dirac masses.
Proof: S, about 15 lines. `ae_mem_interpolatoryQuadrature` and `Measure.ae_mem_finset_iff` (any
finite measure carried by a finset), then `integral_finsetSum_measure`, `integral_smul_measure`,
`integral_dirac`; or `setIntegral_finset` with `Measure.restrict_eq_self_of_ae_mem`. -/
theorem integral_gaussQuadrature_eq_sum (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k = ∑ x ∈ gaussNodes μ k, (gaussQuadrature μ k).real {x} * f x := by
  sorry

/-- Every real function is integrable against the Gauss rule: for every measure $\mu$ on
$\mathbb{R}$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$, $f$ is integrable against
`gaussQuadrature μ k`, a finite sum of Dirac masses.
Proof: S, about 8 lines. Unfold `gaussQuadrature`, `interpolatoryQuadrature`;
`integrable_finset_sum_measure` with
`(integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top`, as in the proof of
`IsOrthogonalPolynomial.integral_interpolatoryQuadrature`. -/
theorem integrable_gaussQuadrature (μ : Measure ℝ) (k : ℕ) (f : ℝ → ℝ) :
    Integrable f (gaussQuadrature μ k) := by
  unfold gaussQuadrature interpolatoryQuadrature
  exact integrable_finsetSum_measure.mpr fun x _ =>
    (integrable_dirac enorm_lt_top).smul_measure ENNReal.ofReal_ne_top

/-! ### Finite measures with compact support -/

section Finite

variable {μ ν : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- A measure carried by the nodes is its own interpolatory rule: if a finite measure $\mu$ is
carried by a finite set $s$, then the interpolatory rule of $\mu$ at $s$ is $\mu$ (its weights
$\int\ell_x\,d\mu$ are the masses $\mu\{x\}$).
Proof: M, about 35 lines. `Measure.ae_mem_finset_iff`; each weight
$\int\ell_x\,d\mu = \mu.\mathrm{real}\{x\}$ (`setIntegral_finset`,
`Measure.restrict_eq_self_of_ae_mem`, `Lagrange.eval_basis_self`, `Lagrange.eval_basis_of_ne`);
`ofReal_measureReal`. -/
theorem interpolatoryQuadrature_eq_self_of_ae_mem {s : Finset ℝ} (hs : ∀ᵐ x ∂μ, x ∈ s) :
    interpolatoryQuadrature μ s = μ := by
  sorry

/-- **Gauss quadrature**: for a finite measure $\mu$ supported in $[a, b]$ and every $k$, the
$k$-point Gauss rule matches the first $2k$ moments of $\mu$: it integrates every real polynomial
of degree less than $2k$ exactly. [Gautschi2004, Theorem 1.45]; [GolubMeurant2010, Ch. 6];
there for $k$ at most the number of support points; past it the rule is $\mu$ itself.
Proof: S, about 15 lines. `by_cases` on `IsMomentPosDef μ k`; definite:
`IsOrthogonalPolynomial.matchesMoments_interpolatoryQuadrature` with
`isOrthogonalPolynomial_nodal_gaussNodes` and `IsMomentPosDef.card_gaussNodes`; else
`interpolatoryQuadrature_eq_self_of_ae_mem` with `ae_mem_gaussNodes_of_not_isMomentPosDef` and
`MatchesMoments.refl`.
Result: gauss-quadrature -/
theorem matchesMoments_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    MatchesMoments μ (gaussQuadrature μ k) (2 * k) := by
  sorry

/-- The integral against the Gauss rule with the interpolatory weights: for a finite measure
$\mu$ supported in $[a, b]$, every $k$ and every $f : \mathbb{R} \to \mathbb{R}$,
$$\int f\,d\,\mathsf{gaussQuadrature}(\mu, k) = \sum_{x\in G}\Bigl(\int\ell_x\,d\mu\Bigr)f(x)\,,$$
$G$ the Gauss nodes of order $k$ and $\ell_x$ the Lagrange basis polynomial of $x$.
Proof: S, about 5 lines. `IsOrthogonalPolynomial.integral_interpolatoryQuadrature` with
`isOrthogonalPolynomial_nodal_gaussNodes`. -/
theorem integral_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) (f : ℝ → ℝ) :
    ∫ x, f x ∂gaussQuadrature μ k =
      ∑ x ∈ gaussNodes μ k, (∫ t, (Lagrange.basis (gaussNodes μ k) id x).eval t ∂μ) * f x := by
  sorry

/-- The Gauss rule lives in every interval carrying the measure: for a finite measure $\mu$
supported in $[a, b]$ and every $k$, almost every point of the $k$-point Gauss rule lies in
$[a, b]$. With `matchesMoments_gaussQuadrature`, the two hypotheses moment-matching error bounds
need.
Proof: S, about 20 lines. `by_cases` on `IsMomentPosDef μ k`; definite:
`ae_mem_interpolatoryQuadrature` and `IsMomentPosDef.gaussNodes_subset_Icc`; else
`interpolatoryQuadrature_eq_self_of_ae_mem` with `ae_mem_gaussNodes_of_not_isMomentPosDef`, and
`hμ`. -/
theorem ae_mem_Icc_gaussQuadrature (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∀ᵐ x ∂gaussQuadrature μ k, x ∈ Set.Icc a b := by
  sorry

/-- The mass of the Gauss rule: for a finite measure $\mu$ supported in $[a, b]$ and $k > 0$,
the $k$-point Gauss rule has mass $\mu(\mathbb{R})$.
Proof: S, about 5 lines. `(matchesMoments_gaussQuadrature hμ k).measureReal_univ_eq`, `.symm`. -/
theorem gaussQuadrature_real_univ (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ} (hk : 0 < k) :
    (gaussQuadrature μ k).real Set.univ = μ.real Set.univ := by
  sorry

/-- The Gauss weights are positive: if a finite measure $\mu$ supported in $[a, b]$ is positive
definite up to degree $k$, then the $k$-point Gauss rule gives every Gauss node positive mass.
[Gautschi2004, Theorem 1.46] (locator to check).
Proof: M, about 30 lines. The mass at $x$ of the Dirac sum (`Measure.coe_finsetSum`,
`dirac_apply`, distinct nodes) is $\int\ell_x = \int\ell_x^2$
(`IsOrthogonalPolynomial.integral_eval_basis_eq_integral_sq` with
`isOrthogonalPolynomial_nodal_gaussNodes`), positive by `h` (`Lagrange.basis_ne_zero`,
`Lagrange.degree_basis`, `IsMomentPosDef.card_gaussNodes`). -/
theorem IsMomentPosDef.gaussQuadrature_real_singleton_pos {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {x : ℝ} (hx : x ∈ gaussNodes μ k) :
    0 < (gaussQuadrature μ k).real {x} := by
  sorry

/-- **Uniqueness of the Gauss rule**: if a finite measure $\nu$ carried by a set of at most $k$
points matches the first $2k$ moments of a finite measure $\mu$ supported in $[a, b]$, then $\nu$
is the $k$-point Gauss rule of $\mu$. [Gautschi2004, §1.4] (locator to check); there among
interpolatory rules with $k$ distinct nodes and positive weights; here any measure on at most $k$
points.
Proof: M, about 25 lines. $T = s \cup G$, $G$ the Gauss nodes; both measures are carried by $T$
(`ae_mem_interpolatoryQuadrature`); they match $2k$ moments (`h.symm.trans` with
`matchesMoments_gaussQuadrature`); $\lvert T\rvert \le 2k$ (`Finset.card_union_le`,
`card_gaussNodes_le`); `MatchesMoments.mono` and `MatchesMoments.eq_of_ae_mem` (with the instance
`isFiniteMeasure_gaussQuadrature`).
Result: gauss-quadrature-uniqueness -/
theorem MatchesMoments.eq_gaussQuadrature [IsFiniteMeasure ν] {k : ℕ}
    (h : MatchesMoments μ ν (2 * k)) (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {s : Finset ℝ}
    (hν : ∀ᵐ x ∂ν, x ∈ s) (hs : s.card ≤ k) : ν = gaussQuadrature μ k := by
  sorry

/-- **The Gauss-rule error from uniform approximation**: for a finite measure $\mu$ supported in
$[a, b]$, $f$ integrable against $\mu$, and a real polynomial $p$ of degree less than $2k$ within
$\varepsilon$ of $f$ on $[a, b]$,
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k)\Bigr\rvert \le
2\varepsilon\,\mu(\mathbb{R})\,.$$
[GolubMeurant2010, Ch. 6]; the composition of exactness with the moment-matching transfer.
Proof: S, about 15 lines.
`MatchesMoments.abs_integral_sub_integral_le_of_isUniformApproxOn` with
`matchesMoments_gaussQuadrature`, `hμ`, `ae_mem_Icc_gaussQuadrature`, `hf`,
`integrable_gaussQuadrature`; the mass by `gaussQuadrature_real_univ` for $k > 0$; at $k = 0$ the
rule is $0$ (`gaussNodes μ 0 = ∅`) and $\varepsilon \ge 0$ unless $[a, b]$ is empty. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {f : ℝ → ℝ} (hf : Integrable f μ) {k : ℕ} {p : ℝ[X]}
    (hp : p.degree < 2 * k) {ε : ℝ}
    (hε : Metric.IsUniformApproxOn (fun x => p.eval x) f (Set.Icc a b) ε) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ k| ≤ 2 * ε * μ.real Set.univ := by
  sorry

/-- **The Gauss-rule error for Lipschitz functions**: for a finite measure $\mu$ supported in
$[a, b]$, $a < b$, and $f$ $L$-Lipschitz on $[a, b]$, the $(k + 1)$-point Gauss rule
satisfies <!-- value jacksonApproximationConstant -->
$$\Bigl\lvert\int f\,d\mu - \int f\,d\,\mathsf{gaussQuadrature}(\mu, k + 1)\Bigr\rvert \le
\frac{\pi L(b - a)}{2k + 3}\mu(\mathbb{R})\,,$$
from Jackson's theorem on $[a, b]$ in degree $2k + 1$ (the constant is
`jacksonApproximationConstant`). [GolubMeurant2010, Ch. 6]; the approximation step is
[ChenTrogdonUbaru2022, Appendix C, Theorem 38]; constants composed here.
Proof: S, about 15 lines. `exists_degree_le_isUniformApproxOn_Icc_of_lipschitzOnWith` in degree
$2k + 1$ (`𝕜 := ℝ`); integrability of $f$ from `LipschitzOnWith.continuousOn`,
`ContinuousOn.integrableOn_Icc` and `Measure.restrict_eq_self_of_ae_mem`;
`abs_integral_sub_integral_gaussQuadrature_le_of_isUniformApproxOn`; `push_cast`, `field_simp`,
`ring`, as the Lanczos Lipschitz corollary. -/
theorem abs_integral_sub_integral_gaussQuadrature_le_of_lipschitzOnWith
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (hab : a < b) {f : ℝ → ℝ} {L : ℝ≥0}
    (hf : LipschitzOnWith L f (Set.Icc a b)) (k : ℕ) :
    |∫ x, f x ∂μ - ∫ x, f x ∂gaussQuadrature μ (k + 1)| ≤
      jacksonApproximationConstant * L * (b - a) / (2 * k + 3) * μ.real Set.univ := by
  sorry

end Finite

end NLAlib
