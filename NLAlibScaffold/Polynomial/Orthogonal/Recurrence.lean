/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Polynomial.Orthogonal.Recurrence
public import NLAlibScaffold.Polynomial.Orthogonal.Basic

/-!
# The three-term recurrence: the theorems of stage KS7

Statements for `NLAlib/Polynomial/Orthogonal/Recurrence.lean` whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.3). The monic orthogonal polynomials
$\pi_k$ of a measure $\mu$ (`NLAlib.orthogonalPolynomial`, defined by the Stieltjes recurrence)
are monic of degree $k$ for every $\mu$; for a finite measure supported in $[a, b]$ they are
orthogonal to the lower degrees for every $k$, with no nondegeneracy hypothesis, their norms
obey $\|\pi_{k+1}\|^2 = \beta_{k+1}\|\pi_k\|^2$, and $\pi_k$ is the only monic orthogonal
polynomial of degree $k$ when $\mu$ is positive definite up to degree $k$. The polynomials, the
recurrence coefficients and the Jacobi matrix depend on $\mu$ only through finitely many moments.

The private steps of the orthogonality induction are fixed here so that each proof stays
short; their hypotheses `h1`, `h0` are the inductive hypotheses.

## Main results

* `NLAlib.monic_orthogonalPolynomial`, `NLAlib.natDegree_orthogonalPolynomial`: monic of
  degree $k$.
* `NLAlib.isOrthogonalPolynomial_orthogonalPolynomial`: existence of the orthogonal polynomials.
* `NLAlib.integral_orthogonalPolynomial_succ_sq`, `NLAlib.integral_orthogonalPolynomial_sq_eq_prod`:
  the norms.
* `NLAlib.isMomentPosDef_succ_iff`: definiteness is positivity of the last norm.
* `NLAlib.IsMomentPosDef.eq_orthogonalPolynomial`: uniqueness.
* `NLAlib.MatchesMoments.orthogonalPolynomial_eq`, `NLAlib.MatchesMoments.jacobiMatrix_eq`:
  moment invariance.
* `NLAlib.isHermitian_jacobiMatrix`: the Jacobi matrix is symmetric.
-/

@[expose] public section

open MeasureTheory Polynomial

namespace NLAlib

/-! ### Algebra and moment invariance (no support hypothesis) -/

section Algebra

variable {μ ν : Measure ℝ}

/-- Monicity and degree of $\pi_k$, proved together by two-step induction: the leading term
$(x - \alpha_{k+1})\pi_{k+1}$ is monic of degree $k + 2$ and $C(\beta_{k+1})\pi_k$ has degree
at most $k$. -/
private theorem monic_and_natDegree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).Monic ∧ (orthogonalPolynomial μ k).natDegree = k := by
  induction k using Nat.twoStepInduction with
  | zero => exact ⟨monic_one, natDegree_one⟩
  | one =>
    rw [orthogonalPolynomial_one]
    exact ⟨monic_X_sub_C _, natDegree_X_sub_C _⟩
  | more k ih0 ih1 =>
    rw [orthogonalPolynomial_add_two]
    have hR : ((X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1)).natDegree =
        k + 2 := by
      rw [Monic.natDegree_mul' (monic_X_sub_C _) ih1.1.ne_zero, natDegree_X_sub_C, ih1.2]
      omega
    have hlt : (C (jacobiBeta μ (k + 1)) * orthogonalPolynomial μ k).natDegree <
        ((X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1)).natDegree := by
      rw [hR]
      exact ((natDegree_C_mul_le _ _).trans_eq ih0.2).trans_lt (by omega)
    exact ⟨((monic_X_sub_C _).mul ih1.1).sub_of_left (degree_lt_degree hlt),
      (natDegree_sub_eq_left_of_natDegree_lt hlt).trans hR⟩

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ is monic.
Proof: M, about 35 lines, one job with `natDegree_orthogonalPolynomial`: one private helper
proving monicity and `natDegree = k` together by two-step induction (`Nat.twoStepInduction`),
unfolding with `orthogonalPolynomial_zero`, `orthogonalPolynomial_one`,
`orthogonalPolynomial_add_two`; `Monic.mul`, `monic_X_sub_C`, `Monic.sub_of_left`,
`natDegree_mul'`, `natDegree_C_mul_le`. -/
theorem monic_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) : (orthogonalPolynomial μ k).Monic :=
  (monic_and_natDegree_orthogonalPolynomial μ k).1

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ has degree exactly
$k$.
Proof: M, about 35 lines, one job with `monic_orthogonalPolynomial` (the shared two-step
induction; see there). -/
theorem natDegree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).natDegree = k := by
  sorry

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ has degree $k$, as
`Polynomial.degree`.
Proof: S, about 3 lines. `degree_eq_natDegree` with `(monic_orthogonalPolynomial μ k).ne_zero`,
then `natDegree_orthogonalPolynomial`. -/
theorem degree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).degree = k := by
  sorry

/-- The off-diagonal recurrence coefficients are nonnegative: $\beta_k \ge 0$ for every measure
$\mu$ on $\mathbb{R}$ and every $k$.
Proof: S, about 8 lines. Cases on `k`: `measureReal_nonneg`; `div_nonneg` of two
`integral_nonneg` (`sq_nonneg`). -/
theorem jacobiBeta_nonneg (μ : Measure ℝ) (k : ℕ) : 0 ≤ jacobiBeta μ k := by
  sorry

/-- The orthogonal polynomial depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k$ moments, then $\pi_k(\mu) = \pi_k(\nu)$. No support
hypothesis: $\pi_k$ is a formula in integrals of polynomials of degree less than $2k$.
Proof: M, about 50 lines. Two-step induction; rewrite $\int x\,p(x)^2\,d\mu$ as the integral of
the polynomial $Xp^2$ (`eval_mul`, `eval_pow`, `eval_X`); degree bounds `natDegree_mul_le`,
`natDegree_pow_le` with `natDegree_orthogonalPolynomial`; `MatchesMoments.mono`. -/
theorem MatchesMoments.orthogonalPolynomial_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    orthogonalPolynomial μ k = orthogonalPolynomial ν k := by
  sorry

/-- The diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 2$ moments, then $\alpha_k(\mu) = \alpha_k(\nu)$.
Proof: S, about 15 lines. Unfold `jacobiAlpha`; `MatchesMoments.orthogonalPolynomial_eq` with
`MatchesMoments.mono`; the two integrals are of polynomials of degree at most $2k + 1$. -/
theorem MatchesMoments.jacobiAlpha_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 2)) :
    jacobiAlpha μ k = jacobiAlpha ν k := by
  sorry

/-- The off-diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 1$ moments, then $\beta_k(\mu) = \beta_k(\nu)$.
Proof: S, about 15 lines. Cases on `k`: $k = 0$ is `MatchesMoments.measureReal_univ_eq`; else
`MatchesMoments.orthogonalPolynomial_eq` at $k + 1$ and $k$ with `MatchesMoments.mono`. -/
theorem MatchesMoments.jacobiBeta_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 1)) :
    jacobiBeta μ k = jacobiBeta ν k := by
  sorry

/-- The Jacobi matrix depends only on the moments: if two measures $\mu$, $\nu$ on $\mathbb{R}$
match their first $2k$ moments, then $\mathbf{J}_k(\mu) = \mathbf{J}_k(\nu)$.
Proof: S, about 20 lines. `ext i j`; unfold `jacobiMatrix`; `split_ifs`;
`MatchesMoments.jacobiAlpha_eq`, `MatchesMoments.jacobiBeta_eq` with `MatchesMoments.mono` (the
indices are less than $k$). -/
theorem MatchesMoments.jacobiMatrix_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    jacobiMatrix μ k = jacobiMatrix ν k := by
  sorry

/-- The Jacobi matrix $\mathbf{J}_k(\mu)$ of every measure $\mu$ on $\mathbb{R}$ is symmetric.
Proof: S, about 15 lines. `Matrix.IsHermitian.ext`; `star` is trivial over ℝ; unfold
`jacobiMatrix`, `split_ifs` with `omega` and `Fin.ext`. -/
theorem isHermitian_jacobiMatrix (μ : Measure ℝ) (k : ℕ) : (jacobiMatrix μ k).IsHermitian := by
  sorry

end Algebra

/-! ### Orthogonality, norms and uniqueness -/

section Orthogonality

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- The norm recurrence: for a finite measure $\mu$ supported in $[a, b]$ and every $k$,
$\|\pi_{k+1}\|^2 = \beta_{k+1}\|\pi_k\|^2$ in $L^2(\mu)$, also when $\|\pi_k\| = 0$.
[Gautschi2004, Theorem 1.27] (equation to check).
Proof: M, about 30 lines. Unfold `jacobiBeta`; if $\|\pi_k\|^2 \ne 0$, `div_mul_cancel₀`; else
$\beta_k = 0$, so $\pi_{k+1} = (X - \alpha_k)\pi_k$ (`orthogonalPolynomial_one`,
`orthogonalPolynomial_add_two`) and its squared norm is $\int\pi_k\cdot(X - \alpha_k)^2\pi_k = 0$
(`integral_eval_mul_eq_zero_of_integral_sq_eq_zero`); at $k = 0$, $\mu(\mathbb{R}) = 0$ gives
$\mu = 0$. -/
theorem integral_orthogonalPolynomial_succ_sq (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ =
      jacobiBeta μ (k + 1) * ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ := by
  sorry

/-- The defining property of $\alpha_k$: for a finite measure $\mu$ supported in $[a, b]$ and
every $k$, $\int(x - \alpha_k)\pi_k(x)^2\,d\mu = 0$, also when $\|\pi_k\| = 0$ ($x/0 = 0$).
Proof: S, about 20 lines. Unfold `jacobiAlpha`; `integral_sub`, `integral_mul_const`
(integrability `integrable_eval_of_ae_mem_Icc`); if $\|\pi_k\|^2 \ne 0$, `div_mul_cancel₀`; else
both integrals are $0$ (`integral_eval_mul_eq_zero_of_integral_sq_eq_zero` with
$r = X\pi_k$). -/
theorem integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (x - jacobiAlpha μ k) * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0 := by
  sorry

/-- Step (a) of the orthogonality induction: if $\pi_{k+1}$ and $\pi_k$ are orthogonal to the
lower degrees, then $\pi_{k+2}$ is orthogonal to every polynomial of degree less than $k$.
Proof: M, about 30 lines. Expand `orthogonalPolynomial_add_two`; `integral_sub`,
`integral_mul_const`; $\int\pi_{k+1}\,(Xr) = 0$ (`h1`, $\deg Xr < k + 1$),
$\int\pi_{k+1}r = 0$ (`h1`), $\int\pi_k r = 0$ (`h0`); integrability
`integrable_eval_of_ae_mem_Icc`; degrees by `degree_orthogonalPolynomial`. -/
private theorem integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1)))
    (h0 : IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k)) {r : ℝ[X]} (hr : r.degree < k) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * r.eval x ∂μ = 0 := by
  sorry

/-- Step (b) of the orthogonality induction: if $\pi_{k+1}$ is orthogonal to the lower degrees,
then $\int\pi_{k+2}\pi_{k+1}\,d\mu = 0$.
Proof: M, about 25 lines. Expand `orthogonalPolynomial_add_two`:
$\int(x - \alpha_{k+1})\pi_{k+1}^2 - \beta_{k+1}\int\pi_k\pi_{k+1}$; the first is
`integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero`, the second `h1` with
$\deg\pi_k = k$ (`degree_orthogonalPolynomial`). -/
private theorem integral_orthogonalPolynomial_add_two_mul_succ
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1))) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ (k + 1)).eval x ∂μ =
      0 := by
  sorry

/-- Step (c) of the orthogonality induction: if $\pi_{k+1}$ is orthogonal to the lower degrees,
then $\int\pi_{k+2}\pi_k\,d\mu = 0$.
Proof: M, about 35 lines. Expand `orthogonalPolynomial_add_two`; $X\pi_k = \pi_{k+1} +
(X\pi_k - \pi_{k+1})$ with the bracket of degree at most $k$ (both monic of degree $k + 1$,
`monic_orthogonalPolynomial`, `natDegree_orthogonalPolynomial`), so
$\int\pi_{k+1}\cdot X\pi_k = \|\pi_{k+1}\|^2$ by `h1`; $\int\pi_{k+1}\pi_k = 0$ by `h1`; then
$\|\pi_{k+1}\|^2 - \beta_{k+1}\|\pi_k\|^2 = 0$ by `integral_orthogonalPolynomial_succ_sq`. -/
private theorem integral_orthogonalPolynomial_add_two_mul_self
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1))) :
    ∫ x, (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ k).eval x ∂μ = 0 := by
  sorry

/-- Step (d) of the orthogonality induction: if $\pi_{k+1}$ and $\pi_k$ are orthogonal to the
lower degrees, so is $\pi_{k+2}$.
Proof: M, about 40 lines. For $\deg r < k + 2$ write $r = c\,\pi_{k+1} + c'\pi_k + r_0$ with
$\deg r_0 < k$ (`modByMonic_add_div` twice, `degree_modByMonic_lt`; the quotients are constants by
degree); `integral_add`, `integral_const_mul`; steps (a), (b) and (c)
(`integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt`,
`integral_orthogonalPolynomial_add_two_mul_succ`,
`integral_orthogonalPolynomial_add_two_mul_self`). -/
private theorem isOrthogonalPolynomial_orthogonalPolynomial_add_two
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {k : ℕ}
    (h1 : IsOrthogonalPolynomial μ (k + 1) (orthogonalPolynomial μ (k + 1)))
    (h0 : IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k)) :
    IsOrthogonalPolynomial μ (k + 2) (orthogonalPolynomial μ (k + 2)) := by
  sorry

/-- **Existence of the orthogonal polynomials**: for a finite measure $\mu$ supported in
$[a, b]$ and every $k$, the monic polynomial $\pi_k$ of degree $k$ is orthogonal in $L^2(\mu)$
to every real polynomial of degree less than $k$. No nondegeneracy is needed: past the number of
support points, $\pi_k$ vanishes on the support. [Gautschi2004, Theorems 1.6 and 1.27]
(which of Theorems 1.6–1.8 states existence is to check); there for $k$ below the number of
support points.
Proof: S, about 20 lines. `Nat.twoStepInduction`; $k = 0$ is vacuous (`degree_lt_zero`…, $r = 0$);
$k = 1$: $r = C\,c$ (`eq_C_of_degree_le_zero`) and $\int(x - \alpha_0)\,c = 0$ from
`integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero` at $0$ ($\pi_0 = 1$); the step is
`isOrthogonalPolynomial_orthogonalPolynomial_add_two`.
Result: orthogonal-polynomial-existence -/
theorem isOrthogonalPolynomial_orthogonalPolynomial (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsOrthogonalPolynomial μ k (orthogonalPolynomial μ k) := by
  sorry

/-- The norms as products of the coefficients: for a finite measure $\mu$ supported in $[a, b]$
and every $k$, $\|\pi_k\|^2 = \beta_0\beta_1\cdots\beta_k$ in $L^2(\mu)$, with
$\beta_0 = \mu(\mathbb{R})$. [Gautschi2004, Theorem 1.27] (equation to check).
Proof: S, about 15 lines. Induction on `k`; $k = 0$: $\int 1\,d\mu = \mu(\mathbb{R})$
(`integral_const`, `jacobiBeta_zero`); the step is `integral_orthogonalPolynomial_succ_sq` with
`Finset.prod_range_succ`. -/
theorem integral_orthogonalPolynomial_sq_eq_prod (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = ∏ i ∈ Finset.range (k + 1), jacobiBeta μ i := by
  sorry

/-- The off-diagonal entry as an integral: for a finite measure $\mu$ supported in $[a, b]$ and
every $k$, $\int x\,\pi_k(x)\pi_{k+1}(x)\,d\mu = \|\pi_{k+1}\|^2$, since
$x\pi_k = \pi_{k+1} + {}$(lower degree).
Proof: M, about 35 lines. $x\pi_k = \pi_{k+1} + \alpha_k\pi_k + \beta_k\pi_{k-1}$ from
`orthogonalPolynomial_one` / `orthogonalPolynomial_add_two` (cases $k = 0$, $k + 1$);
`integral_add`; `isOrthogonalPolynomial_orthogonalPolynomial` at $k + 1$ against $\pi_k$ and
$\pi_{k-1}$ (`degree_orthogonalPolynomial`). -/
theorem integral_mul_orthogonalPolynomial_mul_orthogonalPolynomial_succ
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, x * (orthogonalPolynomial μ k).eval x * (orthogonalPolynomial μ (k + 1)).eval x ∂μ =
      ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ := by
  sorry

/-- Definiteness is positivity of the last norm: a finite measure $\mu$ supported in $[a, b]$ is
positive definite on the polynomials of degree at most $k$ exactly when
$\int\pi_k^2\,d\mu > 0$ (the norms vanish from the first zero one on).
Proof: M, about 40 lines. ⇒: take $p = \pi_k$ (`monic_orthogonalPolynomial`,
`degree_orthogonalPolynomial`). ⇐: the norms are positive for $j \le k$ (contrapositive of
`integral_orthogonalPolynomial_succ_sq` by induction); for $p \ne 0$ of degree $d \le k$,
$p = c\,\pi_d + r$ with $c$ the leading coefficient and $\deg r < d$, and
$\int p^2 = c^2\|\pi_d\|^2 + \int r^2$ by `isOrthogonalPolynomial_orthogonalPolynomial`. -/
theorem isMomentPosDef_succ_iff (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    IsMomentPosDef μ (k + 1) ↔ 0 < ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ := by
  sorry

/-- **Uniqueness of the monic orthogonal polynomial**: if a finite measure $\mu$ supported in
$[a, b]$ is positive definite on the polynomials of degree less than $k$, then every monic real
polynomial $p$ of degree $k$ orthogonal in $L^2(\mu)$ to the polynomials of degree less than $k$
is $\pi_k$. [Gautschi2004, Theorem 1.6] (locator to check).
Proof: M, about 25 lines. $d = p - \pi_k$ has $\deg d < k$ (`degree_sub_lt_left`, both monic of
degree $k$); $\int d^2 = \int d\,p - \int d\,\pi_k = 0$ by `hpo` and
`isOrthogonalPolynomial_orthogonalPolynomial`; definiteness `h` gives $d = 0$. -/
theorem IsMomentPosDef.eq_orthogonalPolynomial {k : ℕ} (h : IsMomentPosDef μ k)
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p : ℝ[X]} (hp : p.Monic) (hpk : p.natDegree = k)
    (hpo : IsOrthogonalPolynomial μ k p) : p = orthogonalPolynomial μ k := by
  sorry

end Orthogonality

end NLAlib
