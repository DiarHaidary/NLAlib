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
    (orthogonalPolynomial μ k).natDegree = k :=
  (monic_and_natDegree_orthogonalPolynomial μ k).2

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ has degree $k$, as
`Polynomial.degree`.
Proof: S, about 3 lines. `degree_eq_natDegree` with `(monic_orthogonalPolynomial μ k).ne_zero`,
then `natDegree_orthogonalPolynomial`. -/
theorem degree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).degree = k := by
  rw [degree_eq_natDegree (monic_orthogonalPolynomial μ k).ne_zero,
    natDegree_orthogonalPolynomial]

/-- $X\pi_k - \pi_{k+1}$ has degree at most $k$: both are monic of degree $k + 1$. -/
private theorem degree_X_mul_sub_orthogonalPolynomial_succ_lt (μ : Measure ℝ) (k : ℕ) :
    (X * orthogonalPolynomial μ k - orthogonalPolynomial μ (k + 1)).degree <
      ((k + 1 : ℕ) : WithBot ℕ) := by
  have hXm : (X * orthogonalPolynomial μ k).Monic := monic_X.mul (monic_orthogonalPolynomial μ k)
  have hXd : (X * orthogonalPolynomial μ k).degree = ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_X, degree_orthogonalPolynomial]; norm_cast; omega
  exact hXd ▸ degree_sub_lt_left (by rw [hXd, degree_orthogonalPolynomial]) hXm.ne_zero
    (by rw [hXm.leadingCoeff, (monic_orthogonalPolynomial μ _).leadingCoeff])

/-- The off-diagonal recurrence coefficients are nonnegative: $\beta_k \ge 0$ for every measure
$\mu$ on $\mathbb{R}$ and every $k$.
Proof: S, about 8 lines. Cases on `k`: `measureReal_nonneg`; `div_nonneg` of two
`integral_nonneg` (`sq_nonneg`). -/
theorem jacobiBeta_nonneg (μ : Measure ℝ) (k : ℕ) : 0 ≤ jacobiBeta μ k := by
  cases k with
  | zero =>
      change 0 ≤ μ.real Set.univ
      exact measureReal_nonneg
  | succ k =>
      change 0 ≤ (∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ
      exact div_nonneg (integral_nonneg fun x => sq_nonneg _)
        (integral_nonneg fun x => sq_nonneg _)

/-- Matching moments transfer the squared norm of $\pi_j(\mu)$, a polynomial of degree $2j$. -/
private theorem MatchesMoments.integral_orthogonalPolynomial_sq_eq {N j : ℕ}
    (h : MatchesMoments μ ν N) (hj : 2 * j < N) :
    ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ =
      ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂ν := by
  have hsq := h (orthogonalPolynomial μ j ^ 2) (by
    rw [degree_eq_natDegree ((monic_orthogonalPolynomial μ j).pow 2).ne_zero, natDegree_pow,
      natDegree_orthogonalPolynomial]
    exact_mod_cast hj)
  simpa only [eval_pow] using hsq

/-- If $\pi_j(\mu) = \pi_j(\nu)$ and the first $2j + 2$ moments match, then
$\alpha_j(\mu) = \alpha_j(\nu)$: both integrals are of polynomials of degree at most $2j + 1$. -/
private theorem MatchesMoments.jacobiAlpha_eq_of_eq {N j : ℕ} (h : MatchesMoments μ ν N)
    (hj : 2 * j + 1 < N) (hp : orthogonalPolynomial μ j = orthogonalPolynomial ν j) :
    jacobiAlpha μ j = jacobiAlpha ν j := by
  have hm := (monic_orthogonalPolynomial μ j).pow 2
  have hx := h (X * orthogonalPolynomial μ j ^ 2) (by
    rw [degree_eq_natDegree (monic_X.mul hm).ne_zero, monic_X.natDegree_mul hm, natDegree_X,
      natDegree_pow, natDegree_orthogonalPolynomial]
    exact_mod_cast (by omega : 1 + 2 * j < N))
  simp only [eval_mul, eval_X, eval_pow] at hx
  rw [jacobiAlpha, jacobiAlpha, ← hp, hx, h.integral_orthogonalPolynomial_sq_eq (by omega)]

/-- If $\pi_{j+1}$ and $\pi_j$ of $\mu$ and $\nu$ agree and the first $2j + 3$ moments match,
then $\beta_{j+1}(\mu) = \beta_{j+1}(\nu)$. -/
private theorem MatchesMoments.jacobiBeta_succ_eq_of_eq {N j : ℕ} (h : MatchesMoments μ ν N)
    (hj : 2 * (j + 1) < N) (hp1 : orthogonalPolynomial μ (j + 1) = orthogonalPolynomial ν (j + 1))
    (hp : orthogonalPolynomial μ j = orthogonalPolynomial ν j) :
    jacobiBeta μ (j + 1) = jacobiBeta ν (j + 1) := by
  simp only [jacobiBeta]
  rw [← hp1, ← hp, h.integral_orthogonalPolynomial_sq_eq hj,
    h.integral_orthogonalPolynomial_sq_eq (by omega)]

/-- The orthogonal polynomial depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k$ moments, then $\pi_k(\mu) = \pi_k(\nu)$. No support
hypothesis: $\pi_k$ is a formula in integrals of polynomials of degree less than $2k$.
Proof: M, about 50 lines. Two-step induction; rewrite $\int x\,p(x)^2\,d\mu$ as the integral of
the polynomial $Xp^2$ (`eval_mul`, `eval_pow`, `eval_X`); degree bounds `natDegree_mul_le`,
`natDegree_pow_le` with `natDegree_orthogonalPolynomial`; `MatchesMoments.mono`. -/
theorem MatchesMoments.orthogonalPolynomial_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    orthogonalPolynomial μ k = orthogonalPolynomial ν k := by
  revert h
  induction k using Nat.twoStepInduction with
  | zero => intro _; rfl
  | one =>
    intro h
    rw [orthogonalPolynomial_one, orthogonalPolynomial_one, h.jacobiAlpha_eq_of_eq (by omega) rfl]
  | more n ihn ih1 =>
    intro h
    have hp := ihn (h.mono (by omega))
    have hp1 := ih1 (h.mono (by omega))
    rw [orthogonalPolynomial_add_two μ n, orthogonalPolynomial_add_two ν n,
      h.jacobiAlpha_eq_of_eq (by omega) hp1, h.jacobiBeta_succ_eq_of_eq (by omega) hp1 hp, hp1, hp]

/-- The diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 2$ moments, then $\alpha_k(\mu) = \alpha_k(\nu)$.
Proof: S, about 15 lines. Unfold `jacobiAlpha`; `MatchesMoments.orthogonalPolynomial_eq` with
`MatchesMoments.mono`; the two integrals are of polynomials of degree at most $2k + 1$. -/
theorem MatchesMoments.jacobiAlpha_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 2)) :
    jacobiAlpha μ k = jacobiAlpha ν k :=
  h.jacobiAlpha_eq_of_eq (by omega) (MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega)))

/-- The off-diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 1$ moments, then $\beta_k(\mu) = \beta_k(\nu)$.
Proof: S, about 15 lines. Cases on `k`: $k = 0$ is `MatchesMoments.measureReal_univ_eq`; else
`MatchesMoments.orthogonalPolynomial_eq` at $k + 1$ and $k$ with `MatchesMoments.mono`. -/
theorem MatchesMoments.jacobiBeta_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 1)) :
    jacobiBeta μ k = jacobiBeta ν k := by
  rcases k with _ | k
  · exact h.measureReal_univ_eq (by omega)
  · exact h.jacobiBeta_succ_eq_of_eq (by omega)
      (MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega)))
      (MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega)))

/-- The Jacobi matrix depends only on the moments: if two measures $\mu$, $\nu$ on $\mathbb{R}$
match their first $2k$ moments, then $\mathbf{J}_k(\mu) = \mathbf{J}_k(\nu)$.
Proof: S, about 20 lines. `ext i j`; unfold `jacobiMatrix`; `split_ifs`;
`MatchesMoments.jacobiAlpha_eq`, `MatchesMoments.jacobiBeta_eq` with `MatchesMoments.mono` (the
indices are less than $k$). -/
theorem MatchesMoments.jacobiMatrix_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k)) :
    jacobiMatrix μ k = jacobiMatrix ν k := by
  ext i j
  simp only [jacobiMatrix, Matrix.of_apply]
  split_ifs with h1 h2 h3
  · exact MatchesMoments.jacobiAlpha_eq (h.mono (by omega))
  · rw [MatchesMoments.jacobiBeta_eq (h.mono (by omega))]
  · rw [MatchesMoments.jacobiBeta_eq (h.mono (by omega))]
  · rfl

/-- The Jacobi matrix $\mathbf{J}_k(\mu)$ of every measure $\mu$ on $\mathbb{R}$ is symmetric.
Proof: S, about 15 lines. `Matrix.IsHermitian.ext`; `star` is trivial over ℝ; unfold
`jacobiMatrix`, `split_ifs` with `omega` and `Fin.ext`. -/
theorem isHermitian_jacobiMatrix (μ : Measure ℝ) (k : ℕ) : (jacobiMatrix μ k).IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [jacobiMatrix, Matrix.of_apply, star_trivial]
  by_cases h : i = j
  · subst h; rfl
  · have hj : ¬(j = i) := fun hc => h hc.symm
    by_cases h2 : (j : ℕ) = (i : ℕ) + 1
    · have h3 : (i : ℕ) ≠ (j : ℕ) + 1 := by omega
      rw [if_neg hj, if_neg h, if_pos h2, if_neg h3, if_pos h2]
    · by_cases h3 : (i : ℕ) = (j : ℕ) + 1
      · rw [if_neg hj, if_neg h2, if_pos h3, if_neg h, if_pos h3]
      · rw [if_neg hj, if_neg h2, if_neg h3, if_neg h, if_neg h3, if_neg h2]

end Algebra

/-! ### Orthogonality, norms and uniqueness -/

section Orthogonality

variable {μ : Measure ℝ} [IsFiniteMeasure μ] {a b : ℝ}

/-- A polynomial multiple of a polynomial of norm zero has norm zero: for a finite measure $\mu$
supported in $[a, b]$, a real polynomial $p$ with $\int p^2\,d\mu = 0$ and every real polynomial
$q$, $\int (qp)^2\,d\mu = 0$. The degenerate branch of the norm recurrence. -/
private theorem integral_eval_mul_sq_eq_zero_of_integral_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) {p q : ℝ[X]}
    (hp : ∫ x, p.eval x ^ 2 ∂μ = 0) : ∫ x, (q * p).eval x ^ 2 ∂μ = 0 := by
  have he : ∀ x, (q * p).eval x ^ 2 = p.eval x * (q ^ 2 * p).eval x := by
    intro x
    simp only [eval_mul, eval_pow]
    ring
  simp only [he]
  exact integral_eval_mul_eq_zero_of_integral_sq_eq_zero hμ hp (q ^ 2 * p)

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
  rcases eq_or_ne (∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) 0 with h0 | h0
  · -- degenerate: $\|\pi_k\|^2 = 0$ gives $\beta_{k+1} = 0$ and $\pi_{k+1} = (X - \alpha_k)\pi_k$
    have hb : jacobiBeta μ (k + 1) = 0 := by
      simp only [jacobiBeta]
      rw [h0, div_zero]
    rw [hb, zero_mul]
    have hp : orthogonalPolynomial μ (k + 1) =
        (X - C (jacobiAlpha μ k)) * orthogonalPolynomial μ k := by
      cases k with
      | zero => rw [orthogonalPolynomial_one, orthogonalPolynomial_zero, mul_one]
      | succ j =>
          have hbj : jacobiBeta μ (j + 1) = 0 := by
            simp only [jacobiBeta]
            rw [h0, zero_div]
          rw [orthogonalPolynomial_add_two μ j]
          simp only [hbj, Polynomial.C_0, zero_mul, sub_zero]
    rw [hp]
    exact integral_eval_mul_sq_eq_zero_of_integral_sq_eq_zero hμ h0
  · rw [jacobiBeta, div_mul_cancel₀ _ h0]

/-- The defining property of $\alpha_k$: for a finite measure $\mu$ supported in $[a, b]$ and
every $k$, $\int(x - \alpha_k)\pi_k(x)^2\,d\mu = 0$, also when $\|\pi_k\| = 0$ ($x/0 = 0$).
Proof: S, about 20 lines. Unfold `jacobiAlpha`; `integral_sub`, `integral_mul_const`
(integrability `integrable_eval_of_ae_mem_Icc`); if $\|\pi_k\|^2 \ne 0$, `div_mul_cancel₀`; else
both integrals are $0$ (`integral_eval_mul_eq_zero_of_integral_sq_eq_zero` with
$r = X\pi_k$). -/
theorem integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (x - jacobiAlpha μ k) * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0 := by
  set π := orthogonalPolynomial μ k
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hx : ∀ x, x * π.eval x ^ 2 = π.eval x * (X * π).eval x := fun x => by
    simp only [eval_mul, eval_X]
    ring
  have himul : Integrable (fun x => x * π.eval x ^ 2) μ :=
    (hint (π * (X * π))).congr (ae_of_all μ fun x => by simp only [hx, eval_mul])
  have hisq : Integrable (fun x => π.eval x ^ 2) μ :=
    (hint (π ^ 2)).congr (ae_of_all μ fun _ => eval_pow 2)
  simp only [sub_mul]
  rw [integral_sub himul (hisq.const_mul _), integral_const_mul]
  rcases eq_or_ne (∫ x, π.eval x ^ 2 ∂μ) 0 with hD | hD
  · -- degenerate case: the norm is $0$, so both integrals vanish
    rw [hD, mul_zero, sub_zero, integral_congr_ae (ae_of_all μ hx)]
    exact integral_eval_mul_eq_zero_of_integral_sq_eq_zero hμ hD _
  · rw [jacobiAlpha, div_mul_cancel₀ _ hD, sub_self]

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
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hXr : (X * r).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    by_cases hr0 : r = 0
    · subst hr0; simp
    · have hnr : r.natDegree < k := (natDegree_lt_iff_degree_lt hr0).mpr hr
      rw [← natDegree_lt_iff_degree_lt (mul_ne_zero X_ne_zero hr0), natDegree_X_mul hr0]
      omega
  have hpoly : ∀ x : ℝ, (orthogonalPolynomial μ (k + 2)).eval x * r.eval x =
      (orthogonalPolynomial μ (k + 1) * (X * r) -
        C (jacobiAlpha μ (k + 1)) * (orthogonalPolynomial μ (k + 1) * r) -
        C (jacobiBeta μ (k + 1)) * (orthogonalPolynomial μ k * r)).eval x := by
    intro x
    rw [orthogonalPolynomial_add_two]
    simp only [eval_mul, eval_sub, eval_X, eval_C, sub_mul]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_sub]
  rw [integral_sub, integral_sub]
  · have hX := h1 _ hXr
    simp only [eval_mul, eval_C, integral_const_mul] at hX ⊢
    rw [hX, h1 r (hr.trans_le (by exact_mod_cast k.le_succ)), h0 r hr]
    ring
  all_goals fun_prop

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
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have key : ∀ x : ℝ,
      (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ (k + 1)).eval x =
      ((X - C (jacobiAlpha μ (k + 1))) * orthogonalPolynomial μ (k + 1) ^ 2 -
        C (jacobiBeta μ (k + 1)) *
          (orthogonalPolynomial μ (k + 1) * orthogonalPolynomial μ k)).eval x := by
    intro x
    rw [orthogonalPolynomial_add_two]
    simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ key)]
  simp only [eval_sub]
  rw [integral_sub (hint _) (hint _)]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, integral_const_mul]
  rw [integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero hμ (k + 1),
    h1 _ (by rw [degree_orthogonalPolynomial]; exact_mod_cast k.lt_succ_self), mul_zero, sub_zero]

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
  set P := orthogonalPolynomial μ
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hpoly : ∀ x, (P (k + 2)).eval x * (P k).eval x =
      (P (k + 1) * (X * P k - P (k + 1)) + P (k + 1) ^ 2 -
        C (jacobiAlpha μ (k + 1)) * (P (k + 1) * P k) -
        C (jacobiBeta μ (k + 1)) * P k ^ 2).eval x := by
    intro x
    rw [show P (k + 2) = _ from orthogonalPolynomial_add_two μ k]
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_add, eval_sub]
  rw [integral_sub, integral_sub, integral_add]
  · simp only [eval_mul, eval_pow, eval_C, integral_const_mul]
    rw [h1 _ (degree_X_mul_sub_orthogonalPolynomial_succ_lt μ k),
      h1 (P k) (by rw [degree_orthogonalPolynomial]; exact_mod_cast k.lt_succ_self),
      integral_orthogonalPolynomial_succ_sq hμ k]
    ring
  all_goals fun_prop

/-- Division by a monic polynomial, one degree at a time: if $p$ is monic of degree $d$ and
$\deg r < d + 1$, then $r = c\,p + r'$ for a constant $c$ with $\deg r' < d$. -/
private theorem exists_eq_C_mul_add_of_degree_lt {d : ℕ} {p r : ℝ[X]} (hp : p.Monic)
    (hpd : p.degree = (d : WithBot ℕ)) (hr : r.degree < (d + 1 : WithBot ℕ)) :
    ∃ (c : ℝ) (r' : ℝ[X]), r = C c * p + r' ∧ r'.degree < (d : WithBot ℕ) := by
  have hmod : r %ₘ p + p * (r /ₘ p) = r := modByMonic_add_div r p
  by_cases hq : r /ₘ p = 0
  · rw [hq, mul_zero, add_zero] at hmod
    refine ⟨0, r %ₘ p, ?_, ?_⟩
    · simpa only [C_0, zero_mul, zero_add] using hmod.symm
    · rw [← hpd]
      exact degree_modByMonic_lt r hp
  · have hle : p.degree ≤ r.degree := by
      by_contra h
      exact hq ((divByMonic_eq_zero_iff hp).2 (not_le.1 h))
    have heq := degree_add_divByMonic hp hle
    have hn : (r /ₘ p).natDegree = 0 := by
      rw [hpd, degree_eq_natDegree hq, ← Nat.cast_add] at heq
      have hlt : (d + (r /ₘ p).natDegree : ℕ) < d + 1 := by exact_mod_cast heq.trans_lt hr
      omega
    have hconst : r /ₘ p = C ((r /ₘ p).coeff 0) := eq_C_of_natDegree_le_zero (by omega)
    refine ⟨(r /ₘ p).coeff 0, r %ₘ p, ?_, ?_⟩
    · rw [hconst, mul_comm p (C _), add_comm] at hmod
      exact hmod.symm
    · rw [← hpd]
      exact degree_modByMonic_lt r hp

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
  intro r hr
  -- split off the multiples of $\pi_{k+1}$ and of $\pi_k$: $r = c_1\pi_{k+1} + c_0\pi_k + r_0$
  obtain ⟨c₁, r₁, hr₁, hdeg₁⟩ := exists_eq_C_mul_add_of_degree_lt
    (monic_orthogonalPolynomial μ (k + 1)) (degree_orthogonalPolynomial μ (k + 1)) hr
  obtain ⟨c₀, r₀, hr₀, hdeg₀⟩ := exists_eq_C_mul_add_of_degree_lt
    (monic_orthogonalPolynomial μ k) (degree_orthogonalPolynomial μ k) hdeg₁
  have hint := integrable_eval_of_ae_mem_Icc hμ
  set P := orthogonalPolynomial μ
  have hsplit : ∀ x, (P (k + 2)).eval x * r.eval x =
      (C c₁ * (P (k + 2) * P (k + 1)) + C c₀ * (P (k + 2) * P k) + P (k + 2) * r₀).eval x := by
    intro x
    rw [hr₁, hr₀]
    simp only [eval_add, eval_mul, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ hsplit)]
  simp only [eval_add]
  rw [integral_add, integral_add]
  · -- steps (a), (b) and (c)
    simp only [eval_mul, eval_C, integral_const_mul]
    rw [integral_orthogonalPolynomial_add_two_mul_succ hμ h1,
      integral_orthogonalPolynomial_add_two_mul_self hμ h1,
      integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt hμ h1 h0 hdeg₀]
    ring
  all_goals fun_prop

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
  induction k using Nat.twoStepInduction with
  | zero =>
    intro r hr
    rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, degree_eq_bot] at hr
    simp only [hr, eval_zero, mul_zero, integral_zero]
  | one =>
    intro r hr
    rcases eq_or_ne r 0 with rfl | hr0
    · simp only [eval_zero, mul_zero, integral_zero]
    · have hrC : r = Polynomial.C (r.coeff 0) :=
        Polynomial.eq_C_of_natDegree_le_zero
          (Nat.lt_one_iff.mp ((Polynomial.natDegree_lt_iff_degree_lt (n := 1) hr0).mpr hr)).le
      rw [hrC, orthogonalPolynomial_one]
      simp only [eval_sub, eval_X, eval_C]
      have h := integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero hμ 0
      rw [orthogonalPolynomial_zero] at h
      simp only [Polynomial.eval_one, one_pow, mul_one] at h
      rw [integral_mul_const _ _, h, zero_mul]
  | more _ h0 h1 =>
    exact isOrthogonalPolynomial_orthogonalPolynomial_add_two hμ h1 h0

/-- The norms as products of the coefficients: for a finite measure $\mu$ supported in $[a, b]$
and every $k$, $\|\pi_k\|^2 = \beta_0\beta_1\cdots\beta_k$ in $L^2(\mu)$, with
$\beta_0 = \mu(\mathbb{R})$. [Gautschi2004, Theorem 1.27] (equation to check).
Proof: S, about 15 lines. Induction on `k`; $k = 0$: $\int 1\,d\mu = \mu(\mathbb{R})$
(`integral_const`, `jacobiBeta_zero`); the step is `integral_orthogonalPolynomial_succ_sq` with
`Finset.prod_range_succ`. -/
theorem integral_orthogonalPolynomial_sq_eq_prod (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a b) (k : ℕ) :
    ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ = ∏ i ∈ Finset.range (k + 1), jacobiBeta μ i := by
  induction k with
  | zero =>
    simp only [orthogonalPolynomial_zero, eval_one, one_pow, integral_const, jacobiBeta_zero,
      Finset.prod_range_succ, Finset.range_zero, Finset.prod_empty, one_mul, smul_eq_mul, mul_one]
  | succ k ih =>
    rw [integral_orthogonalPolynomial_succ_sq hμ k, Finset.prod_range_succ, ih, mul_comm]

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
  have hint := integrable_eval_of_ae_mem_Icc hμ
  set P := orthogonalPolynomial μ
  have hpoly : ∀ x, x * (P k).eval x * (P (k + 1)).eval x =
      (P (k + 1) * (X * P k - P (k + 1)) + P (k + 1) ^ 2).eval x := by
    intro x
    simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_add]
  rw [integral_add (hint _) (hint _)]
  simp only [eval_mul, eval_pow]
  rw [isOrthogonalPolynomial_orthogonalPolynomial hμ (k + 1) _
    (degree_X_mul_sub_orthogonalPolynomial_succ_lt μ k), zero_add]

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
  refine ⟨fun h => h _ (monic_orthogonalPolynomial μ k).ne_zero ?_, fun hpos p hp0 hpdeg => ?_⟩
  · rw [degree_orthogonalPolynomial]
    exact_mod_cast k.lt_succ_self
  have hint := integrable_eval_of_ae_mem_Icc hμ
  -- the norms of $\pi_j$, $j \le k$, are positive, as $\|\pi_{j+1}\|^2 = \beta_{j+1}\|\pi_j\|^2$
  have hlow : ∀ j ≤ k, 0 < ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ := fun j hj =>
    Nat.decreasingInduction (motive := fun j _ => 0 < ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ)
      (fun j _ ih => pos_of_mul_pos_right (integral_orthogonalPolynomial_succ_sq hμ j ▸ ih)
        (jacobiBeta_nonneg μ (j + 1))) hpos hj
  -- $p = c\,\pi_n + r$ with $n = \deg p$, $c$ the leading coefficient and $\deg r < n$
  set π := orthogonalPolynomial μ p.natDegree
  set c := p.leadingCoeff
  set r := p - C c * π
  have hc : c ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  have hrdeg : r.degree < p.natDegree := by
    rw [← degree_eq_natDegree hp0]
    refine degree_sub_lt_left ?_ hp0 ?_
    · rw [degree_C_mul hc, degree_orthogonalPolynomial, degree_eq_natDegree hp0]
    · rw [leadingCoeff_mul, leadingCoeff_C, (monic_orthogonalPolynomial μ _).leadingCoeff, mul_one]
  have hpoly : ∀ x, p.eval x ^ 2 = (C (c ^ 2) * π ^ 2 + C (2 * c) * (π * r) + r ^ 2).eval x := by
    intro x
    simp only [r, eval_add, eval_sub, eval_mul, eval_pow, eval_C]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly)]
  simp only [eval_add]
  rw [integral_add, integral_add]
  · simp only [eval_mul, eval_pow, eval_C, integral_const_mul]
    rw [isOrthogonalPolynomial_orthogonalPolynomial hμ _ r hrdeg, mul_zero, add_zero]
    have hdk : p.natDegree ≤ k := Nat.lt_succ_iff.mp ((natDegree_lt_iff_degree_lt hp0).mpr hpdeg)
    exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) (hlow _ hdk))
      (integral_nonneg fun x => sq_nonneg _)
  all_goals fun_prop

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
  set π := orthogonalPolynomial μ k
  have hint := integrable_eval_of_ae_mem_Icc hμ
  have hdeg : (p - π).degree < k := by
    have h1 : p.degree = k := by rw [degree_eq_natDegree hp.ne_zero, hpk]
    exact h1 ▸ degree_sub_lt_left (by rw [h1, degree_orthogonalPolynomial]) hp.ne_zero
      (by rw [hp.leadingCoeff, (monic_orthogonalPolynomial μ k).leadingCoeff])
  by_contra hne
  refine (h _ (sub_ne_zero.mpr hne) hdeg).ne' ?_
  calc ∫ x, (p - π).eval x ^ 2 ∂μ
      = ∫ x, p.eval x * (p - π).eval x - π.eval x * (p - π).eval x ∂μ := by
        congr 1; ext x; simp only [eval_sub]; ring
    _ = 0 := by
        rw [integral_sub (by simpa only [eval_mul] using hint (p * (p - π)))
          (by simpa only [eval_mul] using hint (π * (p - π))),
          hpo _ hdeg, isOrthogonalPolynomial_orthogonalPolynomial hμ k _ hdeg, sub_zero]

end Orthogonality

end NLAlib
