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
  induction k using Nat.twoStepInduction with
  | zero => simp [orthogonalPolynomial_zero]
  | one => rw [orthogonalPolynomial_one, natDegree_X_sub_C]
  | more n h0 h1 =>
      -- `π_{n+1} ≠ 0`, since its `natDegree` is positive.
      have hne : orthogonalPolynomial μ (n + 1) ≠ 0 := by
        intro h
        rw [h] at h1
        simp at h1
      have hA : ((X - C (jacobiAlpha μ (n + 1))) * orthogonalPolynomial μ (n + 1)).natDegree
          = n + 2 := by
        rw [natDegree_mul (monic_X_sub_C _).ne_zero hne, natDegree_X_sub_C, h1]
        omega
      have hB : (C (jacobiBeta μ (n + 1)) * orthogonalPolynomial μ n).natDegree ≤ n := by
        have hB' := natDegree_mul_le (p := C (jacobiBeta μ (n + 1)))
          (q := orthogonalPolynomial μ n)
        rwa [natDegree_C, zero_add, h0] at hB'
      rw [orthogonalPolynomial_add_two, natDegree_sub_eq_left_of_natDegree_lt (by omega), hA]

/-- The orthogonal polynomial $\pi_k$ of every measure $\mu$ on $\mathbb{R}$ has degree $k$, as
`Polynomial.degree`.
Proof: S, about 3 lines. `degree_eq_natDegree` with `(monic_orthogonalPolynomial μ k).ne_zero`,
then `natDegree_orthogonalPolynomial`. -/
theorem degree_orthogonalPolynomial (μ : Measure ℝ) (k : ℕ) :
    (orthogonalPolynomial μ k).degree = k := by
  rw [degree_eq_natDegree (monic_orthogonalPolynomial μ k).ne_zero,
    natDegree_orthogonalPolynomial]

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
    have hx0 : ∫ x, x ∂μ = ∫ x, x ∂ν := by
      simpa only [eval_X] using h X (by rw [degree_X]; norm_num)
    have h10 : ∫ x, (1 : ℝ) ∂μ = ∫ x, (1 : ℝ) ∂ν := by
      simpa only [eval_C, integral_const, smul_eq_mul, mul_one] using
        h (C 1) (by rw [degree_C one_ne_zero]; norm_num)
    have hα : jacobiAlpha μ 0 = jacobiAlpha ν 0 := by
      unfold jacobiAlpha
      rw [orthogonalPolynomial_zero, orthogonalPolynomial_zero]
      simp only [eval_one, one_pow, mul_one]
      rw [hx0, h10]
    rw [orthogonalPolynomial_one, orthogonalPolynomial_one, hα]
  | more n ihn ih1 =>
    intro h
    have hp : orthogonalPolynomial μ n = orthogonalPolynomial ν n := ihn (h.mono (by omega))
    have hp1 : orthogonalPolynomial μ (n + 1) = orthogonalPolynomial ν (n + 1) :=
      ih1 (h.mono (by omega))
    have hd2 : ∀ j : ℕ, (orthogonalPolynomial ν j ^ 2).natDegree ≤ 2 * j := fun j =>
      natDegree_pow_le.trans_eq (by rw [natDegree_orthogonalPolynomial])
    have hlt : ∀ q : ℝ[X], q.natDegree < 2 * (n + 2) → q.degree < (2 * (n + 2) : ℕ) :=
      fun q hq => (degree_le_of_natDegree_le (Nat.le_refl _)).trans_lt (by exact_mod_cast hq)
    have hsq : ∀ j ≤ n + 1, ∫ x, (orthogonalPolynomial ν j).eval x ^ 2 ∂μ =
        ∫ x, (orthogonalPolynomial ν j).eval x ^ 2 ∂ν := by
      intro j hj
      have hd : (orthogonalPolynomial ν j ^ 2).natDegree < 2 * (n + 2) := by
        have := hd2 j; omega
      simpa only [eval_pow] using h _ (hlt _ hd)
    have hx : ∀ j ≤ n + 1, ∫ x, x * (orthogonalPolynomial ν j).eval x ^ 2 ∂μ =
        ∫ x, x * (orthogonalPolynomial ν j).eval x ^ 2 ∂ν := by
      intro j hj
      have h3 : (X * orthogonalPolynomial ν j ^ 2).natDegree ≤ 1 + 2 * j :=
        natDegree_mul_le.trans (by rw [natDegree_X]; have := hd2 j; omega)
      have hd : (X * orthogonalPolynomial ν j ^ 2).natDegree < 2 * (n + 2) := by
        have := h3; omega
      simpa only [eval_mul, eval_pow, eval_X] using h _ (hlt _ hd)
    have hα : jacobiAlpha μ (n + 1) = jacobiAlpha ν (n + 1) := by
      unfold jacobiAlpha
      rw [hp1, hx (n + 1) (by omega), hsq (n + 1) (by omega)]
    have hβ : jacobiBeta μ (n + 1) = jacobiBeta ν (n + 1) := by
      change (∫ x, (orthogonalPolynomial μ (n + 1)).eval x ^ 2 ∂μ) /
            ∫ x, (orthogonalPolynomial μ n).eval x ^ 2 ∂μ =
          (∫ x, (orthogonalPolynomial ν (n + 1)).eval x ^ 2 ∂ν) /
            ∫ x, (orthogonalPolynomial ν n).eval x ^ 2 ∂ν
      rw [hp1, hp, hsq (n + 1) (by omega), hsq n (by omega)]
    rw [orthogonalPolynomial_add_two μ n, orthogonalPolynomial_add_two ν n, hα, hβ, hp1, hp]

/-- The diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 2$ moments, then $\alpha_k(\mu) = \alpha_k(\nu)$.
Proof: S, about 15 lines. Unfold `jacobiAlpha`; `MatchesMoments.orthogonalPolynomial_eq` with
`MatchesMoments.mono`; the two integrals are of polynomials of degree at most $2k + 1$. -/
theorem MatchesMoments.jacobiAlpha_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 2)) :
    jacobiAlpha μ k = jacobiAlpha ν k := by
  have hp0 : orthogonalPolynomial μ k ≠ 0 := (monic_orthogonalPolynomial μ k).ne_zero
  have hk : (orthogonalPolynomial μ k).natDegree = k := natDegree_orthogonalPolynomial μ k
  have hp : orthogonalPolynomial μ k = orthogonalPolynomial ν k :=
    MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega))
  simp only [jacobiAlpha]
  rw [← hp]
  congr 1
  · have hd := h (X * orthogonalPolynomial μ k ^ 2) (by
      rw [degree_eq_natDegree (mul_ne_zero X_ne_zero (pow_ne_zero 2 hp0)),
        natDegree_mul X_ne_zero (pow_ne_zero 2 hp0), natDegree_X, natDegree_pow, hk]
      exact_mod_cast by omega)
    simp only [eval_mul, eval_X, eval_pow] at hd
    exact hd
  · have hd := h (orthogonalPolynomial μ k ^ 2) (by
      rw [degree_eq_natDegree (pow_ne_zero 2 hp0), natDegree_pow, hk]
      exact_mod_cast by omega)
    simp only [eval_pow] at hd
    exact hd

/-- The off-diagonal coefficient depends only on the moments: if two measures $\mu$, $\nu$ on
$\mathbb{R}$ match their first $2k + 1$ moments, then $\beta_k(\mu) = \beta_k(\nu)$.
Proof: S, about 15 lines. Cases on `k`: $k = 0$ is `MatchesMoments.measureReal_univ_eq`; else
`MatchesMoments.orthogonalPolynomial_eq` at $k + 1$ and $k$ with `MatchesMoments.mono`. -/
theorem MatchesMoments.jacobiBeta_eq {k : ℕ} (h : MatchesMoments μ ν (2 * k + 1)) :
    jacobiBeta μ k = jacobiBeta ν k := by
  rcases k with _ | k
  · simp only [jacobiBeta_zero]
    exact h.measureReal_univ_eq (by omega)
  · have hπ1 : orthogonalPolynomial μ (k + 1) = orthogonalPolynomial ν (k + 1) :=
      MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega))
    have hπ0 : orthogonalPolynomial μ k = orthogonalPolynomial ν k :=
      MatchesMoments.orthogonalPolynomial_eq (h.mono (by omega))
    have hd : ∀ j ≤ k + 1, ((orthogonalPolynomial μ j) ^ 2).degree < 2 * (k + 1) + 1 := by
      intro j hj
      rw [degree_eq_natDegree ((monic_orthogonalPolynomial μ j).pow 2).ne_zero, natDegree_pow,
        natDegree_orthogonalPolynomial]
      exact_mod_cast show 2 * j < 2 * (k + 1) + 1 by omega
    change (∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ =
      (∫ x, (orthogonalPolynomial ν (k + 1)).eval x ^ 2 ∂ν) /
      ∫ x, (orthogonalPolynomial ν k).eval x ^ 2 ∂ν
    have e1 : ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂μ =
        ∫ x, (orthogonalPolynomial μ (k + 1)).eval x ^ 2 ∂ν := by
      simpa only [eval_pow] using h ((orthogonalPolynomial μ (k + 1)) ^ 2) (hd (k + 1) le_rfl)
    have e0 : ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ =
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂ν := by
      simpa only [eval_pow] using h ((orthogonalPolynomial μ k) ^ 2) (hd k (by omega))
    rw [← hπ1, ← hπ0, e1, e0]

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
  have hα : jacobiAlpha μ k =
      (∫ x, x * (orthogonalPolynomial μ k).eval x ^ 2 ∂μ) /
        ∫ x, (orthogonalPolynomial μ k).eval x ^ 2 ∂μ := rfl
  set hp := orthogonalPolynomial μ k
  -- the two integrands are integrable, being evals of polynomials
  have himul : Integrable (fun x : ℝ => x * hp.eval x ^ 2) μ := by
    have h : (fun x : ℝ => x * hp.eval x ^ 2) = fun x => (X * hp * hp).eval x := by
      funext x; simp only [eval_mul, eval_X, pow_two, mul_assoc]
    rw [h]
    exact integrable_eval_of_ae_mem_Icc hμ _
  have hisq : Integrable (fun x : ℝ => hp.eval x ^ 2) μ := by
    have h : (fun x : ℝ => hp.eval x ^ 2) = fun x => (hp * hp).eval x := by
      funext x; simp only [eval_mul, pow_two]
    rw [h]
    exact integrable_eval_of_ae_mem_Icc hμ _
  have hsplit : ∀ c : ℝ, ∫ x, (x - c) * hp.eval x ^ 2 ∂μ =
      (∫ x, x * hp.eval x ^ 2 ∂μ) - c * ∫ x, hp.eval x ^ 2 ∂μ := by
    intro c
    simp only [sub_mul]
    rw [integral_sub himul (hisq.const_mul c), integral_const_mul]
  rcases eq_or_ne (∫ x, hp.eval x ^ 2 ∂μ) 0 with hD | hD
  · -- degenerate case: the norm is $0$, so both integrals vanish
    rw [hsplit (jacobiAlpha μ k), hD, mul_zero, sub_zero]
    have hN : ∫ x, x * hp.eval x ^ 2 ∂μ = ∫ x, hp.eval x * (X * hp).eval x ∂μ := by
      refine integral_congr_ae (ae_of_all μ fun x => ?_)
      simp only [eval_mul, eval_X]
      ring
    rw [hN]
    exact integral_eval_mul_eq_zero_of_integral_sq_eq_zero hμ hD (X * hp)
  · rw [hsplit (jacobiAlpha μ k), hα, div_mul_cancel₀ _ hD]
    ring

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
  have hsplit : ∀ p q : ℝ[X],
      ∫ x, (p - q).eval x ∂μ = ∫ x, p.eval x ∂μ - ∫ x, q.eval x ∂μ := by
    intro p q
    simp only [eval_sub]
    exact integral_sub (integrable_eval_of_ae_mem_Icc hμ p)
      (integrable_eval_of_ae_mem_Icc hμ q)
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
  have key1 : ∫ x, (orthogonalPolynomial μ (k + 1) * (X * r)).eval x ∂μ = 0 := by
    simpa only [eval_mul] using h1 (X * r) hXr
  have hI2 : ∫ x, (C (jacobiAlpha μ (k + 1)) *
      (orthogonalPolynomial μ (k + 1) * r)).eval x ∂μ = 0 := by
    simp only [eval_mul, eval_C, integral_const_mul]
    rw [h1 r (lt_of_lt_of_le hr (by exact_mod_cast Nat.le_succ k))]
    ring
  have hI3 : ∫ x, (C (jacobiBeta μ (k + 1)) *
      (orthogonalPolynomial μ k * r)).eval x ∂μ = 0 := by
    simp only [eval_mul, eval_C, integral_const_mul]
    rw [h0 r hr]
    ring
  rw [integral_congr_ae (ae_of_all μ hpoly), hsplit, hsplit, key1, hI2, hI3]
  ring

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
  have key : ∀ x : ℝ,
      (orthogonalPolynomial μ (k + 2)).eval x * (orthogonalPolynomial μ (k + 1)).eval x =
      (x - jacobiAlpha μ (k + 1)) * (orthogonalPolynomial μ (k + 1)).eval x ^ 2 -
        jacobiBeta μ (k + 1) *
          ((orthogonalPolynomial μ (k + 1)).eval x * (orthogonalPolynomial μ k).eval x) := by
    intro x
    rw [orthogonalPolynomial_add_two]
    simp only [eval_sub, eval_mul, eval_X, eval_C]
    ring
  have hint1 : Integrable (fun x => (x - jacobiAlpha μ (k + 1)) *
      (orthogonalPolynomial μ (k + 1)).eval x ^ 2) μ :=
    (integrable_eval_of_ae_mem_Icc hμ ((X - C (jacobiAlpha μ (k + 1))) *
      (orthogonalPolynomial μ (k + 1)) ^ 2)).congr (ae_of_all μ fun x => by
        simp only [eval_sub, eval_mul, eval_X, eval_C, eval_pow])
  have hint2 : Integrable (fun x => jacobiBeta μ (k + 1) *
      ((orthogonalPolynomial μ (k + 1)).eval x * (orthogonalPolynomial μ k).eval x)) μ := by
    simpa only [eval_mul] using
      (integrable_eval_of_ae_mem_Icc hμ
        (orthogonalPolynomial μ (k + 1) * orthogonalPolynomial μ k)).const_mul
        (jacobiBeta μ (k + 1))
  rw [integral_congr_ae (ae_of_all μ key), integral_sub hint1 hint2, integral_const_mul,
    integral_sub_jacobiAlpha_mul_orthogonalPolynomial_sq_eq_zero hμ (k + 1), zero_sub,
    h1 (orthogonalPolynomial μ k) (by
      rw [degree_orthogonalPolynomial]
      exact_mod_cast Nat.lt_succ_self k),
    mul_zero, neg_zero]

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
  have hm : ∀ n, (P n).Monic := monic_orthogonalPolynomial μ
  have hd : ∀ n, (P n).degree = n := degree_orthogonalPolynomial μ
  have hint := fun p : ℝ[X] => integrable_eval_of_ae_mem_Icc hμ p
  have hXm : (X * P k).Monic := monic_X.mul (hm k)
  have hXd : (X * P k).degree = ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [degree_mul, degree_X, hd]; norm_cast; omega
  have hlt : (X * P k - P (k + 1)).degree < ((k + 1 : ℕ) : WithBot ℕ) := by
    rw [← hXd]
    exact degree_sub_lt (by rw [hXd, hd]) hXm.ne_zero (by rw [hXm.leadingCoeff, (hm _).leadingCoeff])
  have hA := h1 _ hlt
  have hB := h1 (P k) (by rw [hd]; exact_mod_cast Nat.lt_succ_self k)
  have hsq : ∫ x, (P (k + 1)).eval x * (X * P k).eval x ∂μ =
      ∫ x, (P (k + 1)).eval x ^ 2 ∂μ := by
    have h2 : ∫ x, (P (k + 1)).eval x * (X * P k - P (k + 1)).eval x ∂μ =
        ∫ x, (P (k + 1)).eval x * (X * P k).eval x ∂μ -
          ∫ x, (P (k + 1)).eval x ^ 2 ∂μ := by
      rw [← integral_sub]
      · congr 1; ext x; simp only [eval_sub]; ring
      · exact hint ((P (k + 1)) * (X * P k)) |>.congr (Filter.Eventually.of_forall fun x => by simp)
      · exact hint ((P (k + 1)) * (P (k + 1))) |>.congr
          (Filter.Eventually.of_forall fun x => by simp [sq])
    linarith
  have hpt : ∀ x, (P (k + 2)).eval x * (P k).eval x =
      (P (k + 1)).eval x * (X * P k).eval x
        - jacobiAlpha μ (k + 1) * ((P (k + 1)).eval x * (P k).eval x)
        - jacobiBeta μ (k + 1) * (P k).eval x ^ 2 := by
    intro x
    rw [show P (k + 2) = _ from orthogonalPolynomial_add_two μ k]
    simp only [eval_sub, eval_mul, eval_X, eval_C]; ring
  have i1 : Integrable (fun x => (P (k + 1)).eval x * (X * P k).eval x) μ :=
    (hint ((P (k + 1)) * (X * P k))).congr (Filter.Eventually.of_forall fun x => by simp)
  have i2 : Integrable (fun x => (P (k + 1)).eval x * (P k).eval x) μ :=
    (hint ((P (k + 1)) * P k)).congr (Filter.Eventually.of_forall fun x => by simp)
  have i3 : Integrable (fun x => (P k).eval x ^ 2) μ :=
    (hint (P k ^ 2)).congr (Filter.Eventually.of_forall fun x => by simp)
  simp_rw [hpt]
  have i4 : Integrable (fun x => (P (k + 1)).eval x * (X * P k).eval x
      - jacobiAlpha μ (k + 1) * ((P (k + 1)).eval x * (P k).eval x)) μ :=
    i1.sub (i2.const_mul _)
  rw [integral_sub i4 (i3.const_mul _), integral_sub i1 (i2.const_mul _),
    integral_const_mul, integral_const_mul, hsq, hB,
    integral_orthogonalPolynomial_succ_sq hμ k]
  ring

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
  have hint : ∀ p : ℝ[X], Integrable (fun x => p.eval x) μ := integrable_eval_of_ae_mem_Icc hμ
  -- the three orthogonality facts of steps (a), (b) and (c), as integrals of evaluations
  have ha : ∫ x, (orthogonalPolynomial μ (k + 2) * r₀).eval x ∂μ = 0 := by
    simpa only [eval_mul] using
      integral_orthogonalPolynomial_add_two_mul_eq_zero_of_degree_lt hμ h1 h0 hdeg₀
  have hb : ∫ x, (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ (k + 1)).eval x ∂μ
      = 0 := by
    simpa only [eval_mul] using integral_orthogonalPolynomial_add_two_mul_succ hμ h1
  have hc : ∫ x, (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ k).eval x ∂μ = 0 := by
    simpa only [eval_mul] using integral_orthogonalPolynomial_add_two_mul_self hμ h1
  -- the two constant multiples, by $\int c\,f = c\int f$
  have hA : ∫ x, (C c₁ * (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ (k + 1))).eval x
      ∂μ = 0 := by
    have hE : ∀ x : ℝ, (C c₁ * (orthogonalPolynomial μ (k + 2) *
        orthogonalPolynomial μ (k + 1))).eval x
        = c₁ * (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ (k + 1)).eval x :=
      fun x => by rw [eval_mul, eval_C]
    simp only [hE, integral_const_mul c₁
      (fun x => (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ (k + 1)).eval x), hb,
      mul_zero]
  have hB : ∫ x, (C c₀ * (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ k)).eval x
      ∂μ = 0 := by
    have hE : ∀ x : ℝ, (C c₀ * (orthogonalPolynomial μ (k + 2) *
        orthogonalPolynomial μ k)).eval x
        = c₀ * (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ k).eval x :=
      fun x => by rw [eval_mul, eval_C]
    simp only [hE, integral_const_mul c₀
      (fun x => (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ k).eval x), hc, mul_zero]
  -- the split of $r$ at the polynomial level, and the assembly of the three integrals
  have hsplit : orthogonalPolynomial μ (k + 2) * r =
      C c₁ * (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ (k + 1)) +
      (C c₀ * (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ k) +
        orthogonalPolynomial μ (k + 2) * r₀) := by
    rw [hr₁, hr₀]
    ring
  have hintBC : Integrable (fun x => (C c₀ * (orthogonalPolynomial μ (k + 2) *
      orthogonalPolynomial μ k)).eval x + (orthogonalPolynomial μ (k + 2) * r₀).eval x) μ :=
    (hint _).add (hint _)
  simp only [← eval_mul, hsplit, eval_add,
    integral_add (hint (C c₁ * (orthogonalPolynomial μ (k + 2) *
      orthogonalPolynomial μ (k + 1)))) hintBC,
    integral_add (hint (C c₀ * (orthogonalPolynomial μ (k + 2) * orthogonalPolynomial μ k)))
      (hint (orthogonalPolynomial μ (k + 2) * r₀)),
    hA, hB, ha, add_zero]

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
  rcases k with _ | m
  · -- $k = 0$: $x = (x - \alpha_0) + \alpha_0$ and $\int\pi_1 = 0$.
    have hp : X * orthogonalPolynomial μ 0
        = orthogonalPolynomial μ 1 + C (jacobiAlpha μ 0) := by
      rw [orthogonalPolynomial_zero, mul_one, orthogonalPolynomial_one]; ring
    have key : ∀ x : ℝ, x * (orthogonalPolynomial μ 0).eval x
        * (orthogonalPolynomial μ 1).eval x
        = (orthogonalPolynomial μ 1).eval x ^ 2
          + jacobiAlpha μ 0 * (orthogonalPolynomial μ 1).eval x := by
      intro x
      have hx := congrArg (eval x) hp
      simp only [eval_mul, eval_add, eval_X, eval_C] at hx
      rw [hx]; ring
    have h1 : ∫ x, (orthogonalPolynomial μ 1).eval x ∂μ = 0 := by
      have h := isOrthogonalPolynomial_orthogonalPolynomial hμ 1 (1 : ℝ[X])
        (by rw [degree_one]; exact_mod_cast Nat.one_pos)
      simpa only [eval_one, mul_one] using h
    calc ∫ x, x * (orthogonalPolynomial μ 0).eval x * (orthogonalPolynomial μ 1).eval x ∂μ
        = ∫ x, (orthogonalPolynomial μ 1).eval x ^ 2
            + jacobiAlpha μ 0 * (orthogonalPolynomial μ 1).eval x ∂μ :=
          integral_congr_ae (ae_of_all μ fun x => key x)
      _ = ∫ x, (orthogonalPolynomial μ 1).eval x ^ 2 ∂μ
            + jacobiAlpha μ 0 * ∫ x, (orthogonalPolynomial μ 1).eval x ∂μ := by
          have hA : Integrable (fun x => (orthogonalPolynomial μ 1).eval x ^ 2) μ :=
            (integrable_eval_of_ae_mem_Icc hμ (orthogonalPolynomial μ 1 ^ 2)).congr
              (ae_of_all μ fun x => eval_pow 2)
          have hB : Integrable
              (fun x => jacobiAlpha μ 0 * (orthogonalPolynomial μ 1).eval x) μ :=
            (integrable_eval_of_ae_mem_Icc hμ (orthogonalPolynomial μ 1)).const_mul _
          rw [integral_add hA hB, integral_const_mul]
      _ = ∫ x, (orthogonalPolynomial μ 1).eval x ^ 2 ∂μ := by rw [h1, mul_zero, add_zero]
  · -- $k = m + 1$: the three-term recurrence and the orthogonality of $\pi_{m + 2}$.
    have hp : X * orthogonalPolynomial μ (m + 1) = orthogonalPolynomial μ (m + 2)
        + C (jacobiAlpha μ (m + 1)) * orthogonalPolynomial μ (m + 1)
        + C (jacobiBeta μ (m + 1)) * orthogonalPolynomial μ m := by
      rw [orthogonalPolynomial_add_two]; ring
    have key : ∀ x : ℝ, x * (orthogonalPolynomial μ (m + 1)).eval x
        * (orthogonalPolynomial μ (m + 2)).eval x
        = (orthogonalPolynomial μ (m + 2)).eval x ^ 2
          + jacobiAlpha μ (m + 1) * ((orthogonalPolynomial μ (m + 2)).eval x
            * (orthogonalPolynomial μ (m + 1)).eval x)
          + jacobiBeta μ (m + 1) * ((orthogonalPolynomial μ (m + 2)).eval x
            * (orthogonalPolynomial μ m).eval x) := by
      intro x
      have hx := congrArg (eval x) hp
      simp only [eval_mul, eval_add, eval_X, eval_C] at hx
      rw [hx]; ring
    have h1 : ∫ x, (orthogonalPolynomial μ (m + 2)).eval x
        * (orthogonalPolynomial μ (m + 1)).eval x ∂μ = 0 :=
      isOrthogonalPolynomial_orthogonalPolynomial hμ (m + 2) (orthogonalPolynomial μ (m + 1))
        (by rw [degree_orthogonalPolynomial]; exact_mod_cast Nat.lt_succ_self (m + 1))
    have h2 : ∫ x, (orthogonalPolynomial μ (m + 2)).eval x
        * (orthogonalPolynomial μ m).eval x ∂μ = 0 :=
      isOrthogonalPolynomial_orthogonalPolynomial hμ (m + 2) (orthogonalPolynomial μ m)
        (by rw [degree_orthogonalPolynomial]; exact_mod_cast show m < m + 2 by omega)
    have hint : ∀ p q : ℝ[X], Integrable (fun x => p.eval x * q.eval x) μ := fun p q =>
      (integrable_eval_of_ae_mem_Icc hμ (p * q)).congr (ae_of_all μ fun _ => eval_mul)
    have hsq : ∀ p : ℝ[X], Integrable (fun x => p.eval x ^ 2) μ := fun p =>
      (integrable_eval_of_ae_mem_Icc hμ (p ^ 2)).congr (ae_of_all μ fun x => eval_pow 2)
    have hA : Integrable (fun x => (orthogonalPolynomial μ (m + 2)).eval x ^ 2) μ :=
      hsq (orthogonalPolynomial μ (m + 2))
    have hB : Integrable (fun x => jacobiAlpha μ (m + 1)
        * ((orthogonalPolynomial μ (m + 2)).eval x
          * (orthogonalPolynomial μ (m + 1)).eval x)) μ :=
      (hint (orthogonalPolynomial μ (m + 2)) (orthogonalPolynomial μ (m + 1))).const_mul _
    have hC : Integrable (fun x => jacobiBeta μ (m + 1)
        * ((orthogonalPolynomial μ (m + 2)).eval x
          * (orthogonalPolynomial μ m).eval x)) μ :=
      (hint (orthogonalPolynomial μ (m + 2)) (orthogonalPolynomial μ m)).const_mul _
    calc ∫ x, x * (orthogonalPolynomial μ (m + 1)).eval x
          * (orthogonalPolynomial μ (m + 2)).eval x ∂μ
        = ∫ x, (orthogonalPolynomial μ (m + 2)).eval x ^ 2
            + jacobiAlpha μ (m + 1) * ((orthogonalPolynomial μ (m + 2)).eval x
              * (orthogonalPolynomial μ (m + 1)).eval x)
            + jacobiBeta μ (m + 1) * ((orthogonalPolynomial μ (m + 2)).eval x
              * (orthogonalPolynomial μ m).eval x) ∂μ :=
          integral_congr_ae (ae_of_all μ fun x => key x)
      _ = ∫ x, (orthogonalPolynomial μ (m + 2)).eval x ^ 2 ∂μ
            + jacobiAlpha μ (m + 1) * ∫ x, (orthogonalPolynomial μ (m + 2)).eval x
                * (orthogonalPolynomial μ (m + 1)).eval x ∂μ
            + jacobiBeta μ (m + 1) * ∫ x, (orthogonalPolynomial μ (m + 2)).eval x
                * (orthogonalPolynomial μ m).eval x ∂μ := by
          rw [integral_add (hA.fun_add hB) hC, integral_add hA hB, integral_const_mul,
            integral_const_mul]
      _ = ∫ x, (orthogonalPolynomial μ (m + 2)).eval x ^ 2 ∂μ := by
          rw [h1, h2, mul_zero, mul_zero, add_zero, add_zero]

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
  constructor
  · intro h
    refine h _ (monic_orthogonalPolynomial μ k).ne_zero ?_
    rw [degree_orthogonalPolynomial]
    exact_mod_cast Nat.lt_succ_self k
  · intro hpos p hp0 hpdeg
    have hlow : ∀ j m, j + m = k → 0 < ∫ x, (orthogonalPolynomial μ j).eval x ^ 2 ∂μ := by
      intro j m
      induction m generalizing j with
      | zero => intro hj; rw [show j = k by omega]; exact hpos
      | succ m ih =>
        intro hj
        have h1 := ih (j + 1) (by omega)
        rw [integral_orthogonalPolynomial_succ_sq hμ j] at h1
        exact pos_of_mul_pos_right h1 (jacobiBeta_nonneg μ (j + 1))
    have hdk : p.natDegree ≤ k := by
      have := (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
      omega
    have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
    have hdeg_eq : p.degree = (C p.leadingCoeff * orthogonalPolynomial μ p.natDegree).degree := by
      rw [degree_C_mul hc, degree_orthogonalPolynomial, degree_eq_natDegree hp0]
    have hlc_eq : p.leadingCoeff =
        (C p.leadingCoeff * orthogonalPolynomial μ p.natDegree).leadingCoeff := by
      rw [leadingCoeff_mul, leadingCoeff_C, (monic_orthogonalPolynomial μ _).leadingCoeff, mul_one]
    have hrdeg := degree_sub_lt_left hdeg_eq hp0 hlc_eq
    rw [degree_eq_natDegree hp0] at hrdeg
    have hrdeg' : (p - C p.leadingCoeff * orthogonalPolynomial μ p.natDegree).degree <
        (p.natDegree : WithBot ℕ) := by exact_mod_cast hrdeg
    have horth := isOrthogonalPolynomial_orthogonalPolynomial hμ p.natDegree _ hrdeg'
    have hN := hlow p.natDegree (k - p.natDegree) (by omega)
    have hR : 0 ≤ ∫ x, (p - C p.leadingCoeff * orthogonalPolynomial μ p.natDegree).eval x ^ 2 ∂μ :=
      integral_nonneg fun x => sq_nonneg _
    have hint : ∀ q : ℝ[X], Integrable (fun x => q.eval x) μ := fun q =>
      integrable_eval_of_ae_mem_Icc hμ q
    have hpt : (fun x => p.eval x ^ 2) = fun x =>
        p.leadingCoeff ^ 2 * (orthogonalPolynomial μ p.natDegree).eval x ^ 2 +
          (2 * p.leadingCoeff * ((orthogonalPolynomial μ p.natDegree).eval x *
            (p - C p.leadingCoeff * orthogonalPolynomial μ p.natDegree).eval x) +
          (p - C p.leadingCoeff * orthogonalPolynomial μ p.natDegree).eval x ^ 2) := by
      funext x
      simp only [eval_sub, eval_mul, eval_C]
      ring
    set π := orthogonalPolynomial μ p.natDegree with hπ
    set r := p - C p.leadingCoeff * π with hr
    set c := p.leadingCoeff with hcdef
    have i1 : Integrable (fun x => (π.eval x) ^ 2) μ := by
      simpa only [sq, eval_mul] using hint (π * π)
    have i2 : Integrable (fun x => π.eval x * r.eval x) μ := by
      simpa only [eval_mul] using hint (π * r)
    have i3 : Integrable (fun x => r.eval x ^ 2) μ := by
      simpa only [sq, eval_mul] using hint (r * r)
    have hA : Integrable (fun x => c ^ 2 * π.eval x ^ 2) μ := i1.const_mul _
    have hB2 : Integrable (fun x => 2 * c * (π.eval x * r.eval x)) μ := i2.const_mul _
    have hB : Integrable (fun x => 2 * c * (π.eval x * r.eval x) + r.eval x ^ 2) μ := hB2.add i3
    rw [hpt, integral_add hA hB, integral_add hB2 i3, integral_const_mul, integral_const_mul,
      horth, mul_zero, zero_add]
    exact add_pos_of_pos_of_nonneg (mul_pos (by positivity) hN) hR

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
  have hdeg : (p - orthogonalPolynomial μ k).degree < k := by
    have hm := monic_orthogonalPolynomial μ k
    have h1 : p.degree = k := by rw [degree_eq_natDegree hp.ne_zero, hpk]
    have h2 := degree_orthogonalPolynomial μ k
    have := degree_sub_lt (p := p) (q := orthogonalPolynomial μ k) (by rw [h1, h2])
      hp.ne_zero (by rw [hp.leadingCoeff, hm.leadingCoeff])
    rwa [h1] at this
  by_contra hne
  have hd : p - orthogonalPolynomial μ k ≠ 0 := sub_ne_zero.mpr hne
  have hpos := h _ hd hdeg
  have hint := integrable_eval_of_ae_mem_Icc hμ (p * (p - orthogonalPolynomial μ k))
  have hint' := integrable_eval_of_ae_mem_Icc hμ
    (orthogonalPolynomial μ k * (p - orthogonalPolynomial μ k))
  have h0 := hpo _ hdeg
  have h0' := isOrthogonalPolynomial_orthogonalPolynomial hμ k _ hdeg
  simp only [eval_mul] at hint hint'
  have : ∫ x, (p - orthogonalPolynomial μ k).eval x ^ 2 ∂μ = 0 := by
    calc _ = ∫ x, (p.eval x * (p - orthogonalPolynomial μ k).eval x
          - (orthogonalPolynomial μ k).eval x * (p - orthogonalPolynomial μ k).eval x) ∂μ := by
          congr 1; ext x; simp only [eval_sub]; ring
      _ = 0 := by rw [integral_sub hint hint', h0, h0', sub_zero]
  linarith

end Orthogonality

end NLAlib
