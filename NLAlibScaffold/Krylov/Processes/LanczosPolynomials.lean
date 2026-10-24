/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.Compression
public import NLAlib.Krylov.Processes.LanczosRecurrence
public import NLAlibScaffold.Matrix.Spectral.SpectralMeasure
public import NLAlibScaffold.Polynomial.Orthogonal.Recurrence

/-!
# The Lanczos polynomials

For Hermitian $\mathbf{A}$ the Lanczos method from $\mathbf{b}$ computes the orthogonal
polynomials of the spectral measure $\mu_{\mathbf{A},\mathbf{b}}$: column $j$ of the canonical
Lanczos basis is $\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$, the Lanczos
coefficients are $\alpha_j(\mu_{\mathbf{A},\mathbf{b}})$ and
$\sqrt{\beta_{j+1}(\mu_{\mathbf{A},\mathbf{b}})}$, and the Lanczos tridiagonal matrix is the Jacobi
matrix of $\mu_{\mathbf{A},\mathbf{b}}$, for every number of steps (past the grade both sides are
padded with the same zeros). The spectral measure is positive definite up to degree $k$ exactly
when $k$ is at most the grade. Statements of stage KS7 whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.9); the file will be
`NLAlib/Krylov/Processes/LanczosPolynomials.lean`. [GolubMeurant2010]; [Gautschi2004].

## Main results

* `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff`: definiteness is the grade.
* `Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec`: the Lanczos
  vectors.
* `Matrix.IsHermitian.lanczosAlpha_lanczosState`, `Matrix.IsHermitian.lanczosState_beta`: the
  Lanczos coefficients.
* `Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix`: the tridiagonal is the Jacobi matrix.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Definiteness of the spectral measure is the grade: for Hermitian $\mathbf{A}$, every
$\mathbf{b}$ and every $k$, $\mu_{\mathbf{A},\mathbf{b}}$ is positive definite on the polynomials
of degree less than $k$ exactly when $k \le \nu$, $\nu$ the grade of $\mathbf{b}$.
Proof: M, about 35 lines. ⇐: `Matrix.IsHermitian.norm_aeval_mulVec_sq` and
`aeval_mulVec_ne_zero_of_degree_lt_krylovGrade`. ⇒: take $\mathbf{Q}$ spanning
$\mathcal{K}_{\nu+1} = \mathcal{K}_\nu$ (`exists_hasOrthonormalCols_range_eq_krylovSpace`,
`krylovSpace_eq_of_krylovGrade_le`) and $s$ its Ritz values ($\lvert s\rvert \le \nu$);
`HasOrthonormalCols.conjTranspose_mulVec_aeval_nodal_mulVec_eq_zero` gives
$\pi_s(\mathbf{A})\mathbf{b} = \mathbf{0}$, so $\mu_{\mathbf{A},\mathbf{b}}$ is carried by $s$
(`Matrix.IsHermitian.norm_aeval_mulVec_sq`, `ae_eval_eq_zero_of_integral_sq_eq_zero`);
`isMomentPosDef_iff_forall_finset`. -/
theorem _root_.Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (k : ℕ) :
    IsMomentPosDef (spectralMeasure A b) k ↔ k ≤ krylovGrade A b := by
  constructor
  · -- past the grade the Ritz polynomial of $\mathcal{K}_\nu$ annihilates $\mathbf{b}$
    intro h
    by_contra hk
    have hν : krylovGrade A b < k := by omega
    obtain ⟨r, Q, hQ, hK⟩ :=
      exists_hasOrthonormalCols_range_eq_krylovSpace A b (krylovGrade A b + 1)
    have hT : (Qᴴ * A * Q).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul Q hA
    have hr : Fintype.card (Fin r) = krylovGrade A b := by
      have h1 : Fintype.card (Fin r) = min (krylovGrade A b + 1) (krylovGrade A b) := by
        rw [← hQ.rank_eq, ← finrank_krylovSpace, ← hK]
        rfl
      rw [h1, Nat.min_eq_right (Nat.le_succ _)]
    -- the Ritz values, at most $\nu$ of them
    set s : Finset ℝ := Finset.image hT.eigenvalues Finset.univ with hsdef
    have hcard : s.card ≤ krylovGrade A b :=
      Finset.card_image_le.trans (by rw [Finset.card_univ, hr])
    have hs : spectrum ℝ (Qᴴ * A * Q) ⊆ (s : Set ℝ) := by
      rw [hT.spectrum_real_eq_range_eigenvalues]
      exact fun x ⟨i, hi⟩ => Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
    have hdeg : (Lagrange.nodal s id).degree < krylovGrade A b + 1 := by
      rw [Lagrange.degree_nodal]
      exact_mod_cast Nat.lt_succ_of_le hcard
    have hzero : aeval A (Lagrange.nodal s id) *ᵥ b = 0 := by
      rw [← hQ.mulVec_aeval_conjTranspose_mul_mul_mulVec_eq hK hdeg,
        hT.aeval_nodal_eq_zero hs, Matrix.zero_mulVec, Matrix.mulVec_zero]
    have hint : ∫ x, (Lagrange.nodal s id).eval x ^ 2 ∂spectralMeasure A b = 0 := by
      rw [← hA.norm_aeval_mulVec_sq b (Lagrange.nodal s id), hzero]
      simp
    have hpos := h (Lagrange.nodal s id) Lagrange.nodal_monic.ne_zero
      (hdeg.trans_le (by exact_mod_cast Nat.succ_le_of_lt hν))
    rw [hint] at hpos
    exact lt_irrefl 0 hpos
  · -- below the grade no nonzero polynomial of small degree annihilates $\mathbf{b}$
    intro hk p hp0 hp
    rw [← hA.norm_aeval_mulVec_sq b p]
    exact pow_pos (norm_pos_iff.mpr ((WithLp.toLp_eq_zero 2).not.mpr
      (aeval_mulVec_ne_zero_of_degree_lt_krylovGrade hp0
        (hp.trans_le (by exact_mod_cast hk))))) 2

/-- $\pi_j(\mathbf{A})\mathbf{b}$ differs from $\mathbf{A}^j\mathbf{b}$ by a Krylov vector: for
every measure $\mu$ on $\mathbb{R}$, every square $\mathbf{A}$, $\mathbf{b}$ and $j$,
$\pi_j(\mathbf{A})\mathbf{b} - \mathbf{A}^j\mathbf{b} \in \mathcal{K}_j(\mathbf{A}, \mathbf{b})$,
$\pi_j$ the monic orthogonal polynomial of degree $j$ of $\mu$.
Proof: S, about 15 lines. $\pi_j - X^j$ has degree less than $j$ (`monic_orthogonalPolynomial`,
`degree_orthogonalPolynomial`, `degree_sub_lt_left`); `aeval_mulVec_mem_krylovSpace` (real
coefficients), `map_sub`, `aeval_X_pow`, `Matrix.sub_mulVec`. -/
theorem aeval_orthogonalPolynomial_mulVec_sub_pow_mulVec_mem_krylovSpace (μ : Measure ℝ)
    (A : Matrix n n 𝕜) (b : n → 𝕜) (j : ℕ) :
    aeval A (orthogonalPolynomial μ j) *ᵥ b - A ^ j *ᵥ b ∈ krylovSpace A b j := by
  have h : aeval A (orthogonalPolynomial μ j - (X : ℝ[X]) ^ j) *ᵥ b ∈ krylovSpace A b j := by
    refine aeval_mulVec_mem_krylovSpace A b ?_
    have hdeg : (orthogonalPolynomial μ j - (X : ℝ[X]) ^ j).degree <
        (orthogonalPolynomial μ j).degree :=
      degree_sub_lt_left (by rw [degree_orthogonalPolynomial, degree_X_pow])
        (monic_orthogonalPolynomial μ j).ne_zero
        (by rw [(monic_orthogonalPolynomial μ j).leadingCoeff, Polynomial.leadingCoeff_X_pow])
    rwa [degree_orthogonalPolynomial] at hdeg
  rwa [map_sub, Matrix.sub_mulVec, aeval_X_pow] at h

/-- $\pi_j(\mathbf{A})\mathbf{b}$ is orthogonal to the Krylov space: for Hermitian $\mathbf{A}$,
every $\mathbf{b}$, $j$ and $\mathbf{x} \in \mathcal{K}_j(\mathbf{A}, \mathbf{b})$,
$\langle\mathbf{x}, \pi_j(\mathbf{A})\mathbf{b}\rangle = 0$, $\pi_j$ the monic orthogonal
polynomial of degree $j$ of $\mu_{\mathbf{A},\mathbf{b}}$.
Proof: M, about 35 lines. `krylovSpace_eq_span`, `Submodule.span_induction` (or
`mem_span_range_iff_exists_fun`); for $\mathbf{A}^i\mathbf{b} = X^i(\mathbf{A})\mathbf{b}$, $i < j$,
`Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec` and
`isOrthogonalPolynomial_orthogonalPolynomial` (support from `ae_mem_Icc_spectralMeasure`);
`dotProduct` linearity in the first slot with `star`. -/
theorem _root_.Matrix.IsHermitian.star_dotProduct_aeval_orthogonalPolynomial_mulVec_eq_zero_of_mem
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b x : n → 𝕜} {j : ℕ}
    (hx : x ∈ krylovSpace A b j) :
    star x ⬝ᵥ (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) = 0 := by
  sorry

/-- From the grade on, $\pi_j(\mathbf{A})\mathbf{b}$ vanishes: for Hermitian $\mathbf{A}$, every
$\mathbf{b}$ and $j \ge \nu$, $\nu$ the grade of $\mathbf{b}$, $\pi_j(\mathbf{A})\mathbf{b} =
\mathbf{0}$, $\pi_j$ the monic orthogonal polynomial of degree $j$ of $\mu_{\mathbf{A},\mathbf{b}}$.
Proof: S, about 15 lines. `Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff` at $j + 1$ is
false, so `isMomentPosDef_succ_iff` gives $\|\pi_j\|^2 \le 0$;
`Matrix.IsHermitian.norm_aeval_mulVec_sq`, `norm_eq_zero`. -/
theorem _root_.Matrix.IsHermitian.aeval_orthogonalPolynomial_mulVec_eq_zero_of_krylovGrade_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {j : ℕ} (hj : krylovGrade A b ≤ j) :
    aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b = 0 := by
  sorry

/-- The last Lanczos vector below the grade: for Hermitian $\mathbf{A}$ and $j < \nu$, the last
column of the canonical Lanczos basis with $j + 1$ columns is
$\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$.
Proof: M, about 45 lines. `exists_gramSchmidtR_smul_arnoldiMatrix_col_last`:
$r_j\mathbf{q}_j - \pi_j(\mathbf{A})\mathbf{b} \in \mathcal{K}_j$
(`aeval_orthogonalPolynomial_mulVec_sub_pow_mulVec_mem_krylovSpace`); both are orthogonal to
$\mathcal{K}_j$ (`star_arnoldiMatrix_col_last_dotProduct_eq_zero_of_mem`,
`Matrix.IsHermitian.star_dotProduct_aeval_orthogonalPolynomial_mulVec_eq_zero_of_mem`), so equal;
$r_j = \|\pi_j(\mathbf{A})\mathbf{b}\| \ne 0$ (`norm_arnoldiMatrix_col_last`,
`gramSchmidtR_apply_self_nonneg`, `gramSchmidtR_krylovMatrix_apply_last_eq_zero_iff`,
`Matrix.IsHermitian.norm_aeval_mulVec_sq`). -/
private theorem arnoldiMatrix_col_last_eq_of_lt_krylovGrade {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {b : n → 𝕜} {j : ℕ} (hj : j < krylovGrade A b) :
    (arnoldiMatrix A b (j + 1)).col (Fin.last j) =
      (‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)‖⁻¹ : 𝕜) •
        (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) := by
  sorry

/-- **The Lanczos vectors are the orthogonal polynomials of the spectral measure**: for
Hermitian $\mathbf{A}$, every $q$ and $j < q$, column $j$ of the canonical Lanczos basis is
$\pi_j(\mathbf{A})\mathbf{b}/\|\pi_j(\mathbf{A})\mathbf{b}\|$, $\pi_j$ the monic orthogonal
polynomial of degree $j$ of $\mu_{\mathbf{A},\mathbf{b}}$; from the grade on both sides are
$\mathbf{0}$. [GolubMeurant2010, Ch. 4] (locator to check).
Proof: S, about 15 lines. `arnoldiMatrix_col_eq_col_last`; below the grade
`arnoldiMatrix_col_last_eq_of_lt_krylovGrade`; from the grade on
`arnoldiMatrix_col_last_eq_zero_iff` and
`Matrix.IsHermitian.aeval_orthogonalPolynomial_mulVec_eq_zero_of_krylovGrade_le` (`smul_zero`).
Result: lanczos-orthogonal-polynomials -/
theorem _root_.Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (b : n → 𝕜) {q : ℕ} (j : Fin q) :
    (arnoldiMatrix A b q).col j =
      (‖WithLp.toLp 2 (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b)‖⁻¹ : 𝕜) •
        (aeval A (orthogonalPolynomial (spectralMeasure A b) j) *ᵥ b) := by
  sorry

/-- The diagonal Lanczos coefficient is the recurrence coefficient of the spectral measure: for
Hermitian $\mathbf{A}$, every $\mathbf{b}$ and $j$, the coefficient $\alpha_j$ computed by the
Lanczos recurrence from $\mathbf{b}$ is $\alpha_j(\mu_{\mathbf{A},\mathbf{b}})$.
Proof: M, about 40 lines. `Matrix.IsHermitian.lanczosTridiagonal_eq` at $q = j + 1$, entry
$(j, j)$; `NLAlib.conjTranspose_mul_apply`;
`Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec`;
`Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec` with $r = X\pi_j$ (`aeval_mul`,
`aeval_X`); `Matrix.IsHermitian.norm_aeval_mulVec_sq`; `RCLike.ofReal_inj`; zero norms apart. -/
theorem _root_.Matrix.IsHermitian.lanczosAlpha_lanczosState {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    lanczosAlpha A (lanczosState A b j) = jacobiAlpha (spectralMeasure A b) j := by
  sorry

/-- The off-diagonal Lanczos coefficient is the square root of the recurrence coefficient of the
spectral measure: for Hermitian $\mathbf{A}$, every $\mathbf{b}$ and $j$, the coefficient
$\beta_{j+1}$ computed by the Lanczos recurrence from $\mathbf{b}$ is
$\sqrt{\beta_{j+1}(\mu_{\mathbf{A},\mathbf{b}})}$ (Gautschi's $\beta$, the ratio of squared
norms).
Proof: M, about 45 lines. Entry $(j + 1, j)$ of `Matrix.IsHermitian.lanczosTridiagonal_eq` at
$q = j + 2$; `Matrix.IsHermitian.arnoldiMatrix_col_eq_smul_aeval_orthogonalPolynomial_mulVec`
twice; `Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec`;
`integral_mul_orthogonalPolynomial_mul_orthogonalPolynomial_succ`;
$\|\pi_{j+1}\|^2/(\|\pi_{j+1}\|\|\pi_j\|) = \sqrt{\beta_{j+1}}$ (`Real.sqrt_div'`,
`Real.sqrt_sq`, `integral_orthogonalPolynomial_succ_sq`; zero cases apart). -/
theorem _root_.Matrix.IsHermitian.lanczosState_beta {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (j : ℕ) :
    (lanczosState A b (j + 1)).beta = √(jacobiBeta (spectralMeasure A b) (j + 1)) := by
  sorry

/-- **The Lanczos tridiagonal is the Jacobi matrix of the spectral measure**: for Hermitian
$\mathbf{A}$ and every $q$, the tridiagonal matrix of $q$ steps of the Lanczos recurrence from
$\mathbf{b}$ is $\mathbf{J}_q(\mu_{\mathbf{A},\mathbf{b}})$; past the grade both are padded with
the same zeros. [GolubMeurant2010, Ch. 4]; [Gautschi2004, §3.1] (locators to check).
Proof: S, about 20 lines. `ext i j`; unfold `lanczosTridiagonal`, `jacobiMatrix`,
`Matrix.map_apply`; `split_ifs`; `Matrix.IsHermitian.lanczosAlpha_lanczosState`,
`Matrix.IsHermitian.lanczosState_beta`, `RCLike.algebraMap_eq_ofReal`.
Result: lanczos-jacobi-matrix -/
theorem _root_.Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosTridiagonal A b q = (jacobiMatrix (spectralMeasure A b) q).map (algebraMap ℝ 𝕜) := by
  sorry

end NLAlib
