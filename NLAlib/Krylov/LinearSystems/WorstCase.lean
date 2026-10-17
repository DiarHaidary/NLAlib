/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CG
public import NLAlib.Krylov.LinearSystems.MINRES
public import Mathlib.Algebra.Polynomial.Expand

/-!
# Spectra on which the Chebyshev bounds are attained

For every $q$ and $0 < a < a'$ there are a positive definite matrix with spectrum in $[a, a']$
and a right-hand side for which the CG error and the MINRES residual after $q$ steps are exactly
$T_q\bigl(\frac{a' + a}{a' - a}\bigr)^{-1} = \frac{2\rho^q}{1 + \rho^{2q}}$ times their initial
values, $\rho = \frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}$. So the bounds $2\rho^q$ (and $4\rho^{2q}$
squared) of `NLAlib.Krylov.LinearSystems.CG` and `NLAlib.Krylov.LinearSystems.MINRES` are tight
up to the factor $1 + \rho^{2q}$ (squared: $(1 + \rho^{2q})^2$), which tends to $1$.

The matrix is diagonal with the $q + 1$ Chebyshev extrema $\xi_0 < \dots < \xi_q$ of $[a, a']$
(`NLAlib.chebyshevExtremum`), and the right-hand side carries the dual weights
$\omega_k = \lvert\ell_k(0)\rvert$ (`NLAlib.chebyshevWeight`): for these weights the weighted
least-squares problem over residual polynomials, which CG and MINRES solve, has the Chebyshev
minimax polynomial as its solution. Reflecting the extrema of $[a^2, a'^2]$ through
$\pm\sqrt{\cdot}$
gives the same for MINRES on $[-a', -a] \cup [a, a']$ at the rate of
`Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_div_two`.

Greenbaum's theorem that for every positive definite $\mathbf{A}$ some $\mathbf{b}$ attains the
spectrum minimax value `NLAlib.residualMinimax` is not here: it is stage K2b's, with the
machinery it shares there.

## Main definitions

* `NLAlib.chebyshevExtremaMatrix`, `NLAlib.chebyshevErrorVector`, `NLAlib.chebyshevWeightVector`.
* `NLAlib.chebyshevTwoIntervalMatrix`, `NLAlib.chebyshevTwoIntervalVector`.

## Main results

* `NLAlib.re_quadForm_sub_cgIterate_chebyshevExtremaMatrix`: CG attains the Chebyshev value.
* `NLAlib.re_quadForm_sub_cgIterate_chebyshevExtremaMatrix_eq_four_mul_pow_div`: in $\rho$.
* `NLAlib.norm_sub_mulVec_gmresIterate_chebyshevExtremaMatrix`: so does MINRES.
* `NLAlib.norm_sub_mulVec_gmresIterate_chebyshevTwoIntervalMatrix`: two symmetric intervals.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial Polynomial.Chebyshev

namespace NLAlib

variable (𝕜 : Type*) [RCLike 𝕜]

/-- The **Chebyshev extrema matrix**: diagonal with the $q + 1$ Chebyshev extrema of $[a, a']$. -/
noncomputable def chebyshevExtremaMatrix (a a' : ℝ) (q : ℕ) :
    Matrix (Fin (q + 1)) (Fin (q + 1)) 𝕜 :=
  Matrix.diagonal fun k => (chebyshevExtremum a a' q k : 𝕜)

/-- The CG worst-case initial error: entries $\sqrt{\omega_k/\xi_k}$, so that its
$\mathbf{A}$-norm weights are the dual weights. -/
noncomputable def chebyshevErrorVector (a a' : ℝ) (q : ℕ) : Fin (q + 1) → 𝕜 :=
  fun k => (Real.sqrt (chebyshevWeight a a' q k / chebyshevExtremum a a' q k) : 𝕜)

/-- The MINRES worst-case right-hand side: entries $\sqrt{\omega_k}$. -/
noncomputable def chebyshevWeightVector (a a' : ℝ) (q : ℕ) : Fin (q + 1) → 𝕜 :=
  fun k => (Real.sqrt (chebyshevWeight a a' q k) : 𝕜)

/-- The **symmetric two-interval matrix**: diagonal with $\pm\sqrt{\xi_j}$ for the $k + 1$
Chebyshev extrema $\xi_j$ of $[a^2, a'^2]$. -/
noncomputable def chebyshevTwoIntervalMatrix (a a' : ℝ) (k : ℕ) :
    Matrix (Fin (k + 1) ⊕ Fin (k + 1)) (Fin (k + 1) ⊕ Fin (k + 1)) 𝕜 :=
  Matrix.diagonal fun i => Sum.elim
    (fun j : Fin (k + 1) => (Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) : 𝕜))
    (fun j : Fin (k + 1) => (-Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) : 𝕜)) i

/-- The two-interval right-hand side: $\sqrt{\omega_j/2}$ on both copies. -/
noncomputable def chebyshevTwoIntervalVector (a a' : ℝ) (k : ℕ) :
    Fin (k + 1) ⊕ Fin (k + 1) → 𝕜 :=
  fun i => Sum.elim (fun j => (Real.sqrt (chebyshevWeight (a ^ 2) (a' ^ 2) k j / 2) : 𝕜))
    (fun j => (Real.sqrt (chebyshevWeight (a ^ 2) (a' ^ 2) k j / 2) : 𝕜)) i

variable {𝕜}

/-- The Chebyshev extrema matrix is positive definite for $0 < a \le a'$. -/
theorem posDef_chebyshevExtremaMatrix {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a') (q : ℕ) :
    (chebyshevExtremaMatrix 𝕜 a a' q).PosDef := by
  rw [chebyshevExtremaMatrix, Matrix.posDef_diagonal_iff]
  exact fun k => RCLike.ofReal_pos.mpr (ha.trans_le (chebyshevExtremum_mem_Icc haa q k).1)

/-- Its spectrum lies in $[a, a']$. -/
theorem spectrum_chebyshevExtremaMatrix_subset_Icc {a a' : ℝ} (haa : a ≤ a') (q : ℕ) :
    spectrum ℝ (chebyshevExtremaMatrix 𝕜 a a' q) ⊆ Set.Icc a a' := by
  rw [← spectrum.preimage_algebraMap 𝕜, chebyshevExtremaMatrix, spectrum_diagonal]
  rintro r ⟨k, hk⟩
  rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_inj] at hk
  exact hk ▸ chebyshevExtremum_mem_Icc haa q k

/-- The $\mathbf{A}$-norm on the Chebyshev extrema matrix: $\sum_k \xi_k \lvert z_k \rvert^2$. -/
private lemma re_quadForm_chebyshevExtremaMatrix (a a' : ℝ) (q : ℕ) (z : Fin (q + 1) → 𝕜) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) z) =
      ∑ k : Fin (q + 1), chebyshevExtremum a a' q k * ‖z k‖ ^ 2 := by
  rw [chebyshevExtremaMatrix, quadForm_diagonal, map_sum]
  simp only [← RCLike.ofReal_mul, RCLike.ofReal_re]

/-- The squared $\mathbf{A}$-norm of `chebyshevErrorVector` scaled entrywise by $f$ is
$\sum_k\omega_k\lvert f_k \rvert^2$. -/
private lemma re_quadForm_chebyshevErrorVector {a a' : ℝ} (ha : 0 < a) (haa : a < a') (q : ℕ)
    (f : Fin (q + 1) → 𝕜) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q)
        (fun k => f k * chebyshevErrorVector 𝕜 a a' q k)) =
      ∑ k : Fin (q + 1), chebyshevWeight a a' q k * ‖f k‖ ^ 2 := by
  rw [re_quadForm_chebyshevExtremaMatrix]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hξ : 0 < chebyshevExtremum a a' q k :=
    ha.trans_le (chebyshevExtremum_mem_Icc haa.le q k).1
  have hω := (chebyshevWeight_pos ha haa q k).le
  rw [norm_mul, mul_pow, chebyshevErrorVector, RCLike.norm_ofReal,
    abs_of_nonneg (Real.sqrt_nonneg _), Real.sq_sqrt (div_nonneg hω hξ.le)]
  field_simp

/-- Cauchy–Schwarz against the signed dual weights: every $p \in \Bbbk[X]$ with $\deg p \le q$
and $p(0) = 1$ has $\sum_k\omega_k\lvert p(\xi_k)\rvert^2 \ge
T_q\bigl(\frac{a' + a}{a' - a}\bigr)^{-1}$. -/
private lemma inv_eval_T_le_sum_chebyshevWeight_mul_norm_sq {a a' : ℝ} (ha : 0 < a)
    (haa : a < a') {q : ℕ} {p : 𝕜[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ ≤
      ∑ k : Fin (q + 1),
        chebyshevWeight a a' q k * ‖p.eval (chebyshevExtremum a a' q k : 𝕜)‖ ^ 2 := by
  set τ := (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a))
  have hτ : 0 < τ := zero_lt_one.trans_le (one_le_eval_T_real (q : ℤ) (by
    rw [le_div_iff₀ (by linarith)]
    linarith))
  set ω := chebyshevWeight a a' q
  set u := fun k : Fin (q + 1) => ‖p.eval (chebyshevExtremum a a' q k : 𝕜)‖
  have hω : ∀ k, 0 < ω k := chebyshevWeight_pos ha haa q
  have hS : 1 ≤ ∑ k, ω k * u k := by
    have h := congrArg norm (sum_neg_one_pow_mul_chebyshevWeight_mul_eval ha haa hp)
    rw [hp₀, norm_one] at h
    rw [← h]
    refine (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl fun k _ => ?_)
    rw [norm_mul, RCLike.norm_ofReal, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_pos (hω k)]
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul Finset.univ
    (r := fun k => ω k * u k) (f := ω) (g := fun k => ω k * u k ^ 2)
    (fun k _ => (hω k).le) (fun k _ => mul_nonneg (hω k).le (sq_nonneg _))
    (fun k _ => by ring_nf; rfl)
  have hW : ∑ k, ω k = τ := sum_chebyshevWeight ha haa q
  rw [hW] at hCS
  rw [inv_le_iff_one_le_mul₀ hτ]
  nlinarith

/-- **CG attains the Chebyshev value**: for $0 < a < a'$, on the Chebyshev extrema matrix
$\mathbf{A}$ with solution $\mathbf{x}_\star$ = `chebyshevErrorVector` and the zero start,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{A}\mathbf{x}_\star, \mathbf{0},
q)\|_{\mathbf{A}}^2
= T_q\Bigl(\frac{a' + a}{a' - a}\Bigr)^{-2}\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$
The error is $p(\mathbf{A})\mathbf{x}_\star$ for a residual polynomial $p$, of squared
$\mathbf{A}$-norm $\sum_k\omega_k\lvert p(\xi_k)\rvert^2 \ge 1/\sum_k\omega_k$ by Cauchy–Schwarz
against $\sum_k(-1)^k\omega_k p(\xi_k) = 1$; `chebyshevResidual` attains it.
[Greenbaum1997, §3.1]; locator to verify.
Result: cg-chebyshev-sharp -/
theorem re_quadForm_sub_cgIterate_chebyshevExtremaMatrix {a a' : ℝ} (ha : 0 < a) (haa : a < a')
    (q : ℕ) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q -
        cgIterate (chebyshevExtremaMatrix 𝕜 a a' q)
          (chebyshevExtremaMatrix 𝕜 a a' q *ᵥ chebyshevErrorVector 𝕜 a a' q) 0 q)) =
      ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ ^ 2 *
        RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q)) := by
  set A := chebyshevExtremaMatrix 𝕜 a a' q
  set e := chebyshevErrorVector 𝕜 a a' q
  set τ := (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a))
  have hτ : 0 < τ := zero_lt_one.trans_le (one_le_eval_T_real (q : ℤ) (by
    rw [le_div_iff₀ (by linarith)]
    linarith))
  have hA := posDef_chebyshevExtremaMatrix (𝕜 := 𝕜) ha haa.le q
  have he : RCLike.re (quadForm A e) = τ := by
    have h := re_quadForm_chebyshevErrorVector ha haa q (fun _ => (1 : 𝕜))
    simp only [one_mul, norm_one, one_pow, mul_one] at h
    exact h.trans (sum_chebyshevWeight ha haa q)
  rw [he, inv_pow, sq, mul_inv, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one]
  refine le_antisymm ?_ ?_
  · -- the Chebyshev residual attains the value
    have h := hA.re_quadForm_sub_cgIterate_le (spectrum_chebyshevExtremaMatrix_subset_Icc haa.le q)
      (rfl : A *ᵥ e = A *ᵥ e) 0 (degree_chebyshevResidual_le a a' q)
      (eval_chebyshevResidual_zero q ha haa) (η := τ⁻¹) fun x hx => by
        have h := isUniformApproxOn_chebyshevResidual q ha haa x hx
        rwa [Real.dist_eq, sub_zero] at h
    rwa [sub_zero, he, inv_pow, sq, mul_inv, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one] at h
  · -- every residual polynomial does at least as badly
    obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_cgIterate_eq_aeval (rfl : A *ᵥ e = A *ᵥ e) 0 q
    have hpA : aeval A p =
        Matrix.diagonal (fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜)) :=
      aeval_diagonal_self _ p
    rw [hpe, sub_zero, hpA]
    have hv : Matrix.diagonal (fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜))
        *ᵥ e = fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜) * e k := by
      ext k
      rw [Matrix.mulVec_diagonal]
    rw [hv, re_quadForm_chebyshevErrorVector ha haa q]
    exact inv_eval_T_le_sum_chebyshevWeight_mul_norm_sq ha haa hp hp₀

/-- **The CG bound is tight up to $(1 + \rho^{2q})^2$**: on the same instance the squared error
ratio is $\frac{4\rho^{2q}}{(1 + \rho^{2q})^2}$, against the bound $4\rho^{2q}$ of
`Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow`. -/
theorem re_quadForm_sub_cgIterate_chebyshevExtremaMatrix_eq_four_mul_pow_div {a a' : ℝ}
    (ha : 0 < a) (haa : a < a') (q : ℕ) :
    RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q -
        cgIterate (chebyshevExtremaMatrix 𝕜 a a' q)
          (chebyshevExtremaMatrix 𝕜 a a' q *ᵥ chebyshevErrorVector 𝕜 a a' q) 0 q)) =
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) /
          (1 + ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q)) ^ 2 *
        RCLike.re (quadForm (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevErrorVector 𝕜 a a' q)) := by
  rw [re_quadForm_sub_cgIterate_chebyshevExtremaMatrix ha haa,
    inv_eval_T_real_eq_two_mul_pow_div q ha haa, div_pow, mul_pow, ← pow_mul, mul_comm q 2]
  norm_num

/-- The squared Euclidean norm as a sum of squared moduli. -/
private lemma norm_toLp_sq {ι : Type*} [Fintype ι] (v : ι → 𝕜) :
    ‖WithLp.toLp 2 v‖ ^ 2 = ∑ i, ‖v i‖ ^ 2 :=
  EuclideanSpace.norm_sq_eq _

/-- A sum over $n < 2m$ in consecutive pairs. -/
private lemma sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (m : ℕ) :
    ∑ i ∈ Finset.range (2 * m), f i = ∑ i ∈ Finset.range m, (f (2 * i) + f (2 * i + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

/-- The even part of a polynomial through `Polynomial.contract`:
$2\,(\operatorname{contract}_2 p)(x^2) = p(x) + p(-x)$. -/
private lemma two_mul_eval_contract_two_sq (p : 𝕜[X]) (x : 𝕜) :
    2 * (contract 2 p).eval (x ^ 2) = p.eval x + p.eval (-x) := by
  have hp1 : p.natDegree < 2 * (p.natDegree + 1) := by omega
  have hc : (contract 2 p).natDegree < p.natDegree + 1 := by
    refine Nat.lt_succ_of_le (natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_)
    rw [coeff_contract two_ne_zero]
    exact coeff_eq_zero_of_natDegree_lt (by omega)
  rw [eval_eq_sum_range' hc, eval_eq_sum_range' hp1, eval_eq_sum_range' hp1,
    ← Finset.sum_add_distrib, sum_range_two_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [coeff_contract two_ne_zero, Nat.mul_comm i 2, pow_succ x (2 * i), pow_succ (-x) (2 * i),
    pow_mul x 2 i, pow_mul (-x) 2 i, neg_sq]
  ring

/-- The even part has degree at most $\lfloor q/2 \rfloor$ and value $p(0)$ at $0$. -/
private lemma degree_contract_two_le_and_eval_zero {p : 𝕜[X]} {q : ℕ} (hp : p.degree ≤ q) :
    (contract 2 p).degree ≤ (q / 2 : ℕ) ∧ (contract 2 p).eval 0 = p.eval 0 := by
  refine ⟨(degree_le_iff_coeff_zero _ _).mpr fun m hm => ?_, ?_⟩
  · rw [coeff_contract two_ne_zero]
    have hkm : q / 2 < m := by exact_mod_cast hm
    exact coeff_eq_zero_of_degree_lt (hp.trans_lt (by exact_mod_cast (by omega : q < m * 2)))
  · rw [← coeff_zero_eq_eval_zero, coeff_contract two_ne_zero, zero_mul, coeff_zero_eq_eval_zero]

/-- **The even part does at least as well**: with $u = p(x)$, $v = p(-x)$ and $\omega \ge 0$,
$\omega\lvert(\operatorname{contract}_2 p)(x^2)\rvert^2 = \omega\lvert(u + v)/2\rvert^2 \le
\tfrac{\omega}{2}(\lvert u \rvert^2 + \lvert v \rvert^2)$. -/
private lemma mul_norm_eval_contract_two_sq_le (p : 𝕜[X]) (x : 𝕜) {ω : ℝ} (hω : 0 ≤ ω) :
    ω * ‖(contract 2 p).eval (x ^ 2)‖ ^ 2 ≤ ω / 2 * (‖p.eval x‖ ^ 2 + ‖p.eval (-x)‖ ^ 2) := by
  have hle : ‖(contract 2 p).eval (x ^ 2)‖ ≤ (‖p.eval x‖ + ‖p.eval (-x)‖) / 2 := by
    have h := congrArg norm (two_mul_eval_contract_two_sq p x)
    rw [norm_mul, RCLike.norm_two] at h
    have := norm_add_le (p.eval x) (p.eval (-x))
    linarith
  have h3 := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have h4 : ((‖p.eval x‖ + ‖p.eval (-x)‖) / 2) ^ 2 ≤ (‖p.eval x‖ ^ 2 + ‖p.eval (-x)‖ ^ 2) / 2 := by
    nlinarith [sq_nonneg (‖p.eval x‖ - ‖p.eval (-x)‖)]
  nlinarith

/-- Squares of $[-a', -a] \cup [a, a']$ lie in $[a^2, a'^2]$, for $0 < a$. -/
private lemma sq_mem_Icc_of_mem_union {a a' x : ℝ} (ha : 0 < a)
    (hx : x ∈ Set.Icc (-a') (-a) ∪ Set.Icc a a') : x ^ 2 ∈ Set.Icc (a ^ 2) (a' ^ 2) := by
  rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 := mul_nonneg (by linarith : (0 : ℝ) ≤ -a - x) (by linarith : (0 : ℝ) ≤ a - x)
    have e2 := mul_nonneg (by linarith : (0 : ℝ) ≤ x + a') (by linarith : (0 : ℝ) ≤ a' - x)
    constructor <;> nlinarith
  · have e1 := mul_nonneg (by linarith : (0 : ℝ) ≤ x - a) (by linarith : (0 : ℝ) ≤ x + a)
    have e2 := mul_nonneg (by linarith : (0 : ℝ) ≤ a' - x) (by linarith : (0 : ℝ) ≤ a' + x)
    constructor <;> nlinarith

/-- **MINRES attains the Chebyshev value**: for $0 < a < a'$, on the Chebyshev extrema matrix
with right-hand side $\mathbf{w}$ = `chebyshevWeightVector` and the zero start,
$$\|\mathbf{w} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{w}, \mathbf{0}, q)\| =
T_q\Bigl(\frac{a' + a}{a' - a}\Bigr)^{-1}\|\mathbf{w}\| = \frac{2\rho^q}{1 +
\rho^{2q}}\|\mathbf{w}\| \,.$$
As for CG, with residual weights $\lvert\mathbf{w}_k\rvert^2 = \omega_k$.
[Greenbaum1997, §3.1]; locator to verify.
Result: minres-chebyshev-sharp -/
theorem norm_sub_mulVec_gmresIterate_chebyshevExtremaMatrix {a a' : ℝ} (ha : 0 < a)
    (haa : a < a') (q : ℕ) :
    ‖WithLp.toLp 2 (chebyshevWeightVector 𝕜 a a' q - chebyshevExtremaMatrix 𝕜 a a' q *ᵥ
        gmresIterate (chebyshevExtremaMatrix 𝕜 a a' q) (chebyshevWeightVector 𝕜 a a' q) 0 q)‖ =
      ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ *
        ‖WithLp.toLp 2 (chebyshevWeightVector 𝕜 a a' q)‖ := by
  set A := chebyshevExtremaMatrix 𝕜 a a' q
  set w := chebyshevWeightVector 𝕜 a a' q
  set τ := (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a))
  have hτ : 0 < τ := zero_lt_one.trans_le (one_le_eval_T_real (q : ℤ) (by
    rw [le_div_iff₀ (by linarith)]
    linarith))
  have hA := posDef_chebyshevExtremaMatrix (𝕜 := 𝕜) ha haa.le q
  have hnorm : ∀ f : Fin (q + 1) → 𝕜, ‖WithLp.toLp 2 (fun k => f k * w k)‖ ^ 2 =
      ∑ k, chebyshevWeight a a' q k * ‖f k‖ ^ 2 := fun f => by
    rw [norm_toLp_sq]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [w, chebyshevWeightVector]
    rw [norm_mul, mul_pow, RCLike.norm_ofReal, sq_abs,
      Real.sq_sqrt (chebyshevWeight_pos ha haa q k).le, mul_comm]
  have hw : ‖WithLp.toLp 2 w‖ ^ 2 = τ := by
    have h := hnorm fun _ => 1
    simp only [one_mul, norm_one, one_pow, mul_one] at h
    exact h.trans (sum_chebyshevWeight ha haa q)
  refine le_antisymm ?_ ?_
  · have h := hA.isHermitian.norm_sub_mulVec_gmresIterate_le
      (spectrum_chebyshevExtremaMatrix_subset_Icc haa.le q) w 0 (degree_chebyshevResidual_le a a' q)
      (eval_chebyshevResidual_zero q ha haa) (η := τ⁻¹) fun x hx => by
        have h := isUniformApproxOn_chebyshevResidual q ha haa x hx
        rwa [Real.dist_eq, sub_zero] at h
    rwa [Matrix.mulVec_zero, sub_zero] at h
  · obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_mulVec_gmresIterate_eq_aeval A w 0 q
    rw [Matrix.mulVec_zero, sub_zero] at hpe
    have hpA : aeval A p =
        Matrix.diagonal (fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜)) :=
      aeval_diagonal_self _ p
    have hv : aeval A p *ᵥ w =
        fun k : Fin (q + 1) => p.eval (chebyshevExtremum a a' q k : 𝕜) * w k := by
      ext k
      rw [hpA, Matrix.mulVec_diagonal]
    rw [hpe, hv]
    have hsq : (τ⁻¹ * ‖WithLp.toLp 2 w‖) ^ 2 ≤
        ‖WithLp.toLp 2 (fun k : Fin (q + 1) =>
          p.eval (chebyshevExtremum a a' q k : 𝕜) * w k)‖ ^ 2 := by
      rw [hnorm, mul_pow, hw, sq, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one]
      exact inv_eval_T_le_sum_chebyshevWeight_mul_norm_sq ha haa hp hp₀
    exact (pow_le_pow_iff_left₀ (mul_nonneg (inv_nonneg.mpr hτ.le) (norm_nonneg _))
      (norm_nonneg _) two_ne_zero).mp hsq

/-- The spectrum of the two-interval matrix lies in $[-a', -a] \cup [a, a']$. -/
theorem spectrum_chebyshevTwoIntervalMatrix_subset {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a')
    (k : ℕ) :
    spectrum ℝ (chebyshevTwoIntervalMatrix 𝕜 a a' k) ⊆ Set.Icc (-a') (-a) ∪ Set.Icc a a' := by
  have hξ : ∀ j : Fin (k + 1), a ≤ Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) ∧
      Real.sqrt (chebyshevExtremum (a ^ 2) (a' ^ 2) k j) ≤ a' := fun j => by
    have h := chebyshevExtremum_mem_Icc (pow_le_pow_left₀ ha.le haa 2) k j
    exact ⟨(Real.sqrt_sq ha.le).symm.trans_le (Real.sqrt_le_sqrt h.1),
      (Real.sqrt_le_sqrt h.2).trans_eq (Real.sqrt_sq (ha.le.trans haa))⟩
  rw [← spectrum.preimage_algebraMap 𝕜, chebyshevTwoIntervalMatrix, spectrum_diagonal]
  rintro r ⟨i, hi⟩
  rcases i with j | j
  · simp only [Sum.elim_inl] at hi
    rw [RCLike.algebraMap_eq_ofReal, RCLike.ofReal_inj] at hi
    rw [← hi]
    exact Or.inr (hξ j)
  · simp only [Sum.elim_inr] at hi
    rw [RCLike.algebraMap_eq_ofReal, ← RCLike.ofReal_neg, RCLike.ofReal_inj] at hi
    rw [← hi]
    exact Or.inl ⟨neg_le_neg (hξ j).2, neg_le_neg (hξ j).1⟩

/-- **MINRES attains the two-interval value**: for $0 < a < a'$ and every $q$, with
$k = \lfloor q/2 \rfloor$, the two-interval matrix and right-hand side give
$$\|\mathbf{w} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{w}, \mathbf{0}, q)\| =
T_k\Bigl(\frac{a'^2 + a^2}{a'^2 - a^2}\Bigr)^{-1}\|\mathbf{w}\| \,,$$
which is $\frac{2\rho_2^k}{1 + \rho_2^{2k}}$ with $\rho_2 = \frac{a'/a - 1}{a'/a + 1}$, against the
bound $2\rho_2^k$. Odd steps gain nothing: the data are symmetric, so the least-squares residual
polynomial is even. For a residual $p$ of degree at most $q$ and $u = p(\sqrt{\xi_j})$,
$v = p(-\sqrt{\xi_j})$, $\lvert u \rvert^2 + \lvert v \rvert^2 \ge 2\lvert (u + v)/2 \rvert^2$, and
$(u + v)/2 = P(\xi_j)$ for the even part $P(x^2)$ of $p$, of degree at most $\lfloor q/2 \rfloor$;
so the residual is at least the interval value on $[a^2, a'^2]$, which the even Chebyshev residual
attains. [Greenbaum1997, §3.1]; locator to verify. -/
theorem norm_sub_mulVec_gmresIterate_chebyshevTwoIntervalMatrix {a a' : ℝ} (ha : 0 < a)
    (haa : a < a') (q : ℕ) :
    ‖WithLp.toLp 2 (chebyshevTwoIntervalVector 𝕜 a a' (q / 2) -
        chebyshevTwoIntervalMatrix 𝕜 a a' (q / 2) *ᵥ gmresIterate
          (chebyshevTwoIntervalMatrix 𝕜 a a' (q / 2)) (chebyshevTwoIntervalVector 𝕜 a a' (q / 2))
          0 q)‖ =
      ((T ℝ ((q / 2 : ℕ) : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2)))⁻¹ *
        ‖WithLp.toLp 2 (chebyshevTwoIntervalVector 𝕜 a a' (q / 2))‖ := by
  set k := q / 2 with hk
  set A := chebyshevTwoIntervalMatrix 𝕜 a a' k
  set w := chebyshevTwoIntervalVector 𝕜 a a' k
  set ξ := chebyshevExtremum (a ^ 2) (a' ^ 2) k
  set ω := chebyshevWeight (a ^ 2) (a' ^ 2) k
  set τ := (T ℝ (k : ℤ)).eval ((a' ^ 2 + a ^ 2) / (a' ^ 2 - a ^ 2))
  have ha2 : 0 < a ^ 2 := pow_pos ha 2
  have haa2 : a ^ 2 < a' ^ 2 := pow_lt_pow_left₀ haa ha.le two_ne_zero
  have hτ : 0 < τ := zero_lt_one.trans_le (one_le_eval_T_real (k : ℤ) (by
    rw [le_div_iff₀ (by linarith)]
    linarith))
  have hω : ∀ j, 0 < ω j := chebyshevWeight_pos ha2 haa2 k
  have hξ0 : ∀ j : Fin (k + 1), 0 ≤ ξ j := fun j =>
    ha2.le.trans (chebyshevExtremum_mem_Icc haa2.le k j).1
  have hH : A.IsHermitian := by
    change (Matrix.diagonal _).IsHermitian
    rw [Matrix.isHermitian_diagonal_iff]
    rintro (j | j)
    · exact RCLike.conj_ofReal _
    · exact IsSelfAdjoint.neg (show IsSelfAdjoint ((Real.sqrt (ξ j) : ℝ) : 𝕜) from
        RCLike.conj_ofReal _)
  have hnormS : ∀ v : Fin (k + 1) ⊕ Fin (k + 1) → 𝕜, ‖WithLp.toLp 2 v‖ ^ 2 =
      ∑ j, (‖v (Sum.inl j)‖ ^ 2 + ‖v (Sum.inr j)‖ ^ 2) := fun v => by
    rw [norm_toLp_sq, Fintype.sum_sum_type, Finset.sum_add_distrib]
  have hwl : ∀ j, ‖w (Sum.inl j)‖ ^ 2 = ω j / 2 := fun j => by
    simp only [w, chebyshevTwoIntervalVector, Sum.elim_inl]
    rw [RCLike.norm_ofReal, sq_abs, Real.sq_sqrt (by linarith [hω j])]
  have hwr : ∀ j, ‖w (Sum.inr j)‖ ^ 2 = ω j / 2 := fun j => by
    simp only [w, chebyshevTwoIntervalVector, Sum.elim_inr]
    rw [RCLike.norm_ofReal, sq_abs, Real.sq_sqrt (by linarith [hω j])]
  have hw : ‖WithLp.toLp 2 w‖ ^ 2 = τ := by
    rw [hnormS]
    refine (Finset.sum_congr rfl fun j _ => ?_).trans (sum_chebyshevWeight ha2 haa2 k)
    rw [hwl, hwr]
    ring
  refine le_antisymm ?_ ?_
  · -- the even Chebyshev residual attains the value
    have hRn : (chebyshevResidual (a ^ 2) (a' ^ 2) k).natDegree ≤ k :=
      natDegree_le_iff_degree_le.mpr (degree_chebyshevResidual_le _ _ k)
    have hP : ((chebyshevResidual (a ^ 2) (a' ^ 2) k).comp (X ^ 2)).degree ≤ q := by
      refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
      rw [natDegree_X_pow]
      omega
    have hP₀ : ((chebyshevResidual (a ^ 2) (a' ^ 2) k).comp (X ^ 2)).eval 0 = 1 := by
      rw [eval_comp, eval_pow, eval_X, zero_pow two_ne_zero]
      exact eval_chebyshevResidual_zero k ha2 haa2
    have h := hH.norm_sub_mulVec_gmresIterate_le (spectrum_chebyshevTwoIntervalMatrix_subset ha
      haa.le k) w 0 hP hP₀ (η := τ⁻¹) fun x hx => by
        have h := isUniformApproxOn_chebyshevResidual k ha2 haa2 _ (sq_mem_Icc_of_mem_union ha hx)
        rw [Real.dist_eq, sub_zero] at h
        rwa [eval_comp, eval_pow, eval_X]
    rwa [Matrix.mulVec_zero, sub_zero] at h
  · -- every residual polynomial does at least as badly, through its even part
    obtain ⟨p, hp, hp₀, hpe⟩ := exists_sub_mulVec_gmresIterate_eq_aeval A w 0 q
    rw [Matrix.mulVec_zero, sub_zero] at hpe
    have hpA : aeval A p = Matrix.diagonal (fun i => p.eval (Sum.elim
        (fun j : Fin (k + 1) => ((Real.sqrt (ξ j) : ℝ) : 𝕜))
        (fun j : Fin (k + 1) => -((Real.sqrt (ξ j) : ℝ) : 𝕜)) i)) :=
      aeval_diagonal_self _ p
    obtain ⟨hPd, hP₀⟩ := degree_contract_two_le_and_eval_zero hp
    rw [hp₀] at hP₀
    have hterm : ∀ j, ω j * ‖(contract 2 p).eval (ξ j : 𝕜)‖ ^ 2 ≤
        ‖(aeval A p *ᵥ w) (Sum.inl j)‖ ^ 2 + ‖(aeval A p *ᵥ w) (Sum.inr j)‖ ^ 2 := fun j => by
      have hx2 : ((Real.sqrt (ξ j) : ℝ) : 𝕜) ^ 2 = (ξ j : 𝕜) := by
        rw [← RCLike.ofReal_pow, Real.sq_sqrt (hξ0 j)]
      rw [← hx2, hpA, Matrix.mulVec_diagonal, Matrix.mulVec_diagonal]
      simp only [Sum.elim_inl, Sum.elim_inr]
      rw [norm_mul, norm_mul, mul_pow, mul_pow, hwl, hwr]
      have h := mul_norm_eval_contract_two_sq_le p ((Real.sqrt (ξ j) : ℝ) : 𝕜) (hω j).le
      linarith
    have hres : τ⁻¹ ≤ ‖WithLp.toLp 2 (aeval A p *ᵥ w)‖ ^ 2 := by
      rw [hnormS]
      exact (inv_eval_T_le_sum_chebyshevWeight_mul_norm_sq ha2 haa2 hPd hP₀).trans
        (Finset.sum_le_sum fun j _ => hterm j)
    rw [hpe]
    have hsq : (τ⁻¹ * ‖WithLp.toLp 2 w‖) ^ 2 ≤ ‖WithLp.toLp 2 (aeval A p *ᵥ w)‖ ^ 2 := by
      rw [mul_pow, hw, sq, mul_assoc, inv_mul_cancel₀ hτ.ne', mul_one]
      exact hres
    exact (pow_le_pow_iff_left₀ (mul_nonneg (inv_nonneg.mpr hτ.le) (norm_nonneg _))
      (norm_nonneg _) two_ne_zero).mp hsq

end NLAlib
