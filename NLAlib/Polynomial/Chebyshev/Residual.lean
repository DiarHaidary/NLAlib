/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Extremal
public import NLAlib.ForMathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Growth
public import NLAlib.ForMathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.RootsExtrema
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Normalized Chebyshev residuals

The shifted Chebyshev polynomial normalized at zero, with uniform bounds on a positive interval.
Degree and error remain separate, so the same metric approximation interface serves other functions.

## Main results

* `NLAlib.chebyshevResidual`: the normalized residual polynomial.
* `NLAlib.degree_chebyshevResidual_le`: unconditional degree bound.
* `NLAlib.eval_chebyshevResidual_zero`: normalization on a positive nondegenerate interval.
* `NLAlib.isUniformApproxOn_chebyshevResidual`: the reciprocal-Chebyshev error bound.
* `NLAlib.isUniformApproxOn_chebyshevResidual_two_mul_pow`: geometric decay.
* `NLAlib.isLeast_chebyshev_minimax`: exact optimality among normalized residuals.
* `NLAlib.residualMinimax`: the residual minimax value of a set, with
  `NLAlib.residualMinimax_le` and its Chebyshev value on an interval,
  `NLAlib.residualMinimax_Icc`.
* `NLAlib.inv_eval_T_real_eq_two_mul_pow_div`: the Chebyshev value
  $T_q\bigl(\frac{a' + a}{a' - a}\bigr)^{-1} = \frac{2\rho^q}{1 + \rho^{2q}}$ in
  $\rho = \frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}$.
* `NLAlib.exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow`: a residual polynomial that
  kills finitely many outliers and decays at the Chebyshev rate on an interval.
* `NLAlib.chebyshevExtremum`, `NLAlib.chebyshevWeight`: the $q + 1$ points where the normalised
  Chebyshev residual alternates (`NLAlib.eval_chebyshevResidual_chebyshevExtremum`) and their dual
  weights $\lvert\ell_k(0)\rvert$ for the Lagrange basis, with
  `NLAlib.sum_neg_one_pow_mul_chebyshevWeight_mul_eval` and `NLAlib.sum_chebyshevWeight`; the
  worst-case instances of `NLAlib.Krylov.LinearSystems.WorstCase` are built from them.
-/

@[expose] public section

open Polynomial Polynomial.Chebyshev

namespace NLAlib

/-- The normalized residual is
$$r_q(x)=\frac{T_q((b+a-2x)/(b-a))}{T_q((b+a)/(b-a))}.$$
For $0<a<b$ it equals one at zero and is small on $[a,b]$.
[Saad2003, Theorem 6.25 and following corollary]. The definition is total: division by zero
uses Lean's zero inverse. If the normalizing denominator vanishes, the polynomial is zero;
when $a=b$, both affine coefficients are zero, so the result is the constant
$T_q(0)^{-1}T_q(0)$. No normalization is asserted outside $0<a<b$.
-/
noncomputable def chebyshevResidual (a b : ℝ) (q : ℕ) : ℝ[X] :=
  Polynomial.C (((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (q : ℤ)).comp
      (Polynomial.C ((b + a) / (b - a)) - Polynomial.C (2 / (b - a)) * Polynomial.X)

/-- Evaluation of the normalized residual by the scalar Chebyshev quotient. -/
theorem eval_chebyshevResidual (a b : ℝ) (q : ℕ) (x : ℝ) :
    (chebyshevResidual a b q).eval x =
      (T ℝ (q : ℤ)).eval ((b + a) / (b - a) - 2 / (b - a) * x) /
        (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
  simp only [chebyshevResidual, eval_mul, eval_C, eval_comp, eval_sub, eval_X]
  simp only [div_eq_mul_inv]
  exact mul_comm _ _

/-- The normalized residual has degree at most $q$, including degenerate parameters. -/
theorem degree_chebyshevResidual_le (a b : ℝ) (q : ℕ) :
    (chebyshevResidual a b q).degree ≤ (q : WithBot ℕ) := by
  unfold chebyshevResidual
  refine ((congrArg degree (C_mul' _ _)).trans_le (degree_smul_le _ _)).trans
    (degree_le_natDegree.trans ?_)
  have hd : (C ((b + a) / (b - a)) - C (2 / (b - a)) * X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans (max_le (by simp only [natDegree_C, zero_le]) ?_)
    exact (natDegree_C_mul_le _ _).trans (by simp only [natDegree_X, le_refl])
  have h : ((T ℝ (q : ℤ)).comp
      (C ((b + a) / (b - a)) - C (2 / (b - a)) * X)).natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    rw [natDegree_T, Int.natAbs_natCast]
    exact (Nat.mul_le_mul_left q hd).trans_eq (mul_one q)
  exact_mod_cast h

/-- For $0<a<b$, the residual equals one at zero.
[Saad2003, Theorem 6.25 and following corollary]. -/
theorem eval_chebyshevResidual_zero {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    (chebyshevResidual a b q).eval 0 = 1 := by
  have hT := one_le_eval_T_real (q : ℤ) (show 1 ≤ (b + a) / (b - a) by
    rw [le_div_iff₀ (by linarith)]
    linarith)
  rw [eval_chebyshevResidual, mul_zero, sub_zero, div_self (by linarith)]

/-- On $[a,b]$, where $0<a<b$, the residual satisfies
$$|r_q(x)|\le T_q((b+a)/(b-a))^{-1}.$$
[Saad2003, Theorem 6.25 and following corollary].

Result: chebyshev-residual
-/
theorem isUniformApproxOn_chebyshevResidual {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    Metric.IsUniformApproxOn (chebyshevResidual a b q).eval (fun _ => 0) (Set.Icc a b)
      (((T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹) := by
  intro x hx
  have hba : 0 < b - a := by linarith
  have hT := one_le_eval_T_real (q : ℤ) (show 1 ≤ (b + a) / (b - a) by
    rw [le_div_iff₀ hba]
    linarith)
  have hy : |(b + a) / (b - a) - 2 / (b - a) * x| ≤ 1 := by
    have he : (b + a) / (b - a) - 2 / (b - a) * x = (b + a - 2 * x) / (b - a) := by
      field_simp
    rw [he, abs_le, le_div_iff₀ hba, div_le_iff₀ hba]
    constructor <;> linarith [hx.1, hx.2]
  change |(chebyshevResidual a b q).eval x - 0| ≤ _
  rw [sub_zero, eval_chebyshevResidual, abs_div,
    abs_of_pos (show 0 < (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) by linarith),
    ← one_div]
  exact div_le_div_of_nonneg_right (abs_eval_T_real_le_one _ hy) (by linarith)

/-- For $0<a<b$, the uniform residual bound has geometric form
$$|r_q(x)|\le2\left(\frac{\sqrt b-\sqrt a}{\sqrt b+\sqrt a}\right)^q
\quad(x\in[a,b]).$$
At $q=0$ this remains valid with residual one and upper bound two.
[Saad2003, proof of Theorem 6.29, Eq. (6.128)], stated as a scalar residual estimate.

Result: chebyshev-residual
-/
theorem isUniformApproxOn_chebyshevResidual_two_mul_pow {a b : ℝ} (q : ℕ)
    (ha : 0 < a) (hab : a < b) :
    Metric.IsUniformApproxOn (chebyshevResidual a b q).eval (fun _ => 0) (Set.Icc a b)
      (2 * ((Real.sqrt b - Real.sqrt a) / (Real.sqrt b + Real.sqrt a)) ^ q) := by
  apply (isUniformApproxOn_chebyshevResidual q ha hab).mono_error
  have hlow := sqrt_add_div_sqrt_sub_pow_div_two_le_eval_T_real ha hab q
  have hsa := Real.sqrt_pos.2 ha
  have hsb : √a < √b := Real.sqrt_lt_sqrt ha.le hab
  have hρ : 0 < ((√b + √a) / (√b - √a)) ^ q := by
    apply pow_pos
    apply div_pos <;> linarith
  have hT : 0 < (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) := by
    linarith [div_pos hρ two_pos]
  have hinv : (√b - √a) / (√b + √a) = ((√b + √a) / (√b - √a))⁻¹ := by
    rw [inv_div]
  rw [hinv, inv_pow, ← div_eq_mul_inv, ← one_div, div_le_div_iff₀ hT hρ]
  linarith

/-- A polynomial of degree at most $q$, equal to one at zero and uniformly bounded by $M$
on $[a,b]$ with $0<a<b$, satisfies
$$T_q((b+a)/(b-a))^{-1}\le M.$$
[Saad2003, Theorem 6.25 and following corollary], expressed through the metric approximation
interface. This includes $q=0$, when the lower bound is one. -/
theorem inv_eval_T_real_le_of_isUniformApproxOn
    {a b M : ℝ} {q : ℕ} {p : ℝ[X]}
    (ha : 0 < a) (hab : a < b) (hp : p.degree ≤ (q : WithBot ℕ)) (hp0 : p.eval 0 = 1)
    (hb : Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc a b) M) :
    ((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹ ≤ M := by
  have hba : 0 < b - a := by linarith
  have hs : 1 ≤ (b + a) / (b - a) := by
    rw [le_div_iff₀ hba]
    linarith
  have hT := one_le_eval_T_real (q : ℤ) hs
  let L : ℝ[X] := C ((b + a) / 2) - C ((b - a) / 2) * X
  have hLe : ∀ t, L.eval t = (b + a) / 2 - (b - a) / 2 * t := fun t => by
    simp only [L, eval_sub, eval_C, eval_mul, eval_X]
  have hP : (p.comp L).degree ≤ (q : WithBot ℕ) := by
    refine degree_le_natDegree.trans ?_
    have hn : (p.comp L).natDegree ≤ q := by
      refine natDegree_comp_le.trans ?_
      have hL : L.natDegree ≤ 1 := by
        refine (natDegree_sub_le _ _).trans (max_le (by simp only [natDegree_C, zero_le]) ?_)
        exact (natDegree_C_mul_le _ _).trans (by simp only [natDegree_X, le_refl])
      exact (Nat.mul_le_mul (natDegree_le_iff_degree_le.mpr hp) hL).trans_eq (mul_one q)
    exact_mod_cast hn
  have hPb : Metric.IsUniformApproxOn (p.comp L).eval (fun _ => 0)
      (Set.Icc (-1 : ℝ) 1) M := by
    intro t ht
    change |(p.comp L).eval t - 0| ≤ M
    rw [eval_comp, hLe]
    have hi : (b + a) / 2 - (b - a) / 2 * t ∈ Set.Icc a b :=
      ⟨by nlinarith [ht.2], by nlinarith [ht.1]⟩
    simpa only [Real.dist_eq] using hb.apply hi
  have hPs : (p.comp L).eval ((b + a) / (b - a)) = 1 := by
    rw [eval_comp, hLe, ← hp0]
    congr 1
    field_simp
    ring
  have h := abs_eval_le_mul_abs_eval_T_real_of_isUniformApproxOn hP hPb
    (hs.trans (le_abs_self _))
  rw [hPs, abs_one, abs_of_pos (show 0 < (T ℝ (q : ℤ)).eval ((b + a) / (b - a)) by
    linarith)] at h
  rw [← one_div, div_le_iff₀ (by linarith)]
  exact h

/-- Among polynomials of degree at most $q$ equal to one at zero, the least uniform bound
on $[a,b]$, where $0<a<b$, is $T_q((b+a)/(b-a))^{-1}$. It is attained by
`chebyshevResidual`, including $q=0$ with optimum one.
[Saad2003, Theorem 6.25 and following corollary].

Result: chebyshev-minimax
-/
theorem isLeast_chebyshev_minimax {a b : ℝ} (q : ℕ) (ha : 0 < a) (hab : a < b) :
    IsLeast {M : ℝ | ∃ p : ℝ[X], p.degree ≤ (q : WithBot ℕ) ∧ p.eval 0 = 1 ∧
      Metric.IsUniformApproxOn p.eval (fun _ => 0) (Set.Icc a b) M}
      (((Polynomial.Chebyshev.T ℝ (q : ℤ)).eval ((b + a) / (b - a)))⁻¹) :=
  ⟨⟨chebyshevResidual a b q, degree_chebyshevResidual_le a b q,
      eval_chebyshevResidual_zero q ha hab, isUniformApproxOn_chebyshevResidual q ha hab⟩,
    fun _ ⟨_, hp, hp0, hb⟩ => inv_eval_T_real_le_of_isUniformApproxOn ha hab hp hp0 hb⟩

/-! ### The residual minimax value -/

/-- The **residual minimax value** of a set $s$ at degree $q$:
$\mathsf{residualMinimax}(s, q) := \inf_{p}\,\sup_{x \in s}\lvert p(x) \rvert$ over real $p$ with
$\deg p \le q$ and $p(0) = 1$. Junk values: $0$ for $s = \emptyset$; for unbounded $s$ and
$q \ge 1$ every nonconstant $\lvert p \rvert$ is unbounded on $s$ and its supremum is $0$
(Mathlib's `Real.iSup` of an unbounded family), so the value is $0$; at $q = 0$ it is $1$ on any
nonempty $s$. It is meaningful for bounded $s$, in particular a finite spectrum and $[a, a']$.
[Greenbaum1997, §3.1]; locator to verify. -/
noncomputable def residualMinimax (s : Set ℝ) (q : ℕ) : ℝ :=
  ⨅ p : {p : ℝ[X] // p.degree ≤ q ∧ p.eval 0 = 1}, ⨆ x ∈ s, |p.1.eval x|

/-- The residual minimax value is nonnegative. -/
theorem residualMinimax_nonneg (s : Set ℝ) (q : ℕ) : 0 ≤ residualMinimax s q :=
  Real.iInf_nonneg fun _ => Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _

/-- **Every residual polynomial bounds the minimax value**: if $\deg p \le q$, $p(0) = 1$ and
$\lvert p \rvert \le \eta$ on $s$ with $0 \le \eta$, then $\mathsf{residualMinimax}(s, q) \le
\eta$. -/
theorem residualMinimax_le {s : Set ℝ} {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1)
    {η : ℝ} (hη₀ : 0 ≤ η) (hη : ∀ x ∈ s, |p.eval x| ≤ η) : residualMinimax s q ≤ η := by
  refine (ciInf_le ⟨0, ?_⟩ (⟨p, hp, hp₀⟩ : {p : ℝ[X] // p.degree ≤ q ∧ p.eval 0 = 1})).trans ?_
  · rintro _ ⟨p, rfl⟩
    exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  · exact Real.iSup_le (fun x => Real.iSup_le (fun hx => hη x hx) hη₀) hη₀

/-- **The minimax value of an interval is the Chebyshev value**: for $0 < a < a'$,
$\mathsf{residualMinimax}([a, a'], q) = T_q\bigl(\frac{a' + a}{a' - a}\bigr)^{-1}$.
[Saad2003, Theorem 6.25]. -/
theorem residualMinimax_Icc {a a' : ℝ} (q : ℕ) (ha : 0 < a) (haa : a < a') :
    residualMinimax (Set.Icc a a') q = ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ := by
  have hT : 0 ≤ ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ :=
    inv_nonneg.mpr ((zero_le_one).trans (one_le_eval_T_real (q : ℤ) (by
      rw [le_div_iff₀ (by linarith)]
      linarith)))
  refine le_antisymm (residualMinimax_le (degree_chebyshevResidual_le a a' q)
    (eval_chebyshevResidual_zero q ha haa) hT fun x hx => ?_) ?_
  · have h := isUniformApproxOn_chebyshevResidual q ha haa x hx
    rwa [Real.dist_eq, sub_zero] at h
  · have : Nonempty {p : ℝ[X] // p.degree ≤ q ∧ p.eval 0 = 1} :=
      ⟨⟨1, degree_one_le.trans (by exact_mod_cast Nat.zero_le q), eval_one⟩⟩
    refine le_ciInf fun ⟨p, hp, hp₀⟩ => inv_eval_T_real_le_of_isUniformApproxOn ha haa hp hp₀ ?_
    intro x hx
    rw [Real.dist_eq, sub_zero]
    obtain ⟨M, hM⟩ := (isCompact_Icc.image (Polynomial.continuous p).abs).bddAbove
    refine le_ciSup₂ (f := fun x (_ : x ∈ Set.Icc a a') => |p.eval x|) ⟨M, fun z hz => ?_⟩ x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hz
    obtain ⟨y, hy, rfl⟩ := hz
    exact hM ⟨y, hy, rfl⟩

/-- **The Chebyshev value in $\kappa = a'/a$**: for $0 < a < a'$,
$$T_q\Bigl(\frac{a' + a}{a' - a}\Bigr)^{-1} = \frac{2\rho^q}{1 + \rho^{2q}} \,,\qquad
\rho = \frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1} \,.$$ -/
theorem inv_eval_T_real_eq_two_mul_pow_div {a a' : ℝ} (q : ℕ) (ha : 0 < a) (haa : a < a') :
    ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ =
      2 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ q /
        (1 + ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q)) := by
  set s := Real.sqrt (a' / a) with hs_def
  have hκ : 1 < a' / a := by rw [one_lt_div ha]; exact haa
  have hs1 : 1 < s := by rw [hs_def, Real.lt_sqrt zero_le_one, one_pow]; exact hκ
  have hss : s ^ 2 = a' / a := Real.sq_sqrt (by positivity)
  have hσ : (a' + a) / (a' - a) = (s ^ 2 + 1) / (s ^ 2 - 1) := by
    rw [hss]
    field_simp
  have hσ1 : 1 ≤ (a' + a) / (a' - a) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hd : 0 < s ^ 2 - 1 := by nlinarith
  have hsq : Real.sqrt (((a' + a) / (a' - a)) ^ 2 - 1) = 2 * s / (s ^ 2 - 1) := by
    rw [hσ, show ((s ^ 2 + 1) / (s ^ 2 - 1)) ^ 2 - 1 = (2 * s / (s ^ 2 - 1)) ^ 2 by
      field_simp
      ring]
    exact Real.sqrt_sq (div_nonneg (by linarith) hd.le)
  have hρ0 : 0 < (s - 1) / (s + 1) := div_pos (by linarith) (by linarith)
  have hs1' : s - 1 ≠ 0 := by linarith
  have hs1'' : s + 1 ≠ 0 := by linarith
  have hplus : (a' + a) / (a' - a) + Real.sqrt (((a' + a) / (a' - a)) ^ 2 - 1) =
      ((s - 1) / (s + 1))⁻¹ := by
    rw [hsq, hσ, inv_div]
    field_simp
    ring
  have hminus : (a' + a) / (a' - a) - Real.sqrt (((a' + a) / (a' - a)) ^ 2 - 1) =
      (s - 1) / (s + 1) := by
    rw [hsq, hσ]
    field_simp
    ring
  rw [eval_T_real_eq_of_one_le hσ1, hplus, hminus]
  set ρ := (s - 1) / (s + 1)
  have hρq : 0 < ρ ^ q := pow_pos hρ0 q
  rw [inv_pow, pow_mul', inv_div]
  field_simp

/-! ### Killing outliers -/

/-- The polynomial $\prod_{t \in T}(1 - X/t)$: value $1$ at $0$, zero at every nonzero
$t \in T$, degree at most $\lvert T \rvert$. -/
private lemma exists_outlierPolynomial (T : Finset ℝ) :
    ∃ P : ℝ[X], P.natDegree ≤ T.card ∧ P.eval 0 = 1 ∧ (∀ t ∈ T, t ≠ 0 → P.eval t = 0) ∧
      ∀ x, P.eval x = ∏ t ∈ T, (1 - x / t) := by
  refine ⟨∏ t ∈ T, (1 - C t⁻¹ * X), ?_, ?_, fun t ht ht0 => ?_, fun x => ?_⟩
  · refine (natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 1 fun t _ => ?_).trans (by rw [smul_eq_mul, mul_one])
    refine (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; exact zero_le_one) ?_)
    exact (natDegree_C_mul_le _ _).trans (by rw [natDegree_X])
  · simp only [eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X, mul_zero, sub_zero,
      Finset.prod_const_one]
  · rw [eval_prod]
    refine Finset.prod_eq_zero ht ?_
    simp only [eval_sub, eval_one, eval_mul, eval_C, eval_X, inv_mul_cancel₀ ht0, sub_self]
  · simp only [eval_prod, eval_sub, eval_one, eval_mul, eval_C, eval_X, div_eq_inv_mul]

/-- **Killing outliers with a Chebyshev residual**: for $0 < a$, a finite set $T$ of reals and
$\lvert\prod_{t \in T}(1 - x/t)\rvert \le C$ on $[a, a']$, there is a real polynomial $p$ with
$\deg p \le \lvert T \rvert + d$, $p(0) = 1$, $p(t) = 0$ for every nonzero $t \in T$, and
$$\lvert p(x) \rvert \le 2C\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^d
\quad (x \in [a, a']) \,.$$
For $a < a'$ it is $\prod_{t \in T}(1 - X/t)$ times `chebyshevResidual a a' d`; for $a = a'$ the
second factor is $(1 - X/a)^d$; for $a' < a$ the interval is empty and the product alone serves.
[Greenbaum1997, §3.1]; locator to verify. -/
theorem exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow {a a' : ℝ} (ha : 0 < a)
    (T : Finset ℝ) (d : ℕ) {C : ℝ} (hC : ∀ x ∈ Set.Icc a a', |∏ t ∈ T, (1 - x / t)| ≤ C) :
    ∃ p : ℝ[X], p.degree ≤ ↑(T.card + d) ∧ p.eval 0 = 1 ∧ (∀ t ∈ T, t ≠ 0 → p.eval t = 0) ∧
      ∀ x ∈ Set.Icc a a',
        |p.eval x| ≤ 2 * C * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ d := by
  obtain ⟨P, hPd, hP₀, hPT, hPe⟩ := exists_outlierPolynomial T
  rcases lt_trichotomy a a' with hlt | rfl | hgt
  · refine ⟨P * chebyshevResidual a a' d, ?_, ?_, fun t ht ht0 => ?_, fun x hx => ?_⟩
    · refine degree_le_of_natDegree_le (natDegree_mul_le.trans (Nat.add_le_add hPd ?_))
      exact natDegree_le_iff_degree_le.mpr (degree_chebyshevResidual_le a a' d)
    · rw [eval_mul, hP₀, eval_chebyshevResidual_zero d ha hlt, mul_one]
    · rw [eval_mul, hPT t ht ht0, zero_mul]
    · have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x hx)
      have hr := isUniformApproxOn_chebyshevResidual_two_mul_pow d ha hlt x hx
      rw [Real.dist_eq, sub_zero] at hr
      have hρ : (Real.sqrt a' - Real.sqrt a) / (Real.sqrt a' + Real.sqrt a) =
          (Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1) := by
        have hsa := Real.sqrt_pos.2 ha
        rw [Real.sqrt_div' _ ha.le]
        field_simp
      rw [hρ] at hr
      rw [eval_mul, abs_mul, hPe, mul_assoc, mul_left_comm]
      exact mul_le_mul (hC x hx) hr (abs_nonneg _) hC0
  · refine ⟨P * (1 - Polynomial.C a⁻¹ * X) ^ d, ?_, ?_, fun t ht ht0 => ?_, fun x hx => ?_⟩
    · refine degree_le_of_natDegree_le (natDegree_mul_le.trans (Nat.add_le_add hPd ?_))
      refine natDegree_pow_le.trans ?_
      have h1 : (1 - Polynomial.C a⁻¹ * X : ℝ[X]).natDegree ≤ 1 :=
        (natDegree_sub_le _ _).trans (max_le (by rw [natDegree_one]; exact zero_le_one)
          ((natDegree_C_mul_le _ _).trans (by rw [natDegree_X])))
      exact (Nat.mul_le_mul_left d h1).trans_eq (mul_one d)
    · simp only [eval_mul, hP₀, eval_pow, eval_sub, eval_one, eval_C, eval_X, mul_zero, sub_zero,
        one_pow, mul_one]
    · rw [eval_mul, hPT t ht ht0, zero_mul]
    · rw [Set.Icc_self, Set.mem_singleton_iff] at hx
      subst hx
      have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC x (Set.left_mem_Icc.mpr le_rfl))
      have hP := hC x (Set.left_mem_Icc.mpr le_rfl)
      rw [div_self ha.ne', Real.sqrt_one, sub_self, zero_div]
      simp only [eval_mul, eval_pow, eval_sub, eval_one, eval_C, eval_X, inv_mul_cancel₀ ha.ne',
        sub_self, abs_mul, abs_pow, abs_zero, hPe]
      exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg le_rfl d)
  · refine ⟨P, degree_le_of_natDegree_le (hPd.trans (Nat.le_add_right _ _)), hP₀, hPT,
      fun x hx => ?_⟩
    exact absurd (hx.1.trans hx.2) (not_le.mpr hgt)

/-! ### Chebyshev extrema and the dual weights -/

/-- The $k$-th **Chebyshev extremum** on $[a, a']$ at degree $q$:
$\xi_k = \frac{a' + a}{2} - \frac{a' - a}{2}\cos\frac{k\pi}{q}$, increasing in $k = 0, \dots, q$,
where the normalised Chebyshev residual takes the values $\pm T_q(\frac{a' + a}{a' - a})^{-1}$
alternately. Junk value: for $q = 0$ it is $a$. -/
noncomputable def chebyshevExtremum (a a' : ℝ) (q k : ℕ) : ℝ :=
  (a' + a) / 2 - (a' - a) / 2 * Real.cos (k * Real.pi / q)

/-- The Chebyshev extrema lie in $[a, a']$. -/
theorem chebyshevExtremum_mem_Icc {a a' : ℝ} (haa : a ≤ a') (q k : ℕ) :
    chebyshevExtremum a a' q k ∈ Set.Icc a a' := by
  have h1 := Real.neg_one_le_cos (k * Real.pi / q)
  have h2 := Real.cos_le_one (k * Real.pi / q)
  have hd : 0 ≤ (a' - a) / 2 := by linarith
  constructor <;> unfold chebyshevExtremum <;> nlinarith

/-- The Chebyshev extrema $\xi_0 < \dots < \xi_q$ are strictly increasing. -/
theorem strictMono_chebyshevExtremum {a a' : ℝ} (haa : a < a') (q : ℕ) :
    StrictMono fun k : Fin (q + 1) => chebyshevExtremum a a' q k := by
  intro k l hkl
  have hq : (0 : ℝ) < q := by
    have hkl₀ : (k : ℕ) < l := hkl
    exact_mod_cast (show 0 < q by omega)
  have hkl' : ((k : ℕ) : ℝ) < (l : ℕ) := by exact_mod_cast hkl
  have hl : ((l : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.lt_succ_iff.mp l.is_lt
  have hc : Real.cos (l * Real.pi / q) < Real.cos (k * Real.pi / q) := by
    refine Real.cos_lt_cos_of_nonneg_of_le_pi (by positivity) ?_ ?_
    · rw [div_le_iff₀ hq]
      nlinarith [Real.pi_pos]
    · exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hkl' Real.pi_pos) hq
  have hd : 0 < (a' - a) / 2 := by linarith
  simp only [chebyshevExtremum]
  nlinarith

/-- The affine map of the Chebyshev residual sends the $k$-th extremum to $\cos(k\pi/q)$. -/
private lemma chebyshevResidual_arg_chebyshevExtremum {a a' : ℝ} (haa : a < a') (q k : ℕ) :
    (a' + a) / (a' - a) - 2 / (a' - a) * chebyshevExtremum a a' q k =
      Real.cos (k * Real.pi / q) := by
  have hd : a' - a ≠ 0 := by linarith
  unfold chebyshevExtremum
  field_simp
  ring

/-- **The residual alternates at the extrema**: for $a < a'$ and $k \le q$,
$p_q(\xi_k) = (-1)^k T_q\bigl(\frac{a' + a}{a' - a}\bigr)^{-1}$ for $p_q$ =
`chebyshevResidual a a' q`. -/
theorem eval_chebyshevResidual_chebyshevExtremum {a a' : ℝ} (haa : a < a')
    {q k : ℕ} (hk : k ≤ q) :
    (chebyshevResidual a a' q).eval (chebyshevExtremum a a' q k) =
      (-1) ^ k * ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ := by
  rw [eval_chebyshevResidual, chebyshevResidual_arg_chebyshevExtremum haa, T_real_cos,
    div_eq_mul_inv]
  congr 1
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · obtain rfl : k = 0 := Nat.le_zero.mp hk
    simp
  · rw [Int.cast_natCast, mul_div_cancel₀ _ (by exact_mod_cast hq.ne'), Real.cos_nat_mul_pi]

/-- The **dual weight** of the $k$-th Chebyshev extremum, $\omega_k = \lvert\ell_k(0)\rvert$ for the
Lagrange basis $\ell_0, \dots, \ell_q$ at $\xi_0, \dots, \xi_q$: the weights of the discrete
problem whose least-squares and minimax solutions coincide. -/
noncomputable def chebyshevWeight (a a' : ℝ) (q : ℕ) (k : Fin (q + 1)) : ℝ :=
  |(Lagrange.basis Finset.univ (fun j : Fin (q + 1) => chebyshevExtremum a a' q j) k).eval 0|

/-- The Lagrange basis at real nodes, evaluated at $0$ over $\Bbbk$, is the real value. -/
private lemma eval_lagrangeBasis_ofReal_zero {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (v : ι → ℝ) (i : ι) :
    (Lagrange.basis s (fun j => (v j : 𝕜)) i).eval 0 =
      (((Lagrange.basis s v i).eval 0 : ℝ) : 𝕜) := by
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C, eval_sub,
    eval_X, RCLike.ofReal_prod, RCLike.ofReal_mul, RCLike.ofReal_inv, RCLike.ofReal_sub,
    RCLike.ofReal_zero]

/-- The Lagrange basis at the Chebyshev extrema has $\ell_k(0) = (-1)^k\omega_k$: the nodes are
positive and increasing, so $\ell_k(0) = \prod_{j \ne k}\frac{\xi_j}{\xi_j - \xi_k}$ has $k$
negative factors. -/
private lemma eval_lagrangeBasis_chebyshevExtremum_zero {a a' : ℝ} (ha : 0 < a) (haa : a < a')
    {q : ℕ} (k : Fin (q + 1)) :
    (Lagrange.basis Finset.univ (fun j : Fin (q + 1) => chebyshevExtremum a a' q j) k).eval 0 =
      (-1) ^ (k : ℕ) * chebyshevWeight a a' q k := by
  set ξ := fun j : Fin (q + 1) => chebyshevExtremum a a' q j
  have hmono := strictMono_chebyshevExtremum haa q
  have hpos : ∀ j, 0 < ξ j := fun j => ha.trans_le (chebyshevExtremum_mem_Icc haa.le q j).1
  have hfac : ∀ j ∈ Finset.univ.erase k, (ξ k - ξ j)⁻¹ * (0 - ξ j) =
      (if j < k then -1 else 1) * |(ξ k - ξ j)⁻¹ * (0 - ξ j)| := by
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    split_ifs with h
    · have : ξ j < ξ k := hmono h
      rw [abs_of_neg (mul_neg_of_pos_of_neg (inv_pos.2 (by linarith)) (by linarith [hpos j]))]
      ring
    · have : ξ k < ξ j := hmono (lt_of_le_of_ne (not_lt.mp h) (Ne.symm hjk))
      rw [abs_of_pos (mul_pos_of_neg_of_neg (inv_lt_zero.2 (by linarith)) (by linarith [hpos j]))]
      ring
  have hcard : ((Finset.univ.erase k).filter (· < k)).card = k := by
    rw [show (Finset.univ.erase k).filter (· < k) = Finset.Iio k by
      ext j
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, Finset.mem_Iio]
      exact ⟨fun h => h.2, fun h => ⟨⟨h.ne, trivial⟩, h⟩⟩]
    exact Fin.card_Iio k
  have hℓ : (Lagrange.basis Finset.univ ξ k).eval 0 =
      (-1) ^ (k : ℕ) * ∏ j ∈ Finset.univ.erase k, |(ξ k - ξ j)⁻¹ * (0 - ξ j)| := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C, eval_sub,
      eval_X]
    rw [Finset.prod_congr rfl hfac, Finset.prod_mul_distrib, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one, hcard]
  rw [chebyshevWeight, hℓ, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Finset.prod_nonneg fun j _ => abs_nonneg _)]

/-- **The signed dual weights evaluate at $0$**: for $0 < a < a'$ and every $p \in \Bbbk[X]$ with
$\deg p \le q$, $\sum_k (-1)^k\omega_k\,p(\xi_k) = p(0)$. -/
theorem sum_neg_one_pow_mul_chebyshevWeight_mul_eval {𝕜 : Type*} [RCLike 𝕜] {a a' : ℝ}
    (ha : 0 < a) (haa : a < a') {q : ℕ} {p : 𝕜[X]} (hp : p.degree ≤ q) :
    ∑ k : Fin (q + 1), ((-1) ^ (k : ℕ) * chebyshevWeight a a' q k : ℝ) *
      p.eval (chebyshevExtremum a a' q k : 𝕜) = p.eval 0 := by
  have hinj : Set.InjOn (fun j : Fin (q + 1) => (chebyshevExtremum a a' q j : 𝕜))
      (Finset.univ : Finset (Fin (q + 1))) :=
    fun i _ j _ h => (strictMono_chebyshevExtremum haa q).injective (RCLike.ofReal_injective h)
  have hdeg : p.degree < (Finset.univ : Finset (Fin (q + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact hp.trans_lt (by exact_mod_cast Nat.lt_succ_self q)
  conv_rhs => rw [Lagrange.eq_interpolate hinj hdeg]
  rw [Lagrange.interpolate_apply, eval_finsetSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [eval_mul, eval_C, eval_lagrangeBasis_ofReal_zero,
    eval_lagrangeBasis_chebyshevExtremum_zero ha haa, mul_comm]

/-- **The dual weights sum to the Chebyshev value**: for $0 < a < a'$,
$\sum_k \omega_k = T_q\bigl(\frac{a' + a}{a' - a}\bigr)$. -/
theorem sum_chebyshevWeight {a a' : ℝ} (ha : 0 < a) (haa : a < a') (q : ℕ) :
    ∑ k : Fin (q + 1), chebyshevWeight a a' q k = (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)) := by
  have hT : 0 < (T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)) :=
    zero_lt_one.trans_le (one_le_eval_T_real (q : ℤ) (by
      rw [le_div_iff₀ (by linarith)]
      linarith))
  have h := sum_neg_one_pow_mul_chebyshevWeight_mul_eval (𝕜 := ℝ) ha haa
    (degree_chebyshevResidual_le a a' q)
  simp only [RCLike.ofReal_real_eq_id, id, eval_chebyshevResidual_zero q ha haa] at h
  have h' : ∑ k : Fin (q + 1), chebyshevWeight a a' q k *
      ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹ = 1 := by
    rw [← h]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_chebyshevResidual_chebyshevExtremum haa (Nat.lt_succ_iff.mp k.is_lt)]
    have : ((-1 : ℝ) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by rw [← mul_pow]; norm_num
    linear_combination (chebyshevWeight a a' q k *
      ((T ℝ (q : ℤ)).eval ((a' + a) / (a' - a)))⁻¹) * this.symm
  rw [← Finset.sum_mul, mul_inv_eq_one₀ hT.ne'] at h'
  exact h'

/-- The dual weights are positive. -/
theorem chebyshevWeight_pos {a a' : ℝ} (ha : 0 < a) (haa : a < a') (q : ℕ) (k : Fin (q + 1)) :
    0 < chebyshevWeight a a' q k := by
  refine abs_pos.mpr ?_
  simp only [Lagrange.basis, Lagrange.basisDivisor, eval_prod, eval_mul, eval_C, eval_sub, eval_X]
  refine Finset.prod_ne_zero_iff.mpr fun j hj => mul_ne_zero (inv_ne_zero (sub_ne_zero.mpr ?_)) ?_
  · exact fun h => Finset.ne_of_mem_erase hj ((strictMono_chebyshevExtremum haa q).injective h).symm
  · linarith [ha.trans_le (chebyshevExtremum_mem_Icc haa.le q j).1]

end NLAlib
