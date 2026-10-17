/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.GMRES
public import NLAlib.Matrix.Functions.Polynomial
public import NLAlib.Matrix.Inequalities.Order
public import NLAlib.Polynomial.Chebyshev.Residual
public import NLAlib.Matrix.Spectral.Congruence

/-!
# MINRES and preconditioned MINRES

MINRES has no definition of its own: it is `NLAlib.gmresIterate` for Hermitian $\mathbf{A}$, and
the theorems here are Hermitian theorems about it. For Hermitian $\mathbf{A}$ with spectrum in
$s$, the residual is at most $\eta\|\mathbf{r}_0\|$ for every real residual polynomial bounded by
$\eta$ on $s$; on an interval $[a, a']$ with $0 < a$ this gives the rate
$2\bigl(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\bigr)^q$, $\kappa = a'/a$; on two symmetric
intervals $[-a', -a] \cup [a, a']$ the rate $2\bigl(\frac{\kappa - 1}{\kappa + 1}\bigr)^{\lfloor q/2
\rfloor}$; and outliers are killed one step each.

Preconditioned MINRES, with a positive definite preconditioner $\mathbf{M}$ applied as
$\mathbf{M}$, minimises the residual in the $\mathbf{M}$-norm over
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$:
$\mathsf{pminresIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\mathsf{galerkinInverse}(\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{A},
\mathbf{K}_q(\mathbf{M}\mathbf{A},
\mathbf{M}\mathbf{r}_0))\,\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{r}_0$, no square root. At
$\mathbf{M} = \mathbf{I}$ it is GMRES (`pminresIterate_one`); for any factor
$\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ it is $\mathbf{C}$ times MINRES on the split
system, through which the bounds transfer with the spectrum of $\mathbf{M}\mathbf{A}$. The
$\mathbf{M}$-norm of a residual is squared, `RCLike.re (quadForm M _)`, as the $\mathbf{A}$-norm
of CG errors is; Euclidean residual norms are unsquared.

## Main definitions

* `NLAlib.pminresIterate`.

## Main results

* `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le`: the polynomial bound.
* `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow`: the $\kappa$ bound.
* `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_div_two`: two intervals.
* `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_mul_pow`: outliers.
* `Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul`: spectrum-optimal.
* `Matrix.PosDef.isMinOn_pminresIterate`: $\mathbf{M}$-norm optimality.
* `NLAlib.pminresIterate_eq_mulVec_gmresIterate`: PMINRES is MINRES on the split system.
* `Matrix.IsHermitian.re_quadForm_sub_mulVec_pminresIterate_le`,
  `Matrix.IsHermitian.re_quadForm_sub_mulVec_pminresIterate_le_four_mul_pow`: its bounds.
* `NLAlib.pminresIterate_eq_of_krylovGrade_le`: finite termination.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-! ### MINRES: Hermitian theorems about `gmresIterate` -/

/-- **The polynomial bound for MINRES**: for Hermitian $\mathbf{A}$ with spectrum in $s$ and a
real $p$ with $\deg p \le q$, $p(0) = 1$, $\lvert p \rvert \le \eta$ on $s$,
$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
\eta\,\|\mathbf{r}_0\|$. Indefinite $\mathbf{A}$ is allowed, $s$ a union of intervals.
[Greenbaum1997, §3.1]; [Saad2003, §6.11.4]; locators to verify.
Result: minres-polynomial-bound -/
theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {s : Set ℝ} (hs : spectrum ℝ A ⊆ s) (b x₀ : n → 𝕜) {q : ℕ}
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) {η : ℝ} (hη : ∀ x ∈ s, |p.eval x| ≤ η) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤ η * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have h0 : ∀ v : n → 𝕜, ‖WithLp.toLp 2 v‖ = 0 := fun v => by
      rw [Subsingleton.elim v 0, WithLp.toLp_zero, norm_zero]
    rw [h0, h0, mul_zero]
  have hη0 : 0 ≤ η :=
    (abs_nonneg _).trans (hη _ (hA.spectrum_subset_iff.mp hs 0 Fintype.card_pos))
  have hp' : (p.map (algebraMap ℝ 𝕜)).degree ≤ q := degree_map_le.trans hp
  have hp₀' : (p.map (algebraMap ℝ 𝕜)).eval 0 = 1 := by rw [eval_zero_map, hp₀, map_one]
  refine (norm_sub_mulVec_gmresIterate_le_norm_aeval_mulVec A b x₀ hp' hp₀').trans ?_
  rw [aeval_map_algebraMap]
  exact (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right
    (hA.specNorm_aeval_le p hη0 fun x hx => hη x (hs hx)) (norm_nonneg _))

/-- **The Chebyshev bound for MINRES** in $\kappa = a'/a$: for Hermitian $\mathbf{A}$ with
spectrum in $[a, a']$, $0 < a$,
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
2\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^q\|\mathbf{r}_0\| \,.$$
[Greenbaum1997, §3.1]; locator to verify.
Result: minres-chebyshev-bound -/
theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    (b x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      2 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ q *
        ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  obtain ⟨p, hp, hp₀, -, hpI⟩ := exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow
    (a' := a') ha ∅ q (C := 1) fun x _ => by rw [Finset.prod_empty, abs_one]
  rw [Finset.card_empty, zero_add] at hp
  refine (hA.norm_sub_mulVec_gmresIterate_le hs b x₀ hp hp₀ hpI).trans_eq ?_
  ring

/-- **MINRES on two symmetric intervals**: for Hermitian $\mathbf{A}$ with spectrum in
$[-a', -a] \cup [a, a']$, $0 < a$, and $\kappa = a'/a$,
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
2\Bigl(\frac{a'/a - 1}{a'/a + 1}\Bigr)^{\lfloor q/2 \rfloor}\|\mathbf{r}_0\| \,.$$
The residual polynomial is a Chebyshev residual on $[a^2, a'^2]$ composed with $x^2$.
[Greenbaum1997, §3.1]; [ElmanSilvesterWathen2014, Theorem 4.14]; locators to verify.
Result: minres-two-interval-bound -/
theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_div_two
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ A ⊆ Set.Icc (-a') (-a) ∪ Set.Icc a a') (b x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      2 * ((a' / a - 1) / (a' / a + 1)) ^ (q / 2) * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  obtain ⟨R, hR, hR₀, -, hRI⟩ := exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow
    (a' := a' ^ 2) (pow_pos ha 2) ∅ (q / 2) (C := 1)
    fun x _ => by rw [Finset.prod_empty, abs_one]
  rw [Finset.card_empty, zero_add] at hR
  have hRn : R.natDegree ≤ q / 2 := natDegree_le_iff_degree_le.mpr hR
  have hP : (R.comp (X ^ 2)).degree ≤ q := by
    refine degree_le_of_natDegree_le (natDegree_comp_le.trans ?_)
    rw [natDegree_X_pow]
    omega
  have hP₀ : (R.comp (X ^ 2)).eval 0 = 1 := by
    rw [eval_comp, eval_pow, eval_X, zero_pow two_ne_zero, hR₀]
  refine hA.norm_sub_mulVec_gmresIterate_le hs b x₀ hP hP₀ fun x hx => ?_
  have key : a ≤ a' ∧ x ^ 2 ∈ Set.Icc (a ^ 2) (a' ^ 2) := by
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by nlinarith, by nlinarith⟩
    · exact ⟨h1.trans h2, by nlinarith, by nlinarith⟩
  have h := hRI _ key.2
  have hsq : Real.sqrt (a' ^ 2 / a ^ 2) = a' / a := by
    rw [← div_pow, Real.sqrt_sq (div_nonneg (ha.le.trans key.1) ha.le)]
  rw [eval_comp, eval_pow, eval_X]
  rwa [hsq, mul_one] at h

/-- **MINRES kills outlying eigenvalues**: for Hermitian $\mathbf{A}$ with spectrum in
$[a, a'] \cup T$, $0 < a$, $0 \notin T$, and $\lvert\prod_{t \in T}(1 - x/t)\rvert \le C$ on
$[a, a']$, after $m + d$ steps, $m = \lvert T \rvert$,
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, m + d)\|
\le 2C\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^d\|\mathbf{r}_0\| \,.$$
The outliers may be negative (an indefinite matrix with a few negative eigenvalues); the
hypothesis $0 \notin T$ is needed, since every residual polynomial is $1$ at an eigenvalue $0$.
The hypothesis $a \le a'$ is needed too: for an empty interval the rate is negative and the
right side can be negative, while the CG and PCG forms are squares.
[Greenbaum1997, §3.1]; locator to verify.
Result: minres-outlier-bound -/
theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_mul_pow
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a')
    {T : Finset ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a' ∪ ↑T) (hT : (0 : ℝ) ∉ T) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc a a', |∏ t ∈ T, (1 - x / t)| ≤ C) (b x₀ : n → 𝕜) (d : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ (T.card + d))‖ ≤
      2 * C * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ d *
        ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  obtain ⟨p, hp, hp₀, hpT, hpI⟩ :=
    exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow ha T d hC
  have hC0 : 0 ≤ C := (abs_nonneg _).trans (hC a ⟨le_rfl, haa⟩)
  have hρ : 0 ≤ (Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1) := by
    have : 1 ≤ Real.sqrt (a' / a) := Real.one_le_sqrt.mpr ((one_le_div ha).mpr haa)
    exact div_nonneg (by linarith) (by linarith)
  refine hA.norm_sub_mulVec_gmresIterate_le hs b x₀ hp hp₀ fun x hx => ?_
  rcases hx with hI | hT'
  · exact hpI x hI
  · rw [hpT x hT' (fun h => hT (h ▸ hT')), abs_zero]
    exact mul_nonneg (mul_nonneg zero_le_two hC0) (pow_nonneg hρ d)

/-- **Large outliers cost MINRES one step each**: if every outlier is at least $a'$, the outlier
bound holds with $C = 1$ (for $a \le a'$, as in the general form).
Result: minres-outlier-bound -/
theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_two_mul_pow_of_forall_le
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (haa : a ≤ a')
    {T : Finset ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a' ∪ ↑T) (hT : ∀ t ∈ T, a' ≤ t) (b x₀ : n → 𝕜) (d : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ (T.card + d))‖ ≤
      2 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ d *
        ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  have h := hA.norm_sub_mulVec_gmresIterate_le_two_mul_mul_pow ha haa hs
    (fun h0 => (ha.trans_le (haa.trans (hT 0 h0))).false) (C := 1) (fun x hx => ?_) b x₀ d
  · rwa [mul_one] at h
  · rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun t ht => ?_
    have ht0 : 0 < t := ha.trans_le (hx.1.trans (hx.2.trans (hT t ht)))
    have h1 : x / t ≤ 1 := (div_le_one ht0).mpr (hx.2.trans (hT t ht))
    have h2 : 0 ≤ x / t := div_nonneg (ha.le.trans hx.1) ht0.le
    rw [abs_le]
    constructor <;> linarith

/-- **The spectrum bound for a residual polynomial**: for Hermitian $\mathbf{A}$ and a real $p$
with $\deg p \le q$, $p(0) = 1$,
$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
\max_{\lambda \in \sigma(\mathbf{A})}\lvert p(\lambda) \rvert\,\|\mathbf{r}_0\|$, the maximum
being the supremum over the finite spectrum.
Result: minres-polynomial-bound -/
theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_iSup_mul {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b x₀ : n → 𝕜) {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q)
    (hp₀ : p.eval 0 = 1) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      (⨆ x ∈ spectrum ℝ A, |p.eval x|) * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  refine hA.norm_sub_mulVec_gmresIterate_le subset_rfl b x₀ hp hp₀ fun x hx => ?_
  obtain ⟨M, hM⟩ := ((Matrix.finite_real_spectrum (A := A)).image fun x => |p.eval x|).bddAbove
  refine le_ciSup₂ (f := fun x (_ : x ∈ spectrum ℝ A) => |p.eval x|) ⟨M, fun z hz => ?_⟩ x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hM ⟨y, hy, rfl⟩

/-- **The spectrum-optimal bound for MINRES**: for Hermitian $\mathbf{A}$,
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{gmresIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\| \le
\Bigl(\min_{p}\max_{\lambda \in \sigma(\mathbf{A})}\lvert p(\lambda) \rvert\Bigr)\|\mathbf{r}_0\|
\,,$$
the minimum over real residual polynomials of degree at most $q$ (`residualMinimax`). For each
$\mathbf{A}$ some $\mathbf{b}$ attains it (Greenbaum):
`Matrix.IsHermitian.exists_norm_sub_mulVec_gmresIterate_eq_residualMinimax_mul` and
`Matrix.IsHermitian.isGreatest_norm_sub_mulVec_gmresIterate_div` in
`NLAlib.Krylov.LinearSystems.WorstCase`.
[Greenbaum1997, §3.1]; locator to verify.
Result: minres-spectrum-minimax-bound -/
theorem _root_.Matrix.IsHermitian.norm_sub_mulVec_gmresIterate_le_residualMinimax_mul
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (b x₀ : n → 𝕜) (q : ℕ) :
    ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
      residualMinimax (spectrum ℝ A) q * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ := by
  have h1 : (1 : ℝ[X]).degree ≤ q := degree_one_le.trans (by exact_mod_cast Nat.zero_le q)
  have key : ∀ p : {p : ℝ[X] // p.degree ≤ q ∧ p.eval 0 = 1},
      ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ ≤
        (⨆ x ∈ spectrum ℝ A, |p.1.eval x|) * ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ :=
    fun p => hA.norm_sub_mulVec_gmresIterate_le_iSup_mul b x₀ p.2.1 p.2.2
  rcases (norm_nonneg (WithLp.toLp 2 (b - A *ᵥ x₀))).eq_or_lt with hE0 | hEpos
  · have h := key ⟨1, h1, eval_one⟩
    rwa [← hE0, mul_zero] at h ⊢
  · have : Nonempty {p : ℝ[X] // p.degree ≤ q ∧ p.eval 0 = 1} := ⟨⟨1, h1, eval_one⟩⟩
    have hdiv : ‖WithLp.toLp 2 (b - A *ᵥ gmresIterate A b x₀ q)‖ /
        ‖WithLp.toLp 2 (b - A *ᵥ x₀)‖ ≤ residualMinimax (spectrum ℝ A) q := by
      unfold residualMinimax
      exact le_ciInf fun p => (div_le_iff₀ hEpos).mpr (key p)
    rwa [div_le_iff₀ hEpos] at hdiv

/-! ### Preconditioned MINRES -/

/-- The GMRES residual is orthogonal to $\mathbf{A}\mathcal{K}_q$. -/
private lemma conjTranspose_mul_krylovMatrix_mulVec_sub_mulVec_gmresIterate (A : Matrix n n 𝕜)
    (b x₀ : n → 𝕜) (q : ℕ) :
    (A * krylovMatrix A (b - A *ᵥ x₀) q)ᴴ *ᵥ (b - A *ᵥ gmresIterate A b x₀ q) = 0 := by
  rw [sub_mulVec_gmresIterate, Matrix.mulVec_mulVec, Matrix.mul_sub, Matrix.mul_one,
    conjTranspose_mul_rangeProjector, sub_self, Matrix.zero_mulVec]

/-- The **preconditioned MINRES iterate** after $q$ steps from $\mathbf{x}_0$, with
preconditioner $\mathbf{M}$ applied as $\mathbf{M}$ and $\mathbf{r}_0 = \mathbf{b} -
\mathbf{A}\mathbf{x}_0$:
$\mathsf{pminresIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) := \mathbf{x}_0 +
\mathsf{galerkinInverse}(\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{A},
\mathbf{K}_q(\mathbf{M}\mathbf{A},
\mathbf{M}\mathbf{r}_0))\,\mathbf{A}^{\mathsf{H}}\mathbf{M}\mathbf{r}_0$.
For positive definite $\mathbf{M}$ it minimises $\|\mathbf{b} - \mathbf{A}\mathbf{y}\|_{\mathbf{M}}$
over $\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$
(`Matrix.PosDef.isMinOn_pminresIterate`); the method is meant for Hermitian $\mathbf{A}$, the
definition is total. The preconditioned Lanczos recurrence with a small least-squares problem
computes it (`Matrix.IsHermitian.pminresIterate_eq_preconditionedLanczosMatrix`), and so does
the Paige–Saunders recurrence (`Matrix.IsHermitian.minresState_x_eq`). For singular
$\mathbf{A}$ the minimiser is not unique and the definition picks the correction of least
Euclidean norm, while the split form picks least $\mathbf{M}^{-1}$-norm; the two agree for
invertible $\mathbf{A}$, which is why `pminresIterate_eq_mulVec_gmresIterate` assumes it.
[ElmanSilvesterWathen2014, §4.2]; [Greenbaum1997, §8.2]; locators to verify. -/
noncomputable def pminresIterate (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + galerkinInverse (Aᴴ * M * A) (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) *ᵥ
    (Aᴴ *ᵥ (M *ᵥ (b - A *ᵥ x₀)))

/-- The correction lies in the preconditioned Krylov space. -/
theorem pminresIterate_sub_mem_krylovSpace (A M : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    pminresIterate A M b x₀ q - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q := by
  rw [pminresIterate, add_sub_cancel_left]
  exact galerkinInverse_mulVec_mem _ _ _

/-- **No preconditioner is GMRES**, for every $\mathbf{A}$: by
`minResidualInverse_eq_galerkinInverse`. -/
@[simp]
theorem pminresIterate_one (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    pminresIterate A 1 b x₀ q = gmresIterate A b x₀ q := by
  rw [pminresIterate, gmresIterate, minResidualInverse_eq_galerkinInverse, Matrix.mul_one,
    Matrix.one_mul, Matrix.one_mulVec, Matrix.mulVec_mulVec]

/-- **Preconditioned MINRES minimises the residual in the $\mathbf{M}$-norm** over
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{M}\mathbf{A}, \mathbf{M}\mathbf{r}_0)$, for positive definite
$\mathbf{M}$ and every $\mathbf{A}$. [ElmanSilvesterWathen2014, §4.2]; locator to verify.
Result: pminres-optimality -/
theorem _root_.Matrix.PosDef.isMinOn_pminresIterate {M : Matrix n n 𝕜} (hM : M.PosDef)
    (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    IsMinOn (fun y => RCLike.re (quadForm M (b - A *ᵥ y)))
      (AffineSubspace.mk' x₀ (krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) : Set (n → 𝕜))
      (pminresIterate A M b x₀ q) := by
  refine isMinOn_iff.mpr fun y hy => ?_
  have hy' : y - x₀ ∈ krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub] at hy
    exact hy
  have h := isMinOn_iff.mp (hM.isMinOn_galerkinInverse_conjTranspose_mul_mul_mulVec A
    (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) (b - A *ᵥ x₀)) (y - x₀) hy'
  have e : ∀ w, b - A *ᵥ x₀ - A *ᵥ w = b - A *ᵥ (x₀ + w) := fun w => by
    rw [Matrix.mulVec_add]
    abel
  rwa [e, e, add_sub_cancel] at h

/-- **Preconditioned MINRES is MINRES on the split system**: for invertible $\mathbf{A}$ and
$\mathbf{C}$ with $\mathbf{M} = \mathbf{C}\mathbf{C}^{\mathsf{H}}$ and
$\mathbf{C}\mathbf{y}_0 = \mathbf{x}_0$,
$\mathsf{pminresIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b}, \mathbf{x}_0, q) =
\mathbf{C}\,\mathsf{gmresIterate}(\mathbf{C}^{\mathsf{H}}\mathbf{A}\mathbf{C},
\mathbf{C}^{\mathsf{H}}\mathbf{b}, \mathbf{y}_0, q)$. Invertibility of $\mathbf{A}$ makes both
minimisers unique; for singular $\mathbf{A}$ the two least-norm choices differ.
Result: pminres-split-system -/
theorem pminresIterate_eq_mulVec_gmresIterate {A M C : Matrix n n 𝕜} (hA : IsUnit A)
    (hC : IsUnit C) (hM : M = C * Cᴴ) {b x₀ y₀ : n → 𝕜} (hy₀ : C *ᵥ y₀ = x₀) (q : ℕ) :
    pminresIterate A M b x₀ q = C *ᵥ gmresIterate (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ q := by
  have hr := Matrix.conjTranspose_mulVec_sub_mulVec_mulVec A C b y₀
  rw [hy₀] at hr
  have hK : krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q =
      C * krylovMatrix (Cᴴ * A * C) (Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀) q := by
    have h := krylovMatrix_mul_mulVec (Cᴴ * A) C (Cᴴ *ᵥ (b - A *ᵥ x₀)) q
    rwa [← Matrix.mul_assoc, Matrix.mulVec_mulVec, ← hM, hr] at h
  have hG : (Aᴴ * M * A).PosDef := by
    have hinj : Function.Injective (Cᴴ * A).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr ((isUnit_star.mpr hC : IsUnit Cᴴ).mul hA)
    have h := Matrix.PosDef.conjTranspose_mul_self (Cᴴ * A) hinj
    rwa [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc,
      ← Matrix.mul_assoc C, ← hM, ← Matrix.mul_assoc] at h
  have hmem : C *ᵥ gmresIterate (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ q - x₀ ∈
      LinearMap.range (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q).mulVecLin := by
    obtain ⟨w, hw⟩ := gmresIterate_sub_mem_krylovSpace (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ q
    refine ⟨w, ?_⟩
    rw [Matrix.mulVecLin_apply] at hw ⊢
    rw [hK, ← Matrix.mulVec_mulVec, hw, Matrix.mulVec_sub, hy₀]
  have horth : (krylovMatrix (M * A) (M *ᵥ (b - A *ᵥ x₀)) q)ᴴ *ᵥ
      (Aᴴ *ᵥ (M *ᵥ (b - A *ᵥ x₀)) -
        (Aᴴ * M * A) *ᵥ (C *ᵥ gmresIterate (Cᴴ * A * C) (Cᴴ *ᵥ b) y₀ q - x₀)) = 0 := by
    have e : ∀ g : n → 𝕜, Aᴴ *ᵥ (M *ᵥ (b - A *ᵥ x₀)) - (Aᴴ * M * A) *ᵥ (C *ᵥ g - x₀) =
        Aᴴ *ᵥ (C *ᵥ (Cᴴ *ᵥ (b - A *ᵥ (C *ᵥ g)))) := fun g => by
      have h1 : (Aᴴ * M * A) *ᵥ (C *ᵥ g - x₀) = Aᴴ *ᵥ (M *ᵥ (A *ᵥ (C *ᵥ g) - A *ᵥ x₀)) := by
        simp only [← Matrix.mulVec_mulVec, Matrix.mulVec_sub]
      rw [h1, ← Matrix.mulVec_sub, ← Matrix.mulVec_sub, hM, ← Matrix.mulVec_mulVec]
      congr 3
      abel
    have e2 : ∀ w : n → 𝕜, (C * krylovMatrix (Cᴴ * A * C) (Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀) q)ᴴ *ᵥ
        (Aᴴ *ᵥ (C *ᵥ w)) =
          ((Cᴴ * A * C) * krylovMatrix (Cᴴ * A * C) (Cᴴ *ᵥ b - (Cᴴ * A * C) *ᵥ y₀) q)ᴴ *ᵥ w :=
      fun w => by
        simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
          Matrix.mulVec_mulVec, Matrix.mul_assoc]
    rw [e, Matrix.conjTranspose_mulVec_sub_mulVec_mulVec, hK, e2]
    exact conjTranspose_mul_krylovMatrix_mulVec_sub_mulVec_gmresIterate _ _ _ _
  rw [pminresIterate,
    ← hG.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero hmem horth, add_sub_cancel]

/-- **The polynomial bound for preconditioned MINRES**: for Hermitian $\mathbf{A}$, positive
definite $\mathbf{M}$, the spectrum of $\mathbf{M}\mathbf{A}$ in $s$ and a real $p$ with
$\deg p \le q$, $p(0) = 1$, $\lvert p \rvert \le \eta$ on $s$,
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{pminresIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b},
\mathbf{x}_0, q)\|_{\mathbf{M}}^2 \le \eta^2\|\mathbf{r}_0\|_{\mathbf{M}}^2 \,.$$
No invertibility: the comparison is with the candidate $\mathbf{x}_0 + s(\mathbf{M}\mathbf{A})
\mathbf{M}\mathbf{r}_0$, $p = 1 - Xs$, through `Matrix.PosDef.isMinOn_pminresIterate`; its
residual is $p(\mathbf{A}\mathbf{M})\mathbf{r}_0$.
Result: pminres-polynomial-bound -/
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_mulVec_pminresIterate_le {A M : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hM : M.PosDef) {s : Set ℝ} (hs : spectrum ℝ (M * A) ⊆ s)
    (b x₀ : n → 𝕜) {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) {η : ℝ}
    (hη : ∀ x ∈ s, |p.eval x| ≤ η) :
    RCLike.re (quadForm M (b - A *ᵥ pminresIterate A M b x₀ q)) ≤
      η ^ 2 * RCLike.re (quadForm M (b - A *ᵥ x₀)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [quadForm_eq_sum]
  obtain ⟨S, -, hSu, hMS, -⟩ :=
    hM.exists_eq_mul_conjTranspose_and_eq_mul_diagonal_mul_conjTranspose hM.isHermitian
  have hS : IsUnit S := (Matrix.isUnit_iff_isUnit_det S).mpr hSu
  have hq : ∀ v, RCLike.re (quadForm M v) = ‖WithLp.toLp 2 (Sᴴ *ᵥ v)‖ ^ 2 := fun v => by
    have h := quadForm_conjTranspose_mul_self Sᴴ v
    rw [Matrix.conjTranspose_conjTranspose] at h
    rw [hMS, h, RCLike.ofReal_re]
  have hH : (Sᴴ * A * S).IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul S hA
  have hspec : spectrum ℝ (Sᴴ * A * S) ⊆ s := by
    rw [← spectrum_mul_conjTranspose_mul hS, ← hMS]
    exact hs
  have hη0 : 0 ≤ η :=
    (abs_nonneg _).trans (hη _ (hspec (hH.spectrum_subset_iff.mp subset_rfl 0 Fintype.card_pos)))
  obtain ⟨t, ht, hpt⟩ := exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one hp hp₀
  have hint := aeval_mul_eq_mul_aeval_of_mul_eq_mul
    (show A * M * A = A * (M * A) by rw [Matrix.mul_assoc]) t
  have hp' : p = 1 - t * X := by rw [mul_comm t X, ← hpt, sub_sub_cancel]
  have heq : b - A *ᵥ (x₀ + aeval (M * A) t *ᵥ (M *ᵥ (b - A *ᵥ x₀))) =
      aeval (A * M) p *ᵥ (b - A *ᵥ x₀) := by
    rw [hp', map_sub, map_one, map_mul, aeval_X, ← Matrix.mul_assoc, hint, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    simp only [Matrix.mulVec_add, ← Matrix.mulVec_mulVec]
    abel
  have hmem : x₀ + aeval (M * A) t *ᵥ (M *ᵥ (b - A *ᵥ x₀)) ∈
      (AffineSubspace.mk' x₀ (krylovSpace (M * A) (M *ᵥ (b - A *ᵥ x₀)) q) : Set (n → 𝕜)) := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left]
    exact aeval_mulVec_mem_krylovSpace _ _ ht
  have hmin := isMinOn_iff.mp (hM.isMinOn_pminresIterate A b x₀ q) _ hmem
  rw [heq] at hmin
  refine hmin.trans ?_
  have hint2 := aeval_mul_eq_mul_aeval_of_mul_eq_mul
    (show Sᴴ * A * S * Sᴴ = Sᴴ * (A * M) by rw [hMS]; simp only [Matrix.mul_assoc]) p
  have hSv : Sᴴ *ᵥ (aeval (A * M) p *ᵥ (b - A *ᵥ x₀)) =
      aeval (Sᴴ * A * S) p *ᵥ (Sᴴ *ᵥ (b - A *ᵥ x₀)) := by
    rw [Matrix.mulVec_mulVec, ← hint2, ← Matrix.mulVec_mulVec]
  rw [hq, hq, hSv]
  have hn := (norm_toLp_mulVec_le (aeval (Sᴴ * A * S) p) (Sᴴ *ᵥ (b - A *ᵥ x₀))).trans
    (mul_le_mul_of_nonneg_right (hH.specNorm_aeval_le p hη0 fun x hx => hη x (hspec hx))
      (norm_nonneg _))
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hn 2

/-- **The Chebyshev bound for preconditioned MINRES** in $\kappa = a'/a$: for Hermitian
$\mathbf{A}$, positive definite $\mathbf{M}$ and the spectrum of $\mathbf{M}\mathbf{A}$ in
$[a, a']$, $0 < a$,
$$\|\mathbf{b} - \mathbf{A}\,\mathsf{pminresIterate}(\mathbf{A}, \mathbf{M}, \mathbf{b},
\mathbf{x}_0, q)\|_{\mathbf{M}}^2 \le 4\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2q}
\|\mathbf{r}_0\|_{\mathbf{M}}^2 \,.$$ [ElmanSilvesterWathen2014, §4.2]; locator to verify.
Result: pminres-chebyshev-bound -/
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_mulVec_pminresIterate_le_four_mul_pow
    {A M : Matrix n n 𝕜} (hA : A.IsHermitian) (hM : M.PosDef) {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ (M * A) ⊆ Set.Icc a a') (b x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm M (b - A *ᵥ pminresIterate A M b x₀ q)) ≤
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) *
        RCLike.re (quadForm M (b - A *ᵥ x₀)) := by
  obtain ⟨p, hp, hp₀, -, hpI⟩ := exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow
    (a' := a') ha ∅ q (C := 1) fun x _ => by rw [Finset.prod_empty, abs_one]
  rw [Finset.card_empty, zero_add] at hp
  refine (hA.re_quadForm_sub_mulVec_pminresIterate_le hM hs b x₀ hp hp₀ hpI).trans_eq ?_
  ring

/-- **Finite termination for preconditioned MINRES**: for invertible $\mathbf{A}$ and positive
definite $\mathbf{M}$, the iterate is the solution once $q$ is at least the grade of
$\mathbf{M}\mathbf{r}_0$ for $\mathbf{M}\mathbf{A}$.
Result: pminres-finite-termination -/
theorem pminresIterate_eq_of_krylovGrade_le {A M : Matrix n n 𝕜} (hA : IsUnit A) (hM : M.PosDef)
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ}
    (h : krylovGrade (M * A) (M *ᵥ (b - A *ᵥ x₀)) ≤ q) : pminresIterate A M b x₀ q = xs := by
  have hxs' : A *ᵥ (xs - x₀) = b - A *ᵥ x₀ := by rw [Matrix.mulVec_sub, hxs]
  have hmem := mem_krylovSpace_of_krylovGrade_le (hM.isUnit.mul hA)
    (show (M * A) *ᵥ (xs - x₀) = M *ᵥ (b - A *ᵥ x₀) by rw [← Matrix.mulVec_mulVec, hxs']) h
  have hG : (Aᴴ * M * A).PosDef :=
    hM.conjTranspose_mul_mul_same (Matrix.mulVec_injective_iff_isUnit.mpr hA)
  rw [pminresIterate, hG.galerkinInverse_mulVec_eq_of_mem (by
    simp only [← Matrix.mulVec_mulVec, hxs']) hmem, add_sub_cancel]

end NLAlib
