/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.ForMathlib.Algebra.Polynomial.Div
public import NLAlib.Krylov.Basic.Grade
public import NLAlib.Krylov.LinearSystems.Galerkin
public import NLAlib.Matrix.Functions.Polynomial
public import NLAlib.Matrix.Pseudoinverse.ConditionNumber
public import NLAlib.Polynomial.Chebyshev.Residual
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

/-!
# The conjugate gradient iterate

The conjugate gradient iterate is defined mathematically, with no algorithm: from a start
$\mathbf{x}_0$ it is $\mathbf{x}_0$ plus the Galerkin approximation to the error from the Krylov
space of the initial residual,
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{A}, \mathbf{r}_0))\,\mathbf{r}_0$.
For positive definite $\mathbf{A}$ it equals
$\mathbf{x}_0 +
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{r}_0$
for every orthonormal basis $\mathbf{Q}$ of the Krylov space, minimises the $\mathbf{A}$-norm error
over $\mathbf{x}_0 + \mathcal{K}_q$, beats every residual polynomial, converges at the Chebyshev
rate and terminates at the grade.

Errors are written target minus output in the squared $\mathbf{A}$-norm
`RCLike.re (quadForm A _)`. Spectral hypotheses are `spectrum ℝ A ⊆ s`; a Loewner sandwich reaches
them through `spectrum_subset_Icc_of_le`. The rate is written with $\kappa = a'/a$ for a spectrum
in $[a, a']$.

## Main definitions

* `NLAlib.cgIterate`: the CG iterate from the start $\mathbf{x}_0$.

## Main results

* `Matrix.PosDef.cgIterate_eq`: the frame form.
* `Matrix.PosDef.isMinOn_cgIterate`: $\mathbf{A}$-norm optimality over $\mathbf{x}_0 +
  \mathcal{K}_q$.
* `Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`: the Galerkin
  characterisation.
* `NLAlib.exists_sub_cgIterate_eq_aeval`: the error polynomial.
* `Matrix.PosDef.re_quadForm_sub_cgIterate_le`: the polynomial bound.
* `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow`: the Chebyshev rate in $\kappa$.
* `Matrix.PosDef.re_quadForm_sub_cgIterate_le_four_mul_sq_mul_pow`: the outlier bound.
* `Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul`: the spectrum-optimal bound.
* `NLAlib.re_quadForm_sub_cgIterate_conjTranspose_mul_le_four_mul_pow`: CGLS.
* `Matrix.PosDef.cgIterate_eq_of_krylovGrade_le`: finite termination.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-- The **conjugate gradient iterate** after $q$ steps from the start $\mathbf{x}_0$, with
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$:
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) := \mathbf{x}_0 +
\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{A}, \mathbf{r}_0))\,\mathbf{r}_0$,
which is $\mathbf{x}_0 +
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{r}_0$
for every orthonormal basis $\mathbf{Q}$ of $\mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$ when
$\mathbf{A}$ is positive definite (`Matrix.PosDef.cgIterate_eq`). The zero start is
$\mathbf{x}_0 = \mathbf{0}$. Basis-free, total, not an algorithm; the Hestenes–Stiefel recurrence
computes it (`Matrix.PosDef.cgState_x_eq`). Junk value: when the compression of $\mathbf{A}$ to
the Krylov space is singular, the pseudoinverse formula of `galerkinInverse`.
[HestenesStiefel1952]; [Saad2003, §6.7]. -/
noncomputable def cgIterate (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  x₀ + galerkinInverse A (krylovMatrix A (b - A *ᵥ x₀) q) *ᵥ (b - A *ᵥ x₀)

/-- The correction lies in the Krylov space of the initial residual, for every $\mathbf{A}$. -/
theorem cgIterate_sub_mem_krylovSpace (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (q : ℕ) :
    cgIterate A b x₀ q - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) q := by
  rw [cgIterate, add_sub_cancel_left]
  exact galerkinInverse_mulVec_mem A _ _

/-- The zeroth iterate is the start. -/
@[simp]
theorem cgIterate_zero (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) : cgIterate A b x₀ 0 = x₀ := by
  have h := cgIterate_sub_mem_krylovSpace A b x₀ 0
  rwa [krylovSpace_zero, Submodule.mem_bot, sub_eq_zero] at h

/-- **CG in any orthonormal basis of the Krylov space**, for every $\mathbf{A}$:
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) = \mathbf{x}_0 +
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{r}_0$. -/
theorem HasOrthonormalCols.cgIterate_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} {b x₀ : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A (b - A *ᵥ x₀) q) :
    cgIterate A b x₀ q = x₀ + Q *ᵥ (pinv (Qᴴ * A * Q) *ᵥ (Qᴴ *ᵥ (b - A *ᵥ x₀))) := by
  rw [cgIterate, hQ.galerkinInverse_eq hK A, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- **CG is $\mathbf{x}_0 +
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{r}_0$
for any orthonormal basis $\mathbf{Q}$ of the Krylov space**, for positive definite $\mathbf{A}$.
[Saad2003, §6.7].
Result: cg-galerkin-formula -/
theorem _root_.Matrix.PosDef.cgIterate_eq {A : Matrix n n 𝕜} (hA : A.PosDef)
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) {b x₀ : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A (b - A *ᵥ x₀) q) :
    cgIterate A b x₀ q = x₀ + Q *ᵥ ((Qᴴ * A * Q)⁻¹ *ᵥ (Qᴴ *ᵥ (b - A *ᵥ x₀))) := by
  rw [cgIterate, hA.galerkinInverse_eq hQ hK, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

omit [Fintype r] [DecidableEq r] in
/-- **The Galerkin condition**: for positive definite $\mathbf{A}$ the residual of the CG iterate
is orthogonal to $\mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$. -/
theorem _root_.Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero
    {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜) (q : ℕ) :
    (krylovMatrix A (b - A *ᵥ x₀) q)ᴴ *ᵥ (b - A *ᵥ cgIterate A b x₀ q) = 0 := by
  have e : b - A *ᵥ cgIterate A b x₀ q =
      (1 - A * galerkinInverse A (krylovMatrix A (b - A *ᵥ x₀) q)) *ᵥ (b - A *ᵥ x₀) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, cgIterate,
      Matrix.mulVec_add]
    abel
  rw [e, Matrix.mulVec_mulVec, hA.conjTranspose_mul_one_sub_mul_galerkinInverse,
    Matrix.zero_mulVec]

omit [Fintype r] [DecidableEq r] in
/-- **The Galerkin condition characterises CG**: for positive definite $\mathbf{A}$, a vector of
$\mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$ whose residual is orthogonal to the Krylov
space is $\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)$. -/
theorem _root_.Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero
    {A : Matrix n n 𝕜} (hA : A.PosDef) {b x₀ y : n → 𝕜} {q : ℕ}
    (hy : y - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) q)
    (h : (krylovMatrix A (b - A *ᵥ x₀) q)ᴴ *ᵥ (b - A *ᵥ y) = 0) : y = cgIterate A b x₀ q := by
  have h' : (krylovMatrix A (b - A *ᵥ x₀) q)ᴴ *ᵥ ((b - A *ᵥ x₀) - A *ᵥ (y - x₀)) = 0 := by
    rwa [Matrix.mulVec_sub A y x₀, sub_sub_sub_cancel_right]
  rw [cgIterate, ← hA.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero hy h',
    add_sub_cancel]

omit [Fintype r] [DecidableEq r] in
/-- **CG minimises the $\mathbf{A}$-norm error** over the affine Krylov space: for positive
definite $\mathbf{A}$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)$ minimises
$\|\mathbf{x}_\star - \mathbf{y}\|_{\mathbf{A}}^2$ over
$\mathbf{y} \in \mathbf{x}_0 + \mathcal{K}_q(\mathbf{A}, \mathbf{r}_0)$ (Mathlib's
`AffineSubspace.mk'`). [Saad2003, §5.2]; [TrefethenBau1997, Theorem 38.1].
Result: cg-optimality -/
theorem _root_.Matrix.PosDef.isMinOn_cgIterate {A : Matrix n n 𝕜} (hA : A.PosDef)
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    IsMinOn (fun y => RCLike.re (quadForm A (xs - y)))
      (AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) q) : Set (n → 𝕜))
      (cgIterate A b x₀ q) := by
  refine isMinOn_iff.mpr fun y hy => ?_
  have hy' : y - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) q := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub] at hy
    exact hy
  have hxs' : A *ᵥ (xs - x₀) = b - A *ᵥ x₀ := by rw [Matrix.mulVec_sub, hxs]
  have h := isMinOn_iff.mp (hA.isMinOn_galerkinInverse_mulVec
    (krylovMatrix A (b - A *ᵥ x₀) q) hxs') (y - x₀) hy'
  rwa [sub_sub_sub_cancel_right, ← sub_add_eq_sub_sub_swap, add_comm] at h

omit [Fintype r] [DecidableEq r] in
/-- **The CG error polynomial**: for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ there is
$p \in \Bbbk[X]$ with $\deg p \le q$ and $p(0) = 1$ such that
$\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q) =
p(\mathbf{A})(\mathbf{x}_\star - \mathbf{x}_0)$. No assumption on $\mathbf{A}$.
[Saad2003, §6.11.3]. -/
theorem exists_sub_cgIterate_eq_aeval {A : Matrix n n 𝕜} {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (x₀ : n → 𝕜) (q : ℕ) : ∃ p : 𝕜[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      xs - cgIterate A b x₀ q = aeval A p *ᵥ (xs - x₀) := by
  obtain ⟨s, hs, hsb⟩ := mem_krylovSpace_iff.1 (cgIterate_sub_mem_krylovSpace A b x₀ q)
  refine ⟨1 - s * X, ?_, by simp, ?_⟩
  · rcases eq_or_ne s 0 with rfl | h0
    · simp only [zero_mul, sub_zero]
      exact degree_one_le.trans (by exact_mod_cast Nat.zero_le q)
    · have hnat : s.natDegree < q := (natDegree_lt_iff_degree_lt h0).2 hs
      refine degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
      · rw [natDegree_one]
        exact Nat.zero_le q
      · exact natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  · have hr : b - A *ᵥ x₀ = A *ᵥ (xs - x₀) := by rw [Matrix.mulVec_sub, hxs]
    rw [show xs - cgIterate A b x₀ q = (xs - x₀) - (cgIterate A b x₀ q - x₀) by abel, ← hsb, hr,
      map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]

omit [Fintype r] [DecidableEq r] in
/-- **CG beats every residual polynomial**: for positive definite $\mathbf{A}$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and every real $p$ with $\deg p \le q$, $p(0) = 1$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le \|p(\mathbf{A})(\mathbf{x}_\star - \mathbf{x}_0)\|_{\mathbf{A}}^2 \,.$$
[Saad2003, §6.11.3]. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_re_quadForm_aeval {A : Matrix n n 𝕜}
    (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      RCLike.re (quadForm A (aeval A p *ᵥ (xs - x₀))) := by
  obtain ⟨s, hs, hps⟩ := exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one hp hp₀
  have hy : aeval A s *ᵥ (b - A *ᵥ x₀) ∈ krylovSpace A (b - A *ᵥ x₀) q :=
    aeval_mulVec_mem_krylovSpace A _ hs
  have hp' : p = 1 - s * X := by rw [mul_comm, ← hps, sub_sub_cancel]
  have hr : b - A *ᵥ x₀ = A *ᵥ (xs - x₀) := by rw [Matrix.mulVec_sub, hxs]
  have heq : xs - (x₀ + aeval A s *ᵥ (b - A *ᵥ x₀)) = aeval A p *ᵥ (xs - x₀) := by
    rw [hp', hr, ← sub_sub, map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_mulVec]
  have hmem : x₀ + aeval A s *ᵥ (b - A *ᵥ x₀) ∈
      (AffineSubspace.mk' x₀ (krylovSpace A (b - A *ᵥ x₀) q) : Set (n → 𝕜)) := by
    rw [SetLike.mem_coe, AffineSubspace.mem_mk', vsub_eq_sub, add_sub_cancel_left]
    exact hy
  have h := isMinOn_iff.mp (hA.isMinOn_cgIterate hxs x₀ q) _ hmem
  rwa [heq] at h

omit [Fintype r] [DecidableEq r] in
/-- **The polynomial bound for CG**: if $\mathbf{A}$ is positive definite with spectrum in a set
$s$, $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, and a real $p$ with $\deg p \le q$, $p(0) = 1$
satisfies $\lvert p \rvert \le \eta$ on $s$, then
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le \eta^2 \|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$ [Saad2003, §6.11.3]. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le {A : Matrix n n 𝕜} (hA : A.PosDef)
    {s : Set ℝ} (hs : spectrum ℝ A ⊆ s) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    {q : ℕ} {p : ℝ[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) {η : ℝ}
    (hη : ∀ x ∈ s, |p.eval x| ≤ η) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      η ^ 2 * RCLike.re (quadForm A (xs - x₀)) := by
  refine (hA.re_quadForm_sub_cgIterate_le_re_quadForm_aeval hxs x₀ hp hp₀).trans ?_
  have h := hA.isHermitian.re_quadForm_aeval_aeval_mulVec_le subset_rfl X p
    (fun x hx => by rw [eval_X]; exact (hA.spectrum_subset_Ioi hx).le) (fun x hx => hη x (hs hx))
    (xs - x₀)
  rwa [aeval_X] at h

omit [Fintype r] [DecidableEq r] in
/-- **The Chebyshev bound for CG** in the condition number $\kappa = a'/a$ of the interval: if
$\mathbf{A}$ is Hermitian with spectrum in $[a, a']$, $0 < a$, and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, then
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le 4\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2q}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,,$$
the square of the classical
$\|\mathbf{e}_q\|_{\mathbf{A}} \le 2\bigl(\frac{\sqrt\kappa - 1}{\sqrt\kappa + 1}\bigr)^q
\|\mathbf{e}_0\|_{\mathbf{A}}$. A Loewner sandwich gives the hypotheses by
`isHermitian_of_le_smul_one` and `spectrum_subset_Icc_of_le`.
[Saad2003, Theorem 6.29]; [TrefethenBau1997, Theorem 38.5]; stated there for the extreme
eigenvalues and the unsquared $\mathbf{A}$-norm, here for any interval containing the spectrum.
Result: cg-chebyshev-bound -/
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * q) *
        RCLike.re (quadForm A (xs - x₀)) := by
  have hpd : A.PosDef := hA.posDef_iff_eigenvalue_pos.mpr fun k hk =>
    ha.trans_le (hA.spectrum_subset_iff.mp hs k hk).1
  obtain ⟨p, hp, hp₀, -, hpI⟩ := exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow
    (a' := a') ha ∅ q (C := 1) fun x _ => by rw [Finset.prod_empty, abs_one]
  rw [Finset.card_empty, zero_add] at hp
  refine (hpd.re_quadForm_sub_cgIterate_le hs hxs x₀ hp hp₀ hpI).trans_eq ?_
  ring

omit [Fintype r] [DecidableEq r] in
/-- **The Chebyshev bound in the condition number of $\mathbf{A}$**: for positive definite
$\mathbf{A}$ with $\kappa = \kappa(\mathbf{A})$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le 4\Bigl(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\Bigr)^{2q}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$
The interval form at $[\lambda_{\min}, \lambda_{\max}]$. [Saad2003, (6.128)]. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_four_mul_pow_pseudoConditionNumber
    {A : Matrix n n 𝕜} (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      4 * ((Real.sqrt (pseudoConditionNumber A) - 1) /
        (Real.sqrt (pseudoConditionNumber A) + 1)) ^ (2 * q) *
        RCLike.re (quadForm A (xs - x₀)) := by
  rcases isEmpty_or_nonempty n with hn | hn
  · simp [quadForm_eq_sum]
  obtain ⟨k, hk⟩ : ∃ k, k + 1 = Fintype.card n := ⟨Fintype.card n - 1, by
    have := Fintype.card_pos (α := n)
    omega⟩
  have hpos : 0 < eigenvalue A k :=
    hA.isHermitian.posDef_iff_eigenvalue_pos.mp hA k (by omega)
  have hs : spectrum ℝ A ⊆ Set.Icc (eigenvalue A k) (eigenvalue A 0) := by
    rw [hA.isHermitian.spectrum_subset_iff]
    intro i hi
    exact ⟨hA.isHermitian.eigenvalue_le_eigenvalue (by omega) (by omega),
      hA.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le i) hi⟩
  have h := hA.isHermitian.re_quadForm_sub_cgIterate_le_four_mul_pow hpos hs hxs x₀ q
  rwa [← hA.pseudoConditionNumber_eq hk] at h

omit [Fintype r] [DecidableEq r] in
/-- **CG kills outlying eigenvalues**: if $\mathbf{A}$ is positive definite with spectrum in
$[a, a'] \cup T$ for a finite set $T$ of $m$ outliers, $0 < a$, and
$\lvert \prod_{t \in T}(1 - x/t) \rvert \le C$ on $[a, a']$, then after $m + d$ steps
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, m +
d)\|_{\mathbf{A}}^2
\le 4C^2\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2d}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,:$$
$m$ steps are spent on the outliers, and the rate on $[a, a']$ applies to the rest.
No hypothesis on $T$: an element $0$ of $T$ contributes the factor $1$ (Lean's $0^{-1} = 0$) and
is not in the spectrum. [Greenbaum1997, §3.1]; [TrefethenBau1997, Lecture 38]; locators to
verify. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_four_mul_sq_mul_pow
    {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ} (ha : 0 < a) {T : Finset ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a' ∪ ↑T) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc a a', |∏ t ∈ T, (1 - x / t)| ≤ C) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (x₀ : n → 𝕜) (d : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ (T.card + d))) ≤
      4 * C ^ 2 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * d) *
        RCLike.re (quadForm A (xs - x₀)) := by
  obtain ⟨p, hp, hp₀, hpT, hpI⟩ :=
    exists_degree_le_eval_eq_zero_abs_eval_le_two_mul_mul_pow ha T d hC
  refine (hA.re_quadForm_sub_cgIterate_le subset_rfl hxs x₀ hp hp₀
    (η := |2 * C * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ d|)
    fun x hx => ?_).trans_eq ?_
  · rcases hs hx with hI | hT
    · exact (hpI x hI).trans (le_abs_self _)
    · rw [hpT x hT (hA.spectrum_subset_Ioi hx).ne', abs_zero]
      exact abs_nonneg _
  · rw [sq_abs]
    ring

omit [Fintype r] [DecidableEq r] in
/-- **Large outliers cost one step each**: if every outlier is at least $a'$, the outlier bound
holds with $C = 1$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, m +
d)\|_{\mathbf{A}}^2
\le 4\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2d}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$
[Greenbaum1997, §3.1]; locator to verify. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_four_mul_pow_of_forall_le
    {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ} (ha : 0 < a) {T : Finset ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a' ∪ ↑T) (hT : ∀ t ∈ T, a' ≤ t) {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (d : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ (T.card + d))) ≤
      4 * ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * d) *
        RCLike.re (quadForm A (xs - x₀)) := by
  have h := hA.re_quadForm_sub_cgIterate_le_four_mul_sq_mul_pow ha hs (C := 1) (fun x hx => ?_)
    hxs x₀ d
  · rwa [one_pow, mul_one] at h
  · rw [Finset.abs_prod]
    refine Finset.prod_le_one (fun _ _ => abs_nonneg _) fun t ht => ?_
    have ht0 : 0 < t := ha.trans_le (hx.1.trans (hx.2.trans (hT t ht)))
    have h1 : x / t ≤ 1 := (div_le_one ht0).mpr (hx.2.trans (hT t ht))
    have h2 : 0 ≤ x / t := div_nonneg (ha.le.trans hx.1) ht0.le
    rw [abs_le]
    constructor <;> linarith

omit [Fintype r] [DecidableEq r] in
/-- **Small outliers**: if every outlier $t$ lies in $(0, a)$, the outlier bound holds with
$C = \prod_{t \in T}(a'/t - 1)$, which grows as an outlier approaches $0$:
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, m +
d)\|_{\mathbf{A}}^2
\le 4\Bigl(\prod_{t \in T}\Bigl(\frac{a'}{t} - 1\Bigr)\Bigr)^2
\Bigl(\frac{\sqrt{a'/a} - 1}{\sqrt{a'/a} + 1}\Bigr)^{2d}
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$
[Greenbaum1997, §3.1]; locator to verify. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_four_mul_sq_mul_pow_of_forall_lt
    {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ} (ha : 0 < a) {T : Finset ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a' ∪ ↑T) (hT : ∀ t ∈ T, 0 < t ∧ t < a) {b xs : n → 𝕜}
    (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) (d : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ (T.card + d))) ≤
      4 * (∏ t ∈ T, (a' / t - 1)) ^ 2 *
        ((Real.sqrt (a' / a) - 1) / (Real.sqrt (a' / a) + 1)) ^ (2 * d) *
        RCLike.re (quadForm A (xs - x₀)) := by
  refine hA.re_quadForm_sub_cgIterate_le_four_mul_sq_mul_pow ha hs (fun x hx => ?_) hxs x₀ d
  rw [Finset.abs_prod]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun t ht => ?_
  obtain ⟨ht0, hta⟩ := hT t ht
  have h1 : 1 ≤ x / t := (one_le_div ht0).mpr (hta.le.trans hx.1)
  have h2 : x / t ≤ a' / t := div_le_div_of_nonneg_right hx.2 ht0.le
  rw [abs_of_nonpos (by linarith)]
  linarith

omit [Fintype r] [DecidableEq r] in
/-- **The spectrum bound for a residual polynomial**: for positive definite $\mathbf{A}$ and a
real $p$ with $\deg p \le q$, $p(0) = 1$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le \Bigl(\max_{\lambda \in \sigma(\mathbf{A})}\lvert p(\lambda) \rvert\Bigr)^2
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,.$$
The maximum is the supremum over the finite spectrum. [Greenbaum1997, §3.1]; locator to verify. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_iSup_sq_mul {A : Matrix n n 𝕜}
    (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      (⨆ x ∈ spectrum ℝ A, |p.eval x|) ^ 2 * RCLike.re (quadForm A (xs - x₀)) := by
  refine hA.re_quadForm_sub_cgIterate_le subset_rfl hxs x₀ hp hp₀ fun x hx => ?_
  obtain ⟨M, hM⟩ := ((Matrix.finite_real_spectrum (A := A)).image fun x => |p.eval x|).bddAbove
  refine le_ciSup₂ (f := fun x (_ : x ∈ spectrum ℝ A) => |p.eval x|) ⟨M, fun z hz => ?_⟩ x hx
  simp only [Set.mem_iUnion, Set.mem_range] at hz
  obtain ⟨y, hy, rfl⟩ := hz
  exact hM ⟨y, hy, rfl⟩

omit [Fintype r] [DecidableEq r] in
/-- **The spectrum-optimal bound for CG**: for positive definite $\mathbf{A}$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, \mathbf{x}_0, q)\|_{\mathbf{A}}^2
\le \Bigl(\min_{p}\max_{\lambda \in \sigma(\mathbf{A})}\lvert p(\lambda) \rvert\Bigr)^2
\|\mathbf{x}_\star - \mathbf{x}_0\|_{\mathbf{A}}^2 \,,$$
the minimum over real $p$ with $\deg p \le q$, $p(0) = 1$ (`residualMinimax`). Every other bound
of this file follows from it by bounding the minimax value. For each $\mathbf{A}$ some
$\mathbf{b}$ attains it (Greenbaum):
`Matrix.PosDef.exists_re_quadForm_sub_cgIterate_eq_residualMinimax_sq_mul` and
`Matrix.PosDef.isGreatest_re_quadForm_sub_cgIterate_div` in
`NLAlib.Krylov.LinearSystems.WorstCase`. [Greenbaum1997, §3.1]; locator to verify. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul
    {A : Matrix n n 𝕜} (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜)
    (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
      residualMinimax (spectrum ℝ A) q ^ 2 * RCLike.re (quadForm A (xs - x₀)) := by
  have hE : 0 ≤ RCLike.re (quadForm A (xs - x₀)) := hA.posSemidef.re_quadForm_nonneg _
  have hL : 0 ≤ RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) :=
    hA.posSemidef.re_quadForm_nonneg _
  have h1 : (1 : ℝ[X]).degree ≤ q := degree_one_le.trans (by exact_mod_cast Nat.zero_le q)
  have key : ∀ p : {p : ℝ[X] // p.degree ≤ q ∧ p.eval 0 = 1},
      RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) ≤
        (⨆ x ∈ spectrum ℝ A, |p.1.eval x|) ^ 2 * RCLike.re (quadForm A (xs - x₀)) :=
    fun p => hA.re_quadForm_sub_cgIterate_le_iSup_sq_mul hxs x₀ p.2.1 p.2.2
  rcases hE.eq_or_lt with hE0 | hEpos
  · have h := key ⟨1, h1, eval_one⟩
    rwa [← hE0, mul_zero] at h ⊢
  · have : Nonempty {p : ℝ[X] // p.degree ≤ q ∧ p.eval 0 = 1} := ⟨⟨1, h1, eval_one⟩⟩
    have hsq : Real.sqrt (RCLike.re (quadForm A (xs - cgIterate A b x₀ q)) /
        RCLike.re (quadForm A (xs - x₀))) ≤ residualMinimax (spectrum ℝ A) q := by
      unfold residualMinimax
      refine le_ciInf fun p => Real.sqrt_le_iff.mpr ⟨?_, ?_⟩
      · exact Real.iSup_nonneg fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
      · rw [div_le_iff₀ hEpos]
        exact key p
    have h := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2) hE
    rwa [Real.sq_sqrt (div_nonneg hL hE), div_mul_cancel₀ _ hEpos.ne'] at h

omit [Fintype r] [DecidableEq r] in
/-- **CGLS**: conjugate gradients on the normal equations, with no definition of its own,
$\mathsf{cgIterate}(\mathbf{A}^{\mathsf{H}}\mathbf{A}, \mathbf{A}^{\mathsf{H}}\mathbf{b},
\mathbf{x}_0, q)$. For $\mathbf{A}$ of full column rank and a least-squares solution
$\mathbf{x}_\star$ ($\mathbf{A}^{\mathsf{H}}\mathbf{A}\mathbf{x}_\star =
\mathbf{A}^{\mathsf{H}}\mathbf{b}$),
with $\kappa = \kappa(\mathbf{A})$,
$$\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_q)\|^2 \le
4\Bigl(\frac{\kappa - 1}{\kappa + 1}\Bigr)^{2q}\|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_0)\|^2
\,,$$
written in the $\mathbf{A}^{\mathsf{H}}\mathbf{A}$-norm. [Saad2003, §8.3]; locator to verify. -/
theorem re_quadForm_sub_cgIterate_conjTranspose_mul_le_four_mul_pow {m : Type*} [Fintype m]
    {A : Matrix m n 𝕜} (hA : Function.Injective A.mulVec) {b : m → 𝕜} {xs : n → 𝕜}
    (hxs : (Aᴴ * A) *ᵥ xs = Aᴴ *ᵥ b) (x₀ : n → 𝕜) (q : ℕ) :
    RCLike.re (quadForm (Aᴴ * A) (xs - cgIterate (Aᴴ * A) (Aᴴ *ᵥ b) x₀ q)) ≤
      4 * ((pseudoConditionNumber A - 1) / (pseudoConditionNumber A + 1)) ^ (2 * q) *
        RCLike.re (quadForm (Aᴴ * A) (xs - x₀)) := by
  have hpd := posDef_conjTranspose_mul_self_iff.mpr hA
  have h := hpd.re_quadForm_sub_cgIterate_le_four_mul_pow_pseudoConditionNumber hxs x₀ q
  rwa [pseudoConditionNumber_conjTranspose_mul_self,
    Real.sqrt_sq (pseudoConditionNumber_nonneg A)] at h

omit [Fintype r] [DecidableEq r] in
/-- **Finite termination**: for positive definite $\mathbf{A}$, CG reaches the solution once $q$
is at least the grade of $\mathbf{r}_0$, in particular at $q = \lvert n \rvert$.
[Saad2003, §6.2]. -/
theorem _root_.Matrix.PosDef.cgIterate_eq_of_krylovGrade_le {A : Matrix n n 𝕜} (hA : A.PosDef)
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (x₀ : n → 𝕜) {q : ℕ}
    (h : krylovGrade A (b - A *ᵥ x₀) ≤ q) : cgIterate A b x₀ q = xs := by
  have hxs' : A *ᵥ (xs - x₀) = b - A *ᵥ x₀ := by rw [Matrix.mulVec_sub, hxs]
  rw [cgIterate, hA.galerkinInverse_mulVec_eq_of_mem hxs'
    (mem_krylovSpace_of_krylovGrade_le hA.isUnit hxs' h), add_sub_cancel]

end NLAlib
