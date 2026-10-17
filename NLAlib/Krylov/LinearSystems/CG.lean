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

/-!
# The conjugate gradient iterate

The conjugate gradient iterate is defined mathematically, with no algorithm: it is the Galerkin
approximation to the solution of $\mathbf{A}\mathbf{x} = \mathbf{b}$ from the Krylov space,
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q) =
\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{A}, \mathbf{b}))\,\mathbf{b}$. For
positive definite $\mathbf{A}$ it equals
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$ for
every orthonormal basis $\mathbf{Q}$ of the Krylov space, minimises the $\mathbf{A}$-norm error over
it, beats every residual polynomial, converges at the Chebyshev rate and terminates at the grade.
The Hestenes–Stiefel recurrence computes it (`Matrix.PosDef.cgState_x_eq`), and so does the Lanczos
recurrence (`Matrix.PosDef.cgIterate_eq_lanczosMatrix`).

Errors are written target minus output, $\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A},
\mathbf{b}, q)$ with $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, in the squared $\mathbf{A}$-norm
`RCLike.re (quadForm A _)`. Spectral hypotheses are `spectrum ℝ A ⊆ s`; a Loewner sandwich reaches
them through `spectrum_subset_Icc_of_le`.

## Main definitions

* `NLAlib.cgIterate`: the CG iterate from the zero start.

## Main results

* `Matrix.PosDef.cgIterate_eq`: CG is
  $\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
  for any orthonormal basis of the Krylov space.
* `Matrix.PosDef.isMinOn_cgIterate`: $\mathbf{A}$-norm optimality.
* `Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`: the Galerkin
  characterisation.
* `NLAlib.exists_sub_cgIterate_eq_aeval`: the error polynomial.
* `Matrix.PosDef.re_quadForm_sub_cgIterate_le_re_quadForm_aeval`: CG beats every residual
  polynomial.
* `Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_two_mul_pow`: the Chebyshev rate.
* `Matrix.PosDef.cgIterate_eq_of_krylovGrade_le`: finite termination.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder
open Polynomial

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-- The **conjugate gradient iterate** after $q$ steps from the zero start:
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q) :=
\mathsf{galerkinInverse}(\mathbf{A}, \mathbf{K}_q(\mathbf{A}, \mathbf{b}))\,\mathbf{b}$, which is
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
for every orthonormal basis $\mathbf{Q}$ of $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ when
$\mathbf{A}$ is positive definite (`Matrix.PosDef.cgIterate_eq`). A start $\mathbf{x}_0$ is
$\mathbf{x}_0 + \mathsf{cgIterate}(\mathbf{A}, \mathbf{b} - \mathbf{A}\mathbf{x}_0, q)$. The
definition is basis-free, total and not an algorithm; the Hestenes–Stiefel recurrence computes it
(`Matrix.PosDef.cgState_x_eq`). Junk value: when the compression of $\mathbf{A}$ to the Krylov
space is singular, the pseudoinverse formula of `galerkinInverse`.
[HestenesStiefel1952]; [Saad2003, §6.7]. -/
noncomputable def cgIterate (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) : n → 𝕜 :=
  galerkinInverse A (krylovMatrix A b q) *ᵥ b

/-- The CG iterate lies in the Krylov space, for every $\mathbf{A}$. -/
theorem cgIterate_mem_krylovSpace (A : Matrix n n 𝕜) (b : n → 𝕜) (q : ℕ) :
    cgIterate A b q ∈ krylovSpace A b q :=
  galerkinInverse_mulVec_mem A _ b

/-- The zeroth iterate is zero. -/
@[simp]
theorem cgIterate_zero (A : Matrix n n 𝕜) (b : n → 𝕜) : cgIterate A b 0 = 0 := by
  have h := cgIterate_mem_krylovSpace A b 0
  rwa [krylovSpace_zero, Submodule.mem_bot] at h

/-- **CG in any orthonormal basis of the Krylov space**, for every $\mathbf{A}$:
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q) =
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$. -/
theorem HasOrthonormalCols.cgIterate_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    cgIterate A b q = Q *ᵥ (pinv (Qᴴ * A * Q) *ᵥ (Qᴴ *ᵥ b)) := by
  rw [cgIterate, hQ.galerkinInverse_eq hK A, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

/-- **CG is
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
for any orthonormal basis $\mathbf{Q}$ of the Krylov space**, for positive definite $\mathbf{A}$.
[Saad2003, §6.7].
Result: cg-galerkin-formula -/
theorem _root_.Matrix.PosDef.cgIterate_eq {A : Matrix n n 𝕜} (hA : A.PosDef)
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    cgIterate A b q = Q *ᵥ ((Qᴴ * A * Q)⁻¹ *ᵥ (Qᴴ *ᵥ b)) := by
  rw [cgIterate, hA.galerkinInverse_eq hQ hK, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

omit [Fintype r] [DecidableEq r] in
/-- **The Galerkin condition**: for positive definite $\mathbf{A}$ the residual
$\mathbf{b} - \mathbf{A}\,\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)$ is orthogonal to
$\mathcal{K}_q(\mathbf{A}, \mathbf{b})$:
$\mathbf{K}_q^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\,\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q))
= \mathbf{0}$. -/
theorem _root_.Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero
    {A : Matrix n n 𝕜} (hA : A.PosDef) (b : n → 𝕜) (q : ℕ) :
    (krylovMatrix A b q)ᴴ *ᵥ (b - A *ᵥ cgIterate A b q) = 0 := by
  have h := congrArg (· *ᵥ b)
    (hA.conjTranspose_mul_one_sub_mul_galerkinInverse (krylovMatrix A b q))
  simpa only [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.zero_mulVec, Matrix.mulVec_sub, cgIterate] using h

omit [Fintype r] [DecidableEq r] in
/-- **The Galerkin condition characterises CG**: for positive definite $\mathbf{A}$, a vector of
$\mathcal{K}_q(\mathbf{A}, \mathbf{b})$ whose residual is orthogonal to $\mathcal{K}_q$ is
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)$. -/
theorem _root_.Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero
    {A : Matrix n n 𝕜} (hA : A.PosDef) {b y : n → 𝕜} {q : ℕ} (hy : y ∈ krylovSpace A b q)
    (h : (krylovMatrix A b q)ᴴ *ᵥ (b - A *ᵥ y) = 0) : y = cgIterate A b q :=
  hA.eq_galerkinInverse_mulVec_of_conjTranspose_mulVec_sub_eq_zero hy h

omit [Fintype r] [DecidableEq r] in
/-- **CG minimises the $\mathbf{A}$-norm error** over the Krylov space: for positive definite
$\mathbf{A}$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)$ minimises
$\|\mathbf{x}_\star - \mathbf{y}\|_{\mathbf{A}}^2$ over $\mathbf{y} \in \mathcal{K}_q(\mathbf{A},
\mathbf{b})$. [Saad2003, §5.2]; [TrefethenBau1997, Theorem 38.1].
Result: cg-optimality -/
theorem _root_.Matrix.PosDef.isMinOn_cgIterate {A : Matrix n n 𝕜} (hA : A.PosDef)
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (q : ℕ) :
    IsMinOn (fun y => RCLike.re (quadForm A (xs - y))) (krylovSpace A b q : Set (n → 𝕜))
      (cgIterate A b q) :=
  hA.isMinOn_galerkinInverse_mulVec _ hxs

omit [Fintype r] [DecidableEq r] in
/-- **The CG error polynomial**: for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ there is
$p \in \Bbbk[X]$ with $\deg p \le q$ and $p(0) = 1$ such that
$\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q) = p(\mathbf{A})\mathbf{x}_\star$.
No assumption on $\mathbf{A}$. [Saad2003, §6.11.3]. -/
theorem exists_sub_cgIterate_eq_aeval {A : Matrix n n 𝕜} {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (q : ℕ) : ∃ p : 𝕜[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      xs - cgIterate A b q = aeval A p *ᵥ xs := by
  obtain ⟨s, hs, hsb⟩ := mem_krylovSpace_iff.1 (cgIterate_mem_krylovSpace A b q)
  refine ⟨1 - s * X, ?_, by simp, ?_⟩
  · rcases eq_or_ne s 0 with rfl | h0
    · simp only [zero_mul, sub_zero]
      exact degree_one_le.trans (by exact_mod_cast Nat.zero_le q)
    · have hnat : s.natDegree < q := (natDegree_lt_iff_degree_lt h0).2 hs
      refine degree_le_of_natDegree_le ((natDegree_sub_le _ _).trans (max_le ?_ ?_))
      · rw [natDegree_one]
        exact Nat.zero_le q
      · exact natDegree_mul_le.trans (by rw [natDegree_X]; omega)
  · rw [← hsb, ← hxs, map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]

omit [Fintype r] [DecidableEq r] in
/-- **CG beats every residual polynomial**: for positive definite $\mathbf{A}$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and every real $p$ with $\deg p \le q$, $p(0) = 1$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}}^2 \le
\|p(\mathbf{A})\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$ [Saad2003, §6.11.3]. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_re_quadForm_aeval {A : Matrix n n 𝕜}
    (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) {q : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤
      RCLike.re (quadForm A (aeval A p *ᵥ xs)) := by
  obtain ⟨s, hs, hps⟩ := exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one hp hp₀
  have hy : aeval A s *ᵥ b ∈ krylovSpace A b q := aeval_mulVec_mem_krylovSpace A b hs
  have hp' : p = 1 - s * X := by rw [mul_comm, ← hps, sub_sub_cancel]
  have heq : xs - aeval A s *ᵥ b = aeval A p *ᵥ xs := by
    rw [hp', ← hxs, map_sub, map_one, map_mul, aeval_X, Matrix.sub_mulVec, Matrix.one_mulVec,
      Matrix.mulVec_mulVec]
  have h : RCLike.re (quadForm A (xs - cgIterate A b q)) ≤
      RCLike.re (quadForm A (xs - aeval A s *ᵥ b)) := hA.isMinOn_cgIterate hxs q hy
  rwa [heq] at h

omit [Fintype r] [DecidableEq r] in
/-- **The polynomial bound for CG**: if $\mathbf{A}$ is positive definite with spectrum in a set
$s$, $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, and a real $p$ with $\deg p \le q$, $p(0) = 1$
satisfies $\lvert p \rvert \le M$ on $s$, then
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}}^2 \le
M^2 \|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$ [Saad2003, §6.11.3]. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le {A : Matrix n n 𝕜} (hA : A.PosDef)
    {s : Set ℝ} (hs : spectrum ℝ A ⊆ s) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) {q : ℕ}
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) {M : ℝ}
    (hM : ∀ x ∈ s, |p.eval x| ≤ M) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤ M ^ 2 * RCLike.re (quadForm A xs) := by
  refine (hA.re_quadForm_sub_cgIterate_le_re_quadForm_aeval hxs hp hp₀).trans ?_
  have h := hA.isHermitian.re_quadForm_aeval_aeval_mulVec_le subset_rfl X p
    (fun x hx => by rw [eval_X]; exact (hA.spectrum_subset_Ioi hx).le) (fun x hx => hM x (hs hx)) xs
  rwa [aeval_X] at h

omit [Fintype r] [DecidableEq r] in
/-- **The Chebyshev bound for CG**: if $\mathbf{A}$ is Hermitian with spectrum in $[a, a']$,
$0 < a$, and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}}^2 \le
\Bigl(2\Bigl(\frac{\sqrt{a'} - \sqrt{a}}{\sqrt{a'} + \sqrt{a}}\Bigr)^q\Bigr)^2
\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$
A Loewner sandwich $a\mathbf{I} \preceq \mathbf{A} \preceq a'\mathbf{I}$ gives the hypotheses by
`isHermitian_of_le_smul_one` and `spectrum_subset_Icc_of_le`.
[Saad2003, Theorem 6.29]; stated there for the $\mathbf{A}$-norm itself, here squared, over any
`RCLike` field and with an interval $[a, a']$ containing the spectrum in place of the extreme
eigenvalues.
Result: cg-chebyshev-bound -/
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_two_mul_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤
      (2 * ((Real.sqrt a' - Real.sqrt a) / (Real.sqrt a' + Real.sqrt a)) ^ q) ^ 2 *
        RCLike.re (quadForm A xs) := by
  have hpd : A.PosDef := hA.posDef_iff_eigenvalue_pos.mpr fun k hk =>
    ha.trans_le (hA.spectrum_subset_iff.mp hs k hk).1
  rcases lt_trichotomy a a' with hlt | rfl | hgt
  · refine hpd.re_quadForm_sub_cgIterate_le hs hxs (degree_chebyshevResidual_le a a' q)
      (eval_chebyshevResidual_zero q ha hlt) fun x hx => ?_
    have h := (isUniformApproxOn_chebyshevResidual_two_mul_pow q ha hlt) x hx
    rwa [Real.dist_eq, sub_zero] at h
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · refine hpd.re_quadForm_sub_cgIterate_le hs hxs (p := 1) (by
        exact degree_one_le.trans le_rfl) (by simp) fun x _ => ?_
      norm_num
    · refine hpd.re_quadForm_sub_cgIterate_le hs hxs (p := 1 - C a⁻¹ * X) ?_ (by simp)
        fun x hx => ?_
      · refine (degree_sub_le _ _).trans (max_le (degree_one_le.trans ?_) ?_)
        · exact_mod_cast Nat.zero_le q
        · exact (degree_C_mul_X_le _).trans (by exact_mod_cast hq)
      · rw [Set.Icc_self, Set.mem_singleton_iff] at hx
        subst hx
        simp [ha.ne', zero_pow hq.ne']
  · refine hpd.re_quadForm_sub_cgIterate_le hs hxs (p := 1) (degree_one_le.trans (by
      exact_mod_cast Nat.zero_le q)) (by simp) fun x hx => ?_
    exact absurd (hx.1.trans hx.2) (not_le.mpr hgt)

omit [Fintype r] [DecidableEq r] in
/-- **The Chebyshev bound in the condition number**: for positive definite $\mathbf{A}$ with
$\kappa = \kappa(\mathbf{A})$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}}^2 \le
\Bigl(2\Bigl(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\Bigr)^q\Bigr)^2
\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$ [Saad2003, (6.128)]. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_two_mul_pow_pseudoConditionNumber
    {A : Matrix n n 𝕜} (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤
      (2 * ((Real.sqrt (pseudoConditionNumber A) - 1) /
        (Real.sqrt (pseudoConditionNumber A) + 1)) ^ q) ^ 2 * RCLike.re (quadForm A xs) := by
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
  have h := hA.isHermitian.re_quadForm_sub_cgIterate_le_two_mul_pow hpos hs hxs q
  have hl0 : 0 < eigenvalue A 0 :=
    hpos.trans_le (hA.isHermitian.eigenvalue_le_eigenvalue (Nat.zero_le k) (by omega))
  have hκ : (Real.sqrt (pseudoConditionNumber A) - 1) / (Real.sqrt (pseudoConditionNumber A) + 1) =
      (Real.sqrt (eigenvalue A 0) - Real.sqrt (eigenvalue A k)) /
        (Real.sqrt (eigenvalue A 0) + Real.sqrt (eigenvalue A k)) := by
    have hsk := Real.sqrt_pos.2 hpos
    have hs0 := Real.sqrt_pos.2 hl0
    rw [hA.pseudoConditionNumber_eq hk, Real.sqrt_div' _ hpos.le]
    field_simp
  rwa [hκ]

omit [Fintype r] [DecidableEq r] in
/-- **Finite termination**: for positive definite $\mathbf{A}$, CG reaches the solution once $q$
is at least the grade of $\mathbf{b}$, in particular at $q = \lvert n \rvert$.
[Saad2003, §6.2]. -/
theorem _root_.Matrix.PosDef.cgIterate_eq_of_krylovGrade_le {A : Matrix n n 𝕜} (hA : A.PosDef)
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) {q : ℕ} (h : krylovGrade A b ≤ q) :
    cgIterate A b q = xs :=
  hA.galerkinInverse_mulVec_eq_of_mem hxs (mem_krylovSpace_of_krylovGrade_le hA.isUnit hxs h)

end NLAlib
