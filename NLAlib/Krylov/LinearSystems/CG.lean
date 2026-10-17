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
  sorry

/-- **CG in any orthonormal basis of the Krylov space**, for every $\mathbf{A}$:
$\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q) =
\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$. -/
theorem HasOrthonormalCols.cgIterate_eq {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q)
    {A : Matrix n n 𝕜} {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    cgIterate A b q = Q *ᵥ (pinv (Qᴴ * A * Q) *ᵥ (Qᴴ *ᵥ b)) := by
  sorry

/-- **CG is
$\mathbf{Q}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q})^{-1}\mathbf{Q}^{\mathsf{H}}\mathbf{b}$
for any orthonormal basis $\mathbf{Q}$ of the Krylov space**, for positive definite $\mathbf{A}$.
[Saad2003, §6.7].
Result: cg-galerkin-formula -/
theorem _root_.Matrix.PosDef.cgIterate_eq {A : Matrix n n 𝕜} (hA : A.PosDef)
    {Q : Matrix n r 𝕜} (hQ : HasOrthonormalCols Q) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) :
    cgIterate A b q = Q *ᵥ ((Qᴴ * A * Q)⁻¹ *ᵥ (Qᴴ *ᵥ b)) := by
  sorry

omit [Fintype r] [DecidableEq r] in
/-- **The Galerkin condition**: for positive definite $\mathbf{A}$ the residual
$\mathbf{b} - \mathbf{A}\,\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)$ is orthogonal to
$\mathcal{K}_q(\mathbf{A}, \mathbf{b})$:
$\mathbf{K}_q^{\mathsf{H}}(\mathbf{b} - \mathbf{A}\,\mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q))
= \mathbf{0}$. -/
theorem _root_.Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_sub_mulVec_cgIterate_eq_zero
    {A : Matrix n n 𝕜} (hA : A.PosDef) (b : n → 𝕜) (q : ℕ) :
    (krylovMatrix A b q)ᴴ *ᵥ (b - A *ᵥ cgIterate A b q) = 0 := by
  sorry

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
No assumption on $\mathbf{A}$. [Saad2003, §6.11.3].
Proof: `cgIterate_mem_krylovSpace` and `mem_krylovSpace_iff` give $s$; take $p = 1 - Xs$. Small. -/
theorem exists_sub_cgIterate_eq_aeval {A : Matrix n n 𝕜} {b xs : n → 𝕜} (hxs : A *ᵥ xs = b)
    (q : ℕ) : ∃ p : 𝕜[X], p.degree ≤ q ∧ p.eval 0 = 1 ∧
      xs - cgIterate A b q = aeval A p *ᵥ xs := by
  sorry

omit [Fintype r] [DecidableEq r] in
/-- **CG beats every residual polynomial**: for positive definite $\mathbf{A}$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and every real $p$ with $\deg p \le q$, $p(0) = 1$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}}^2 \le
\|p(\mathbf{A})\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$ [Saad2003, §6.11.3].
Proof: `Polynomial.exists_degree_lt_one_sub_eq_X_mul_of_eval_zero_eq_one`, then
`aeval_mulVec_mem_krylovSpace` and `Matrix.PosDef.isMinOn_cgIterate`. Small. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_re_quadForm_aeval {A : Matrix n n 𝕜}
    (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) {q : ℕ} {p : ℝ[X]}
    (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤
      RCLike.re (quadForm A (aeval A p *ᵥ xs)) := by
  sorry

omit [Fintype r] [DecidableEq r] in
/-- **The polynomial bound for CG**: if $\mathbf{A}$ is positive definite with spectrum in a set
$s$, $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, and a real $p$ with $\deg p \le q$, $p(0) = 1$
satisfies $\lvert p \rvert \le M$ on $s$, then
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}}^2 \le
M^2 \|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$ [Saad2003, §6.11.3].
Proof: the comparison theorem, then `Matrix.IsHermitian.re_quadForm_aeval_aeval_mulVec_le` with
weight $X$ on the spectrum. Small. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le {A : Matrix n n 𝕜} (hA : A.PosDef)
    {s : Set ℝ} (hs : spectrum ℝ A ⊆ s) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) {q : ℕ}
    {p : ℝ[X]} (hp : p.degree ≤ q) (hp₀ : p.eval 0 = 1) {M : ℝ}
    (hM : ∀ x ∈ s, |p.eval x| ≤ M) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤ M ^ 2 * RCLike.re (quadForm A xs) := by
  sorry

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
Proof: for $a < a'$ the polynomial bound at `chebyshevResidual a a' q`
(`isUniformApproxOn_chebyshevResidual_two_mul_pow`); for $a = a'$ at $1 - X/a$; for $a' < a$ the
index type is empty. Small.
Result: cg-chebyshev-bound -/
theorem _root_.Matrix.IsHermitian.re_quadForm_sub_cgIterate_le_two_mul_pow {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a')
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤
      (2 * ((Real.sqrt a' - Real.sqrt a) / (Real.sqrt a' + Real.sqrt a)) ^ q) ^ 2 *
        RCLike.re (quadForm A xs) := by
  sorry

omit [Fintype r] [DecidableEq r] in
/-- **The Chebyshev bound in the condition number**: for positive definite $\mathbf{A}$ with
$\kappa = \kappa(\mathbf{A})$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{x}_\star - \mathsf{cgIterate}(\mathbf{A}, \mathbf{b}, q)\|_{\mathbf{A}}^2 \le
\Bigl(2\Bigl(\frac{\sqrt{\kappa} - 1}{\sqrt{\kappa} + 1}\Bigr)^q\Bigr)^2
\|\mathbf{x}_\star\|_{\mathbf{A}}^2 \,.$$ [Saad2003, (6.128)].
Proof: the rate at the extreme eigenvalues and `Matrix.PosDef.pseudoConditionNumber_eq`. Small. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_le_two_mul_pow_pseudoConditionNumber
    {A : Matrix n n 𝕜} (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (q : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b q)) ≤
      (2 * ((Real.sqrt (pseudoConditionNumber A) - 1) /
        (Real.sqrt (pseudoConditionNumber A) + 1)) ^ q) ^ 2 * RCLike.re (quadForm A xs) := by
  sorry

omit [Fintype r] [DecidableEq r] in
/-- **Finite termination**: for positive definite $\mathbf{A}$, CG reaches the solution once $q$
is at least the grade of $\mathbf{b}$, in particular at $q = \lvert n \rvert$.
[Saad2003, §6.2]. -/
theorem _root_.Matrix.PosDef.cgIterate_eq_of_krylovGrade_le {A : Matrix n n 𝕜} (hA : A.PosDef)
    {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) {q : ℕ} (h : krylovGrade A b ≤ q) :
    cgIterate A b q = xs :=
  hA.galerkinInverse_mulVec_eq_of_mem hxs (mem_krylovSpace_of_krylovGrade_le hA.isUnit hxs h)

end NLAlib
