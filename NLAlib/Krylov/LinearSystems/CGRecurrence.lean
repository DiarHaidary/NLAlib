/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CG

/-!
# The Hestenes–Stiefel recurrence

The conjugate gradient algorithm of Hestenes and Stiefel as a total recursion on a state indexed
by the step: iterate $\mathbf{x}_k$, residual $\mathbf{r}_k$, search direction $\mathbf{p}_k$.
Breakdown is a value: with $0^{-1} = 0$ a zero residual makes both step sizes zero, and the state
stays at the solution.

The realisation theorem says that for positive definite $\mathbf{A}$ the computed iterates are
the conjugate gradient iterates `NLAlib.cgIterate`, for every $k$ and with no breakdown
hypothesis. Its proof needs only that $\mathbf{x}_k - \mathbf{x}_0$ lies in the Krylov space and
that the residual is orthogonal to it, through the Galerkin characterisation
`Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`.

## Main definitions

* `NLAlib.CGState`, `NLAlib.cgStep`, `NLAlib.cgState`.

## Main results

* `NLAlib.cgState_r_eq`, `NLAlib.cgState_x_sub_mem_krylovSpace`: for every $\mathbf{A}$.
* `Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero`: the residual is
  orthogonal to the Krylov space.
* `Matrix.PosDef.cgState_x_eq`: the Hestenes–Stiefel iterates are the CG iterates.
* `Matrix.PosDef.cgState_r_eq_zero_iff`: the residual vanishes exactly from the grade on.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The state of the Hestenes–Stiefel recurrence after $k$ steps: iterate $\mathbf{x}_k$,
residual $\mathbf{r}_k$, search direction $\mathbf{p}_k$. -/
structure CGState (𝕜 n : Type*) where
  /-- The iterate $\mathbf{x}_k$. -/
  x : n → 𝕜
  /-- The residual $\mathbf{r}_k$, equal to $\mathbf{b} - \mathbf{A}\mathbf{x}_k$. -/
  r : n → 𝕜
  /-- The search direction $\mathbf{p}_k$. -/
  p : n → 𝕜

/-- **One Hestenes–Stiefel step**:
$\alpha_k = \|\mathbf{r}_k\|^2 /
\operatorname{Re}(\mathbf{p}_k^{\mathsf{H}}\mathbf{A}\mathbf{p}_k)$,
$\mathbf{x}_{k+1} = \mathbf{x}_k + \alpha_k\mathbf{p}_k$,
$\mathbf{r}_{k+1} = \mathbf{r}_k - \alpha_k\mathbf{A}\mathbf{p}_k$,
$\beta_k = \|\mathbf{r}_{k+1}\|^2/\|\mathbf{r}_k\|^2$,
$\mathbf{p}_{k+1} = \mathbf{r}_{k+1} + \beta_k\mathbf{p}_k$. With $0^{-1} = 0$ a zero residual
gives $\alpha_k = \beta_k = 0$ and the state stays put.
[HestenesStiefel1952]; [TrefethenBau1997, Algorithm 38.1]. -/
noncomputable def cgStep (A : Matrix n n 𝕜) (s : CGState 𝕜 n) : CGState 𝕜 n :=
  let α : ℝ := ‖WithLp.toLp 2 s.r‖ ^ 2 / RCLike.re (quadForm A s.p)
  let r' := s.r - (α : 𝕜) • (A *ᵥ s.p)
  ⟨s.x + (α : 𝕜) • s.p, r',
    r' + ((‖WithLp.toLp 2 r'‖ ^ 2 / ‖WithLp.toLp 2 s.r‖ ^ 2 : ℝ) : 𝕜) • s.p⟩

/-- The **Hestenes–Stiefel recurrence** (the conjugate gradient algorithm) from the start
$\mathbf{x}_0$: the state after $k$ steps, from $(\mathbf{x}_0, \mathbf{r}_0, \mathbf{r}_0)$,
$\mathbf{r}_0 = \mathbf{b} - \mathbf{A}\mathbf{x}_0$. [HestenesStiefel1952]. -/
noncomputable def cgState (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) : ℕ → CGState 𝕜 n
  | 0 => ⟨x₀, b - A *ᵥ x₀, b - A *ᵥ x₀⟩
  | k + 1 => cgStep A (cgState A b x₀ k)

variable {A : Matrix n n 𝕜} {b x₀ : n → 𝕜}

omit [DecidableEq n] in
/-- The updated residual is the true residual, for every $\mathbf{A}$. -/
theorem cgState_r_eq (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).r = b - A *ᵥ (cgState A b x₀ k).x := by
  sorry

/-- The iterates stay in the shifted Krylov space, for every $\mathbf{A}$:
$\mathbf{x}_k - \mathbf{x}_0 \in \mathcal{K}_k(\mathbf{A}, \mathbf{r}_0)$.
Proof: jointly with $\mathbf{r}_k, \mathbf{p}_k \in \mathcal{K}_{k+1}$, by induction
(`mulVec_mem_krylovSpace_succ`, `krylovSpace_mono`). Small. -/
theorem cgState_x_sub_mem_krylovSpace (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).x - x₀ ∈ krylovSpace A (b - A *ᵥ x₀) k := by
  sorry

/-- **The residual is orthogonal to the Krylov space**, for positive definite $\mathbf{A}$:
$\mathbf{K}_k(\mathbf{A}, \mathbf{r}_0)^{\mathsf{H}}\mathbf{r}_k = \mathbf{0}$.
Proof: joint induction with `Matrix.PosDef.span_cgState_p` and the $\mathbf{A}$-conjugacy of
$\mathbf{p}_k$ to $\mathcal{K}_k$; $\alpha_k$ makes $\mathbf{r}_{k+1} \perp \mathbf{p}_k$ and
Hermitian symmetry the rest. Medium; prove first, with `span_cgState_p`. -/
theorem _root_.Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero (hA : A.PosDef)
    (b x₀ : n → 𝕜) (k : ℕ) : (krylovMatrix A (b - A *ᵥ x₀) k)ᴴ *ᵥ (cgState A b x₀ k).r = 0 := by
  sorry

/-- The search directions span the Krylov spaces, for positive definite $\mathbf{A}$. -/
theorem _root_.Matrix.PosDef.span_cgState_p (hA : A.PosDef) (k : ℕ) :
    Submodule.span 𝕜 (Set.range fun j : Fin k => (cgState A b x₀ j).p) =
      krylovSpace A (b - A *ᵥ x₀) k := by
  sorry

omit [DecidableEq n] in
/-- **The residuals are orthogonal**, for positive definite $\mathbf{A}$:
$\mathbf{r}_j^{\mathsf{H}}\mathbf{r}_k = 0$ for $j < k$. -/
theorem _root_.Matrix.PosDef.star_cgState_r_dotProduct_eq_zero (hA : A.PosDef) {j k : ℕ}
    (hjk : j < k) : star (cgState A b x₀ j).r ⬝ᵥ (cgState A b x₀ k).r = 0 := by
  sorry

omit [DecidableEq n] in
/-- **The search directions are $\mathbf{A}$-conjugate**, for positive definite $\mathbf{A}$:
$\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_k = 0$ for $j < k$. -/
theorem _root_.Matrix.PosDef.star_cgState_p_dotProduct_mulVec_eq_zero (hA : A.PosDef) {j k : ℕ}
    (hjk : j < k) : star (cgState A b x₀ j).p ⬝ᵥ (A *ᵥ (cgState A b x₀ k).p) = 0 := by
  sorry

/-- **The Hestenes–Stiefel iterates are the CG iterates**: for positive definite $\mathbf{A}$ and
every $k$, with no breakdown hypothesis,
$\mathbf{x}_k = \mathbf{x}_0 +
\mathsf{cgIterate}(\mathbf{A}, \mathbf{b} - \mathbf{A}\mathbf{x}_0, k)$.
[HestenesStiefel1952]; [TrefethenBau1997, Theorem 38.1].
Proof: `cgState_x_sub_mem_krylovSpace`, `cgState_r_eq` and
`Matrix.PosDef.conjTranspose_krylovMatrix_mulVec_cgState_r_eq_zero` in
`Matrix.PosDef.eq_cgIterate_of_conjTranspose_krylovMatrix_mulVec_sub_eq_zero`. Small.
Result: cg-recurrence -/
theorem _root_.Matrix.PosDef.cgState_x_eq (hA : A.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).x = x₀ + cgIterate A (b - A *ᵥ x₀) k := by
  sorry

/-- **CG stops exactly at the grade**: for positive definite $\mathbf{A}$ the computed residual
vanishes iff $k$ is at least the grade of $\mathbf{r}_0$. -/
theorem _root_.Matrix.PosDef.cgState_r_eq_zero_iff (hA : A.PosDef) (b x₀ : n → 𝕜) (k : ℕ) :
    (cgState A b x₀ k).r = 0 ↔ krylovGrade A (b - A *ᵥ x₀) ≤ k := by
  sorry

end NLAlib
