/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.LinearSystems.CGLanczos
public import NLAlib.Krylov.LinearSystems.CGRecurrence

/-!
# The tridiagonal matrix of the conjugate gradient coefficients

The coefficients of the Hestenes–Stiefel recurrence determine the Lanczos tridiagonal matrix
through its $\mathbf{L}\mathbf{D}\mathbf{L}^{\mathsf{T}}$ factorisation: with step lengths
$\gamma_j$ and residual norms $\rho_j$,
$$\mathbf{T}_k = \mathbf{L}_k\,\operatorname{diag}(\gamma_0^{-1}, \dots, \gamma_{k-1}^{-1})\,
\mathbf{L}_k^{\mathsf{T}},\qquad (\mathbf{L}_k)_{i+1,i} = \rho_{i+1}/\rho_i,$$
(`NLAlib.cgTridiagonal`, defined from any two sequences), and conversely, since the factorisation
of a positive definite matrix is unique, a matrix on which exact Lanczos computes
`NLAlib.cgTridiagonal γ ρ k` is one on which exact CG computes the step lengths $\gamma_j$ and the
residual norms $\rho_j$. The first entry of the inverse is the Gauss quadrature value
$\rho_0^2(\mathbf{T}_k^{-1})_{00} = \sum_{i<k}\gamma_i\rho_i^2$, and the squared
$\mathbf{A}$-norm error decreases by $\gamma_j\rho_j^2$ at step $j$ [HestenesStiefel1952,
Theorem 6:1]. Together with the pivot bounds of a positive definite CG run (residual ratios,
$\|\mathbf{p}_j\| / \|\mathbf{r}_j\|$, the coefficient ratio $\delta_j/\gamma_j$), this is the
exact-arithmetic layer of the finite-precision conjugate gradient analysis.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§5).
Placement on integration: `NLAlib.cgAlpha` and the pivot bounds go to `CGRecurrence.lean`, the
rest is a new file `NLAlib/Krylov/LinearSystems/CGTridiagonal.lean`.

## Main definitions

* `NLAlib.cgAlpha`: the step length of a Hestenes–Stiefel state.
* `NLAlib.cgBidiagonal`, `NLAlib.cgTridiagonal`: the factors and the tridiagonal matrix.

## Main results

* `NLAlib.cgTridiagonal_eq_mul`: the factorisation.
* `NLAlib.sq_mul_inv_cgTridiagonal_zero_zero`: the Gauss quadrature value.
* `Matrix.PosDef.lanczosTridiagonal_eq_cgTridiagonal`: exact CG–Lanczos correspondence.
* `Matrix.PosDef.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq`,
  `Matrix.PosDef.norm_cgState_r_eq_of_lanczosTridiagonal_eq`: the converse.
* `Matrix.PosDef.re_quadForm_sub_cgIterate_sub_re_quadForm_sub_cgIterate_succ`: the decrease of
  the error.
* `Matrix.PosDef.norm_cgState_p_sq_eq`: the direction norm [HestenesStiefel1952, Theorem 5:5].
* `Matrix.PosDef.norm_cgState_r_le`, `Matrix.PosDef.norm_cgState_p_sq_le`,
  `Matrix.PosDef.cgAlpha_le`, `Matrix.PosDef.norm_cgState_r_succ_sq_div_le`: pivot bounds.
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The **step length** of the Hestenes–Stiefel state $s$:
$\gamma = \|\mathbf{r}\|^2/\operatorname{Re}(\mathbf{p}^{\mathsf{H}}\mathbf{A}\mathbf{p})$, the
$\alpha_k$ of `NLAlib.cgStep` (to be used there by name on integration). -/
noncomputable def cgAlpha (A : Matrix n n 𝕜) (s : CGState 𝕜 n) : ℝ :=
  ‖WithLp.toLp 2 s.r‖ ^ 2 / RCLike.re (quadForm A s.p)

omit [DecidableEq n] in
/-- The iterate update of `NLAlib.cgStep` with the named step length. -/
theorem cgStep_x (A : Matrix n n 𝕜) (s : CGState 𝕜 n) :
    (cgStep A s).x = s.x + (cgAlpha A s : 𝕜) • s.p :=
  rfl

/-! ### Identities of the Hestenes–Stiefel recurrence -/

section Identities

omit [DecidableEq n]

/-- One Hestenes–Stiefel step, by components. -/
private theorem cgState_succ_eq (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) (j : ℕ) :
    (cgState A b x₀ (j + 1)).x =
        (cgState A b x₀ j).x + (cgAlpha A (cgState A b x₀ j) : 𝕜) • (cgState A b x₀ j).p ∧
      (cgState A b x₀ (j + 1)).r = (cgState A b x₀ j).r -
        (cgAlpha A (cgState A b x₀ j) : 𝕜) • (A *ᵥ (cgState A b x₀ j).p) ∧
      (cgState A b x₀ (j + 1)).p = (cgState A b x₀ (j + 1)).r +
        ((‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
          ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2 : ℝ) : 𝕜) • (cgState A b x₀ j).p :=
  ⟨rfl, rfl, rfl⟩

/-- The step length is nonnegative for positive definite $\mathbf{A}$. -/
private theorem cgAlpha_nonneg {A : Matrix n n 𝕜} (hA : A.PosDef) (s : CGState 𝕜 n) :
    0 ≤ cgAlpha A s :=
  div_nonneg (sq_nonneg _) (hA.posSemidef.re_quadForm_nonneg _)

/-- The line search: $\mathbf{p}_j^{\mathsf{H}}\mathbf{r}_j = \|\mathbf{r}_j\|^2$ gives
$\mathbf{p}_j^{\mathsf{H}}\mathbf{r}_{j+1} = 0$. -/
private theorem star_p_dotProduct_r_succ_of {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜)
    (j : ℕ) (h : star (cgState A b x₀ j).p ⬝ᵥ (cgState A b x₀ j).r =
      ((‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2 : ℝ) : 𝕜)) :
    star (cgState A b x₀ j).p ⬝ᵥ (cgState A b x₀ (j + 1)).r = 0 := by
  rw [(cgState_succ_eq A b x₀ j).2.1]
  set s := cgState A b x₀ j
  by_cases hp : s.p = 0
  · simp [hp]
  have hQ := hA.re_quadForm_pos hp
  have hquad : star s.p ⬝ᵥ (A *ᵥ s.p) = (RCLike.re (quadForm A s.p) : 𝕜) :=
    (hA.isHermitian.coe_re_quadForm _).symm
  rw [dotProduct_sub, dotProduct_smul, hquad, h, smul_eq_mul, ← RCLike.ofReal_mul, cgAlpha,
    div_mul_cancel₀ _ hQ.ne', sub_self]

/-- $\mathbf{p}_j^{\mathsf{H}}\mathbf{r}_j = \|\mathbf{r}_j\|^2$. -/
private theorem star_p_dotProduct_r {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜) :
    ∀ j, star (cgState A b x₀ j).p ⬝ᵥ (cgState A b x₀ j).r =
      ((‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2 : ℝ) : 𝕜)
  | 0 => EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq _
  | j + 1 => by
    have h0 := star_p_dotProduct_r_succ_of hA b x₀ j (star_p_dotProduct_r hA b x₀ j)
    rw [(cgState_succ_eq A b x₀ j).2.2, star_add, add_dotProduct, star_smul, smul_dotProduct, h0,
      smul_zero, add_zero]
    exact EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq _

/-- $\mathbf{p}_j^{\mathsf{H}}\mathbf{r}_{j+1} = 0$. -/
private theorem star_p_dotProduct_r_succ {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜)
    (j : ℕ) : star (cgState A b x₀ j).p ⬝ᵥ (cgState A b x₀ (j + 1)).r = 0 :=
  star_p_dotProduct_r_succ_of hA b x₀ j (star_p_dotProduct_r hA b x₀ j)

/-- A nonzero residual has a nonzero direction. -/
private theorem p_ne_zero {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜) {j : ℕ}
    (hr : (cgState A b x₀ j).r ≠ 0) : (cgState A b x₀ j).p ≠ 0 := by
  intro hp
  have h := star_p_dotProduct_r hA b x₀ j
  rw [hp, star_zero, zero_dotProduct] at h
  have h2 : ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2 = 0 := by exact_mod_cast h.symm
  exact hr (by simpa using h2)

/-- For a nonzero residual, $\gamma_j\,\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j =
\|\mathbf{r}_j\|^2$ with a positive quadratic form. -/
private theorem cgAlpha_mul_re_quadForm {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜)
    {j : ℕ} (hr : (cgState A b x₀ j).r ≠ 0) :
    cgAlpha A (cgState A b x₀ j) * RCLike.re (quadForm A (cgState A b x₀ j).p) =
        ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2 ∧
      0 < RCLike.re (quadForm A (cgState A b x₀ j).p) := by
  have hQ := hA.re_quadForm_pos (p_ne_zero hA b x₀ hr)
  exact ⟨div_mul_cancel₀ _ hQ.ne', hQ⟩

/-- A zero residual stays zero, with a zero direction. -/
private theorem cgState_succ_of_r_eq_zero (A : Matrix n n 𝕜) (b x₀ : n → 𝕜) {j : ℕ}
    (hr : (cgState A b x₀ j).r = 0) :
    (cgState A b x₀ (j + 1)).r = 0 ∧ (cgState A b x₀ (j + 1)).p = 0 := by
  obtain ⟨-, h1, h2⟩ := cgState_succ_eq A b x₀ j
  have hα : cgAlpha A (cgState A b x₀ j) = 0 := by simp [cgAlpha, hr]
  have hr' : (cgState A b x₀ (j + 1)).r = 0 := by rw [h1, hα, hr]; simp
  exact ⟨hr', by rw [h2, hr', hr]; simp⟩

/-- The direction update is orthogonal:
$\|\mathbf{p}_{j+1}\|^2 = \|\mathbf{r}_{j+1}\|^2 + \delta_j^2\|\mathbf{p}_j\|^2$. -/
private theorem norm_p_succ_sq {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜) (j : ℕ) :
    ‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).p‖ ^ 2 =
      ‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 +
      (‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
        ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2) ^ 2 *
        ‖WithLp.toLp 2 (cgState A b x₀ j).p‖ ^ 2 := by
  have h0 := star_p_dotProduct_r_succ hA b x₀ j
  have h0' : star (cgState A b x₀ (j + 1)).r ⬝ᵥ (cgState A b x₀ j).p = 0 := by
    rw [← star_star (cgState A b x₀ j).p, Matrix.star_dotProduct_star, h0, star_zero]
  have hp := (cgState_succ_eq A b x₀ j).2.2
  set d : ℝ := ‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
    ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2
  have key : ((‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).p‖ ^ 2 : ℝ) : 𝕜) =
      ((‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 +
        d ^ 2 * ‖WithLp.toLp 2 (cgState A b x₀ j).p‖ ^ 2 : ℝ) : 𝕜) := by
    rw [← EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, hp]
    simp only [star_add, star_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, h0, h0', zero_add,
      EuclideanSpace.star_dotProduct_self_eq_coe_norm_sq, RCLike.star_def, RCLike.conj_ofReal,
      smul_eq_mul]
    push_cast
    ring
  exact_mod_cast key

/-- The quadratic form of the direction update:
$\mathbf{p}_{j+1}^{\mathsf{H}}\mathbf{A}\mathbf{p}_{j+1} =
\mathbf{r}_{j+1}^{\mathsf{H}}\mathbf{A}\mathbf{r}_{j+1} -
\delta_j^2\,\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j$ (conjugacy). -/
private theorem re_quadForm_p_succ {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜) (j : ℕ) :
    RCLike.re (quadForm A (cgState A b x₀ (j + 1)).p) =
      RCLike.re (quadForm A (cgState A b x₀ (j + 1)).r) -
        (‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
          ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2) ^ 2 *
          RCLike.re (quadForm A (cgState A b x₀ j).p) := by
  have hc : star (cgState A b x₀ j).p ⬝ᵥ (A *ᵥ (cgState A b x₀ (j + 1)).p) = 0 :=
    hA.star_cgState_p_dotProduct_mulVec_eq_zero (Nat.lt_succ_self j)
  have hc' : star (cgState A b x₀ (j + 1)).p ⬝ᵥ (A *ᵥ (cgState A b x₀ j).p) = 0 := by
    rw [hA.isHermitian.star_dotProduct_mulVec_comm, hc, star_zero]
  have hp := (cgState_succ_eq A b x₀ j).2.2
  set d : ℝ := ‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
    ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2
  generalize (cgState A b x₀ (j + 1)).p = P at hp hc hc' ⊢
  generalize (cgState A b x₀ (j + 1)).r = R at hp ⊢
  generalize (cgState A b x₀ j).p = p0 at hp hc hc' ⊢
  subst hp
  have key : quadForm A (R + (d : 𝕜) • p0) =
      quadForm A R - ((d ^ 2 : ℝ) : 𝕜) * quadForm A p0 := by
    simp only [quadForm_def, Matrix.mulVec_add, Matrix.mulVec_smul, star_add, star_smul,
      add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      RCLike.star_def, RCLike.conj_ofReal] at hc hc' ⊢
    push_cast
    linear_combination (d : 𝕜) * hc + (d : 𝕜) * hc'
  rw [key, map_sub, RCLike.re_ofReal_mul]

end Identities

/-- Rayleigh bounds from a spectral interval: $a\|\mathbf{x}\|^2 \le
\operatorname{Re}(\mathbf{x}^{\mathsf{H}}\mathbf{A}\mathbf{x}) \le a'\|\mathbf{x}\|^2$. -/
private theorem rayleigh_of_spectrum {A : Matrix n n 𝕜} (hA : A.IsHermitian) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (x : n → 𝕜) :
    a * ‖WithLp.toLp 2 x‖ ^ 2 ≤ RCLike.re (quadForm A x) ∧
      RCLike.re (quadForm A x) ≤ a' * ‖WithLp.toLp 2 x‖ ^ 2 := by
  have hA' : IsSelfAdjoint A := hA
  have h₁ : a • (1 : Matrix n n 𝕜) ≤ A := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (algebraMap_le_iff_le_spectrum hA').mpr fun x hx => (hs hx).1
  have h₂ : A ≤ a' • (1 : Matrix n n 𝕜) := by
    rw [← Algebra.algebraMap_eq_smul_one]
    exact (le_algebraMap_iff_spectrum_le hA').mpr fun x hx => (hs hx).2
  have e₁ := re_quadForm_le_re_quadForm_of_le h₁ x
  have e₂ := re_quadForm_le_re_quadForm_of_le h₂ x
  rw [re_quadForm_real_smul_one] at e₁ e₂
  exact ⟨e₁, e₂⟩

/-- Residual against energy norm: $a\,\mathbf{e}^{\mathsf{H}}\mathbf{A}\mathbf{e} \le
\|\mathbf{A}\mathbf{e}\|^2 \le a'\,\mathbf{e}^{\mathsf{H}}\mathbf{A}\mathbf{e}$, through
$\mathbf{A}^{1/2}$. -/
private theorem rayleigh_sq_of_spectrum {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ}
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (e : n → 𝕜) :
    a * RCLike.re (quadForm A e) ≤ ‖WithLp.toLp 2 (A *ᵥ e)‖ ^ 2 ∧
      ‖WithLp.toLp 2 (A *ᵥ e)‖ ^ 2 ≤ a' * RCLike.re (quadForm A e) := by
  set S := CFC.sqrt A
  have hS : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg
  have h1 : RCLike.re (quadForm A e) = ‖WithLp.toLp 2 (S *ᵥ e)‖ ^ 2 := by
    rw [← RCLike.ofReal_re (K := 𝕜) (‖WithLp.toLp 2 (S *ᵥ e)‖ ^ 2),
      ← quadForm_conjTranspose_mul_self, hS, hSS]
  have h2 : RCLike.re (quadForm A (S *ᵥ e)) = ‖WithLp.toLp 2 (A *ᵥ e)‖ ^ 2 := by
    rw [← quadForm_conjTranspose_mul_mul, hS,
      show S * A * S = Aᴴ * A by rw [hA.isHermitian.eq, ← hSS]; simp only [Matrix.mul_assoc],
      quadForm_conjTranspose_mul_self, RCLike.ofReal_re]
  have := rayleigh_of_spectrum hA.isHermitian hs (S *ᵥ e)
  rw [← h1, h2] at this
  exact this

/-- $\|\mathbf{r}_j\|^2 \le \|\mathbf{p}_j\|^2$. -/
private theorem norm_r_sq_le_norm_p_sq {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜) :
    ∀ j, ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2 ≤ ‖WithLp.toLp 2 (cgState A b x₀ j).p‖ ^ 2
  | 0 => le_rfl
  | j + 1 => by
    rw [norm_p_succ_sq hA b x₀ j]
    have := sq_nonneg (‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
      ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2)
    have := sq_nonneg ‖WithLp.toLp 2 (cgState A b x₀ j).p‖
    nlinarith

/-- $\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j \le
\mathbf{r}_j^{\mathsf{H}}\mathbf{A}\mathbf{r}_j$. -/
private theorem re_quadForm_p_le_r {A : Matrix n n 𝕜} (hA : A.PosDef) (b x₀ : n → 𝕜) :
    ∀ j, RCLike.re (quadForm A (cgState A b x₀ j).p) ≤
      RCLike.re (quadForm A (cgState A b x₀ j).r)
  | 0 => le_rfl
  | j + 1 => by
    rw [re_quadForm_p_succ hA b x₀ j]
    have := hA.posSemidef.re_quadForm_nonneg (cgState A b x₀ j).p
    have := sq_nonneg (‖WithLp.toLp 2 (cgState A b x₀ (j + 1)).r‖ ^ 2 /
      ‖WithLp.toLp 2 (cgState A b x₀ j).r‖ ^ 2)
    nlinarith

/-- The **unit lower bidiagonal factor** $\mathbf{L}_k$: ones on the diagonal and
$\rho_{i+1}/\rho_i$ at $(i + 1, i)$. -/
noncomputable def cgBidiagonal (ρ : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j => if i = j then 1 else if (i : ℕ) = j + 1 then ρ i / ρ j else 0

/-- The **conjugate gradient tridiagonal matrix** of step lengths $\gamma$ and residual norms
$\rho$, indexed from $0$: $\gamma_i^{-1} + (\rho_i/\rho_{i-1})^2\gamma_{i-1}^{-1}$ at $(i, i)$
(the second term for $i \ge 1$), and $\rho_i/(\gamma_{i-1}\rho_{i-1})$ at $(i, i-1)$ and
$(i-1, i)$. -/
noncomputable def cgTridiagonal (γ ρ : ℕ → ℝ) (k : ℕ) : Matrix (Fin k) (Fin k) ℝ :=
  Matrix.of fun i j =>
    if i = j then (γ i)⁻¹ + (if (i : ℕ) = 0 then 0 else (ρ i / ρ (i - 1)) ^ 2 / γ (i - 1))
    else if (i : ℕ) = j + 1 then ρ i / (γ j * ρ j)
    else if (j : ℕ) = i + 1 then ρ j / (γ i * ρ i)
    else 0

/-- The entries of the bidiagonal factor. -/
private theorem cgBidiagonal_apply (ρ : ℕ → ℝ) (k : ℕ) (i l : Fin k) :
    cgBidiagonal ρ k i l = if i = l then 1 else if (i : ℕ) = l + 1 then ρ i / ρ l else 0 :=
  rfl

/-- The bidiagonal factor is unit lower triangular. -/
private theorem isLowerTriangular_cgBidiagonal (ρ : ℕ → ℝ) (k : ℕ) :
    (cgBidiagonal ρ k).IsLowerTriangular := by
  intro i l hil
  have hil' : i < l := OrderDual.toDual_lt_toDual.mp hil
  rw [cgBidiagonal_apply, if_neg (ne_of_lt hil'), if_neg (by rw [Fin.lt_def] at hil'; omega)]

/-- The bidiagonal factor is invertible. -/
private theorem isUnit_cgBidiagonal (ρ : ℕ → ℝ) (k : ℕ) : IsUnit (cgBidiagonal ρ k) := by
  rw [Matrix.isUnit_iff_isUnit_det,
    Matrix.det_of_isLowerTriangular _ (isLowerTriangular_cgBidiagonal ρ k)]
  simp [cgBidiagonal_apply]

/-- The bidiagonal factor applied to a vector:
$(\mathbf{L}_k\mathbf{y})_i = y_i + (\rho_i/\rho_{i-1})y_{i-1}$, the second term for $i \ge 1$. -/
private theorem cgBidiagonal_mulVec_apply (ρ : ℕ → ℝ) (k : ℕ) (y : Fin k → ℝ) (i : Fin k) :
    (cgBidiagonal ρ k *ᵥ y) i =
      y i + if h : (i : ℕ) = 0 then 0 else ρ i / ρ (i - 1) * y ⟨i - 1, by omega⟩ := by
  rw [Matrix.mulVec, dotProduct]
  split_ifs with h
  · rw [add_zero, Finset.sum_eq_single i]
    · rw [cgBidiagonal_apply, if_pos rfl, one_mul]
    · intro l _ hl
      rw [cgBidiagonal_apply, if_neg (Ne.symm hl), if_neg (by omega), zero_mul]
    · simp
  · set i' : Fin k := ⟨i - 1, by omega⟩
    have hii' : i ≠ i' := fun e => by have := congrArg Fin.val e; simp [i'] at this; omega
    rw [Finset.sum_eq_add_of_mem i i' (Finset.mem_univ _) (Finset.mem_univ _) hii']
    · rw [cgBidiagonal_apply, if_pos rfl, one_mul, cgBidiagonal_apply, if_neg hii',
        if_pos (by simp [i']; omega)]
    · intro l _ hl
      rw [cgBidiagonal_apply, if_neg (Ne.symm hl.1),
        if_neg (fun e => hl.2 (Fin.ext (by simp [i']; omega))), zero_mul]

/-- **The factorisation**: `NLAlib.cgTridiagonal γ ρ k` $=
\mathbf{L}_k\operatorname{diag}(\gamma^{-1})\mathbf{L}_k^{\mathsf{T}}$, for any sequences.
[MeurantStrakos2006, §3.1].
Proof: entrywise; the product of bidiagonal factors has three nonzero diagonals.
Difficulty: easy. -/
theorem cgTridiagonal_eq_mul (γ ρ : ℕ → ℝ) (k : ℕ) :
    cgTridiagonal γ ρ k =
      cgBidiagonal ρ k * Matrix.diagonal (fun i : Fin k => (γ i)⁻¹) * (cgBidiagonal ρ k)ᵀ := by
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  have hL := cgBidiagonal_apply ρ k
  simp only [cgTridiagonal, Matrix.of_apply]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl]
    by_cases h0 : (i : ℕ) = 0
    · rw [if_pos h0, add_zero, Finset.sum_eq_single i]
      · rw [hL, if_pos rfl]; ring
      · intro l _ hl
        rw [hL, if_neg (Ne.symm hl), if_neg (by omega)]; ring
      · simp
    · rw [if_neg h0]
      set i' : Fin k := ⟨i - 1, by omega⟩
      have hii' : i ≠ i' := fun e => by have := congrArg Fin.val e; simp [i'] at this; omega
      rw [Finset.sum_eq_add_of_mem i i' (Finset.mem_univ _) (Finset.mem_univ _) hii']
      · rw [hL, if_pos rfl, hL, if_neg hii', if_pos (by simp [i']; omega)]
        simp only [i']
        ring
      · intro l _ hl
        rw [hL, if_neg (Ne.symm hl.1),
          if_neg (fun e => hl.2 (Fin.ext (by simp [i']; omega)))]; ring
  · rw [if_neg hij]
    by_cases h1 : (i : ℕ) = j + 1
    · rw [if_pos h1, Finset.sum_eq_single j]
      · rw [hL, if_neg hij, if_pos h1, hL, if_pos rfl]; ring
      · intro l _ hl
        rw [hL j l, if_neg (Ne.symm hl)]
        by_cases h2 : (j : ℕ) = l + 1
        · rw [hL i l, if_neg (fun e => by rw [← e] at h2; omega), if_neg (by omega)]; ring
        · rw [if_neg h2]; ring
      · simp
    · rw [if_neg h1]
      by_cases h2 : (j : ℕ) = i + 1
      · rw [if_pos h2, Finset.sum_eq_single i]
        · rw [hL, if_pos rfl, hL, if_neg (Ne.symm hij), if_pos h2]; ring
        · intro l _ hl
          have n1 : ¬ i = l := Ne.symm hl
          by_cases h3 : (i : ℕ) = l + 1
          · have n2 : ¬ j = l := fun e => by subst e; omega
            have n3 : ¬ (j : ℕ) = l + 1 := by omega
            rw [hL i l, hL j l, if_neg n1, if_neg n2, if_neg n3]; ring
          · rw [hL i l, if_neg n1, if_neg h3]; ring
        · simp
      · rw [if_neg h2]
        refine (Finset.sum_eq_zero fun l _ => ?_).symm
        have hij' : (i : ℕ) ≠ j := fun e => hij (Fin.ext e)
        rw [hL i l, hL j l]
        by_cases a1 : i = l
        · subst a1
          have n1 : ¬ j = i := Ne.symm hij
          have n2 : ¬ (j : ℕ) = i + 1 := h2
          rw [if_neg n1, if_neg n2]; ring
        · rw [if_neg a1]
          by_cases a2 : (i : ℕ) = l + 1
          · have n1 : ¬ j = l := fun e => by subst e; omega
            have n2 : ¬ (j : ℕ) = l + 1 := by omega
            rw [if_neg n1, if_neg n2]; ring
          · rw [if_neg a2]; ring

/-- The conjugate gradient tridiagonal matrix of positive step lengths is positive definite.
Proof: `cgTridiagonal_eq_mul`; the unit triangular factor is invertible, so the congruence of a
positive diagonal matrix is positive definite. Difficulty: easy. -/
theorem posDef_cgTridiagonal {γ : ℕ → ℝ} (ρ : ℕ → ℝ) {k : ℕ} (hγ : ∀ i < k, 0 < γ i) :
    (cgTridiagonal γ ρ k).PosDef := by
  rw [cgTridiagonal_eq_mul]
  have hD : (Matrix.diagonal fun i : Fin k => (γ i)⁻¹).PosDef :=
    Matrix.posDef_diagonal_iff.mpr fun i => inv_pos.mpr (hγ i i.2)
  have h := hD.mul_mul_conjTranspose_same
    (B := cgBidiagonal ρ k) (Matrix.vecMul_injective_iff_isUnit.mpr (isUnit_cgBidiagonal ρ k))
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- **The Gauss quadrature value of the coefficients**: for positive step lengths and nonzero
residual norms,
$\rho_0^2\,(\mathbf{T}_{k+1}^{-1})_{00} = \sum_{i \le k}\gamma_i\rho_i^2$.
[MeurantStrakos2006, §3.3]; [StrakosTichy2002, (4.4)].
Proof: $\mathbf{T}^{-1} = \mathbf{L}^{-\mathsf{T}}\operatorname{diag}(\gamma)\mathbf{L}^{-1}$ and
$\mathbf{L}^{-1}\mathbf{e}_0 = ((-1)^i\rho_i/\rho_0)_i$ (forward substitution).
Difficulty: easy. -/
theorem sq_mul_inv_cgTridiagonal_zero_zero {γ ρ : ℕ → ℝ} {k : ℕ} (hγ : ∀ i ≤ k, 0 < γ i)
    (hρ : ∀ i ≤ k, ρ i ≠ 0) :
    ρ 0 ^ 2 * (cgTridiagonal γ ρ (k + 1))⁻¹ 0 0 = ∑ i ∈ Finset.range (k + 1), γ i * ρ i ^ 2 := by
  set L := cgBidiagonal ρ (k + 1)
  have hLu := isUnit_cgBidiagonal ρ (k + 1)
  have hLd : IsUnit L.det := (Matrix.isUnit_iff_isUnit_det L).mp hLu
  set y : Fin (k + 1) → ℝ := fun i => (-1) ^ (i : ℕ) * (ρ i / ρ 0)
  have hρ0 : ρ 0 ≠ 0 := hρ 0 (Nat.zero_le _)
  have hLy : L *ᵥ y = Pi.single 0 1 := by
    funext i
    rw [cgBidiagonal_mulVec_apply]
    split_ifs with h
    · have hi : i = 0 := Fin.ext h
      subst hi
      simp [y, hρ0]
    · have hi : i ≠ 0 := fun e => h (by rw [e]; rfl)
      rw [Pi.single_eq_of_ne hi]
      have hi1 : ρ (i - 1) ≠ 0 := hρ _ (by omega)
      obtain ⟨m, hm⟩ : ∃ m, (i : ℕ) = m + 1 := ⟨i - 1, by omega⟩
      have hm1 : ρ m ≠ 0 := by rwa [hm, Nat.add_sub_cancel] at hi1
      simp only [y, hm, Nat.add_sub_cancel, pow_succ]
      field_simp
      ring
  have hy : ∀ a, L⁻¹ a 0 = y a := fun a => by
    have h := congrArg (L⁻¹ *ᵥ ·) hLy
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hLd, Matrix.one_mulVec] at h
    rw [h]
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hD : (Matrix.diagonal fun i : Fin (k + 1) => (γ i)⁻¹)⁻¹ =
      Matrix.diagonal fun i : Fin (k + 1) => γ i := by
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact mul_inv_cancel₀ (hγ i (by omega)).ne'
  rw [cgTridiagonal_eq_mul, Matrix.mul_inv_rev, Matrix.mul_inv_rev, hD,
    ← Matrix.transpose_nonsing_inv, Matrix.mul_apply]
  simp only [Matrix.transpose_apply, Matrix.diagonal_mul]
  rw [show (cgBidiagonal ρ (k + 1))⁻¹ = L⁻¹ from rfl]
  simp only [hy]
  rw [Finset.mul_sum, ← Fin.sum_univ_eq_sum_range (fun i => γ i * ρ i ^ 2)]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [y]
  field_simp
  rw [← pow_mul, mul_comm (a : ℕ) 2, pow_mul]
  norm_num

omit [DecidableEq n] in
/-- **Exact CG computes the Lanczos tridiagonal matrix** (the CG–Lanczos correspondence): for
positive definite real $\mathbf{A}$ and residuals $\mathbf{r}_j \ne \mathbf{0}$, $j < k$, of CG
from $\mathbf{x}_0 = \mathbf{0}$,
`NLAlib.lanczosTridiagonal A b k` $=$ `NLAlib.cgTridiagonal` of the step lengths and residual
norms. [MeurantStrakos2006, §3.1]; [HestenesStiefel1952, §18].
Proof: the vectors $(-1)^j\mathbf{r}_j/\|\mathbf{r}_j\|$ are orthonormal
(`Matrix.PosDef.star_cgState_r_dotProduct_eq_zero`) and satisfy the three-term recurrence with
the entries of `cgTridiagonal` (eliminate $\mathbf{p}$ from the two updates), so
`NLAlib.lanczosState_eq_of_orthonormal_recurrence` identifies them with the Lanczos vectors.
Difficulty: moderate. -/
theorem _root_.Matrix.PosDef.lanczosTridiagonal_eq_cgTridiagonal
    {A : Matrix n n ℝ} (hA : A.PosDef) (b : n → ℝ) (k : ℕ)
    (hr : ∀ j < k, (cgState A b 0 j).r ≠ 0) :
    lanczosTridiagonal A b k = cgTridiagonal (fun j => cgAlpha A (cgState A b 0 j))
      (fun j => ‖WithLp.toLp 2 (cgState A b 0 j).r‖) k := by
  sorry

omit [DecidableEq n] in
/-- **Exact Lanczos data determine the CG step lengths**: if exact Lanczos on a positive
definite $\mathbf{A}$ from $\mathbf{b}$ computes `NLAlib.cgTridiagonal γ ρ k` and the last
coefficient $\beta_k = \rho_k/(\gamma_{k-1}\rho_{k-1})$, with $\gamma_j > 0$, $\rho_j > 0$
($j < k$) and $\rho_0 = \|\mathbf{b}\|$, then exact CG on $(\mathbf{A}, \mathbf{b})$ from
$\mathbf{0}$ has step lengths $\gamma_j$, $j < k$.
Proof: induction on $j$; at each step $\mathbf{r}_j \ne \mathbf{0}$ (else the Lanczos recurrence
has broken down, contradicting $\beta_j > 0$),
`Matrix.PosDef.lanczosTridiagonal_eq_cgTridiagonal` at $j + 1$, and uniqueness of the
$\mathbf{L}\mathbf{D}\mathbf{L}^{\mathsf{T}}$ factorisation: the pivots of
`NLAlib.cgTridiagonal` are read off by elimination, $D_0 = T_{00}$,
$D_{i+1} = T_{i+1,i+1} - T_{i+1,i}^2/D_i$. Difficulty: moderate. -/
theorem _root_.Matrix.PosDef.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq
    {A : Matrix n n ℝ} (hA : A.PosDef) {b : n → ℝ} {γ ρ : ℕ → ℝ} {k : ℕ} (hk : 0 < k)
    (hT : lanczosTridiagonal A b k = cgTridiagonal γ ρ k)
    (hβ : (lanczosState A b k).beta = ρ k / (γ (k - 1) * ρ (k - 1)))
    (hγ : ∀ j < k, 0 < γ j) (hρ : ∀ j < k, 0 < ρ j) (hρ0 : ρ 0 = ‖WithLp.toLp 2 b‖)
    {j : ℕ} (hj : j < k) :
    cgAlpha A (cgState A b 0 j) = γ j := by
  sorry

omit [DecidableEq n] in
/-- **Exact Lanczos data determine the CG residual norms**: under the hypotheses of
`Matrix.PosDef.cgAlpha_cgState_eq_of_lanczosTridiagonal_eq`, exact CG has residual norms
$\|\mathbf{r}_j\| = \rho_j$ for $j \le k$ (the last one from $\beta_k$).
Proof: the same induction; $\|\mathbf{r}_{j+1}\| = \gamma_j\rho_j\beta_{j+1}$ in exact CG.
Difficulty: moderate (shares the induction). -/
theorem _root_.Matrix.PosDef.norm_cgState_r_eq_of_lanczosTridiagonal_eq
    {A : Matrix n n ℝ} (hA : A.PosDef) {b : n → ℝ} {γ ρ : ℕ → ℝ} {k : ℕ} (hk : 0 < k)
    (hT : lanczosTridiagonal A b k = cgTridiagonal γ ρ k)
    (hβ : (lanczosState A b k).beta = ρ k / (γ (k - 1) * ρ (k - 1)))
    (hγ : ∀ j < k, 0 < γ j) (hρ : ∀ j < k, 0 < ρ j) (hρ0 : ρ 0 = ‖WithLp.toLp 2 b‖)
    {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (cgState A b 0 j).r‖ = ρ j := by
  sorry

/-- **The decrease of the $\mathbf{A}$-norm error** in one CG step: for positive definite
$\mathbf{A}$ and $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 -
\|\mathbf{x}_\star - \mathbf{x}_{j+1}\|_{\mathbf{A}}^2 = \gamma_j\|\mathbf{r}_j\|^2$.
[HestenesStiefel1952, Theorem 6:1]; [StrakosTichy2002, (4.4)].
Proof: $\mathbf{e}_{j+1} = \mathbf{e}_j - \gamma_j\mathbf{p}_j$,
$\mathbf{A}\mathbf{e}_j = \mathbf{r}_j$,
$\mathbf{p}_j^{\mathsf{H}}\mathbf{r}_j = \|\mathbf{r}_j\|^2$ (`CGRecurrence.lean`, private
`star_p_dotProduct_r`, to be made public) and
$\gamma_j\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j
= \|\mathbf{r}_j\|^2$; with `Matrix.PosDef.cgState_x_eq`. Difficulty: easy. -/
theorem _root_.Matrix.PosDef.re_quadForm_sub_cgIterate_sub_re_quadForm_sub_cgIterate_succ
    {A : Matrix n n 𝕜} (hA : A.PosDef) {b xs : n → 𝕜} (hxs : A *ᵥ xs = b) (j : ℕ) :
    RCLike.re (quadForm A (xs - cgIterate A b 0 j)) -
        RCLike.re (quadForm A (xs - cgIterate A b 0 (j + 1))) =
      cgAlpha A (cgState A b 0 j) * ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 := by
  rw [← hA.cgState_x_eq b 0 j, ← hA.cgState_x_eq b 0 (j + 1), (cgState_succ_eq A b 0 j).1]
  set s := cgState A b 0 j with hs
  set c := cgAlpha A s
  set ρ := ‖WithLp.toLp 2 s.r‖ ^ 2
  set Q := RCLike.re (quadForm A s.p)
  have hAe : A *ᵥ (xs - s.x) = s.r := by rw [Matrix.mulVec_sub, hxs, hs, cgState_r_eq]
  have hpr : star s.p ⬝ᵥ s.r = (ρ : 𝕜) := star_p_dotProduct_r hA b 0 j
  have hquad : star s.p ⬝ᵥ (A *ᵥ s.p) = (Q : 𝕜) := (hA.isHermitian.coe_re_quadForm _).symm
  have hrp : star (xs - s.x) ⬝ᵥ (A *ᵥ s.p) = (ρ : 𝕜) := by
    rw [hA.isHermitian.star_dotProduct_mulVec_comm, hAe, hpr, RCLike.star_def,
      RCLike.conj_ofReal]
  rw [show xs - (s.x + (c : 𝕜) • s.p) = (xs - s.x) - (c : 𝕜) • s.p by abel]
  generalize xs - s.x = e at hAe hrp ⊢
  have key : quadForm A (e - (c : 𝕜) • s.p) =
      quadForm A e - ((2 * c * ρ - c ^ 2 * Q : ℝ) : 𝕜) := by
    simp only [quadForm_def, Matrix.mulVec_sub, Matrix.mulVec_smul, star_sub, star_smul,
      sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      RCLike.star_def, RCLike.conj_ofReal, hAe, hpr, hrp, hquad]
    push_cast
    ring
  have hcQ : c * (c * Q) = c * ρ := by
    by_cases hQ : Q = 0
    · have : c = 0 := by simp only [c, cgAlpha]; rw [show RCLike.re (quadForm A s.p) = Q from rfl,
        hQ, div_zero]
      rw [this, zero_mul, zero_mul]
    · rw [show c * Q = ρ from div_mul_cancel₀ _ hQ]
  rw [key, map_sub, RCLike.ofReal_re]
  linear_combination -hcQ

/-- **Residual ratios of exact CG** (E1): for spectrum in $[a, a']$, $a > 0$, and $i \le j$,
$\|\mathbf{r}_j\| \le \sqrt{a'/a}\,\|\mathbf{r}_i\|$.
[StrakosTichy2002, (7.20)] (there for finite precision, by an imported monotonicity).
Proof: $a\|\mathbf{e}\|_{\mathbf{A}}^2 \le \|\mathbf{r}\|^2 \le a'\|\mathbf{e}\|_{\mathbf{A}}^2$
(Rayleigh) and the monotonicity of the error (`Matrix.PosDef.isMinOn_cgIterate` over nested
Krylov spaces). Difficulty: easy. -/
theorem _root_.Matrix.PosDef.norm_cgState_r_le {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) {i j : ℕ} (hij : i ≤ j) :
    ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ≤
      Real.sqrt (a' / a) * ‖WithLp.toLp 2 (cgState A b 0 i).r‖ := by
  set xs := A⁻¹ *ᵥ b
  have hxs : A *ᵥ xs = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hA.isUnit), Matrix.one_mulVec]
  set E : ℕ → ℝ := fun m => RCLike.re (quadForm A (xs - cgIterate A b 0 m))
  have hE : Antitone E := antitone_nat_of_succ_le fun m => by
    have h := hA.re_quadForm_sub_cgIterate_sub_re_quadForm_sub_cgIterate_succ hxs m
    have := cgAlpha_nonneg hA (cgState A b 0 m)
    have : 0 ≤ cgAlpha A (cgState A b 0 m) * ‖WithLp.toLp 2 (cgState A b 0 m).r‖ ^ 2 := by
      positivity
    simp only [E]
    linarith
  have hr : ∀ m, (cgState A b 0 m).r = A *ᵥ (xs - cgIterate A b 0 m) := fun m => by
    rw [Matrix.mulVec_sub, hxs, ← hA.cgState_x_eq, cgState_r_eq]
  by_cases hrj : (cgState A b 0 j).r = 0
  · rw [hrj, WithLp.toLp_zero, norm_zero]
    positivity
  obtain ⟨hj1, hj2⟩ := rayleigh_sq_of_spectrum hA hs (xs - cgIterate A b 0 j)
  obtain ⟨hi1, hi2⟩ := rayleigh_sq_of_spectrum hA hs (xs - cgIterate A b 0 i)
  rw [← hr] at hj1 hj2 hi1 hi2
  have hEij := hE hij
  simp only [E] at hEij
  have hEj : 0 < RCLike.re (quadForm A (xs - cgIterate A b 0 j)) := by
    refine hA.re_quadForm_pos fun h0 => hrj ?_
    rw [hr, h0, Matrix.mulVec_zero]
  have hrj2 : 0 < ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 := by
    have : WithLp.toLp 2 (cgState A b 0 j).r ≠ 0 := by simpa using hrj
    positivity
  have haa : 0 ≤ a' := by nlinarith
  have hai : 0 ≤ a' / a := div_nonneg haa ha.le
  have hsq : ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 ≤
      a' / a * ‖WithLp.toLp 2 (cgState A b 0 i).r‖ ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ ha]
    have e1 := mul_le_mul_of_nonneg_left hj2 ha.le
    have e2 := mul_le_mul_of_nonneg_left hEij (mul_nonneg ha.le haa)
    have e3 := mul_le_mul_of_nonneg_left hi1 haa
    nlinarith
  calc ‖WithLp.toLp 2 (cgState A b 0 j).r‖
      = Real.sqrt (‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (a' / a * ‖WithLp.toLp 2 (cgState A b 0 i).r‖ ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (a' / a) * ‖WithLp.toLp 2 (cgState A b 0 i).r‖ := by
      rw [Real.sqrt_mul hai, Real.sqrt_sq (norm_nonneg _)]

/-- **The direction norm of exact CG** [HestenesStiefel1952, Theorem 5:5]: for positive definite
$\mathbf{A}$,
$$\|\mathbf{p}_j\|^2 = \|\mathbf{r}_j\|^4\sum_{i \le j}\|\mathbf{r}_i\|^{-2} .$$
No hypothesis on the residuals: once $\mathbf{r}_i = \mathbf{0}$ the later residuals and
directions vanish (the step length and the coefficient are $0$ in `NLAlib.cgStep`), and both
sides are $0$. With (E2) it bounds the residual ratios of a positive definite CG run,
$\sum_{i \le j}\|\mathbf{r}_j\|^2/\|\mathbf{r}_i\|^2 \le a'/a$: the step (P) of the a priori
analysis of finite-precision CG, applied to exact CG on the backward model (design note §7).
Proof: $\mathbf{p}_j = \mathbf{r}_j + \delta_{j-1}\mathbf{p}_{j-1}$ with
$\delta_{j-1} = \|\mathbf{r}_j\|^2/\|\mathbf{r}_{j-1}\|^2$ and
$\mathbf{p}_{j-1}^{\mathsf{H}}\mathbf{r}_j = 0$ (the line search,
`Matrix.PosDef.star_cgState_r_dotProduct_eq_zero` with the direction update) give
$\|\mathbf{p}_j\|^2 = \|\mathbf{r}_j\|^2 + \delta_{j-1}^2\|\mathbf{p}_{j-1}\|^2$; induct on $j$.
Difficulty: easy. -/
theorem _root_.Matrix.PosDef.norm_cgState_p_sq_eq {A : Matrix n n 𝕜} (hA : A.PosDef)
    (b : n → 𝕜) (j : ℕ) :
    ‖WithLp.toLp 2 (cgState A b 0 j).p‖ ^ 2 = ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 4 *
      ∑ i ∈ Finset.range (j + 1), (‖WithLp.toLp 2 (cgState A b 0 i).r‖ ^ 2)⁻¹ := by
  induction j with
  | zero =>
    rw [Finset.sum_range_one]
    change ‖WithLp.toLp 2 (cgState A b 0 0).r‖ ^ 2 = _
    by_cases h0 : ‖WithLp.toLp 2 (cgState A b 0 0).r‖ = 0
    · rw [h0]; ring
    · field_simp
  | succ j ih =>
    rw [norm_p_succ_sq hA b 0 j, ih, Finset.sum_range_succ _ (j + 1)]
    set S := ∑ i ∈ Finset.range (j + 1), (‖WithLp.toLp 2 (cgState A b 0 i).r‖ ^ 2)⁻¹
    by_cases hr : (cgState A b 0 j).r = 0
    · have h1 := (cgState_succ_of_r_eq_zero A b 0 hr).1
      simp [hr, h1]
    have hρ : ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ≠ 0 := by simpa using hr
    clear_value S
    by_cases hr' : ‖WithLp.toLp 2 (cgState A b 0 (j + 1)).r‖ = 0
    · rw [hr']; ring
    · field_simp
      ring

/-- **Directions against residuals** (E2): for spectrum in $[a, a']$, $a > 0$,
$\|\mathbf{p}_j\|^2 \le (a'/a)\|\mathbf{r}_j\|^2$ (with
`Matrix.PosDef.norm_cgState_p_sq_eq`, a bound on the residual ratios).
Proof: by conjugacy $\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j =
\mathbf{r}_j^{\mathsf{H}}\mathbf{A}\mathbf{r}_j - \delta_{j-1}^2\mathbf{p}_{j-1}^{\mathsf{H}}
\mathbf{A}\mathbf{p}_{j-1} \le a'\|\mathbf{r}_j\|^2$ and $a\|\mathbf{p}_j\|^2 \le
\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j$
(`Matrix.PosDef.star_cgState_p_dotProduct_mulVec_eq_zero`).
Difficulty: easy. -/
theorem _root_.Matrix.PosDef.norm_cgState_p_sq_le {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) (j : ℕ) :
    ‖WithLp.toLp 2 (cgState A b 0 j).p‖ ^ 2 ≤ a' / a * ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 := by
  have h1 := (rayleigh_of_spectrum hA.isHermitian hs (cgState A b 0 j).p).1
  have h2 := (rayleigh_of_spectrum hA.isHermitian hs (cgState A b 0 j).r).2
  have h3 := re_quadForm_p_le_r hA b 0 j
  rw [div_mul_eq_mul_div, le_div_iff₀ ha]
  linarith

/-- **Step lengths of exact CG** (E3, first half): for spectrum in $[a, a']$, $a > 0$,
$\gamma_j \le 1/a$. Proof: $\|\mathbf{p}_j\| \ge \|\mathbf{r}_j\|$ ($\mathbf{r}_j \perp
\mathbf{p}_{j-1}$) and $\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j \ge a\|\mathbf{p}_j\|^2$.
Difficulty: easy. -/
theorem _root_.Matrix.PosDef.cgAlpha_le {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) (j : ℕ) :
    cgAlpha A (cgState A b 0 j) ≤ 1 / a := by
  by_cases hr : (cgState A b 0 j).r = 0
  · have : cgAlpha A (cgState A b 0 j) = 0 := by simp [cgAlpha, hr]
    rw [this]
    positivity
  obtain ⟨hγQ, hQ⟩ := cgAlpha_mul_re_quadForm hA b 0 hr
  have hρ : 0 < ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 := by
    have : WithLp.toLp 2 (cgState A b 0 j).r ≠ 0 := by simpa using hr
    positivity
  have h1 := (rayleigh_of_spectrum hA.isHermitian hs (cgState A b 0 j).p).1
  have h2 := norm_r_sq_le_norm_p_sq hA b 0 j
  have hγ := cgAlpha_nonneg hA (cgState A b 0 j)
  rw [le_div_iff₀ ha]
  -- γ a ρ ≤ γ Q = ρ
  have : cgAlpha A (cgState A b 0 j) * (a * ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2) ≤
      ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 := by
    rw [← hγQ]
    exact mul_le_mul_of_nonneg_left (by nlinarith) hγ
  nlinarith

/-- **The coefficient ratio of exact CG** (E3, second half): for spectrum in $[a, a']$,
$\delta_j/\gamma_j = \|\mathbf{r}_{j+1}\|^2/(\gamma_j\|\mathbf{r}_j\|^2) \le a'$, written without
division by $\gamma_j$.
Proof: $\delta_j^2\,\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j \le
\mathbf{r}_{j+1}^{\mathsf{H}}\mathbf{A}\mathbf{r}_{j+1} \le a'\|\mathbf{r}_{j+1}\|^2$ (conjugacy,
as in `Matrix.PosDef.norm_cgState_p_sq_le`) and
$\gamma_j\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j = \|\mathbf{r}_j\|^2$.
Difficulty: easy. -/
theorem _root_.Matrix.PosDef.norm_cgState_r_succ_sq_div_le {A : Matrix n n 𝕜} (hA : A.PosDef)
    {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) (j : ℕ) :
    ‖WithLp.toLp 2 (cgState A b 0 (j + 1)).r‖ ^ 2 ≤
      a' * cgAlpha A (cgState A b 0 j) * ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 := by
  by_cases hr : (cgState A b 0 j).r = 0
  · rw [(cgState_succ_of_r_eq_zero A b 0 hr).1, hr]
    simp
  obtain ⟨hγQ, hQ⟩ := cgAlpha_mul_re_quadForm hA b 0 hr
  set ρ := ‖WithLp.toLp 2 (cgState A b 0 j).r‖ ^ 2 with hρdef
  set ρ' := ‖WithLp.toLp 2 (cgState A b 0 (j + 1)).r‖ ^ 2 with hρ'def
  set Q := RCLike.re (quadForm A (cgState A b 0 j).p)
  set γ := cgAlpha A (cgState A b 0 j)
  have hρ : 0 < ρ := by
    have : WithLp.toLp 2 (cgState A b 0 j).r ≠ 0 := by simpa using hr
    positivity
  have hρ' : 0 ≤ ρ' := by positivity
  have hp0 : 0 < ‖WithLp.toLp 2 (cgState A b 0 j).p‖ ^ 2 := by
    have : WithLp.toLp 2 (cgState A b 0 j).p ≠ 0 := by simpa using p_ne_zero hA b 0 hr
    positivity
  have haa : a ≤ a' := by
    obtain ⟨e1, e2⟩ := rayleigh_of_spectrum hA.isHermitian hs (cgState A b 0 j).p
    nlinarith
  have hq := re_quadForm_p_succ hA b 0 j
  have hpp := hA.posSemidef.re_quadForm_nonneg (cgState A b 0 (j + 1)).p
  have hrr := (rayleigh_of_spectrum hA.isHermitian hs (cgState A b 0 (j + 1)).r).2
  -- (ρ'/ρ)² Q ≤ a' ρ'
  have hmain : (ρ' / ρ) ^ 2 * Q ≤ a' * ρ' := by linarith
  have hγ : γ = ρ / Q := rfl
  rw [hγ]
  rw [div_pow, div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hmain
  have ha' : 0 ≤ a' := by linarith
  have hgoal : ρ' * Q ≤ a' * ρ * ρ := by
    rcases hρ'.eq_or_lt with h | h
    · rw [← h, zero_mul]; positivity
    · refine le_of_mul_le_mul_left ?_ h
      nlinarith
  calc ρ' = ρ' * Q / Q := by field_simp
    _ ≤ a' * ρ * ρ / Q := div_le_div_of_nonneg_right hgoal hQ.le
    _ = a' * (ρ / Q) * ρ := by ring

end NLAlib
