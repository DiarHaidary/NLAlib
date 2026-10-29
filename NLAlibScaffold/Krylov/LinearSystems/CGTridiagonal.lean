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

open scoped Matrix ComplexOrder

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

/-- **The factorisation**: `NLAlib.cgTridiagonal γ ρ k` $=
\mathbf{L}_k\operatorname{diag}(\gamma^{-1})\mathbf{L}_k^{\mathsf{T}}$, for any sequences.
[MeurantStrakos2006, §3.1].
Proof: entrywise; the product of bidiagonal factors has three nonzero diagonals.
Difficulty: easy. -/
theorem cgTridiagonal_eq_mul (γ ρ : ℕ → ℝ) (k : ℕ) :
    cgTridiagonal γ ρ k =
      cgBidiagonal ρ k * Matrix.diagonal (fun i : Fin k => (γ i)⁻¹) * (cgBidiagonal ρ k)ᵀ := by
  sorry

/-- The conjugate gradient tridiagonal matrix of positive step lengths is positive definite.
Proof: `cgTridiagonal_eq_mul`; the unit triangular factor is invertible, so the congruence of a
positive diagonal matrix is positive definite. Difficulty: easy. -/
theorem posDef_cgTridiagonal {γ : ℕ → ℝ} (ρ : ℕ → ℝ) {k : ℕ} (hγ : ∀ i < k, 0 < γ i) :
    (cgTridiagonal γ ρ k).PosDef := by
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- **Step lengths of exact CG** (E3, first half): for spectrum in $[a, a']$, $a > 0$,
$\gamma_j \le 1/a$. Proof: $\|\mathbf{p}_j\| \ge \|\mathbf{r}_j\|$ ($\mathbf{r}_j \perp
\mathbf{p}_{j-1}$) and $\mathbf{p}_j^{\mathsf{H}}\mathbf{A}\mathbf{p}_j \ge a\|\mathbf{p}_j\|^2$.
Difficulty: easy. -/
theorem _root_.Matrix.PosDef.cgAlpha_le {A : Matrix n n 𝕜} (hA : A.PosDef) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (b : n → 𝕜) (j : ℕ) :
    cgAlpha A (cgState A b 0 j) ≤ 1 / a := by
  sorry

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
  sorry

end NLAlib
