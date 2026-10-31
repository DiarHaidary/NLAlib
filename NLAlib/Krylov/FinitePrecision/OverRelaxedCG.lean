/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.FinitePrecision.CGRun

/-!
# Over-relaxed conjugate gradients: an admissible run that does not converge

The rounding pattern $\theta_j = \eta^\gamma_j = \varepsilon$ (relative error $+\varepsilon$ in
the computed $\|\mathbf{r}_j\|^2$ and in the division $\nu_j/\mu_j$, every other operation exact)
is admissible in the standard model. Under it the run is exact CG with every step length
multiplied by $c = (1 + \varepsilon)^2$, **over-relaxed CG** (`NLAlib.overRelaxedCG`), and its
data satisfy, exactly, with $\rho_j = \|\mathbf{r}_j\|$,
$$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j = \bigl(1 - j(c - 1)\bigr)\rho_j^2,\qquad
\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 - \|\mathbf{x}_\star -
\mathbf{x}_{j+1}\|_{\mathbf{A}}^2 = \gamma_j\rho_j^2\bigl(1 - (2j + 1)(c - 1)\bigr) :$$
the line search defect drifts linearly and is never damped, and for
$(2j + 1)(c - 1) \ge 1$, i.e. $j \gtrsim 1/(4\varepsilon)$, the $\mathbf{A}$-norm error
increases at every step. So the updated residual is bounded away from zero
(`NLAlib.overRelaxedCG_exists_pos_le_norm_r`), independently of $\kappa$ and $n$: every
convergence theorem for HSCG in the standard model needs a hypothesis $k\varepsilon \le c_0$
with $c_0 < 1/4$, and a $k$-uniform backward model is impossible in the worst case.

**Realization.** `NLAlib.overRelaxedCGRun` realizes the first $k$ steps as an
`NLAlib.CGRun` (the analysis interface) whenever $k\varepsilon \le 1/100$; the interface carries
that bound as a field, so the non-convergent regime $j > 1/(4\varepsilon)$ is outside every
`NLAlib.CGRun`. A realization at the level of the program `NLAlib.cgProg` under a value
semantics meeting `NLAlib.Computation.IsRelErrSem` is **not** proved here. What it needs: (1) a
semantics producing the pattern, for which a `NLAlib.Computation.ScalarSem` over $\mathbb{R}$
does not suffice (it sees only the operand values, not which dot product or division it
evaluates; perturbing the products with equal operands $x \cdot x$ is admissible but can
coincide with other products of the run) while a carrier of words that record their history
(terms, decoded by evaluation) does: $\mathrm{fl}(x \cdot x) = x^2(1 + \varepsilon)$ for
syntactically equal operands, exact otherwise, gives $\theta_j = \varepsilon$,
$\eta^\gamma_j = 0$, i.e. $c = 1 + \varepsilon$; (2) the execution of `NLAlib.cgProg` under that
semantics for $q$ steps, a re-run of the proof of `NLAlib.exec_cgProg_exactInterp` with the
perturbed dot product.


## Main definitions

* `NLAlib.overRelaxedCGAlpha`, `NLAlib.overRelaxedCGStep`, `NLAlib.overRelaxedCG`.

## Main results

* `NLAlib.overRelaxedCG_p_dotProduct_r`: the linear drift of the line search defect.
* `NLAlib.quadForm_sub_overRelaxedCG_sub_quadForm_sub_overRelaxedCG_succ`: the
  $\mathbf{A}$-norm decrement.
* `NLAlib.quadForm_sub_overRelaxedCG_le_of_le`: no decrease past $1/(4\varepsilon)$.
* `NLAlib.overRelaxedCG_exists_pos_le_norm_r`: no convergence.
* `NLAlib.overRelaxedCGRun`: the admissible run.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- The **over-relaxed step length** of a state $s$:
$c\,\mathbf{r}^{\mathsf{T}}\mathbf{r}/\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$ ($c = 1$ is
`NLAlib.cgAlpha`). -/
noncomputable def overRelaxedCGAlpha (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (s : CGState ℝ (Fin n)) : ℝ :=
  c * (s.r ⬝ᵥ s.r) / (s.p ⬝ᵥ (A *ᵥ s.p))

/-- **One over-relaxed CG step**: `NLAlib.cgStep` with the step length multiplied by $c$,
$$\mathbf{x}' = \mathbf{x} + \gamma\mathbf{p},\quad \mathbf{r}' = \mathbf{r} -
\gamma\mathbf{A}\mathbf{p},\quad \mathbf{p}' = \mathbf{r}' +
\frac{\mathbf{r}'^{\mathsf{T}}\mathbf{r}'}{\mathbf{r}^{\mathsf{T}}\mathbf{r}}\mathbf{p},\qquad
\gamma = \frac{c\,\mathbf{r}^{\mathsf{T}}\mathbf{r}}{\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}}
\,.$$ -/
noncomputable def overRelaxedCGStep (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ)
    (s : CGState ℝ (Fin n)) : CGState ℝ (Fin n) :=
  let γ := overRelaxedCGAlpha A c s
  let r' := s.r - γ • (A *ᵥ s.p)
  ⟨s.x + γ • s.p, r', r' + ((r' ⬝ᵥ r') / (s.r ⬝ᵥ s.r)) • s.p⟩

/-- **Over-relaxed CG** from $\mathbf{x}_0 = \mathbf{0}$, $\mathbf{r}_0 = \mathbf{p}_0 =
\mathbf{b}$: the state after $j$ steps of `NLAlib.overRelaxedCGStep`. For
$c = (1 + \varepsilon)^2$ it is the HSCG run with the admissible rounding pattern
$\theta_j = \eta^\gamma_j = \varepsilon$ (`NLAlib.overRelaxedCGRun`). -/
noncomputable def overRelaxedCG (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ) :
    ℕ → CGState ℝ (Fin n)
  | 0 => ⟨0, b, b⟩
  | j + 1 => overRelaxedCGStep A c (overRelaxedCG A b c j)

variable {A : Matrix (Fin n) (Fin n) ℝ} {b : Fin n → ℝ} {c : ℝ}

private theorem orcg_x_succ (j : ℕ) : (overRelaxedCG A b c (j + 1)).x =
    (overRelaxedCG A b c j).x + overRelaxedCGAlpha A c (overRelaxedCG A b c j) •
      (overRelaxedCG A b c j).p := rfl

private theorem orcg_r_succ (j : ℕ) : (overRelaxedCG A b c (j + 1)).r =
    (overRelaxedCG A b c j).r - overRelaxedCGAlpha A c (overRelaxedCG A b c j) •
      (A *ᵥ (overRelaxedCG A b c j).p) := rfl

private theorem orcg_p_succ (j : ℕ) : (overRelaxedCG A b c (j + 1)).p =
    (overRelaxedCG A b c (j + 1)).r + (((overRelaxedCG A b c (j + 1)).r ⬝ᵥ
      (overRelaxedCG A b c (j + 1)).r) / ((overRelaxedCG A b c j).r ⬝ᵥ
        (overRelaxedCG A b c j).r)) • (overRelaxedCG A b c j).p := rfl

/-- The step length against the curvature: $\gamma\,\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}
= c\,\mathbf{r}^{\mathsf{T}}\mathbf{r}$ when the curvature is nonzero. -/
private theorem orcg_alpha_mul {s : CGState ℝ (Fin n)} (h : s.p ⬝ᵥ (A *ᵥ s.p) ≠ 0) :
    overRelaxedCGAlpha A c s * (s.p ⬝ᵥ (A *ᵥ s.p)) = c * (s.r ⬝ᵥ s.r) := by
  rw [overRelaxedCGAlpha, div_mul_cancel₀ _ h]

/-- A zero residual stays zero. -/
private theorem orcg_r_succ_eq_zero {j : ℕ} (h : (overRelaxedCG A b c j).r = 0) :
    (overRelaxedCG A b c (j + 1)).r = 0 := by
  rw [orcg_r_succ, overRelaxedCGAlpha, h]
  simp

/-- The updated residual of over-relaxed CG is the true one:
$\mathbf{r}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j$. -/
theorem overRelaxedCG_r_eq (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ) (j : ℕ) :
    (overRelaxedCG A b c j).r = b - A *ᵥ (overRelaxedCG A b c j).x := by
  induction j with
  | zero =>
    change b = b - A *ᵥ 0
    simp
  | succ j ih =>
    rw [orcg_r_succ, orcg_x_succ, ih, Matrix.mulVec_add, Matrix.mulVec_smul]
    abel

/-- **The line search defect drifts linearly**: if
$\mathbf{p}_i^{\mathsf{T}}\mathbf{A}\mathbf{p}_i \ne 0$ for $i < j$, then
$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j = (1 - j(c - 1))\,\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_j$
exactly. The multiplier $\delta_{j-1}\rho_{j-1}^2/\rho_j^2$ of the defect is $1$, so it is
never damped (the mechanism behind [StrakosTichy2002, (9.6)]). -/
theorem overRelaxedCG_p_dotProduct_r (b : Fin n → ℝ) (c : ℝ) {j : ℕ}
    (hμ : ∀ i < j, (overRelaxedCG A b c i).p ⬝ᵥ (A *ᵥ (overRelaxedCG A b c i).p) ≠ 0) :
    (overRelaxedCG A b c j).p ⬝ᵥ (overRelaxedCG A b c j).r =
      (1 - j * (c - 1)) * ((overRelaxedCG A b c j).r ⬝ᵥ (overRelaxedCG A b c j).r) := by
  induction j with
  | zero =>
    change b ⬝ᵥ b = (1 - ((0 : ℕ) : ℝ) * (c - 1)) * (b ⬝ᵥ b)
    simp
  | succ j ih =>
    have ih := ih fun i hi => hμ i (by omega)
    have hμj := hμ j (by omega)
    have hpr : (overRelaxedCG A b c j).p ⬝ᵥ (overRelaxedCG A b c (j + 1)).r =
        (1 - j * (c - 1)) * ((overRelaxedCG A b c j).r ⬝ᵥ (overRelaxedCG A b c j).r) -
          c * ((overRelaxedCG A b c j).r ⬝ᵥ (overRelaxedCG A b c j).r) := by
      rw [orcg_r_succ, dotProduct_sub, dotProduct_smul, smul_eq_mul, orcg_alpha_mul hμj, ih]
    by_cases hR : (overRelaxedCG A b c j).r ⬝ᵥ (overRelaxedCG A b c j).r = 0
    · have hr1 := orcg_r_succ_eq_zero (A := A) (b := b) (c := c) (dotProduct_self_eq_zero.mp hR)
      rw [orcg_p_succ, hr1]
      simp
    · rw [orcg_p_succ, add_dotProduct, smul_dotProduct, smul_eq_mul, hpr]
      push_cast
      field_simp
      ring

/-- **The $\mathbf{A}$-norm decrement of over-relaxed CG**: for symmetric $\mathbf{A}$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $\mathbf{p}_i^{\mathsf{T}}\mathbf{A}\mathbf{p}_i
\ne 0$ for $i \le j$,
$$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 - \|\mathbf{x}_\star -
\mathbf{x}_{j+1}\|_{\mathbf{A}}^2 = \gamma_j\,\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_j\,
\bigl(1 - (2j + 1)(c - 1)\bigr) .$$
Exact CG ($c = 1$) has $\gamma_j\rho_j^2$, the estimator of [StrakosTichy2002, (4.9)]. -/
theorem quadForm_sub_overRelaxedCG_sub_quadForm_sub_overRelaxedCG_succ (b : Fin n → ℝ) (c : ℝ)
    (hA : Aᵀ = A) {xs : Fin n → ℝ} (hx : A *ᵥ xs = b) {j : ℕ}
    (hμ : ∀ i ≤ j, (overRelaxedCG A b c i).p ⬝ᵥ (A *ᵥ (overRelaxedCG A b c i).p) ≠ 0) :
    quadForm A (xs - (overRelaxedCG A b c j).x) -
        quadForm A (xs - (overRelaxedCG A b c (j + 1)).x) =
      overRelaxedCGAlpha A c (overRelaxedCG A b c j) *
        ((overRelaxedCG A b c j).r ⬝ᵥ (overRelaxedCG A b c j).r) *
          (1 - (2 * j + 1) * (c - 1)) := by
  have hμj := hμ j le_rfl
  have hpr := overRelaxedCG_p_dotProduct_r (A := A) b c (j := j) fun i hi => hμ i hi.le
  have h1 := orcg_alpha_mul (A := A) (c := c) hμj
  have hr : A *ᵥ (xs - (overRelaxedCG A b c j).x) = (overRelaxedCG A b c j).r := by
    rw [Matrix.mulVec_sub, hx, overRelaxedCG_r_eq]
  have hsym : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := fun u v => by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  have he : xs - (overRelaxedCG A b c (j + 1)).x = (xs - (overRelaxedCG A b c j).x) -
      overRelaxedCGAlpha A c (overRelaxedCG A b c j) • (overRelaxedCG A b c j).p := by
    rw [orcg_x_succ]
    abel
  rw [he]
  simp only [quadForm_def, star_trivial]
  set γ := overRelaxedCGAlpha A c (overRelaxedCG A b c j)
  set e := xs - (overRelaxedCG A b c j).x
  set p := (overRelaxedCG A b c j).p
  have hexp : (e - γ • p) ⬝ᵥ (A *ᵥ (e - γ • p)) = e ⬝ᵥ (A *ᵥ e) - γ * (e ⬝ᵥ (A *ᵥ p)) -
      γ * (p ⬝ᵥ (A *ᵥ e)) + γ * (γ * (p ⬝ᵥ (A *ᵥ p))) := by
    simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [hexp, hsym e p, hr, h1, hpr]
  ring

/-- **No decrease past $j_1$**: for positive definite $\mathbf{A}$, $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, $c \ge 0$, directions $\mathbf{p}_i \ne \mathbf{0}$ for $i < j$ and
$j_1 \le j$ with $(2j_1 + 1)(c - 1) \ge 1$,
$\|\mathbf{x}_\star - \mathbf{x}_{j_1}\|_{\mathbf{A}}^2 \le \|\mathbf{x}_\star -
\mathbf{x}_j\|_{\mathbf{A}}^2$. For $c = (1 + \varepsilon)^2$, $j_1 \approx 1/(4\varepsilon)$. -/
theorem quadForm_sub_overRelaxedCG_le_of_le (b : Fin n → ℝ) (hA : A.PosDef) (hc : 0 ≤ c)
    {xs : Fin n → ℝ} (hx : A *ᵥ xs = b) {j₁ j : ℕ} (hj₁ : 1 ≤ (2 * j₁ + 1) * (c - 1))
    (hj : j₁ ≤ j) (hp : ∀ i < j, (overRelaxedCG A b c i).p ≠ 0) :
    quadForm A (xs - (overRelaxedCG A b c j₁).x) ≤
      quadForm A (xs - (overRelaxedCG A b c j).x) := by
  have hAT : Aᵀ = A := by
    have := hA.isHermitian.eq
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at this
  have hc1 : 0 < c - 1 := by
    by_contra h
    have : (2 * (j₁ : ℝ) + 1) * (c - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  suffices h : ∀ m, j₁ + m ≤ j → quadForm A (xs - (overRelaxedCG A b c j₁).x) ≤
      quadForm A (xs - (overRelaxedCG A b c (j₁ + m)).x) by
    have := h (j - j₁) (by omega)
    rwa [Nat.add_sub_cancel' hj] at this
  intro m hm
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    have ih := ih (by omega)
    have hμ : ∀ i ≤ j₁ + m,
        (overRelaxedCG A b c i).p ⬝ᵥ (A *ᵥ (overRelaxedCG A b c i).p) ≠ 0 := fun i hi => by
      have := hA.dotProduct_mulVec_pos (hp i (by omega))
      simp only [star_trivial] at this
      exact this.ne'
    have hpos : 0 < (overRelaxedCG A b c (j₁ + m)).p ⬝ᵥ
        (A *ᵥ (overRelaxedCG A b c (j₁ + m)).p) := by
      have := hA.dotProduct_mulVec_pos (hp (j₁ + m) (by omega))
      simpa only [star_trivial] using this
    have hd := quadForm_sub_overRelaxedCG_sub_quadForm_sub_overRelaxedCG_succ b c hAT hx hμ
    have hR : 0 ≤ (overRelaxedCG A b c (j₁ + m)).r ⬝ᵥ (overRelaxedCG A b c (j₁ + m)).r :=
      Finset.sum_nonneg fun i _ => mul_self_nonneg _
    have hγ : 0 ≤ overRelaxedCGAlpha A c (overRelaxedCG A b c (j₁ + m)) :=
      div_nonneg (mul_nonneg hc hR) hpos.le
    have hj' : 1 ≤ (2 * ((j₁ + m : ℕ) : ℝ) + 1) * (c - 1) := by
      push_cast
      nlinarith
    have hneg : overRelaxedCGAlpha A c (overRelaxedCG A b c (j₁ + m)) *
        ((overRelaxedCG A b c (j₁ + m)).r ⬝ᵥ (overRelaxedCG A b c (j₁ + m)).r) *
          (1 - (2 * ((j₁ + m : ℕ) : ℝ) + 1) * (c - 1)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hγ hR) (by linarith)
    rw [← add_assoc]
    linarith

/-- The Rayleigh lower bound of a symmetric matrix with spectrum in $[a, a']$. -/
private theorem orcg_mul_norm_sq_le {a a' : ℝ} (hH : A.IsHermitian)
    (hs : spectrum ℝ A ⊆ Set.Icc a a') (v : Fin n → ℝ) :
    a * ‖WithLp.toLp 2 v‖ ^ 2 ≤ v ⬝ᵥ (A *ᵥ v) := by
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0
    have hv : v = 0 := Subsingleton.elim _ _
    subst hv
    rw [WithLp.toLp_zero, norm_zero]
    simp
  · obtain ⟨c, hc⟩ : ∃ c, c + 1 = Fintype.card (Fin n) := ⟨n - 1, by simp; omega⟩
    have h1 := hH.eigenvalue_last_mul_le_re_quadForm hc v
    simp only [quadForm_def, star_trivial, RCLike.re_to_real] at h1
    have e1 := (hH.spectrum_subset_iff.mp hs c (by omega)).1
    exact (mul_le_mul_of_nonneg_right e1 (sq_nonneg _)).trans h1

/-- **Over-relaxed CG does not converge**: for symmetric $\mathbf{A}$ with spectrum in
$[a, a']$, $a > 0$, $c > 1$ and directions $\mathbf{p}_j \ne \mathbf{0}$ for all $j$, the
residual norms are bounded away from $0$: there is $\eta > 0$ with $\eta \le \|\mathbf{r}_j\|$
for every $j$. In particular the HSCG run with the admissible pattern
$\theta_j = \eta^\gamma_j = \varepsilon > 0$ has $\|\mathbf{r}_j\| \not\to 0$.
No printed source. -/
theorem overRelaxedCG_exists_pos_le_norm_r (b : Fin n → ℝ) (hA : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hc : 1 < c)
    (hp : ∀ j, (overRelaxedCG A b c j).p ≠ 0) :
    ∃ η > 0, ∀ j, η ≤ ‖WithLp.toLp 2 (overRelaxedCG A b c j).r‖ := by
  have hherm : A.IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial, hA]
  have hPD : A.PosDef := hherm.posDef_iff_eigenvalue_pos.mpr fun i hi =>
    ha.trans_le (hherm.spectrum_subset_iff.mp hs i hi).1
  have hr : ∀ j, (overRelaxedCG A b c j).r ≠ 0 := fun j h => hp (j + 1) (by
    rw [orcg_p_succ, orcg_r_succ_eq_zero h]
    simp)
  set xs := A⁻¹ *ᵥ b
  have hx : A *ᵥ xs = b := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp
      hPD.isUnit), Matrix.one_mulVec]
  have hre : ∀ j, A *ᵥ (xs - (overRelaxedCG A b c j).x) = (overRelaxedCG A b c j).r := fun j => by
    rw [Matrix.mulVec_sub, hx, overRelaxedCG_r_eq]
  -- `a eᵀAe ≤ ‖Ae‖²`
  have hlow : ∀ e : Fin n → ℝ, a * (e ⬝ᵥ (A *ᵥ e)) ≤ ‖WithLp.toLp 2 (A *ᵥ e)‖ ^ 2 := fun e => by
    have h1 := orcg_mul_norm_sq_le hherm hs e
    have h2 := (le_abs_self _).trans (EuclideanSpace.abs_dotProduct_le_norm e (A *ᵥ e))
    set N := ‖WithLp.toLp 2 e‖
    set R := ‖WithLp.toLp 2 (A *ᵥ e)‖
    have hN := norm_nonneg (WithLp.toLp 2 e)
    have hR := norm_nonneg (WithLp.toLp 2 (A *ᵥ e))
    rcases hN.lt_or_eq with hN' | hN'
    · have haN : a * N ≤ R := le_of_mul_le_mul_left (by nlinarith) hN'
      nlinarith
    · have hN0 : N = 0 := hN'.symm
      rw [hN0] at h1 h2
      nlinarith
  set j₁ := ⌈1 / (c - 1)⌉₊
  have hc1 : 0 < c - 1 := by linarith
  have hj₁ : 1 ≤ (2 * (j₁ : ℝ) + 1) * (c - 1) := by
    have h := Nat.le_ceil (1 / (c - 1))
    have : 1 ≤ (j₁ : ℝ) * (c - 1) := by
      rw [div_le_iff₀ hc1] at h
      linarith
    nlinarith
  set Q := quadForm A (xs - (overRelaxedCG A b c j₁).x)
  have hQ : 0 < Q := by
    have he : xs - (overRelaxedCG A b c j₁).x ≠ 0 := fun h => hr j₁ (by
      rw [← hre j₁, h, Matrix.mulVec_zero])
    simpa only [Q, quadForm_def] using hPD.dotProduct_mulVec_pos he
  have hρ : ∀ j, 0 < ‖WithLp.toLp 2 (overRelaxedCG A b c j).r‖ := fun j =>
    norm_pos_iff.mpr fun h => hr j (by simpa using congrArg WithLp.ofLp h)
  refine ⟨min (Real.sqrt (a * Q)) ((Finset.range (j₁ + 1)).inf' ⟨0, by simp⟩
    fun j => ‖WithLp.toLp 2 (overRelaxedCG A b c j).r‖), lt_min (Real.sqrt_pos.mpr
      (mul_pos ha hQ)) ((Finset.lt_inf'_iff _).mpr fun j _ => hρ j), fun j => ?_⟩
  rcases le_or_gt j j₁ with hj | hj
  · exact (min_le_right _ _).trans (Finset.inf'_le _ (by simp; omega))
  · refine (min_le_left _ _).trans ?_
    have hmono := quadForm_sub_overRelaxedCG_le_of_le b hPD (by linarith) hx hj₁ hj.le
      fun i _ => hp i
    have h1 := hlow (xs - (overRelaxedCG A b c j).x)
    have h3 : ‖WithLp.toLp 2 (A *ᵥ (xs - (overRelaxedCG A b c j).x))‖ =
        ‖WithLp.toLp 2 (overRelaxedCG A b c j).r‖ := by rw [hre j]
    rw [h3] at h1
    have h2 : a * Q ≤ ‖WithLp.toLp 2 (overRelaxedCG A b c j).r‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_left hmono ha.le
      simp only [Q, quadForm_def, star_trivial] at this ⊢
      linarith
    calc Real.sqrt (a * Q) ≤ Real.sqrt (‖WithLp.toLp 2 (overRelaxedCG A b c j).r‖ ^ 2) :=
          Real.sqrt_le_sqrt h2
      _ = _ := Real.sqrt_sq (norm_nonneg _)

/-- The directions of over-relaxed CG are nonzero while the residuals are and
$j(c - 1) < 1$: for positive definite $\mathbf{A}$, $c \ge 1$, $\mathbf{r}_i \ne \mathbf{0}$ for
$i \le j$ and $j(c - 1) < 1$, $\mathbf{p}_j \ne \mathbf{0}$. -/
theorem overRelaxedCG_p_ne_zero (b : Fin n → ℝ) (hA : A.PosDef) (hc : 1 ≤ c) {j : ℕ}
    (hr : ∀ i ≤ j, (overRelaxedCG A b c i).r ≠ 0) (hj : j * (c - 1) < 1) :
    (overRelaxedCG A b c j).p ≠ 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    have hR : ∀ i ≤ j, 0 < (overRelaxedCG A b c i).r ⬝ᵥ (overRelaxedCG A b c i).r :=
      fun i hi => lt_of_le_of_ne (Finset.sum_nonneg fun l _ => mul_self_nonneg _)
        fun h => hr i hi (dotProduct_self_eq_zero.mp h.symm)
    have hμ : ∀ i < j,
        (overRelaxedCG A b c i).p ⬝ᵥ (A *ᵥ (overRelaxedCG A b c i).p) ≠ 0 := fun i hi => by
      have hij : (i : ℝ) ≤ j := by exact_mod_cast hi.le
      have hpi := ih i hi (fun i' hi' => hr i' (by omega)) (by nlinarith)
      have := hA.dotProduct_mulVec_pos hpi
      simp only [star_trivial] at this
      exact this.ne'
    have h := overRelaxedCG_p_dotProduct_r b c hμ
    intro h0
    rw [h0, zero_dotProduct] at h
    have hu : 0 < 1 - (j : ℝ) * (c - 1) := by linarith
    nlinarith [mul_pos hu (hR j le_rfl)]

/-- **Over-relaxed CG is an admissible run**: for symmetric positive definite $\mathbf{A}$,
$0 \le \varepsilon$, $1 \le k$, $k\varepsilon \le 1/100$ and $\mathbf{r}_j \ne \mathbf{0}$ for
$j < k$, the first $k$ steps of over-relaxed CG with $c = (1 + \varepsilon)^2$ are an
`NLAlib.CGRun` with accuracy parameter $\varepsilon$: $\theta_j = \eta^\gamma_j = \varepsilon$,
every other local error $0$, $\mathbf{s}_j = \mathbf{A}\mathbf{p}_j$,
$\nu_j = (1 + \varepsilon)\|\mathbf{r}_j\|^2$, $\mu_j = \mathbf{p}_j^{\mathsf{T}}\mathbf{A}
\mathbf{p}_j$, $\delta_j = \nu_{j+1}/\nu_j$. -/
noncomputable def overRelaxedCGRun (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ε : ℝ)
    (k : ℕ) (hA : A.PosDef) (hAT : Aᵀ = A) (hε : 0 ≤ ε) (hk : 0 < k)
    (hkε : (k : ℝ) * ε ≤ 1 / 100) (hr : ∀ j < k, (overRelaxedCG A b ((1 + ε) ^ 2) j).r ≠ 0) :
    CGRun n k where
  A := A
  b := b
  x j := (overRelaxedCG A b ((1 + ε) ^ 2) j).x
  r j := (overRelaxedCG A b ((1 + ε) ^ 2) j).r
  p j := (overRelaxedCG A b ((1 + ε) ^ 2) j).p
  s j := A *ᵥ (overRelaxedCG A b ((1 + ε) ^ 2) j).p
  ν j := ‖WithLp.toLp 2 (overRelaxedCG A b ((1 + ε) ^ 2) j).r‖ ^ 2 * (1 + ε)
  μ j := (overRelaxedCG A b ((1 + ε) ^ 2) j).p ⬝ᵥ (A *ᵥ (overRelaxedCG A b ((1 + ε) ^ 2) j).p)
  γ j := overRelaxedCGAlpha A ((1 + ε) ^ 2) (overRelaxedCG A b ((1 + ε) ^ 2) j)
  δ j := ‖WithLp.toLp 2 (overRelaxedCG A b ((1 + ε) ^ 2) (j + 1)).r‖ ^ 2 * (1 + ε) /
    (‖WithLp.toLp 2 (overRelaxedCG A b ((1 + ε) ^ 2) j).r‖ ^ 2 * (1 + ε))
  es _ := 0
  θ _ := ε
  eμ _ := 0
  eγ _ := ε
  ex _ := 0
  er _ := 0
  eδ _ := 0
  ep _ := 0
  ε := ε
  transpose_A := hAT
  ε_nonneg := hε
  k_pos := hk
  k_mul_ε_le := hkε
  x_zero := rfl
  r_zero := rfl
  p_zero := rfl
  ν_eq _ _ := rfl
  abs_θ_le _ _ := (abs_of_nonneg hε).le
  ν_pos j hj := by
    have h : WithLp.toLp 2 (overRelaxedCG A b ((1 + ε) ^ 2) j).r ≠ 0 := fun h =>
      hr j hj (by simpa using congrArg WithLp.ofLp h)
    have := norm_pos_iff.mpr h
    positivity
  s_eq _ _ := (add_zero _).symm
  norm_es_le _ _ := by
    rw [WithLp.toLp_zero, norm_zero]
    have := specNorm_nonneg A
    positivity
  μ_eq _ _ := (add_zero _).symm
  abs_eμ_le _ _ := by
    rw [abs_zero]
    positivity
  μ_pos j hj := by
    have hε1 : ε ≤ 1 / 100 := by
      have : (1 : ℝ) ≤ k := by exact_mod_cast hk
      nlinarith
    have hjε : (j : ℝ) * ε ≤ 1 / 100 := by
      have : (j : ℝ) ≤ k := by exact_mod_cast hj.le
      nlinarith
    have hp := overRelaxedCG_p_ne_zero b hA (by nlinarith) (fun i hi => hr i (by omega))
      (by nlinarith : (j : ℝ) * ((1 + ε) ^ 2 - 1) < 1)
    simpa only [star_trivial] using hA.dotProduct_mulVec_pos hp
  γ_eq _ _ := by
    simp only [overRelaxedCGAlpha, EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
    ring
  abs_eγ_le _ _ := (abs_of_nonneg hε).le
  x_succ _ _ := by
    rw [add_zero]
    rfl
  norm_ex_le _ _ := by
    rw [WithLp.toLp_zero, norm_zero]
    positivity
  r_succ _ _ := by
    rw [add_zero]
    rfl
  norm_er_le _ _ := by
    rw [WithLp.toLp_zero, norm_zero]
    positivity
  δ_eq _ _ := by rw [add_zero, mul_one]
  abs_eδ_le _ _ := by
    rw [abs_zero]
    exact hε
  p_succ j _ := by
    rw [add_zero, orcg_p_succ, mul_div_mul_right _ _ (by linarith : (1 + ε) ≠ 0),
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self,
      EuclideanSpace.norm_toLp_sq_eq_dotProduct_self]
  norm_ep_le _ _ := by
    rw [WithLp.toLp_zero, norm_zero]
    positivity

/-- The realized run is over-relaxed CG: its residuals are those of `NLAlib.overRelaxedCG` with
$c = (1 + \varepsilon)^2$, so `NLAlib.overRelaxedCG_exists_pos_le_norm_r` applies to the data of
every `NLAlib.overRelaxedCGRun`. -/
theorem overRelaxedCGRun_r (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ε : ℝ) (k : ℕ)
    (hA : A.PosDef) (hAT : Aᵀ = A) (hε : 0 ≤ ε) (hk : 0 < k) (hkε : (k : ℝ) * ε ≤ 1 / 100)
    (hr : ∀ j < k, (overRelaxedCG A b ((1 + ε) ^ 2) j).r ≠ 0) (j : ℕ) :
    (overRelaxedCGRun A b ε k hA hAT hε hk hkε hr).r j = (overRelaxedCG A b ((1 + ε) ^ 2) j).r :=
  rfl

end NLAlib
