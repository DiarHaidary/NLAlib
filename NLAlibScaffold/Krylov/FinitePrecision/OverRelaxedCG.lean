/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.CGRun

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
with $c_0 < 1/4$, and a $k$-uniform backward model is impossible in the worst case. The research
note `~/nlalib-harness/reports/HSCG-FP-Research.md`, §4.6, with a numerical check.

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

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md`.

## Main definitions

* `NLAlib.overRelaxedCGAlpha`, `NLAlib.overRelaxedCGStep`, `NLAlib.overRelaxedCG`.

## Main results

* `NLAlib.overRelaxedCG_p_dotProduct_r`: the linear drift of the line search defect.
* `NLAlib.overRelaxedCG_quadForm_sub_sub_quadForm_sub_succ`: the $\mathbf{A}$-norm decrement.
* `NLAlib.overRelaxedCG_quadForm_sub_le_of_le`: no decrease past $1/(4\varepsilon)$.
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

/-- The updated residual of over-relaxed CG is the true one:
$\mathbf{r}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j$. Proof: induction. Difficulty: easy. -/
theorem overRelaxedCG_r_eq (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (c : ℝ) (j : ℕ) :
    (overRelaxedCG A b c j).r = b - A *ᵥ (overRelaxedCG A b c j).x := by
  sorry

/-- **The line search defect drifts linearly**: if
$\mathbf{p}_i^{\mathsf{T}}\mathbf{A}\mathbf{p}_i \ne 0$ for $i < j$, then
$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j = (1 - j(c - 1))\,\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_j$
exactly. The multiplier $\delta_{j-1}\rho_{j-1}^2/\rho_j^2$ of the defect is $1$, so it is
never damped (the mechanism behind [StrakosTichy2002, (9.6)]).
Proof: $\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1} = \mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j -
c\rho_j^2$ and $\mathbf{p}_{j+1}^{\mathsf{T}}\mathbf{r}_{j+1} = \rho_{j+1}^2 +
(\rho_{j+1}^2/\rho_j^2)\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1}$; induction. Difficulty: easy. -/
theorem overRelaxedCG_p_dotProduct_r (b : Fin n → ℝ) (c : ℝ) {j : ℕ}
    (hμ : ∀ i < j, (overRelaxedCG A b c i).p ⬝ᵥ (A *ᵥ (overRelaxedCG A b c i).p) ≠ 0) :
    (overRelaxedCG A b c j).p ⬝ᵥ (overRelaxedCG A b c j).r =
      (1 - j * (c - 1)) * ((overRelaxedCG A b c j).r ⬝ᵥ (overRelaxedCG A b c j).r) := by
  sorry

/-- **The $\mathbf{A}$-norm decrement of over-relaxed CG**: for symmetric $\mathbf{A}$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $\mathbf{p}_i^{\mathsf{T}}\mathbf{A}\mathbf{p}_i
\ne 0$ for $i \le j$,
$$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 - \|\mathbf{x}_\star -
\mathbf{x}_{j+1}\|_{\mathbf{A}}^2 = \gamma_j\,\mathbf{r}_j^{\mathsf{T}}\mathbf{r}_j\,
\bigl(1 - (2j + 1)(c - 1)\bigr) .$$
Exact CG ($c = 1$) has $\gamma_j\rho_j^2$, the estimator of [StrakosTichy2002, (4.9)].
Proof: $\|\mathbf{e} - \gamma\mathbf{p}\|_{\mathbf{A}}^2 = \|\mathbf{e}\|_{\mathbf{A}}^2 -
2\gamma\mathbf{p}^{\mathsf{T}}\mathbf{r} + \gamma^2\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$
with $\mathbf{A}\mathbf{e}_j = \mathbf{r}_j$, `NLAlib.overRelaxedCG_p_dotProduct_r` and
$\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j = c\rho_j^2$. Difficulty: easy. -/
theorem overRelaxedCG_quadForm_sub_sub_quadForm_sub_succ (b : Fin n → ℝ) (c : ℝ)
    (hA : Aᵀ = A) {xs : Fin n → ℝ} (hx : A *ᵥ xs = b) {j : ℕ}
    (hμ : ∀ i ≤ j, (overRelaxedCG A b c i).p ⬝ᵥ (A *ᵥ (overRelaxedCG A b c i).p) ≠ 0) :
    quadForm A (xs - (overRelaxedCG A b c j).x) -
        quadForm A (xs - (overRelaxedCG A b c (j + 1)).x) =
      overRelaxedCGAlpha A c (overRelaxedCG A b c j) *
        ((overRelaxedCG A b c j).r ⬝ᵥ (overRelaxedCG A b c j).r) *
          (1 - (2 * j + 1) * (c - 1)) := by
  sorry

/-- **No decrease past $j_1$**: for positive definite $\mathbf{A}$, $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, $c \ge 0$, directions $\mathbf{p}_i \ne \mathbf{0}$ for $i < j$ and
$j_1 \le j$ with $(2j_1 + 1)(c - 1) \ge 1$,
$\|\mathbf{x}_\star - \mathbf{x}_{j_1}\|_{\mathbf{A}}^2 \le \|\mathbf{x}_\star -
\mathbf{x}_j\|_{\mathbf{A}}^2$. For $c = (1 + \varepsilon)^2$, $j_1 \approx 1/(4\varepsilon)$.
Proof: every decrement of `NLAlib.overRelaxedCG_quadForm_sub_sub_quadForm_sub_succ` from $j_1$
on is $\le 0$ ($\gamma_i \ge 0$). Difficulty: easy. -/
theorem overRelaxedCG_quadForm_sub_le_of_le (b : Fin n → ℝ) (hA : A.PosDef) (hc : 0 ≤ c)
    {xs : Fin n → ℝ} (hx : A *ᵥ xs = b) {j₁ j : ℕ} (hj₁ : 1 ≤ (2 * j₁ + 1) * (c - 1))
    (hj : j₁ ≤ j) (hp : ∀ i < j, (overRelaxedCG A b c i).p ≠ 0) :
    quadForm A (xs - (overRelaxedCG A b c j₁).x) ≤
      quadForm A (xs - (overRelaxedCG A b c j).x) := by
  sorry

/-- **Over-relaxed CG does not converge**: for symmetric $\mathbf{A}$ with spectrum in
$[a, a']$, $a > 0$, $c > 1$ and directions $\mathbf{p}_j \ne \mathbf{0}$ for all $j$, the
residual norms are bounded away from $0$: there is $\eta > 0$ with $\eta \le \|\mathbf{r}_j\|$
for every $j$. In particular the HSCG run with the admissible pattern
$\theta_j = \eta^\gamma_j = \varepsilon > 0$ has $\|\mathbf{r}_j\| \not\to 0$.
No printed source; the research note, §4.6.
Proof: for $j \ge j_1 = \lceil 1/(c - 1)\rceil$, $\|\mathbf{r}_j\|^2 = \|\mathbf{A}\mathbf{e}_j\|^2
\ge a\|\mathbf{e}_j\|_{\mathbf{A}}^2 \ge a\|\mathbf{e}_{j_1}\|_{\mathbf{A}}^2 > 0$
(`NLAlib.overRelaxedCG_quadForm_sub_le_of_le`); below $j_1$ finitely many $\mathbf{r}_j \ne
\mathbf{0}$ (a zero residual makes the next direction zero). Difficulty: easy. -/
theorem overRelaxedCG_exists_pos_le_norm_r (b : Fin n → ℝ) (hA : Aᵀ = A) {a a' : ℝ}
    (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hc : 1 < c)
    (hp : ∀ j, (overRelaxedCG A b c j).p ≠ 0) :
    ∃ η > 0, ∀ j, η ≤ ‖WithLp.toLp 2 (overRelaxedCG A b c j).r‖ := by
  sorry

/-- The directions of over-relaxed CG are nonzero while the residuals are and
$j(c - 1) < 1$: for positive definite $\mathbf{A}$, $c \ge 1$, $\mathbf{r}_i \ne \mathbf{0}$ for
$i \le j$ and $j(c - 1) < 1$, $\mathbf{p}_j \ne \mathbf{0}$.
Proof: `NLAlib.overRelaxedCG_p_dotProduct_r`, induction. Difficulty: easy. -/
theorem overRelaxedCG_p_ne_zero (b : Fin n → ℝ) (hA : A.PosDef) (hc : 1 ≤ c) {j : ℕ}
    (hr : ∀ i ≤ j, (overRelaxedCG A b c i).r ≠ 0) (hj : j * (c - 1) < 1) :
    (overRelaxedCG A b c j).p ≠ 0 := by
  sorry

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
  abs_θ_le _ _ := by sorry
  ν_pos := by sorry
  s_eq _ _ := by sorry
  norm_es_le := by sorry
  μ_eq _ _ := by sorry
  abs_eμ_le := by sorry
  μ_pos := by sorry
  γ_eq := by sorry
  abs_eγ_le := by sorry
  x_succ := by sorry
  norm_ex_le := by sorry
  r_succ := by sorry
  norm_er_le := by sorry
  δ_eq := by sorry
  abs_eδ_le := by sorry
  p_succ := by sorry
  norm_ep_le := by sorry

/-- The realized run is over-relaxed CG: its residuals are those of `NLAlib.overRelaxedCG` with
$c = (1 + \varepsilon)^2$, so `NLAlib.overRelaxedCG_exists_pos_le_norm_r` applies to the data of
every `NLAlib.overRelaxedCGRun`. Proof: `rfl`. Difficulty: easy. -/
theorem overRelaxedCGRun_r (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (ε : ℝ) (k : ℕ)
    (hA : A.PosDef) (hAT : Aᵀ = A) (hε : 0 ≤ ε) (hk : 0 < k) (hkε : (k : ℝ) * ε ≤ 1 / 100)
    (hr : ∀ j < k, (overRelaxedCG A b ((1 + ε) ^ 2) j).r ≠ 0) (j : ℕ) :
    (overRelaxedCGRun A b ε k hA hAT hε hk hkε hr).r j = (overRelaxedCG A b ((1 + ε) ^ 2) j).r :=
  rfl

end NLAlib
