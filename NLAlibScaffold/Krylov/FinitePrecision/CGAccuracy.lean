/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.CGBackward

/-!
# The residual gap and the attainable accuracy of finite-precision CG, a priori

For a conjugate gradient run `C : NLAlib.CGRun n k` on a matrix with spectrum in $[a, a']$,
$a > 0$, $\kappa = a'/a$, under (H) $k^3\varepsilon\kappa^2 \le 10^{-5}$ and
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, the computed iterates, the $\mathbf{A}$-norm error of
the computed run and the residual gap $\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j -
\mathbf{r}_j$ are bounded a priori: with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{x}_j\| \le 1.001\,M,\qquad
\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le 1.001\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2,
\qquad \|\mathbf{g}_k\| \le 11\,k\,\varepsilon\,a'M .$$
Every rigorous gap bound in the literature keeps $\max_j\|\mathbf{x}_j\|$ (a posteriori);
[MeurantStrakos2006, §5.4] states the a priori form as a heuristic.

The proof is one joint induction (the private theorem `gapErrorInduction`) on the gap and the
true $\mathbf{A}$-norm error $E_j$ of the computed run: the descent
$\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j \ge 0.999\rho_j^2$ (G1, from the line search defect), the
step $\gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \le 1.001\gamma_j\rho_j^2$ (G2),
$\gamma_j\|\mathbf{p}_j\| \le 1.5\|\mathbf{b}\|/a$ through the model's
$\sum_j\gamma_j\rho_j^2 \le 2\|\mathbf{b}\|^2/a$ (G2′), and the one-step inequality for
$E_{j+1}$ (G3).

The **attainable accuracy**: after $k^\star = \lceil\tfrac12(\sqrt{\kappa'} + 1)\ell\rceil$ steps,
$\kappa' = 2\kappa + 1$, $\ell = \ln(\sqrt{\kappa'}/(4\varepsilon))$, the computed residual is
below $8\varepsilon\|\mathbf{b}\|$ (`NLAlib.CGRun.ρ_le_of_cgKStar_le`, the Chebyshev bound of the
model), so the true residual is the gap up to $8\varepsilon\|\mathbf{b}\|$. Exact arithmetic is
an admissible run with zero gap, so no statement "computed residual $\ll$ true residual" holds;
the $\delta$-form compares with the gap bound instead.

Validity: (H) bounds the number of steps; with $k = k^\star$ this needs roughly
$\kappa \lesssim 0.05\,\varepsilon^{-2/7}\ell^{-6/7}$ (the research note
`~/nlalib-harness/reports/HSCG-FP-Research.md`, §4.3: $\kappa \le 80$ at $\varepsilon = u$ in
double precision, $\kappa \le 5$ for dense products at $N = 10^3$).

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§9) and
the research note, §§4.2–4.3, 4.5. Constants are unoptimised and differ from the note's
(maintainer, 2026-10-29: "do whatever is cleanest proof-wise").

## Main definitions

* `NLAlib.cgKStar`: the number of steps after which the computed residual is at gap level.

## Main results

* `NLAlib.CGRun.p_dotProduct_r_ge`, `NLAlib.CGRun.γ_sq_mul_dotProduct_mulVec_le`,
  `NLAlib.CGRun.γ_mul_norm_p_le`, `NLAlib.CGRun.quadForm_sub_x_succ_le`: the one-step lemmas.
* `NLAlib.CGRun.quadForm_sub_x_le_sub_sum`, `NLAlib.CGRun.quadForm_sub_x_le`,
  `NLAlib.CGRun.norm_x_le`: the computed run's error and iterates, a priori.
* `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy`,
  `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_sol`,
  `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_b`: the residual gap, a priori.
* `NLAlib.CGRun.norm_sub_mulVec_x_le`: the true residual.
* `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.abs_norm_sub_mulVec_x_sub_norm_gap_le`,
  `NLAlib.CGRun.norm_sub_mulVec_x_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_x_le_of_cgKStar_le`,
  `NLAlib.CGRun.norm_sub_mulVec_x_cgKStar_le`: the attainable accuracy.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The number of steps to gap level**: with $\kappa' = 2\kappa + 1$,
<!-- value cgKStar \kappa \varepsilon \delta -->
$k^\star(\kappa, \varepsilon, \delta) = \bigl\lceil\tfrac12(\sqrt{2\kappa+1} + 1)
\ln\bigl(\sqrt{2\kappa+1}/(4\delta\varepsilon)\bigr)\bigr\rceil$. After $k^\star$ steps the
Chebyshev factor $2\sqrt{\kappa'}q^{k}$, $q = (\sqrt{\kappa'} - 1)/(\sqrt{\kappa'} + 1)$, is at
most $8\delta\varepsilon$ (`NLAlib.pow_cgKStar_le`). The research note has $\sqrt{\kappa'}$ in
place of $\sqrt{\kappa'} + 1$ (from $\ln(1/q) \ge 2/\sqrt{\kappa'}$); here
$q \le e^{-2/(\sqrt{\kappa'} + 1)}$, which is one line. -/
noncomputable def cgKStar (κ ε δ : ℝ) : ℕ :=
  ⌈(Real.sqrt (2 * κ + 1) + 1) / 2 * Real.log (Real.sqrt (2 * κ + 1) / (4 * δ * ε))⌉₊

/-- **The Chebyshev factor after $k^\star$ steps**: for $\varepsilon, \delta > 0$, $\kappa \ge 0$
and $m \ge k^\star(\kappa, \varepsilon, \delta)$, with $\kappa' = 2\kappa + 1$,
$$\Bigl(\frac{\sqrt{\kappa'} - 1}{\sqrt{\kappa'} + 1}\Bigr)^m \le
\frac{4\delta\varepsilon}{\sqrt{\kappa'}} \,.$$
Proof: $q = 1 - 2/(\sqrt{\kappa'} + 1) \le e^{-2/(\sqrt{\kappa'} + 1)}$
(`Real.add_one_le_exp`), $0 \le q$, and $2m/(\sqrt{\kappa'} + 1) \ge \ell$. Difficulty: easy. -/
theorem pow_cgKStar_le {κ ε δ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hδ : 0 < δ) {m : ℕ}
    (hm : cgKStar κ ε δ ≤ m) :
    ((Real.sqrt (2 * κ + 1) - 1) / (Real.sqrt (2 * κ + 1) + 1)) ^ m ≤
      4 * δ * ε / Real.sqrt (2 * κ + 1) := by
  sorry

/-- $k^\star \ge 1$ for $\kappa \ge 0$, $0 < \delta \le 1$ and $0 < \varepsilon \le 1/100$:
the logarithm is at least $\ln 25 > 0$. Proof: `Nat.ceil_pos`. Difficulty: easy. -/
theorem cgKStar_pos {κ ε δ : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) : 0 < cgKStar κ ε δ := by
  sorry

/-- **The window condition for $k^\star$**: for $\kappa \ge 1$ and $0 < \varepsilon \le 1/100$,
with $\ell = \ln(\sqrt{2\kappa + 1}/(4\varepsilon))$,
$\kappa^3\sqrt{\kappa}\,\varepsilon\,\ell^3 \le 7 \cdot 10^{-7}$ implies that (H) holds at
$k^\star$: $(k^\star)^3\varepsilon\kappa^2 \le 10^{-5}$. The research note has $\kappa^{7/2}
\varepsilon\ell^3 \le 1.5 \cdot 10^{-5}$ with its sharper $k^\star$.
Proof: $k^\star \le \tfrac12(\sqrt{2\kappa+1} + 1)\ell + 1 \le 2.37\sqrt{\kappa}\,\ell$ since
$\ell \ge 1$ and $\sqrt{2\kappa + 1} \le \sqrt{3}\sqrt{\kappa}$; $2.37^3 \cdot 7 \cdot 10^{-7} \le
10^{-5}$. Difficulty: easy. -/
theorem cgKStar_cube_mul_le {κ ε : ℝ} (hκ : 1 ≤ κ) (hε : 0 < ε) (hε1 : ε ≤ 1 / 100)
    (h : κ ^ 3 * Real.sqrt κ * ε *
      Real.log (Real.sqrt (2 * κ + 1) / (4 * 1 * ε)) ^ 3 ≤ 7 / 10 ^ 7) :
    (cgKStar κ ε 1 : ℝ) ^ 3 * ε * κ ^ 2 ≤ 1 / 10 ^ 5 := by
  sorry

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-! ### One step -/

/-- **Descent (G1)**: under (H), $\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j \ge
0.999\,\|\mathbf{r}_j\|^2$ for $j < k$. Exact CG has equality; here the line search defect
$\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{r}_j$ enters through
$\mathbf{p}_j = \mathbf{r}_j + \delta_{j-1}\mathbf{p}_{j-1} + \mathbf{e}^p_{j-1}$.
Proof: `NLAlib.CGRun.abs_p_dotProduct_r_succ_le` with $\Pi = 2\kappa$, $K = 1.05\kappa$
(`NLAlib.CGRun.norm_p_sq_le`, `NLAlib.CGRun.specNorm_mul_γ_mul_norm_p_sq_le`), so
$\lvert\delta_{j-1}\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{r}_j\rvert \le
26k\varepsilon\kappa\rho_j^2$, and
$\lvert\mathbf{e}^{p\mathsf{T}}_{j-1}\mathbf{r}_j\rvert \le
\varepsilon(\rho_j + \delta_{j-1}\|\mathbf{p}_{j-1}\|)\rho_j \le 5\varepsilon\kappa\rho_j^2$
(`NLAlib.CGRun.δ_mul_norm_p_le`). Difficulty: easy. -/
theorem p_dotProduct_r_ge {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    (1 - 1 / 1000) * C.ρ j ^ 2 ≤ C.p j ⬝ᵥ C.r j := by
  sorry

/-- **The step against the residual (G2)**: under (H), for $j < k$,
$\gamma_j^2\,\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \le 1.001\,\gamma_j\|\mathbf{r}_j\|^2$.
Proof: $\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j = \mu_j - e^\mu_j -
\mathbf{p}_j^{\mathsf{T}}\mathbf{e}^s_j \le \mu_j + 2.1\varepsilon\kappa\,
\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j$ and $\gamma_j\mu_j = \nu_j(1 + \eta^\gamma_j)$
(`NLAlib.CGRun.γ_mul_μ`). Difficulty: easy. -/
theorem γ_sq_mul_dotProduct_mulVec_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j < k) :
    C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) ≤ (1 + 1 / 1000) * (C.γ j * C.ρ j ^ 2) := by
  sorry

/-- **The step length, a priori (G2′)**: under (H), $\gamma_j\|\mathbf{p}_j\| \le
1.5\|\mathbf{b}\|/a$ for $j < k$.
Proof: $a\gamma_j^2\|\mathbf{p}_j\|^2 \le \gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}\mathbf{p}_j
\le 1.001\gamma_j\rho_j^2$ (`NLAlib.CGRun.γ_sq_mul_dotProduct_mulVec_le`) and
$\sum_{j<k}\gamma_j\rho_j^2 \le 2\|\mathbf{b}\|^2/a$ (`NLAlib.CGRun.sum_γ_mul_ρ_sq_le`, the model).
Difficulty: easy. -/
theorem γ_mul_norm_p_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {j : ℕ} (hj : j < k) :
    C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ≤ 3 / 2 * ‖WithLp.toLp 2 C.b‖ / a := by
  sorry

/-- **One step of the computed run's $\mathbf{A}$-norm error (G3)**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j < k$, with the gap
$\mathbf{g}_j = \mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j$,
$$\|\mathbf{x}_\star - \mathbf{x}_{j+1}\|_{\mathbf{A}} \le
\sqrt{\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 - 0.99\,\gamma_j\|\mathbf{r}_j\|^2 +
2\gamma_j\|\mathbf{p}_j\|\|\mathbf{g}_j\|} + \sqrt{a'}\,\|\mathbf{e}^x_j\| \,.$$
Proof: $\mathbf{w} = \mathbf{x}_\star - \mathbf{x}_j - \gamma_j\mathbf{p}_j$ has
$\|\mathbf{w}\|_{\mathbf{A}}^2 = E_j^2 - 2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_j -
2\gamma_j\mathbf{p}_j^{\mathsf{T}}\mathbf{g}_j + \gamma_j^2\mathbf{p}_j^{\mathsf{T}}\mathbf{A}
\mathbf{p}_j$ (G1, G2), and $\mathbf{x}_\star - \mathbf{x}_{j+1} = \mathbf{w} - \mathbf{e}^x_j$
with $\|\mathbf{A}\mathbf{w}\|^2 \le a'\|\mathbf{w}\|_{\mathbf{A}}^2$. Difficulty: easy. -/
theorem quadForm_sub_x_succ_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x (j + 1)) ≤
      (Real.sqrt (quadForm C.A (xs - C.x j) - 99 / 100 * (C.γ j * C.ρ j ^ 2) +
          2 * (C.γ j * ‖WithLp.toLp 2 (C.p j)‖) * ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖) +
        Real.sqrt a' * ‖WithLp.toLp 2 (C.ex j)‖) ^ 2 := by
  sorry

/-! ### The joint induction -/

/-- **The residual gap, a priori, in $\|\mathbf{b}\|$**: under (H), for $j \le k$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j\| \le 12\,j\,\varepsilon\,\kappa\,
\|\mathbf{b}\| .$$
No solution is needed in the statement. The research note has $9$.
Proof: the private induction `gapErrorInduction` of this file. Difficulty: moderate. -/
theorem norm_sub_mulVec_x_sub_r_le_norm_b {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖ ≤
      12 * j * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  sorry

/-- **The computed estimator bounds the computed run's error decrease (one-sided ER3)**: under
(H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j \le k$,
$$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le \|\mathbf{x}_\star\|_{\mathbf{A}}^2 -
0.99\sum_{i<j}\gamma_i\|\mathbf{r}_i\|^2 + 25\,j^2\varepsilon\kappa\,\frac{\|\mathbf{b}\|^2}{a}
\,.$$
The exact relation, for the model, is `NLAlib.CGRun.quadForm_backwardH_sub_cgIterate_eq`; this
is the computed run's own error. The research note has $0.999$ and $30$.
Proof: the private induction `gapErrorInduction` of this file. Difficulty: moderate. -/
theorem quadForm_sub_x_le_sub_sum {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤ quadForm C.A xs -
      99 / 100 * ∑ i ∈ Finset.range j, C.γ i * C.ρ i ^ 2 +
        25 * j ^ 2 * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a) := by
  sorry

/-- **The computed run's $\mathbf{A}$-norm error, a priori**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $j \le k$,
$\|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}^2 \le 1.001\,\|\mathbf{x}_\star\|_{\mathbf{A}}^2$.
Proof: `NLAlib.CGRun.quadForm_sub_x_le_sub_sum` and
$\|\mathbf{b}\|^2/a \le \kappa\|\mathbf{x}_\star\|_{\mathbf{A}}^2$ (from
$\|\mathbf{A}\mathbf{x}_\star\|^2 \le a'\|\mathbf{x}_\star\|_{\mathbf{A}}^2$), $25j^2\varepsilon
\kappa^2 \le 2.5 \cdot 10^{-4}$. Difficulty: easy. -/
theorem quadForm_sub_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤ (1 + 1 / 1000) * quadForm C.A xs := by
  sorry

/-- **The computed iterates, a priori**: under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$
and $j \le k$,
$$\|\mathbf{x}_j\| \le 1.001\Bigl(\|\mathbf{x}_\star\| +
\frac{\|\mathbf{x}_\star\|_{\mathbf{A}}}{\sqrt{a}}\Bigr) ,$$
the exact-arithmetic bound on $\max_j\|\mathbf{x}_j\|$ through the $\mathbf{A}$-norm.
[MeurantStrakos2006, §5.4] assert $\|\mathbf{x}_j\| \le 2\|\mathbf{x}_\star\|$ "to within a
small error" for finite-precision CG without proof; this is $\sqrt{\kappa}$ weaker and proved.
Proof: $\|\mathbf{x}_j\| \le \|\mathbf{x}_\star\| + \|\mathbf{x}_\star - \mathbf{x}_j\|_{\mathbf{A}}
/\sqrt{a}$ and `NLAlib.CGRun.quadForm_sub_x_le`. Difficulty: easy. -/
theorem norm_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    ‖WithLp.toLp 2 (C.x j)‖ ≤
      (1 + 1 / 1000) * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  sorry

/-! ### The residual gap -/

/-- **The residual gap, a priori**: under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
with $M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k - \mathbf{r}_k\| \le 11\,k\,\varepsilon\,a'M .$$
[Greenbaum1997SIMAX]; [StrakosTichy2002, (7.16)], there with $\|\mathbf{x}_\star\| +
\max_j\|\mathbf{x}_j\|$ (a posteriori) and $+O(\varepsilon^2)$; here
$\max_j\|\mathbf{x}_j\| \le 1.001M$ is proved (`NLAlib.CGRun.norm_x_le`).
Proof: `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le` with $\|\mathbf{x}_j\| \le 1.001M$,
$\gamma_j\|\mathbf{p}_j\| \le 1.02(\|\mathbf{x}_j\| + \|\mathbf{x}_{j+1}\|)$ (the iterate
update), $\rho_j \le \|\mathbf{A}(\mathbf{x}_\star - \mathbf{x}_j)\| + \|\mathbf{g}_j\| \le
1.002a'M$. Difficulty: easy. -/
theorem norm_sub_mulVec_x_sub_r_le_energy {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  sorry

/-- **The residual gap, a priori, in $\|\mathbf{x}_\star\|$**: under (H), for
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k - \mathbf{r}_k\| \le 22\,k\,\varepsilon\sqrt{\kappa}\,
a'\|\mathbf{x}_\star\| .$$
$\sqrt{\kappa}$ worse than the folklore $O(k\varepsilon)a'\|\mathbf{x}_\star\|$, which rests on
a Euclidean monotonicity of the errors not known in finite precision. The research note has $20$.
Proof: `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy` and
$\|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a} \le \sqrt{\kappa}\|\mathbf{x}_\star\|$. Difficulty:
easy. -/
theorem norm_sub_mulVec_x_sub_r_le_norm_sol {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      22 * k * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
  sorry

/-- **The true residual**: under (H), for $\mathbf{A}\mathbf{x}_\star = \mathbf{b}$, with
$\kappa' = 2\kappa + 1$, $q = (\sqrt{\kappa'} - 1)/(\sqrt{\kappa'} + 1)$ and
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le 2\sqrt{\kappa'}\,q^k\|\mathbf{b}\| +
11\,k\,\varepsilon\,a'M .$$
Proof: $\mathbf{b} - \mathbf{A}\mathbf{x}_k = \mathbf{r}_k + \mathbf{g}_k$,
`NLAlib.CGRun.ρ_le_chebyshev`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy`. Difficulty:
easy. -/
theorem norm_sub_mulVec_x_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      2 * Real.sqrt (2 * (a' / a) + 1) *
          ((Real.sqrt (2 * (a' / a) + 1) - 1) / (Real.sqrt (2 * (a' / a) + 1) + 1)) ^ k *
          ‖WithLp.toLp 2 C.b‖ +
        11 * k * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  sorry

/-! ### Attainable accuracy -/

/-- **The computed residual at gap level**: under (H), for $\varepsilon, \delta > 0$ and
$k^\star(\kappa, \varepsilon, \delta) \le j \le k$ (`NLAlib.cgKStar`),
$\|\mathbf{r}_j\| \le 8\delta\varepsilon\|\mathbf{b}\|$. With $\delta = 1$ this is the level of
every a priori gap bound ($\|\mathbf{b}\| \le a'M$); with $\delta < 1$ it is the $\delta$-form
of "the computed residual is negligible", the only true one: exact arithmetic is an admissible
run with zero gap.
Proof: `NLAlib.CGRun.ρ_le_chebyshev` and `NLAlib.pow_cgKStar_le`. Difficulty: easy. -/
theorem ρ_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) (hε : 0 < C.ε) {δ : ℝ}
    (hδ : 0 < δ) {j : ℕ} (hkj : cgKStar (a' / a) C.ε δ ≤ j) (hj : j ≤ k) :
    C.ρ j ≤ 8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by
  sorry

/-- **Past $k^\star(\delta)$ the true residual is the gap** up to $\delta$ times the gap's
level: under (H), for $\varepsilon, \delta > 0$ and $k^\star(\kappa, \varepsilon, \delta) \le j
\le k$,
$$\bigl\lvert\|\mathbf{b} - \mathbf{A}\mathbf{x}_j\| -
\|\mathbf{b} - \mathbf{A}\mathbf{x}_j - \mathbf{r}_j\|\bigr\rvert \le
8\delta\varepsilon\|\mathbf{b}\| .$$
Proof: the triangle inequality and `NLAlib.CGRun.ρ_le_of_cgKStar_le`. Difficulty: easy. -/
theorem abs_norm_sub_mulVec_x_sub_norm_gap_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) {δ : ℝ} (hδ : 0 < δ) {j : ℕ} (hkj : cgKStar (a' / a) C.ε δ ≤ j)
    (hj : j ≤ k) :
    |‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j)‖ - ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x j - C.r j)‖| ≤
      8 * δ * C.ε * ‖WithLp.toLp 2 C.b‖ := by
  sorry

/-- **Attainable accuracy at a prescribed step**: under (H), for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k^\star(\kappa, \varepsilon, 1)$, with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (11k + 8)\,\varepsilon\,a'M .$$
The bound grows linearly in $k$: the term $\mathbf{A}\mathbf{e}^x_j$ of the gap does not decay
(as in [Greenbaum1997SIMAX]), so the best step is $k^\star$
(`NLAlib.CGRun.norm_sub_mulVec_x_cgKStar_le`).
Proof: `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_energy` and
$\|\mathbf{b}\| \le a'\|\mathbf{x}_\star\|$. Difficulty: easy. -/
theorem norm_sub_mulVec_x_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      (11 * k + 8) * C.ε * a' * (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) :=
  by sorry

/-- **Attainable accuracy in $\|\mathbf{x}_\star\|$**: under (H), for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k^\star(\kappa, \varepsilon, 1)$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (22k + 8)\,\varepsilon\sqrt{\kappa}\,a'
\|\mathbf{x}_\star\| .$$
Proof: `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_sol`.
Difficulty: easy. -/
theorem norm_sub_mulVec_x_le_norm_sol_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤
      (22 * k + 8) * C.ε * Real.sqrt (a' / a) * a' * ‖WithLp.toLp 2 xs‖ := by
  sorry

/-- **Attainable accuracy in $\|\mathbf{b}\|$**: under (H), for $\varepsilon > 0$ and
$k \ge k^\star(\kappa, \varepsilon, 1)$,
$\|\mathbf{b} - \mathbf{A}\mathbf{x}_k\| \le (12k + 8)\,\varepsilon\,\kappa\,\|\mathbf{b}\|$.
The research note has $9k + 8$.
Proof: `NLAlib.CGRun.ρ_le_of_cgKStar_le`, `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le_norm_b`.
Difficulty: easy. -/
theorem norm_sub_mulVec_x_le_norm_b_of_cgKStar_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a') (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hε : 0 < C.ε) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k)‖ ≤ (12 * k + 8) * C.ε * (a' / a) * ‖WithLp.toLp 2 C.b‖ := by
  sorry

/-- **The forward error at a prescribed step**: under (H), for $\varepsilon > 0$,
$\mathbf{A}\mathbf{x}_\star = \mathbf{b}$ and $k \ge k^\star(\kappa, \varepsilon, 1)$, with
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$\|\mathbf{x}_\star - \mathbf{x}_k\| \le (11k + 8)\,\varepsilon\,\kappa\,M$.
Proof: $\|\mathbf{x}_\star - \mathbf{x}_k\| \le \|\mathbf{b} - \mathbf{A}\mathbf{x}_k\|/a$ and
`NLAlib.CGRun.norm_sub_mulVec_x_le_of_cgKStar_le`. Difficulty: easy. -/
theorem norm_sub_x_le_of_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5) (hε : 0 < C.ε) {xs : Fin n → ℝ}
    (hx : C.A *ᵥ xs = C.b) (hk : cgKStar (a' / a) C.ε 1 ≤ k) :
    ‖WithLp.toLp 2 (xs - C.x k)‖ ≤
      (11 * k + 8) * C.ε * (a' / a) *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  sorry

/-- **Attainable accuracy, a priori**: for $\varepsilon > 0$, $\mathbf{A}\mathbf{x}_\star =
\mathbf{b}$, $k \ge k^\star = k^\star(\kappa, \varepsilon, 1)$ and (H) **at $k^\star$ only**,
$(k^\star)^3\varepsilon\kappa^2 \le 10^{-5}$, with $\kappa' = 2\kappa + 1$,
$\ell = \ln(\sqrt{\kappa'}/(4\varepsilon))$ and
$M = \|\mathbf{x}_\star\| + \|\mathbf{x}_\star\|_{\mathbf{A}}/\sqrt{a}$,
$$\|\mathbf{b} - \mathbf{A}\mathbf{x}_{k^\star}\| \le
\Bigl(\frac{11}{2}(\sqrt{\kappa'} + 1)\,\ell + 19\Bigr)\varepsilon\,a'M ,$$
an attainable relative residual of order $\kappa\ln(1/\varepsilon)\,\varepsilon$ (one
$\sqrt{\kappa}$ from $M \le (1 + \sqrt{\kappa})\|\mathbf{x}_\star\|$, one from
$k^\star \propto \sqrt{\kappa}$). `NLAlib.cgKStar_cube_mul_le` gives the hypothesis at $k^\star$
from $\kappa^{7/2}\varepsilon\ell^3 \le 7 \cdot 10^{-7}$. No printed source; the research note has
$\tfrac{11}{2}\sqrt{\kappa'}\ell + 19$.
Proof: `NLAlib.CGRun.norm_sub_mulVec_x_le_of_cgKStar_le` on `C.take k⋆`
(`NLAlib.cgKStar_pos`) and $k^\star \le \tfrac12(\sqrt{\kappa'} + 1)\ell + 1$. Difficulty: easy. -/
theorem norm_sub_mulVec_x_cgKStar_le {a a' : ℝ} (ha : 0 < a) (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hε : 0 < C.ε) (hk : cgKStar (a' / a) C.ε 1 ≤ k)
    (hsmall : (cgKStar (a' / a) C.ε 1 : ℝ) ^ 3 * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x (cgKStar (a' / a) C.ε 1))‖ ≤
      (11 / 2 * (Real.sqrt (2 * (a' / a) + 1) + 1) *
          Real.log (Real.sqrt (2 * (a' / a) + 1) / (4 * 1 * C.ε)) + 19) * C.ε * a' *
        (‖WithLp.toLp 2 xs‖ + Real.sqrt (quadForm C.A xs) / Real.sqrt a) := by
  sorry

end CGRun

end NLAlib
