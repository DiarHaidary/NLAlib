/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.LanczosRun

/-!
# Local errors of a finite-precision Lanczos run

For a run `L : NLAlib.LanczosRun n k` (the recurrence in Paige's ordering A(1) with bounded local
errors, accuracy parameter $\varepsilon$, $k\varepsilon \le 1/100$) the computed quantities stay
bounded by a multiple of $\|\mathbf{H}\|_2$ that grows at most linearly in the step, and the
computed vectors satisfy the three-term recurrence up to a residual of order
$j\varepsilon\|\mathbf{H}\|_2$, with consecutive vectors nearly orthogonal in the same sense.

Steps are indexed from $0$ as the columns of the computed basis: step $j < k$ is the paper's step
$j + 1$, it reads $\mathbf{v}_{j+1}$ (`L.v (j + 1)`) and produces $\mathbf{v}_{j+2}$. The bound on
$\lvert\|\mathbf{v}_{j+1}\|^2 - 1\rvert$ is the field `NLAlib.LanczosRun.abs_norm_v_sq_sub_one_le`.

No printed source: the maintainer's draft (T. Chen, *A simple stability analysis of Lanczos in
finite precision*), `lem:coefficients` and `thm:local-errors`; constants differ (design note
`docs/design/Krylov-LanczosRounding.md`, §3.5).

## Main definitions

* `NLAlib.LanczosRun.recurrenceError`: the residual $\mathbf{f}$ of the three-term recurrence.
* `NLAlib.LanczosRun.adjacentInner`: the inner product $\beta\,\mathbf{v}^{\mathsf{T}}\mathbf{v}'$
  of consecutive vectors.

## Main results

* `NLAlib.LanczosRun.β_le`, `NLAlib.LanczosRun.norm_u_le`, `NLAlib.LanczosRun.norm_w_le`,
  `NLAlib.LanczosRun.abs_α_le`, `NLAlib.LanczosRun.norm_z_le`: the a priori coefficient bounds.
* `NLAlib.LanczosRun.recurrenceError_eq`: the residual is minus the sum of the local errors.
* `NLAlib.LanczosRun.norm_recurrenceError_le`: the local error bound on the residual.
* `NLAlib.LanczosRun.abs_adjacentInner_le`: local orthogonality.
-/

@[expose] public section

namespace NLAlib

open scoped Matrix

namespace LanczosRun

variable {n k : ℕ} (L : LanczosRun n k)

/-- The **residual of the three-term recurrence** at step $j$ (0-based):
$\mathbf{f}_j = \mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j - \alpha_{j+1}\mathbf{v}_{j+1}
- \beta_{j+1}\mathbf{v}_{j+2}$, the paper's $\mathbf{f}_{j+1}$. At a terminal last step
$\beta_k = 0$ and $\mathbf{v}_{k+1}$ does not enter. -/
noncomputable def recurrenceError (j : ℕ) : Fin n → ℝ :=
  L.H *ᵥ L.v (j + 1) - L.β j • L.v j - L.α (j + 1) • L.v (j + 1) - L.β (j + 1) • L.v (j + 2)

/-- The **inner product of consecutive Lanczos vectors** at step $j$ (0-based):
$\mathbf{v}_{j+1}^{\mathsf{T}}(\beta_{j+1}\mathbf{v}_{j+2})$, the paper's $p_{j+1}$. -/
noncomputable def adjacentInner (j : ℕ) : ℝ :=
  L.v (j + 1) ⬝ᵥ (L.β (j + 1) • L.v (j + 2))

/-! ### A priori coefficient bounds -/

/-- **The off-diagonal coefficients grow at most linearly**: for $j \le k$,
$\beta_j \le \tfrac54\, j\,\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients`, proves $\beta_j \le 4j\|\mathbf{A}\|$
(Step 3); the recurrence $\beta_j \le (1 + 8\varepsilon)(\beta_{j-1} + (1+\varepsilon)
\|\mathbf{H}\|_2)$ used here carries less slack.
Proof: induction on that scalar recurrence, which bounds $\beta_{j+1}$ by $\|\mathbf{z}_{j+1}\|$
(normalisation), $\|\mathbf{z}_{j+1}\|$ by $\|\mathbf{w}_{j+1}\|$ (the exact projection does not
increase the norm) and $\|\mathbf{w}_{j+1}\|$ by $\beta_j$; easy. -/
theorem β_le {j : ℕ} (hj : j ≤ k) : L.β j ≤ 5 / 4 * j * specNorm L.H := by
  sorry

/-- **The computed products are bounded**: for $j < k$,
$\|\mathbf{u}_{j+1}\| \le \tfrac{21}{20}\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 2), prints
$2\|\mathbf{A}\|$. -/
theorem norm_u_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.u (j + 1))‖ ≤ 21 / 20 * specNorm L.H := by
  sorry

/-- **The first updates are bounded**: for $j < k$,
$\|\mathbf{w}_{j+1}\| \le \tfrac54 (j + 1)\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 4), prints $5j\|\mathbf{A}\|$
in its 1-based indexing. -/
theorem norm_w_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.w (j + 1))‖ ≤ 5 / 4 * (j + 1) * specNorm L.H := by
  sorry

/-- **The diagonal coefficients are bounded**: for $j < k$,
$\lvert\alpha_{j+1}\rvert \le \tfrac43 (j + 1)\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 4), prints
$6j\|\mathbf{A}\|$ in its 1-based indexing. -/
theorem abs_α_le {j : ℕ} (hj : j < k) : |L.α (j + 1)| ≤ 4 / 3 * (j + 1) * specNorm L.H := by
  sorry

/-- **The unnormalised next vectors are bounded**: for $j < k$,
$\|\mathbf{z}_{j+1}\| \le \tfrac43 (j + 1)\|\mathbf{H}\|_2$.
No printed source; the maintainer's draft, `lem:coefficients` (Step 4), prints
$7j\|\mathbf{A}\|$ in its 1-based indexing. -/
theorem norm_z_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.z (j + 1))‖ ≤ 4 / 3 * (j + 1) * specNorm L.H := by
  sorry

/-! ### Local error bounds -/

/-- The residual of the recurrence is minus the sum of the four vector local errors:
$\mathbf{f}_j = -(\mathbf{e}^u_{j+1} + \mathbf{e}^w_{j+1} + \mathbf{e}^z_{j+1}
+ \boldsymbol{\delta}_{j+1})$ for $j < k$. -/
theorem recurrenceError_eq {j : ℕ} (hj : j < k) :
    L.recurrenceError j = -(L.eu (j + 1) + L.ew (j + 1) + L.ez (j + 1) + L.δ (j + 1)) := by
  sorry

/-- **Local error bound for finite-precision Lanczos** (Paige): the computed vectors satisfy the
three-term recurrence up to a small residual, for $j < k$,
$$\|\mathbf{H}\mathbf{v}_{j+1} - \beta_j\mathbf{v}_j - \alpha_{j+1}\mathbf{v}_{j+1}
- \beta_{j+1}\mathbf{v}_{j+2}\| \le 6\,(j + 1)\,\varepsilon\,\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `thm:local-errors`, states
$\|\mathbf{f}_j\| \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $700j$); the
constant here comes from the sharper coefficient bounds. [Paige1976, §2–3] has bounds of this
kind, from floating-point arithmetic directly.
Proof: `NLAlib.LanczosRun.recurrenceError_eq`, the triangle inequality, the five error fields
and the coefficient bounds; easy.
Result: lanczos-local-errors -/
theorem norm_recurrenceError_le {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (L.recurrenceError j)‖ ≤ 6 * (j + 1) * L.ε * specNorm L.H := by
  sorry

/-- The inner product of consecutive vectors in terms of the local errors: for $j < k$,
$p_j = -e^\alpha_{j+1} - (\|\mathbf{v}_{j+1}\|^2 - 1)\alpha_{j+1}
+ \mathbf{v}_{j+1}^{\mathsf{T}}\mathbf{e}^z_{j+1} + \mathbf{v}_{j+1}^{\mathsf{T}}
\boldsymbol{\delta}_{j+1}$. -/
theorem adjacentInner_eq {j : ℕ} (hj : j < k) :
    L.adjacentInner j = -L.eα (j + 1) - (‖WithLp.toLp 2 (L.v (j + 1))‖ ^ 2 - 1) * L.α (j + 1)
      + L.v (j + 1) ⬝ᵥ L.ez (j + 1) + L.v (j + 1) ⬝ᵥ L.δ (j + 1) := by
  sorry

/-- **Local orthogonality of finite-precision Lanczos** (Paige): consecutive computed vectors
are nearly orthogonal, for $j < k$,
$$\lvert\beta_{j+1}\,\mathbf{v}_{j+1}^{\mathsf{T}}\mathbf{v}_{j+2}\rvert
\le 7\,(j + 1)\,\varepsilon\,\|\mathbf{H}\|_2 \,.$$
No printed source; the maintainer's draft, `thm:local-errors`, states
$\lvert p_j\rvert \lesssim_k \varepsilon\|\mathbf{A}\|$ (its formalization: $1200j$).
Proof: `NLAlib.LanczosRun.adjacentInner_eq`, Cauchy–Schwarz and the coefficient bounds; easy.
Result: lanczos-local-orthogonality -/
theorem abs_adjacentInner_le {j : ℕ} (hj : j < k) :
    |L.adjacentInner j| ≤ 7 * (j + 1) * L.ε * specNorm L.H := by
  sorry

end LanczosRun

end NLAlib
