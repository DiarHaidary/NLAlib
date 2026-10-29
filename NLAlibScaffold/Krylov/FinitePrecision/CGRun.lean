/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Krylov.FinitePrecision.NormalizedBackward
public import NLAlibScaffold.Krylov.LinearSystems.CGTridiagonal

/-!
# A conjugate gradient run with bounded local errors

`NLAlib.CGRun n k` is $k$ steps of the Hestenes–Stiefel recurrence from $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{p}_0 = \mathbf{b}$, for a real symmetric $\mathbf{A}$, with a local error
in each operation bounded relative to its operands by one accuracy parameter $\varepsilon$
(0-based, step $j < k$):
$$\nu_j = \|\mathbf{r}_j\|^2(1 + \theta_j),\quad
\mathbf{s}_j = \mathbf{A}\mathbf{p}_j + \mathbf{e}^s_j,\quad
\mu_j = \mathbf{p}_j^{\mathsf{T}}\mathbf{s}_j + e^\mu_j,\quad
\gamma_j = \frac{\nu_j}{\mu_j}(1 + \eta^\gamma_j),$$
$$\mathbf{x}_{j+1} = \mathbf{x}_j + \gamma_j\mathbf{p}_j + \mathbf{e}^x_j,\quad
\mathbf{r}_{j+1} = \mathbf{r}_j - \gamma_j\mathbf{s}_j + \mathbf{e}^r_j,\quad
\delta_j = \frac{\nu_{j+1}}{\nu_j}(1 + \eta^\delta_j),\quad
\mathbf{p}_{j+1} = \mathbf{r}_{j+1} + \delta_j\mathbf{p}_j + \mathbf{e}^p_j .$$
It is the interface between the rounding-error analysis of the conjugate gradient program
(`NLAlibScaffold/Krylov/LinearSystems/CGRounding.lean`) and the stability analysis.

The **Lanczos data of the run** (`NLAlib.CGRun.toNormalizedLanczosData`) are the normalised
residuals $\bar{\mathbf{v}}_{j+1} = (-1)^j\mathbf{r}_j/\|\mathbf{r}_j\|$ with the tridiagonal
matrix `NLAlib.cgTridiagonal` of the computed $\gamma_j$ and the norms $\rho_j =
\|\mathbf{r}_j\|$ of the computed residuals. The local errors of this datum (Lemmas A and B of the
design note) are bounded a posteriori in terms of three run certificates: $\Pi \ge
\|\mathbf{p}_j\|/\|\mathbf{r}_j\|$, $K \ge \|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2/
\|\mathbf{r}_j\|^2$, and $B$ bounding the coefficients $\beta_{j+1} =
\rho_{j+1}/(\gamma_j\rho_j)$ and $\delta_j/\gamma_j$ for $j + 1 < k$ (the last pair,
$\beta_k$ and $\delta_{k-1}/\gamma_{k-1}$, does not enter the local errors of $k$ steps). The
a priori bounds on the certificates are in
`NLAlibScaffold/Krylov/FinitePrecision/CGBackward.lean`.

Research branch `research/hscg-fp`. Design: `docs/design/research/Krylov-CGRounding.md` (§3, §6).
Constants are unoptimised and carry a margin over the hand derivation of the research note
`docs/design/research/HSCG-FiniteP.md` §§2.4–2.5; they are to be re-derived in the proofs.

## Main definitions

* `NLAlib.CGRun`: a run of $k$ steps with accuracy parameter $\varepsilon$.
* `NLAlib.CGRun.toLanczosData`, `NLAlib.CGRun.toNormalizedLanczosData`: its Lanczos data.
* `NLAlib.CGRun.backwardH`: the backward model of the run.

## Main results

* `NLAlib.CGRun.tridiagonal_toLanczosData`: the tridiagonal matrix is `NLAlib.cgTridiagonal`.
* `NLAlib.CGRun.norm_recurrenceError_le` (Lemma A),
  `NLAlib.CGRun.abs_adjacentInner_le` (Lemma B): the local errors.
* `NLAlib.CGRun.frobNorm_backwardH_sub_dilatedH_le_of_certificates`: the a posteriori model.
* `NLAlib.CGRun.norm_r_le_two_mul_norm_p`, `NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`:
  the next division succeeds.
* `NLAlib.CGRun.norm_sub_mulVec_x_sub_r_le`: the residual gap.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **A conjugate gradient run with bounded local errors**: $k \ge 1$ steps of the
Hestenes–Stiefel recurrence from $\mathbf{x}_0 = \mathbf{0}$ for a real symmetric $\mathbf{A}$,
every operation exact up to an error bounded by $\varepsilon$ times its operands (the normwise
standard model), $\nu_j > 0$ and $\mu_j > 0$ at every step taken, and $k\varepsilon \le 1/100$.
The computed $\nu_k$ after the last step may be $0$ (the program stops there). -/
structure CGRun (n k : ℕ) where
  /-- The matrix. -/
  A : Matrix (Fin n) (Fin n) ℝ
  /-- The right-hand side. -/
  b : Fin n → ℝ
  /-- The iterates $\mathbf{x}_j$. -/
  x : ℕ → Fin n → ℝ
  /-- The updated residuals $\mathbf{r}_j$. -/
  r : ℕ → Fin n → ℝ
  /-- The search directions $\mathbf{p}_j$. -/
  p : ℕ → Fin n → ℝ
  /-- The products $\mathbf{s}_j$. -/
  s : ℕ → Fin n → ℝ
  /-- The computed squared residual norms $\nu_j$. -/
  ν : ℕ → ℝ
  /-- The computed curvatures $\mu_j$. -/
  μ : ℕ → ℝ
  /-- The step lengths $\gamma_j$. -/
  γ : ℕ → ℝ
  /-- The direction coefficients $\delta_j$. -/
  δ : ℕ → ℝ
  /-- The error of the product. -/
  es : ℕ → Fin n → ℝ
  /-- The relative error of the squared residual norm. -/
  θ : ℕ → ℝ
  /-- The error of the curvature. -/
  eμ : ℕ → ℝ
  /-- The relative error of the step length. -/
  eγ : ℕ → ℝ
  /-- The error of the iterate update. -/
  ex : ℕ → Fin n → ℝ
  /-- The error of the residual update. -/
  er : ℕ → Fin n → ℝ
  /-- The relative error of the direction coefficient. -/
  eδ : ℕ → ℝ
  /-- The error of the direction update. -/
  ep : ℕ → Fin n → ℝ
  /-- The accuracy parameter. -/
  ε : ℝ
  /-- The matrix is symmetric. -/
  transpose_A : Aᵀ = A
  /-- The accuracy parameter is nonnegative. -/
  ε_nonneg : 0 ≤ ε
  /-- At least one step. -/
  k_pos : 0 < k
  /-- Small accuracy parameter. -/
  k_mul_ε_le : (k : ℝ) * ε ≤ 1 / 100
  /-- $\mathbf{x}_0 = \mathbf{0}$. -/
  x_zero : x 0 = 0
  /-- $\mathbf{r}_0 = \mathbf{b}$. -/
  r_zero : r 0 = b
  /-- $\mathbf{p}_0 = \mathbf{b}$. -/
  p_zero : p 0 = b
  /-- The computed squared residual norm. -/
  ν_eq : ∀ j ≤ k, ν j = ‖WithLp.toLp 2 (r j)‖ ^ 2 * (1 + θ j)
  /-- Its relative error. -/
  abs_θ_le : ∀ j ≤ k, |θ j| ≤ ε
  /-- No stop before the last step. -/
  ν_pos : ∀ j < k, 0 < ν j
  /-- The computed product. -/
  s_eq : ∀ j < k, s j = A *ᵥ p j + es j
  /-- The product error. -/
  norm_es_le : ∀ j < k,
    ‖WithLp.toLp 2 (es j)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 (p j)‖
  /-- The computed curvature. -/
  μ_eq : ∀ j < k, μ j = p j ⬝ᵥ s j + eμ j
  /-- The curvature error. -/
  abs_eμ_le : ∀ j < k, |eμ j| ≤ ε * ‖WithLp.toLp 2 (p j)‖ * ‖WithLp.toLp 2 (s j)‖
  /-- The curvature is positive at every step taken (the division succeeded). -/
  μ_pos : ∀ j < k, 0 < μ j
  /-- The step length. -/
  γ_eq : ∀ j < k, γ j = ν j / μ j * (1 + eγ j)
  /-- Its relative error. -/
  abs_eγ_le : ∀ j < k, |eγ j| ≤ ε
  /-- The iterate update. -/
  x_succ : ∀ j < k, x (j + 1) = x j + γ j • p j + ex j
  /-- The iterate update error. -/
  norm_ex_le : ∀ j < k, ‖WithLp.toLp 2 (ex j)‖ ≤
    ε * (‖WithLp.toLp 2 (x j)‖ + |γ j| * ‖WithLp.toLp 2 (p j)‖)
  /-- The residual update. -/
  r_succ : ∀ j < k, r (j + 1) = r j - γ j • s j + er j
  /-- The residual update error. -/
  norm_er_le : ∀ j < k, ‖WithLp.toLp 2 (er j)‖ ≤
    ε * (‖WithLp.toLp 2 (r j)‖ + |γ j| * ‖WithLp.toLp 2 (s j)‖)
  /-- The direction coefficient. -/
  δ_eq : ∀ j < k, δ j = ν (j + 1) / ν j * (1 + eδ j)
  /-- Its relative error. -/
  abs_eδ_le : ∀ j < k, |eδ j| ≤ ε
  /-- The direction update. -/
  p_succ : ∀ j < k, p (j + 1) = r (j + 1) + δ j • p j + ep j
  /-- The direction update error. -/
  norm_ep_le : ∀ j < k, ‖WithLp.toLp 2 (ep j)‖ ≤
    ε * (‖WithLp.toLp 2 (r (j + 1))‖ + |δ j| * ‖WithLp.toLp 2 (p j)‖)

/-- **The computed curvature is positive** for a nonzero direction: if the spectrum of the
symmetric $\mathbf{A}$ lies in $[a, a']$, $a > 0$, $\mathbf{s} = \mathbf{A}\mathbf{p} +
\mathbf{e}$ with $\|\mathbf{e}\| \le \varepsilon\|\mathbf{A}\|_2\|\mathbf{p}\|$ and
$\lvert e'\rvert \le \varepsilon\|\mathbf{p}\|\|\mathbf{s}\|$, and $3\varepsilon a' \le a$, then
$\mathbf{p}^{\mathsf{T}}\mathbf{s} + e' > 0$. So the division by the computed
$\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p}$ succeeds. [StrakosTichy2002, (7.14)].
Proof: $\mathbf{p}^{\mathsf{T}}\mathbf{s} + e' \ge (a - \varepsilon a' -
\varepsilon(1+\varepsilon)a')\|\mathbf{p}\|^2$, with $\|\mathbf{A}\|_2 \le a'$ and
$\mathbf{p}^{\mathsf{T}}\mathbf{A}\mathbf{p} \ge a\|\mathbf{p}\|^2$ from the spectrum.
Difficulty: easy. -/
theorem dotProduct_add_pos_of_spectrum_subset_Icc {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : Aᵀ = A) {a a' ε : ℝ} (ha : 0 < a) (hs : spectrum ℝ A ⊆ Set.Icc a a') (hε : 0 ≤ ε)
    (hsmall : 3 * ε * a' ≤ a) {p e : Fin n → ℝ} {e' : ℝ} (hp : p ≠ 0)
    (he : ‖WithLp.toLp 2 e‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 p‖)
    (he' : |e'| ≤ ε * ‖WithLp.toLp 2 p‖ * ‖WithLp.toLp 2 (A *ᵥ p + e)‖) :
    0 < p ⬝ᵥ (A *ᵥ p + e) + e' := by
  sorry

namespace CGRun

variable {n k : ℕ} (C : CGRun n k)

/-- The norms of the computed residuals, $\rho_j = \|\mathbf{r}_j\|$. -/
noncomputable def ρ (j : ℕ) : ℝ :=
  ‖WithLp.toLp 2 (C.r j)‖

/-- The **Lanczos vectors of the run**, 1-based as `NLAlib.LanczosData`:
$\bar{\mathbf{v}}_0 = \mathbf{0}$,
$\bar{\mathbf{v}}_{j+1} = (-1)^j\mathbf{r}_j/\|\mathbf{r}_j\|$, and
$\bar{\mathbf{v}}_{j+1} = \mathbf{b}/\|\mathbf{b}\|$ if $\mathbf{r}_j = \mathbf{0}$ (only at the
last index, where it is multiplied by $\beta_k = 0$). -/
noncomputable def lanczosV (j : ℕ) : Fin n → ℝ :=
  if j = 0 then 0
  else if C.r (j - 1) = 0 then (‖WithLp.toLp 2 C.b‖⁻¹ : ℝ) • C.b
  else ((-1 : ℝ) ^ (j - 1) * (C.ρ (j - 1))⁻¹) • C.r (j - 1)

/-- The diagonal coefficients of the run's Lanczos data, 1-based: $\alpha_{j+1}$ is the
$(j, j)$ entry of `NLAlib.cgTridiagonal C.γ C.ρ k`. -/
noncomputable def lanczosα (j : ℕ) : ℝ :=
  (C.γ (j - 1))⁻¹ + if j ≤ 1 then 0 else (C.ρ (j - 1) / C.ρ (j - 2)) ^ 2 / C.γ (j - 2)

/-- The off-diagonal coefficients of the run's Lanczos data, 1-based:
$\beta_0 = 0$, $\beta_{j+1} = \rho_{j+1}/(\gamma_j\rho_j)$. -/
noncomputable def lanczosβ (j : ℕ) : ℝ :=
  if j = 0 then 0 else C.ρ j / (C.γ (j - 1) * C.ρ (j - 1))

/-- **The Lanczos data of a conjugate gradient run**: the normalised residuals with the
coefficients of `NLAlib.cgTridiagonal`. -/
noncomputable def toLanczosData : LanczosData n k where
  H := C.A
  v := C.lanczosV
  α := C.lanczosα
  β := C.lanczosβ
  transpose_H := C.transpose_A
  k_pos := C.k_pos
  v_zero := by simp [lanczosV]
  β_zero := by simp [lanczosβ]

/-- **The computed squared residual norm vanishes exactly with the residual**:
$\nu_j = 0 \iff \mathbf{r}_j = \mathbf{0}$, $j \le k$. This is a statement about the model
of computation without underflow (`NLAlib.CGRun.ν_eq`); in IEEE arithmetic
$\mathrm{fl}(\|\mathbf{r}\|^2)$ can underflow to $0$ with $\mathbf{r} \ne \mathbf{0}$.
Proof: `C.ν_eq` and $1 + \theta_j \ge 1 - \varepsilon > 0$. Difficulty: easy. -/
theorem ν_eq_zero_iff {j : ℕ} (hj : j ≤ k) : C.ν j = 0 ↔ C.r j = 0 := by
  sorry

/-- The step lengths are positive. Proof: `C.γ_eq`, `C.ν_pos`, `C.μ_pos`, $\varepsilon < 1$.
Difficulty: easy. -/
theorem γ_pos {j : ℕ} (hj : j < k) : 0 < C.γ j := by
  sorry

/-- The Lanczos vectors of the run are unit vectors. Proof: `C.ν_eq_zero_iff` and `C.ν_pos` give
$\mathbf{r}_0 = \mathbf{b} \ne \mathbf{0}$; each branch of `NLAlib.CGRun.lanczosV` is normalised.
Difficulty: easy. -/
theorem norm_lanczosV {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ k + 1) :
    ‖WithLp.toLp 2 (C.lanczosV j)‖ = 1 := by
  sorry

/-- The coefficients $\beta_j$ of the run are nonnegative. Proof: `C.γ_pos`. Difficulty: easy. -/
theorem lanczosβ_nonneg {j : ℕ} (hj : j ≤ k) : 0 ≤ C.lanczosβ j := by
  sorry

/-- The coefficients $\beta_j$, $1 \le j < k$, are positive. Proof: `C.γ_pos` and
$\mathbf{r}_j \ne \mathbf{0}$ (`C.ν_pos`, `C.ν_eq_zero_iff`). Difficulty: easy. -/
theorem lanczosβ_pos {j : ℕ} (h1 : 1 ≤ j) (h2 : j < k) : 0 < C.lanczosβ j := by
  sorry

/-- **The run as normalised Lanczos data** (`NLAlib.NormalizedLanczosData`). -/
noncomputable def toNormalizedLanczosData : NormalizedLanczosData n k :=
  { C.toLanczosData with
    norm_v := fun _ h1 h2 => C.norm_lanczosV h1 h2
    β_nonneg := fun _ hj => C.lanczosβ_nonneg hj
    β_pos := fun _ h1 h2 => C.lanczosβ_pos h1 h2 }

/-- The **backward model of the run**: `NLAlib.NormalizedLanczosData.backwardH` of its Lanczos
data. -/
noncomputable def backwardH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  C.toNormalizedLanczosData.backwardH

/-- The dilated matrix $\mathbf{I}_{k+1} \otimes \mathbf{A}$. -/
def dilatedH : Matrix (Fin n × Fin (k + 1)) (Fin n × Fin (k + 1)) ℝ :=
  Matrix.blockDiagonal fun _ => C.A

/-- The **dilated right-hand side** $(\mathbf{b}, \mathbf{0}, \dots, \mathbf{0})$: the start of
exact CG on the model, $\|\mathbf{b}\|$ times the dilated Lanczos start. -/
def dilatedRhs : Fin n × Fin (k + 1) → ℝ :=
  fun x => if (x.2 : ℕ) = 0 then C.b x.1 else 0

/-- **The tridiagonal matrix of the run is the CG tridiagonal matrix** of the computed step
lengths and residual norms. Proof: unfold; the cases of `NLAlib.cgTridiagonal` and
`NLAlib.LanczosData.tridiagonal` match entry by entry. Difficulty: easy. -/
theorem tridiagonal_toLanczosData : C.toLanczosData.tridiagonal = cgTridiagonal C.γ C.ρ k := by
  sorry

/-- The direction coefficient against the exact residual ratio:
$\lvert\delta_j - \rho_{j+1}^2/\rho_j^2\rvert \le 4\varepsilon\rho_{j+1}^2/\rho_j^2$, $j < k$.
Proof: `C.δ_eq`, `C.ν_eq` at $j$ and $j + 1$, $\varepsilon \le 1/100$. Difficulty: easy. -/
theorem abs_δ_sub_le {j : ℕ} (hj : j < k) :
    |C.δ j - C.ρ (j + 1) ^ 2 / C.ρ j ^ 2| ≤ 4 * C.ε * (C.ρ (j + 1) ^ 2 / C.ρ j ^ 2) := by
  sorry

/-- **The step length against the direction** (the computed Rayleigh quotient):
$\rho_j^2 \le \tfrac{21}{20}\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2$, $j < k$, i.e.
$\gamma_j^{-1} \le 1.05\|\mathbf{A}\|_2\pi_j^2$.
Proof: $\mu_j \le (1+\varepsilon)^2\|\mathbf{A}\|_2\|\mathbf{p}_j\|^2$ and
$\nu_j \ge (1-\varepsilon)\rho_j^2$. Difficulty: easy. -/
theorem ρ_sq_le {j : ℕ} (hj : j < k) :
    C.ρ j ^ 2 ≤ 21 / 20 * specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 := by
  sorry

/-- **Lemma A (recurrence error)**: with certificates $\|\mathbf{p}_j\| \le \Pi\rho_j$
($j < k$) and $\beta_{j+1}, \delta_j/\gamma_j \le B$ ($j + 1 < k$), the Lanczos data of the
run satisfy
$$\|\bar{\mathbf{f}}_j\| \le 8\varepsilon\bigl(\|\mathbf{A}\|_2(1 + \Pi)^2 + B\bigr),
\qquad j < k .$$
No residual ratio enters. No printed source; the research note `HSCG-FiniteP.md` §2.4, after
[GreenbaumLiuChen2021, (2.2)–(2.4)], who derive the perturbation term but do not bound it.
Proof: the exact identity $\mathbf{A}\mathbf{r}_j = (\gamma_j^{-1} + \delta_{j-1}/\gamma_{j-1})
\mathbf{r}_j - \gamma_j^{-1}\mathbf{r}_{j+1} - (\delta_{j-1}/\gamma_{j-1})\mathbf{r}_{j-1} +
\mathbf{g}_j$ in the computed data (eliminate $\mathbf{A}\mathbf{p}_j$ between the residual and
direction updates), normalise by $(-1)^j/\rho_j$, then the term table of the note; the
diagonal convention of `NLAlib.cgTridiagonal` adds $\le 3.2\varepsilon\,\delta_{j-1}/
\gamma_{j-1}$, and $\gamma_j^{-1} \le 1.05\|\mathbf{A}\|_2\pi_j^2$ (`C.ρ_sq_le`). Step $j$
uses $B$ only for $\beta_j$ and $\delta_{j-1}/\gamma_{j-1}$ (index $j - 1$, so $j - 1 + 1 < k$);
$\beta_{j+1}$ enters $\bar{\mathbf{f}}_j$ only through the exact cancellation
$\beta_{j+1}\bar{\mathbf{v}}_{j+2} = (-1)^{j+1}\mathbf{r}_{j+1}/(\gamma_j\rho_j)$.
Difficulty: hard (one identity, then about ten norm estimates). -/
theorem norm_recurrenceError_le {P B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) {j : ℕ} (hj : j < k) :
    ‖WithLp.toLp 2 (C.toLanczosData.recurrenceError j)‖ ≤
      8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B) := by
  sorry

/-- **The line search defect** [StrakosTichy2002, Theorem 9.1], a posteriori: with certificates
$\|\mathbf{p}_i\| \le \Pi\rho_i$ and $\|\mathbf{A}\|_2\gamma_i\|\mathbf{p}_i\|^2 \le K\rho_i^2$
($i \le j < k$),
$$\lvert\mathbf{p}_j^{\mathsf{T}}\mathbf{r}_{j+1}\rvert \le
5(j+1)\varepsilon(1 + \Pi + K)\rho_j^2 .$$
Strakoš and Tichý state it with $\kappa(\mathbf{A})$ and $+O(\varepsilon^2)$, using an imported
bound on residual ratios; in normalised form the multipliers telescope and no ratio enters.
Proof: $\tau_j = \delta_{j-1}\tau_{j-1} + M_j$ with
$\lvert M_j\rvert \le \varepsilon(4.1 + 2.1\pi_j + 2.1\kappa_j)\rho_j^2$ (the updates and
$\gamma_j\mu_j = \nu_j(1+\eta^\gamma_j)$), and
$\delta_{j-1}\rho_{j-1}^2 = \rho_j^2(1 + O(\varepsilon))$;
unroll. Difficulty: moderate. -/
theorem abs_p_dotProduct_r_succ_le {P K : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r (j + 1)| ≤ 5 * (j + 1) * C.ε * (1 + P + K) * C.ρ j ^ 2 := by
  sorry

/-- **Lemma B (local orthogonality is inherited)**: with the certificates of
`NLAlib.CGRun.norm_recurrenceError_le` ($B$ for $j + 1 < k$ only) and
$\|\mathbf{A}\|_2\gamma_j\|\mathbf{p}_j\|^2 \le K\rho_j^2$ ($j < k$), the adjacent inner
products of the run's Lanczos data satisfy
$$\lvert\bar p_j\rvert \le 16(j+1)\varepsilon\bigl(\|\mathbf{A}\|_2(1 + \Pi)^2 +
B(1 + \Pi + K)\bigr),\qquad j < k .$$
No printed source; the research note `HSCG-FiniteP.md` §2.5. The orthogonality
$\mathbf{r}_j \perp \mathbf{r}_{j+1}$ is not produced at step $j$: it is the previous one
transported by the conjugacy $\mathbf{p}_{j-1}^{\mathsf{T}}\mathbf{A}\mathbf{p}_j \approx 0$.
Proof: the recursion $\bar p_j = (1 + \eta_{j-1})\bar p_{j-1} + L_j$ (three identities in the
computed data, one use of $\mathbf{A}^{\mathsf{T}} = \mathbf{A}$), the bound on $L_j$ in which
only $\delta_{j-1}/\gamma_{j-1}$, $\gamma_j^{-1}$, $\beta_j$ occur (not $\alpha_{j+1}$,
$\beta_{j+1}$: this is what keeps the a priori hypothesis at $\kappa^2$), and
`NLAlib.CGRun.abs_p_dotProduct_r_succ_le`. Difficulty: hard (the risky step of the design). -/
theorem abs_adjacentInner_le {P K B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) {j : ℕ} (hj : j < k) :
    |C.toLanczosData.adjacentInner j| ≤
      16 * (j + 1) * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K)) := by
  sorry

/-- **The a posteriori backward model**: with the certificates $\Pi$, $K$ ($j < k$) and $B$
($j + 1 < k$) of the run,

$$\|\tilde{\mathbf{H}} - \mathbf{I}_{k+1} \otimes \mathbf{A}\|_{\mathsf{F}} \le 102k^3 f + 96k^2 p,
\quad f = 8\varepsilon(\|\mathbf{A}\|_2(1+\Pi)^2 + B),\
p = 16k\varepsilon(\|\mathbf{A}\|_2(1+\Pi)^2 + B(1+\Pi+K)) .$$
The certificates are computable from the run; in practice $\Pi \ll \sqrt{\kappa}$. It is the
engine of the a priori induction (`NLAlibScaffold/Krylov/FinitePrecision/CGBackward.lean`): the
model of the prefix `C.take j` needs $B$ for the steps $i + 1 < j$ only, which the models of the
shorter prefixes provide.
Proof: `NLAlib.NormalizedLanczosData.frobNorm_backwardH_sub_dilatedH_le` with Lemmas A and B.
Difficulty: easy. -/
theorem frobNorm_backwardH_sub_dilatedH_le_of_certificates {P K B : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hB : ∀ j, j + 1 < k → C.lanczosβ (j + 1) ≤ B ∧ C.δ j ≤ B * C.γ j) :
    frobNorm (C.backwardH - C.dilatedH) ≤
      normalizedBackwardBound k (8 * C.ε * (specNorm C.A * (1 + P) ^ 2 + B))
        (16 * k * C.ε * (specNorm C.A * (1 + P) ^ 2 + B * (1 + P + K))) := by
  sorry

/-- **The next direction is not small**: with certificates $\Pi$, $K$ on the steps $j < k$ and
$20k\varepsilon(1 + \Pi + K) \le 1$, the direction after the last step satisfies
$\rho_k \le 2\|\mathbf{p}_k\|$. So $\mathbf{p}_k \ne \mathbf{0}$ when $\mathbf{r}_k \ne \mathbf{0}$,
and the next curvature is positive (`NLAlib.dotProduct_add_pos_of_spectrum_subset_Icc`): the
program's next division succeeds.
Proof: $\|\mathbf{r}_k + \delta_{k-1}\mathbf{p}_{k-1}\|^2 = \rho_k^2 + \delta_{k-1}^2
\|\mathbf{p}_{k-1}\|^2 + 2\delta_{k-1}\tau_{k-1}$ with `NLAlib.CGRun.abs_p_dotProduct_r_succ_le`
and $\delta_{k-1}\rho_{k-1}^2 \le 1.04\rho_k^2$; then `C.norm_ep_le`, bounded through the
quadratic mean, $\|\mathbf{e}^p_{k-1}\| \le \sqrt{2}\,\varepsilon\,(\rho_k^2 +
\delta_{k-1}^2\|\mathbf{p}_{k-1}\|^2)^{1/2}$, and $\rho_k^2 + \delta_{k-1}^2\|\mathbf{p}_{k-1}\|^2
\le \|\mathbf{r}_k + \delta_{k-1}\mathbf{p}_{k-1}\|^2 + 2\delta_{k-1}\lvert\tau_{k-1}\rvert$
(bounding $\delta_{k-1}\|\mathbf{p}_{k-1}\|$ directly reintroduces $\rho_k/\rho_{k-1}$); the
result is $\|\mathbf{p}_k\| \ge 0.67\rho_k$. Difficulty: moderate. -/
theorem norm_r_le_two_mul_norm_p {P K : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    (hsmall : 20 * k * C.ε * (1 + P + K) ≤ 1) :
    C.ρ k ≤ 2 * ‖WithLp.toLp 2 (C.p k)‖ := by
  sorry

/-- **The residual gap** (true minus updated residual): with $\mathbf{x}_0 = \mathbf{0}$,
$\mathbf{r}_0 = \mathbf{b}$,
$$\|(\mathbf{b} - \mathbf{A}\mathbf{x}_k) - \mathbf{r}_k\| \le \varepsilon\sum_{j<k}
\bigl(\|\mathbf{A}\|_2(\|\mathbf{x}_j\| + 4\gamma_j\|\mathbf{p}_j\|) + \|\mathbf{r}_j\|\bigr) .$$
[Greenbaum1997SIMAX]; [StrakosTichy2002, (7.16)], there with $\|\mathbf{x}\| +
\max_j\|\mathbf{x}_j\|$ and $+O(\varepsilon^2)$. Local: no Lanczos reduction, no $\kappa$.
Proof: the gap satisfies $\mathbf{g}_{j+1} = \mathbf{g}_j + \gamma_j\mathbf{e}^s_j -
\mathbf{A}\mathbf{e}^x_j - \mathbf{e}^r_j$, $\mathbf{g}_0 = \mathbf{0}$; sum the norms.
Difficulty: easy. -/
theorem norm_sub_mulVec_x_sub_r_le :
    ‖WithLp.toLp 2 (C.b - C.A *ᵥ C.x k - C.r k)‖ ≤
      C.ε * ∑ j ∈ Finset.range k, (specNorm C.A * (‖WithLp.toLp 2 (C.x j)‖ +
        4 * C.γ j * ‖WithLp.toLp 2 (C.p j)‖) + C.ρ j) := by
  sorry

end CGRun

end NLAlib
