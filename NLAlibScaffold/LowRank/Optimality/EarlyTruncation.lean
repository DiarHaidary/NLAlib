/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.EarlyTruncation
public import NLAlib.Probability.Distributions.ChiSquare
public import NLAlibScaffold.ForMathlib.Probability.Moments.PaleyZygmund
public import NLAlibScaffold.Probability.Distributions.ChiSquareMoments

/-!
# The early-truncated randomized SVD needs $\Theta(k/\varepsilon^2)$ samples

The early-truncated randomized SVD $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$
(`NLAlib.earlyTruncatedRSVD`) projects $\mathbf{A}$ onto $k$ dominant left singular vectors of the
sketch $\mathbf{A}\mathbf{\Omega}$. With a standard Gaussian $\mathbf{\Omega}$ it reaches
$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}\|_{\mathsf{F}}^2 \le (1+\varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$ with $\ell \ge 900k/\varepsilon^2$
samples
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`).
This file shows the rate $\varepsilon^{-2}$ cannot be improved to $\varepsilon^{-1}$:

* for $k = 1$ on $\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with
  $\delta = 1/(4\sqrt{\ell})$, the expected error is at least $(1 + 1/(100\sqrt{\ell}))$ times the
  optimum for every $\ell \ge 100$, and with probability at least $1/12$ the error exceeds
  $(1 + \delta)$ times the optimum. The sketch ranks the head direction below the tail one when
  $\|\mathbf{\omega}_1\|^2 < (1-\delta)^2\|\mathbf{\omega}_2\|^2$, which by Paley–Zygmund happens
  with constant probability at this gap;
* for large $k$ on $\operatorname{diag}(\mathbf{I}_k, (1 - \delta)\mathbf{I}_k)$ with
  $\delta = \sqrt{k/\ell}/4$ the expected excess is at least $c\sqrt{k/\ell}$ (absolute constants,
  existential), so $\ell \ge c^2 k/\varepsilon^2$ is necessary.

These results are new: no printed source states a lower bound for this estimator (research note
`reports/OP1-EarlyTruncatedRSVD.md` of the NLAlib workflow, 2026-10-25). Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.1. Real throughout. Proofs deferred.

## Main results

* `NLAlib.le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix`:
  the $k = 1$ expectation bound.
* `NLAlib.le_measureReal_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_gt_of_hasLaw_gaussianMatrix`:
  the $k = 1$ probability bound.
* `NLAlib.one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le`,
  `NLAlib.not_exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`
  :
  $\ell \ge 10^{-4}/\varepsilon^2$ is necessary, and $O(k/\varepsilon)$ samples do not suffice.
* `NLAlib.exists_forall_le_integral_frobNorm_sub_earlyTruncatedRSVD_sq_of_hasLaw_gaussianMatrix`:
  the general-$k$ instance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l : Type*} [Fintype l]

/-! ### The case $k = 1$: the $2 \times 2$ instance -/

/-- **A swapped ranking costs half the gap**: for $\mathbf{A} = \operatorname{diag}(1, s)$ with
$0 \le s \le 1$ and a test matrix $\mathbf{\Omega} \in \mathbb{R}^{2 \times \ell}$ with rows
$\mathbf{\omega}_1, \mathbf{\omega}_2$, if the sketch ranks the head row below the tail row,
$\|\mathbf{\omega}_1\|^2 < s^2\|\mathbf{\omega}_2\|^2$, then
$$s^2 + \frac{1 - s^2}{2} \le
\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)\|_{\mathsf{F}}^2\,,$$
against the optimum $s^2$. Deterministic; for the choice `truncatedSVD` makes.
Proof: M, about 50 lines. Let $\mathbf{P}$ be the range projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_1$ (`rangeProjector`, rank at most $1$, so
$p_1 + p_2 = \operatorname{tr}\mathbf{P} \le 1$ with $p_i = \mathbf{P}_{i,i} \ge 0$). The error is
$\|\mathbf{A}\|_{\mathsf{F}}^2 - \|\mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 = 1 + s^2 - p_1 - s^2 p_2
\ge 1 - (1 - s^2) p_1$ (`sub_earlyTruncatedRSVD`, Pythagoras for an orthogonal projector). With
$\mathbf{S}$ the swap permutation matrix, $\mathbf{S}\mathbf{P}\mathbf{S}$ is again an orthogonal
projector of rank at most $1$, and $\mathbf{P}$ maximises $\|\mathbf{P}'\mathbf{Y}\|_{\mathsf{F}}$
over those ($\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$, Eckart–Young `frobNorm_sub_truncatedSVD_le`
through `rangeProjector_truncatedSVD_mul`); the difference is
$\operatorname{tr}((\mathbf{S}\mathbf{P}\mathbf{S} - \mathbf{P})\mathbf{Y}\mathbf{Y}^{\mathsf{T}})
= (b - a)(p_1 - p_2)$ with $a = \|\mathbf{\omega}_1\|^2$, $b = s^2\|\mathbf{\omega}_2\|^2$. So
$a < b$ forces $p_1 \le p_2$, hence $p_1 \le 1/2$. All on $2 \times 2$ matrices
(`Matrix.trace_fin_two`, `Fin.sum_univ_two`). -/
theorem add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) {Ω' : Matrix (Fin 2) l ℝ}
    (hab : ∑ j, Ω' 0 j ^ 2 < s ^ 2 * ∑ j, Ω' 1 j ^ 2) :
    s ^ 2 + (1 - s ^ 2) / 2 ≤
      frobNorm (Matrix.diagonal ![1, s] - earlyTruncatedRSVD (Matrix.diagonal ![1, s]) Ω' 1) ^ 2
      := by
  sorry

/-- **The sketch misranks the two rows with constant probability**: for a standard Gaussian
$2 \times \ell$ test matrix with rows $\mathbf{\omega}_1, \mathbf{\omega}_2$, $\ell \ge 100$ and
$\delta = 1/(4\sqrt{\ell})$,
$$\mathbb{P}\bigl[\|\mathbf{\omega}_1\|^2 < (1 - \delta)^2\|\mathbf{\omega}_2\|^2\bigr] \ge
\frac{1}{12}\,.$$
No printed source. New (research note OP1, §1).
Proof: M, about 70 lines. Let $X = \|\mathbf{\omega}_1\|^2 - \|\mathbf{\omega}_2\|^2$. The rows
are independent standard Gaussian vectors (`hasLaw_uncurry_of_hasLaw_gaussianMatrix`, then the
row maps and `iIndepFun` of the coordinates, or the transpose and
`iIndepFun_col_of_hasLaw_gaussianMatrix`). Paley–Zygmund
(`ProbabilityTheory.sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt`) on $Z = X^2$ with
$\theta = 1/4$, $\mathbb{E}Z = 4\ell$, $\mathbb{E}Z^2 = 48\ell^2 + 96\ell$
(`integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector`,
`integral_norm_sq_sub_norm_sq_pow_four_of_hasLaw_gaussianVector`) gives
$\mathbb{P}[X^2 > \ell] \ge 9\ell/(48\ell + 96)$. $X$ and $-X$ have the same law (swap the rows:
the law `gaussianMatrix` is invariant under the row permutation), so
$\mathbb{P}[X \le -\sqrt{\ell}] \ge 9\ell/(96\ell + 192) \ge 0.0919$ at $\ell \ge 100$. On
$\{X \le -\sqrt{\ell}\} \cap \{\|\mathbf{\omega}_2\|^2 < 2\ell\}$ the event holds, since
$1 - (1-\delta)^2 < 2\delta = 1/(2\sqrt{\ell})$. The chi-square upper tail at $\beta = 2$
(`measureReal_norm_sq_ge_mul_card_le_of_hasLaw_gaussianVector`) bounds the complement by
$e^{(\ell/2)(\log 2 - 1)} \le e^{-15}$. Then $0.0919 - e^{-15} \ge 1/12$ (`norm_num`, with
`Real.exp_le_one_div` or `Real.add_one_le_exp`-type estimates for $e^{-15}$). -/
theorem le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix {X : Ω → Matrix (Fin 2) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ) (hl : 100 ≤ Fintype.card l) :
    1 / 12 ≤ μ.real {ω | ∑ j, X ω 0 j ^ 2 <
      (1 - 1 / (4 * √(Fintype.card l : ℝ))) ^ 2 * ∑ j, X ω 1 j ^ 2} := by
  sorry

/-- **The early-truncated randomized SVD has excess $\Omega(1/\sqrt{\ell})$ at $k = 1$**: for
$\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with $\delta = 1/(4\sqrt{\ell})$, a standard
Gaussian $2 \times \ell$ test matrix $\mathbf{\Omega}$ and $\ell \ge 100$,
$$\Bigl(1 + \frac{1}{100\sqrt{\ell}}\Bigr)\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1
\|_{\mathsf{F}}^2 \le \mathbb{E}\|\mathbf{A} -
\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)\|_{\mathsf{F}}^2\,,$$
with $\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1\|_{\mathsf{F}}^2 = (1 - \delta)^2$. So
relative error $1 + \varepsilon$ in expectation needs $\ell \ge 10^{-4}/\varepsilon^2$
(`NLAlib.one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le`), matching the
$\varepsilon^{-2}$ of
`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`. The
constant $1/100$ is safe, not sharp: the proof gives about $0.017$, and the excess on this instance
is about $0.5/\sqrt{\ell}$ (research note OP1, §2).
No printed source. New (research note OP1, §1).
Proof: M, about 60 lines. Write $s = 1 - \delta$; the error is at least $s^2$ everywhere
(Eckart–Young: `frobNorm_sub_truncatedSVD_le` for the rank-one `earlyTruncatedRSVD`,
`rank_earlyTruncatedRSVD_le`) and at least $s^2 + (1 - s^2)/2$ on the misranking event
(`add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq`), whose probability is at least
$1/12$ (`le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix`). Integrate the pointwise bound
$s^2 + \frac{1-s^2}{2}\mathbf{1}_E$ (`integral_mono`, integrability from
`integrable_frobNorm_sub_earlyTruncatedRSVD_sq`-type boundedness: the error is at most
$\|\mathbf{A}\|_{\mathsf{F}}^2 = 1 + s^2$). Then $(1 - s^2)/24 \ge s^2/(100\sqrt{\ell})$ since
$1 - s^2 = \delta(2 - \delta) \ge 1.97\,\delta$ and $\delta \le 1/40$. The optimum:
`frobNorm_sub_truncatedSVD_sq` with the singular values $1, s$ of the diagonal matrix.
Result: early-truncated-rsvd-lower-bound -/
theorem le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix
    {X : Ω → Matrix (Fin 2) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ)
    (hl : 100 ≤ Fintype.card l) :
    (1 + 1 / (100 * √(Fintype.card l : ℝ))) *
        frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
          truncatedSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) 1) ^ 2 ≤
      ∫ ω, frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
        earlyTruncatedRSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) (X ω)
          1) ^ 2
        ∂μ := by
  sorry

/-- **Constant-probability $(1+\varepsilon)$ also needs $\varepsilon^{-2}$ samples at $k = 1$**: for
$\mathbf{A} = \operatorname{diag}(1, 1 - \delta)$ with $\delta = 1/(4\sqrt{\ell})$, a standard
Gaussian $2 \times \ell$ test matrix $\mathbf{\Omega}$, $\ell \ge 100$ and
$16\varepsilon^2\ell < 1$,
$$\mathbb{P}\Bigl[\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)
\|_{\mathsf{F}}^2 > (1 + \varepsilon)
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1\|_{\mathsf{F}}^2
\Bigr] \ge \frac{1}{12}\,.$$
No printed source. New (research note OP1, §1).
Proof: S, about 30 lines. On the misranking event of
`le_measureReal_sum_sq_lt_of_hasLaw_gaussianMatrix` the error is at least
$s^2 + (1 - s^2)/2 \ge (1 + \delta)s^2$
(`add_div_two_le_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq`; $2 - \delta \ge 2(1-\delta)^2$),
and $\delta > \varepsilon$ when $16\varepsilon^2\ell < 1$ (for $\varepsilon \le 0$ trivially); the
optimum is $s^2 > 0$. `measureReal_mono`. -/
theorem
    le_measureReal_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_gt_of_hasLaw_gaussianMatrix
    {X : Ω → Matrix (Fin 2) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ)
    (hl : 100 ≤ Fintype.card l) {ε : ℝ} (hε : 16 * ε ^ 2 * Fintype.card l < 1) :
    1 / 12 ≤ μ.real {ω | (1 + ε) *
        frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
          truncatedSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) 1) ^ 2 <
      frobNorm (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))] -
        earlyTruncatedRSVD (Matrix.diagonal ![1, 1 - 1 / (4 * √(Fintype.card l : ℝ))]) (X ω)
          1) ^ 2}
      := by
  sorry

/-- **Relative error $1 + \varepsilon$ in expectation needs $\ell \ge 10^{-4}/\varepsilon^2$
samples**: if a standard Gaussian test matrix $\mathbf{\Omega}$ with $\ell \ge 100$ columns gives
$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, 1)
\|_{\mathsf{F}}^2 \le (1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_1
\|_{\mathsf{F}}^2$ for every real $2 \times 2$ matrix $\mathbf{A}$, then
$1 \le 10^4\varepsilon^2\ell$. The library's sufficient condition is $\ell \ge 900k/\varepsilon^2$
(`NLAlib.integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`):
the rate is $\Theta(\varepsilon^{-2})$.
No printed source. New (research note OP1).
Proof: S, about 20 lines. Apply the hypothesis to the instance of
`le_integral_frobNorm_sub_earlyTruncatedRSVD_diagonal_sq_of_hasLaw_gaussianMatrix`; the optimum
$(1 - \delta)^2$ is positive, so $1/(100\sqrt{\ell}) \le \varepsilon$; square
(`Real.sq_sqrt`). -/
theorem one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le
    {X : Ω → Matrix (Fin 2) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin 2) l) μ)
    (hl : 100 ≤ Fintype.card l) {ε : ℝ}
    (h : ∀ A : Matrix (Fin 2) (Fin 2) ℝ,
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) 1) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A 1) ^ 2) :
    1 ≤ 10 ^ 4 * ε ^ 2 * Fintype.card l := by
  sorry

/-- **$O(k/\varepsilon)$ samples do not suffice for the early-truncated randomized SVD**: there are
no constants $C, \varepsilon_0 > 0$ such that for every standard Gaussian $n \times \ell$ test
matrix $\mathbf{\Omega}$, every $\mathbf{A}$, $k$ and $0 < \varepsilon \le \varepsilon_0$ with
$\ell \ge Ck/\varepsilon$,
$$\mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2 \le (1+\varepsilon)\|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
The negation of the $\varepsilon^{-1}$ analogue of
`NLAlib.exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix`
(which holds with $\ell \ge Ck/\varepsilon^2$).
No printed source. New (research note OP1).
Proof: S, about 30 lines. Given $C, \varepsilon_0$, take $k = 1$, $\mathbf{A}$ the
$2 \times 2$ instance, $\Omega = $ `Matrix (Fin 2) (Fin L) ℝ` with $\mu = $ `gaussianMatrix` and
$\mathbf{X} = \mathrm{id}$ (`HasLaw.id` or `hasLaw_id`), $\varepsilon$ small with
$\max(C/\varepsilon, 100) + 1 < 10^{-4}/\varepsilon^2$ and $\varepsilon \le \varepsilon_0$, and
$L = \lceil\max(C/\varepsilon, 100)\rceil$ (`Nat.le_ceil`); then
`one_le_mul_card_of_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le` contradicts
$10^4\varepsilon^2 L < 1$. -/
theorem
    not_exists_forall_integral_frobNorm_sub_earlyTruncatedRSVD_sq_le_of_hasLaw_gaussianMatrix :
    ¬ ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω m n l : Type} [MeasurableSpace Ω] [Fintype m]
      [Fintype n] [Fintype l] (μ : Measure Ω) (A : Matrix m n ℝ) (X : Ω → Matrix n l ℝ) (k : ℕ)
      (ε : ℝ),
      HasLaw X (gaussianMatrix n l) μ → 0 < ε → ε ≤ ε₀ →
      C * ((k : ℝ) / ε) ≤ Fintype.card l →
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ ≤
        (1 + ε) * frobNorm (A - truncatedSVD A k) ^ 2 := by
  sorry

/-! ### General $k$: the block instance -/

/-- **The tail content of the sketch's dominant frame controls the error**, deterministic: for
$\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, s\mathbf{I}_k)$ with $0 \le s \le 1$, any
$\mathbf{\Omega} = [\mathbf{\Omega}_1; \mathbf{\Omega}_2] \in \mathbb{R}^{2k \times \ell}$ with
$\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \ge k$, $\mathbf{P}$ the range projector of
$\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$, $T = \operatorname{tr}\mathbf{P}_{22}$ its tail
content, and $0 \le \theta \le \pi/2$: the error is at least $ks^2 + (1 - s^2)T$, and
$$\begin{aligned}
&T\bigl(s^2\|\mathbf{\Omega}_2\|_2^2 - \sigma_{k-1}(\mathbf{\Omega}_1)^2\bigr) +
2s\,\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2\sqrt{kT} \\
&\quad\ge 2s\sin\theta\cos\theta\,\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_* -
\sin^2\theta\,\bigl(\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 -
s^2\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2\bigr)\,.
\end{aligned}$$
No printed source. New (research note OP1, §4 steps 1–3).
Proof: M, about 90 lines (split the two conjuncts). Write
$\mathbf{P} = \mathbf{U}\mathbf{U}^{\mathsf{T}}$
with $\mathbf{U} = [\mathbf{U}_h; \mathbf{U}_t]$ an orthonormal $k$-frame
(`rangeProjector_truncatedSVD_mul`, rank exactly $k$), so $T = \|\mathbf{U}_t\|_{\mathsf{F}}^2$ and
$\|\mathbf{U}_h\|_{\mathsf{F}}^2 = k - T$. (1) Error:
$\|\mathbf{A}\|_{\mathsf{F}}^2 - \operatorname{tr}(\mathbf{P}\mathbf{A}^2) =
k + ks^2 - (k - T) - s^2T$.
(2) Upper bound on $f(\mathbf{U}) = \|\mathbf{U}^{\mathsf{T}}\mathbf{Y}\|_{\mathsf{F}}^2$,
$\mathbf{Y} = \mathbf{A}\mathbf{\Omega}$, with
$\mathbf{W}_{ij} = \mathbf{\Omega}_i\mathbf{\Omega}_j^{\mathsf{T}}$:
$f(\mathbf{U}) \le \operatorname{tr}\mathbf{W}_{11} - \lambda_{\min}(\mathbf{W}_{11})T +
2s\|\mathbf{W}_{12}\|_2\sqrt{kT} + s^2\lambda_{\max}(\mathbf{W}_{22})T$ (Loewner
$\mathbf{I} - \mathbf{U}_h\mathbf{U}_h^{\mathsf{T}} \succeq \mathbf{0}$, Cauchy–Schwarz
`frobInner_le`-type bound, `specNorm` of a product). (3) Competitor
$\mathbf{V} = [\cos\theta\,\mathbf{I}; \sin\theta\,\mathbf{R}]$, $\mathbf{R}$ the orthogonal polar
factor with $\operatorname{tr}(\mathbf{W}_{12}\mathbf{R}) = \|\mathbf{W}_{12}\|_*$
(`exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm` at full rank, or the polar factor);
$f(\mathbf{U}) \ge f(\mathbf{V})$ is Ky Fan maximality of the truncated SVD (Eckart–Young on
$\mathbf{Y}$ via `rangeProjector_truncatedSVD_mul`). Subtract. $\lambda_{\max}(\mathbf{W}_{22}) =
\|\mathbf{\Omega}_2\|_2^2$,
$\lambda_{\min}(\mathbf{W}_{11}) = \sigma_{k-1}(\mathbf{\Omega}_1)^2$. -/
theorem frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational {k : ℕ} {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) {A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ}
    (hA : A = Matrix.fromBlocks 1 0 0 (s • 1)) {Ω' : Matrix (Fin k ⊕ Fin k) l ℝ}
    (hr : k ≤ (A * Ω').rank) {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2) {T : ℝ}
    (hT : T = ∑ i : Fin k, rangeProjector (truncatedSVD (A * Ω') k) (Sum.inr i) (Sum.inr i)) :
    k * s ^ 2 + (1 - s ^ 2) * T ≤ frobNorm (A - earlyTruncatedRSVD A Ω' k) ^ 2 ∧
      2 * s * Real.sin θ * Real.cos θ * nuclearNorm (Ω'.toRows₁ * Ω'.toRows₂ᵀ) -
          Real.sin θ ^ 2 * (frobNorm Ω'.toRows₁ ^ 2 - s ^ 2 * frobNorm Ω'.toRows₂ ^ 2) ≤
        T * (s ^ 2 * specNorm Ω'.toRows₂ ^ 2 - singularValues Ω'.toRows₁ (k - 1) ^ 2) +
          2 * s * specNorm (Ω'.toRows₁ * Ω'.toRows₂ᵀ) * √(k * T) := by
  sorry

/-- **The early-truncated randomized SVD has excess $\Omega(\sqrt{k/\ell})$**: there are absolute
constants $c, C > 0$ and $K_0$ such that for every $k \ge K_0$, a standard Gaussian
$2k \times \ell$ test matrix $\mathbf{\Omega}$ with $\ell \ge Ck$, and
$\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, (1 - \delta)\mathbf{I}_k)$ with
$\delta = \sqrt{k/\ell}/4$,
$$\Bigl(1 + c\sqrt{k/\ell}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2\,.$$
So relative error $1 + \varepsilon$ needs $\ell \ge c^2k/\varepsilon^2$: the $k$-dependence of
the library's $900k/\varepsilon^2$ is also sharp. The constants are existential: the proof gives
$c \approx 10^{-4}$ with large $C$, $K_0$ (Chebyshev-level concentration); numerically
$c \approx 0.2$ for every $k \ge 1$ (research note OP1, §2(b)). $k \ge K_0$ is where the proof's
concentration events have probability at least $1/2$; for $2 \le k < K_0$ the statement is
expected but not proved (design note, OQ3).
No printed source. New (research note OP1, §4).
Proof: H, about 300 lines. On the event $G$ where (i)
$\|\mathbf{\Omega}_2\|_2 \le \sqrt{\ell} + \tfrac54\sqrt{k}$,
$\sigma_{k-1}(\mathbf{\Omega}_1) \ge \sqrt{\ell} - \tfrac54\sqrt{k}$
(`measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix`,
`measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix`), (ii)
$\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_2 \le 2.2\sqrt{k\ell}$
(`measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix`), (iii)
$\|\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}\|_{\mathsf{F}}^2 \ge 0.9k^2\ell$ (Chebyshev with
`integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix`), so
$\|\cdot\|_* \ge \|\cdot\|_{\mathsf{F}}^2/\|\cdot\|_2 \ge 0.4k\sqrt{k\ell}$, (iv)
$\lvert\|\mathbf{\Omega}_1\|_{\mathsf{F}}^2 - \|\mathbf{\Omega}_2\|_{\mathsf{F}}^2\rvert \le
0.01k\sqrt{k\ell}$ and
$\|\mathbf{\Omega}_2\|_{\mathsf{F}}^2 \le 1.01k\ell$ (Chebyshev on chi-square sums,
`integral_norm_sq_sub_norm_sq_sq_of_hasLaw_gaussianVector`), each failing with probability
$O(1/k)$ or $O(e^{-ck})$ for $\ell \ge Ck$, so $\mathbb{P}[G] \ge 1/2$ for $k \ge K_0$.
On $G$, `frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational` at $\theta = 1/4$ gives
$5T + 4.5\sqrt{kT} \ge 0.09k$, hence $T \ge 10^{-4}k$ (if $T < 10^{-4}k$ the left side is below
$0.046k$). The error is $\ge ks^2$ everywhere (first conjunct, $T \ge 0$) and
$\ge ks^2 + (1 - s^2)10^{-4}k$ on $G$; integrate, $1 - s^2 \ge \delta$, the optimum is $ks^2$
(`frobNorm_sub_truncatedSVD_sq`; singular values $1$ ($k$ times) and $s$). Take
$c = 10^{-4}/8$.
Result: early-truncated-rsvd-lower-bound -/
theorem
    exists_forall_le_integral_frobNorm_sub_earlyTruncatedRSVD_sq_of_hasLaw_gaussianMatrix :
    ∃ c C : ℝ, ∃ K₀ : ℕ, 0 < c ∧ 0 < C ∧ ∀ {Ω l : Type} [MeasurableSpace Ω] [Fintype l]
      (μ : Measure Ω) (k : ℕ) (X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ)
      (A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ),
      HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ → K₀ ≤ k → C * k ≤ Fintype.card l →
      A = Matrix.fromBlocks 1 0 0 ((1 - √((k : ℝ) / Fintype.card l) / 4) • 1) →
      (1 + c * √((k : ℝ) / Fintype.card l)) *
          frobNorm (A - truncatedSVD A k) ^ 2 ≤
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
  sorry

end NLAlib
