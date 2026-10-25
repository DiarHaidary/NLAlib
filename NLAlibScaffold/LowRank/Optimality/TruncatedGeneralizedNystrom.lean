/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.LowRank.Gaussian.TruncatedGeneralizedNystrom
public import NLAlibScaffold.LowRank.Structural.Truncation

/-!
# Truncated generalized Nyström: a lower bound on Epperly and Webber's instance

Late-truncated generalized Nyström $\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega},
\mathbf{\Psi})\rrbracket_k$ with independent standard Gaussian test matrices reaches relative
error $1 + \varepsilon$ in expectation at $\ell = O(k/\varepsilon)$, $p = O(k/\varepsilon^2)$
([relative-error
bound](https://nla-lib.org/explore/#d/NLAlib.integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_one_add_mul_of_hasLaw_gaussianMatrix)).
On Epperly and Webber's two-eigenvalue instance
$\mathbf{A}_a = \operatorname{diag}(a\mathbf{I}_k, \mathbf{I}_{n-k})$, as $a \to \infty$ the
expected error is at least
$$\|\mathbf{A}_a - \llbracket\mathbf{A}_a\rrbracket_k\|_{\mathsf{F}}^2 +
\frac{k(n - \ell)}{p - \ell - 1}\,,$$
so relative error $1 + \varepsilon$ needs $p \ge \ell + 1 + k(n-\ell)/((n-k)\varepsilon)$. On
the same instance untruncated generalized Nyström pays $\ell/(p - \ell - 1)$ in place of
$k/(p - \ell - 1)$ (Epperly and Webber's identity,
`NLAlib.integral_frobNorm_sub_generalizedNystrom_sq_eq_mul_integral_of_hasLaw_gaussianMatrix`):
late truncation gains the factor $\ell/k$ where Epperly and Webber's lower bound for generalized
Nyström lives. Whether $p = O(k/\varepsilon)$ suffices for every $\mathbf{A}$ is open
(design note §5).
New (research note `reports/OP2-TruncatedGN.md` of the NLAlib workflow, §3, L1; the
finite-gap argument through
`NLAlib.le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq` is this design's). Design:
`docs/design/LowRank-EstimatorLowerBounds.md` §3.2. Real. Proofs deferred.

## Main results

* `NLAlib.eventually_le_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq`:
  the lower bound as $a \to \infty$.
* `NLAlib.mul_le_of_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq_le`:
  the co-range size it forces.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l p s t : Type*} [Fintype l]
  [Fintype p] [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
  {X : Ω → Matrix (s ⊕ t) l ℝ} {Ψ : Ω → Matrix (s ⊕ t) p ℝ}

/-- **Truncated generalized Nyström keeps the noise in the head subspace** (lower bound on
Epperly and Webber's instance): for $\mathbf{A}_a = \operatorname{diag}(a\mathbf{I}_k,
\mathbf{I}_{n-k})$ on $s \oplus t$ ($k = \lvert s\rvert$, $n = \lvert s\rvert + \lvert t\rvert$),
independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($n \times p$), $k + 2 \le \ell$, $\ell + 2 \le p$, and every $\eta > 0$: for all
large $a$,
$$\lvert t\rvert + \frac{k(n - \ell)}{p - \ell - 1} - \eta \le
\mathbb{E}\|\mathbf{A}_a - \llbracket\mathsf{gn}(\mathbf{A}_a, \mathbf{\Omega}, \mathbf{\Psi})
\rrbracket_k\|_{\mathsf{F}}^2\,,$$
where $\lvert t\rvert = \|\mathbf{A}_a - \llbracket\mathbf{A}_a\rrbracket_k\|_{\mathsf{F}}^2$ for
$a \ge 1$. For $n \le \ell$ the bound is below the optimum and trivially true. For the choice
`truncatedSVD` makes.
No printed source. New (research note OP2, §3, L1, there as a limit inferior; the instance is
[EpperlyWebber2026, §6.5]).
Proof: H, about 200 lines. Write $\mathbf{R}_a = \mathsf{rsvd}(\mathbf{A}_a, \mathbf{\Omega})$,
$\mathbf{N}_a$ the core noise and $g_a = \sigma_{k-1}(\mathbf{R}_a)^2 - \sigma_k(\mathbf{R}_a)^2$.
(1) Pointwise, under the rank event
(`ae_rank_conjTranspose_mul_mul_eq`-type, private in `TruncatedGeneralizedNystrom.lean`: re-derive
from `ae_rank_mul_eq_min_of_hasLaw_gaussianMatrix`), the error is at least
$\|\mathbf{A}_a - \llbracket\mathbf{R}_a\rrbracket_k\|_{\mathsf{F}}^2 +
\|\mathbf{P}\mathbf{N}_a\|_{\mathsf{F}}^2 - \min(\|\mathbf{P}\mathbf{N}_a\|_{\mathsf{F}}^2,
\|\mathbf{N}_a\|_{\mathsf{F}}^4/g_a)$ (`le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq` when
$g_a > 0$, and
`frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq` always).
(2) Integrate: $\mathbb{E}\|\mathbf{A}_a - \llbracket\mathbf{R}_a\rrbracket_k\|_{\mathsf{F}}^2 \ge
\lvert t\rvert$ (Eckart–Young); $\mathbb{E}\|\mathbf{P}\mathbf{N}_a\|_{\mathsf{F}}^2 =
\tfrac{k}{p-\ell-1}\mathbb{E}\|\mathbf{A}_a - \mathbf{R}_a\|_{\mathsf{F}}^2$
(`integral_frobNorm_rangeProjector_mul_obliqueProjector_sq_of_hasLaw_gaussianMatrix`)
and $\|\mathbf{A}_a - \mathbf{R}_a\|_{\mathsf{F}}^2 \ge n - \ell$ (rank of $\mathbf{R}_a$ at most
$\ell$, `frobNorm_sub_truncatedSVD_sq`). (3) The defect tends to $0$: with
$\mathbf{\Omega} = [\mathbf{\Omega}_1; \mathbf{\Omega}_2]$, HMT's deterministic bound
(`HasOrthonormalCols.frobNorm_sub_rsvd_sq_le` with the head frame) gives
$\|\mathbf{A}_a - \mathbf{R}_a\|_{\mathsf{F}}^2 \le D^2 := \lvert t\rvert +
\|\mathbf{\Omega}_2\mathbf{\Omega}_1^{+}\|_{\mathsf{F}}^2$, independent of $a$, with
$\mathbb{E}D^2 < \infty$ for $k + 2 \le \ell$
(`integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix`-type
inverse moments, independence of the row blocks); Weyl gives $\sigma_{k-1}(\mathbf{R}_a) \ge a - D$
and $\sigma_k(\mathbf{R}_a) \le 1$, so $g_a \ge a^2/8$ on $\{D \le a/2\}$, $a \ge 4$. Bound the
defect by $\|\mathbf{N}_a\|_{\mathsf{F}}^2\mathbf{1}_{D > a/2} +
\min(\|\mathbf{N}_a\|_{\mathsf{F}}^2, 8\|\mathbf{N}_a\|_{\mathsf{F}}^4/a^2)$. Conditionally on
$\mathbf{\Omega}$, $\mathbb{E}\|\mathbf{N}_a\|_{\mathsf{F}}^2 = \tfrac{\ell}{p-\ell-1}\|\mathbf{A}_a
-
\mathbf{R}_a\|_{\mathsf{F}}^2 \le \tfrac{\ell}{p-\ell-1}D^2$ (the fixed-$\mathbf{\Omega}$ form of
`integral_frobNorm_sub_generalizedNystrom_sq_of_hasLaw_gaussianMatrix` and Pythagoras), so the first
part is at most $\tfrac{\ell}{p-\ell-1}\mathbb{E}[D^2\mathbf{1}_{D > a/2}] \to 0$ (dominated
convergence in $\mathbf{\Omega}$ alone). For the second, conditionally on $\mathbf{\Omega}$,
$\|\mathbf{N}_a\|_{\mathsf{F}} \le \|\mathbf{G}_1^{+}\|_2\,\|\mathbf{G}_2\|_2\,D$ with
$(\mathbf{G}_1, \mathbf{G}_2) = (\mathbf{\Psi}^{\mathsf{T}}\mathbf{Q}_a,
\mathbf{\Psi}^{\mathsf{T}}\mathbf{Q}_{a,\perp})$
of a fixed product Gaussian law (rotation invariance), so its conditional mean is at most
$h_a(D)$ with $h_a(d) = \mathbb{E}\min(Z d^2, 8Z^2d^4/a^2)$,
$Z = \|\mathbf{G}_1^{+}\|_2^2\|\mathbf{G}_2\|_2^2$ integrable for $\ell + 2 \le p$; $h_a(d) \to 0$
and $h_a(D) \le D^2\,\mathbb{E}Z$, dominated convergence twice.
Result: truncated-gn-lower-bound -/
theorem eventually_le_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq
    (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ) (hΨ : HasLaw Ψ (gaussianMatrix (s ⊕ t) p) μ)
    (hXΨ : IndepFun X Ψ μ) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ a : ℝ in atTop, (Fintype.card t : ℝ) +
        Fintype.card s * ((Fintype.card s : ℝ) + Fintype.card t - Fintype.card l) /
          ((Fintype.card p : ℝ) - Fintype.card l - 1) - η ≤
      ∫ ω, frobNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ) -
        truncatedSVD (generalizedNystrom
          (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ)) (X ω) (Ψ ω))
            (Fintype.card s)) ^ 2 ∂μ := by
  sorry

/-- **Relative error $1 + \varepsilon$ forces $p - \ell - 1 \ge k(n - \ell)/((n-k)\varepsilon)$**:
for independent standard Gaussian test matrices $\mathbf{\Omega}$ ($n \times \ell$) and
$\mathbf{\Psi}$ ($n \times p$), $k + 2 \le \ell$, $\ell + 2 \le p$, if truncated generalized
Nyström has expected error at most $(1 + \varepsilon)\|\mathbf{A}_a -
\llbracket\mathbf{A}_a\rrbracket_k\|_{\mathsf{F}}^2 = (1 + \varepsilon)\lvert t\rvert$ on every
$\mathbf{A}_a = \operatorname{diag}(a\mathbf{I}_k, \mathbf{I}_{n-k})$ with $a \ge 1$
($k = \lvert s\rvert$, $n = \lvert s\rvert + \lvert t\rvert$), then
$$k(n - \ell) \le \varepsilon\,(p - \ell - 1)\,\lvert t\rvert\,.$$
For $n \gg \ell$: $p \ge \ell + 1 + k/\varepsilon$ up to the factor $(n-\ell)/(n-k)$.
No printed source. New (research note OP2, §3, L1).
Proof: S, about 20 lines. For every $\eta > 0$ pick $a \ge 1$ in the eventually-set of
`eventually_le_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq`
(`Filter.Eventually.exists_forall_of_atTop`, `eventually_ge_atTop`); so
$k(n - \ell)/(p - \ell - 1) \le \varepsilon\lvert t\rvert + \eta$; let $\eta \to 0$
(`le_of_forall_pos_le_add`) and clear the positive denominator. -/
theorem mul_le_of_forall_integral_frobNorm_sub_truncatedSVD_generalizedNystrom_fromBlocks_sq_le
    (hX : HasLaw X (gaussianMatrix (s ⊕ t) l) μ) (hΨ : HasLaw Ψ (gaussianMatrix (s ⊕ t) p) μ)
    (hXΨ : IndepFun X Ψ μ) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    (hlp : Fintype.card l + 2 ≤ Fintype.card p) {ε : ℝ}
    (h : ∀ a : ℝ, 1 ≤ a →
      ∫ ω, frobNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ) -
        truncatedSVD (generalizedNystrom
          (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (1 : Matrix t t ℝ)) (X ω) (Ψ ω))
            (Fintype.card s)) ^ 2 ∂μ ≤ (1 + ε) * Fintype.card t) :
    Fintype.card s * ((Fintype.card s : ℝ) + Fintype.card t - Fintype.card l) ≤
      ε * ((Fintype.card p : ℝ) - Fintype.card l - 1) * Fintype.card t := by
  sorry

end NLAlib
