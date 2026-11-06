/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Matrix.QRIteration.Ritz

/-!
# Forward-approximate Ritz values are optimal or decouple early (scaffold)

Statements for a new `NLAlib/Matrix/QRIteration/Dichotomy.lean` (stage SHIFTED-QR, wave W3,
design note `docs/design/Eigensolvers-ShiftedQR.md` §3.7): the exact-arithmetic dichotomy of
[BanksGarzaVargasSrivastava2022, §4.1]. If shifts within $\beta$ of the Ritz values fail to be
$\theta$-optimal, then one of them is close to an eigenvalue of large last-row weight, and the
degree $k$ step with that shift has a large $\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} -
r\mathbf{I})^{-k}\|$ (it decouples early). It is the bridge from the forward-approximate Ritz
values a small eigensolver computes to the $\theta$-optimal ones the strategy needs; no
arithmetic model is involved.

## Main results

* `NLAlib.sum_lastRowWeights_mul_norm_eval_sq_sub_le`: perturbing roots raises the weighted
  second moment only through weight near the roots.
* `NLAlib.IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le`: the dichotomy.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- **Instability implies support**: let $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$ with $\mathbf{V}$ invertible and last-row weights $w$, the eigenvalues separated by
$\lvert\mathbf{d}_i - \mathbf{d}_j\rvert \ge \Gamma$ for $i \ne j$; let $c > 0$,
$0 \le \beta \le c\Gamma$, and let `ss`, `ss'` be lists of $k$ shifts with
$\lvert s_i - s_i'\rvert \le \beta$ and $\lvert s_i\rvert \le \|\mathbf{H}\|_2$. With
$q = \prod_i (z - s_i)$, $q' = \prod_i (z - s_i')$,
$$\sum_i w_i\lvert q'(\mathbf{d}_i)\rvert^2 - (1 + 2c)^{2k}\sum_i w_i\lvert q(\mathbf{d}_i)
\rvert^2 \le \bigl(2(\|\mathbf{H}\|_2 + \beta)(1 + 2c)\bigr)^{2k}\sum_{i\,:\,\exists s \in
\mathrm{ss},\ \lvert\mathbf{d}_i - s\rvert \le \beta/(2c)} w_i\,.$$
[BanksGarzaVargasSrivastava2022, Lemma 4.2].
Proof: the paper's: group the shifts by their nearest eigenvalue (`Finset.exists_min_image`),
exchange $s_i$ for $s_i'$ one group at a time (Claim 4.4 there): at an eigenvalue other than the
group's, each exchanged factor grows by at most $1 + 2\beta/\Gamma \le 1 + 2c$ (the eigenvalue is
at distance $\ge \Gamma/2$ from the shift); at the group's eigenvalue, either it is farther
than $\beta/(2c)$ from the group (factor $\le 1 + 2c$ again) or the whole term is at most
$(2(\|\mathbf{H}\|_2 + \beta))^{2k}w_j$ ($\lvert\mathbf{d}_j\rvert \le \|\mathbf{H}\|_2$ by
`spectrum.norm_le_norm_of_mem`); induction over the groups. L, about 120 lines (the claim as a
private lemma). -/
theorem sum_lastRowWeights_mul_norm_eval_sq_sub_le {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ}
    {d : Fin (n + 1) → ℂ} (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {Γ c β : ℝ}
    (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖) (hc : 0 < c) (hβ : 0 ≤ β) (hβc : β ≤ c * Γ)
    {ss ss' : List ℂ} (hclose : List.Forall₂ (fun s s' => ‖s - s'‖ ≤ β) ss ss')
    (hss : ∀ s ∈ ss, ‖s‖ ≤ specNorm H) :
    ∑ i, lastRowWeights V i * ‖(shiftPoly ss').eval (d i)‖ ^ 2 -
        (1 + 2 * c) ^ (2 * ss.length) * ∑ i, lastRowWeights V i * ‖(shiftPoly ss).eval (d i)‖ ^ 2 ≤
      (2 * (specNorm H + β) * (1 + 2 * c)) ^ (2 * ss.length) *
        ∑ i ∈ Finset.univ.filter (fun i => ∃ s ∈ ss, ‖d i - s‖ ≤ β / (2 * c)),
          lastRowWeights V i := by
  sorry

/-- **The dichotomy for forward-approximate Ritz values**: let $\mathbf{H}$ be upper Hessenberg
with $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(\mathbf{d})$, $\mathbf{V}$ invertible,
$\kappa = \|\mathbf{V}\|_2\|\mathbf{V}^{-1}\|_2$, eigenvalues separated by $\Gamma$; let
$1 \le k \le n$, $x = (2\kappa^4)^{1/(2k)} < \theta$, $c = \tfrac12(\theta/x - 1)$,
$0 < \beta < c\Gamma$, and let `rs` be within $\beta$ of the Ritz values of order $k$, entry by
entry. Then `rs` is a set of $\theta$-optimal Ritz values, or some $r$ in `rs` is an eigenvalue,
or
$$\tfrac25\,\psi_k(\mathbf{H})\Bigl(1 - \frac x\theta\Bigr) \le \kappa^{2/k}(\|\mathbf{H}\|_2 +
\beta)\,\beta\,\|\mathbf{e}_n^{\mathsf{H}}(\mathbf{H} - r\mathbf{I})^{-k}\|^{1/k}$$
for some $r$ in `rs`. [BanksGarzaVargasSrivastava2022, Theorem 4.1], there with $\tfrac12$ for
$\tfrac25$ (a factor $k^{-1/(2k)}/2 \ge 2/5$ is lost in its last display; gap G10) and
$\beta \le c\Gamma$ (which can let two eigenvalues share a Ritz value).
Proof: if `rs` is not optimal, $\sum_i w_i\lvert p(\mathbf{d}_i)\rvert^2 \ge
2(1 + 2c)^{2k}\sum_i w_i\lvert\chi_k(\mathbf{d}_i)\rvert^2$
(`NLAlib.sum_lastRowWeights_mul_sq_le`, `NLAlib.norm_mul_diagonal_mul_inv_last_sq_le`,
`NLAlib.IsUpperHessenberg.norm_aeval_charpoly_trailingBlock_eq`, the shift polynomial of
`NLAlib.ritzValues` is $\chi_k$); `NLAlib.sum_lastRowWeights_mul_norm_eval_sq_sub_le` (with
`NLAlib.norm_le_specNorm_of_mem_ritzValues`) gives weight $\ge \psi^{2k}/(\kappa^2(2(\|\mathbf{H}
\|_2 + \beta))^{2k})$ within $\beta/(2c)$ of the Ritz values; each Ritz value has at most one
eigenvalue that close ($\beta/c < \Gamma$), so one eigenvalue $\mathbf{d}_j$ carries $1/k$ of it
and is within $\beta(1 + 1/(2c))$ of some $r_i$; then `NLAlib.sum_lastRowWeights_mul_sq_le` for
$(\mathbf{H} - r_i\mathbf{I})^{-k}$ and $k^{-1/(2k)} \ge 4/5$. L, about 90 lines (pigeonhole over
the $k$ Ritz values with the `List.Forall₂` bookkeeping).
Result: shifted-qr-ritz-dichotomy -/
theorem IsUpperHessenberg.isOptimalRitzValues_or_exists_mem_det_eq_zero_or_le
    {H V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ} (hH : IsUpperHessenberg H) {d : Fin (n + 1) → ℂ}
    (hV : IsUnit V) (hHV : H * V = V * Matrix.diagonal d) {k : ℕ} (hk : 0 < k) (hkn : k ≤ n)
    {Γ θ β : ℝ} (hgap : ∀ i j, i ≠ j → Γ ≤ ‖d i - d j‖)
    (hθ : (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) < θ) (hβ : 0 < β)
    (hβΓ : β < (θ / (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) - 1) / 2 * Γ)
    {rs : List ℂ} (hclose : List.Forall₂ (fun ρ r => ‖ρ - r‖ ≤ β) (ritzValues k H) rs) :
    IsOptimalRitzValues θ H rs ∨ ∃ r ∈ rs,
      (H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).det = 0 ∨
        2 / 5 * hessenbergPotential k H *
            (1 - (2 * pseudoConditionNumber V ^ 4) ^ ((2 * k : ℝ)⁻¹) / θ) ≤
          pseudoConditionNumber V ^ ((2 : ℝ) / k) * (specNorm H + β) * β *
            ‖WithLp.toLp 2 (((H - r • (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ))⁻¹ ^ k)
              (Fin.last n))‖ ^ ((k : ℝ)⁻¹) := by
  sorry

end NLAlib
