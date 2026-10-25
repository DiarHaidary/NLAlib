/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.Truncation

/-!
# Truncated generalized Nyström: the sharpened and the reverse perturbed truncation (stage S10)

Three deterministic statements for `NLAlib/LowRank/Structural/Truncation.lean`, next to
`NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm`. With
$\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$:

* truncated generalized Nyström never beats the truncated randomized SVD;
* an upper bound in which the cross term carries
  $\|\llbracket\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}$, the energy
of
  the next $k$ singular values only, in place of $\|\mathbf{R} -
\llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}$;
* a lower bound: the error is at least the truncated randomized SVD error plus the noise in the
  oracle subspace, $\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2$, up
  to $\|\mathbf{N}\|_{\mathsf{F}}^4$ over the gap $\sigma_{k-1}(\mathbf{R})^2 -
\sigma_k(\mathbf{R})^2$.
  It feeds the lower bound on Epperly and Webber's instance
  (`NLAlib.LowRank.Optimality.TruncatedGeneralizedNystrom`).

Both are new (research note `reports/OP2-TruncatedGN.md` of the NLAlib workflow, §2, D1–D2;
the lower bound is this design's). Design: `docs/design/LowRank-EstimatorLowerBounds.md` §3.2.
Proofs deferred.

## Main results

* `NLAlib.frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq`
* `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm`
* `NLAlib.le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq`
-/

@[expose] public section

open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p]

/-- **Truncated generalized Nyström never beats the truncated randomized SVD**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$
has the rank of $\mathbf{A}\mathbf{\Omega}$, and any $k$,
$$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})\rrbracket_k\|_{\mathsf{F}}^2
\le
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2\,:$$
both outputs lie in $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$, and the truncated randomized
SVD
is the best rank-$k$ approximation there. For the choice `truncatedSVD` makes.
Proof: S, about 15 lines. The core form (`exists_core_generalizedNystrom`, private: copy as a
private helper) gives the error as $\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 +
\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}}^2$ with $\operatorname{rank}\mathbf{Y} \le k$; Eckart–Young
(`frobNorm_sub_truncatedSVD_le`) and the third conjunct give
$\|\mathbf{C} - \mathbf{Y}\|_{\mathsf{F}} \ge \|\mathbf{R} -
\llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}$;
Pythagoras (`truncatedSVD_rsvd_eq_rangeProjector_mul`, `sub_rsvd`) splits
$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2$ the same way. -/
theorem frobNorm_sub_truncatedSVD_rsvd_sq_le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 := by
  sorry

/-- **The perturbed truncation with the next-$k$ tail**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$
has the rank of $\mathbf{A}\mathbf{\Omega}$, any $k$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A},
\mathbf{\Omega})$,
the core noise $\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}
(\mathbf{A} - \mathbf{R})$ and
$\gamma_k = \|\llbracket\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\rrbracket_k\|_{\mathsf{F}}
= (\sum_{k \le i < 2k}\sigma_i(\mathbf{R})^2)^{1/2}$,
$$\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
4\sqrt{k}\,\|\mathbf{N}\|_2\,\gamma_k + 12k\,\|\mathbf{N}\|_2^2\,.$$
Since $\gamma_k \le \min(\|\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}},
\sqrt{k}\,\sigma_k(\mathbf{R}))$, it sharpens the cross term $4\sqrt{2k}\,\gamma\,\|\mathbf{N}\|_2$
of `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm` (expanded), at the
price of $12k$ for $8k$ in the noise term. For the choice `truncatedSVD` makes.
No printed source. New (research note OP2, §2, D2, with the constants recomputed here).
Proof: M, about 80 lines. Core form as in `exists_core_generalizedNystrom` (private in
`NLAlib/LowRank/Structural/Truncation.lean`: copy its proof as a private helper, extended to
return the basis $\mathbf{Q}$ with $\mathbf{N} = \mathbf{Q}\mathbf{E}$): the error is
$\|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 + \|\mathbf{B} - \mathbf{P}(\mathbf{B} +
\mathbf{E})\|_{\mathsf{F}}^2$
with $\mathbf{B} = \mathbf{Q}^{\mathsf{H}}\mathbf{A}$ and $\mathbf{P}$ the range projector of the
best approximation $\mathbf{Y} = \mathbf{P}(\mathbf{B}+\mathbf{E})$. With
$\mathbf{P}_B$ the range projector of $\llbracket\mathbf{B}\rrbracket_k$, $x =
\|\llbracket\mathbf{B}\rrbracket_k\|_{\mathsf{F}}^2 - \|\mathbf{P}\mathbf{B}\|_{\mathsf{F}}^2$,
$w = \|\mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2$: (D1) optimality of $\mathbf{P}$ against
$\mathbf{P}_B$
gives $x + w \le 2\operatorname{Re}\langle(\mathbf{P} - \mathbf{P}_B)\mathbf{B}, \mathbf{E}\rangle +
2w$;
(D2) $\|(\mathbf{P} - \mathbf{P}_B)\mathbf{B}\|_{\mathsf{F}}^2 = x + 2\gamma_P^2$ with
$\gamma_P = \|\mathbf{P}(\mathbf{B} - \llbracket\mathbf{B}\rrbracket_k)\|_{\mathsf{F}} \le \gamma_k$
(orthogonal row and column spaces of the two SVD pieces; Ky Fan
`exists_rank_le_specNorm_le_one_frobInner_eq_kyFanNorm`-type bound for a rank-$k$ projector);
$\operatorname{rank}(\mathbf{P} - \mathbf{P}_B) \le 2k$ so the inner product is at most
$\sqrt{2k}\,\|\mathbf{E}\|_2\sqrt{x + 2\gamma_P^2}$; $w \le k\|\mathbf{E}\|_2^2$. With
$S = x + w$ and $u = \sqrt{S + 2\gamma_P^2}$: $u^2 - 2\gamma_P^2 \le 2\sqrt{2k}\,e\,u + 2ke^2$, so
$u \le \sqrt{2k}e + 2\sqrt{k}e + \sqrt2\gamma_P$ and
$S \le 4\sqrt{k}\,e\,\gamma_P + (6 + 4\sqrt2)ke^2$. -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_specNorm_mul_frobNorm
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 +
        4 * √(k : ℝ) * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) *
          frobNorm (truncatedSVD (rsvd A Ω - truncatedSVD (rsvd A Ω) k) k) +
        12 * k * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 2 := by
  sorry

/-- **The reverse perturbed truncation**: for $\mathbf{A} \in \Bbbk^{m \times n}$,
$\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and $\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
$k \ge 1$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ with a gap
$g = \sigma_{k-1}(\mathbf{R})^2 - \sigma_k(\mathbf{R})^2 > 0$, and the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$,
$$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
\|\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N}\|_{\mathsf{F}}^2 -
\frac{\|\mathbf{N}\|_{\mathsf{F}}^4}{g} \le
\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2\,.$$
Truncated generalized Nyström keeps the noise that falls in the dominant subspace of
$\mathbf{R}$, up to a perturbation that vanishes as the gap grows. For the choice
`truncatedSVD` makes (the left side is choice-free under the gap).
No printed source. New (this design, §3.2, after research note OP2, §1).
Proof: M, about 80 lines. Core form as in the previous statement: the excess over
$\|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2$ is $x + w$ with
$\mathbf{P}_{\llbracket\mathbf{R}\rrbracket_k}\mathbf{N} = \mathbf{Q}\mathbf{P}_B\mathbf{E}$. With
$\mathbf{B}\mathbf{B}^{\mathsf{H}} = \sum_i \lambda_i\mathbf{u}_i\mathbf{u}_i^{\mathsf{H}}$, $w_i =
\mathbf{u}_i^{\mathsf{H}}\mathbf{P}\mathbf{u}_i \in [0,1]$, $\sum_i w_i \le k$ and
$t = \sum_{i<k}(1 - w_i)$: $x \ge (\lambda_{k-1} - \lambda_k)\,t = g\,t$ (split the sums at $k$);
$\|\mathbf{P} - \mathbf{P}_B\|_{\mathsf{F}}^2 = \operatorname{tr}\mathbf{P} - k + 2t \le 2t$; and
$\lvert\|\mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2 - \|\mathbf{P}_B\mathbf{E}\|_{\mathsf{F}}^2\rvert =
\lvert\langle\mathbf{P} - \mathbf{P}_B, \mathbf{E}\mathbf{E}^{\mathsf{H}}\rangle\rvert \le
\sqrt{2t}\,\|\mathbf{E}\|_{\mathsf{F}}^2$. So $x + w \ge \|\mathbf{P}_B\mathbf{E}\|_{\mathsf{F}}^2 +
g t - \sqrt{2t}\,\|\mathbf{E}\|_{\mathsf{F}}^2 \ge \|\mathbf{P}_B\mathbf{E}\|_{\mathsf{F}}^2 -
\|\mathbf{E}\|_{\mathsf{F}}^4/(2g)$ (minimise the quadratic in $\sqrt t$; the statement drops the
factor $2$). -/
theorem le_frobNorm_sub_truncatedSVD_generalizedNystrom_sq
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) {k : ℕ} (hk : 0 < k)
    (hgap : singularValues (rsvd A Ω) k ^ 2 < singularValues (rsvd A Ω) (k - 1) ^ 2) :
    frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 +
        frobNorm (rangeProjector (truncatedSVD (rsvd A Ω) k) *
          (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω))) ^ 2 -
        frobNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 4 /
          (singularValues (rsvd A Ω) (k - 1) ^ 2 - singularValues (rsvd A Ω) k ^ 2) ≤
      frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 := by
  sorry

end NLAlib
