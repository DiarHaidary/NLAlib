/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Structural.Truncation
public import NLAlib.Matrix.Subspaces.ObliqueProjector
public import NLAlibScaffold.Matrix.Perturbation.BestRankApprox

/-!
# Late truncation of generalized Nyström: the localized deterministic bound (research)

Generalized Nyström is the randomized SVD plus its core noise,
$\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}) = \mathbf{R} + \mathbf{N}$ with
$\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$ and
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} -
\mathbf{R})$, and its late truncation splits orthogonally into the range-finder residual and a
perturbed truncation of $\mathbf{R}$; the localized perturbed truncation
(`NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window`) then bounds the error
pointwise. Joins `NLAlib/LowRank/Structural/Truncation.lean`. Research statements for
`docs/design/research/TruncatedGN-Upper.md` (T-series). Not for `main`. Proofs deferred.

## Main results

* `NLAlib.generalizedNystrom_eq_rsvd_add`: $\mathsf{gn} = \mathbf{R} + \mathbf{N}$ (T1).
* `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_eq_add`: the Pythagorean split (T2).
* `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_window`: the pointwise
  localized bound (T3).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {l m n p : Type*} [Fintype l] [Fintype m] [Fintype n]
  [Fintype p]

/-- **Generalized Nyström is the randomized SVD plus the core noise**: for
$\mathbf{A} \in \Bbbk^{m \times n}$, $\mathbf{\Omega} \in \Bbbk^{n \times \ell}$ and
$\mathbf{\Psi} \in \Bbbk^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
with $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$$\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}) = \mathbf{R} +
\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} - \mathbf{R})\,.$$
No printed source.
Proof: S, about 10 lines. `generalizedNystrom` is
$\mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A}$; write
$\mathbf{A} = \mathbf{R} + (\mathbf{A} - \mathbf{R})$, `Matrix.mul_add`, and
$\mathbf{\Pi}\mathbf{R} = \mathbf{R}$ by `obliqueProjector_mul_eq_self_of_range_le` with
`range_rsvd_le`. -/
theorem generalizedNystrom_eq_rsvd_add {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {Ψ : Matrix m p 𝕜}
    (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) :
    generalizedNystrom A Ω Ψ = rsvd A Ω + obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω) := by
  rw [generalizedNystrom, Matrix.mul_sub,
    obliqueProjector_mul_eq_self_of_range_le h (range_rsvd_le A Ω)]
  abel

/-- **The truncated generalized Nyström error splits**: for $\mathbf{A} \in \Bbbk^{m \times n}$,
$\mathbf{\Omega} \in \Bbbk^{n \times \ell}$, $\mathbf{\Psi} \in \Bbbk^{m \times p}$ and any $k$,
with $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$,
$$\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 = \|\mathbf{A} - \mathbf{R}\|_{\mathsf{F}}^2 + \|\mathbf{R} -
\llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k\|_{\mathsf{F}}^2\,,$$
with no rank hypothesis: the truncation lies in $\operatorname{range}(\mathbf{A}\mathbf{\Omega})$.
No printed source.
Proof: S, about 15 lines. As in
`IsBestRankApprox.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add`: with
$\mathbf{Y} = \llbracket\mathsf{gn}\rrbracket_k$, $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{Y}
= \mathbf{Y}$ (`rangeProjector_mul_eq_self_iff`, `range_truncatedSVD_le`,
`range_generalizedNystrom_le`), then `frobNorm_sub_mul_sq` at
$\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$ (`isStarProjection_rangeProjector`,
`IsStarProjection.rangeProjector_eq`, `sub_rsvd`). -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_eq_add (A : Matrix m n 𝕜)
    (Ω : Matrix n l 𝕜) (Ψ : Matrix m p 𝕜) (k : ℕ) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 =
      frobNorm (A - rsvd A Ω) ^ 2 +
        frobNorm (rsvd A Ω - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 := by
  sorry

/-- **The localized truncated generalized Nyström error, deterministic form**: for
$\mathbf{A} \in \mathbb{R}^{m \times n}$, $\mathbf{\Omega} \in \mathbb{R}^{n \times \ell}$ and
$\mathbf{\Psi} \in \mathbb{R}^{m \times p}$ such that
$\mathbf{\Psi}^{\mathsf{T}}\mathbf{A}\mathbf{\Omega}$ has the rank of $\mathbf{A}\mathbf{\Omega}$,
$1 \le k$, $\mathbf{R} = \mathsf{rsvd}(\mathbf{A}, \mathbf{\Omega})$, the core noise
$\mathbf{N} = \mathbf{\Pi}_{\mathbf{A}\mathbf{\Omega},\mathbf{\Psi}^{\mathsf{T}}}(\mathbf{A} -
\mathbf{R})$, $\theta = \sigma_{k-1}(\mathbf{R})$, and a window $a \le k \le b$ with
$2\theta \le \sigma_i(\mathbf{R})$ for $i < a$, $\sigma_a(\mathbf{R}) \le 2\theta$ and
$\sigma_b(\mathbf{R}) \le \theta/2$, with $\mathbf{P}_i$, $\mathbf{P}'_i$ the range projectors of
$\llbracket\mathbf{R}\rrbracket_i$ and of its transpose,
$$\|\mathbf{A} - \llbracket\mathsf{gn}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi})\rrbracket_k
\|_{\mathsf{F}}^2 \le \|\mathbf{A} - \llbracket\mathbf{R}\rrbracket_k\|_{\mathsf{F}}^2 +
500k\,\|\mathbf{N}\|_2^2 + 40\,\theta\min(k, b - k)\,
\|(\mathbf{P}_b - \mathbf{P}_a)\mathbf{N}(\mathbf{P}'_b - \mathbf{P}'_a)\|_2\,.$$
For the choice `truncatedSVD` makes. No printed source.
Proof: S, about 20 lines. `NLAlib.frobNorm_sub_truncatedSVD_generalizedNystrom_sq_eq_add` and
`frobNorm_sub_truncatedSVD_rsvd_sq` reduce to $\|\mathbf{R} - \mathbf{Y}\|^2 \le
\|\mathbf{R} - \llbracket\mathbf{R}\rrbracket_k\|^2 + \ldots$ with
$\mathbf{Y} = \llbracket\mathsf{gn}\rrbracket_k$, a best rank-$k$ approximation of
$\mathbf{R} + \mathbf{N}$ by `isBestRankApprox_truncatedSVD` and
`NLAlib.generalizedNystrom_eq_rsvd_add`; apply
`NLAlib.IsBestRankApprox.frobNorm_sub_sq_le_add_specNorm_sq_add_window`. -/
theorem frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_add_window {A : Matrix m n ℝ}
    {Ω : Matrix n l ℝ} {Ψ : Matrix m p ℝ} (h : (Ψᴴ * (A * Ω)).rank = (A * Ω).rank) {k : ℕ}
    (hk : 1 ≤ k) {a b : ℕ} (hak : a ≤ k) (hkb : k ≤ b)
    (ha : ∀ i < a, 2 * singularValues (rsvd A Ω) (k - 1) ≤ singularValues (rsvd A Ω) i)
    (ha₂ : singularValues (rsvd A Ω) a ≤ 2 * singularValues (rsvd A Ω) (k - 1))
    (hb : singularValues (rsvd A Ω) b ≤ singularValues (rsvd A Ω) (k - 1) / 2) :
    frobNorm (A - truncatedSVD (generalizedNystrom A Ω Ψ) k) ^ 2 ≤
      frobNorm (A - truncatedSVD (rsvd A Ω) k) ^ 2 +
        500 * k * specNorm (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) ^ 2 +
        40 * singularValues (rsvd A Ω) (k - 1) * ((min k (b - k) : ℕ) : ℝ) *
          specNorm ((rangeProjector (truncatedSVD (rsvd A Ω) b) -
              rangeProjector (truncatedSVD (rsvd A Ω) a)) *
            (obliqueProjector (A * Ω) Ψᴴ * (A - rsvd A Ω)) *
            (rangeProjector (truncatedSVD (rsvd A Ω) b)ᴴ -
              rangeProjector (truncatedSVD (rsvd A Ω) a)ᴴ)) := by
  sorry

end NLAlib
