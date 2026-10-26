/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Basic.BlockSpace
public import NLAlib.Matrix.Basic.Projector

/-!
# Block Krylov spaces of a diagonal matrix: the level decomposition (scaffold)

Statement for `NLAlib/Krylov/Basic/BlockSpace.lean` (stage LB-C1, design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md` §3.4). For a diagonal
$\mathbf{D} = \operatorname{diag}(\mathbf{d})$ the block Krylov space of $[\mathbf{g}, \mathbf{G}]$
splits over the levels $t$ of $\mathbf{d}$: on the coordinates $\{i : d_i = t\}$ a vector of the
space is $f_0(t)\mathbf{g}_t + \mathbf{G}_t\mathbf{f}(t)$. So the residual
$\mathbf{g} - \mathbf{D}\mathbf{x}$ of $\mathbf{x} \in \mathcal{K}_s$ is at least, on each level,
the residual polynomial at $t$ times the part of $\mathbf{g}_t$ orthogonal to the columns of
$\mathbf{G}_t$.

## Main results

* `NLAlib.exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq`.
-/

@[expose] public section

open Polynomial
open scoped Matrix

namespace NLAlib

/-- **Level decomposition of a Krylov residual**: let
$\mathbf{D} = \operatorname{diag}(\mathbf{d})$, $\mathbf{g} \in \mathbb{R}^n$ and
$\mathbf{G} \in \mathbb{R}^{n \times c}$. For every $\mathbf{x}$ in
$\mathcal{K}_s(\mathbf{D}, [\mathbf{g}, \mathbf{G}])$ there is a real $r$ with $\deg r \le s$ and
$r(0) = 1$ such that
$$\sum_{t} r(t)^2\,\bigl\|(\mathbf{I} - \mathbf{P}_{\mathbf{G}_t})\,\mathbf{g}_t\bigr\|^2 \le
\|\mathbf{g} - \mathbf{D}\mathbf{x}\|^2 \,,$$
the sum over the distinct values $t$ of $\mathbf{d}$, with $\mathbf{g}_t$, $\mathbf{G}_t$ the rows
$\{i : d_i = t\}$ of $\mathbf{g}$, $\mathbf{G}$ and $\mathbf{P}_{\mathbf{G}_t}$ the projector onto
the range of $\mathbf{G}_t$.
[Shamir2026, Section 3.3]; there in the proof of Theorem 1, with $r = 1 - p_0$.
Proof: `NLAlib.mem_blockKrylovSpace_iff` writes $\mathbf{x} = f_0(\mathbf{D})\mathbf{g} +
\sum_j f_j(\mathbf{D})\mathbf{G}_{:,j}$ with $\deg f_j < s$; set $r = 1 - X f_0$
(`Polynomial.degree_sub_le`, `Polynomial.eval_mul_X`). On level $t$, $(\mathbf{g} -
\mathbf{D}\mathbf{x})_t = r(t)\mathbf{g}_t - \mathbf{G}_t\mathbf{y}_t$
(`Matrix.mulVec_diagonal`, `NLAlib.aeval_diagonal_self`); its norm is at least that of its
projection by $\mathbf{I} - \mathbf{P}_{\mathbf{G}_t}$ (`NLAlib.rangeProjector_mulVec_mulVec`,
`NLAlib.isStarProjection_rangeProjector`), and $\|\mathbf{v}\|^2$ is the sum over the levels of
the squared norms of the blocks (`Finset.sum_fiberwise`). M, about 60 lines. -/
theorem exists_sum_eval_sq_mul_norm_sq_le_norm_sub_mulVec_sq {n c : Type*} [Fintype n]
    [DecidableEq n] [Fintype c] (d g : n → ℝ) (G : Matrix n c ℝ) {s : ℕ} {x : n → ℝ}
    (hx : x ∈ blockKrylovSpace (Matrix.diagonal d)
      (Matrix.fromCols (Matrix.replicateCol Unit g) G) s) :
    ∃ r : ℝ[X], r.degree ≤ s ∧ r.eval 0 = 1 ∧
      ∑ t ∈ Finset.univ.image d, r.eval t ^ 2 *
          ‖WithLp.toLp 2 ((1 - rangeProjector (G.submatrix (Subtype.val : {i // d i = t} → n) id))
            *ᵥ fun i => g i.1)‖ ^ 2 ≤
        ‖WithLp.toLp 2 (g - Matrix.diagonal d *ᵥ x)‖ ^ 2 := by
  sorry

end NLAlib
