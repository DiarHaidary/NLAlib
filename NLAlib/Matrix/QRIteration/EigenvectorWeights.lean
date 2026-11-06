/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Data.Complex.Basic

/-!
# Last-row weights of an eigenvector matrix

For an invertible eigenvector matrix $\mathbf{V}$ of a diagonalizable $\mathbf{H}$, the weights
$$w_i = \frac{\lvert\mathbf{V}_{n,i}\rvert^2}{\|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2}$$
form a probability vector on the eigenvalues. Sums against them are the "approximate functional
calculus" of [BanksGarzaVargasSrivastava2021, Definition 4.1]: the law of the random variable
$Z_{\mathbf{H}}$ there, written as finite weighted sums here. For normal $\mathbf{H}$ and unitary
$\mathbf{V}$ it is the spectral measure of $\mathbf{H}$ at $\mathbf{e}_n$.

## Main definitions

* `NLAlib.lastRowWeights`.
-/

@[expose] public section

namespace NLAlib

variable {n : ℕ}

/-- The **last-row weights** of a square matrix $\mathbf{V}$:
$w_i = \lvert\mathbf{V}_{n,i}\rvert^2 / \|\mathbf{e}_n^{\mathsf{H}}\mathbf{V}\|^2$, the squared
moduli of the last row normalised to sum to $1$ (all $0$ if the last row vanishes, which an
invertible $\mathbf{V}$ excludes). With $\mathbf{H}\mathbf{V} = \mathbf{V}\operatorname{diag}(
\mathbf{d})$, the weight $w_i$ sits on the eigenvalue $\mathbf{d}_i$: this is the distribution of
$Z_{\mathbf{H}}$ in [BanksGarzaVargasSrivastava2021, Definition 4.1], where $\mathbf{V}$ is
normalised by $\|\mathbf{V}\|_2 = \|\mathbf{V}^{-1}\|_2$, which no statement here needs. -/
noncomputable def lastRowWeights (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (i : Fin (n + 1)) :
    ℝ :=
  ‖V (Fin.last n) i‖ ^ 2 / ‖WithLp.toLp 2 (V (Fin.last n))‖ ^ 2

end NLAlib
