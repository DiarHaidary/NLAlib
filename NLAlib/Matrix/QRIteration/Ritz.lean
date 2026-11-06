/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import NLAlib.Matrix.QRIteration.EigenvectorWeights
public import NLAlib.Matrix.QRIteration.ShiftedQR

/-!
# Optimal and promising Ritz values

The two notions of approximate Ritz value that drive the shifting strategy of
[BanksGarzaVargasSrivastava2021]:

* `NLAlib.IsOptimalRitzValues θ H ss`: the shift polynomial of `ss` nearly minimises
  $\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\|$ over monic $p$ of its degree, whose minimum is
  $\psi_k(\mathbf{H})^k$ ($\theta$-optimal Ritz values, Definition 1.5 there);
* `NLAlib.IsPromisingRitzValue α V d ss r`: the single shift $r$ captures, up to $\alpha^k$, the
  inverse moment of the whole shift polynomial against the last-row weights (Definition 4.3
  there);

and the binary search `NLAlib.findRitz` (the subroutine $\mathrm{Find}$ of §4.3 there), which
halves the list $\log_2 k$ times, keeping the half whose inverse shift polynomial has the larger
last row. All are mathematical objects: norms and inverses are exact.

## Main definitions

* `NLAlib.IsOptimalRitzValues`, `NLAlib.IsPromisingRitzValue`, `NLAlib.findRitz`.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {n : ℕ}

/-- A list `ss` of $k$ shifts is a set of **$\theta$-optimal Ritz values** of $\mathbf{H}$ if
$$\|\mathbf{e}_n^{\mathsf{H}}p(\mathbf{H})\| \le (\theta\,\psi_k(\mathbf{H}))^k,\qquad
p(z) = \prod_{s \in \mathrm{ss}} (z - s)\,.$$
For upper Hessenberg $\mathbf{H}$ and $k \le n$, $\psi_k(\mathbf{H})^k$ is the minimum of
$\|\mathbf{e}_n^{\mathsf{H}}q(\mathbf{H})\|$ over monic $q$ of degree $k$, attained by the
characteristic polynomial of the trailing block, so this is
[BanksGarzaVargasSrivastava2021, Definition 1.5] with the minimum written out. -/
def IsOptimalRitzValues (θ : ℝ) (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (ss : List ℂ) :
    Prop :=
  ‖WithLp.toLp 2 ((Polynomial.aeval H (shiftPoly ss)) (Fin.last n))‖ ≤
    (θ * hessenbergPotential ss.length H) ^ ss.length

/-- A member $r$ of a list `ss` of $k$ shifts is **$\alpha$-promising** for the eigenvector
matrix $\mathbf{V}$ and eigenvalues $\mathbf{d}$ if, with $w$ the last-row weights of
$\mathbf{V}$ and $p(z) = \prod_{s \in \mathrm{ss}} (z - s)$,
$$\sum_i \frac{w_i}{\lvert p(\mathbf{d}_i)\rvert} \le
\alpha^k \sum_i \frac{w_i}{\lvert\mathbf{d}_i - r\rvert^k}\,.$$
It is meaningful when no shift is an eigenvalue (division by zero gives $0$ in Lean); the
theorems assume so. [BanksGarzaVargasSrivastava2021, Definition 4.3], with
$\mathbb{E}\,f(Z_{\mathbf{H}}) = \sum_i w_i f(\mathbf{d}_i)$. -/
def IsPromisingRitzValue (α : ℝ) (V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (d : Fin (n + 1) → ℂ) (ss : List ℂ) (r : ℂ) : Prop :=
  r ∈ ss ∧ ∑ i, lastRowWeights V i / ‖(shiftPoly ss).eval (d i)‖ ≤
    α ^ ss.length * ∑ i, lastRowWeights V i / ‖d i - r‖ ^ ss.length

/-- The **binary search for a promising Ritz value** ($\mathrm{Find}$ of
[BanksGarzaVargasSrivastava2021, §4.3]). `findRitz H m e ss` with `ss` of length $2^m$ splits
`ss` into its first and second halves $a$, $b$, keeps the half $h$ with the larger
$\|\mathbf{e}_n^{\mathsf{H}}p_h(\mathbf{H})^{-e}\|$ (the first on a tie), and recurses with
exponent $2e$; after $m$ halvings one shift is left. The strategy calls it with $e = 1$, so
that level $j$ compares degree $2^{m-1}$ polynomials $p_h^{2^{j-1}}$, as in the paper. With
$p_h(\mathbf{H})$ singular the inverse is Lean's junk value; the analysis assumes that no shift
is an eigenvalue.
Algorithm: shifted-qr (specification) -/
noncomputable def findRitz (H : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    ℕ → ℕ → List ℂ → ℂ
  | 0, _, ss => ss.headD 0
  | m + 1, e, ss =>
    if ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.drop (ss.length / 2))))⁻¹ ^ e)
          (Fin.last n))‖ ≤
        ‖WithLp.toLp 2 (((Polynomial.aeval H (shiftPoly (ss.take (ss.length / 2))))⁻¹ ^ e)
          (Fin.last n))‖ then
      findRitz H m (2 * e) (ss.take (ss.length / 2))
    else
      findRitz H m (2 * e) (ss.drop (ss.length / 2))

end NLAlib
