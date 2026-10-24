/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Spectral.SpectralMeasure

/-!
# Spectral measures: the additions of stage KS7

Statements for `NLAlib/Matrix/Spectral/SpectralMeasure.lean` whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.7). For Hermitian $\mathbf{A}$ the inner
product of $p(\mathbf{A})\mathbf{b}$ and $r(\mathbf{A})\mathbf{b}$, $p$, $r$ real polynomials, is
the $L^2(\mu_{\mathbf{A},\mathbf{b}})$ inner product of $p$ and $r$. The spectral measure of a
diagonal matrix is the sum of point masses at its entries, and every finite measure carried by a
finite set is the spectral measure of a real diagonal matrix and a vector.

## Main results

* `Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec`,
  `Matrix.IsHermitian.norm_aeval_mulVec_sq`: polynomial inner products.
* `NLAlib.spectralMeasure_diagonal`: the spectral measure of a diagonal matrix.
* `NLAlib.spectralMeasure_diagonal_sqrt_of_ae_mem`: every finite atomic measure is a spectral
  measure.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix MatrixOrder ComplexOrder ENNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- Polynomial inner products are spectral integrals: for Hermitian $\mathbf{A}$, every
$\mathbf{b}$ and real polynomials $p$, $r$,
$$\langle p(\mathbf{A})\mathbf{b}, r(\mathbf{A})\mathbf{b}\rangle =
\int p\,r\,d\mu_{\mathbf{A},\mathbf{b}}\,,$$
the inner product of $p$ and $r$ in $L^2(\mu_{\mathbf{A},\mathbf{b}})$.
Proof: M, about 25 lines. `star_mulVec_dotProduct`, `(hA.aeval p).eq` (a real polynomial of a
Hermitian matrix is Hermitian), `Matrix.mulVec_mulVec`, `← map_mul`;
`Matrix.IsHermitian.integral_eval_spectralMeasure` with `eval_mul`; the quadratic form of a
Hermitian matrix is real (`Matrix.IsHermitian.coe_re_quadForm`). -/
theorem _root_.Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (p r : ℝ[X]) :
    star (aeval A p *ᵥ b) ⬝ᵥ (aeval A r *ᵥ b) =
      ((∫ x, p.eval x * r.eval x ∂spectralMeasure A b : ℝ) : 𝕜) := by
  sorry

/-- Polynomial norms are spectral integrals: for Hermitian $\mathbf{A}$, every $\mathbf{b}$ and
every real polynomial $p$, $\|p(\mathbf{A})\mathbf{b}\|^2 = \int p^2\,d\mu_{\mathbf{A},\mathbf{b}}$.
Proof: S, about 10 lines. The squared norm as `re (star v ⬝ᵥ v)` (as in
`norm_arnoldiMatrix_col_last`), then `Matrix.IsHermitian.star_aeval_mulVec_dotProduct_aeval_mulVec`
with $r = p$ (`sq`, `RCLike.ofReal_re`). -/
theorem _root_.Matrix.IsHermitian.norm_aeval_mulVec_sq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (p : ℝ[X]) :
    ‖WithLp.toLp 2 (aeval A p *ᵥ b)‖ ^ 2 = ∫ x, p.eval x ^ 2 ∂spectralMeasure A b := by
  sorry

/-- The spectral measure of a diagonal matrix: for real $\mathbf{d}$ and every $\mathbf{w}$,
$$\mu_{\operatorname{diag}(\mathbf{d}),\,\mathbf{w}} = \sum_i\lvert\mathbf{w}_i\rvert^2\,
\delta_{\mathbf{d}_i}\,.$$
Proof: S, about 10 lines. `HasOrthonormalCols.spectralMeasure_eq_sum` with $\mathbf{U} = \mathbf{I}$
(`HasOrthonormalCols` of `1` from `conjTranspose_one`, `Matrix.one_mul`), `one_mul`,
`Matrix.conjTranspose_one`, `Matrix.one_mulVec`. -/
theorem spectralMeasure_diagonal {r : Type*} [Fintype r] [DecidableEq r] (d : r → ℝ)
    (w : r → 𝕜) :
    spectralMeasure (Matrix.diagonal fun i => ((d i : ℝ) : 𝕜)) w =
      ∑ i, ENNReal.ofReal (‖w i‖ ^ 2) • Measure.dirac (d i) := by
  sorry

/-- Every finite measure carried by a finite set is a spectral measure: if a finite measure
$\nu$ is carried by a finite set $s \subseteq \mathbb{R}$, then $\nu$ is the spectral measure of
the real diagonal matrix of the points of $s$ and the vector of the square roots of their masses,
$\nu = \mu_{\operatorname{diag}(x)_{x\in s},\,(\sqrt{\nu\{x\}})_{x\in s}}$.
Proof: M, about 25 lines. `spectralMeasure_diagonal` (with `𝕜 := ℝ`); `Real.norm_eq_abs`, `sq_abs`,
`Real.sq_sqrt` (`measureReal_nonneg`), `ofReal_measureReal`; the sum over the subtype is
`Finset.sum_coe_sort`; `Measure.ae_mem_finset_iff` writes $\nu$ as the same sum. -/
theorem spectralMeasure_diagonal_sqrt_of_ae_mem {ν : Measure ℝ} [IsFiniteMeasure ν]
    {s : Finset ℝ} (hν : ∀ᵐ x ∂ν, x ∈ s) :
    spectralMeasure (Matrix.diagonal fun x : s => (x : ℝ)) (fun x => √(ν.real {(x : ℝ)})) = ν := by
  sorry

end NLAlib
