/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.RandomMatrix.Gaussian.Complex

/-!
# Randomized deflation with a complex Gaussian test matrix (scaffold)

Statement for a new file `NLAlib/Eigensolvers/RandomizedDeflation.lean` (stage HDIAG, wave W3,
design note `docs/design/Eigensolvers-HermitianDiagonalization.md` §3.6; the folder
`NLAlib/Eigensolvers` is open question OQ1 of the note). With a standard complex Gaussian sample,
the deterministic bound of
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`
holds with $m$ replaced by its high-probability bound ([Shah2024, Theorem 3.3]).

## Main results

* `NLAlib.FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- **Randomized deflation** (Theorem 3.3): under the machine contract
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with constants $\mu_{\mathrm{MM}}$,
$\mu_{\mathrm{QR}}$, $c_{\mathrm N}$, let $r \le n$, $\mathbf{U}, \mathbf{V} \in
\mathbb{C}^{n \times r}$ have orthonormal columns, $\mathbf{S}$ be invertible, $\mathbf{A} =
\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$ and the stored $\widetilde{\mathbf{A}}$ decode
within $\beta \le 1$ of $\mathbf{A}$, and let $\mathbf{G}$ be a standard complex Gaussian $n \times
n$ matrix. For $t \ge 0$ and $x > 0$ put
$$\bar m = (\|\mathbf{S}\|_2 + 2)\|\mathbf{S}^{-1}\|_2\,\frac{\sqrt2\,(2\sqrt n + t)}{x} \,.$$
If $\bar m\beta \le 1/5$,
$(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u
\le \beta$, $\tau \le \|\mathbf{S}\|_2 x$, $\sqrt n\,\tau \le x$ and $2(\|\mathbf{S}\|_2 +
1)\sqrt2(2\sqrt n + t) \le \Omega$, then
$$\mathbb{P}\bigl[\text{no unitary } \mathbf{W} \text{ has }
\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le 6\bar m\beta\bigr]
\le 2e^{-t^2/2} + r^2x^2 \,,$$
$\mathsf{deflate}$ the algorithm `NLAlib.deflate` with sample $\mathbf{G}$. [Shah2024, Theorem 3.3],
there with $(2\sqrt2 + t)\sqrt n$, failure $2e^{-nt^2} + (r/2)x^2$ and the requirement on $\beta$
written out; the constants differ through Lemmas 3.1 and 3.2.
Proof: outside the events $\{\|\mathbf{G}\|_2 \ge \sqrt2(2\sqrt n + t)\}$
(`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`) and
$\{\sigma_{r-1}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1) \le x\}$
(`NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix`,
`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`,
`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`), the matrix
$\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ is invertible with inverse of norm below $1/x$
(`NLAlib.singularValues_last_mul_norm_le`), $\|\mathbf{G}\|_2 \ge x$, so $m \le \bar m$,
$\|\mathbf{G}\|_2 < \sqrt2(2\sqrt n + t) \le \Omega$ (from `hΩ`), and
`NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le` applies;
union bound (`MeasureTheory.measureReal_union_le`, `MeasureTheory.measureReal_mono`). Case $r = 0$
trivial. M, about 60 lines. -/
theorem FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x * β ≤ 1 / 5)
    (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (√2 * (2 * √(n : ℝ) + t)) ≤ Ω)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) :
    μ.real {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        6 * ((specNorm S + 2) * specNorm S⁻¹ * (√2 * (2 * √(n : ℝ) + t)) / x) * β} ≤
      2 * Real.exp (-t ^ 2 / 2) + r ^ 2 * x ^ 2 := by
  sorry

end NLAlib
