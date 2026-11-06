/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.RandomizedDeflation
public import NLAlibScaffold.Matrix.Computation.Deflation
public import NLAlibScaffold.RandomMatrix.Gaussian.Complex

/-!
# Randomized deflation with sharper Gaussian tails (scaffold, stage HDIAG-BOUNDS)

Statement for `NLAlib/Eigensolvers/RandomizedDeflation.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, items I5–I7): [Shah2024,
Theorem 3.3] with DF2', the norm tail CG4' and the smallest singular value tail
$\min(r^2, e r)x^2$ (CG6 and CG6').

## Main results

* [DP1'](https://nla-lib.org/explore/#d/NLAlib.FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix').
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

-- The declaration name and a docstring line exceed 100 characters.
set_option linter.style.longLine false in
/-- **Accuracy of randomized deflation with probability, sharp tails** (DP1'): under the
hypotheses of DF2' for a standard complex Gaussian $\mathbf{G}$, with $t \ge 0$, $x > 0$,
$\bar m = (1 + 2\beta + \|\mathbf{S}\|_2/8)\|\mathbf{S}^{-1}\|_2(2\sqrt2\sqrt n + t)/x$ and
$\bar m\beta \le 1/64$, the probability that no unitary $\mathbf{W}$ has
$\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le \tfrac32\bar m\beta$
is at most $e^{-t^2} + \min(r^2, e\,r)\,x^2$. [Shah2024, Theorem 3.3].
Proof: as DP1: on $\{\|\mathbf{G}\|_2 < 2\sqrt2\sqrt n + t\} \cap
\{\sigma_{\min}(\mathbf{V}^{\mathsf H}\mathbf{G}_1) > x\}$ apply DF2' (its $m$ is at most $\bar m$);
the first event fails with probability at most $e^{-t^2}$
(`NLAlib.measureReal_specNorm_ge_add_le_of_hasLaw_complexGaussianMatrix`), the second, through
`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix` and
`NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix`, with probability at most $r^2x^2$
(`NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`) and at most
$e\,r x^2$ (`NLAlib.measureReal_singularValues_le_le_exp_one_mul_of_hasLaw_complexGaussianMatrix`);
$u \ge 0$ and $\mu_{\mathrm{MM}}(n) \ge 0$ are derived as in DP1. M, about 100 lines (DP1's
proof with the two tails swapped). -/
theorem
    FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix'
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β t x : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β) (hβ₁ : β ≤ 1) (ht : 0 ≤ t) (hx : 0 < x)
    (hmβ : (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x * β ≤
      1 / 64)
    (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β) (hτ : τ ≤ specNorm S * x)
    (hτN : τ * √(n : ℝ) ≤ x)
    (hΩ : 2 * (specNorm S + 1) * (2 * √2 * √(n : ℝ) + t) ≤ Ω)
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {μ : Measure Ω'} {G : Ω' → Matrix (Fin n) (Fin n) ℂ}
    (hG : HasLaw G (complexGaussianMatrix (Fin n) (Fin n)) μ) :
    μ.real {ω | ¬ ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' (G ω))) ≤
        3 / 2 * ((1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * (2 * √2 * √(n : ℝ) + t) / x) *
          β} ≤
      Real.exp (-t ^ 2) + min ((r : ℝ) ^ 2) (Real.exp 1 * r) * x ^ 2 := by
  sorry

end NLAlib
