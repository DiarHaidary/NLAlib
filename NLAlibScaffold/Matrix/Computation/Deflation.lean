/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Deflation

/-!
# Sharper constants for deflation (scaffold, stage HDIAG-BOUNDS)

Statements for `NLAlib/Matrix/Computation/Deflation.lean` (design note
`docs/design/Eigensolvers-HermitianDiagonalization-Bounds.md`, item I7): the nearest unitary
rotation between two orthonormal bases at canonical-angle distance $\delta$ is within
$\sqrt2\,\delta$ (DF1', in place of $6\delta$), and the deterministic deflation bound with the
roundings charged at $1/16$ of the accuracy, so that the output error is $\tfrac32 m\beta$ with
$m \approx \|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2\|(\mathbf{V}^{\mathsf H}\mathbf{G}_1)^{-1}\|_2$
(DF2', in place of $6m\beta$ with the factor $\|\mathbf{S}\|_2 + \beta + 1$).

## Main results

* `NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul` (DF1').
* `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le`
  (DF2').
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **Orthonormal bases close up to a rotation, with constant $\sqrt2$** (DF1'): if
$\mathbf{U}, \mathbf{Q}'$ have orthonormal columns and $\|\mathbf{U} - \mathbf{Q}'\mathbf{C}\|_2
\le \delta$ for some $\mathbf{C}$, there is a unitary $\mathbf{W}$ with $\|\mathbf{U}\mathbf{W} -
\mathbf{Q}'\|_2 \le \sqrt2\,\delta$. The orthogonal Procrustes rotation: for canonical angles
$\theta_i$ the optimum is $\max_i 2\sin(\theta_i/2)$ [StewartSun1990, Chapter I.5].
Proof: $(\mathbf{I} - \mathbf{Q}'\mathbf{Q}'^{\mathsf H})\mathbf{U} = (\mathbf{I} -
\mathbf{Q}'\mathbf{Q}'^{\mathsf H})(\mathbf{U} - \mathbf{Q}'\mathbf{C})$, so for a unit $v$,
$\|\mathbf{Q}'^{\mathsf H}\mathbf{U}v\|^2 \ge 1 - \delta^2$ and
$\sigma_{\min}(\mathbf{Q}'^{\mathsf H}\mathbf{U}) \ge \sqrt{1 - \delta^2}$ (for $\delta \le 1$;
for $\delta > 1$ use $\|\mathbf{U}\mathbf{W} - \mathbf{Q}'\|_2^2 \le 2$ below). Take $\mathbf{W}$
the polar factor of $\mathbf{U}^{\mathsf H}\mathbf{Q}'$ (`NLAlib.polarFactor`), so that
$\mathbf{W}^{\mathsf H}\mathbf{U}^{\mathsf H}\mathbf{Q}' = \mathbf{P} \succeq 0$ with
eigenvalues the singular values; then $(\mathbf{U}\mathbf{W} - \mathbf{Q}')^{\mathsf
H}(\mathbf{U}\mathbf{W} - \mathbf{Q}') = 2(\mathbf{I} - \mathbf{P})$ and
$\|\mathbf{U}\mathbf{W} - \mathbf{Q}'\|_2^2 = 2(1 - \sigma_{\min}) \le 2(1 - \sqrt{1 - \delta^2})
\le 2\delta^2$. M, about 90 lines (DF1's polar-factor facts reused). -/
theorem HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le_sqrt_two_mul
    {𝕜 : Type*} [RCLike 𝕜] {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]
    {U Q' : Matrix m r 𝕜} (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q')
    {C : Matrix r r 𝕜} {δ : ℝ} (hδ : specNorm (U - Q' * C) ≤ δ) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q') ≤ √2 * δ := by
  sorry

/-- **Deterministic accuracy of randomized deflation, sharp constants** (DF2'): under the
hypotheses of `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`
with the precision condition strengthened to $16(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} +
2\mu_{\mathrm{MM}}(n))u \le \beta$, the factor
$m = (1 + 2\beta + \|\mathbf{S}\|_2/8)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$ and $m\beta \le 1/64$, there is a unitary
$\mathbf{W}$ with $\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le
\tfrac32 m\beta$. [Shah2024, Theorem 3.3].
Proof: DF2's proof up to the bound $\|\mathbf{U} - \mathbf{Q}'_1\mathbf{C}\|_2 \le \delta$, where
the perturbation of $\mathbf{M}_1 = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf H}\mathbf{G}_1$ is
$\beta\|\mathbf{G}\|_2(1 + \beta)$ from $\widetilde{\mathbf{A}}$ plus the sampler, product and QR
roundings, at most $(\|\mathbf{S}\|_2 + \beta)\beta\|\mathbf{G}\|_2/16$ by the strengthened
condition, so $\delta \le m\beta$; then DF1' in place of DF1 ($\sqrt2\delta$) and the QR
orthogonality error $\mu_{\mathrm{QR}}u \le \beta/64 \le m\beta/64$. L, about 200 lines (DF2's
helpers reused). -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le_of_mul_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β mval : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hμM : 0 ≤ μM n) (hu₀ : 0 ≤ u) (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr)))
    (hm : mval = (1 + 2 * β + specNorm S / 8) * specNorm S⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹)
    (hmβ : mval * β ≤ 1 / 64) (hu : 16 * (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ specNorm S * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (specNorm S + β) * specNorm G ≤ Ω) (hΩG : specNorm G ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' G)) ≤ 3 / 2 * mval * β := by
  sorry

end NLAlib
