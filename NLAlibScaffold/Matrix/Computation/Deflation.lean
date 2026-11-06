/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Deflation
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.QR
public import NLAlib.Matrix.Norms.Compare
public import NLAlib.Matrix.Spectral.LeastSingularValue

/-!
# Deterministic accuracy of randomized deflation (scaffold)

Statements for `NLAlib/Matrix/Computation/Deflation.lean` (stage HDIAG, wave W3, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.6): the deterministic half of
[Shah2024, Theorem 3.3]. If $\widetilde{\mathbf{A}}$ is within $\beta$ of
$\mathbf{A} = \mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$ of rank $r$ and the sample
$\mathbf{G}$ has $\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ invertible ($\mathbf{G}_1$ its first $r$
columns), the computed basis is within $6m\beta$ of $\mathbf{U}\mathbf{W}$ for a unitary
$\mathbf{W}$, where $m = (\|\mathbf{S}\|_2 + \beta + 1)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$. The probabilistic half is in
`NLAlibScaffold/Eigensolvers/RandomizedDeflation.lean`.

## Main results

* `NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le`: a basis that spans
  nearly the range of a frame is near a rotation of the frame.
* `NLAlib.FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le`: the
  deterministic bound.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {m r : Type*} [Fintype m] [Fintype r] [DecidableEq r]

/-- **A near-basis close to a frame up to a change of basis is close to a rotation of it**: let
$\mathbf{U}, \mathbf{Q}' \in \Bbbk^{m \times r}$ have orthonormal columns, and
$\mathbf{Q}_1 \in \Bbbk^{m \times r}$, $\mathbf{C} \in \Bbbk^{r \times r}$ satisfy
$\|\mathbf{Q}_1 - \mathbf{Q}'\|_2 \le \nu$ and $\|\mathbf{U} - \mathbf{Q}_1\mathbf{C}\|_2 \le
\delta$ with $\nu \le \delta \le 1/5$. Then there is a unitary $\mathbf{W}$ with
$$\|\mathbf{U}\mathbf{W} - \mathbf{Q}_1\|_2 \le 6\delta \,.$$
[Shah2024, proof of Theorem 3.3]: the three inequalities there, which avoid the square-root loss
of [BanksGarzaVargasKulkarniSrivastava2020].
Proof: from $\|\mathbf{U} - \mathbf{Q}_1\mathbf{C}\|_2 \le \delta$, the singular values of
$\mathbf{C}$ lie in $[(1 - \delta)/(1 + \nu), (1 + \delta)/(1 - \nu)]$, those of
$\mathbf{U}^{\mathsf{H}}\mathbf{Q}_1$ in $[(1 - \delta)(1 - \nu)/(1 + \delta),
(1 + \delta)(1 + \nu)/(1 - \delta)]$, and $\|(\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})
\mathbf{Q}_1\|_2 \le \delta(1 + \nu)/(1 - \delta)$ (`NLAlib.singularValues_last_mul_norm_le`,
`NLAlib.exists_norm_eq_one_and_norm_mulVec_eq_singularValues`). Take $\mathbf{W}$ the polar factor
of $\mathbf{U}^{\mathsf{H}}\mathbf{Q}_1$ (`NLAlib.polarFactor`); then $\|\mathbf{W} -
\mathbf{U}^{\mathsf{H}}\mathbf{Q}_1\|_2 = \max_i \lvert \sigma_i - 1 \rvert \le 4\delta$, and
$\mathbf{U}\mathbf{W} - \mathbf{Q}_1 = \mathbf{U}(\mathbf{W} - \mathbf{U}^{\mathsf{H}}\mathbf{Q}_1)
- (\mathbf{I} - \mathbf{U}\mathbf{U}^{\mathsf{H}})\mathbf{Q}_1$ gives $4\delta + 1.5\delta$.
M, about 70 lines. -/
theorem HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le {U Q' Q₁ : Matrix m r 𝕜}
    (hU : HasOrthonormalCols U) (hQ' : HasOrthonormalCols Q') {C : Matrix r r 𝕜} {ν δ : ℝ}
    (hν : specNorm (Q₁ - Q') ≤ ν) (hδ : specNorm (U - Q₁ * C) ≤ δ) (hνδ : ν ≤ δ)
    (hδ₅ : δ ≤ 1 / 5) :
    ∃ W : Matrix r r 𝕜, HasOrthonormalCols W ∧ specNorm (U * W - Q₁) ≤ 6 * δ := by
  sorry

/-- **Deterministic accuracy of randomized deflation** (Theorem 3.3, deterministic half): under
the machine contract `NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with constants
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$, $c_{\mathrm N}$, let
$r \le n$, $\mathbf{U}, \mathbf{V} \in \mathbb{C}^{n \times r}$ have orthonormal columns,
$\mathbf{S} \in \mathbb{C}^{r \times r}$ be invertible, $\mathbf{A} =
\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$, $\widetilde{\mathbf{A}}$ stored with
$\|\mathbf{A} - \bar{\widetilde{\mathbf{A}}}\|_2 \le \beta$, and $\mathbf{G}$ have
$\mathbf{V}^{\mathsf{H}}\mathbf{G}_1$ invertible, $\mathbf{G}_1$ its first $r$ columns. With
$m = (\|\mathbf{S}\|_2 + \beta + 1)\|\mathbf{S}^{-1}\|_2\|\mathbf{G}\|_2
\|(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}\|_2$, if $m\beta \le 1/5$,
$(4\mu_{\mathrm{QR}}(n) + 4\sqrt n\,c_{\mathrm N} + 2\mu_{\mathrm{MM}}(n))u \le \beta$,
$\tau \le \|\mathbf{S}\|_2\|\mathbf{G}\|_2$, $\sqrt n\,\tau \le \|\mathbf{G}\|_2$ (the floor of the
normal sampler, absorbed into a factor $2$) and $2(\|\mathbf{S}\|_2 + \beta)\|\mathbf{G}\|_2 \le
\Omega$, then there is a unitary $\mathbf{W}$ with
$$\|\mathbf{U}\mathbf{W} - \mathsf{deflate}(\widetilde{\mathbf{A}}, r)\|_2 \le 6m\beta \,,$$
$\mathsf{deflate}$ the decoded output of `NLAlib.deflate` with ideal sample $\mathbf{G}$. [Shah2024,
Theorem 3.3], there for $\mathbf{S}$ the diagonal of singular values and with the probability
folded in.
Proof: [Shah2024, proof of Theorem 3.3], (3.1) there: write $\widetilde{\mathbf{G}} =
\mathbf{G} + \mathbf{E}_{\mathbf{G}}$ with $\|\mathbf{E}_{\mathbf{G}}\|_2 \le \sqrt n\,c_{\mathrm N}
u\|\mathbf{G}\|_2$ (entrywise, `NLAlib.specNorm_le_frobNorm`,
`NLAlib.frobNorm_le_sqrt_card_mul_specNorm`), $\mathbf{M} = \widetilde{\mathbf{A}}
\widetilde{\mathbf{G}} + \mathbf{F}$ (product contract), $\mathbf{M}' = \mathbf{Q}'\mathbf{R}$
and $\mathbf{Q} = \mathbf{Q}' + \mathbf{E}_{\mathbf{Q}}$ (QR contract), $\mathbf{R}$ upper
trapezoidal so its first $r$ columns are $\mathbf{R}_{11}$ on top of $\mathbf{0}$; then
$\mathbf{U} = \mathbf{Q}_1\mathbf{C} + \mathbf{Z}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}
\mathbf{S}^{-1}$ with $\mathbf{C} = \mathbf{R}_{11}(\mathbf{V}^{\mathsf{H}}\mathbf{G}_1)^{-1}
\mathbf{S}^{-1}$ and $\|\mathbf{Z}\|_2 \le [(4\mu_{\mathrm{QR}} + 2\sqrt n c_{\mathrm N} +
2\mu_{\mathrm{MM}})(\|\mathbf{S}\|_2 + \beta)u + \beta]\|\mathbf{G}\|_2$, so
$\|\mathbf{U} - \mathbf{Q}_1\mathbf{C}\|_2 \le m\beta$; conclude with
`NLAlib.HasOrthonormalCols.exists_hasOrthonormalCols_specNorm_mul_sub_le`
($\nu = \mu_{\mathrm{QR}}u \le \beta/4 \le m\beta$; $m \ge 1$ when $r \ge 1$, and $r = 0$ is
trivial). The floor and range conditions make each contract applicable with the upper bounds
used. Split into private lemmas for $\mathbf{E}_{\mathbf{G}}$, the identity for $\mathbf{U}$ and
the bound on $\mathbf{Z}$. L, about 140 lines. -/
theorem FloatMachine.IsAccurate.exists_hasOrthonormalCols_specNorm_mul_sub_deflate_le
    {F : Type*} {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN β mval : ℝ} {μM μQ : ℕ → ℝ}
    (hM : M.IsAccurate dec u τ Ω μM μQ cN) {n r : ℕ} (hr : r ≤ n)
    {U V : Matrix (Fin n) (Fin r) ℂ} (hU : HasOrthonormalCols U) (hV : HasOrthonormalCols V)
    {S : Matrix (Fin r) (Fin r) ℂ} (hS : IsUnit S) {A G : Matrix (Fin n) (Fin n) ℂ}
    {A' : Matrix (Fin n) (Fin n) (F × F)} (hA : A = U * S * Vᴴ)
    (hβ : specNorm (A - decodeMatrix dec A') ≤ β)
    (hG : IsUnit (Vᴴ * G.submatrix id (Fin.castLE hr)))
    (hm : mval = (specNorm S + β + 1) * specNorm S⁻¹ * specNorm G *
      specNorm (Vᴴ * G.submatrix id (Fin.castLE hr))⁻¹)
    (hmβ : mval * β ≤ 1 / 5) (hu : (4 * μQ n + 4 * √(n : ℝ) * cN + 2 * μM n) * u ≤ β)
    (hτ : τ ≤ specNorm S * specNorm G) (hτN : τ * √(n : ℝ) ≤ specNorm G)
    (hΩ : 2 * (specNorm S + β) * specNorm G ≤ Ω) :
    ∃ W : Matrix (Fin r) (Fin r) ℂ, HasOrthonormalCols W ∧
      specNorm (U * W - decodeMatrix dec (deflate M r A' G)) ≤ 6 * mval * β := by
  sorry

end NLAlib
