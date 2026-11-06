/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.PolarFactor
public import NLAlib.Matrix.Factorizations.Householder
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Norms.Frobenius

/-!
# Symmetric backward perturbations from orthonormal bases (scaffold)

Statements for the backward model of Lanczos with full reorthogonalization (stage
LANCZOS-REORTH, design note `docs/design/Krylov-LanczosReorth.md` §3.3, ids E1, E2, E5, F2a), all
in the Matrix layer: the symmetric completion of a residual against an orthonormal basis
[KahanParlettJiang1982], the polar factor of a nearly orthonormal basis, an orthogonal map
sending one unit vector to another and close to the identity (two reflectors), and the count of
orthonormal approximate eigenvectors with small residuals.

## Main results

* `NLAlib.exists_transpose_eq_mul_eq_neg_of_hasOrthonormalCols`: the symmetric completion.
* `NLAlib.hasOrthonormalCols_polarFactor`, `NLAlib.frobNorm_polarFactor_sub_le`.
* `NLAlib.exists_orthogonal_mulVec_eq_specNorm_sub_one_le`: the rotation.
* `NLAlib.card_le_card_eigenvalue_mem_of_hasOrthonormalCols`: the residual-gated count.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- **The symmetric completion of a residual** (E1): for $\mathbf{U}$ with orthonormal columns
and $\mathbf{R}$ with $\mathbf{U}^{\mathsf{T}}\mathbf{R}$ symmetric, the symmetric
$\mathbf{E} = -\mathbf{R}\mathbf{U}^{\mathsf{T}} - \mathbf{U}\mathbf{R}^{\mathsf{T}} +
\mathbf{U}(\mathbf{U}^{\mathsf{T}}\mathbf{R})\mathbf{U}^{\mathsf{T}}$ satisfies
$\mathbf{E}\mathbf{U} = -\mathbf{R}$, $\|\mathbf{E}\|_{\mathsf F} \le
\sqrt2\,\|\mathbf{R}\|_{\mathsf F}$
and $\|\mathbf{E}\|_2 \le 2\|\mathbf{R}\|_2$. [KahanParlettJiang1982] (locator to verify).
Proof: take that $\mathbf{E}$; symmetry from $(\mathbf{U}^{\mathsf{T}}\mathbf{R})^{\mathsf{T}} =
\mathbf{U}^{\mathsf{T}}\mathbf{R}$ (`Matrix.transpose_mul`, `Matrix.transpose_add`), and
$\mathbf{E}\mathbf{U} = -\mathbf{R}$ from $\mathbf{U}^{\mathsf{T}}\mathbf{U} = \mathbf{I}$
(`Matrix.mul_assoc`, `HasOrthonormalCols` unfolds to it over ℝ). For the norms write
$\mathbf{R} = \mathbf{U}\mathbf{S} + \mathbf{R}_\perp$, $\mathbf{R}_\perp = (\mathbf{I} -
\mathbf{U}\mathbf{U}^{\mathsf{T}})\mathbf{R}$, so $\mathbf{E} =
-\mathbf{U}\mathbf{S}\mathbf{U}^{\mathsf{T}}
- \mathbf{R}_\perp\mathbf{U}^{\mathsf{T}} - \mathbf{U}\mathbf{R}_\perp^{\mathsf{T}}$, three mutually
Frobenius-orthogonal terms: $\|\mathbf{E}\|_{\mathsf F}^2 = \|\mathbf{S}\|_{\mathsf F}^2 +
2\|\mathbf{R}_\perp\|_{\mathsf F}^2 \le 2\|\mathbf{R}\|_{\mathsf F}^2$; spectral: $\|\mathbf{E}\|_2
\le
\|\mathbf{U}\mathbf{S}\mathbf{U}^{\mathsf{T}} + \mathbf{R}_\perp\mathbf{U}^{\mathsf{T}}\|_2 +
\|\mathbf{U}\mathbf{R}_\perp^{\mathsf{T}}\|_2 \le 2\|\mathbf{R}\|_2$. S, about 60 lines. -/
theorem exists_transpose_eq_mul_eq_neg_of_hasOrthonormalCols {n k : ℕ}
    {U : Matrix (Fin n) (Fin k) ℝ} (hU : HasOrthonormalCols U) {R : Matrix (Fin n) (Fin k) ℝ}
    (hR : (Uᵀ * R)ᵀ = Uᵀ * R) :
    ∃ E : Matrix (Fin n) (Fin n) ℝ, Eᵀ = E ∧ E * U = -R ∧
      frobNorm E ≤ Real.sqrt 2 * frobNorm R ∧ specNorm E ≤ 2 * specNorm R := by
  sorry

/-- **The polar factor of a nearly orthonormal basis is orthonormal** (E2): if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta < 1$ then
`NLAlib.polarFactor` $\mathbf{V}$ has orthonormal columns. [Higham2008, Theorem 8.1].
Proof: $\mathbf{G} = \mathbf{V}^{\mathsf{T}}\mathbf{V}$ is symmetric positive definite (its
eigenvalues lie in $[1-\eta, 1+\eta]$ by `Matrix.IsHermitian.abs_eigenvalue_sub_le` against
$\mathbf{I}$); with $\mathbf{K} = $ `cfc (√·)⁻¹` $\mathbf{G}$, symmetric and commuting with
$\mathbf{G}$, $\mathbf{K}\mathbf{G}\mathbf{K} = $ `cfc` of $x \mapsto x/x = 1$ on the spectrum
(`cfc_mul`, `cfc_congr`, `cfc_one`). S, about 30 lines. -/
theorem hasOrthonormalCols_polarFactor {n m : ℕ} {V : Matrix (Fin n) (Fin m) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) (hη : η < 1) : HasOrthonormalCols (polarFactor V) := by
  sorry

/-- **The polar factor is close to a nearly orthonormal basis** (E2): if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta < 1$ then
$$\|\operatorname{polar}(\mathbf{V}) - \mathbf{V}\|_{\mathsf F} \le
\frac{\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_{\mathsf F}}{1 + \sqrt{1 - \eta}}.$$
[Higham2008, Theorem 8.4] for the nearest-orthonormal property; the bound itself has no printed
source here.
Proof: with $\mathbf{U} = $ `NLAlib.polarFactor` $\mathbf{V}$ and $\mathbf{G} =
\mathbf{V}^{\mathsf{T}}
\mathbf{V}$, $\mathbf{V} = \mathbf{U}\mathbf{G}^{1/2}$, so $\mathbf{U} - \mathbf{V} =
\mathbf{U}(\mathbf{I} - \mathbf{G}^{1/2})$ and $\|\mathbf{U} - \mathbf{V}\|_{\mathsf F} =
\|\mathbf{I} - \mathbf{G}^{1/2}\|_{\mathsf F}$ (`NLAlib.hasOrthonormalCols_polarFactor`); then
`Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le_of_lipschitzOnWith` with $\sqrt{\cdot}$ Lipschitz with
constant $1/(1 + \sqrt{1-\eta})$ on $[1-\eta, 1+\eta]$ (or the eigenvalue sum directly:
$|1 - \sqrt\lambda| = |1 - \lambda|/(1 + \sqrt\lambda)$). S, about 40 lines. -/
theorem frobNorm_polarFactor_sub_le {n m : ℕ} {V : Matrix (Fin n) (Fin m) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) (hη : η < 1) :
    frobNorm (polarFactor V - V) ≤ frobNorm (Vᵀ * V - 1) / (1 + Real.sqrt (1 - η)) := by
  sorry

/-- **A rotation taking one unit vector to another** (E5): for unit $\mathbf{x}$, $\mathbf{y}$ the
orthogonal $\mathbf{Z} = \mathbf{H}_{\mathbf{x}+\mathbf{y}}\mathbf{H}_{\mathbf{x}}$ (two
reflectors, `NLAlib.householder`; the identity on $\{\mathbf{x}, \mathbf{y}\}^\perp$) satisfies
$\mathbf{Z}\mathbf{x} = \mathbf{y}$ and $\|\mathbf{Z} - \mathbf{I}\|_2 \le \|\mathbf{x} -
\mathbf{y}\|$ (a single reflector has $\|\mathbf{H} - \mathbf{I}\|_2 = 2$). No printed source.
Proof: $\mathbf{H}_{\mathbf{x}}\mathbf{x} = -\mathbf{x}$ (`NLAlib.householder_mulVec_self`, unit
norm) and $\mathbf{H}_{\mathbf{x}+\mathbf{y}}(-\mathbf{x}) = \mathbf{y}$
(`NLAlib.householder_mulVec`: $(\mathbf{x}+\mathbf{y})^{\mathsf{T}}\mathbf{x} = 1 +
\mathbf{x}^{\mathsf{T}}\mathbf{y}$, $\|\mathbf{x}+\mathbf{y}\|^2 = 2(1 + \mathbf{x}^{\mathsf{T}}
\mathbf{y})$; the case $\mathbf{y} = -\mathbf{x}$ by `NLAlib.householder_zero`); orthogonality by
`NLAlib.hasOrthonormalCols_householder` twice. For the norm, $\mathbf{Z} - \mathbf{I}$ vanishes
on $\{\mathbf{x}, \mathbf{y}\}^\perp$ (`NLAlib.householder_mulVec_of_dotProduct_eq_zero`) and is a
rotation by the angle $\theta$ of $\mathbf{x}, \mathbf{y}$ minus the identity on their span, of
norm $2\sin(\theta/2) = \|\mathbf{x} - \mathbf{y}\|$: bound $\|(\mathbf{Z} -
\mathbf{I})\mathbf{v}\|$
for $\mathbf{v} = a\mathbf{x} + b\mathbf{x}^\perp + \mathbf{r}$ by direct computation. M, about 80
lines. -/
theorem exists_orthogonal_mulVec_eq_specNorm_sub_one_le {n : ℕ} {x y : Fin n → ℝ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (hy : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Zᵀ * Z = 1 ∧ Z *ᵥ x = y ∧
      specNorm (Z - 1) ≤ ‖WithLp.toLp 2 (x - y)‖ := by
  sorry

/-- **Orthonormal approximate eigenvectors are counted by the spectrum** (F2a): for symmetric
$\mathbf{M}$, $r$ orthonormal vectors $\mathbf{x}_i$ and values $\theta_i \in [a, b]$ with
residuals $\|\mathbf{M}\mathbf{x}_i - \theta_i\mathbf{x}_i\| < d/\sqrt r$, $d > 0$, the number of
eigenvalues of $\mathbf{M}$ in $(a - d, b + d)$ is at least $r$. The finite-dimensional
core of "converged Ritz values are not duplicated". No printed source; Fable review of
`docs/design/Krylov-LanczosReorth.md`, finding 1.
Proof: let $\mathbf{P}$ be the orthogonal projector onto the eigenvectors with eigenvalues in
$(a - d, b + d)$ (from the spectral decomposition, `Matrix.IsHermitian.eigenvectorBasis`); its
rank is the count $c$. Every other eigenvalue is at distance $\ge d$ from $\theta_i$, so
$\|(\mathbf{I} - \mathbf{P})\mathbf{x}_i\| \le \|\mathbf{M}\mathbf{x}_i - \theta_i\mathbf{x}_i\|/d
< 1/\sqrt r$ (expand in eigencoordinates as in
`Matrix.IsHermitian.exists_abs_eigenvalue_sub_mul_norm_le`). Hence
$\sum_i\|\mathbf{P}\mathbf{x}_i\|^2
> r - 1$, while $\sum_i\|\mathbf{P}\mathbf{x}_i\|^2 = \operatorname{tr}(\mathbf{X}^{\mathsf{T}}
\mathbf{P}\mathbf{X}) \le \operatorname{tr}\mathbf{P} = c$ ($\mathbf{X}\mathbf{X}^{\mathsf{T}}
\preceq \mathbf{I}$). So $c > r - 1$. M, about 90 lines. -/
theorem card_le_card_eigenvalue_mem_of_hasOrthonormalCols {n r : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) {X : Matrix (Fin n) (Fin r) ℝ}
    (hX : HasOrthonormalCols X) {θ : Fin r → ℝ} {a b d : ℝ} (hd : 0 < d)
    (hθ : ∀ i, θ i ∈ Set.Icc a b)
    (hres : ∀ i, ‖WithLp.toLp 2 (M *ᵥ (fun k => X k i) - θ i • fun k => X k i)‖ <
      d / Real.sqrt r) :
    r ≤ ((Finset.range n).filter fun i => eigenvalue M i ∈ Set.Ioo (a - d) (b + d)).card := by
  sorry

end NLAlib
