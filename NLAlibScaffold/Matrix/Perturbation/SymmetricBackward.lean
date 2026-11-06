/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.Matrix.Factorizations.Householder
public import NLAlib.Matrix.Spectral.Weyl
public import NLAlib.Matrix.Perturbation.Residual
public import NLAlib.Matrix.Norms.Frobenius
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlibScaffold.Matrix.Perturbation.OrthErr

/-!
# Symmetric backward perturbations from orthonormal bases (scaffold)

Statements for the backward model of Lanczos with full reorthogonalization (stage
LANCZOS-REORTH, design note `docs/design/Krylov-LanczosReorth.md` §3.3, ids E1, E2, E5, F2a), all
in the Matrix layer: the symmetric completion of a residual against an orthonormal basis
[KahanParlettJiang1982], main's polar factor (`NLAlib/Matrix/Factorizations/Polar.lean`) of a
nearly orthonormal basis, an orthogonal map
sending one unit vector to another and close to the identity (two reflectors), and the count of
orthonormal approximate eigenvectors with small residuals.

## Main results

* `NLAlib.exists_transpose_eq_mul_eq_neg_of_hasOrthonormalCols`: the symmetric completion.
* `NLAlib.hasOrthonormalCols_polarFactor`, `NLAlib.frobNorm_polarFactor_sub_le`: main's polar factor
  of a nearly orthonormal basis.
* `NLAlib.exists_orthogonal_mulVec_eq_specNorm_sub_one_le`: the rotation.
* `NLAlib.card_le_card_eigenvalue_mem_of_hasOrthonormalCols`: the residual-gated count.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

/-- Frobenius norms add in square when the cross term has zero trace. -/
private lemma frobNorm_add_sq_of_trace_transpose_mul_eq_zero {n k : ℕ}
    {A B : Matrix (Fin n) (Fin k) ℝ} (h : (Aᵀ * B).trace = 0) :
    frobNorm (A + B) ^ 2 = frobNorm A ^ 2 + frobNorm B ^ 2 := by
  have h' : (Bᵀ * A).trace = 0 := by
    rw [← Matrix.trace_transpose, Matrix.transpose_mul, Matrix.transpose_transpose]
    exact h
  simp only [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_eq_transpose_of_trivial,
    Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, Matrix.trace_add, h, h',
    RCLike.re_to_real]
  ring

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
  have hUU : Uᵀ * U = 1 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial]
    exact hU
  have hRU : Rᵀ * U = Uᵀ * R := by
    rw [← hR, Matrix.transpose_mul, Matrix.transpose_transpose]
  have hQU : (1 - U * Uᵀ) * U = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, hUU, Matrix.mul_one, sub_self]
  have hP : IsStarProjection (1 - U * Uᵀ) := by
    have h := isStarProjection_rangeProjector U
    rw [hU.rangeProjector_eq, Matrix.conjTranspose_eq_transpose_of_trivial] at h
    exact h.one_sub
  have hQn : specNorm (1 - U * Uᵀ) ≤ 1 := hP.specNorm_le_one
  have hUn : specNorm Uᵀ ≤ 1 := by
    rw [specNorm_transpose]
    exact hU.specNorm_le_one
  refine ⟨-(R * Uᵀ + U * Rᵀ * (1 - U * Uᵀ)), ?_, ?_, ?_, ?_⟩
  · have hX : U * Rᵀ * (U * Uᵀ) = U * (Uᵀ * R) * Uᵀ := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc Rᵀ, hRU]
      simp only [Matrix.mul_assoc]
    simp only [Matrix.transpose_neg, Matrix.transpose_add, Matrix.transpose_mul,
      Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_transpose]
    congr 1
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_assoc] at hX ⊢
    rw [hX]
    abel
  · rw [Matrix.neg_mul, Matrix.add_mul]
    simp only [Matrix.mul_assoc, hUU, hQU, Matrix.mul_one, Matrix.mul_zero, add_zero]
  · rw [frobNorm_neg]
    have htr : ((R * Uᵀ)ᵀ * (U * Rᵀ * (1 - U * Uᵀ))).trace = 0 := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose,
        show U * Rᵀ * (U * Rᵀ * (1 - U * Uᵀ)) = (U * Rᵀ * (U * Rᵀ)) * (1 - U * Uᵀ) by
          simp only [Matrix.mul_assoc], Matrix.trace_mul_comm]
      simp only [← Matrix.mul_assoc, hQU, Matrix.zero_mul, Matrix.trace_zero]
    have hfA : frobNorm (R * Uᵀ) ≤ frobNorm R :=
      (frobNorm_mul_le_frobNorm_mul_specNorm R Uᵀ).trans
        (mul_le_of_le_one_right (frobNorm_nonneg R) hUn)
    have hfB : frobNorm (U * Rᵀ * (1 - U * Uᵀ)) ≤ frobNorm R := by
      rw [Matrix.mul_assoc, hU.frobNorm_mul_left]
      refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans ?_
      rw [frobNorm_transpose]
      exact mul_le_of_le_one_right (frobNorm_nonneg R) hQn
    have hsq := frobNorm_add_sq_of_trace_transpose_mul_eq_zero htr
    have h1 : frobNorm (R * Uᵀ) ^ 2 ≤ frobNorm R ^ 2 := pow_le_pow_left₀ (frobNorm_nonneg _) hfA 2
    have h2 : frobNorm (U * Rᵀ * (1 - U * Uᵀ)) ^ 2 ≤ frobNorm R ^ 2 :=
      pow_le_pow_left₀ (frobNorm_nonneg _) hfB 2
    have hs2 : (Real.sqrt 2 * frobNorm R) ^ 2 = 2 * frobNorm R ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    have hR0 : 0 ≤ Real.sqrt 2 * frobNorm R := by positivity
    nlinarith [frobNorm_nonneg (R * Uᵀ + U * Rᵀ * (1 - U * Uᵀ))]
  · rw [specNorm_neg]
    have hA : specNorm (R * Uᵀ) ≤ specNorm R :=
      (specNorm_mul_le R Uᵀ).trans (mul_le_of_le_one_right (specNorm_nonneg R) hUn)
    have hB : specNorm (U * Rᵀ * (1 - U * Uᵀ)) ≤ specNorm R := by
      rw [Matrix.mul_assoc, hU.specNorm_mul_left]
      refine (specNorm_mul_le _ _).trans ?_
      rw [specNorm_transpose]
      exact mul_le_of_le_one_right (specNorm_nonneg R) hQn
    linarith [specNorm_add_le (R * Uᵀ) (U * Rᵀ * (1 - U * Uᵀ))]

/-- **The polar factor of a nearly orthonormal basis is orthonormal** (E2): if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta < 1$ then
`NLAlib.polarFactor` $\mathbf{V}$ (main's
$\mathbf{V}((\mathbf{V}^{\mathsf{H}}\mathbf{V})^{1/2})^{+}$, which for full column rank is
$\mathbf{V}(\mathbf{V}^{\mathsf{T}}\mathbf{V})^{-1/2}$) has orthonormal columns. [Higham2008,
Theorem 8.1].
Proof: `NLAlib.hasOrthonormalCols_polarFactor_iff` reduces it to injectivity of
$\mathbf{x} \mapsto \mathbf{V}\mathbf{x}$, which is
`NLAlib.injective_mulVec_of_specNorm_gram_sub_one_lt_one` ($\mathbf{V}^{\mathsf{H}} =
\mathbf{V}^{\mathsf{T}}$ over ℝ, `Matrix.conjTranspose_eq_transpose_of_trivial`). S, about 8 lines.
-/
theorem hasOrthonormalCols_polarFactor {n m : ℕ} {V : Matrix (Fin n) (Fin m) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) (hη : η < 1) : HasOrthonormalCols (polarFactor V) := by
  sorry

/-- **The polar factor is close to a nearly orthonormal basis** (E2): if
$\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta < 1$ then
$$\|\operatorname{polar}(\mathbf{V}) - \mathbf{V}\|_{\mathsf F} \le
\frac{\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_{\mathsf F}}{2\sqrt{1 - \eta}}.$$
[Higham2008, Theorem 8.4] for the nearest-orthonormal property; the bound itself has no printed
source here. (The constant is the Lipschitz constant of $\sqrt{\cdot}$ on $[1-\eta, 1+\eta]$; the
sharper $1/(1 + \sqrt{1-\eta})$ of the design note needs the eigenvalue sum directly and is not
needed downstream.)
Proof: with $\mathbf{U} = $ `NLAlib.polarFactor` $\mathbf{V}$ and $\mathbf{G} =
\mathbf{V}^{\mathsf{T}}\mathbf{V}$, $\mathbf{V} = \mathbf{U}\mathbf{G}^{1/2}$
(`NLAlib.polarFactor_mul_sqrt`, with `CFC.sqrt` $\mathbf{G}$ = `cfc Real.sqrt` $\mathbf{G}$), so
$\mathbf{U} - \mathbf{V} =
\mathbf{U}(\mathbf{I} - \mathbf{G}^{1/2})$ and $\|\mathbf{U} - \mathbf{V}\|_{\mathsf F} =
\|\mathbf{I} - \mathbf{G}^{1/2}\|_{\mathsf F}$ (`NLAlib.hasOrthonormalCols_polarFactor`,
`HasOrthonormalCols.frobNorm_mul_left`). Write $\mathbf{I} = $ `cfc Real.sqrt 1`
(`cfc_algebraMap` with `map_one`) and apply
`Matrix.IsHermitian.frobNorm_cfc_sub_cfc_le_of_lipschitzOnWith` to $\mathbf{G}$ and $\mathbf{I}$
with $s = [1-\eta, 1+\eta]$: both spectra lie in $s$
(`Matrix.IsHermitian.spectrum_eq_image_eigenvalue`, Weyl `Matrix.IsHermitian.abs_eigenvalue_sub_le`
against $\mathbf{I}$), and $\sqrt{\cdot}$ is Lipschitz on $s$ with constant
$1/(2\sqrt{1-\eta})$ since $|\sqrt x - \sqrt y| = |x - y|/(\sqrt x + \sqrt y)$
(`Real.sq_sqrt`, `Real.sqrt_le_sqrt`, `LipschitzOnWith.of_dist_le_mul`). S, about 50 lines. -/
theorem frobNorm_polarFactor_sub_le {n m : ℕ} {V : Matrix (Fin n) (Fin m) ℝ} {η : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η) (hη : η < 1) :
    frobNorm (polarFactor V - V) ≤ frobNorm (Vᵀ * V - 1) / (2 * Real.sqrt (1 - η)) := by
  sorry

/-- **A rotation taking one unit vector to another** (E5): for unit $\mathbf{x}$, $\mathbf{y}$ the
orthogonal $\mathbf{Z} = \mathbf{H}_{\mathbf{x}+\mathbf{y}}\mathbf{H}_{\mathbf{x}}$ (two
reflectors, `NLAlib.householder`; the identity on $\{\mathbf{x}, \mathbf{y}\}^\perp$) satisfies
$\mathbf{Z}\mathbf{x} = \mathbf{y}$, $\|\mathbf{Z} - \mathbf{I}\|_2 \le \|\mathbf{x} -
\mathbf{y}\|$ and $\|\mathbf{Z} - \mathbf{I}\|_{\mathsf F} \le \sqrt2\|\mathbf{x} - \mathbf{y}\|$
(a single reflector has $\|\mathbf{H} - \mathbf{I}\|_2 = 2$). No printed source.
Proof: $\mathbf{H}_{\mathbf{x}}\mathbf{x} = -\mathbf{x}$ (`NLAlib.householder_mulVec_self`, unit
norm) and $\mathbf{H}_{\mathbf{x}+\mathbf{y}}(-\mathbf{x}) = \mathbf{y}$
(`NLAlib.householder_mulVec`: $(\mathbf{x}+\mathbf{y})^{\mathsf{T}}\mathbf{x} = 1 +
\mathbf{x}^{\mathsf{T}}\mathbf{y}$, $\|\mathbf{x}+\mathbf{y}\|^2 = 2(1 + \mathbf{x}^{\mathsf{T}}
\mathbf{y})$; the case $\mathbf{y} = -\mathbf{x}$ by `NLAlib.householder_zero`); orthogonality by
`NLAlib.hasOrthonormalCols_householder` twice. For the spectral norm, $\mathbf{Z} - \mathbf{I}$
vanishes on $\{\mathbf{x}, \mathbf{y}\}^\perp$ (`NLAlib.householder_mulVec_of_dotProduct_eq_zero`)
and is a rotation by the angle $\theta$ of $\mathbf{x}, \mathbf{y}$ minus the identity on their
span, of norm $2\sin(\theta/2) = \|\mathbf{x} - \mathbf{y}\|$: bound $\|(\mathbf{Z} -
\mathbf{I})\mathbf{v}\|$
for $\mathbf{v} = a\mathbf{x} + b\mathbf{x}^\perp + \mathbf{r}$ by direct computation. For the
Frobenius norm use the trace: for orthogonal $\mathbf{Z}$,
$\|\mathbf{Z} - \mathbf{I}\|_{\mathsf F}^2
= \operatorname{tr}((\mathbf{Z}-\mathbf{I})^{\mathsf T}(\mathbf{Z}-\mathbf{I})) = 2n -
2\operatorname{tr}\mathbf{Z}$ (`frobNorm_sq_eq_re_trace`), and with $\mathbf{p} = (\mathbf{x} +
\mathbf{y})/\|\mathbf{x}+\mathbf{y}\|$, $\mathbf{Z} = \mathbf{I} - 2\mathbf{x}\mathbf{x}^{\mathsf T}
- 2\mathbf{p}\mathbf{p}^{\mathsf T} +
4(\mathbf{p}^{\mathsf T}\mathbf{x})\mathbf{p}\mathbf{x}^{\mathsf T}$
has $\operatorname{tr}\mathbf{Z} = n - 4 + 4(\mathbf{p}^{\mathsf T}\mathbf{x})^2 = n - 2 +
2\mathbf{x}^{\mathsf T}\mathbf{y}$, so $\|\mathbf{Z} - \mathbf{I}\|_{\mathsf F}^2 = 4 -
4\mathbf{x}^{\mathsf T}\mathbf{y} = 2\|\mathbf{x} - \mathbf{y}\|^2$ (for $\mathbf{y} = -\mathbf{x}$:
$\mathbf{Z} = \mathbf{H}_{\mathbf{x}}$,
$\|\mathbf{Z} - \mathbf{I}\|_{\mathsf F} = 2 = \|\mathbf{x} -
\mathbf{y}\|$). M, about 110 lines. -/
theorem exists_orthogonal_mulVec_eq_specNorm_sub_one_le {n : ℕ} {x y : Fin n → ℝ}
    (hx : ‖WithLp.toLp 2 x‖ = 1) (hy : ‖WithLp.toLp 2 y‖ = 1) :
    ∃ Z : Matrix (Fin n) (Fin n) ℝ, Zᵀ * Z = 1 ∧ Z *ᵥ x = y ∧
      specNorm (Z - 1) ≤ ‖WithLp.toLp 2 (x - y)‖ ∧
      frobNorm (Z - 1) ≤ Real.sqrt 2 * ‖WithLp.toLp 2 (x - y)‖ := by
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
