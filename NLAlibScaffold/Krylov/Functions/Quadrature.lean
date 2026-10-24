/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Krylov.Functions.Quadrature
public import NLAlibScaffold.Krylov.Processes.LanczosPolynomials
public import NLAlibScaffold.Polynomial.Orthogonal.Gauss

/-!
# Lanczos quadrature and Golub–Welsch: the additions of stage KS7

Statements for `NLAlib/Krylov/Functions/Quadrature.lean` whose proofs are deferred
(`docs/design/Polynomial-OrthogonalStructure.md`, §4.10 and "Interface for SLQ" item 4). For
Hermitian $\mathbf{A}$ and every $q$, the Lanczos rule is the $q$-point Gauss rule of the spectral
measure $\mu_{\mathbf{A},\mathbf{b}}$, with no frame, Ritz-value set or grade hypothesis; below
the grade the Ritz values are the Gauss nodes. For every finite measure $\mu$ with compact
support, the $(k+1)$-point Gauss rule is the spectral measure of the Jacobi matrix
$\mathbf{J}_{k+1}(\mu)$ and $\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$ (Golub–Welsch), over $\mathbb{R}$
and over every `RCLike` field.

The Golub–Welsch statements are placed here, beside the Lanczos form, with a flag (P10): their
vocabulary is Matrix plus Polynomial, so their home by subject is
`NLAlib/Matrix/Spectral/SpectralMeasure.lean`; the proof's use of Lanczos keeps them here.

## Main results

* `Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`: Lanczos quadrature is the Gauss rule.
* `NLAlib.HasOrthonormalCols.nodal_eq_orthogonalPolynomial`,
  `NLAlib.HasOrthonormalCols.gaussNodes_spectralMeasure_eq`: the Ritz values are the Gauss nodes.
* `NLAlib.spectralMeasure_jacobiMatrix`, `NLAlib.spectralMeasure_map_jacobiMatrix`,
  `NLAlib.HasOrthonormalCols.gaussQuadrature_succ_eq_sum`: Golub–Welsch.
-/

@[expose] public section

open MeasureTheory Polynomial
open scoped Matrix ComplexOrder MatrixOrder NNReal

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n r : Type*} [Fintype n] [DecidableEq n] [Fintype r]
  [DecidableEq r]

/-- **Lanczos quadrature is the Gauss rule of the spectral measure**: for Hermitian
$\mathbf{A}$ and every $q$,
$\mathsf{lanczosQuadrature}(\mathbf{A}, \mathbf{b}, q)$ is the $q$-point Gauss rule of
$\mu_{\mathbf{A},\mathbf{b}}$, for every `RCLike` field (complex Hermitian included).
[GolubMeurant2010, Ch. 6].
Proof: S, about 25 lines. `exists_hasOrthonormalCols_range_eq_krylovSpace`;
`HasOrthonormalCols.lanczosQuadrature_eq`; the rule is carried by the Ritz values
(`spectralMeasure_compl_spectrum_eq_zero`), at most $q$ of them (the private
`card_spectrum_le_of_range_eq` of the NLAlib file, which a scaffold proof cannot see);
`(hA.matchesMoments_lanczosQuadrature b q).symm`; an interval containing the finite spectrum and
`ae_mem_Icc_spectralMeasure`; `MatchesMoments.eq_gaussQuadrature`.
Result: lanczos-gauss-quadrature -/
theorem _root_.Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (b : n → 𝕜) (q : ℕ) :
    lanczosQuadrature A b q = gaussQuadrature (spectralMeasure A b) q := by
  sorry

/-- **The Ritz values are the Gauss nodes** (nodal form): for Hermitian $\mathbf{A}$,
$\mathbf{Q}$ with orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, $q$ at
most the grade and $s$ the set of Ritz values, the nodal polynomial of $s$ is the monic
orthogonal polynomial of degree $q$ of $\mu_{\mathbf{A},\mathbf{b}}$. [GolubMeurant2010, Ch. 4]
(locator to check).
Proof: S, about 20 lines. `IsMomentPosDef.eq_orthogonalPolynomial` with
`Matrix.IsHermitian.isMomentPosDef_spectralMeasure_iff` (`hq`), `Lagrange.nodal_monic`,
`Lagrange.natDegree_nodal` and `HasOrthonormalCols.card_spectrum_conjTranspose_mul_mul_eq`
(degree $q$), `HasOrthonormalCols.isOrthogonalPolynomial_nodal`; support from
`ae_mem_Icc_spectralMeasure`. -/
theorem HasOrthonormalCols.nodal_eq_orthogonalPolynomial {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    Lagrange.nodal s id = orthogonalPolynomial (spectralMeasure A b) q := by
  sorry

/-- **The Ritz values are the Gauss nodes**: for Hermitian $\mathbf{A}$, $\mathbf{Q}$ with
orthonormal columns spanning $\mathcal{K}_q(\mathbf{A}, \mathbf{b})$, $q$ at most the grade and
$s$ the set of Ritz values, the Gauss nodes of order $q$ of $\mu_{\mathbf{A},\mathbf{b}}$ are $s$.
The grade hypothesis is needed: past the grade the Gauss nodes can contain a spurious $0$ of
weight $0$. [GolubMeurant2010, Ch. 4] (locator to check).
Proof: S, about 10 lines. Rewrite `HasOrthonormalCols.nodal_eq_orthogonalPolynomial` backwards;
`Lagrange.nodal_eq`, `Polynomial.roots_prod_X_sub_C`, `Finset.val_toFinset`. -/
theorem HasOrthonormalCols.gaussNodes_spectralMeasure_eq {Q : Matrix n r 𝕜}
    (hQ : HasOrthonormalCols Q) {A : Matrix n n 𝕜} (hA : A.IsHermitian) {b : n → 𝕜} {q : ℕ}
    (hK : LinearMap.range Q.mulVecLin = krylovSpace A b q) (hq : q ≤ krylovGrade A b)
    {s : Finset ℝ} (hs : (s : Set ℝ) = spectrum ℝ (Qᴴ * A * Q)) :
    gaussNodes (spectralMeasure A b) q = s := by
  sorry

/-- **Golub–Welsch**: for a finite measure $\mu$ supported in $[a, c]$ and every $k$, the
$(k+1)$-point Gauss rule of $\mu$ is the spectral measure of its Jacobi matrix and
$\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$: its nodes are the eigenvalues of
$\mathbf{J}_{k+1}(\mu)$ and its weights $\mu(\mathbb{R})$ times the squared first components of
the eigenvectors. Past the support size of $\mu$ the matrix has zero rows, and the extra
eigenvalues carry no weight. [Gautschi2004, Theorem 3.1]; [GolubWelsch1969, §2] (labels to
check).
Proof: M, about 45 lines. $\nu$ := the Gauss rule; `spectralMeasure_diagonal_sqrt_of_ae_mem`
realises it as $\mu_{\mathbf{D},\mathbf{w}}$ on the index type `gaussNodes μ (k + 1)` (with
`ae_mem_interpolatoryQuadrature`, `isFiniteMeasure_gaussQuadrature`);
`Matrix.IsHermitian.lanczosQuadrature_succ_eq` for $(\mathbf{D}, \mathbf{w})$,
`Matrix.IsHermitian.lanczosTridiagonal_eq_jacobiMatrix`,
`Matrix.IsHermitian.lanczosQuadrature_eq_gaussQuadrature`; $\nu$ is its own Gauss rule
(`MatchesMoments.eq_gaussQuadrature` with `MatchesMoments.refl`, `ae_mem_Icc_gaussQuadrature`,
`card_gaussNodes_le`); `MatchesMoments.jacobiMatrix_eq` with `matchesMoments_gaussQuadrature`;
$\|\mathbf{w}\|^2 = \nu(\mathbb{R}) = \mu(\mathbb{R})$
(`Matrix.IsHermitian.spectralMeasure_real_univ`, `gaussQuadrature_real_univ`); `Matrix.map_id`.
Result: golub-welsch -/
theorem spectralMeasure_jacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) (k : ℕ) :
    spectralMeasure (jacobiMatrix μ (k + 1)) ((√(μ.real Set.univ) : ℝ) • Pi.single 0 1) =
      gaussQuadrature μ (k + 1) := by
  sorry

/-- **Golub–Welsch, explicit form**: for a finite measure $\mu$ supported in $[a, c]$, every
$k$, and an orthogonal diagonalisation
$\mathbf{J}_{k+1}(\mu) = \mathbf{U}\operatorname{diag}(\mathbf{d})\mathbf{U}^{\mathsf{H}}$ of its
Jacobi matrix,
$$\mathsf{gaussQuadrature}(\mu, k + 1) = \sum_i\mu(\mathbb{R})\,\mathbf{U}_{0,i}^2\,
\delta_{\mathbf{d}_i}\,.$$
[Gautschi2004, Theorem 3.1]; [GolubWelsch1969, §2] (labels to check).
Proof: S, about 15 lines. Rewrite `spectralMeasure_jacobiMatrix`, then
`HasOrthonormalCols.spectralMeasure_eq_sum` (`hr` by `rfl`, the diagonal's casts by `simp`);
$(\mathbf{U}^{\mathsf{H}}\mathbf{e}_0)_i = \mathbf{U}_{0,i}$. -/
theorem HasOrthonormalCols.gaussQuadrature_succ_eq_sum {k : ℕ}
    {U : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ} (hU : HasOrthonormalCols U) {μ : Measure ℝ}
    [IsFiniteMeasure μ] {a c : ℝ} (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) {d : Fin (k + 1) → ℝ}
    (hJ : jacobiMatrix μ (k + 1) = U * Matrix.diagonal d * Uᴴ) :
    gaussQuadrature μ (k + 1) =
      ∑ i, ENNReal.ofReal (μ.real Set.univ * U 0 i ^ 2) • Measure.dirac (d i) := by
  sorry

/-- **Golub–Welsch over any `RCLike` field**: for a finite measure $\mu$ supported in $[a, c]$
and every $k$, the $(k+1)$-point Gauss rule of $\mu$ is the spectral measure of the Jacobi matrix
$\mathbf{J}_{k+1}(\mu)$, with its real entries read in $\Bbbk$, and
$\sqrt{\mu(\mathbb{R})}\,\mathbf{e}_0$. The form for implementation statements over a complex
Hermitian matrix. [Gautschi2004, Theorem 3.1]; [GolubWelsch1969, §2] (labels to check).
Proof: M, about 35 lines. Diagonalise the real $\mathbf{J}$ (`Matrix.IsHermitian.eigenvectorUnitary`
over ℝ, with `isHermitian_jacobiMatrix`), map the factorisation to $\Bbbk$ (`Matrix.map_mul`,
`RCLike.ofReal` casts), `HasOrthonormalCols.spectralMeasure_eq_sum` on both sides; the two Dirac
sums agree termwise ($\lVert(r : \Bbbk)\rVert = \lvert r\rvert$); then
`spectralMeasure_jacobiMatrix`. -/
theorem spectralMeasure_map_jacobiMatrix (μ : Measure ℝ) [IsFiniteMeasure μ] {a c : ℝ}
    (hμ : ∀ᵐ x ∂μ, x ∈ Set.Icc a c) (k : ℕ) :
    spectralMeasure ((jacobiMatrix μ (k + 1)).map (algebraMap ℝ 𝕜))
        ((√(μ.real Set.univ) : 𝕜) • Pi.single 0 1) = gaussQuadrature μ (k + 1) := by
  sorry

end NLAlib
