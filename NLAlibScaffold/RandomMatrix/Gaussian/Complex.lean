/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Gaussian.Complex
public import NLAlib.RandomMatrix.Gaussian.ExtremeSingularValues
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.Matrix.Spectral.LeastSingularValue
public import NLAlib.Matrix.Basic.Projector
public import Mathlib.Probability.Distributions.Gaussian.Multivariate

/-!
# Complex Gaussian matrices: invariance, norm and smallest singular value (scaffold)

Statements for `NLAlib/RandomMatrix/Gaussian/Complex.lean` (stage HDIAG, wave W3, design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` §3.5). A standard complex Gaussian matrix
is the image of a real Gaussian matrix with twice the rows, $(\mathbf{G}_1 +
i\mathbf{G}_2)/\sqrt2$; through it the real results apply: unitary invariance of the
compression $\mathbf{V}^{\mathsf{H}}\mathbf{G}$, the norm tail, and an elementary tail for the
smallest singular value of a square one that replaces Edelman's exact law ([Shah2024, Lemmas 3.1,
3.2]).

## Main results

* `NLAlib.complexGaussian_eq_map_stdGaussian`: the bridge to Mathlib.
* `NLAlib.complexGaussianMatrix_eq_map_gaussianMatrix`: the realification.
* `NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`,
  `NLAlib.hasLaw_submatrix_of_hasLaw_complexGaussianMatrix`.
* `NLAlib.measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix`: Lemma 3.2.
* `NLAlib.measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector`: small ball of a
  projection.
* `NLAlib.measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix`: Lemma 3.1.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n p q : Type*} [Fintype m]
  [Fintype n] [Fintype p] [Fintype q]

/-- **Bridge to Mathlib's standard Gaussian**: the standard complex Gaussian law is the image of
Mathlib's `ProbabilityTheory.stdGaussian` on $\mathbb{C}$ (the real two-dimensional standard
Gaussian, of variance $1$ in each part) under $z \mapsto z/\sqrt2$.
Proof: `ProbabilityTheory.stdGaussian_eq_map_pi_orthonormalBasis` with the basis
`Complex.orthonormalBasisOneI`, then `Measure.map_map` and
`ProbabilityTheory.gaussianReal_map_const_mul` on each coordinate, `Measure.map_prod_map`. S,
about 25 lines. -/
theorem complexGaussian_eq_map_stdGaussian :
    complexGaussian = (stdGaussian ℂ).map fun z => ((√2 : ℝ)⁻¹ : ℂ) * z := by
  sorry

/-- **A complex Gaussian matrix is a real Gaussian matrix in disguise**: the standard complex
Gaussian law on $m \times n$ matrices is the law of $(\mathbf{G}_1 + i\mathbf{G}_2)/\sqrt2$,
where $\begin{bmatrix} \mathbf{G}_1 \\ \mathbf{G}_2 \end{bmatrix}$ is a $2m \times n$ standard
real Gaussian matrix (rows indexed by $m \oplus m$). No printed source.
Proof: both sides are product measures over the entries (`Measure.pi`); for one entry the law of
$(x + iy)/\sqrt2$ with $x, y \sim \mathcal{N}(0, 1)$ independent is `NLAlib.complexGaussian`
(`ProbabilityTheory.gaussianReal_map_const_mul`, `Measure.map_map`, `Measure.map_prod_map`);
reorganise the index $(m \oplus m) \times n$ as $m \times n \times \mathrm{Bool}$
(`MeasureTheory.measurePreserving_piCongrLeft`, `MeasureTheory.Measure.pi_map_pi`-type lemmas).
M, about 70 lines. -/
theorem complexGaussianMatrix_eq_map_gaussianMatrix :
    complexGaussianMatrix m n = (gaussianMatrix (m ⊕ m) n).map fun X =>
      (√2 : ℝ)⁻¹ • ((X.submatrix Sum.inl id).map (fun x : ℝ => (x : ℂ)) +
        Complex.I • (X.submatrix Sum.inr id).map (fun x : ℝ => (x : ℂ))) := by
  sorry

/-- **Unitary invariance of a complex Gaussian matrix**: if $\mathbf{G}$ is a standard complex
Gaussian $n \times k$ matrix and $\mathbf{V} \in \mathbb{C}^{n \times r}$ has orthonormal
columns, then $\mathbf{V}^{\mathsf{H}}\mathbf{G}$ is a standard complex Gaussian $r \times k$
matrix. [Shah2024, proof of Theorem 3.3], "by rotational invariance".
Proof: realify with `NLAlib.complexGaussianMatrix_eq_map_gaussianMatrix`: the real form of
$\mathbf{V}^{\mathsf{H}}$, $\begin{bmatrix} \operatorname{Re}\mathbf{V}^{\mathsf{H}} &
-\operatorname{Im}\mathbf{V}^{\mathsf{H}} \\ \operatorname{Im}\mathbf{V}^{\mathsf{H}} &
\operatorname{Re}\mathbf{V}^{\mathsf{H}} \end{bmatrix}$ (`Matrix.fromBlocks`), has orthonormal
rows and maps the stacked real Gaussian to the stacked real and imaginary parts of
$\sqrt2\,\mathbf{V}^{\mathsf{H}}\mathbf{G}$; `NLAlib.hasLaw_const_mul_of_hasLaw_gaussianMatrix`,
then back through the realification. M, about 60 lines. -/
theorem hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    [DecidableEq r] {G : Ω → Matrix n q ℂ} (hG : HasLaw G (complexGaussianMatrix n q) μ)
    {V : Matrix n r ℂ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => Vᴴ * G ω) (complexGaussianMatrix r q) μ := by
  sorry

/-- A submatrix of a standard complex Gaussian matrix on injective row and column maps is a
standard complex Gaussian matrix.
Proof: as `NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix` (selection matrices with orthonormal
columns, `NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix` on both sides via the
transpose), or directly from the product structure (`MeasureTheory.Measure.pi_map_restrict`-type
marginal lemmas). S, about 25 lines. -/
theorem hasLaw_submatrix_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {f : p → m} (hf : Function.Injective f)
    {e : q → n} (he : Function.Injective e) :
    HasLaw (fun ω => (G ω).submatrix f e) (complexGaussianMatrix p q) μ := by
  sorry

/-- **Norm tail of a complex Gaussian matrix** (Lemma 3.2): for a standard complex Gaussian
$m \times n$ matrix $\mathbf{G}$ and $t \ge 0$,
$$\mathbb{P}\bigl[\sqrt2\,(\sqrt{\lvert m \rvert} + \sqrt{\lvert n \rvert} + t) \le
\|\mathbf{G}\|_2\bigr] \le 2e^{-t^2/2} \,.$$
[Shah2024, Lemma 3.2], citing [BanksKulkarniMukherjeeSrivastava2021, Lemma 2.2]: there
$\mathbb{P}[\|\mathbf{G}\|_2 > (2\sqrt2 + t)\sqrt n] \le 2e^{-nt^2}$ for square $\mathbf{G}$; the
constant in the exponent differs.
Proof: with the realification,
$\|\mathbf{G}\|_2 \le (\|\mathbf{G}_1\|_2 + \|\mathbf{G}_2\|_2)/\sqrt2$
(`NLAlib.specNorm_add_le`, `NLAlib.specNorm_smul`, the norm of the entrywise coercion equals the
real norm); if the left event holds one of the two real norms is at least
$\sqrt{\lvert m \rvert} + \sqrt{\lvert n \rvert} + t$; union bound and
`NLAlib.measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix` for the two blocks
(`NLAlib.hasLaw_submatrix_of_hasLaw_gaussianMatrix` on `Sum.inl`, `Sum.inr`). M, about 45 lines. -/
theorem measureReal_specNorm_ge_le_of_hasLaw_complexGaussianMatrix {G : Ω → Matrix m n ℂ}
    (hG : HasLaw G (complexGaussianMatrix m n) μ) {t : ℝ} (ht : 0 ≤ t) :
    μ.real {ω | √2 * (√(Fintype.card m : ℝ) + √(Fintype.card n : ℝ) + t) ≤ specNorm (G ω)} ≤
      2 * Real.exp (-t ^ 2 / 2) := by
  sorry

/-- **Small ball of a projected complex Gaussian vector**: for a standard complex Gaussian vector
$\mathbf{g}$, a nonzero orthogonal projector $\mathbf{\Pi}$ and $s \ge 0$,
$\mathbb{P}[\|\mathbf{\Pi}\mathbf{g}\| \le s] \le s^2$. A complex Gaussian has two real degrees of
freedom per coordinate: $\lvert z \rvert^2$ is exponential, $\mathbb{P}[\lvert z \rvert \le s] =
1 - e^{-s^2} \le s^2$. No printed source.
Proof: pick a unit $\mathbf{w}$ in the range of $\mathbf{\Pi}$; $\|\mathbf{\Pi}\mathbf{g}\| \ge
\lvert \langle \mathbf{w}, \mathbf{g} \rangle \rvert$; $\langle \mathbf{w}, \mathbf{g} \rangle$ is
a standard complex Gaussian (`NLAlib.hasLaw_conjTranspose_mul_of_hasLaw_complexGaussianMatrix`
with a one-column frame, or the realification and
`NLAlib.hasLaw_dotProduct_of_hasLaw_gaussianVector`); its squared modulus is a sum of two
independent $\mathcal{N}(0, 1/2)$ squares, whose CDF at $s^2$ is $1 - e^{-s^2}$ (polar
coordinates, `integral_comp_polarCoord_symm`, or the $\chi^2_2$ law of
`Probability/Distributions/ChiSquare.lean`); `Real.add_one_le_exp`. M, about 60 lines. -/
theorem measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector {g : Ω → n → ℂ}
    (hg : HasLaw g (complexGaussianVector n) μ) {P : Matrix n n ℂ} (hP : IsStarProjection P)
    (hP₀ : P ≠ 0) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | ‖WithLp.toLp 2 (P *ᵥ g ω)‖ ≤ s} ≤ s ^ 2 := by
  sorry

/-- **Smallest singular value of a square complex Gaussian matrix** (Lemma 3.1): for a standard
complex Gaussian $r \times r$ matrix $\mathbf{G}$, $k + 1 = \lvert r \rvert$ and $x \ge 0$,
$$\mathbb{P}[\sigma_k(\mathbf{G}) \le x] \le \lvert r \rvert^2 x^2 \,.$$
[Shah2024, Lemma 3.1], citing [Edelman1988, Theorem 3.2]: there $(\lvert r \rvert/2)x^2$ (the exact
law of $\sigma_{\min}$); this elementary bound loses a factor $2\lvert r \rvert$, which costs
$O(\log n)$ bits in the precision of the eigensolver.
Proof: by `NLAlib.exists_iInf_norm_mulVec_le_of_singularValues_le`, $\sigma_k \le x$ puts some
column $\mathbf{g}_j$ within $\sqrt{\lvert r \rvert}\,x$ of the span of the others, that is
$\|(\mathbf{I} - \mathbf{P}_j)\mathbf{g}_j\| \le \sqrt{\lvert r \rvert}\,x$ with $\mathbf{P}_j$ the
projector onto the span of the other columns (`NLAlib.rangeProjector`; identify the infimum with
the projection residual, `NLAlib.isStarProjection_rangeProjector`), a nonzero projector since the
others span at most $\lvert r \rvert - 1$ dimensions. Union bound over $j$; for each $j$, condition
on the other columns (independent of $\mathbf{g}_j$, `ProbabilityTheory.iIndepFun` of the columns
from the product law, `ProbabilityTheory.IndepFun.integral_comp_eq_integral_integral` or
`Measure.prod` Fubini) and apply
`NLAlib.measureReal_norm_mulVec_le_le_of_hasLaw_complexGaussianVector`
with $s = \sqrt{\lvert r \rvert}\,x$. Measurability of $\mathbf{P}_j$ in the other columns:
`Probability/Measurability/Matrix.lean`. L, about 120 lines. -/
theorem measureReal_singularValues_le_le_of_hasLaw_complexGaussianMatrix {r : Type*} [Fintype r]
    {G : Ω → Matrix r r ℂ} (hG : HasLaw G (complexGaussianMatrix r r) μ) {k : ℕ}
    (hk : k + 1 = Fintype.card r) {x : ℝ} (hx : 0 ≤ x) :
    μ.real {ω | singularValues (G ω) k ≤ x} ≤ (Fintype.card r : ℝ) ^ 2 * x ^ 2 := by
  sorry

end NLAlib
