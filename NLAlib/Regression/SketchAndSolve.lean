/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.RandomMatrix.Gaussian.BlockMoments
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.RandomMatrix.Gaussian.Rank
public import NLAlib.RandomMatrix.Haar.Blocks

/-!
# Sketched least squares with Gaussian and Haar sketches

For a standard Gaussian $p \times m$ sketch $\mathbf{S}$, a fixed basis $\mathbf{X}$ of rank $q$
with $q + 2 \le p$ and every $\mathbf{B}$, the oblique projection
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ (`NLAlib.obliqueProjector`) inflates the error of the
orthogonal projection by exactly the factor $1 + q/(p - q - 1)$, in expectation:
$$\mathbb{E}\|(\mathbf{I}-\mathbf{\Pi}_{\mathbf{X},\mathbf{S}})\mathbf{B}\|_{\mathsf{F}}^2 =
\Bigl(1 + \frac{q}{p-q-1}\Bigr)
\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2\,.$$
At $\mathbf{X} = \mathbf{A}$ this is Epperly and Webber's exact mean squared residual of Gaussian
sketch-and-solve, and the solution
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$ is unbiased. The excess
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$ has a second
spectral moment of order $1/p$ times the Frobenius residual: the core noise of generalized
Nyström.

The proofs take an orthonormal basis $\mathbf{Q}_1$ of $\operatorname{range}\mathbf{X}$ and one,
$\mathbf{Q}_2$, of the range of the residual $(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$; on
the almost sure event $\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$
the excess is $\mathbf{Q}_1(\mathbf{S}\mathbf{Q}_1)^{+}(\mathbf{S}\mathbf{Q}_2)
\mathbf{Q}_2^{\mathsf{H}}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$, a Gaussian block whose
moments are in `NLAlib.RandomMatrix.Gaussian.BlockMoments`. Unbiasedness is a symmetry: the
reflection $2\mathbf{P}_{\mathbf{A}} - \mathbf{I}$ preserves the Gaussian law, fixes $\mathbf{A}$
and negates the residual. The sketch is on the left, $\mathbf{S} : p \times m$, as in the other
Gaussian sketching files; a co-range test matrix $\mathbf{\Psi}$ is the sketch
$\mathbf{\Psi}^{\mathsf{H}}$ (`NLAlib.hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`). Scaling the
sketch changes nothing (`NLAlib.obliqueProjector_smul_right`).

For an $m \times p$ Haar frame $\mathbf{Q}$ with $p \le m$ and the sketch $\mathbf{Q}^{\mathsf{H}}$
the factor is <!-- value haarProjectionFactor m p q -->
$1 + (m - p)/(m - q) \cdot (q/(p - q - 1))$ (`NLAlib.haarProjectionFactor m p q`), at most the
Gaussian one: orthogonality helps, but only a bit. Every Haar statement carries $p \le m$: a wider
Haar frame has orthonormal rows, the sketch is an isometry and the factor would be $1$. Real
throughout.

## Main results

* `NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix`: the
  Gaussian completion identity.
* `NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix`: the exact mean
  squared residual of Gaussian sketch-and-solve.
* `NLAlib.integral_sketchAndSolve_of_hasLaw_gaussianMatrix`: unbiasedness.
* the spectral norm of the excess,
  `integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix`
  and its numerical form for $4q \le p$ (the same name with `_le_div_card` in place of `_le`).
* the first spectral moment of the excess through a left factor $\mathbf{F}$, in namespace `NLAlib`:
`integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix`
* `NLAlib.haarProjectionFactor_le_gaussianProjectionFactor`.
* Haar sketches: the completion identity
  `NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame`, the exact mean
  squared residual `NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`, and
  unbiasedness, `NLAlib.integral_sketchAndSolve_of_hasLaw_haarFrame`.
* `NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`,
  `NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame`:
  expected relative squared residual, with rank-zero-safe $O((r+1)/\varepsilon)$ forms
  `NLAlib.exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_gaussianMatrix`
  and `NLAlib.exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_haarFrame`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n p r s a : Type*} [Fintype m]
  [Fintype n] [Fintype p] [Fintype r] [Fintype s] [Fintype a] [DecidableEq m]
  {S : Ω → Matrix p m ℝ}

/-! ### The basis step -/

omit [DecidableEq m] in
/-- The rank event holds almost surely for a Gaussian sketch:
$\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$ when
$\operatorname{rank}\mathbf{X} \le p$. -/
private theorem ae_rank_mul_eq (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank ≤ Fintype.card p) : ∀ᵐ ω ∂μ, (S ω * X).rank = X.rank := by
  filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix X
    (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS) hX] with ω hω
  rwa [Matrix.conjTranspose_conjTranspose] at hω

/-! ### The completion identity -/

/-- The completion split, almost surely: the error of the oblique projection is the orthogonal
residual plus the Gaussian block in the two bases. -/
private theorem ae_frobNorm_one_sub_obliqueProjector_mul_sq_eq
    (hS : HasLaw S (gaussianMatrix p m) μ) {X : Matrix m s ℝ} (hX : X.rank ≤ Fintype.card p)
    {B : Matrix m r ℝ} {t : ℕ}
    {Q₁ : Matrix m (Fin X.rank) ℝ} {Q₂ : Matrix m (Fin t) ℝ} (hQ₁ : HasOrthonormalCols Q₁)
    (hR₁ : LinearMap.range Q₁.mulVecLin = LinearMap.range X.mulVecLin)
    (hE : Q₂ * (Q₂ᴴ * ((1 - rangeProjector X) * B)) = (1 - rangeProjector X) * B) :
    ∀ᵐ ω ∂μ, frobNorm ((1 - obliqueProjector X (S ω)) * B) ^ 2 =
      frobNorm ((1 - rangeProjector X) * B) ^ 2 +
        frobNorm (pinv (S ω * Q₁) * (S ω * Q₂) * (Q₂ᴴ * ((1 - rangeProjector X) * B))) ^ 2 := by
  filter_upwards [ae_rank_mul_eq hS X hX] with ω hω
  rw [frobNorm_one_sub_obliqueProjector_mul_sq hω,
    obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hω, hQ₁.frobNorm_mul_left]

/-- The squared error of the Gaussian oblique projection is integrable for
$\operatorname{rank}\mathbf{X} + 2 \le p$. -/
theorem integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm ((1 - obliqueProjector X (S ω)) * B) ^ 2) μ := by
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrk : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hint := integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix hG hQ₁ hQ₂ h₁₂ hrk
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  simp only [Matrix.conjTranspose_conjTranspose] at hint
  exact ((integrable_const _).add hint).congr
    ((ae_frobNorm_one_sub_obliqueProjector_mul_sq_eq hS (by omega) hQ₁ hR₁ hE).mono
      fun _ h => h.symm)

/-- **The Gaussian completion identity**: for a standard Gaussian $p \times m$ sketch
$\mathbf{S}$, every fixed $\mathbf{X}$ with $\operatorname{rank}\mathbf{X} + 2 \le p$ and every
$\mathbf{B}$, writing
$q = \operatorname{rank}\mathbf{X}$, <!-- value gaussianProjectionFactor q p -->
$$\mathbb{E}\|(\mathbf{I}-\mathbf{\Pi}_{\mathbf{X},\mathbf{S}})\mathbf{B}\|_{\mathsf{F}}^2 =
\Bigl(1 + \frac{q}{p - q - 1}\Bigr)\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2
\,:$$
the oblique projection inflates the orthogonal projection's error by exactly the factor
`gaussianProjectionFactor q p`. No full rank of $\mathbf{X}$ is assumed.
[EpperlyWebber2026, Theorem 2.1 and Lemma 5.1]; [TroppYurtseverUdellCevher2017, Lemma A.5];
there for $\mathbf{X} = \mathbf{A}$ (EW) or an orthonormal $\mathbf{Q}$ (TYUC), here any basis of
any rank.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm ((1 - obliqueProjector X (S ω)) * B) ^ 2 ∂μ =
      gaussianProjectionFactor X.rank (Fintype.card p) *
        frobNorm ((1 - rangeProjector X) * B) ^ 2 := by
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrk : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hint := integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix hG hQ₁ hQ₂ h₁₂ hrk
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  have hval := integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix hG hQ₁ hQ₂ h₁₂ hrk
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  simp only [Matrix.conjTranspose_conjTranspose] at hint hval
  have hQE : frobNorm (Q₂ᴴ * ((1 - rangeProjector X) * B)) =
      frobNorm ((1 - rangeProjector X) * B) := by
    rw [← hQ₂.frobNorm_mul_left, hE]
  rw [integral_congr_ae (ae_frobNorm_one_sub_obliqueProjector_mul_sq_eq hS (by omega) hQ₁ hR₁ hE),
    integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul, hval,
    Fintype.card_fin, gaussianProjectionFactor_def, hQE]
  ring

/-- **Exact mean squared residual of Gaussian sketch-and-solve**: for a standard Gaussian
$p \times m$ sketch $\mathbf{S}$ and $r = \operatorname{rank}\mathbf{A}$ with
$r + 2 \le p$, <!-- value gaussianProjectionFactor r p -->
$$\mathbb{E}\|\mathbf{B} - \mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})
\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{r}{p - r - 1}\Bigr)\min_{\mathbf{Y}}
\|\mathbf{B}-\mathbf{A}\mathbf{Y}\|_{\mathsf{F}}^2\,,$$
the minimum being $\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2$. Its
integrand is that of
`NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix` at
$\mathbf{X} = \mathbf{A}$ (`NLAlib.mul_sketchAndSolve`), whose integrability companion applies.
[EpperlyWebber2026, Theorem 2.1 (Gaussian)]; real case, $\alpha_{\mathbb{R}} = 1$; first proved by
Bartan and Pilanci, as EW report.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) {A : Matrix m n ℝ}
    (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 ∂μ =
      gaussianProjectionFactor A.rank (Fintype.card p) *
        frobNorm ((1 - rangeProjector A) * B) ^ 2 := by
  simp only [mul_sketchAndSolve]
  rw [← integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix hS A hA B]
  simp only [Matrix.sub_mul, Matrix.one_mul]

/-! ### The spectral norm of the excess -/

/-- The excess in spectral norm, almost surely: the spectral norm of the Gaussian block in the
two bases. -/
private theorem ae_specNorm_obliqueProjector_mul_eq (hS : HasLaw S (gaussianMatrix p m) μ)
    {X : Matrix m s ℝ} (hX : X.rank ≤ Fintype.card p) {B : Matrix m r ℝ} {t : ℕ}
    {Q₁ : Matrix m (Fin X.rank) ℝ} {Q₂ : Matrix m (Fin t) ℝ} (hQ₁ : HasOrthonormalCols Q₁)
    (hR₁ : LinearMap.range Q₁.mulVecLin = LinearMap.range X.mulVecLin)
    (hE : Q₂ * (Q₂ᴴ * ((1 - rangeProjector X) * B)) = (1 - rangeProjector X) * B) :
    ∀ᵐ ω ∂μ, specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2 =
      specNorm (pinv (S ω * Q₁) * (S ω * Q₂) * (Q₂ᴴ * ((1 - rangeProjector X) * B))) ^ 2 := by
  filter_upwards [ae_rank_mul_eq hS X hX] with ω hω
  rw [obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hω, hQ₁.specNorm_mul_left]

/-- The squared spectral norm of the Gaussian sketch-and-solve excess is integrable for
$\operatorname{rank}\mathbf{X} + 2 \le p$. -/
theorem
    integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable
      (fun ω => specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2) μ := by
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrk : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hint := integrable_specNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix hG hQ₁ hQ₂ h₁₂ hrk
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  simp only [Matrix.conjTranspose_conjTranspose] at hint
  exact hint.congr ((ae_specNorm_obliqueProjector_mul_eq hS (by omega) hQ₁ hR₁ hE).mono
    fun _ h => h.symm)

/-- **The spectral norm of the Gaussian sketch-and-solve excess**: with
$\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$, $q = \operatorname{rank}\mathbf{X}$
and $q + 2 \le p$, <!-- value gaussianPinvSpecNormBound q p -->
$$\mathbb{E}\|\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E}\|_2^2 \le
\Bigl(\|\mathbf{E}\|_2\sqrt{\tfrac{q}{p-q-1}} + \|\mathbf{E}\|_{\mathsf{F}}\,
\frac{e}{p - q}\sqrt{(p + q - 1)/2}\Bigr)^2 +
\|\mathbf{E}\|_2^2\Bigl(\frac{e}{p - q}\sqrt{(p + q - 1)/2}\Bigr)^2\,,$$
the constant being `gaussianPinvSpecNormBound q p`. For $4q \le p$ this is at most
$(25/p)\|\mathbf{E}\|_{\mathsf{F}}^2 + (4q/p)\|\mathbf{E}\|_2^2$ (the theorem of
the same name with `_le_div_card` in place of `_le`): the excess is spectrally flat. It is the
core noise of generalized Nyström in projector form.
Proved without a literature source; inputs [TroppWebber2023, Lemmas B.1, B.3] (in the forms of
this library); the algebra is [EpperlyWebber2026, Lemma 5.1] and
[TroppYurtseverUdellCevher2017, Lemma A.4]. -/
theorem
    integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2 ∂μ ≤
      (specNorm ((1 - rangeProjector X) * B) *
            √((X.rank : ℝ) / ((Fintype.card p : ℝ) - X.rank - 1)) +
          frobNorm ((1 - rangeProjector X) * B) *
            gaussianPinvSpecNormBound X.rank (Fintype.card p)) ^ 2 +
        (specNorm ((1 - rangeProjector X) * B) *
          gaussianPinvSpecNormBound X.rank (Fintype.card p)) ^ 2 := by
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrk : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hval := integral_specNorm_pinv_mul_mul_sq_le_of_hasLaw_gaussianMatrix hG hQ₁ hQ₂ h₁₂ hrk
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  simp only [Matrix.conjTranspose_conjTranspose, Fintype.card_fin] at hval
  have hQE : frobNorm (Q₂ᴴ * ((1 - rangeProjector X) * B)) =
      frobNorm ((1 - rangeProjector X) * B) := by
    rw [← hQ₂.frobNorm_mul_left, hE]
  have hQE' : specNorm (Q₂ᴴ * ((1 - rangeProjector X) * B)) =
      specNorm ((1 - rangeProjector X) * B) := by
    rw [← hQ₂.specNorm_mul_left, hE]
  rw [integral_congr_ae (ae_specNorm_obliqueProjector_mul_eq hS (by omega) hQ₁ hR₁ hE)]
  rwa [hQE, hQE'] at hval

/-- The numerical constant of the Gaussian excess: for $4q \le p$ and
$q \ge 1$, <!-- value gaussianPinvSpecNormBound q p -->
$3\bigl(e\sqrt{(p + q - 1)/2}/(p - q)\bigr)^2 \le 25/p$, the left side being three times the square
of `gaussianPinvSpecNormBound q p`. -/
private theorem three_mul_gaussianPinvSpecNormBound_sq_le {q p : ℕ} (hq : 1 ≤ q)
    (hqp : 4 * q ≤ p) :
    3 * gaussianPinvSpecNormBound q p ^ 2 ≤ 25 / (p : ℝ) := by
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hqp' : 4 * (q : ℝ) ≤ p := by exact_mod_cast hqp
  have hp : (0 : ℝ) < p := by linarith
  have hpq : (0 : ℝ) < p - q := by linarith
  have he := Real.exp_one_lt_d9
  have he0 := Real.exp_pos 1
  have h1 : ((p : ℝ) + q - 1) * p ≤ 5 / 4 * (p : ℝ) ^ 2 := by nlinarith
  have h2 : 9 / 16 * (p : ℝ) ^ 2 ≤ ((p : ℝ) - q) ^ 2 := by nlinarith
  have h3 : Real.exp 1 ^ 2 ≤ 7.5 := by nlinarith
  have h4 := mul_le_mul h3 h1 (by nlinarith) (by norm_num)
  have key : 3 * Real.exp 1 ^ 2 * (((p : ℝ) + q - 1) / 2) * p ≤ 25 * ((p : ℝ) - q) ^ 2 := by
    nlinarith
  rw [gaussianPinvSpecNormBound_def, mul_pow, div_pow, Real.sq_sqrt (by linarith),
    show 3 * (Real.exp 1 ^ 2 / ((p : ℝ) - q) ^ 2 * (((p : ℝ) + q - 1) / 2)) =
      3 * Real.exp 1 ^ 2 * (((p : ℝ) + q - 1) / 2) / ((p : ℝ) - q) ^ 2 by ring,
    div_le_div_iff₀ (by positivity) hp]
  exact key

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- The Gaussian sketch-and-solve excess is spectrally flat: with
$\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$, $q = \operatorname{rank}\mathbf{X}$
and $4q \le p$,
$$\mathbb{E}\|\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E}\|_2^2 \le
\frac{25}{p}\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{4q}{p}\|\mathbf{E}\|_2^2\,:$$
the core noise of generalized Nyström is $O(1/p)$ times the Frobenius residual. An explicit
comparison of the bound of
`integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix`,
so an improvement of its constant leaves it true. Proved without a literature source. -/
theorem
    integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_div_card_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : 4 * X.rank ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2 ∂μ ≤
      25 / (Fintype.card p : ℝ) * frobNorm ((1 - rangeProjector X) * B) ^ 2 +
        4 * (X.rank : ℝ) / Fintype.card p * specNorm ((1 - rangeProjector X) * B) ^ 2 := by
  rcases Nat.eq_zero_or_pos X.rank with h0 | hq
  · have hX0 : X = 0 := Matrix.rank_eq_zero.mp h0
    subst hX0
    simp only [obliqueProjector, Matrix.zero_mul, specNorm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, integral_zero]
    positivity
  · refine
      (integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix
        hS X (by omega) B).trans ?_
    set a := specNorm ((1 - rangeProjector X) * B)
    set b := frobNorm ((1 - rangeProjector X) * B)
    set β := gaussianPinvSpecNormBound X.rank (Fintype.card p)
    set h := (X.rank : ℝ) / ((Fintype.card p : ℝ) - X.rank - 1)
    have ha : 0 ≤ a := specNorm_nonneg _
    have hab : a ≤ b := specNorm_le_frobNorm _
    have hq' : (1 : ℝ) ≤ X.rank := by exact_mod_cast hq
    have hqp : 4 * (X.rank : ℝ) ≤ Fintype.card p := by exact_mod_cast hX
    have hp : (0 : ℝ) < Fintype.card p := by linarith
    have hh0 : 0 ≤ h := div_nonneg (Nat.cast_nonneg _) (by linarith)
    have hden : 0 < (Fintype.card p : ℝ) - X.rank - 1 := by linarith
    have hh : 2 * h ≤ 4 * (X.rank : ℝ) / Fintype.card p := by
      rw [show 2 * h = 2 * (X.rank : ℝ) / ((Fintype.card p : ℝ) - X.rank - 1) by
        simp only [h]; ring, div_le_div_iff₀ hden hp]
      nlinarith
    have hβ := three_mul_gaussianPinvSpecNormBound_sq_le hq hX
    have hs : √h ^ 2 = h := Real.sq_sqrt hh0
    have hcross : 2 * (a * √h) * (b * β) ≤ (a * √h) ^ 2 + (b * β) ^ 2 := by
      nlinarith [sq_nonneg (a * √h - b * β)]
    have hab2 : a ^ 2 * β ^ 2 ≤ b ^ 2 * β ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) (sq_nonneg _)
    have e1 : (a * √h + b * β) ^ 2 + (a * β) ^ 2 ≤ 2 * h * a ^ 2 + 3 * β ^ 2 * b ^ 2 := by
      nlinarith
    refine e1.trans ?_
    have e2 : 2 * h * a ^ 2 ≤ 4 * (X.rank : ℝ) / Fintype.card p * a ^ 2 :=
      mul_le_mul_of_nonneg_right hh (sq_nonneg _)
    have e3 : 3 * β ^ 2 * b ^ 2 ≤ 25 / (Fintype.card p : ℝ) * b ^ 2 :=
      mul_le_mul_of_nonneg_right hβ (sq_nonneg _)
    linarith

-- The declaration name alone exceeds 100 characters.
set_option linter.style.longLine false in
/-- The Gaussian sketch-and-solve excess through a left factor: for a standard Gaussian
sketch $\mathbf{S} \in \mathbb{R}^{p \times m}$, $\mathbf{X} \in \mathbb{R}^{m \times s}$ with
$\operatorname{rank}\mathbf{X} + 2 \le p$, any $\mathbf{B} \in \mathbb{R}^{m \times r}$ and
$\mathbf{F} \in \mathbb{R}^{a \times m}$, with $\mathbf{E} = (\mathbf{I} -
\mathbf{P}_{\mathbf{X}})\mathbf{B}$, $q = \operatorname{rank}\mathbf{X}$ and the constant
`gaussianPinvSpecNormBound` written out, <!-- value gaussianPinvSpecNormBound q p -->
$$\mathbb{E}\|\mathbf{F}\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E}\|_2 \le
\frac{e}{p - q}\sqrt{(p + q - 1)/2}\,\bigl(\|\mathbf{E}\|_2\|\mathbf{F}\|_{\mathsf{F}} +
\|\mathbf{E}\|_{\mathsf{F}}\|\mathbf{F}\|_2\bigr)\,.$$
No printed source. -/
theorem
    integral_specNorm_mul_obliqueProjector_mul_one_sub_rangeProjector_mul_le_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) (F : Matrix a m ℝ) :
    ∫ ω, specNorm (F * (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B))) ∂μ ≤
      gaussianPinvSpecNormBound X.rank (Fintype.card p) *
        (specNorm ((1 - rangeProjector X) * B) * frobNorm F +
          frobNorm ((1 - rangeProjector X) * B) * specNorm F) := by
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrk : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hint := integral_specNorm_mul_mul_pinv_mul_le_of_hasLaw_gaussianMatrix hG hQ₁ hQ₂ h₁₂ hrk
    (((1 - rangeProjector X) * B)ᴴ * Q₂) (Q₁ᴴ * Fᴴ)
  simp only [Fintype.card_fin] at hint
  have hpt : ∀ᵐ ω ∂μ, specNorm (F * (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B))) =
      specNorm (((1 - rangeProjector X) * B)ᴴ * Q₂ * (Q₂ᴴ * (S ω)ᴴ) *
        pinv (Q₁ᴴ * (S ω)ᴴ) * (Q₁ᴴ * Fᴴ)) := by
    have hrank : ∀ᵐ ω ∂μ, (S ω * X).rank = X.rank := by
      filter_upwards [ae_rank_conjTranspose_mul_eq_of_hasLaw_gaussianMatrix X
        (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS) (by omega)] with ω hω
      rwa [Matrix.conjTranspose_conjTranspose] at hω
    filter_upwards [hrank] with ω hω
    rw [obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hω, ← specNorm_conjTranspose]
    congr 1
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
      ← pinv_conjTranspose, Matrix.mul_assoc]
  have hC : (Q₂ᴴ * ((1 - rangeProjector X) * B))ᴴ = ((1 - rangeProjector X) * B)ᴴ * Q₂ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hS1 : specNorm (((1 - rangeProjector X) * B)ᴴ * Q₂) =
      specNorm ((1 - rangeProjector X) * B) := by
    rw [← hC, specNorm_conjTranspose, ← hQ₂.specNorm_mul_left, hE]
  have hS2 : frobNorm (((1 - rangeProjector X) * B)ᴴ * Q₂) =
      frobNorm ((1 - rangeProjector X) * B) := by
    rw [← hC, frobNorm_conjTranspose, ← hQ₂.frobNorm_mul_left, hE]
  have hT1 : specNorm (Q₁ᴴ * Fᴴ) ≤ specNorm F := by
    refine (specNorm_mul_le _ _).trans ?_
    rw [specNorm_conjTranspose, specNorm_conjTranspose]
    exact mul_le_of_le_one_left (specNorm_nonneg _) hQ₁.specNorm_le_one
  have hT2 : frobNorm (Q₁ᴴ * Fᴴ) ≤ frobNorm F := by
    refine (frobNorm_mul_le_specNorm_mul_frobNorm _ _).trans ?_
    rw [specNorm_conjTranspose, frobNorm_conjTranspose]
    exact mul_le_of_le_one_left (frobNorm_nonneg _) hQ₁.specNorm_le_one
  rw [integral_congr_ae hpt]
  refine hint.trans ?_
  rw [hS1, hS2]
  exact mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left hT2 (specNorm_nonneg _))
      (mul_le_mul_of_nonneg_left hT1 (frobNorm_nonneg _)))
    (gaussianPinvSpecNormBound_nonneg (by omega))

/-! ### Unbiasedness -/

omit [Fintype r] [DecidableEq m] in
/-- The sketch-and-solve solution for the residual lies in the row space of $\mathbf{A}$, so it is
$\mathbf{A}^{+}$ times its fitted values. -/
private theorem pinv_mul_mul_sketchAndSolve (A : Matrix m n ℝ) (S₀ : Matrix p m ℝ)
    (E : Matrix m r ℝ) : pinv A * (A * sketchAndSolve A S₀ E) = sketchAndSolve A S₀ E := by
  have h : rangeProjector Aᴴ * pinv (S₀ * A) = pinv (S₀ * A) := by
    refine rangeProjector_mul_eq_self_iff.mpr ?_
    rw [range_pinv]
    exact range_le_iff_exists_mul.mpr ⟨S₀ᴴ, Matrix.conjTranspose_mul _ _⟩
  rw [← Matrix.mul_assoc, pinv_mul, sketchAndSolve, ← Matrix.mul_assoc, h]

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- The Gaussian sketch-and-solve solution
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$ is integrable for
$\operatorname{rank}\mathbf{A} + 1 \le p$. -/
theorem integrable_sketchAndSolve_of_hasLaw_gaussianMatrix [DecidableEq r]
    (hS : HasLaw S (gaussianMatrix p m) μ) {A : Matrix m n ℝ}
    (hA : A.rank + 1 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => sketchAndSolve A (S ω) B) μ := by
  classical
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl A B
  set E := (1 - rangeProjector A) * B
  have hm : Measurable fun S₀ : Matrix p m ℝ => sketchAndSolve A S₀ B :=
    (measurable_pinv.comp (measurable_id.matrix_mul measurable_const)).matrix_mul
      (measurable_id.matrix_mul measurable_const)
  have hY₁ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hQ₁
  have hY₂ := hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hQ₂
  have hU : Integrable (fun ω => specNorm (pinv (Q₁ᴴ * (S ω)ᴴ))) μ := by
    have := integrable_specNorm_pinv_rpow_of_hasLaw_gaussianMatrix hY₁ one_pos (q := 1)
      (by rw [Fintype.card_fin]; have : (A.rank : ℝ) + 1 ≤ Fintype.card p := by exact_mod_cast hA
          linarith)
    simpa only [Real.rpow_one] using this
  have hW : Integrable (fun ω => frobNorm (Q₂ᴴ * (S ω)ᴴ)) μ := by
    have := integrable_frobNorm_mul_mul_of_hasLaw_gaussianMatrix hY₂
      (1 : Matrix (Fin (Fintype.card m - A.rank)) (Fin (Fintype.card m - A.rank)) ℝ)
      (1 : Matrix p p ℝ)
    simpa only [Matrix.one_mul, Matrix.mul_one] using this
  have hind : IndepFun (fun ω => specNorm (pinv (Q₁ᴴ * (S ω)ᴴ)))
      (fun ω => frobNorm (Q₂ᴴ * (S ω)ᴴ)) μ :=
    (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hG hQ₁ hQ₂ h₁₂).comp
      (continuous_specNorm.measurable.comp measurable_pinv) continuous_frobNorm.measurable
  have hUW := hind.integrable_mul hU hW
  refine Integrable.mono' ((integrable_const (specNorm (pinv A * B))).add
    ((hUW.mul_const (specNorm (Q₂ᴴ * E))).const_mul (specNorm (pinv A))))
    (hm.comp_aemeasurable hS.aemeasurable).aestronglyMeasurable ?_
  filter_upwards [ae_rank_mul_eq hS A (by omega)] with ω hω
  rw [← specNorm_eq_norm, sketchAndSolve_eq_pinv_mul_add hω B]
  refine (specNorm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [← pinv_mul_mul_sketchAndSolve A (S ω) E, mul_sketchAndSolve,
    obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hω]
  refine (specNorm_mul_le _ _).trans ?_
  rw [hQ₁.specNorm_mul_left]
  simp only [Pi.mul_apply]
  refine mul_le_mul_of_nonneg_left ?_ (specNorm_nonneg _)
  have h1 : specNorm (pinv (S ω * Q₁)) = specNorm (pinv (Q₁ᴴ * (S ω)ᴴ)) := by
    rw [← specNorm_conjTranspose, ← pinv_conjTranspose, Matrix.conjTranspose_mul]
  have h2 : specNorm (S ω * Q₂) ≤ frobNorm (Q₂ᴴ * (S ω)ᴴ) := by
    rw [← specNorm_conjTranspose, Matrix.conjTranspose_mul]
    exact specNorm_le_frobNorm _
  calc specNorm (pinv (S ω * Q₁) * (S ω * Q₂) * (Q₂ᴴ * E))
      ≤ specNorm (pinv (S ω * Q₁)) * specNorm (S ω * Q₂) * specNorm (Q₂ᴴ * E) :=
        (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (specNorm_mul_le _ _)
          (specNorm_nonneg _))
    _ ≤ specNorm (pinv (Q₁ᴴ * (S ω)ᴴ)) * frobNorm (Q₂ᴴ * (S ω)ᴴ) * specNorm (Q₂ᴴ * E) := by
        rw [h1]
        gcongr

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- **Gaussian sketch-and-solve is unbiased**: for a standard Gaussian $p \times m$ sketch
$\mathbf{S}$ and $\operatorname{rank}\mathbf{A} + 1 \le p$,
$$\mathbb{E}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B}) =
\mathbf{A}^{+}\mathbf{B}\,.$$
At $\mathbf{A} = \mathbf{Q}$ with orthonormal columns this is the unbiasedness of the sketched
core of generalized Nyström. The reflection $2\mathbf{P}_{\mathbf{A}} - \mathbf{I}$ preserves the
law of $\mathbf{S}$, fixes $\mathbf{A}$ and negates the residual; at $p = \operatorname{rank}
\mathbf{A}$ the solution need not be integrable.
[EpperlyWebber2026, Theorem 2.1]; [TroppYurtseverUdellCevher2017, Lemma A.5]; there with
$\operatorname{rank}\mathbf{A} + 2 \le p$.
Result: sketch-and-solve-expected-error -/
theorem integral_sketchAndSolve_of_hasLaw_gaussianMatrix [DecidableEq r]
    (hS : HasLaw S (gaussianMatrix p m) μ) {A : Matrix m n ℝ}
    (hA : A.rank + 1 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, sketchAndSolve A (S ω) B ∂μ = pinv A * B := by
  classical
  have := hS.isProbabilityMeasure
  set E := (1 - rangeProjector A) * B with hEdef
  set D : Matrix m m ℝ := (2 : ℝ) • rangeProjector A - 1 with hDdef
  have hPP := rangeProjector_mul_rangeProjector A
  have hDD : D * D = 1 := by
    simp only [hDdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hPP]
    module
  have hDh : Dᴴ = D := by
    simp only [hDdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
      conjTranspose_rangeProjector, Matrix.conjTranspose_one]
  have hD : HasOrthonormalCols D := by
    rw [hasOrthonormalCols_iff, hDh, hDD]
  have hDA : D * A = A := by
    simp only [hDdef, Matrix.sub_mul, Matrix.smul_mul, rangeProjector_mul_self, Matrix.one_mul]
    module
  have hDE : D * E = -E := by
    have hPE : rangeProjector A * E = 0 := by
      rw [hEdef, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
        Matrix.zero_mul]
    simp only [hDdef, Matrix.sub_mul, Matrix.smul_mul, hPE, Matrix.one_mul, smul_zero, zero_sub]
  set f : Matrix p m ℝ → Matrix n r ℝ := fun S₀ => sketchAndSolve A S₀ E with hf
  have hfm : Measurable f :=
    (measurable_pinv.comp (measurable_id.matrix_mul measurable_const)).matrix_mul
      (measurable_id.matrix_mul measurable_const)
  have hfD (S₀ : Matrix p m ℝ) : f (S₀ * D) = -f S₀ := by
    simp only [hf, sketchAndSolve, Matrix.mul_assoc, hDA, hDE, Matrix.mul_neg]
  have hSD := hasLaw_mul_const_of_hasLaw_gaussianMatrix hS hD
  have h1 : ∫ ω, f (S ω) ∂μ = ∫ x, f x ∂(gaussianMatrix p m) :=
    hS.integral_comp hfm.aestronglyMeasurable
  have h2 : ∫ ω, f (S ω * D) ∂μ = ∫ x, f x ∂(gaussianMatrix p m) :=
    hSD.integral_comp hfm.aestronglyMeasurable
  have h0 : ∫ ω, f (S ω) ∂μ = 0 := by
    have h3 : ∫ ω, f (S ω) ∂μ = -∫ ω, f (S ω) ∂μ :=
      calc ∫ ω, f (S ω) ∂μ = ∫ ω, f (S ω * D) ∂μ := h1.trans h2.symm
        _ = ∫ ω, -f (S ω) ∂μ := by simp only [hfD]
        _ = -∫ ω, f (S ω) ∂μ := integral_neg _
    have h4 : (2 : ℝ) • ∫ ω, f (S ω) ∂μ = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h3]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h4).resolve_left two_ne_zero
  have hfi : Integrable (fun ω => f (S ω)) μ :=
    integrable_sketchAndSolve_of_hasLaw_gaussianMatrix hS hA E
  have hae : ∀ᵐ ω ∂μ, sketchAndSolve A (S ω) B = pinv A * B + f (S ω) := by
    filter_upwards [ae_rank_mul_eq hS A (by omega)] with ω hω
    exact sketchAndSolve_eq_pinv_mul_add hω B
  rw [integral_congr_ae hae, integral_add (integrable_const _) hfi, h0, add_zero, integral_const,
    probReal_univ, one_smul]

/-! ### Haar sketches

For an $m \times p$ Haar frame $\mathbf{Q}$ with $p \le m$ the sketch is
$\mathbf{Q}^{\mathsf{H}}$; the proofs are those above with the random orthonormal sketching
identity `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame` in
place of the Gaussian block moment. -/

variable {Q : Ω → Matrix m p ℝ}

/-- **Orthogonality helps, but only a bit**: the Haar projection factor is at most the Gaussian
one, <!-- value haarProjectionFactor d p q --> <!-- value gaussianProjectionFactor q p -->
$1 + (d - p)/(d - q) \cdot (q/(p - q - 1)) \le 1 + q/(p - q - 1)$ for $q + 2 \le p \le d$; the
excesses over $1$ are in the ratio $(d-p)/(d-q)$.
[EpperlyWebber2026, §2.1]. -/
theorem haarProjectionFactor_le_gaussianProjectionFactor {d p q : ℕ} (hqp : q + 2 ≤ p)
    (hpd : p ≤ d) : haarProjectionFactor d p q ≤ gaussianProjectionFactor q p := by
  have hqp' : (q : ℝ) + 2 ≤ p := by exact_mod_cast hqp
  have hpd' : (p : ℝ) ≤ d := by exact_mod_cast hpd
  rw [haarProjectionFactor_def, gaussianProjectionFactor_def, add_le_add_iff_left]
  refine mul_le_of_le_one_left (div_nonneg (Nat.cast_nonneg q) (by linarith)) ?_
  exact div_le_one_of_le₀ (by linarith) (by linarith)

omit [DecidableEq m] in
/-- The rank event holds almost surely for a Haar sketch:
$\operatorname{rank}(\mathbf{Q}^{\mathsf{H}}\mathbf{X}) = \operatorname{rank}\mathbf{X}$ when
$\operatorname{rank}\mathbf{X} \le p$. -/
private theorem ae_rank_conjTranspose_mul_eq [DecidableEq p] (hQ : HasLaw Q (haarFrame m p) μ)
    (X : Matrix m s ℝ) (hX : X.rank ≤ Fintype.card p) :
    ∀ᵐ ω ∂μ, ((Q ω)ᴴ * X).rank = X.rank := by
  filter_upwards [ae_rank_mul_eq_min_of_hasLaw_haarFrame Xᴴ hQ] with ω hω
  rw [show (Q ω)ᴴ * X = (Xᴴ * Q ω)ᴴ by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], Matrix.rank_conjTranspose,
    hω, Matrix.rank_conjTranspose, min_eq_left hX]

/-! ### Haar sketches: the completion identity -/

/-- The completion split, almost surely, for a Haar sketch. -/
private theorem ae_frobNorm_one_sub_obliqueProjector_mul_sq_eq_haar [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) {X : Matrix m s ℝ} (hX : X.rank ≤ Fintype.card p)
    {B : Matrix m r ℝ} {t : ℕ}
    {Q₁ : Matrix m (Fin X.rank) ℝ} {Q₂ : Matrix m (Fin t) ℝ} (hQ₁ : HasOrthonormalCols Q₁)
    (hR₁ : LinearMap.range Q₁.mulVecLin = LinearMap.range X.mulVecLin)
    (hE : Q₂ * (Q₂ᴴ * ((1 - rangeProjector X) * B)) = (1 - rangeProjector X) * B) :
    ∀ᵐ ω ∂μ, frobNorm ((1 - obliqueProjector X (Q ω)ᴴ) * B) ^ 2 =
      frobNorm ((1 - rangeProjector X) * B) ^ 2 +
        frobNorm (pinv ((Q ω)ᴴ * Q₁) * ((Q ω)ᴴ * Q₂) *
          (Q₂ᴴ * ((1 - rangeProjector X) * B))) ^ 2 := by
  filter_upwards [ae_rank_conjTranspose_mul_eq hQ X hX] with ω hω
  rw [frobNorm_one_sub_obliqueProjector_mul_sq hω,
    obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hω, hQ₁.frobNorm_mul_left]

/-- The squared error of the Haar oblique projection is integrable for
$\operatorname{rank}\mathbf{X} + 2 \le p \le m$. -/
theorem integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    (X : Matrix m s ℝ) (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm ((1 - obliqueProjector X (Q ω)ᴴ) * B) ^ 2) μ := by
  have := hQ.isProbabilityMeasure
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrp : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hint := integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame hQ hpm hQ₁ hQ₂ hrp
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  exact ((integrable_const _).add hint).congr
    ((ae_frobNorm_one_sub_obliqueProjector_mul_sq_eq_haar hQ (by omega) hQ₁ hR₁ hE).mono
      fun _ h => h.symm)

/-- **The Haar completion identity**: for an $m \times p$ Haar frame $\mathbf{Q}$ with $p \le m$,
the sketch $\mathbf{Q}^{\mathsf{H}}$, every fixed $\mathbf{X}$ with
$\operatorname{rank}\mathbf{X} + 2 \le p$ and every $\mathbf{B}$, writing
$q = \operatorname{rank}\mathbf{X}$, <!-- value haarProjectionFactor m p q -->
$$\mathbb{E}\|(\mathbf{I}-\mathbf{\Pi}_{\mathbf{X},\mathbf{Q}^{\mathsf{H}}})\mathbf{B}
\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{m - p}{m - q}\cdot\frac{q}{p - q - 1}\Bigr)
\|(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}\|_{\mathsf{F}}^2\,,$$
No full rank of $\mathbf{X}$ is assumed. For
$p > m$ the formula is false (the sketch is then an isometry and the error is the orthogonal one),
hence $p \le m$. The Gaussian twin is
`NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix`.
[EpperlyWebber2026, Theorem 2.1 and Proposition 5.7]; there for $\mathbf{X} = \mathbf{A}$, here any
basis of any rank.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    (X : Matrix m s ℝ) (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm ((1 - obliqueProjector X (Q ω)ᴴ) * B) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) X.rank *
        frobNorm ((1 - rangeProjector X) * B) ^ 2 := by
  have := hQ.isProbabilityMeasure
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl X B
  have hrp : Fintype.card (Fin X.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hrs : Fintype.card (Fin X.rank) + Fintype.card (Fin (Fintype.card m - X.rank)) =
      Fintype.card m := by
    simp only [Fintype.card_fin]; omega
  have hint := integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame hQ hpm hQ₁ hQ₂ hrp
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  have hval := integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame hQ hpm hQ₁ hQ₂ h₁₂ hrs hrp
    (Q₂ᴴ * ((1 - rangeProjector X) * B))
  have hQE : frobNorm (Q₂ᴴ * ((1 - rangeProjector X) * B)) =
      frobNorm ((1 - rangeProjector X) * B) := by
    rw [← hQ₂.frobNorm_mul_left, hE]
  rw [integral_congr_ae
      (ae_frobNorm_one_sub_obliqueProjector_mul_sq_eq_haar hQ (by omega) hQ₁ hR₁ hE),
    integral_add (integrable_const _) hint, integral_const, probReal_univ, one_smul, hval,
    Fintype.card_fin, haarProjectionFactor_def, hQE]
  ring

/-- **Exact mean squared residual of sketch-and-solve with a random orthonormal sketch**: for an
$m \times p$ Haar frame $\mathbf{Q}$ with $p \le m$, the sketch $\mathbf{Q}^{\mathsf{H}}$ and
$r = \operatorname{rank}\mathbf{A}$ with $r + 2 \le p$, <!-- value haarProjectionFactor m p r -->
$$\mathbb{E}\|\mathbf{B} - \mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{Q}^{\mathsf{H}},
\mathbf{B})\|_{\mathsf{F}}^2 = \Bigl(1 + \frac{m - p}{m - r}\cdot\frac{r}{p - r - 1}\Bigr)
\min_{\mathbf{Y}}\|\mathbf{B}-\mathbf{A}\mathbf{Y}\|_{\mathsf{F}}^2\,,$$
the minimum being $\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}\|_{\mathsf{F}}^2$ and the factor
`haarProjectionFactor m p r`. Its integrand is that of
`NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame` at
$\mathbf{X} = \mathbf{A}$ (`NLAlib.mul_sketchAndSolve`), whose integrability companion applies.
[EpperlyWebber2026, Theorem 2.1 (random orthonormal)]; real case, $\alpha_{\mathbb{R}} = 1$.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame [DecidableEq p]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2 ∂μ =
      haarProjectionFactor (Fintype.card m) (Fintype.card p) A.rank *
        frobNorm ((1 - rangeProjector A) * B) ^ 2 := by
  simp only [mul_sketchAndSolve]
  rw [← integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame hQ hpm A hA B]
  simp only [Matrix.sub_mul, Matrix.one_mul]

/-! ### Haar sketches: unbiasedness -/

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- The sketch-and-solve solution
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{Q}^{\mathsf{H}}, \mathbf{B})$ with a Haar sketch is
integrable for $\operatorname{rank}\mathbf{A} + 2 \le p \le m$. -/
theorem integrable_sketchAndSolve_of_hasLaw_haarFrame [DecidableEq p] [DecidableEq r]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => sketchAndSolve A (Q ω)ᴴ B) μ := by
  classical
  have := hQ.isProbabilityMeasure
  obtain ⟨Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_hasOrthonormalCols_frames_range_compl A B
  set E := (1 - rangeProjector A) * B
  have hrp : Fintype.card (Fin A.rank) + 2 ≤ Fintype.card p := by rwa [Fintype.card_fin]
  have hint := integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame hQ hpm hQ₁ hQ₂ hrp
    (Q₂ᴴ * E)
  have hm : Measurable fun Q₀ : Matrix m p ℝ => sketchAndSolve A Q₀ᴴ B :=
    (measurable_pinv.comp (continuous_id.matrix_conjTranspose.measurable.matrix_mul
      measurable_const)).matrix_mul
      (continuous_id.matrix_conjTranspose.measurable.matrix_mul measurable_const)
  refine Integrable.mono' ((integrable_const (specNorm (pinv A * B))).add
    (((integrable_const 1).add hint).const_mul (specNorm (pinv A))))
    (hm.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable ?_
  filter_upwards [ae_rank_conjTranspose_mul_eq hQ A (by omega)] with ω hω
  rw [← specNorm_eq_norm, sketchAndSolve_eq_pinv_mul_add hω B]
  refine (specNorm_add_le _ _).trans (add_le_add le_rfl ?_)
  rw [← pinv_mul_mul_sketchAndSolve A (Q ω)ᴴ E, mul_sketchAndSolve,
    obliqueProjector_mul_one_sub_rangeProjector_mul_eq hR₁ hE hω]
  refine (specNorm_mul_le _ _).trans (mul_le_mul_of_nonneg_left ?_ (specNorm_nonneg _))
  rw [hQ₁.specNorm_mul_left]
  set x := frobNorm (pinv ((Q ω)ᴴ * Q₁) * ((Q ω)ᴴ * Q₂) * (Q₂ᴴ * E))
  have hx : x ≤ 1 + x ^ 2 := by nlinarith [sq_nonneg (x - 1)]
  exact (specNorm_le_frobNorm _).trans hx

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- **Sketch-and-solve with a random orthonormal sketch is unbiased**: for an $m \times p$ Haar
frame $\mathbf{Q}$ with $p \le m$ and $\operatorname{rank}\mathbf{A} + 2 \le p$,
$$\mathbb{E}\,\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{Q}^{\mathsf{H}}, \mathbf{B}) =
\mathbf{A}^{+}\mathbf{B}\,.$$
The reflection $2\mathbf{P}_{\mathbf{A}} - \mathbf{I}$, acting on the left of the frame, preserves
its law, fixes $\mathbf{A}$ and negates the residual. The Gaussian twin is
`NLAlib.integral_sketchAndSolve_of_hasLaw_gaussianMatrix`.
[EpperlyWebber2026, Theorem 2.1]; real case.
Result: sketch-and-solve-expected-error -/
theorem integral_sketchAndSolve_of_hasLaw_haarFrame [DecidableEq p] [DecidableEq r]
    (hQ : HasLaw Q (haarFrame m p) μ) (hpm : Fintype.card p ≤ Fintype.card m)
    {A : Matrix m n ℝ} (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, sketchAndSolve A (Q ω)ᴴ B ∂μ = pinv A * B := by
  classical
  have := hQ.isProbabilityMeasure
  set E := (1 - rangeProjector A) * B with hEdef
  set D : Matrix m m ℝ := (2 : ℝ) • rangeProjector A - 1 with hDdef
  have hPP := rangeProjector_mul_rangeProjector A
  have hDD : D * D = 1 := by
    simp only [hDdef, Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one, hPP]
    module
  have hDh : Dᴴ = D := by
    simp only [hDdef, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, star_trivial,
      conjTranspose_rangeProjector, Matrix.conjTranspose_one]
  have hD : HasOrthonormalCols D := by
    rw [hasOrthonormalCols_iff, hDh, hDD]
  have hDA : D * A = A := by
    simp only [hDdef, Matrix.sub_mul, Matrix.smul_mul, rangeProjector_mul_self, Matrix.one_mul]
    module
  have hDE : D * E = -E := by
    have hPE : rangeProjector A * E = 0 := by
      rw [hEdef, ← Matrix.mul_assoc, Matrix.mul_sub, Matrix.mul_one, hPP, sub_self,
        Matrix.zero_mul]
    simp only [hDdef, Matrix.sub_mul, Matrix.smul_mul, hPE, Matrix.one_mul, smul_zero, zero_sub]
  set f : Matrix m p ℝ → Matrix n r ℝ := fun Q₀ => sketchAndSolve A Q₀ᴴ E with hf
  have hfm : Measurable f :=
    (measurable_pinv.comp (continuous_id.matrix_conjTranspose.measurable.matrix_mul
      measurable_const)).matrix_mul
      (continuous_id.matrix_conjTranspose.measurable.matrix_mul measurable_const)
  have hfD (Q₀ : Matrix m p ℝ) : f (D * Q₀) = -f Q₀ := by
    simp only [hf, sketchAndSolve, Matrix.conjTranspose_mul, hDh, Matrix.mul_assoc, hDA, hDE,
      Matrix.mul_neg]
  have hQD := hasLaw_const_mul_of_isLeftUnitarilyInvariant hQ hD
  have h1 : ∫ ω, f (Q ω) ∂μ = ∫ x, f x ∂(haarFrame m p) :=
    hQ.integral_comp hfm.aestronglyMeasurable
  have h2 : ∫ ω, f (D * Q ω) ∂μ = ∫ x, f x ∂(haarFrame m p) :=
    hQD.integral_comp hfm.aestronglyMeasurable
  have h0 : ∫ ω, f (Q ω) ∂μ = 0 := by
    have h3 : ∫ ω, f (Q ω) ∂μ = -∫ ω, f (Q ω) ∂μ :=
      calc ∫ ω, f (Q ω) ∂μ = ∫ ω, f (D * Q ω) ∂μ := h1.trans h2.symm
        _ = ∫ ω, -f (Q ω) ∂μ := by simp only [hfD]
        _ = -∫ ω, f (Q ω) ∂μ := integral_neg _
    have h4 : (2 : ℝ) • ∫ ω, f (Q ω) ∂μ = 0 := by
      rw [two_smul]
      nth_rewrite 2 [h3]
      exact add_neg_cancel _
    exact (smul_eq_zero.mp h4).resolve_left two_ne_zero
  have hfi : Integrable (fun ω => f (Q ω)) μ :=
    integrable_sketchAndSolve_of_hasLaw_haarFrame hQ hpm hA E
  have hae : ∀ᵐ ω ∂μ, sketchAndSolve A (Q ω)ᴴ B = pinv A * B + f (Q ω) := by
    filter_upwards [ae_rank_conjTranspose_mul_eq hQ A (by omega)] with ω hω
    exact sketchAndSolve_eq_pinv_mul_add hω B
  rw [integral_congr_ae hae, integral_add (integrable_const _) hfi, h0, add_zero, integral_const,
    probReal_univ, one_smul]

/-! ### Expected relative residual -/

omit [DecidableEq m] in
/-- The squared Frobenius residual of Gaussian sketch-and-solve
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{S}, \mathbf{B})$ is integrable when
$\operatorname{rank}\mathbf{A}+2\le p$. This rewrites the oblique-projection integrability
result into the algorithm's residual form. -/
theorem integrable_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (A : Matrix m n ℝ)
    (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2) μ := by
  classical
  simpa only [mul_sketchAndSolve, Matrix.sub_mul, Matrix.one_mul] using
    integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix hS A hA B

omit [DecidableEq m] in
/-- The squared Frobenius residual of Haar sketch-and-solve
$\mathsf{sketchAndSolve}(\mathbf{A}, \mathbf{Q}^{\mathsf{H}}, \mathbf{B})$ is integrable when
$\operatorname{rank}\mathbf{A}+2\le p\le m$. This rewrites the oblique-projection
integrability result into the algorithm's residual form. -/
theorem integrable_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame [DecidableEq p]
    {Q : Ω → Matrix m p ℝ} (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (A : Matrix m n ℝ)
    (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2) μ := by
  classical
  simpa only [mul_sketchAndSolve, Matrix.sub_mul, Matrix.one_mul] using
    integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_haarFrame hQ hpm A hA B

/-- **Gaussian sketch-and-solve, expected relative residual**: for a standard Gaussian
$p\times m$ sketch $\mathbf{S}$, $r=\operatorname{rank}\mathbf{A}$,
$r+2\le p$ and a real $\varepsilon$ with $r\le\varepsilon(p-r-1)$ (for $\varepsilon>0$:
$p\ge r+1+r/\varepsilon$),
$$\mathbb{E}\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{S},\mathbf{B})
\|_{\mathsf{F}}^2\le(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2\,.$$
The right side uses the optimal squared residual, for any rank of $\mathbf{A}$ and any matrix
right-hand side. [EpperlyWebber2026, Theorem 2.1 and §2.1]; the real Gaussian identity there,
here its sufficient-size corollary. Integrability is
`NLAlib.integrable_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix`.
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_gaussianMatrix`.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (A : Matrix m n ℝ) (B : Matrix m r ℝ)
    {ε : ℝ} (hA : A.rank + 2 ≤ Fintype.card p)
    (hp : (A.rank : ℝ) ≤ ε * ((Fintype.card p : ℝ) - A.rank - 1)) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 := by
  rw [integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix hS hA B]
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  have hA' : (A.rank : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hA
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ (by linarith)]
  exact hp

/-- **Haar sketch-and-solve, expected relative residual**: for an $m\times p$ Haar frame
$\mathbf{Q}$, the sketch $\mathbf{Q}^{\mathsf{H}}$, $r=\operatorname{rank}\mathbf{A}$,
$r+2\le p\le m$ and a real $\varepsilon$ with $r\le\varepsilon(p-r-1)$ (for $\varepsilon>0$:
$p\ge r+1+r/\varepsilon$),
$$\mathbb{E}\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{Q}^{\mathsf{H}},
\mathbf{B})\|_{\mathsf{F}}^2\le(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2\,.$$
The right side uses the optimal squared residual, for any rank of $\mathbf{A}$ and any matrix
right-hand side. [EpperlyWebber2026, Theorem 2.1 and §2.1]; the real orthonormal identity there,
here a sufficient-size corollary using its factor's upper bound by the Gaussian factor.
Integrability is `NLAlib.integrable_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame`.
Asymptotic form:
`NLAlib.exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_haarFrame`.
Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame
    [DecidableEq p] {Q : Ω → Matrix m p ℝ} (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (A : Matrix m n ℝ) (B : Matrix m r ℝ)
    {ε : ℝ} (hA : A.rank + 2 ≤ Fintype.card p)
    (hp : (A.rank : ℝ) ≤ ε * ((Fintype.card p : ℝ) - A.rank - 1)) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 := by
  rw [integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame hQ hpm hA B]
  apply mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  refine (haarProjectionFactor_le_gaussianProjectionFactor hA hpm).trans ?_
  have hA' : (A.rank : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hA
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ (by linarith)]
  exact hp

/-- **Gaussian sketch-and-solve, asymptotic expected relative residual**:
$O((r+1)/\varepsilon)$ Gaussian rows suffice, where $r=\operatorname{rank}\mathbf{A}$:
for $0<\varepsilon\le\varepsilon_0$ and absolute constants $C,\varepsilon_0>0$, a standard
Gaussian $p\times m$ sketch with $p\ge C(r+1)/\varepsilon$ satisfies
$$\mathbb{E}\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{S},\mathbf{B})
\|_{\mathsf{F}}^2\le(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2\,.$$
No positive-rank hypothesis is needed. The constants precede every dimension and matrix.
Proved from
`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_gaussianMatrix`
with $C=3$, $\varepsilon_0=1$. [EpperlyWebber2026, Theorem 2.1 and §2.1]; the source gives the
explicit sufficient size, here a rank-zero-safe asymptotic corollary.
Asymptotic:
NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
Result: sketch-and-solve-expected-error -/
theorem exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω m n r p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        [Fintype r] [Fintype p] [DecidableEq m] (μ : Measure Ω) (S : Ω → Matrix p m ℝ)
        (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε : ℝ),
        HasLaw S (gaussianMatrix p m) μ → 0 < ε → ε ≤ ε₀ →
        C * (((A.rank : ℝ) + 1) / ε) ≤ Fintype.card p →
        ∫ ω, frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 ∂μ ≤
          (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n r p _ _ _ _ _ _ μ S A B ε hS hε hε1 hp
  have hp' : 3 * (((A.rank + 1 : ℕ) : ℝ) / ε) ≤ Fintype.card p := by
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  obtain ⟨hA, hfac⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le
    (Nat.succ_pos A.rank) hε hε1 hp'
  have hA' : (A.rank : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast (show A.rank + 2 ≤
    Fintype.card p by omega)
  have hfac' := (gaussianProjectionFactor_le_gaussianProjectionFactor (Nat.le_succ _) hA).trans hfac
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ (by linarith)] at hfac'
  exact integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    hS A B (by omega) hfac'

/-- **Haar sketch-and-solve, asymptotic expected relative residual**:
$O((r+1)/\varepsilon)$ orthonormal sketch rows suffice, where $r=\operatorname{rank}\mathbf{A}$:
for $0<\varepsilon\le\varepsilon_0$ and absolute constants $C,\varepsilon_0>0$, an $m\times p$
Haar frame with $C(r+1)/\varepsilon\le p\le m$ satisfies
$$\mathbb{E}\|\mathbf{B}-\mathbf{A}\,\mathsf{sketchAndSolve}(\mathbf{A},\mathbf{Q}^{\mathsf{H}},
\mathbf{B})\|_{\mathsf{F}}^2\le(1+\varepsilon)\|(\mathbf{I}-\mathbf{P}_{\mathbf{A}})\mathbf{B}
\|_{\mathsf{F}}^2\,.$$
No positive-rank hypothesis is needed. The constants precede every dimension and matrix.
Proved from
`NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame`
with $C=3$, $\varepsilon_0=1$. [EpperlyWebber2026, Theorem 2.1 and §2.1]; here the uniform
sufficient Gaussian size also bounds the smaller Haar factor.
Asymptotic:
NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame
Result: sketch-and-solve-expected-error -/
theorem exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω m n r p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        [Fintype r] [Fintype p] [DecidableEq m] [DecidableEq p] (μ : Measure Ω)
        (Q : Ω → Matrix m p ℝ) (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε : ℝ),
        HasLaw Q (haarFrame m p) μ → Fintype.card p ≤ Fintype.card m →
        0 < ε → ε ≤ ε₀ → C * (((A.rank : ℝ) + 1) / ε) ≤ Fintype.card p →
        ∫ ω, frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2 ∂μ ≤
          (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 := by
  refine ⟨3, 1, by norm_num, one_pos, ?_⟩
  intro Ω m n r p _ _ _ _ _ _ _ μ Q A B ε hQ hpm hε hε1 hp
  have hp' : 3 * (((A.rank + 1 : ℕ) : ℝ) / ε) ≤ Fintype.card p := by
    simpa only [Nat.cast_add, Nat.cast_one] using hp
  obtain ⟨hA, hfac⟩ := gaussianProjectionFactor_le_one_add_of_three_mul_div_le
    (Nat.succ_pos A.rank) hε hε1 hp'
  have hA' : (A.rank : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast (show A.rank + 2 ≤
    Fintype.card p by omega)
  have hfac' := (gaussianProjectionFactor_le_gaussianProjectionFactor (Nat.le_succ _) hA).trans hfac
  rw [gaussianProjectionFactor_def, add_le_add_iff_left, div_le_iff₀ (by linarith)] at hfac'
  exact integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame
    hQ hpm A B (by omega) hfac'

end NLAlib
