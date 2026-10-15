/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import NLAlib.Matrix.Pseudoinverse.LeastSquares
public import NLAlib.Probability.MatrixIntegral
public import NLAlib.RandomMatrix.Gaussian.BlockMomentsSpectral
public import NLAlib.RandomMatrix.Gaussian.Invariance
public import NLAlib.RandomMatrix.Gaussian.Rank

/-!
# Sketched least squares with Gaussian sketches

For a standard Gaussian $p \times m$ sketch $\mathbf{S}$, a fixed basis $\mathbf{X}$ of rank $q$
with $q + 2 \le p$ and every $\mathbf{B}$, the oblique projection
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}$ (`NLAlib.obliqueProjector`) inflates the error of the
orthogonal projection by exactly the factor $1 + \frac{q}{p - q - 1}$, in expectation:
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
$\mathbf{Q}_2$, of the range of the residual $(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$;
on the almost sure event $\operatorname{rank}(\mathbf{S}\mathbf{X}) = \operatorname{rank}\mathbf{X}$
the excess is $\mathbf{Q}_1(\mathbf{S}\mathbf{Q}_1)^{+}(\mathbf{S}\mathbf{Q}_2)
\mathbf{Q}_2^{\mathsf{H}}(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$, a Gaussian block whose
moments are in `NLAlib.RandomMatrix.Gaussian.BlockMoments` and
`NLAlib.RandomMatrix.Gaussian.BlockMomentsSpectral`. Unbiasedness is a symmetry: the reflection
$2\mathbf{P}_{\mathbf{A}} - \mathbf{I}$ preserves the Gaussian law, fixes $\mathbf{A}$ and negates
the residual. The sketch is on the left, $\mathbf{S} : p \times m$, as in the other Gaussian
sketching files; a co-range test matrix $\mathbf{\Psi}$ is the sketch $\mathbf{\Psi}^{\mathsf{H}}$
(`NLAlib.hasLaw_conjTranspose_of_hasLaw_gaussianMatrix`). Scaling the sketch changes nothing
(`NLAlib.obliqueProjector_smul_right`). Real throughout. Design: `docs/design/LowRank-S6.md` §3.2,
§8 (the Gaussian half; the Haar statements follow in a later section).

## Main results

* `NLAlib.integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix`: the
  Gaussian completion identity.
* `NLAlib.integral_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix`: the exact mean
  squared residual of Gaussian sketch-and-solve.
* `NLAlib.integral_sketchAndSolve_of_hasLaw_gaussianMatrix`: unbiasedness.
* the spectral norm of the excess,
  `integral_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_le_of_hasLaw_gaussianMatrix`
  and its numerical form for $4q \le p$ (the same name with `_le_div_card` in place of `_le`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m n p r s : Type*} [Fintype m]
  [Fintype n] [Fintype p] [Fintype r] [Fintype s] [DecidableEq m] {S : Ω → Matrix p m ℝ}

/-! ### The basis step -/

omit [Fintype r] in
/-- Orthonormal bases of $\operatorname{range}\mathbf{X}$ and of its orthogonal complement; the
second reproduces every residual $(\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$. -/
private theorem exists_frames (X : Matrix m s ℝ) (B : Matrix m r ℝ) :
    ∃ (t : ℕ) (Q₁ : Matrix m (Fin X.rank) ℝ) (Q₂ : Matrix m (Fin t) ℝ),
      HasOrthonormalCols Q₁ ∧ HasOrthonormalCols Q₂ ∧ Q₁ᴴ * Q₂ = 0 ∧
        LinearMap.range Q₁.mulVecLin = LinearMap.range X.mulVecLin ∧
          Q₂ * (Q₂ᴴ * ((1 - rangeProjector X) * B)) = (1 - rangeProjector X) * B := by
  obtain ⟨Q₁, hQ₁, hR₁⟩ := exists_hasOrthonormalCols_range_eq (p := Fin X.rank) X
    (Fintype.card_fin _)
  obtain ⟨Q₂, hQ₂, hR₂⟩ := exists_hasOrthonormalCols_range_eq
    (p := Fin (1 - rangeProjector X).rank) (1 - rangeProjector X) (Fintype.card_fin _)
  refine ⟨_, Q₁, Q₂, hQ₁, hQ₂, ?_, hR₁, ?_⟩
  · obtain ⟨C, hC⟩ := range_mulVecLin_le_iff_exists_mul.mp hR₂.le
    have hP : rangeProjector X = Q₁ * Q₁ᴴ := by
      rw [← rangeProjector_inj.mpr hR₁, hQ₁.rangeProjector_eq]
    have h0 : Q₁ᴴ * (1 - rangeProjector X) = 0 := by
      rw [hP, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hQ₁.conjTranspose_mul_self,
        Matrix.one_mul, sub_self]
    rw [hC, ← Matrix.mul_assoc, h0, Matrix.zero_mul]
  · rw [← Matrix.mul_assoc, ← hQ₂.rangeProjector_eq, rangeProjector_inj.mpr hR₂,
      ← Matrix.mul_assoc, rangeProjector_mul_self]

omit [Fintype r] in
/-- On the rank event the excess is a Gaussian block in the two bases:
$\mathbf{\Pi}_{\mathbf{X},\mathbf{S}}\mathbf{E} =
\mathbf{Q}_1(\mathbf{S}\mathbf{Q}_1)^{+}(\mathbf{S}\mathbf{Q}_2)\mathbf{Q}_2^{\mathsf{H}}\mathbf{E}$
with $\mathbf{E} = (\mathbf{I}-\mathbf{P}_{\mathbf{X}})\mathbf{B}$. -/
private theorem obliqueProjector_mul_eq_frames {X : Matrix m s ℝ} {B : Matrix m r ℝ} {t : ℕ}
    {Q₁ : Matrix m (Fin X.rank) ℝ} {Q₂ : Matrix m (Fin t) ℝ}
    (hR₁ : LinearMap.range Q₁.mulVecLin = LinearMap.range X.mulVecLin)
    (hE : Q₂ * (Q₂ᴴ * ((1 - rangeProjector X) * B)) = (1 - rangeProjector X) * B)
    {S₀ : Matrix p m ℝ} (h : (S₀ * X).rank = X.rank) :
    obliqueProjector X S₀ * ((1 - rangeProjector X) * B) =
      Q₁ * (pinv (S₀ * Q₁) * (S₀ * Q₂) * (Q₂ᴴ * ((1 - rangeProjector X) * B))) := by
  rw [obliqueProjector_eq_of_range_eq h hR₁.symm, obliqueProjector]
  conv_lhs => rw [← hE]
  simp only [Matrix.mul_assoc]

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
  rw [frobNorm_one_sub_obliqueProjector_mul_sq hω, obliqueProjector_mul_eq_frames hR₁ hE hω,
    hQ₁.frobNorm_mul_left]

/-- The squared error of the Gaussian oblique projection is integrable for
$\operatorname{rank}\mathbf{X} + 2 \le p$. -/
theorem integrable_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm ((1 - obliqueProjector X (S ω)) * B) ^ 2) μ := by
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨t, Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_frames X B
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
`gaussianProjectionFactor q p`. No full rank of $\mathbf{X}$ is assumed; at
$p = q + 1$ the left side is not integrable unless the residual vanishes.
[EpperlyWebber2026, Theorem 2.1 and Lemma 5.1]; [TroppYurtseverUdellCevher2017, Lemma A.5];
there for $\mathbf{X} = \mathbf{A}$ (EW) or an orthonormal $\mathbf{Q}$ (TYUC), here any basis of
any rank. Result: sketch-and-solve-expected-error -/
theorem integral_frobNorm_one_sub_obliqueProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    ∫ ω, frobNorm ((1 - obliqueProjector X (S ω)) * B) ^ 2 ∂μ =
      gaussianProjectionFactor X.rank (Fintype.card p) *
        frobNorm ((1 - rangeProjector X) * B) ^ 2 := by
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨t, Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_frames X B
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
Bartan and Pilanci, as EW report. Result: sketch-and-solve-expected-error -/
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
  rw [obliqueProjector_mul_eq_frames hR₁ hE hω, hQ₁.specNorm_mul_left]

/-- The squared spectral norm of the Gaussian sketch-and-solve excess is integrable for
$\operatorname{rank}\mathbf{X} + 2 \le p$. -/
theorem
    integrable_specNorm_obliqueProjector_mul_one_sub_rangeProjector_mul_sq_of_hasLaw_gaussianMatrix
    (hS : HasLaw S (gaussianMatrix p m) μ) (X : Matrix m s ℝ)
    (hX : X.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable
      (fun ω => specNorm (obliqueProjector X (S ω) * ((1 - rangeProjector X) * B)) ^ 2) μ := by
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨t, Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_frames X B
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
$\frac{25}{p}\|\mathbf{E}\|_{\mathsf{F}}^2 + \frac{4q}{p}\|\mathbf{E}\|_2^2$ (the theorem of
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
  obtain ⟨t, Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_frames X B
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
/-- **The Gaussian sketch-and-solve excess is spectrally flat**: with
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

/-! ### Unbiasedness -/

omit [Fintype r] [DecidableEq m] in
/-- The sketch-and-solve solution for the residual lies in the row space of $\mathbf{A}$, so it is
$\mathbf{A}^{+}$ times its fitted values. -/
private theorem pinv_mul_mul_sketchAndSolve (A : Matrix m n ℝ) (S₀ : Matrix p m ℝ)
    (E : Matrix m r ℝ) : pinv A * (A * sketchAndSolve A S₀ E) = sketchAndSolve A S₀ E := by
  have h : rangeProjector Aᴴ * pinv (S₀ * A) = pinv (S₀ * A) := by
    refine rangeProjector_mul_eq_self_iff.mpr ?_
    rw [range_mulVecLin_pinv]
    exact range_mulVecLin_le_iff_exists_mul.mpr ⟨S₀ᴴ, Matrix.conjTranspose_mul _ _⟩
  rw [← Matrix.mul_assoc, pinv_mul, sketchAndSolve, ← Matrix.mul_assoc, h]

omit [DecidableEq m] in
open scoped Matrix.Norms.L2Operator in
/-- The Gaussian sketch-and-solve solution is integrable for
$\operatorname{rank}\mathbf{A} + 1 \le p$. -/
theorem integrable_sketchAndSolve_of_hasLaw_gaussianMatrix [DecidableEq r]
    (hS : HasLaw S (gaussianMatrix p m) μ) {A : Matrix m n ℝ}
    (hA : A.rank + 1 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => sketchAndSolve A (S ω) B) μ := by
  classical
  have := hS.isProbabilityMeasure
  have hG := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hS
  obtain ⟨t, Q₁, Q₂, hQ₁, hQ₂, h₁₂, hR₁, hE⟩ := exists_frames A B
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
    have := integrable_frobNorm_mul_mul_of_hasLaw_gaussianMatrix hY₂ (1 : Matrix (Fin t) (Fin t) ℝ)
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
    obliqueProjector_mul_eq_frames hR₁ hE hω]
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
$\operatorname{rank}\mathbf{A} + 2 \le p$. Result: sketch-and-solve-expected-error -/
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

end NLAlib
