/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Random.Nystrom
public import NLAlib.Matrix.Factorizations.NystromOrder
public import NLAlib.RandomMatrix.Gaussian.BlockMoments
public import NLAlib.RandomMatrix.Haar.Blocks
public import NLAlib.RandomMatrix.Haar.Transfer

/-!
# Epperly and Webber's factor and the two-eigenvalue instance

Epperly and Webber's sharp factor for rotation-invariant test matrices,
`NLAlib.rotationInvariantFactor r l q`, <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$, is HMT's factor times
$(r - \ell)/(r - q)$, with $r$ a bound on the rank, $\ell$ the number of samples and $q$ the
comparison rank. It is computed on the matrix
$\mathbf{D} = \operatorname{diag}(a\mathbf{I}_s, b\mathbf{I}_t)$ with two eigenvalues: for a test
matrix with a left unitarily invariant law and full column rank almost surely, the expected trace
error of Nyström is at most the factor times $b\lvert t\rvert$, at every $a$ (Epperly and Webber's
Lemma 6.2 takes the limit $a \to \infty$, where it is attained). The proof: the polar factor of the
test matrix is a Haar frame with the same Nyström approximation, the pointwise bound
`NLAlib.HasOrthonormalCols.nuclearNorm_fromBlocks_sub_nystrom_le`, and the Beta trace
`NLAlib.integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`. The sharp bounds themselves are in
`NLAlib.LowRank.Gaussian.RotationInvariant`; the matching lower bounds on this instance are in
`NLAlib.LowerBounds.LowRank.RotationInvariant`. Real field.

## Main definitions

* `NLAlib.rotationInvariantFactor`: Epperly and Webber's factor.

## Main results

* `NLAlib.rotationInvariantFactor_def`, `NLAlib.rotationInvariantFactor_nonneg`,
  `NLAlib.rotationInvariantFactor_le_gaussianProjectionFactor` (at most HMT's factor),
  `NLAlib.rotationInvariantFactor_le_rotationInvariantFactor` (monotone in the rank parameter).
* `NLAlib.integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant`: the
  two-eigenvalue instance.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix ComplexOrder MatrixOrder

namespace NLAlib

/-- **Epperly and Webber's factor** <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$: the sharp expected squared Frobenius error of
the randomized SVD, relative to the best rank-$q$ error, over matrices of rank $r$ and full-rank
rotation-invariant test matrices with $\ell$ columns, and the sharp expected trace error of
randomized Nyström relative to $\|\mathbf{H} - \llbracket\mathbf{H}\rrbracket_q\|_*$. It is HMT's
factor times $(r - \ell)/(r - q)$. A plain definition, because its body is the source's formula.
Junk: $0$ at $r = q$ (Lean's $x/0 = 0$), and HMT's factor is junk at $\ell = q + 1$; theorems carry
$q + 2 \le \ell \le r$. [EpperlyWebber2026, Theorems 3.2, 3.3]; there with
$\alpha_{\mathbb{R}} = 1$ in place of the $1$ in $\ell - q - 1$, and a minimum over $q$. -/
noncomputable def rotationInvariantFactor (r l q : ℕ) : ℝ :=
  ((r : ℝ) - l) / ((r : ℝ) - q) * gaussianProjectionFactor q l

/-- Epperly and Webber's factor is <!-- value rotationInvariantFactor r \ell q -->
$(r - \ell)/(r - q) \cdot (1 + q/(\ell - q - 1))$, as an equation with casts to $\mathbb{R}$. -/
theorem rotationInvariantFactor_def (r l q : ℕ) :
    rotationInvariantFactor r l q =
      ((r : ℝ) - l) / ((r : ℝ) - q) * (1 + (q : ℝ) / ((l : ℝ) - q - 1)) := by
  rw [rotationInvariantFactor, gaussianProjectionFactor_def]

/-- Epperly and Webber's factor is nonnegative for $q + 2 \le \ell \le r$. -/
theorem rotationInvariantFactor_nonneg {r l q : ℕ} (hq : q + 2 ≤ l) (hl : l ≤ r) :
    0 ≤ rotationInvariantFactor r l q := by
  have hq' : (q : ℝ) + 2 ≤ l := by exact_mod_cast hq
  have hl' : (l : ℝ) ≤ r := by exact_mod_cast hl
  rw [rotationInvariantFactor]
  exact mul_nonneg (div_nonneg (by linarith) (by linarith))
    (zero_le_one.trans (one_le_gaussianProjectionFactor hq))

/-- Epperly and Webber's factor is at most HMT's, <!-- value gaussianProjectionFactor q \ell -->
$1 + q/(\ell - q - 1)$ (the Lean name is `gaussianProjectionFactor q l`), for
$q + 2 \le \ell \le r$: the factor $(r - \ell)/(r - q)$ is at most one. -/
theorem rotationInvariantFactor_le_gaussianProjectionFactor {r l q : ℕ} (hq : q + 2 ≤ l)
    (hl : l ≤ r) : rotationInvariantFactor r l q ≤ gaussianProjectionFactor q l := by
  have hq' : (q : ℝ) + 2 ≤ l := by exact_mod_cast hq
  have hl' : (l : ℝ) ≤ r := by exact_mod_cast hl
  rw [rotationInvariantFactor]
  refine mul_le_of_le_one_left (zero_le_one.trans (one_le_gaussianProjectionFactor hq)) ?_
  rw [div_le_one (by linarith)]
  linarith

/-- Epperly and Webber's factor increases with the rank parameter: for
$q + 2 \le \ell \le r \le r'$ the factor at $r$ is at most the factor at $r'$, since
$(r - \ell)/(r - q) = 1 - (\ell - q)/(r - q)$. -/
theorem rotationInvariantFactor_le_rotationInvariantFactor {r r' l q : ℕ} (hq : q + 2 ≤ l)
    (hl : l ≤ r) (hr : r ≤ r') :
    rotationInvariantFactor r l q ≤ rotationInvariantFactor r' l q := by
  have hq' : (q : ℝ) + 2 ≤ l := by exact_mod_cast hq
  have hl' : (l : ℝ) ≤ r := by exact_mod_cast hl
  have hr' : (r : ℝ) ≤ r' := by exact_mod_cast hr
  rw [rotationInvariantFactor, rotationInvariantFactor]
  refine mul_le_mul_of_nonneg_right ?_ (zero_le_one.trans (one_le_gaussianProjectionFactor hq))
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l : Type*} [Fintype l]

/-- **Nyström for a matrix with two eigenvalues** (the hard instance): for $\mathbf{Y}$ on
$(s \oplus t) \times l$ with a left unitarily invariant law and full column rank almost surely,
$q = \lvert s\rvert$, $r = \lvert s\rvert + \lvert t\rvert$, $q + 2 \le \ell$ and
$a, b \ge 0$, <!-- value rotationInvariantFactor r \ell q -->
$$\mathbb{E}\bigl\|\mathbf{D} - \mathsf{nystrom}(\mathbf{D}, \mathbf{Y})\bigr\|_* \le
\frac{r - \ell}{r - q}\Bigl(1 + \frac{q}{\ell - q - 1}\Bigr)\,b\,\lvert t\rvert,\qquad
\mathbf{D} = \begin{bmatrix} a\mathbf{I} & \mathbf{0} \\ \mathbf{0} & b\mathbf{I}\end{bmatrix},$$
that is $b(r - \ell)(1 + q/(\ell-q-1))$; $b\lvert t\rvert$ is the best rank-$q$ trace error
when $a \ge b$. No hypothesis $\ell \le r$: the full-rank hypothesis forces it (for $r < \ell$ the
statement is vacuous, not false). [EpperlyWebber2026, Lemma 6.2]; there the limit as
$a \to \infty$ (an equality) for $a > b > 0$, here the upper bound at every $a, b \ge 0$.
Result: nystrom-two-eigenvalue-instance -/
theorem integral_nuclearNorm_fromBlocks_sub_nystrom_le_of_isLeftUnitarilyInvariant
    {s t : Type*} [Fintype s] [Fintype t] [DecidableEq s] [DecidableEq t]
    {ν' : Measure (Matrix (s ⊕ t) l ℝ)} [IsProbabilityMeasure ν'] [IsLeftUnitarilyInvariant ν']
    {Y : Ω → Matrix (s ⊕ t) l ℝ} (hY : HasLaw Y ν' μ)
    (hYr : ∀ᵐ ω ∂μ, Function.Injective (Y ω).mulVec) (hsl : Fintype.card s + 2 ≤ Fintype.card l)
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∫ ω, nuclearNorm (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (b • 1) -
        nystrom (Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (b • 1)) (Y ω)) ∂μ ≤
      rotationInvariantFactor (Fintype.card s + Fintype.card t) (Fintype.card l)
        (Fintype.card s) * (b * Fintype.card t) := by
  classical
  have := hY.isProbabilityMeasure_iff.2 inferInstance
  set D := Matrix.fromBlocks (a • (1 : Matrix s s ℝ)) 0 0 (b • (1 : Matrix t t ℝ))
  have hD : D.PosSemidef :=
    (Matrix.PosSemidef.one.smul ha).fromBlocks_zero₁₂_zero₂₁ (Matrix.PosSemidef.one.smul hb)
  have hΨ := hasLaw_polarFactor_of_isLeftUnitarilyInvariant hY hYr
  have hl : Fintype.card l ≤ Fintype.card (s ⊕ t) := by
    obtain ⟨ω, hω⟩ := hYr.exists
    exact (hasOrthonormalCols_polarFactor_iff.2 hω).card_le
  set W : Matrix s (s ⊕ t) ℝ := (selectionMatrix Sum.inl)ᴴ
  have hW : HasOrthonormalCols Wᴴ := by
    rw [Matrix.conjTranspose_conjTranspose]
    exact hasOrthonormalCols_selectionMatrix Sum.inl_injective
  have hWrank : W.rank = Fintype.card s := by
    rw [Matrix.rank_conjTranspose]
    exact (hasOrthonormalCols_selectionMatrix Sum.inl_injective).rank_eq
  have hWΨ : ∀ Ψ : Matrix (s ⊕ t) l ℝ, W * Ψ = Ψ.toRows₁ := fun Ψ => by
    rw [conjTranspose_selectionMatrix_mul]
    rfl
  have hpt : ∀ᵐ ω ∂μ, nuclearNorm (D - nystrom D (Y ω)) ≤
      b * frobNorm (pinv (W * polarFactor (Y ω))) ^ 2 +
        b * ((Fintype.card t : ℝ) - Fintype.card l) := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hΨ hl,
      ae_rank_mul_eq_min_of_hasLaw_haarFrame W hΨ] with ω hω hr
    rw [hD.nystrom_eq_of_range_eq (rangeProjector_inj.mp (rangeProjector_polarFactor (Y ω))).symm,
      hWΨ]
    refine hω.nuclearNorm_fromBlocks_sub_nystrom_le ?_ ha hb
    rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose, ← hWΨ, hr, hWrank,
      min_eq_left (by omega)]
  have hint : Integrable (fun ω => b * frobNorm (pinv (W * polarFactor (Y ω))) ^ 2 +
      b * ((Fintype.card t : ℝ) - Fintype.card l)) μ :=
    ((integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hΨ hl hW hsl).const_mul b).add
      (integrable_const _)
  refine (integral_mono_ae (hD.integrable_nuclearNorm_sub_nystrom hY.aemeasurable) hint
    hpt).trans (le_of_eq ?_)
  rw [integral_add ((integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hΨ hl hW
    hsl).const_mul b) (integrable_const _), integral_const_mul,
    integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hΨ hl hW hsl, integral_const,
    probReal_univ, one_smul, rotationInvariantFactor_def, Fintype.card_sum]
  have hsl' : (Fintype.card s : ℝ) + 2 ≤ Fintype.card l := by exact_mod_cast hsl
  have hl' : (Fintype.card l : ℝ) ≤ Fintype.card s + Fintype.card t := by
    rw [Fintype.card_sum] at hl
    exact_mod_cast hl
  have h1 : (Fintype.card l : ℝ) - Fintype.card s - 1 ≠ 0 := by linarith
  have h2 : ((Fintype.card s + Fintype.card t : ℕ) : ℝ) - Fintype.card s ≠ 0 := by
    push_cast; linarith
  push_cast at h2 ⊢
  field_simp
  ring

end NLAlib
