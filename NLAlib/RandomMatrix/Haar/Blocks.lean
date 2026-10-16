/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Basic.OrthonormalBasis
public import NLAlib.Matrix.Factorizations.Polar
public import NLAlib.RandomMatrix.Gaussian.InverseMoments.Frobenius
public import NLAlib.RandomMatrix.Gaussian.Moments
public import NLAlib.RandomMatrix.Haar.Transfer
public import NLAlib.RandomMatrix.Haar.Uniqueness

/-!
# Blocks of a Haar frame

Rows, corners and the Beta matrix of a Haar frame (`NLAlib.haarFrame`). For an $n \times k$ Haar
frame $\mathbf{Q}$ and a fixed $\mathbf{W}$ with $p$ orthonormal rows, $\mathbf{W}\mathbf{Q}$ is a
$p \times k$ Haar frame when $\mathbf{Q}$ has orthonormal rows
($\lvert n\rvert \le \lvert k\rvert$), and in general it has the law of the $p \times k$ corner
of a Haar orthogonal matrix, realised as $\mathbf{P}\mathbf{V}$ for a $p \times n$ Haar frame
$\mathbf{P}$ and any frame $\mathbf{V}$. The column block is
`NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame` (in `NLAlib.RandomMatrix.Haar.Uniqueness`), and the
polar factor of a wide matrix is
`NLAlib.polarFactor_eq_pinv_sqrt_mul`.

$\mathbf{W}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W}^{\mathsf{H}}$ is a Beta matrix (Epperly and
Webber's Definition 5.5); its inverse mean, in trace form, is
$\mathbb{E}\|(\mathbf{W}\mathbf{Q})^{+}\|_{\mathsf{F}}^2 = p\bigl(1 + (n-k)/(k-p-1)\bigr)$, computed
from the Gaussian inverse moments without the Beta law. With it and the coupled conjugation average
(`NLAlib.integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant`) the random
orthonormal sketching identity follows: for complementary frames $\mathbf{V}_1$ ($r$ columns) and
$\mathbf{V}_2$ and $r + 2 \le k \le n$,
$$\mathbb{E}\|(\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\mathbf{B}
\|_{\mathsf{F}}^2 = \frac{n-k}{n-r}\cdot\frac{r}{k-r-1}\,\|\mathbf{B}\|_{\mathsf{F}}^2\,,$$
packaged in the Haar projection factor <!-- value haarProjectionFactor d p q -->
$1 + (d - p)/(d - q) \cdot (q/(p - q - 1))$ (`NLAlib.haarProjectionFactor d p q`), the completion
factor of Haar sketch-and-solve. Real field, as the Haar frame. The moments
are here rather than in `NLAlib.RandomMatrix.Haar.Moments` because they are moments of the block
$\mathbf{W}\mathbf{Q}$, proved from its law and the Gaussian inverse moments. Design:
`docs/design/LowRank-S4.md` §3.2, §8 item 8; the sketching identity and the factor,
`docs/design/LowRank-S6.md` §3.1, §8 items 3 and 6.

## Main results

* `NLAlib.hasLaw_const_mul_of_hasLaw_haarFrame`: row blocks of a Haar frame with orthonormal rows.
* `NLAlib.hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols`: corner blocks.
* `NLAlib.integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`, with its integrability
  `NLAlib.integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`: the inverse mean of the Beta
  matrix, trace form.
* `NLAlib.haarProjectionFactor`, with `NLAlib.one_le_haarProjectionFactor` and the monotonicity
  `NLAlib.haarProjectionFactor_le_haarProjectionFactor`.
* `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame`, with its integrability
  `NLAlib.integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame`: the random orthonormal
  sketching identity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {n k p : Type*} [Fintype n]
  [Fintype k] [Fintype p] {X : Ω → Matrix n k ℝ}

/-- **Row blocks of a Haar frame with orthonormal rows**: for an $n \times k$ Haar frame
$\mathbf{Q}$ with $\lvert n\rvert \le \lvert k\rvert$ (orthonormal rows; a Haar orthogonal matrix
for $n = k$) and a fixed $\mathbf{W}$ with orthonormal rows, $\mathbf{W}\mathbf{Q}$ is a
$p \times k$ Haar frame. The row twin of `NLAlib.hasLaw_mul_const_of_hasLaw_haarFrame`.
[Meckes2019, Ch. 1]; [EpperlyWebber2026, p. 14], there the first rows of a Haar unitary.
Result: haar-frame-block-law -/
theorem hasLaw_const_mul_of_hasLaw_haarFrame [DecidableEq k] [DecidableEq p]
    (hX : HasLaw X (haarFrame n k) μ) (hnk : Fintype.card n ≤ Fintype.card k)
    {W : Matrix p n ℝ} (hW : HasOrthonormalCols Wᴴ) :
    HasLaw (fun ω => W * X ω) (haarFrame p k) μ := by
  classical
  have h := hasLaw_conjTranspose_of_hasLaw_haarFrame
    (hasLaw_mul_const_of_hasLaw_haarFrame (hasLaw_conjTranspose_of_hasLaw_haarFrame hX) hnk hW)
  refine h.congr (ae_of_all _ fun ω => ?_)
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- **Corner blocks of a Haar frame**: for an $n \times k$ Haar frame $\mathbf{Q}$, a fixed
$\mathbf{W}$ with orthonormal rows and any fixed frame $\mathbf{V}$ ($n \times k$, orthonormal
columns), $\mathbf{W}\mathbf{Q}$ has the law of $\mathbf{P}\mathbf{V}$ for a $p \times n$ Haar frame
$\mathbf{P}$ (orthonormal rows), that is of $(\mathbf{G}\mathbf{G}^{\mathsf{H}})^{-1/2}\mathbf{G}
\mathbf{V}$ for a standard Gaussian $\mathbf{G}$. The law does not depend on $\mathbf{V}$: it is the
law of the $p \times k$ corner of a Haar orthogonal matrix, which any frame $\mathbf{V}$ realises;
$\mathbf{V}$ forces $\lvert k\rvert \le \lvert n\rvert$. [EpperlyWebber2026, p. 14].
Result: haar-frame-block-law -/
theorem hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols [DecidableEq n]
    [DecidableEq k] [DecidableEq p] (hX : HasLaw X (haarFrame n k) μ) {W : Matrix p n ℝ}
    (hW : HasOrthonormalCols Wᴴ) {V : Matrix n k ℝ} (hV : HasOrthonormalCols V) :
    HasLaw (fun ω => W * X ω) ((haarFrame p n).map (· * V)) μ := by
  have hV' : (haarFrame n n).map (· * V) = haarFrame n k :=
    (hasLaw_mul_const_of_hasLaw_haarFrame (HasLaw.id (μ := haarFrame n n)) le_rfl hV).map_eq
  have hW' : (haarFrame n n).map (W * ·) = haarFrame p n :=
    (hasLaw_const_mul_of_hasLaw_haarFrame (HasLaw.id (μ := haarFrame n n)) le_rfl hW).map_eq
  have hmW : Measurable fun x : Matrix n k ℝ => W * x := measurable_const.matrix_mul measurable_id
  have hmW' : Measurable fun x : Matrix n n ℝ => W * x := measurable_const.matrix_mul measurable_id
  have hmV : Measurable fun x : Matrix n n ℝ => x * V := measurable_id.matrix_mul measurable_const
  have hmV' : Measurable fun x : Matrix p n ℝ => x * V := measurable_id.matrix_mul measurable_const
  refine HasLaw.fun_comp (Y := (W * ·)) ⟨hmW.aemeasurable, ?_⟩ hX
  rw [← hV', Measure.map_map hmW hmV, ← hW', Measure.map_map hmV' hmW']
  congr 1
  funext x
  simp only [Function.comp, Matrix.mul_assoc]


/-- A frame $\mathbf{V}$ ($n \times k$, $k \le n$) with an orthogonal complement $\mathbf{V}'$. -/
private theorem exists_hasOrthonormalCols_compl [DecidableEq n] [DecidableEq k]
    (hkn : Fintype.card k ≤ Fintype.card n) :
    ∃ (V : Matrix n k ℝ) (V' : Matrix n (Fin (Fintype.card n - Fintype.card k)) ℝ),
      HasOrthonormalCols V ∧ HasOrthonormalCols V' ∧ Vᴴ * V' = 0 ∧ V * Vᴴ + V' * V'ᴴ = 1 := by
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hkn
  have hV : HasOrthonormalCols (selectionMatrix e : Matrix n k ℝ) :=
    hasOrthonormalCols_selectionMatrix e.injective
  have hc : Fintype.card k + Fintype.card (Fin (Fintype.card n - Fintype.card k)) =
      Fintype.card n := by
    rw [Fintype.card_fin]; omega
  obtain ⟨V', hV'⟩ := hV.exists_fromCols hc
  obtain ⟨-, h2, h3⟩ := hasOrthonormalCols_fromCols_iff.mp hV'
  exact ⟨_, V', hV, h2, h3, hV'.mul_conjTranspose_add_mul_conjTranspose hc⟩

/-- The squared Frobenius norm of the pseudoinverse of $\operatorname{polar}(\mathbf{G})\mathbf{V}$
through the blocks $\mathbf{K} = \mathbf{G}\mathbf{V}$, $\mathbf{L} = \mathbf{G}\mathbf{V}'$, when
$\mathbf{K}$ has full row rank. -/
private theorem frobNorm_pinv_polarFactor_mul_sq [DecidableEq n] {d : Type*} [Fintype d]
    [DecidableEq d] {V : Matrix n k ℝ} {V' : Matrix n d ℝ} (hVV : V * Vᴴ + V' * V'ᴴ = 1)
    {G : Matrix p n ℝ} (hK : Function.Injective (G * V)ᴴ.mulVec) :
    frobNorm (pinv (polarFactor G * V)) ^ 2 =
      Fintype.card p + frobNorm (pinv (G * V) * (G * V') * (1 : Matrix d d ℝ)) ^ 2 := by
  classical
  set K := G * V with hKdef
  set L := G * V' with hLdef
  have hGG : G * Gᴴ = K * Kᴴ + L * Lᴴ := by
    have e : G * Gᴴ = G * (V * Vᴴ + V' * V'ᴴ) * Gᴴ := by rw [hVV, Matrix.mul_one]
    rw [e]
    simp only [K, L, Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  have hGinj : Function.Injective Gᴴ.mulVec := fun x y hxy => hK (by
    simp only [K, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec, hxy])
  clear_value K L
  have hPD : (G * Gᴴ).PosDef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using
      posDef_conjTranspose_mul_self_iff.mpr hGinj
  set S := CFC.sqrt (G * Gᴴ)
  have hSu : IsUnit S := hPD.isUnit_sqrt
  have hSdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).mp hSu
  have hSh : Sᴴ = S := (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian.eq
  have hSS : S * S = G * Gᴴ := CFC.sqrt_mul_sqrt_self _ hPD.posSemidef.nonneg
  have hX : (K * Kᴴ).PosDef := by
    simpa only [Matrix.conjTranspose_conjTranspose] using posDef_conjTranspose_mul_self_iff.mpr hK
  have hXdet : IsUnit (K * Kᴴ).det := (Matrix.isUnit_iff_isUnit_det _).mp hX.isUnit
  have hXh : (K * Kᴴ)⁻¹ᴴ = (K * Kᴴ)⁻¹ := by
    rw [Matrix.conjTranspose_nonsing_inv, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hpol : polarFactor G * V = S⁻¹ * K := by
    rw [polarFactor_eq_pinv_sqrt_mul, pinv_of_isUnit hSu, Matrix.mul_assoc, hKdef]
  have hSih : (S⁻¹)ᴴ = S⁻¹ := by rw [Matrix.conjTranspose_nonsing_inv, hSh]
  have hYinj : Function.Injective (S⁻¹ * K)ᴴ.mulVec := by
    rw [Matrix.conjTranspose_mul, hSih]
    have e : (Kᴴ * S⁻¹).mulVec = Kᴴ.mulVec ∘ (S⁻¹).mulVec := by
      funext x
      simp only [Function.comp, Matrix.mulVec_mulVec]
    rw [e]
    exact hK.comp (Matrix.mulVec_injective_of_isUnit (Matrix.isUnit_nonsing_inv_iff.mpr hSu))
  rw [hpol, frobNorm_pinv_sq_eq_re_trace_inv_of_injective_conjTranspose hYinj]
  rw [Matrix.mul_one]
  rw [frobNorm_sq_eq_re_trace, pinv_eq_conjTranspose_mul_inv hK]
  have e1 : (S⁻¹ * K * (S⁻¹ * K)ᴴ)⁻¹ = S * (K * Kᴴ)⁻¹ * S := by
    rw [Matrix.conjTranspose_mul, hSih]
    rw [show S⁻¹ * K * (Kᴴ * S⁻¹) = S⁻¹ * (K * Kᴴ) * S⁻¹ by simp only [Matrix.mul_assoc]]
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hSdet,
      Matrix.mul_assoc]
  have e2 : (Kᴴ * (K * Kᴴ)⁻¹ * L)ᴴ * (Kᴴ * (K * Kᴴ)⁻¹ * L) = Lᴴ * (K * Kᴴ)⁻¹ * L := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hXh, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc K Kᴴ, Matrix.mul_nonsing_inv_cancel_left _ _ hXdet]
  have e3 : (S * (K * Kᴴ)⁻¹ * S).trace = Fintype.card p + ((K * Kᴴ)⁻¹ * (L * Lᴴ)).trace := by
    rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.trace_mul_comm, hSS, hGG,
      Matrix.mul_add, Matrix.nonsing_inv_mul _ hXdet, Matrix.trace_add, Matrix.trace_one]
  have e4 : (Lᴴ * (K * Kᴴ)⁻¹ * L).trace = ((K * Kᴴ)⁻¹ * (L * Lᴴ)).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc]
  rw [e1, e2, e3, e4, map_add, RCLike.natCast_re]

/-- Almost surely in the Gaussian picture, the identity of
`frobNorm_pinv_polarFactor_mul_sq` holds ($\mathbf{G}\mathbf{V}$ has full row rank). -/
private theorem ae_frobNorm_pinv_polarFactor_mul_sq [DecidableEq n] [DecidableEq k]
    {d : Type*} [Fintype d] [DecidableEq d] {V : Matrix n k ℝ} {V' : Matrix n d ℝ}
    (hV : HasOrthonormalCols V) (hVV : V * Vᴴ + V' * V'ᴴ = 1)
    (hpk : Fintype.card p ≤ Fintype.card k) :
    ∀ᵐ G ∂gaussianMatrix p n, frobNorm (pinv (polarFactor G * V)) ^ 2 =
      Fintype.card p + frobNorm (pinv (G * V) * (G * V') * (1 : Matrix d d ℝ)) ^ 2 := by
  have hK := hasLaw_mul_const_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix p n)) hV
  filter_upwards [ae_rank_eq_min_of_hasLaw_gaussianMatrix hK] with G hG
  have hinj : Function.Injective (G * V)ᴴ.mulVec := by
    rw [mulVec_injective_iff_rank_eq, Matrix.rank_conjTranspose]
    exact hG.trans (min_eq_left hpk)
  exact frobNorm_pinv_polarFactor_mul_sq hVV hinj

omit [Fintype k] in
/-- The blocks $\mathbf{G}\mathbf{V}$ and $\mathbf{G}\mathbf{V}'$ of a standard Gaussian matrix
are independent. -/
private theorem indepFun_mul_const_mul_const [Finite k] [DecidableEq k] {d : Type*} [Finite d]
    [DecidableEq d]
    {V : Matrix n k ℝ} {V' : Matrix n d ℝ} (hV : HasOrthonormalCols V)
    (hV' : HasOrthonormalCols V') (h₁₂ : Vᴴ * V' = 0) :
    IndepFun (fun G : Matrix p n ℝ => G * V) (fun G => G * V') (gaussianMatrix p n) := by
  have hT := hasLaw_conjTranspose_of_hasLaw_gaussianMatrix (HasLaw.id (μ := gaussianMatrix p n))
  have h := (indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hT hV hV' h₁₂).comp
    (continuous_id.matrix_conjTranspose.measurable (α := Matrix k p ℝ))
    (continuous_id.matrix_conjTranspose.measurable (α := Matrix d p ℝ))
  convert h using 1 <;> funext G <;>
    simp only [Function.comp, id, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- $\|(\mathbf{W}\mathbf{Q})^{+}\|_{\mathsf{F}}^2$ is integrable for an $n \times k$ Haar frame
$\mathbf{Q}$ with $\lvert k\rvert \le \lvert n\rvert$, $\mathbf{W}$ with $p$ orthonormal rows and
$\lvert p\rvert + 2 \le \lvert k\rvert$. -/
theorem integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame [DecidableEq k] [DecidableEq p]
    (hX : HasLaw X (haarFrame n k) μ)
    (hkn : Fintype.card k ≤ Fintype.card n) {W : Matrix p n ℝ} (hW : HasOrthonormalCols Wᴴ)
    (hpk : Fintype.card p + 2 ≤ Fintype.card k) :
    Integrable (fun ω => frobNorm (pinv (W * X ω)) ^ 2) μ := by
  classical
  obtain ⟨V, V', hV, hV', h₁₂, hVV⟩ := exists_hasOrthonormalCols_compl hkn
  have hf : Measurable fun Y : Matrix p k ℝ => frobNorm (pinv Y) ^ 2 :=
    (measurable_frobNorm.comp measurable_pinv).pow_const 2
  have hZ : HasLaw (fun G : Matrix p n ℝ => polarFactor G * V) ((haarFrame p n).map (· * V))
      (gaussianMatrix p n) :=
    HasLaw.fun_comp (Y := (· * V)) ⟨(measurable_id.matrix_mul measurable_const).aemeasurable, rfl⟩
      (hasLaw_polarFactor_of_hasLaw_gaussianMatrix HasLaw.id)
  have hlaw := hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols hX hW hV
  have hK : HasLaw (fun G : Matrix p n ℝ => G * V) (gaussianMatrix p k) (gaussianMatrix p n) :=
    hasLaw_mul_const_of_hasLaw_gaussianMatrix HasLaw.id hV
  have hL : HasLaw (fun G : Matrix p n ℝ => G * V')
      (gaussianMatrix p (Fin (Fintype.card n - Fintype.card k))) (gaussianMatrix p n) :=
    hasLaw_mul_const_of_hasLaw_gaussianMatrix HasLaw.id hV'
  have hint : Integrable (fun G : Matrix p n ℝ =>
      frobNorm (pinv (G * V) * (G * V') *
        (1 : Matrix (Fin (Fintype.card n - Fintype.card k))
          (Fin (Fintype.card n - Fintype.card k)) ℝ)) ^ 2) (gaussianMatrix p n) :=
    (integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun hL hK.aemeasurable
      (indepFun_mul_const_mul_const hV hV' h₁₂) (S := pinv)
      (T := fun _ => (1 : Matrix (Fin (Fintype.card n - Fintype.card k))
          (Fin (Fintype.card n - Fintype.card k)) ℝ))
      measurable_pinv measurable_const).2
      ((integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hK hpk).mul_const _)
  have h1 : Integrable (fun G : Matrix p n ℝ => frobNorm (pinv (polarFactor G * V)) ^ 2)
      (gaussianMatrix p n) :=
    ((integrable_const (Fintype.card p : ℝ)).add hint).congr
      ((ae_frobNorm_pinv_polarFactor_mul_sq (p := p) hV hVV (by omega)).mono fun _ h => h.symm)
  have h2 : Integrable (fun Y : Matrix p k ℝ => frobNorm (pinv Y) ^ 2)
      ((haarFrame p n).map (· * V)) := by
    rw [← hZ.map_eq]
    exact (integrable_map_measure (by rw [hZ.map_eq]; exact hf.aestronglyMeasurable)
      hZ.aemeasurable).2 h1
  rw [← hlaw.map_eq] at h2
  exact (integrable_map_measure (by rw [hlaw.map_eq]; exact hf.aestronglyMeasurable)
    hlaw.aemeasurable).1 h2

/-- **The inverse mean of a Beta matrix, trace form**: for an $n \times k$ Haar frame
$\mathbf{Q}$, $\mathbf{W}$ with $p$ orthonormal rows and $p + 2 \le k \le n$,
$$\mathbb{E}\|(\mathbf{W}\mathbf{Q})^{+}\|_{\mathsf{F}}^2 =
\mathbb{E}\operatorname{tr}\bigl((\mathbf{W}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}
\mathbf{W}^{\mathsf{H}})^{-1}\bigr) = p\Bigl(1 + \frac{n-k}{k-p-1}\Bigr).$$
$\mathbf{W}\mathbf{Q}\mathbf{Q}^{\mathsf{H}}\mathbf{W}^{\mathsf{H}}$ is a Beta matrix; its law is
not used. At $n = k$ the value is $p$ ($\mathbf{W}\mathbf{Q}$ has orthonormal rows). The proof
writes $\mathbf{W}\mathbf{Q}$ as $\operatorname{polar}(\mathbf{G})\mathbf{V}$
(`NLAlib.hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols`) and the trace as
$p + \|\mathbf{K}^{+}\mathbf{L}\|_{\mathsf{F}}^2$ for the independent Gaussian blocks
$\mathbf{K} = \mathbf{G}\mathbf{V}$, $\mathbf{L} = \mathbf{G}\mathbf{V}'$.
[EpperlyWebber2026, Proposition 5.6]; there the matrix $\mathbb{E}\mathbf{X}^{-1}$ over
$\mathbb{R}$ and $\mathbb{C}$, here its trace over $\mathbb{R}$, the only part their Proposition 5.7
and Lemma 6.2 use.
Result: beta-matrix-inverse-mean -/
theorem integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame [DecidableEq k] [DecidableEq p]
    (hX : HasLaw X (haarFrame n k) μ)
    (hkn : Fintype.card k ≤ Fintype.card n) {W : Matrix p n ℝ} (hW : HasOrthonormalCols Wᴴ)
    (hpk : Fintype.card p + 2 ≤ Fintype.card k) :
    ∫ ω, frobNorm (pinv (W * X ω)) ^ 2 ∂μ =
      Fintype.card p * (1 + ((Fintype.card n : ℝ) - Fintype.card k) /
        ((Fintype.card k : ℝ) - Fintype.card p - 1)) := by
  classical
  obtain ⟨V, V', hV, hV', h₁₂, hVV⟩ := exists_hasOrthonormalCols_compl hkn
  have hf : Measurable fun Y : Matrix p k ℝ => frobNorm (pinv Y) ^ 2 :=
    (measurable_frobNorm.comp measurable_pinv).pow_const 2
  have hZ : HasLaw (fun G : Matrix p n ℝ => polarFactor G * V) ((haarFrame p n).map (· * V))
      (gaussianMatrix p n) :=
    HasLaw.fun_comp (Y := (· * V)) ⟨(measurable_id.matrix_mul measurable_const).aemeasurable, rfl⟩
      (hasLaw_polarFactor_of_hasLaw_gaussianMatrix HasLaw.id)
  have hlaw := hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols hX hW hV
  have hK : HasLaw (fun G : Matrix p n ℝ => G * V) (gaussianMatrix p k) (gaussianMatrix p n) :=
    hasLaw_mul_const_of_hasLaw_gaussianMatrix HasLaw.id hV
  have hL : HasLaw (fun G : Matrix p n ℝ => G * V')
      (gaussianMatrix p (Fin (Fintype.card n - Fintype.card k))) (gaussianMatrix p n) :=
    hasLaw_mul_const_of_hasLaw_gaussianMatrix HasLaw.id hV'
  have hind := indepFun_mul_const_mul_const (p := p) hV hV' h₁₂
  have hint : Integrable (fun G : Matrix p n ℝ =>
      frobNorm (pinv (G * V) * (G * V') *
        (1 : Matrix (Fin (Fintype.card n - Fintype.card k))
          (Fin (Fintype.card n - Fintype.card k)) ℝ)) ^ 2) (gaussianMatrix p n) :=
    (integrable_frobNorm_mul_mul_sq_iff_of_hasLaw_gaussianMatrix_of_indepFun hL hK.aemeasurable
      hind (S := pinv)
      (T := fun _ => (1 : Matrix (Fin (Fintype.card n - Fintype.card k))
          (Fin (Fintype.card n - Fintype.card k)) ℝ))
      measurable_pinv measurable_const).2
      ((integrable_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hK hpk).mul_const _)
  have hmom := integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix_of_indepFun hL
    hK.aemeasurable hind (S := pinv)
    (T := fun _ => (1 : Matrix (Fin (Fintype.card n - Fintype.card k))
          (Fin (Fintype.card n - Fintype.card k)) ℝ))
    measurable_pinv measurable_const
  have h1 : frobNorm (1 : Matrix (Fin (Fintype.card n - Fintype.card k))
          (Fin (Fintype.card n - Fintype.card k)) ℝ) ^ 2 =
      ((Fintype.card n : ℝ) - Fintype.card k) := by
    rw [frobNorm_sq_eq_re_trace, Matrix.conjTranspose_one, Matrix.mul_one, Matrix.trace_one,
      Fintype.card_fin, RCLike.re_to_real, Nat.cast_sub hkn]
  have e0 : ∫ ω, frobNorm (pinv (W * X ω)) ^ 2 ∂μ =
      ∫ G, frobNorm (pinv (polarFactor G * V)) ^ 2 ∂gaussianMatrix p n :=
    (hlaw.integral_comp hf.aestronglyMeasurable).trans
      (hZ.integral_comp hf.aestronglyMeasurable).symm
  rw [e0, integral_congr_ae (ae_frobNorm_pinv_polarFactor_mul_sq (p := p) hV hVV (by omega)),
    integral_add (integrable_const _) hint, integral_const, hmom, integral_mul_const,
    integral_frobNorm_pinv_sq_of_hasLaw_gaussianMatrix hK hpk, h1]
  have hd : (0 : ℝ) < (Fintype.card k : ℝ) - Fintype.card p - 1 := by
    have : (Fintype.card p : ℝ) + 2 ≤ Fintype.card k := by exact_mod_cast hpk
    linarith
  simp only [probReal_univ, one_smul]
  field_simp

end NLAlib

namespace NLAlib

/-! ### The Haar projection factor -/

/-- **The Haar projection factor** <!-- value haarProjectionFactor d p q -->
$1 + (d - p)/(d - q) \cdot (q/(p - q - 1))$ (casts to $\mathbb{R}$): the factor by which a Haar
sketch of size $p$ in ambient dimension $d$ inflates the least-squares error of a basis of rank
$q$, Epperly and Webber's random orthonormal constant, and their
$1 + \gamma\frac{\ell}{p - \ell - 1}$ with $\gamma = \frac{d - p}{d - \ell}$ at $q = \ell$. Junk for
$p \le q + 1$ or $d \le q$ (Lean's $x/0 = 0$, signs); theorems carry `q + 2 ≤ p` and `p ≤ d`. A
plain definition, because its body is the source's formula.
[EpperlyWebber2026, Theorem 2.1]. -/
noncomputable def haarProjectionFactor (d p q : ℕ) : ℝ :=
  1 + ((d : ℝ) - p) / ((d : ℝ) - q) * ((q : ℝ) / ((p : ℝ) - q - 1))

/-- The body of `haarProjectionFactor`, <!-- value haarProjectionFactor d p q -->
$1 + (d - p)/(d - q) \cdot (q/(p - q - 1))$, as a simp lemma. -/
@[simp]
theorem haarProjectionFactor_def (d p q : ℕ) :
    haarProjectionFactor d p q =
      1 + ((d : ℝ) - p) / ((d : ℝ) - q) * ((q : ℝ) / ((p : ℝ) - q - 1)) :=
  rfl

/-- The Haar projection factor is at least $1$ for $q + 2 \le p \le d$. -/
theorem one_le_haarProjectionFactor {d p q : ℕ} (hqp : q + 2 ≤ p) (hpd : p ≤ d) :
    1 ≤ haarProjectionFactor d p q := by
  have hqp' : (q : ℝ) + 2 ≤ p := by exact_mod_cast hqp
  have hpd' : (p : ℝ) ≤ d := by exact_mod_cast hpd
  rw [haarProjectionFactor_def, le_add_iff_nonneg_right]
  exact mul_nonneg (div_nonneg (by linarith) (by linarith))
    (div_nonneg (Nat.cast_nonneg q) (by linarith))

/-- The Haar projection factor is monotone in the rank: the factor at the actual rank is at most
the factor at any larger rank $q'$ with $q' + 2 \le p \le d$. -/
theorem haarProjectionFactor_le_haarProjectionFactor {d p q q' : ℕ} (hq : q ≤ q')
    (hq' : q' + 2 ≤ p) (hpd : p ≤ d) :
    haarProjectionFactor d p q ≤ haarProjectionFactor d p q' := by
  have hq1 : (q : ℝ) ≤ q' := by exact_mod_cast hq
  have hq2 : (q' : ℝ) + 2 ≤ p := by exact_mod_cast hq'
  have hpd' : (p : ℝ) ≤ d := by exact_mod_cast hpd
  simp only [haarProjectionFactor_def, add_le_add_iff_left]
  exact mul_le_mul (div_le_div_of_nonneg_left (by linarith) (by linarith) (by linarith))
    (div_le_div₀ (Nat.cast_nonneg _) hq1 (by linarith) (by linarith))
    (div_nonneg (Nat.cast_nonneg _) (by linarith)) (div_nonneg (by linarith) (by linarith))

/-! ### The random orthonormal sketching identity -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {m p r s a : Type*} [Fintype m]
  [Fintype p] [Fintype r] [Fintype s] [Fintype a] {Q : Ω → Matrix m p ℝ}

/-- The middle factor $F(\mathbf{x}) = (\mathbf{x}^{\mathsf{H}})^{+\mathsf{H}}
(\mathbf{x}^{\mathsf{H}})^{+}$ of the sketching identity. -/
private noncomputable def middle (x : Matrix r p ℝ) : Matrix p p ℝ :=
  (pinv xᴴ)ᴴ * pinv xᴴ

omit [Fintype r] in
private theorem measurable_middle [Fintype r] : Measurable (middle (r := r) (p := p)) := by
  have hT : Measurable fun x : Matrix r p ℝ => xᴴ := continuous_id.matrix_conjTranspose.measurable
  have hP : Measurable fun x : Matrix r p ℝ => pinv xᴴ := measurable_pinv.comp hT
  exact (continuous_id.matrix_conjTranspose.measurable.comp hP).matrix_mul hP

/-- The squared norm in the sketching identity as a trace against the conjugated middle factor. -/
private theorem frobNorm_pinv_mul_mul_sq_eq_trace (Q₀ : Matrix m p ℝ) (V₁ : Matrix m r ℝ)
    (V₂ : Matrix m s ℝ) (B : Matrix s a ℝ) :
    frobNorm (pinv (Q₀ᴴ * V₁) * (Q₀ᴴ * V₂) * B) ^ 2 =
      (V₂ᴴ * Q₀ * middle (V₁ᴴ * Q₀) * (V₂ᴴ * Q₀)ᴴ * (B * Bᴴ)).trace := by
  have h1 : (V₁ᴴ * Q₀)ᴴ = Q₀ᴴ * V₁ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have h2 : (V₂ᴴ * Q₀)ᴴ = Q₀ᴴ * V₂ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [frobNorm_sq_eq_re_trace, RCLike.re_to_real]
  have e : (pinv (Q₀ᴴ * V₁) * (Q₀ᴴ * V₂) * B)ᴴ * (pinv (Q₀ᴴ * V₁) * (Q₀ᴴ * V₂) * B) =
      Bᴴ * (V₂ᴴ * Q₀ * middle (V₁ᴴ * Q₀) * (V₂ᴴ * Q₀)ᴴ * B) := by
    rw [middle, h1, h2]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc]

/-- The two traces of the middle factor, for $\mathbf{x}^{\mathsf{H}}$ of full column rank. -/
private theorem trace_middle_mul_eq [DecidableEq r] {x : Matrix r p ℝ}
    (hL : pinv xᴴ * xᴴ = 1) : (middle x * (xᴴ * x)).trace = Fintype.card r := by
  rw [middle, show (pinv xᴴ)ᴴ * pinv xᴴ * (xᴴ * x) = (pinv xᴴ)ᴴ * (pinv xᴴ * xᴴ) * x by
      simp only [Matrix.mul_assoc], hL, Matrix.mul_one, Matrix.trace_mul_comm,
    show x * (pinv xᴴ)ᴴ = (pinv xᴴ * xᴴ)ᴴ by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], hL,
    Matrix.conjTranspose_one, Matrix.trace_one]

private theorem trace_middle (x : Matrix r p ℝ) : (middle x).trace = frobNorm (pinv x) ^ 2 := by
  rw [middle, pinv_conjTranspose, Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm,
    frobNorm_sq_eq_re_trace, RCLike.re_to_real]

/-- The trace of the conjugated middle factor, on the event that $\mathbf{Q}$ has orthonormal
columns and $\mathbf{V}_1^{\mathsf{H}}\mathbf{Q}$ has full row rank. -/
private theorem trace_conj_middle_eq [DecidableEq m] [DecidableEq p]
    {Q₀ : Matrix m p ℝ} (hQ₀ : HasOrthonormalCols Q₀) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hVV : V₁ * V₁ᴴ + V₂ * V₂ᴴ = 1) (hinj : Function.Injective (Q₀ᴴ * V₁).mulVec) :
    (V₂ᴴ * Q₀ * middle (V₁ᴴ * Q₀) * (V₂ᴴ * Q₀)ᴴ).trace =
      frobNorm (pinv (V₁ᴴ * Q₀)) ^ 2 - Fintype.card r := by
  classical
  have h1 : (V₁ᴴ * Q₀)ᴴ = Q₀ᴴ * V₁ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hL : pinv (V₁ᴴ * Q₀)ᴴ * (V₁ᴴ * Q₀)ᴴ = 1 := by
    rw [h1]; exact pinv_mul_self_of_injective hinj
  have hG : (V₂ᴴ * Q₀)ᴴ * (V₂ᴴ * Q₀) = 1 - (V₁ᴴ * Q₀)ᴴ * (V₁ᴴ * Q₀) := by
    have e : Q₀ᴴ * (V₁ * V₁ᴴ + V₂ * V₂ᴴ) * Q₀ = 1 := by
      rw [hVV, Matrix.mul_one, hQ₀.conjTranspose_mul_self]
    rw [eq_sub_iff_add_eq, ← e]
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_assoc]
    abel
  rw [Matrix.mul_assoc, Matrix.trace_mul_comm, Matrix.mul_assoc, hG, Matrix.mul_sub,
    Matrix.mul_one, Matrix.trace_sub, trace_middle, trace_middle_mul_eq hL]

/-- Almost surely the squared norm is at most $\|(\mathbf{V}_1^{\mathsf{H}}\mathbf{Q})^{+}
\|_{\mathsf{F}}^2\|\mathbf{B}\|_2^2$, since $\|\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\|_2 \le 1$. -/
private theorem ae_frobNorm_pinv_mul_mul_sq_le [DecidableEq p] (hQ : HasLaw Q (haarFrame m p) μ)
    {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ} [DecidableEq s] (hV₂ : HasOrthonormalCols V₂)
    (B : Matrix s a ℝ) :
    ∀ᵐ ω ∂μ, frobNorm (pinv ((Q ω)ᴴ * V₁) * ((Q ω)ᴴ * V₂) * B) ^ 2 ≤
      frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 * specNorm B ^ 2 := by
  filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ] with ω hω
  have h1 : frobNorm (pinv ((Q ω)ᴴ * V₁)) = frobNorm (pinv (V₁ᴴ * Q ω)) := by
    rw [show (Q ω)ᴴ * V₁ = (V₁ᴴ * Q ω)ᴴ by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], pinv_conjTranspose,
      frobNorm_conjTranspose]
  have h2 : specNorm ((Q ω)ᴴ * V₂) ≤ 1 := by
    rw [← specNorm_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    exact (hV₂.specNorm_conjTranspose_mul_le _).trans hω
  have h3 : frobNorm (pinv ((Q ω)ᴴ * V₁) * ((Q ω)ᴴ * V₂) * B) ≤
      frobNorm (pinv (V₁ᴴ * Q ω)) * specNorm B := by
    refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans
      (mul_le_mul_of_nonneg_right ?_ (specNorm_nonneg _))
    refine (frobNorm_mul_le_frobNorm_mul_specNorm _ _).trans ?_
    rw [h1]
    exact mul_le_of_le_one_right (frobNorm_nonneg _) h2
  rw [← mul_pow]
  exact pow_le_pow_left₀ (frobNorm_nonneg _) h3 2

/-- The integrand of the sketching identity is measurable in the frame. -/
private theorem measurable_frobNorm_pinv_mul_mul_sq (V₁ : Matrix m r ℝ) (V₂ : Matrix m s ℝ)
    (B : Matrix s a ℝ) :
    Measurable fun Q₀ : Matrix m p ℝ => frobNorm (pinv (Q₀ᴴ * V₁) * (Q₀ᴴ * V₂) * B) ^ 2 := by
  have hT : Measurable fun Q₀ : Matrix m p ℝ => Q₀ᴴ :=
    continuous_id.matrix_conjTranspose.measurable
  exact (measurable_frobNorm.comp (((measurable_pinv.comp
    (hT.matrix_mul measurable_const)).matrix_mul (hT.matrix_mul measurable_const)).matrix_mul
      measurable_const)).pow_const 2

/-- The squared norm of the Haar block
$(\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\mathbf{B}$ is
integrable, for an $m \times p$ Haar frame $\mathbf{Q}$, a frame $\mathbf{V}_1$ with
$r + 2 \le p \le m$ and any $\mathbf{V}_2$ with orthonormal columns. -/
theorem integrable_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame [DecidableEq p] [DecidableEq r]
    [DecidableEq s] (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) (B : Matrix s a ℝ) :
    Integrable (fun ω => frobNorm (pinv ((Q ω)ᴴ * V₁) * ((Q ω)ᴴ * V₂) * B) ^ 2) μ := by
  have hW : HasOrthonormalCols (V₁ᴴ)ᴴ := by rwa [Matrix.conjTranspose_conjTranspose]
  have hint := integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hQ hpm hW hrp
  exact Integrable.mono' (hint.mul_const (specNorm B ^ 2))
    ((measurable_frobNorm_pinv_mul_mul_sq V₁ V₂ B).comp_aemeasurable
      hQ.aemeasurable).aestronglyMeasurable
    ((ae_frobNorm_pinv_mul_mul_sq_le hQ hV₂ B).mono fun ω h => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]; exact h)

open scoped Matrix.Norms.L2Operator in
/-- **The random orthonormal sketching identity**: for an $m \times p$ Haar frame $\mathbf{Q}$,
$p \le m$, complementary frames $\mathbf{V}_1$ ($r$ columns) and $\mathbf{V}_2$
($\mathbf{V}_1^{\mathsf{H}}\mathbf{V}_2 = \mathbf{0}$, $r + \lvert s\rvert = m$), $r + 2 \le p$ and
every $\mathbf{B}$,
$$\mathbb{E}\|(\mathbf{Q}^{\mathsf{H}}\mathbf{V}_1)^{+}\mathbf{Q}^{\mathsf{H}}\mathbf{V}_2\mathbf{B}
\|_{\mathsf{F}}^2 = \frac{m-p}{m-r}\cdot\frac{r}{p-r-1}\,\|\mathbf{B}\|_{\mathsf{F}}^2\,,$$
the Haar twin of `NLAlib.integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_gaussianMatrix`, smaller than
the Gaussian value $\frac{r}{p-r-1}$ by the factor $\frac{m-p}{m-r}$. Unlike the Gaussian case the
frames must be complementary: the proof uses
$\mathbf{\Omega}_1^{\mathsf{H}}\mathbf{\Omega}_1 + \mathbf{\Omega}_2^{\mathsf{H}}\mathbf{\Omega}_2 =
\mathbf{Q}^{\mathsf{H}}\mathbf{Q} = \mathbf{I}$ for the blocks
$\mathbf{\Omega}_i = \mathbf{V}_i^{\mathsf{H}}\mathbf{Q}$.
[EpperlyWebber2026, Proposition 5.7]; there an inequality for general $\mathbf{R}$, equality at
$\mathbf{R} = \mathbf{I}$, over $\mathbb{R}$ and $\mathbb{C}$; here the real case at
$\mathbf{R} = \mathbf{I}$.
Result: haar-sketching-identity -/
theorem integral_frobNorm_pinv_mul_mul_sq_of_hasLaw_haarFrame [DecidableEq p] [DecidableEq r]
    [DecidableEq s] (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) {V₁ : Matrix m r ℝ} {V₂ : Matrix m s ℝ}
    (hV₁ : HasOrthonormalCols V₁) (hV₂ : HasOrthonormalCols V₂) (h₁₂ : V₁ᴴ * V₂ = 0)
    (hrs : Fintype.card r + Fintype.card s = Fintype.card m)
    (hrp : Fintype.card r + 2 ≤ Fintype.card p) (B : Matrix s a ℝ) :
    ∫ ω, frobNorm (pinv ((Q ω)ᴴ * V₁) * ((Q ω)ᴴ * V₂) * B) ^ 2 ∂μ =
      frobNorm B ^ 2 * (((Fintype.card m : ℝ) - Fintype.card p) /
        ((Fintype.card m : ℝ) - Fintype.card r) *
          ((Fintype.card r : ℝ) / ((Fintype.card p : ℝ) - Fintype.card r - 1))) := by
  classical
  have := hQ.isProbabilityMeasure
  have hVV : V₁ * V₁ᴴ + V₂ * V₂ᴴ = 1 :=
    (hasOrthonormalCols_fromCols_iff.mpr ⟨hV₁, hV₂, h₁₂⟩).mul_conjTranspose_add_mul_conjTranspose
      hrs
  have hW : HasOrthonormalCols (V₁ᴴ)ᴴ := by rwa [Matrix.conjTranspose_conjTranspose]
  have hpinv := integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hQ hpm hW hrp
  set Z : Ω → Matrix s s ℝ := fun ω => V₂ᴴ * Q ω * middle (V₁ᴴ * Q ω) * (V₂ᴴ * Q ω)ᴴ with hZdef
  have hZm : Measurable fun Q₀ : Matrix m p ℝ =>
      V₂ᴴ * Q₀ * middle (V₁ᴴ * Q₀) * (V₂ᴴ * Q₀)ᴴ :=
    (((measurable_const.matrix_mul measurable_id).matrix_mul
      (measurable_middle.comp (measurable_const.matrix_mul measurable_id))).matrix_mul
      (continuous_id.matrix_conjTranspose.measurable.comp
        (measurable_const.matrix_mul measurable_id)))
  -- The conjugated middle factor is integrable: its norm is at most `‖(V₁ᴴQ)⁺‖_F²`.
  have hZ : Integrable Z μ := by
    refine Integrable.mono' hpinv (hZm.comp_aemeasurable hQ.aemeasurable).aestronglyMeasurable ?_
    filter_upwards [ae_specNorm_le_one_of_hasLaw_haarFrame hQ] with ω hω
    rw [← specNorm_eq_norm]
    have hY : specNorm (V₂ᴴ * Q ω) ≤ 1 := (hV₂.specNorm_conjTranspose_mul_le _).trans hω
    have hM : specNorm (middle (V₁ᴴ * Q ω)) ≤ frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 := by
      rw [middle]
      refine (specNorm_mul_le _ _).trans ?_
      rw [specNorm_conjTranspose, pinv_conjTranspose, specNorm_conjTranspose, ← sq]
      exact pow_le_pow_left₀ (specNorm_nonneg _) (specNorm_le_frobNorm _) 2
    have hM0 := specNorm_nonneg (middle (V₁ᴴ * Q ω))
    have hY0 := specNorm_nonneg (V₂ᴴ * Q ω)
    change specNorm (V₂ᴴ * Q ω * middle (V₁ᴴ * Q ω) * (V₂ᴴ * Q ω)ᴴ) ≤ _
    calc specNorm (V₂ᴴ * Q ω * middle (V₁ᴴ * Q ω) * (V₂ᴴ * Q ω)ᴴ)
        ≤ specNorm (V₂ᴴ * Q ω) * specNorm (middle (V₁ᴴ * Q ω)) * specNorm (V₂ᴴ * Q ω) := by
          refine (specNorm_mul_le _ _).trans ?_
          rw [specNorm_conjTranspose]
          exact mul_le_mul_of_nonneg_right (specNorm_mul_le _ _) hY0
      _ ≤ 1 * frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 * 1 := by gcongr
      _ = frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 := by ring
  have hrank : ∀ᵐ ω ∂μ, Function.Injective ((Q ω)ᴴ * V₁).mulVec := by
    filter_upwards [ae_rank_mul_eq_min_of_hasLaw_haarFrame V₁ᴴ hQ] with ω hω
    rw [mulVec_injective_iff_rank_eq, show (Q ω)ᴴ * V₁ = (V₁ᴴ * Q ω)ᴴ by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose], Matrix.rank_conjTranspose,
      hω, Matrix.rank_conjTranspose, hV₁.rank_eq]
    omega
  have htr : ∀ᵐ ω ∂μ, (Z ω).trace = frobNorm (pinv (V₁ᴴ * Q ω)) ^ 2 - Fintype.card r := by
    filter_upwards [ae_hasOrthonormalCols_of_hasLaw_haarFrame hQ hpm, hrank] with ω h1 h2
    exact trace_conj_middle_eq h1 hVV h2
  have hU2 := integral_conjTranspose_mul_mul_mul_conjTranspose_of_isLeftUnitarilyInvariant hQ hV₂
    h₁₂ measurable_middle hZ
  have hval := integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame hQ hpm hW hrp
  have htrZ : ∫ ω, (Z ω).trace ∂μ = Fintype.card r * (1 + ((Fintype.card m : ℝ) - Fintype.card p) /
      ((Fintype.card p : ℝ) - Fintype.card r - 1)) - Fintype.card r := by
    rw [integral_congr_ae htr, integral_sub hpinv (integrable_const _), hval, integral_const,
      probReal_univ, one_smul]
  have hC : (B * Bᴴ).trace = frobNorm B ^ 2 := by
    rw [← frobNorm_conjTranspose B, frobNorm_sq_eq_re_trace, Matrix.conjTranspose_conjTranspose,
      RCLike.re_to_real]
  simp only [frobNorm_pinv_mul_mul_sq_eq_trace]
  rw [Matrix.integral_trace (hZ.mul_const _), Matrix.integral_mul_const hZ, hU2]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul, smul_eq_mul]
  rw [htrZ, hC]
  have hs : (Fintype.card s : ℝ) = Fintype.card m - Fintype.card r := by
    rw [← hrs]; push_cast; ring
  have hmr : (0 : ℝ) < (Fintype.card m : ℝ) - Fintype.card r := by
    have : (Fintype.card r : ℝ) + 2 ≤ Fintype.card m := by exact_mod_cast hrp.trans hpm
    linarith
  have hpr : (0 : ℝ) < (Fintype.card p : ℝ) - Fintype.card r - 1 := by
    have : (Fintype.card r : ℝ) + 2 ≤ Fintype.card p := by exact_mod_cast hrp
    linarith
  rw [hs]
  field_simp
  ring

end NLAlib
