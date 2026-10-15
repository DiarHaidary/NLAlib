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
from the Gaussian inverse moments without the Beta law. Real field, as the Haar frame. The moments
are here rather than in `NLAlib.RandomMatrix.Haar.Moments` because they are moments of the block
$\mathbf{W}\mathbf{Q}$, proved from its law and the Gaussian inverse moments. Design:
`docs/design/LowRank-S4.md` §3.2, §8 item 8.

## Main results

* `NLAlib.hasLaw_const_mul_of_hasLaw_haarFrame`: row blocks of a Haar frame with orthonormal rows.
* `NLAlib.hasLaw_const_mul_of_hasLaw_haarFrame_of_hasOrthonormalCols`: corner blocks.
* `NLAlib.integral_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`, with its integrability
  `NLAlib.integrable_frobNorm_pinv_const_mul_sq_of_hasLaw_haarFrame`: the inverse mean of the Beta
  matrix, trace form.
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
