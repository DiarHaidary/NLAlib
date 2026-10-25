/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.LowRank.Gaussian.EarlyTruncation
public import NLAlib.RandomMatrix.Gaussian.FourthMoment
public import NLAlib.ForMathlib.Probability.Moments.PaleyZygmund
public import NLAlib.LowerBounds.LowRank.EarlyTruncationBlock

/-!
# The early-truncated randomized SVD needs $\Omega(k/\varepsilon^2)$ samples for large $k$

For $\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, (1 - \delta)\mathbf{I}_k)$ with
$\delta = \sqrt{k/\ell}/4$ and a standard Gaussian $2k \times \ell$ test matrix $\mathbf{\Omega}$,
the expected error of the early-truncated randomized SVD
$\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ (`NLAlib.earlyTruncatedRSVD`)
exceeds the optimum by a factor $1 + c\sqrt{k/\ell}$ for $k \ge K_0$ and $\ell \ge Ck$, so relative
error $1 + \varepsilon$ needs $\ell \ge c^2k/\varepsilon^2$. The proof puts the deterministic step
`NLAlib.frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational`
(`NLAlib.LowerBounds.LowRank.EarlyTruncationBlock`) on a good event of probability at least
$1/24$: extreme singular value tails of the two row blocks and a Paley–Zygmund bound for the cross
product $\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}$, conditionally on $\mathbf{\Omega}_2$.
The $k = 1$ instance is in `NLAlib.LowerBounds.LowRank.EarlyTruncation`.

New (research note `reports/OP1-EarlyTruncatedRSVD.md` of the NLAlib workflow, 2026-10-25).
Design: `docs/design/LowRank-EstimatorLowerBounds.md` §3.1. Real throughout.

## Main results

* `NLAlib.exists_forall_le_integral_frobNorm_sub_earlyTruncatedRSVD_sq_of_hasLaw_gaussianMatrix`:
  the general-$k$ expectation bound.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix
open scoped Matrix

namespace NLAlib

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {l : Type*} [Fintype l]

/-- The left side of the variational inequality at $\theta = \arctan(1/40)$ is at least
$0.0045\,v^3u$ under the concentration bounds (with $v = \sqrt{k}$, $u = \sqrt{\ell}$). -/
private theorem le_variational_arith_lhs {u v s py b a F fx fy : ℝ} (hu : 0 < u) (hv : 0 < v)
    (hvu : 100 * v ≤ u) (hs : s = 1 - v / (4 * u)) (hpy : py < u + 5 / 4 * v)
    (hfx : fx ≤ v ^ 2 * (u + 5 / 4 * v) ^ 2) (hfy : v ^ 2 * (u - 5 / 4 * v) ^ 2 ≤ fy)
    (hF : 1 / 2 * (v ^ 2 * fy) < F) (hb0 : 0 ≤ b) (hb : b < 3 * v * py) (hab : F ≤ a * b) :
    0.0045 * (v ^ 3 * u) ≤ 2 * s * (40 / 1601) * a - 1 / 1601 * (fx - s ^ 2 * fy) := by
  have huv : 0 < u * v := mul_pos hu hv
  set q := v / (4 * u) with hqdef
  have hq : q ≤ 1 / 400 := by
    rw [hqdef, div_le_iff₀ (by positivity)]
    linarith
  have hq0 : 0 ≤ q := by positivity
  have hs0 : 399 / 400 ≤ s := by linarith
  have hd : 0 ≤ u - 5 / 4 * v := by linarith
  have huv' : u * v ≤ u * (u / 100) := mul_le_mul_of_nonneg_left (by linarith) hu.le
  have hd2 : 39 / 40 * u ^ 2 ≤ (u - 5 / 4 * v) ^ 2 := by
    have : (u - 5 / 4 * v) ^ 2 = u ^ 2 - 5 / 2 * (u * v) + 25 / 16 * v ^ 2 := by ring
    linarith [sq_nonneg v]
  have hv4u2 : 0 < v ^ 4 * u ^ 2 := by positivity
  have hFlow : 39 / 80 * (v ^ 4 * u ^ 2) < F := by
    have e1 := mul_le_mul_of_nonneg_left hfy (sq_nonneg v)
    have e2 := mul_le_mul_of_nonneg_left hd2 (by positivity : 0 ≤ v ^ 2 * v ^ 2)
    linarith
  -- `3.0375 = 3 (1 + 5/4 · 1/100)`, from `py < u + 5v/4` and `v ≤ u/100`
  have hbup : b < 3.0375 * (u * v) := by
    have := mul_lt_mul_of_pos_left hpy (by positivity : 0 < 3 * v)
    have hvv : v * v ≤ v * (u / 100) := mul_le_mul_of_nonneg_left (by linarith) hv.le
    linarith
  have ha0 : 0 < a := by
    by_contra h
    push Not at h
    linarith [mul_nonpos_of_nonpos_of_nonneg h hb0]
  -- `3.0375 = 3 (1 + 5/4 · 1/100)`: the bound `b < 3 v py ≤ 3 v (u + 5v/4)` with `v ≤ u/100`
  have halow : 39 / 80 * (v ^ 4 * u ^ 2) < a * (3.0375 * (u * v)) := by
    have := mul_le_mul_of_nonneg_left hbup.le ha0.le
    linarith
  -- `0.16 < (39/80) / 3.0375 ≈ 0.1605`
  have halow' : 0.16 * (v ^ 3 * u) ≤ a := by
    refine le_of_mul_le_mul_right ?_ (by positivity : 0 < 3.0375 * (u * v))
    have : 0.16 * (v ^ 3 * u) * (3.0375 * (u * v)) = 0.486 * (v ^ 4 * u ^ 2) := by ring
    linarith
  have hss : 1 - 2 * q ≤ s ^ 2 := by
    have : s ^ 2 = 1 - 2 * q + q ^ 2 := by rw [hs]; ring
    linarith [sq_nonneg q]
  -- `5.5 = 5 + 1/2`: `(u + 5v/4)² - (u - 5v/4)² = 5uv`, and `s² ≥ 1 - 2q` costs `2q u² = uv/2`
  have hD : fx - s ^ 2 * fy ≤ 5.5 * (v ^ 3 * u) := by
    have h1 : s ^ 2 * (v ^ 2 * (u - 5 / 4 * v) ^ 2) ≤ s ^ 2 * fy :=
      mul_le_mul_of_nonneg_left hfy (sq_nonneg s)
    have h2 : (1 - 2 * q) * (u - 5 / 4 * v) ^ 2 ≤ s ^ 2 * (u - 5 / 4 * v) ^ 2 :=
      mul_le_mul_of_nonneg_right hss (sq_nonneg _)
    have h3 : q * (u - 5 / 4 * v) ^ 2 ≤ q * u ^ 2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hd (by linarith) 2) hq0
    have h4 : q * u ^ 2 = u * v / 4 := by
      rw [hqdef]
      field_simp
    have h5 := mul_le_mul_of_nonneg_left h2 (sq_nonneg v)
    have h6 := mul_le_mul_of_nonneg_left h3 (sq_nonneg v)
    rw [h4] at h6
    have h7 : v ^ 2 * (u + 5 / 4 * v) ^ 2 - v ^ 2 * (u - 5 / 4 * v) ^ 2 = 5 * (v ^ 3 * u) := by
      ring
    have h8 : v ^ 2 * (u * v / 4) = v ^ 3 * u / 4 := by ring
    linarith
  have := mul_le_mul hs0 halow' (by positivity) (by linarith)
  have e : 2 * s * (40 / 1601) * a = 80 / 1601 * (s * a) := by ring
  rw [e]
  norm_num at this hD ⊢
  linarith [(by positivity : 0 ≤ v ^ 3 * u)]

/-- The arithmetic of the block instance: the concentration bounds and the variational inequality
at $\theta = \arctan(1/40)$ force the tail content $T \ge 10^{-7}k$ (with $v = \sqrt{k}$,
$u = \sqrt{\ell}$). -/
private theorem le_of_variational_arith {u v s T sx py b a F fx fy : ℝ} (hu : 0 < u)
    (hv : 0 < v) (hvu : 100 * v ≤ u) (hs : s = 1 - v / (4 * u)) (hT : 0 ≤ T) (hpy0 : 0 ≤ py)
    (hpy : py < u + 5 / 4 * v) (hsx : u - 5 / 4 * v < sx)
    (hfx : fx ≤ v ^ 2 * (u + 5 / 4 * v) ^ 2) (hfy : v ^ 2 * (u - 5 / 4 * v) ^ 2 ≤ fy)
    (hF : 1 / 2 * (v ^ 2 * fy) < F) (hb0 : 0 ≤ b) (hb : b < 3 * v * py) (hab : F ≤ a * b)
    (hE7 : 2 * s * (40 / 1601) * a - 1 / 1601 * (fx - s ^ 2 * fy) ≤
      T * (s ^ 2 * py ^ 2 - sx ^ 2) + 2 * s * b * √(v ^ 2 * T)) :
    1 / 10 ^ 7 * v ^ 2 ≤ T := by
  have hR := le_variational_arith_lhs hu hv hvu hs hpy hfx hfy hF hb0 hb hab
  have huv : 0 < u * v := mul_pos hu hv
  have hq : v / (4 * u) ≤ 1 / 400 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hq0 : 0 ≤ v / (4 * u) := by positivity
  have hs1 : s ≤ 1 := by linarith
  have hd : 0 ≤ u - 5 / 4 * v := by linarith
  have hsx2 : (u - 5 / 4 * v) ^ 2 ≤ sx ^ 2 := pow_le_pow_left₀ hd hsx.le 2
  have hpy2 : py ^ 2 ≤ (u + 5 / 4 * v) ^ 2 := pow_le_pow_left₀ hpy0 hpy.le 2
  have hbup : b < 3.0375 * (u * v) := by
    have := mul_lt_mul_of_pos_left hpy (by positivity : 0 < 3 * v)
    have hvv : v * v ≤ v * (u / 100) := mul_le_mul_of_nonneg_left (by linarith) hv.le
    linarith
  set w := √(v ^ 2 * T) with hw
  have hw0 : 0 ≤ w := Real.sqrt_nonneg _
  have hw2 : w ^ 2 = v ^ 2 * T := Real.sq_sqrt (by positivity)
  have hL1 : T * (s ^ 2 * py ^ 2 - sx ^ 2) ≤ T * (5 * (u * v)) := by
    apply mul_le_mul_of_nonneg_left _ hT
    have h1 : s ^ 2 * py ^ 2 ≤ py ^ 2 :=
      mul_le_of_le_one_left (sq_nonneg py) (pow_le_one₀ (by linarith) hs1)
    have h2 : (u + 5 / 4 * v) ^ 2 - (u - 5 / 4 * v) ^ 2 = 5 * (u * v) := by ring
    linarith
  have hL2 : 2 * s * b * w ≤ 2 * (3.0375 * (u * v)) * w := by
    have h1 : s * b ≤ b := mul_le_of_le_one_left hb0 hs1
    exact mul_le_mul_of_nonneg_right (by linarith) hw0
  -- divide the two sides by `u v`; `6.075 = 2 · 3.0375`
  have hkey : 0.0045 * v ^ 2 ≤ 5 * T + 6.075 * w := by
    refine le_of_mul_le_mul_left ?_ huv
    have : (u * v) * (0.0045 * v ^ 2) = 0.0045 * (v ^ 3 * u) := by ring
    linarith
  by_contra hcon
  push Not at hcon
  -- with `T < 10⁻⁷ v²`: `5 T < 5·10⁻⁷ v²`, so `6.075 w > 0.0045 v² - 5·10⁻⁷ v²` would force
  -- `w ≥ 0.00074 v²`, while `w = √(v² T) < √(10⁻⁷) v² ≈ 0.000316 v²`
  have hw' : w < 0.000317 * v ^ 2 := by
    by_contra h
    push Not at h
    have := mul_le_mul h h (by positivity) hw0
    have h2 : 0.000317 * v ^ 2 * (0.000317 * v ^ 2) = 0.000317 ^ 2 * (v ^ 2 * v ^ 2) := by ring
    have h3 := mul_lt_mul_of_pos_left hcon (by positivity : 0 < v ^ 2)
    nlinarith
  linarith

/-- $100\sqrt{k} \le \sqrt{\ell}$ when $10^4 k \le \ell$. -/
private lemma hundred_mul_sqrt_le_sqrt {x y : ℝ} (h : 10 ^ 4 * x ≤ y) : 100 * √x ≤ √y :=
  calc 100 * √x = √(10 ^ 4 * x) := by
        rw [Real.sqrt_mul (by norm_num), show (10 ^ 4 : ℝ) = 100 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
    _ ≤ √y := Real.sqrt_le_sqrt h

omit [Fintype l] in
/-- Both row blocks of a measurable matrix-valued map are measurable. -/
private lemma measurable_toRows {k : ℕ} {X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ}
    (hX : Measurable X) :
    Measurable (fun ω => (X ω).toRows₁) ∧ Measurable (fun ω => (X ω).toRows₂) :=
  ⟨Matrix.measurable_iff.2 fun i j => (Matrix.measurable_apply (Sum.inl i) j).comp hX,
    Matrix.measurable_iff.2 fun i j => (Matrix.measurable_apply (Sum.inr i) j).comp hX⟩

/-- The two row blocks of a standard Gaussian matrix are independent standard Gaussians. -/
private theorem hasLaw_toRows_indepFun {k : ℕ} {X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ}
    (hX : HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ) :
    HasLaw (fun ω => (X ω).toRows₁) (gaussianMatrix (Fin k) l) μ ∧
      HasLaw (fun ω => (X ω).toRows₂) (gaussianMatrix (Fin k) l) μ ∧
      IndepFun (fun ω => (X ω).toRows₁) (fun ω => (X ω).toRows₂) μ := by
  classical
  have h1 : HasOrthonormalCols (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) :=
    hasOrthonormalCols_selectionMatrix Sum.inl_injective
  have h2 : HasOrthonormalCols (selectionMatrix Sum.inr : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) :=
    hasOrthonormalCols_selectionMatrix Sum.inr_injective
  have h12 : (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ *
      (selectionMatrix Sum.inr : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ) = 0 := by
    rw [conjTranspose_selectionMatrix_mul]
    ext i j
    rw [Matrix.submatrix_apply, selectionMatrix_apply]
    simp
  have e1 : (fun ω => (X ω).toRows₁) =
      fun ω => (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ * X ω := by
    funext ω
    rw [conjTranspose_selectionMatrix_mul]
    rfl
  have e2 : (fun ω => (X ω).toRows₂) =
      fun ω => (selectionMatrix Sum.inr : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ * X ω := by
    funext ω
    rw [conjTranspose_selectionMatrix_mul]
    rfl
  rw [e1, e2]
  exact ⟨hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX h1,
    hasLaw_conjTranspose_mul_of_hasLaw_gaussianMatrix hX h2,
    indepFun_conjTranspose_mul_of_hasLaw_gaussianMatrix hX h1 h2 h12⟩

/-- The extreme singular value tails of a $k \times \ell$ Gaussian at deviation
$\sqrt{k}/4$. -/
private theorem measureReal_specNorm_ge_le_and_singularValues_le_le {k : ℕ} (hk : 1 ≤ k)
    {Y : Ω → Matrix (Fin k) l ℝ}
    (hY : HasLaw Y (gaussianMatrix (Fin k) l) μ) :
    μ.real {ω | √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ≤ specNorm (Y ω)} ≤
        Real.exp (-(k : ℝ) / 32) ∧
      μ.real {ω | singularValues (Y ω)ᴴ (k - 1) ≤
        √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ)} ≤ Real.exp (-(k : ℝ) / 32) := by
  have := hY.isProbabilityMeasure
  have ht : (0 : ℝ) ≤ √(k : ℝ) / 4 := by positivity
  have hsq : -(√(k : ℝ) / 4) ^ 2 / 2 = -(k : ℝ) / 32 := by
    rw [div_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
  constructor
  · have h := measureReal_specNorm_ge_le_of_hasLaw_gaussianMatrix hY ht
    rw [hsq, Fintype.card_fin] at h
    refine (measureReal_mono fun ω hω => ?_).trans h
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith
  · have h := measureReal_singularValues_le_le_of_hasLaw_gaussianMatrix
      (hasLaw_conjTranspose_of_hasLaw_gaussianMatrix hY) (k := k - 1)
      (by rw [Fintype.card_fin]; omega) ht
    rw [hsq, Fintype.card_fin] at h
    refine (measureReal_mono fun ω hω => ?_).trans h
    simp only [Set.mem_ofPred_eq] at hω ⊢
    linarith

/-- The section bound for the cross term at a fixed $\mathbf{y}$ of full row rank:
Paley–Zygmund for $\|\mathbf{\Omega}_1\mathbf{y}^{\mathsf{T}}\|_{\mathsf{F}}^2$ and the Chevet
tail. -/
private theorem measureReal_section_le {k : ℕ} (hk : 1 ≤ k) {Y : Ω → Matrix (Fin k) l ℝ}
    (hY : HasLaw Y (gaussianMatrix (Fin k) l) μ) (hYm : Measurable Y) {y : Matrix (Fin k) l ℝ}
    (hy : 0 < singularValues yᴴ (k - 1)) :
    μ.real {ω |
      ¬ (1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm yᵀ ^ 2) <
        frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) ^ 2) ∨
      ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} ≤
      11 / 12 + Real.exp (-(k : ℝ) / 2) := by
  have := hY.isProbabilityMeasure
  have : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  have hTy : yᵀ = yᴴ := (Matrix.conjTranspose_eq_transpose_of_trivial y).symm
  have hsp : 0 < specNorm yᵀ := hTy ▸ hy.trans_le (singularValues_le_specNorm _ _)
  have hfr : 0 < frobNorm yᵀ := hsp.trans_le (specNorm_le_frobNorm _)
  set m := frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm yᵀ ^ 2 with hm
  have hm0 : 0 < m := by
    rw [hm, frobNorm_one_sq, Fintype.card_fin]
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  set Z : Ω → ℝ := fun ω => frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) ^ 2 with hZ
  have hZm : Measurable Z :=
    (measurable_frobNorm.comp ((measurable_const.matrix_mul hYm).matrix_mul
      measurable_const)).pow_const 2
  have hZ1 : ∫ ω, Z ω ∂μ = m := integral_frobNorm_mul_mul_sq_of_hasLaw_gaussianMatrix hY _ _
  have hZ4 : ∫ ω, Z ω ^ 2 ∂μ ≤ 3 * m ^ 2 := by
    have h := integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix hY
      (1 : Matrix (Fin k) (Fin k) ℝ) yᵀ
    simpa only [hZ, ← pow_mul] using h
  have hZ2 : MemLp Z 2 μ := by
    rw [memLp_two_iff_integrable_sq hZm.aestronglyMeasurable]
    simpa only [hZ, ← pow_mul] using
      integrable_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix hY
        (1 : Matrix (Fin k) (Fin k) ℝ) yᵀ
  have hPZ := sq_mul_sq_integral_le_integral_sq_mul_measureReal_gt
    (ae_of_all _ fun ω => sq_nonneg _) hZ2 (θ := 1 / 2) (by norm_num) (by norm_num)
  rw [hZ1] at hPZ
  set p := μ.real {ω | 1 / 2 * m < Z ω} with hp
  have hp1 : 1 / 12 ≤ p := by
    have hp0 : 0 ≤ p := measureReal_nonneg
    have h3 : (∫ ω, Z ω ^ 2 ∂μ) * p ≤ 3 * m ^ 2 * p := mul_le_mul_of_nonneg_right hZ4 hp0
    have hm2 : 0 < m ^ 2 := by positivity
    nlinarith
  have hA : μ.real {ω | ¬ (1 / 2 * m < Z ω)} ≤ 11 / 12 := by
    have hmeas : MeasurableSet {ω | 1 / 2 * m < Z ω} := measurableSet_lt measurable_const hZm
    have := probReal_compl_eq_one_sub (μ := μ) hmeas
    rw [Set.compl_ofPred] at this
    linarith
  have hB : μ.real {ω | ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} ≤
      Real.exp (-(k : ℝ) / 2) := by
    have h := measureReal_specNorm_mul_mul_ge_le_of_hasLaw_gaussianMatrix hY
      (1 : Matrix (Fin k) (Fin k) ℝ) yᵀ (t := √(k : ℝ) * specNorm yᵀ) (by positivity)
    have e : -(√(k : ℝ) * specNorm yᵀ) ^ 2 /
        (2 * (specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ) ^ 2) = -(k : ℝ) / 2 := by
      rw [specNorm_one, mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]
      field_simp
    rw [e] at h
    refine (measureReal_mono fun ω hω => ?_).trans h
    simp only [Set.mem_ofPred_eq, not_lt] at hω ⊢
    exact hω
  have hU : {ω | ¬ (1 / 2 * m < Z ω) ∨ ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} =
      {ω | ¬ (1 / 2 * m < Z ω)} ∪ {ω | ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Y ω * yᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm yᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm yᵀ + √(k : ℝ) * specNorm yᵀ)} :=
    Set.ofPred_or
  rw [hU]
  exact (measureReal_union_le _ _).trans (add_le_add hA hB)

/-- The good event of the block instance: the extreme singular values of both row blocks lie
within $\tfrac54\sqrt{k}$ of $\sqrt{\ell}$, and the cross product
$\mathbf{\Omega}_1\mathbf{\Omega}_2^{\mathsf{T}}$ is large in the Frobenius norm and small in the
spectral norm (in the form of the Paley–Zygmund and Chevet bounds of
`measureReal_section_le`). -/
private def IsGoodBlock {k : ℕ} (Ω' : Matrix (Fin k ⊕ Fin k) l ℝ) : Prop :=
  specNorm Ω'.toRows₁ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ∧
    √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues Ω'.toRows₁ᴴ (k - 1) ∧
    specNorm Ω'.toRows₂ < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ∧
    √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues Ω'.toRows₂ᴴ (k - 1) ∧
    1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm Ω'.toRows₂ᵀ ^ 2) <
      frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Ω'.toRows₁ * Ω'.toRows₂ᵀ) ^ 2 ∧
    specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * Ω'.toRows₁ * Ω'.toRows₂ᵀ) <
      specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm Ω'.toRows₂ᵀ +
        frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm Ω'.toRows₂ᵀ +
        √(k : ℝ) * specNorm Ω'.toRows₂ᵀ

/-- The good event of a measurable test matrix is measurable. -/
private lemma measurableSet_isGoodBlock {k : ℕ} {X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ}
    (hXm : Measurable X) : MeasurableSet {ω | IsGoodBlock (X ω)} := by
  obtain ⟨hR1, hR2⟩ := measurable_toRows hXm
  have hH : Measurable fun M : Matrix (Fin k) l ℝ => singularValues Mᴴ (k - 1) :=
    ((continuous_singularValues _).comp continuous_id.matrix_conjTranspose).measurable
  have hR2T : Measurable fun ω => (X ω).toRows₂ᵀ := hR2.matrix_transpose
  have hW : Measurable fun ω =>
      (1 : Matrix (Fin k) (Fin k) ℝ) * (X ω).toRows₁ * (X ω).toRows₂ᵀ :=
    (measurable_const.matrix_mul hR1).matrix_mul hR2T
  have m5 : Measurable fun ω => 1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 *
      frobNorm (X ω).toRows₂ᵀ ^ 2) :=
    (((measurable_frobNorm.comp hR2T).pow_const 2).const_mul _).const_mul _
  have m6 : Measurable fun ω => specNorm (1 : Matrix (Fin k) (Fin k) ℝ) *
      frobNorm (X ω).toRows₂ᵀ + frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) *
      specNorm (X ω).toRows₂ᵀ + √(k : ℝ) * specNorm (X ω).toRows₂ᵀ :=
    (((measurable_frobNorm.comp hR2T).const_mul _).add
      ((measurable_specNorm.comp hR2T).const_mul _)).add
      ((measurable_specNorm.comp hR2T).const_mul _)
  exact (measurableSet_lt (measurable_specNorm.comp hR1) measurable_const).inter
    ((measurableSet_lt measurable_const (hH.comp hR1)).inter
    ((measurableSet_lt (measurable_specNorm.comp hR2) measurable_const).inter
    ((measurableSet_lt measurable_const (hH.comp hR2)).inter
    ((measurableSet_lt m5 ((measurable_frobNorm.comp hW).pow_const 2)).inter
    (measurableSet_lt (measurable_specNorm.comp hW) m6)))))

/-- A complement bound: if $S^{\mathsf{c}} \subseteq A \cup B \cup C$ then
$\mathbb{P}[S] \ge 1 - \mathbb{P}[A] - \mathbb{P}[B] - \mathbb{P}[C]$. -/
private lemma one_sub_le_measureReal_of_compl_subset [IsProbabilityMeasure μ] {S A B C : Set Ω}
    (h : Sᶜ ⊆ A ∪ B ∪ C) : 1 - (μ.real A + μ.real B + μ.real C) ≤ μ.real S := by
  have hu := measureReal_union_le (μ := μ) S Sᶜ
  rw [Set.union_compl_self, probReal_univ] at hu
  have h1 := measureReal_mono (μ := μ) h
  have h2 := measureReal_union_le (μ := μ) (A ∪ B) C
  have h3 := measureReal_union_le (μ := μ) A B
  linarith

/-- $e^{-x} \le 1/126$ for $x \ge 125$. -/
private lemma exp_neg_le_one_div_of_le {x : ℝ} (hx : 125 ≤ x) : Real.exp (-x) ≤ 1 / 126 := by
  rw [Real.exp_neg, inv_eq_one_div, div_le_div_iff₀ (Real.exp_pos x) (by norm_num)]
  linarith [Real.add_one_le_exp x]

/-- The good event of the block instance has probability at least $1/24$. -/
private theorem le_measureReal_isGoodBlock_of_hasLaw_gaussianMatrix {k : ℕ} (hk : 4000 ≤ k)
    (hl : (10 ^ 4 : ℝ) * k ≤ Fintype.card l)
    {X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ} (hX : HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ)
    (hXm : Measurable X) :
    1 / 24 ≤ μ.real {ω | IsGoodBlock (X ω)} := by
  have := hX.isProbabilityMeasure
  obtain ⟨hY₁, hY₂, hind⟩ := hasLaw_toRows_indepFun hX
  obtain ⟨hY₁m, hY₂m⟩ := measurable_toRows hXm
  have hk1 : 1 ≤ k := by omega
  have hK : (4000 : ℝ) ≤ k := by exact_mod_cast hk
  have hpos : 0 < √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) := by
    have := hundred_mul_sqrt_le_sqrt hl
    have : 0 < √(k : ℝ) := Real.sqrt_pos.2 (by linarith)
    linarith
  obtain ⟨t1a, t1b⟩ := measureReal_specNorm_ge_le_and_singularValues_le_le hk1 hY₁
  obtain ⟨t2a, t2b⟩ := measureReal_specNorm_ge_le_and_singularValues_le_le hk1 hY₂
  have hH : Measurable fun M : Matrix (Fin k) l ℝ => singularValues Mᴴ (k - 1) :=
    ((continuous_singularValues _).comp continuous_id.matrix_conjTranspose).measurable
  set G₂ : Set (Matrix (Fin k) l ℝ) := {y | specNorm y < √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ)
    ∧ √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ) < singularValues yᴴ (k - 1)} with hG₂
  have hG₂m : MeasurableSet G₂ :=
    (measurableSet_lt measurable_specNorm measurable_const).inter
      (measurableSet_lt measurable_const hH)
  set E : Set (Matrix (Fin k) l ℝ × Matrix (Fin k) l ℝ) := {p | p.2 ∉ G₂ ∨
      ¬ (1 / 2 * (frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) ^ 2 * frobNorm p.2ᵀ ^ 2) <
        frobNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * p.1 * p.2ᵀ) ^ 2) ∨
      ¬ (specNorm ((1 : Matrix (Fin k) (Fin k) ℝ) * p.1 * p.2ᵀ) <
        specNorm (1 : Matrix (Fin k) (Fin k) ℝ) * frobNorm p.2ᵀ +
          frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) * specNorm p.2ᵀ + √(k : ℝ) * specNorm p.2ᵀ)}
    with hE
  have hEm : MeasurableSet E := by
    have hT : Measurable fun p : Matrix (Fin k) l ℝ × Matrix (Fin k) l ℝ => p.2ᵀ :=
      measurable_snd.matrix_transpose
    have hW : Measurable fun p : Matrix (Fin k) l ℝ × Matrix (Fin k) l ℝ =>
        (1 : Matrix (Fin k) (Fin k) ℝ) * p.1 * p.2ᵀ :=
      (measurable_const.matrix_mul measurable_fst).matrix_mul hT
    refine (hG₂m.preimage measurable_snd).compl.union
      ((measurableSet_lt ?_ ((measurable_frobNorm.comp hW).pow_const 2)).compl.union
      (measurableSet_lt (measurable_specNorm.comp hW) ?_).compl)
    · exact (((measurable_frobNorm.comp hT).pow_const 2).const_mul _).const_mul _
    · exact (((measurable_frobNorm.comp hT).const_mul _).add
        ((measurable_specNorm.comp hT).const_mul _)).add
        ((measurable_specNorm.comp hT).const_mul _)
  have hC := hind.measureReal_mem_le_add hY₁m.aemeasurable hY₂m.aemeasurable hEm hG₂m
    (δ₁ := 11 / 12 + Real.exp (-(k : ℝ) / 2)) (δ₂ := Real.exp (-(k : ℝ) / 32) +
      Real.exp (-(k : ℝ) / 32)) (by positivity)
    (fun y hy => by
      refine (measureReal_mono fun ω hω => ?_).trans
        (measureReal_section_le hk1 hY₁ hY₁m (hpos.trans hy.2))
      simp only [hE, Set.mem_ofPred_eq] at hω ⊢
      rcases hω with h | h
      · exact absurd hy h
      · exact h)
    (by
      refine (measureReal_mono fun ω hω => ?_).trans ((measureReal_union_le _ _).trans
        (add_le_add t2a t2b))
      simp only [hG₂, Set.mem_ofPred_eq, not_and_or, not_lt, Set.mem_union] at hω ⊢
      exact hω)
  have he1 : Real.exp (-(k : ℝ) / 32) ≤ 1 / 126 := by
    rw [neg_div]
    exact exp_neg_le_one_div_of_le (by linarith)
  have he2 : Real.exp (-(k : ℝ) / 2) ≤ 1 / 126 := by
    rw [neg_div]
    exact exp_neg_le_one_div_of_le (by linarith)
  have hS := one_sub_le_measureReal_of_compl_subset (μ := μ) (S := {ω | IsGoodBlock (X ω)})
    (A := {ω | √(Fintype.card l : ℝ) + 5 / 4 * √(k : ℝ) ≤ specNorm (X ω).toRows₁})
    (B := {ω | singularValues (X ω).toRows₁ᴴ (k - 1) ≤
      √(Fintype.card l : ℝ) - 5 / 4 * √(k : ℝ)})
    (C := {ω | ((X ω).toRows₁, (X ω).toRows₂) ∈ E}) fun ω hω => by
      simp only [IsGoodBlock, hE, hG₂, Set.mem_compl_iff, Set.mem_union, Set.mem_ofPred_eq]
        at hω ⊢
      by_contra hc
      push Not at hc
      exact hω ⟨hc.1.1, hc.1.2, hc.2.1.1, hc.2.1.2, hc.2.2.1, hc.2.2.2⟩
  linarith

/-- The block instance has rank at least $k$ once the head block has full row rank. -/
private lemma le_rank_fromBlocks_mul {k : ℕ} {s : ℝ} {Ω' : Matrix (Fin k ⊕ Fin k) l ℝ}
    {A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ} (hA : A = Matrix.fromBlocks 1 0 0 (s • 1))
    (h : 0 < singularValues Ω'.toRows₁ᴴ (k - 1)) : k ≤ (A * Ω').rank := by
  rw [singularValues_pos_iff, Matrix.rank_conjTranspose] at h
  have e : (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ * (A * Ω') =
      Ω'.toRows₁ := by
    rw [conjTranspose_selectionMatrix_mul, hA]
    ext i j
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toRows₁]
  have := Matrix.rank_mul_le_right
    (selectionMatrix Sum.inl : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ)ᴴ (A * Ω')
  rw [e] at this
  omega

/-- The angle of the competitor frame: for $\theta = \arctan(1/40)$,
$\sin\theta\cos\theta = 40/1601$ and $\sin^2\theta = 1/1601$. -/
private lemma sin_arctan_mul_cos_arctan_and_sin_arctan_sq :
    Real.sin (Real.arctan (1 / 40)) * Real.cos (Real.arctan (1 / 40)) = 40 / 1601 ∧
      Real.sin (Real.arctan (1 / 40)) ^ 2 = 1 / 1601 := by
  have hsq : √(1 + (1 / 40 : ℝ) ^ 2) * √(1 + (1 / 40 : ℝ) ^ 2) = 1 + (1 / 40 : ℝ) ^ 2 :=
    Real.mul_self_sqrt (by positivity)
  constructor
  · rw [Real.sin_arctan, Real.cos_arctan, div_mul_div_comm, mul_one, hsq]
    norm_num
  · rw [Real.sin_arctan, div_pow, sq (√_), hsq]
    norm_num

/-- On the good event the error exceeds the optimum by $(1 - s^2)10^{-7}k$. -/
private theorem le_frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_of_isGoodBlock {k : ℕ}
    (hk : 4000 ≤ k) (hl : (10 ^ 4 : ℝ) * k ≤ Fintype.card l) {Ω' : Matrix (Fin k ⊕ Fin k) l ℝ}
    {A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ} {s : ℝ}
    (hs : s = 1 - √((k : ℝ) / Fintype.card l) / 4) (hA : A = Matrix.fromBlocks 1 0 0 (s • 1))
    (hG : IsGoodBlock Ω') :
    k * s ^ 2 + (1 - s ^ 2) * (1 / 10 ^ 7 * k) ≤ frobNorm (A - earlyTruncatedRSVD A Ω' k) ^ 2 := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hG
  have : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  set u := √(Fintype.card l : ℝ) with hu
  set v := √(k : ℝ) with hv
  have hK : (4000 : ℝ) ≤ k := by exact_mod_cast hk
  have hv0 : 0 < v := Real.sqrt_pos.2 (by linarith)
  have hv2 : v ^ 2 = k := Real.sq_sqrt (by linarith)
  have hvu : 100 * v ≤ u := hundred_mul_sqrt_le_sqrt hl
  have hu0 : 0 < u := by linarith
  have hs' : s = 1 - v / (4 * u) := by
    rw [hs, Real.sqrt_div' _ (Nat.cast_nonneg _), ← hu, ← hv]
    field_simp
  have hq : v / (4 * u) ≤ 1 / 400 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hq0 : 0 ≤ v / (4 * u) := by positivity
  have hs0 : 0 ≤ s := by linarith
  have hs1 : s ≤ 1 := by linarith
  have hd : 0 < u - 5 / 4 * v := by linarith
  set T := ∑ i : Fin k, rangeProjector (truncatedSVD (A * Ω') k) (Sum.inr i) (Sum.inr i) with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ =>
    ((isStarProjection_rangeProjector (truncatedSVD (A * Ω') k)).posSemidef.diag_nonneg)
  obtain ⟨hE1, hE2⟩ := frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_ge_and_variational hs0 hs1
    hA (le_rank_fromBlocks_mul hA (hd.trans h2)) (Real.arctan (1 / 40)) hT
  obtain ⟨hsc, hs2⟩ := sin_arctan_mul_cos_arctan_and_sin_arctan_sq
  set W := Ω'.toRows₁ * Ω'.toRows₂ᵀ with hW
  have hsx : u - 5 / 4 * v < singularValues Ω'.toRows₁ (k - 1) := by simpa using h2
  have hfx : frobNorm Ω'.toRows₁ ^ 2 ≤ v ^ 2 * (u + 5 / 4 * v) ^ 2 := by
    have h := frobNorm_sq_le_card_mul_specNorm_sq Ω'.toRows₁ᵀ
    rw [frobNorm_transpose, specNorm_transpose, Fintype.card_fin, ← hv2] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (specNorm_nonneg _) h1.le 2) (sq_nonneg v))
  have hfy : v ^ 2 * (u - 5 / 4 * v) ^ 2 ≤ frobNorm Ω'.toRows₂ ^ 2 := by
    have e := frobNorm_sq_eq_sum_singularValues_sq Ω'.toRows₂ᴴ
    rw [frobNorm_conjTranspose, Fintype.card_fin] at e
    have h := Finset.card_nsmul_le_sum (Finset.range k)
      (fun i => singularValues Ω'.toRows₂ᴴ i ^ 2) ((u - 5 / 4 * v) ^ 2) fun i hi =>
        pow_le_pow_left₀ hd.le ((h4.le).trans (singularValues_antitone _
          (by rw [Finset.mem_range] at hi; omega))) 2
    rw [Finset.card_range, nsmul_eq_mul, ← hv2] at h
    rw [e]
    exact h
  have hF : 1 / 2 * (v ^ 2 * frobNorm Ω'.toRows₂ ^ 2) < frobNorm W ^ 2 := by
    rw [frobNorm_one_sq, Fintype.card_fin, frobNorm_transpose, Matrix.one_mul, ← hv2] at h5
    exact h5
  have hf1 : frobNorm (1 : Matrix (Fin k) (Fin k) ℝ) = v := by
    rw [← Real.sqrt_sq (frobNorm_nonneg _), frobNorm_one_sq, Fintype.card_fin]
  have hb : specNorm W < 3 * v * specNorm Ω'.toRows₂ := by
    rw [Matrix.one_mul, specNorm_one, one_mul, specNorm_transpose, hf1] at h6
    have h := frobNorm_le_sqrt_card_mul_specNorm Ω'.toRows₂ᵀ
    rw [Fintype.card_fin, specNorm_transpose] at h
    linarith
  have hab : frobNorm W ^ 2 ≤ nuclearNorm W * specNorm W := by
    have h := abs_frobInner_le_nuclearNorm_mul_specNorm W W
    rwa [frobInner_self, abs_of_nonneg (sq_nonneg _)] at h
  have hE7 : 2 * s * (40 / 1601) * nuclearNorm W - 1 / 1601 *
      (frobNorm Ω'.toRows₁ ^ 2 - s ^ 2 * frobNorm Ω'.toRows₂ ^ 2) ≤
      T * (s ^ 2 * specNorm Ω'.toRows₂ ^ 2 - singularValues Ω'.toRows₁ (k - 1) ^ 2) +
        2 * s * specNorm W * √(v ^ 2 * T) := by
    rw [← hsc, ← hs2, hv2]
    linarith [hE2]
  have hTk := le_of_variational_arith hu0 hv0 hvu hs' hT0 (specNorm_nonneg _) h3 hsx hfx hfy hF
    (specNorm_nonneg _) hb hab hE7
  rw [hv2] at hTk
  have h1s : 0 ≤ 1 - s ^ 2 := sub_nonneg.2 (pow_le_one₀ hs0 hs1)
  have := mul_le_mul_of_nonneg_left hTk h1s
  linarith only [this, hE1]

/-- The optimum of the block instance is at most $ks^2$: compare with the head projector. -/
private lemma frobNorm_fromBlocks_sub_truncatedSVD_sq_le {k : ℕ} {s : ℝ}
    {A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ} (hA : A = Matrix.fromBlocks 1 0 0 (s • 1)) :
    frobNorm (A - truncatedSVD A k) ^ 2 ≤ k * s ^ 2 := by
  set V : Matrix (Fin k ⊕ Fin k) (Fin k) ℝ := selectionMatrix Sum.inl with hV
  have hB : (V * Vᴴ).rank ≤ k :=
    (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_card_width V).trans (by simp))
  have hAB : A - V * Vᴴ =
      Matrix.diagonal (Sum.elim (fun _ : Fin k => (0 : ℝ)) (fun _ : Fin k => s)) := by
    ext i j
    rw [hA, Matrix.sub_apply, Matrix.mul_apply]
    simp only [hV, selectionMatrix_apply, Matrix.conjTranspose_apply, star_trivial]
    rcases i with i | i <;> rcases j with j | j <;>
      simp [Matrix.one_apply, Matrix.diagonal, eq_comm]
  have hF : frobNorm (A - V * Vᴴ) ^ 2 = k * s ^ 2 := by
    rw [hAB, frobNorm_diagonal_sq]
    simp [Fintype.sum_sum_type, Real.norm_eq_abs, sq_abs]
  rw [← hF]
  exact pow_le_pow_left₀ (frobNorm_nonneg _) (frobNorm_sub_truncatedSVD_le_of_rank_le _ hB) 2

/-- **The early-truncated randomized SVD has excess $\Omega(\sqrt{k/\ell})$**: there are absolute
constants $c, C > 0$ and $K_0$ such that for every $k \ge K_0$, a standard Gaussian
$2k \times \ell$ test matrix $\mathbf{\Omega}$ with $\ell \ge Ck$, and
$\mathbf{A} = \operatorname{diag}(\mathbf{I}_k, (1 - \delta)\mathbf{I}_k)$ with
$\delta = \sqrt{k/\ell}/4$,
$$\Bigl(1 + c\sqrt{k/\ell}\Bigr)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2
\le \mathbb{E}\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)
\|_{\mathsf{F}}^2\,.$$
So relative error $1 + \varepsilon$ needs $\ell \ge c^2k/\varepsilon^2$: the $k$-dependence of
the library's $900k/\varepsilon^2$ is also sharp. The constants are existential: the proof gives
$c = 1/(96 \cdot 10^7)$, $C = 10^4$, $K_0 = 4000$; numerically
$c \approx 0.2$ for every $k \ge 1$ (research note OP1, §2(b)). $k \ge K_0$ is where the proof's
concentration events have probability at least $1/24$; for $2 \le k < K_0$ the statement is
expected but not proved (design note, OQ3).
No printed source. New (research note OP1, §4).
Result: early-truncated-rsvd-lower-bound -/
theorem
    exists_forall_le_integral_frobNorm_sub_earlyTruncatedRSVD_sq_of_hasLaw_gaussianMatrix :
    ∃ c C : ℝ, ∃ K₀ : ℕ, 0 < c ∧ 0 < C ∧ ∀ {Ω l : Type} [MeasurableSpace Ω] [Fintype l]
      (μ : Measure Ω) (k : ℕ) (X : Ω → Matrix (Fin k ⊕ Fin k) l ℝ)
      (A : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) ℝ),
      HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ → K₀ ≤ k → C * k ≤ Fintype.card l →
      A = Matrix.fromBlocks 1 0 0 ((1 - √((k : ℝ) / Fintype.card l) / 4) • 1) →
      (1 + c * √((k : ℝ) / Fintype.card l)) *
          frobNorm (A - truncatedSVD A k) ^ 2 ≤
        ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
  refine ⟨1 / (10 ^ 7 * 96), 10 ^ 4, 4000, by norm_num, by norm_num, ?_⟩
  intro Ω l _ _ μ k X₀ A hX₀ hk hl hA
  obtain ⟨X, hXm, hXX⟩ := hX₀.aemeasurable
  have hX : HasLaw X (gaussianMatrix (Fin k ⊕ Fin k) l) μ := hX₀.congr hXX.symm
  rw [integral_congr_ae (g := fun ω => frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2)
    (hXX.mono fun ω h => by simp only [h])]
  clear hXX hX₀
  have hP := hX.isProbabilityMeasure
  set K : ℝ := (k : ℝ) with hKdef
  set L : ℝ := (Fintype.card l : ℝ) with hLdef
  set r := √(K / L) with hr
  set s := 1 - r / 4 with hs
  have hK : (4000 : ℝ) ≤ K := by
    rw [hKdef]
    exact_mod_cast hk
  have hL0 : 0 < L := by linarith
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr1 : r ≤ 1 / 100 := by
    rw [hr, Real.sqrt_le_left (by norm_num), div_le_iff₀ hL0]
    linarith
  set G := {ω | IsGoodBlock (X ω)}
  have hG : 1 / 24 ≤ μ.real G := le_measureReal_isGoodBlock_of_hasLaw_gaussianMatrix hk hl hX hXm
  have hGm : MeasurableSet G := measurableSet_isGoodBlock hXm
  set O := frobNorm (A - truncatedSVD A k) ^ 2 with hO
  set β := (1 - s ^ 2) * (1 / 10 ^ 7 * K) with hβ
  have hopt : O ≤ K * s ^ 2 := frobNorm_fromBlocks_sub_truncatedSVD_sq_le hA
  have hlow : ∀ ω, O ≤ frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 := fun ω =>
    pow_le_pow_left₀ (frobNorm_nonneg _)
      (frobNorm_sub_truncatedSVD_le_of_rank_le A (rank_earlyTruncatedRSVD_le A (X ω) k)) 2
  have hβ0 : 0 ≤ β := by
    have : s ^ 2 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have : 0 ≤ 1 - s ^ 2 := by linarith
    positivity
  have hmono : ∫ ω, (O + G.indicator (fun _ => β) ω) ∂μ ≤
      ∫ ω, frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2 ∂μ := by
    refine integral_mono ((integrable_const _).add ((integrable_const β).indicator hGm))
      (integrable_frobNorm_sub_earlyTruncatedRSVD_sq A hX.aemeasurable k) fun ω => ?_
    by_cases hω : ω ∈ G
    · simp only [Set.indicator_of_mem hω]
      linarith [le_frobNorm_sub_earlyTruncatedRSVD_fromBlocks_sq_of_isGoodBlock hk hl hs hA hω]
    · simp only [Set.indicator_of_notMem hω, add_zero]
      exact hlow ω
  rw [integral_add (integrable_const _) ((integrable_const β).indicator hGm), integral_const,
    integral_indicator_const _ hGm, probReal_univ, one_smul, smul_eq_mul] at hmono
  refine le_trans ?_ hmono
  have h1s : r / 4 ≤ 1 - s ^ 2 := by
    rw [hs]
    nlinarith
  have hO0 : 0 ≤ O := sq_nonneg _
  have hOK : O ≤ K := by nlinarith
  have hb : 1 / 24 * (r / 4 * (1 / 10 ^ 7 * K)) ≤ μ.real G * β := by
    rw [hβ]
    exact mul_le_mul hG (mul_le_mul_of_nonneg_right h1s (by positivity)) (by positivity)
      measureReal_nonneg
  have : 1 / (10 ^ 7 * 96) * r * O ≤ 1 / (10 ^ 7 * 96) * r * K :=
    mul_le_mul_of_nonneg_left hOK (by positivity)
  nlinarith

end NLAlib
