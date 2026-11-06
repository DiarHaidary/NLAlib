/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.ClassicalGramSchmidt
public import NLAlib.Matrix.Computation.OrthRoutine
public import NLAlib.Computation.BLAS.RoundingErrors
public import NLAlib.Computation.BLAS.MatrixKernels
public import NLAlibScaffold.Matrix.Perturbation.OrthErr

/-!
# Classical Gram–Schmidt with reorthogonalization: exact and rounded guarantees (scaffold)

Statements for `NLAlib/Matrix/Computation/ClassicalGramSchmidt.lean` (stage LANCZOS-REORTH,
design note `docs/design/Krylov-LanczosReorth.md` §2.2, §3.3, ids C2–C7): the exact run of CGS2,
the rounded run of one pass with its error coefficient
`NLAlib.cgsPassBound`, <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$,
the one-pass and
two-pass algebra ("twice is enough": the input-relative term $\varepsilon_3$ is first order for
one pass, second order for two), and the routine certificate `NLAlib.Computation.IsOrthRoutine`
of CGS2 under the standard model. [GiraudLangouRozloznikVandenEshof2005, Theorems 1–2] prove
the corresponding QR statements.

## Main results

* `NLAlib.Computation.exec_cgs2_exactSem`: the exact run.
* `NLAlib.Computation.IsRelErrSem.exec_cgsPass`: the rounded pass.
* `NLAlib.norm_transpose_mulVec_cgsPass_le`, `NLAlib.isOrthErr_of_one_pass`,
  `NLAlib.isOrthErr_of_two_passes`: the algebra.
* `NLAlib.Computation.IsRelErrSem.isOrthRoutine_cgs2`: the certificate.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

/-- **One pass leaves a first-order loss of orthogonality** (C4): if
$\|\mathbf{w}_1 - (\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w})\| \le
c_1\|\mathbf{w}\|$ and $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0$, then
$\|\mathbf{V}^{\mathsf{T}}\mathbf{w}_1\| \le \sqrt{1 + \eta_0}\,(\eta_0 + c_1)\|\mathbf{w}\|$.
[GiraudLangouRozloznikVandenEshof2005, proof of Theorem 1].
Proof: $\mathbf{V}^{\mathsf{T}}\mathbf{w}_1 = (\mathbf{I} - \mathbf{V}^{\mathsf{T}}\mathbf{V})
\mathbf{V}^{\mathsf{T}}\mathbf{w} + \mathbf{V}^{\mathsf{T}}\mathbf{f}_1$ (`Matrix.mulVec_mulVec`,
`Matrix.sub_mulVec`); bound both terms with `NLAlib.specNorm_le_sqrt_of_specNorm_gram_sub_one_le`
for $\mathbf{V}^{\mathsf{T}}$. S, about 20 lines. -/
theorem norm_transpose_mulVec_cgsPass_le {n j : ℕ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w w₁ : Fin n → ℝ} {η₀ c₁ : ℝ} (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hc₁ : 0 ≤ c₁)
    (hw₁ : ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ c₁ * ‖WithLp.toLp 2 w‖) :
    ‖WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ ≤ Real.sqrt (1 + η₀) * (η₀ + c₁) * ‖WithLp.toLp 2 w‖ := by
  have hs : specNorm Vᵀ ≤ Real.sqrt (1 + η₀) := by
    rw [specNorm_transpose]
    exact specNorm_le_sqrt_of_specNorm_gram_sub_one_le hV
  have hη : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have hy : ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ≤ Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 w‖ :=
    (norm_toLp_mulVec_le Vᵀ w).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have key : ∀ x : Fin n → ℝ, Vᵀ *ᵥ (x + (w - V *ᵥ (Vᵀ *ᵥ w))) =
      Vᵀ *ᵥ x - (Vᵀ * V - 1) *ᵥ (Vᵀ *ᵥ w) := by
    intro x
    rw [Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.sub_mulVec,
      Matrix.one_mulVec]
    abel
  have hkey := key (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))
  rw [sub_add_cancel] at hkey
  have hsx : specNorm Vᵀ * ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤
      Real.sqrt (1 + η₀) * (c₁ * ‖WithLp.toLp 2 w‖) :=
    mul_le_mul hs hw₁ (norm_nonneg _) (Real.sqrt_nonneg _)
  have hsy : specNorm (Vᵀ * V - 1) * ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ≤
      η₀ * (Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 w‖) :=
    mul_le_mul hV hy (norm_nonneg _) hη
  rw [hkey, WithLp.toLp_sub]
  have h1 := norm_toLp_mulVec_le Vᵀ (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))
  have h2 := norm_toLp_mulVec_le (Vᵀ * V - 1) (Vᵀ *ᵥ w)
  have htri := norm_sub_le (WithLp.toLp 2 (Vᵀ *ᵥ (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))))
    (WithLp.toLp 2 ((Vᵀ * V - 1) *ᵥ (Vᵀ *ᵥ w)))
  have hfin : Real.sqrt (1 + η₀) * (c₁ * ‖WithLp.toLp 2 w‖) +
      η₀ * (Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 w‖) =
      Real.sqrt (1 + η₀) * (η₀ + c₁) * ‖WithLp.toLp 2 w‖ := by ring
  linarith

/-- **One classical Gram–Schmidt pass meets the guarantee with a first-order input term** (C7):
from the bounds of `NLAlib.Computation.IsRelErrSem.exec_cgsPass`, `NLAlib.IsOrthErr` holds with
$\varepsilon_1 = 0$, $\varepsilon_2 = c_1$, $\varepsilon_3 = \sqrt{1+\eta_0}(\eta_0 + c_1)$; this is
why one pass is not enough (the loss is divided by the admissibility ratio).
[GiraudLangouRozloznikVandenEshof2005, Theorem 1].
Proof: the two fields from the hypotheses and `NLAlib.norm_transpose_mulVec_cgsPass_le`.
S, about 10 lines. -/
theorem isOrthErr_of_one_pass {n j : ℕ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w w₁ : Fin n → ℝ} {h₁ : Fin j → ℝ} {η₀ c₁ : ℝ} (hc₁ : 0 ≤ c₁)
    (hres : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (w - V *ᵥ h₁ - w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖)
    (hw₁ : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ c₁ * ‖WithLp.toLp 2 w‖) :
    IsOrthErr η₀ 0 c₁ (Real.sqrt (1 + η₀) * (η₀ + c₁)) V w h₁ w₁ := by
  refine ⟨hres, fun hV => ?_⟩
  rw [zero_mul, zero_add]
  exact norm_transpose_mulVec_cgsPass_le hV hc₁ (hw₁ hV)

private lemma norm_toLp_sub_mulVec_transpose_mulVec_le_of_gram {n j : ℕ}
    {V : Matrix (Fin n) (Fin j) ℝ} {w : Fin n → ℝ} {η₀ : ℝ}
    (hV : specNorm (Vᵀ * V - 1) ≤ η₀) (hη : η₀ ≤ 1) :
    ‖WithLp.toLp 2 (w - V *ᵥ (Vᵀ *ᵥ w))‖ ≤ ‖WithLp.toLp 2 w‖ := by
  have hs := specNorm_le_sqrt_of_specNorm_gram_sub_one_le hV
  have hη0 : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have hy := (norm_toLp_mulVec_le V (Vᵀ *ᵥ w)).trans
    (mul_le_mul_of_nonneg_right hs (norm_nonneg _))
  have hinner : inner ℝ (WithLp.toLp 2 w) (WithLp.toLp 2 (V *ᵥ (Vᵀ *ᵥ w))) =
      ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp,
      EuclideanSpace.inner_toLp_toLp]
    simp only [star_trivial]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have hsq : ‖WithLp.toLp 2 (V *ᵥ (Vᵀ *ᵥ w))‖ ^ 2 ≤ (1 + η₀) * ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖ ^ 2 := by
    rw [← Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 1 + η₀), ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) hy 2
  rw [WithLp.toLp_sub, ← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _), norm_sub_sq_real, hinner]
  nlinarith [sq_nonneg ‖WithLp.toLp 2 (Vᵀ *ᵥ w)‖]

private lemma two_passes_residual_arith {c₁ u s a b₁ H₁ H₂ H R : ℝ} (hc0 : 0 ≤ c₁)
    (hc₁ : c₁ ≤ 1 / 100) (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c₁) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 + 1 / 200)
    (ha : 0 ≤ a) (hb₁ : b₁ ≤ (1 + c₁) * a) (hres : R ≤ c₁ * a + c₁ * b₁ + s * (u * H))
    (hh : H ≤ H₁ + H₂) (hh₁ : H₁ ≤ (s + c₁) * a) (hh₂ : H₂ ≤ (s + c₁) * b₁) :
    R ≤ 3 * c₁ * a := by
  have hH : H₁ + H₂ ≤ 21 / 10 * a := by
    have hk : (s + c₁) * ((2 + c₁) * a) ≤ (1 + 3 / 200) * ((2 + c₁) * a) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hb₁ (by linarith : 0 ≤ s + c₁),
      mul_le_mul_of_nonneg_right hc₁ ha]
  have h1 : u * H ≤ u * (21 / 10 * a) := mul_le_mul_of_nonneg_left (hh.trans hH) hu
  have hsu : s * (u * H) ≤ 3 / 5 * c₁ * a := by
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0, mul_le_mul_of_nonneg_right hs1
      (mul_nonneg hu ha), mul_le_mul_of_nonneg_right hu₁ ha, mul_nonneg hu ha]
  nlinarith [mul_le_mul_of_nonneg_left hb₁ hc0, mul_nonneg hc0 ha]

private lemma two_passes_orth_arith {η₀ c₁ s a b₁ b₂ t X : ℝ} (hη0 : 0 ≤ η₀)
    (hη : η₀ ≤ 1 / 100) (hc0 : 0 ≤ c₁) (hc₁ : c₁ ≤ 1 / 100) (hs0 : 0 ≤ s) (hs1 : s ≤ 1 + η₀ / 2)
    (hss : s ^ 2 = 1 + η₀) (ha : 0 ≤ a) (hb0 : 0 ≤ b₁) (ht0 : 0 ≤ t)
    (ht : t ≤ s * (η₀ + c₁) * a) (horth : X ≤ s * (c₁ * b₁) + η₀ * t)
    (hb₁' : b₁ ≤ b₂ + c₁ * b₁ + s * t) :
    X ≤ 2 * c₁ * b₂ + 2 * (η₀ + c₁) ^ 2 * a := by
  have h2 : 2 * c₁ * ((1 - c₁) * b₁) ≤ 2 * c₁ * (b₂ + s * t) :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have h3 : s * (c₁ * b₁) ≤ 2 * c₁ * ((1 - c₁) * b₁) := by
    nlinarith [mul_nonneg hc0 hb0, mul_nonneg (mul_nonneg hc0 hc0) hb0]
  have h4 : (η₀ + 2 * c₁ * s) * t ≤ (η₀ + 2 * c₁ * s) * (s * (η₀ + c₁) * a) :=
    mul_le_mul_of_nonneg_left ht (by positivity)
  have h5 : (η₀ + 2 * c₁ * s) * s ≤ 2 * (η₀ + c₁) := by
    nlinarith [mul_le_mul_of_nonneg_left hs1 hη0, mul_nonneg hc0 hη0]
  have h6 : (η₀ + 2 * c₁ * s) * (s * (η₀ + c₁) * a) ≤ 2 * (η₀ + c₁) * ((η₀ + c₁) * a) :=
    calc _ = (η₀ + 2 * c₁ * s) * s * ((η₀ + c₁) * a) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h5 (mul_nonneg (by linarith) ha)
  linarith only [horth, h2, h3, h4, h6]

/-- **Twice is enough** (C5): two passes with the bounds of
`NLAlib.Computation.IsRelErrSem.exec_cgsPass`
(the second on $\mathbf{w}_1$) and coefficients summed with relative error $u$ meet
`NLAlib.IsOrthErr` with $\varepsilon_1 = 2c_1$, $\varepsilon_2 = 3c_1$,
$\varepsilon_3 = 2(\eta_0 + c_1)^2$, for $\eta_0 \le 1/100$, $c_1 \le 1/100$, $4u \le c_1$.
[GiraudLangouRozloznikVandenEshof2005, Theorem 2]; [Parlett1998, §6.9].
Proof: `NLAlib.norm_transpose_mulVec_cgsPass_le` for both passes:
$\|\mathbf{V}^{\mathsf{T}}\mathbf{w}_2\| \le \eta_0\|\mathbf{V}^{\mathsf{T}}\mathbf{w}_1\| +
\sqrt{1+\eta_0}\,c_1\|\mathbf{w}_1\|$ (write $\mathbf{V}^{\mathsf{T}}\mathbf{w}_2 =
(\mathbf{I} - \mathbf{V}^{\mathsf{T}}\mathbf{V})\mathbf{V}^{\mathsf{T}}\mathbf{w}_1 +
\mathbf{V}^{\mathsf{T}}\mathbf{f}_2$), and $\|\mathbf{w}_1\| \le (\|\mathbf{w}_2\| + (1+\eta_0)
(\eta_0 + c_1)\|\mathbf{w}\|)/(1 - c_1)$; collect into $2c_1\|\mathbf{w}_2\| +
2(\eta_0 + c_1)^2\|\mathbf{w}\|$ (`nlinarith` on the numeric constants). Residual: sum the two
pass residuals, $\|\mathbf{w}_1\| \le (1 + c_1)\|\mathbf{w}\|$: here $\|\mathbf{w} -
\mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}\|^2 = \|\mathbf{w}\|^2 - 2\|\mathbf{V}^{\mathsf{T}}
\mathbf{w}\|^2 + (\mathbf{V}^{\mathsf{T}}\mathbf{w})^{\mathsf{T}}(\mathbf{V}^{\mathsf{T}}\mathbf{V})
(\mathbf{V}^{\mathsf{T}}\mathbf{w}) \le \|\mathbf{w}\|^2$ by expanding the square
(`EuclideanSpace.norm_sq_eq`-style, `Matrix.dotProduct_mulVec`) and $\mathbf{y}^{\mathsf{T}}
\mathbf{V}^{\mathsf{T}}\mathbf{V}\mathbf{y} \le (1 + \eta_0)\|\mathbf{y}\|^2 \le 2\|\mathbf{y}\|^2$
(`NLAlib.norm_toLp_mulVec_le`); the crude $\|\mathbf{w}_1\| \le (2 + \eta_0 + c_1)\|\mathbf{w}\|$ is
not enough for $3c_1$. Then the summation error
$\|\mathbf{V}\mathbf{e}_s\| \le \sqrt{1+\eta_0}\,u\,(\|\mathbf{h}_1\| + \|\mathbf{h}_2\|)$ with
$\|\mathbf{h}_1\| \le (\sqrt{1+\eta_0} + c_1)\|\mathbf{w}\|$, $\|\mathbf{h}_2\| \le
(\sqrt{1+\eta_0} + c_1)\|\mathbf{w}_1\|$; in all $\le (2.01 c_1 + 2.1u)\|\mathbf{w}\| \le
3c_1\|\mathbf{w}\|$. M, about 80 lines. -/
theorem isOrthErr_of_two_passes {n j : ℕ} {V : Matrix (Fin n) (Fin j) ℝ}
    {w w₁ w₂ : Fin n → ℝ} {h₁ h₂ h : Fin j → ℝ} {η₀ c₁ u : ℝ} (hη : η₀ ≤ 1 / 100)
    (hc₁ : c₁ ≤ 1 / 100) (hu : 0 ≤ u) (hu₁ : 4 * u ≤ c₁)
    (hp₁ : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (h₁ - Vᵀ *ᵥ w)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (w - V *ᵥ h₁ - w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤ c₁ * ‖WithLp.toLp 2 w‖)
    (hp₂ : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (h₂ - Vᵀ *ᵥ w₁)‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖ ∧
      ‖WithLp.toLp 2 (w₁ - V *ᵥ h₂ - w₂)‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖ ∧
      ‖WithLp.toLp 2 (w₂ - (w₁ - V *ᵥ (Vᵀ *ᵥ w₁)))‖ ≤ c₁ * ‖WithLp.toLp 2 w₁‖)
    (hsum : ∀ i, |h i - (h₁ i + h₂ i)| ≤ u * |h₁ i + h₂ i|) :
    IsOrthErr η₀ (2 * c₁) (3 * c₁) (2 * (η₀ + c₁) ^ 2) V w h w₂ := by
  suffices H : specNorm (Vᵀ * V - 1) ≤ η₀ →
      ‖WithLp.toLp 2 (w - V *ᵥ h - w₂)‖ ≤ 3 * c₁ * ‖WithLp.toLp 2 w‖ ∧
      ‖WithLp.toLp 2 (Vᵀ *ᵥ w₂)‖ ≤
        2 * c₁ * ‖WithLp.toLp 2 w₂‖ + 2 * (η₀ + c₁) ^ 2 * ‖WithLp.toLp 2 w‖ from
    ⟨fun hV => (H hV).1, fun hV => (H hV).2⟩
  intro hV
  obtain ⟨e₁, r₁, f₁⟩ := hp₁ hV
  obtain ⟨e₂, r₂, f₂⟩ := hp₂ hV
  have hc0 : 0 ≤ c₁ := by linarith
  have hη0 : 0 ≤ η₀ := (specNorm_nonneg _).trans hV
  have hs0 : 0 ≤ Real.sqrt (1 + η₀) := Real.sqrt_nonneg _
  have hs1 : Real.sqrt (1 + η₀) ≤ 1 + η₀ / 2 :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have hVx : ∀ x, ‖WithLp.toLp 2 (V *ᵥ x)‖ ≤ Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 x‖ :=
    fun x => (norm_toLp_mulVec_le V x).trans (mul_le_mul_of_nonneg_right
      (specNorm_le_sqrt_of_specNorm_gram_sub_one_le hV) (norm_nonneg _))
  have hVTx : ∀ x, ‖WithLp.toLp 2 (Vᵀ *ᵥ x)‖ ≤ Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 x‖ :=
    fun x => (norm_toLp_mulVec_le Vᵀ x).trans (mul_le_mul_of_nonneg_right
      (by rw [specNorm_transpose]; exact specNorm_le_sqrt_of_specNorm_gram_sub_one_le hV)
      (norm_nonneg _))
  have ht := norm_transpose_mulVec_cgsPass_le hV hc0 f₁
  have hb₁ : ‖WithLp.toLp 2 w₁‖ ≤ (1 + c₁) * ‖WithLp.toLp 2 w‖ := by
    calc ‖WithLp.toLp 2 w₁‖
        = ‖WithLp.toLp 2 (w₁ - (w - V *ᵥ (Vᵀ *ᵥ w))) + WithLp.toLp 2 (w - V *ᵥ (Vᵀ *ᵥ w))‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ c₁ * ‖WithLp.toLp 2 w‖ + ‖WithLp.toLp 2 w‖ :=
          (norm_add_le _ _).trans (add_le_add f₁
            (norm_toLp_sub_mulVec_transpose_mulVec_le_of_gram hV (by linarith)))
      _ = _ := by ring
  have hb₁' : ‖WithLp.toLp 2 w₁‖ ≤ ‖WithLp.toLp 2 w₂‖ + c₁ * ‖WithLp.toLp 2 w₁‖ +
      Real.sqrt (1 + η₀) * ‖WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ := by
    calc ‖WithLp.toLp 2 w₁‖
        = ‖WithLp.toLp 2 w₂ - WithLp.toLp 2 (w₂ - (w₁ - V *ᵥ (Vᵀ *ᵥ w₁))) +
            WithLp.toLp 2 (V *ᵥ (Vᵀ *ᵥ w₁))‖ := by
          rw [← WithLp.toLp_sub, ← WithLp.toLp_add]; congr 2; abel
      _ ≤ _ := (norm_add_le _ _).trans (add_le_add ((norm_sub_le _ _).trans
            (add_le_add le_rfl f₂)) (hVx _))
  have hid : Vᵀ *ᵥ w₂ = Vᵀ *ᵥ (w₂ - (w₁ - V *ᵥ (Vᵀ *ᵥ w₁))) - (Vᵀ * V - 1) *ᵥ (Vᵀ *ᵥ w₁) := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec]
    abel
  have horth : ‖WithLp.toLp 2 (Vᵀ *ᵥ w₂)‖ ≤ Real.sqrt (1 + η₀) * (c₁ * ‖WithLp.toLp 2 w₁‖) +
      η₀ * ‖WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ := by
    rw [hid, WithLp.toLp_sub]
    refine (norm_sub_le _ _).trans (add_le_add ((hVTx _).trans ?_) ?_)
    · exact mul_le_mul_of_nonneg_left f₂ hs0
    · exact (norm_toLp_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right hV (norm_nonneg _))
  have hsum' : ‖WithLp.toLp 2 (h - (h₁ + h₂))‖ ≤ u * ‖WithLp.toLp 2 (h₁ + h₂)‖ := by
    calc ‖WithLp.toLp 2 (h - (h₁ + h₂))‖ ≤ ‖WithLp.toLp 2 (u • (h₁ + h₂))‖ :=
          EuclideanSpace.norm_toLp_le_norm_toLp fun i => by
            simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg hu] using hsum i
      _ = _ := by rw [WithLp.toLp_smul, norm_smul, Real.norm_of_nonneg hu]
  have hh₁ : ‖WithLp.toLp 2 h₁‖ ≤ (Real.sqrt (1 + η₀) + c₁) * ‖WithLp.toLp 2 w‖ := by
    calc ‖WithLp.toLp 2 h₁‖ = ‖WithLp.toLp 2 (h₁ - Vᵀ *ᵥ w) + WithLp.toLp 2 (Vᵀ *ᵥ w)‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by linarith [hVTx w])
  have hh₂ : ‖WithLp.toLp 2 h₂‖ ≤ (Real.sqrt (1 + η₀) + c₁) * ‖WithLp.toLp 2 w₁‖ := by
    calc ‖WithLp.toLp 2 h₂‖ = ‖WithLp.toLp 2 (h₂ - Vᵀ *ᵥ w₁) + WithLp.toLp 2 (Vᵀ *ᵥ w₁)‖ := by
          rw [← WithLp.toLp_add, sub_add_cancel]
      _ ≤ _ := (norm_add_le _ _).trans (by linarith [hVTx w₁])
  have hh : ‖WithLp.toLp 2 (h₁ + h₂)‖ ≤ ‖WithLp.toLp 2 h₁‖ + ‖WithLp.toLp 2 h₂‖ := by
    rw [WithLp.toLp_add]; exact norm_add_le _ _
  have hres : ‖WithLp.toLp 2 (w - V *ᵥ h - w₂)‖ ≤ c₁ * ‖WithLp.toLp 2 w‖ +
      c₁ * ‖WithLp.toLp 2 w₁‖ + Real.sqrt (1 + η₀) * (u * ‖WithLp.toLp 2 (h₁ + h₂)‖) := by
    have hid' : w - V *ᵥ h - w₂ =
        (w - V *ᵥ h₁ - w₁) + (w₁ - V *ᵥ h₂ - w₂) - V *ᵥ (h - (h₁ + h₂)) := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_add]; abel
    rw [hid', WithLp.toLp_sub, WithLp.toLp_add]
    exact (norm_sub_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add r₁ r₂))
      ((hVx _).trans (mul_le_mul_of_nonneg_left hsum' hs0)))
  have hss : Real.sqrt (1 + η₀) ^ 2 = 1 + η₀ := Real.sq_sqrt (by linarith)
  exact ⟨two_passes_residual_arith hc0 hc₁ hu hu₁ hs0 (by linarith) (norm_nonneg _) hb₁ hres hh
      hh₁ hh₂,
    two_passes_orth_arith hη0 hη hc0 hc₁ hs0 hs1 hss (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
      ht horth hb₁'⟩

namespace Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

/-- A store of the shape of `s` that holds `a` and `c` in two blocks of distinct buffers and reads
as `s` outside them is the result of the two block writes. -/
private theorem eq_of_read_writeBlock_writeBlock {s s' m f : Store P ℝ} {p : P}
    {b₁ b₂ o₁ o₂ : ℕ} {a c : Array ℝ} (hb : b₁ ≠ b₂) (hsh : s'.shape = s.shape)
    (hA : ∀ i < a.size, s'.read p b₁ (o₁ + i) = a[i]?)
    (hC : ∀ i < c.size, s'.read p b₂ (o₂ + i) = c[i]?)
    (hrest : ∀ q b i, ¬(b = b₁ ∧ o₁ ≤ i ∧ i < o₁ + a.size) →
      ¬(b = b₂ ∧ o₂ ≤ i ∧ i < o₂ + c.size) → s'.read q b i = s.read q b i)
    (hm : s.writeBlock p b₁ o₁ a = some m) (hf : m.writeBlock p b₂ o₂ c = some f) : s' = f := by
  have hshm := Store.shape_of_writeBlock_eq_some hm
  have hshf := Store.shape_of_writeBlock_eq_some hf
  refine Store.ext_of_shape_eq (by rw [hsh, hshf, hshm]) fun q b i => ?_
  by_cases h₁ : b = b₁ ∧ o₁ ≤ i ∧ i < o₁ + a.size
  · obtain ⟨rfl, hi, hi'⟩ := h₁
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hk : k < a.size := by omega
    rw [Store.read_of_writeBlock_eq_some_of_ne hf (Or.inl hb)]
    by_cases hq : q = p
    · subst hq
      rw [hA k hk, Store.read_of_writeBlock_eq_some_of_lt hm hk]
    · obtain ⟨n, hn, -⟩ := Store.exists_getElem?_shape_of_writeBlock_eq_some hm hk
      rw [Store.read_eq_none_of_getElem?_shape_of_ne (hsh ▸ hn) hq,
        Store.read_eq_none_of_getElem?_shape_of_ne (hshm ▸ hn) hq]
  by_cases h₂ : b = b₂ ∧ o₂ ≤ i ∧ i < o₂ + c.size
  · obtain ⟨rfl, hi, hi'⟩ := h₂
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    have hk : k < c.size := by omega
    by_cases hq : q = p
    · subst hq
      rw [hC k hk, Store.read_of_writeBlock_eq_some_of_lt hf hk]
    · obtain ⟨n, hn, -⟩ := Store.exists_getElem?_shape_of_writeBlock_eq_some hf hk
      rw [Store.read_eq_none_of_getElem?_shape_of_ne (hsh ▸ hshm ▸ hn) hq,
        Store.read_eq_none_of_getElem?_shape_of_ne (hshf ▸ hn) hq]
  have hout : ∀ {bb oo L : ℕ}, ¬(b = bb ∧ oo ≤ i ∧ i < oo + L) → b ≠ bb ∨ i < oo ∨ oo + L ≤ i :=
    fun {bb oo L} h => by
      by_cases hbb : b = bb
      · exact Or.inr (by omega)
      · exact Or.inl hbb
  rw [hrest q b i h₁ h₂, Store.read_of_writeBlock_eq_some_of_ne hf (hout h₂),
    Store.read_of_writeBlock_eq_some_of_ne hm (hout h₁)]

/-- A loop whose $k$-th body writes $f(k)$ into cell $o + k$ of buffer `b` and nothing else,
from any store that reads as the start outside the cells written so far, writes the block. -/
private theorem exists_exec_loop_eq_some_of_write (I : Interp P ι ℝ C) {n : IExp ℕ}
    {body : ℕ → Stmt P ι ℕ ℕ} {st : St P ℝ C} (p : P) (b o : ℕ) (f : ℕ → ℝ)
    (hstep : ∀ k < n.eval, ∀ s : St P ℝ C, s.store.shape = st.store.shape →
      (∀ q b' i, ¬(b' = b ∧ o ≤ i ∧ i < o + k) → s.store.read q b' i = st.store.read q b' i) →
      ∃ s', exec I (body k) s = some s' ∧ s.store.write p b (o + k) (f k) = some s'.store) :
    ∃ s', exec I (.loop n body) st = some s' ∧ s'.store.shape = st.store.shape ∧
      (∀ k < n.eval, s'.store.read p b (o + k) = some (f k)) ∧
      ∀ q b' i, ¬(b' = b ∧ o ≤ i ∧ i < o + n.eval) →
        s'.store.read q b' i = st.store.read q b' i := by
  refine exists_exec_loop_eq_some_of_forall I (fun k s => s.store.shape = st.store.shape ∧
    (∀ k' < k, s.store.read p b (o + k') = some (f k')) ∧
    ∀ q b' i, ¬(b' = b ∧ o ≤ i ∧ i < o + k) → s.store.read q b' i = st.store.read q b' i)
    ⟨rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ _ => rfl⟩ ?_
  rintro k hk s ⟨hsh, hvals, hfr⟩
  obtain ⟨s', hrun, hw⟩ := hstep k hk s hsh hfr
  refine ⟨s', hrun, (Store.shape_of_write_eq_some hw).trans hsh, fun k' hk' => ?_,
    fun q b' i hi => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk' with hk' | rfl
    · rw [Store.read_of_write_eq_some_of_ne hw (Or.inr (by omega)), hvals k' hk']
    · exact Store.read_of_write_eq_some hw
  · have hne : b' ≠ b ∨ i ≠ o + k := by
      by_cases hb : b' = b
      · exact Or.inr fun h => hi ⟨hb, by omega, by omega⟩
      · exact Or.inl hb
    rw [Store.read_of_write_eq_some_of_ne hw hne,
      hfr q b' i fun h => hi ⟨h.1, h.2.1, by omega⟩]

/-- The $j$ dots of an exact pass write $\mathbf{V}^{\mathsf{T}}\mathbf{w}$ into the coefficient
block and nothing else. -/
private theorem exec_forRange_dot_exactSem (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P ℝ C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : Holds st.store tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, st.store.read tag wb (wo.eval + i) = some (w i))
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb) :
    ∃ s', exec I (.loop jE fun i =>
        (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) st = some s' ∧
      s'.store.shape = st.store.shape ∧
      (∀ k : Fin jE.eval, s'.store.read tag hb (ho.eval + k) = some ((Vᵀ *ᵥ w) k)) ∧
      ∀ q b i, ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        s'.store.read q b i = st.store.read q b i := by
  have hR : IsRelErrSem (fun _ => (0 : ℝ)) (fun _ x => x) (fun _ _ => True) I.sem :=
    hI ▸ isRelErrSem_exactSem
  have hZ : AddsZeroExactly (fun _ x => x) I.sem := hI ▸ addsZeroExactly_exactSem
  obtain ⟨s', hrun, hsh, hval, hfr⟩ := exists_exec_loop_eq_some_of_write I (n := jE)
    (body := fun i => (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) (st := st)
    tag hb ho.eval (fun k => if h : k < jE.eval then (Vᵀ *ᵥ w) ⟨k, h⟩ else 0)
    fun k hk s hs hs' => by
      have hrd : ∀ {b i}, b ≠ hb → s.store.read tag b i = st.store.read tag b i :=
        fun hb' => hs' _ _ _ fun h => hb' h.1
      obtain ⟨st', w', hrun, hst, habs⟩ := IsRelErrSem.exec_dot_abs_sum_mul_sub_le I tag s hR hZ
        ⟨hb, ho + .var k⟩ Vb (NE * .var k) wb wo NE
        (fun r => if h : r < NE.eval then V ⟨r, h⟩ ⟨k, hk⟩ else 0)
        (fun r => if h : r < NE.eval then w ⟨r, h⟩ else 0) (by norm_num)
        (fun r hr => ⟨V ⟨r, hr⟩ ⟨k, hk⟩, by
          rw [hrd (Ne.symm (hne (by omega) (by omega)).2)]
          simpa [IExp.eval, Nat.add_comm] using hV ⟨r, hr⟩ ⟨k, hk⟩, by simp [hr]⟩)
        (fun r hr => ⟨w ⟨r, hr⟩, by
          rw [hrd (Ne.symm (hne (by omega) (by omega)).1)]; exact hw ⟨r, hr⟩, by simp [hr]⟩)
        (fun h r hr => absurd h (hne (by omega) (by omega)).2)
        (fun h r hr => absurd h (hne (by omega) (by omega)).1) (by
          obtain ⟨len, hlen, hlt⟩ := hhlen k hk
          exact ⟨0, Store.exists_write_eq_some_of_getElem?_shape 0 (hs ▸ hlen) hlt⟩)
      refine ⟨st', hrun, ?_⟩
      have hw' : w' = ∑ r ∈ Finset.range NE.eval,
          (if h : r < NE.eval then V ⟨r, h⟩ ⟨k, hk⟩ else 0) *
            (if h : r < NE.eval then w ⟨r, h⟩ else 0) := by
        simp only [roundingFactor, sub_zero, one_pow, inv_one, sub_self, zero_mul] at habs
        linarith [abs_nonpos_iff.mp habs]
      convert hst using 2
      · rfl
      · rw [dif_pos hk, hw', ← Fin.sum_univ_eq_sum_range]
        simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
  exact ⟨s', hrun, hsh, fun k => by simpa [k.2] using hval k k.2, hfr⟩

/-- The `gemv` of an exact pass writes $\mathbf{V}\mathbf{h}$ into the scratch block `S`. -/
private theorem exec_gemv_exactSem (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (NE jE : IExp ℕ) (Vb hb S : ℕ) (ho : IExp ℕ) (s : St P ℝ C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (h : Fin jE.eval → ℝ)
    (hV : Holds s.store tag Vb 0 V)
    (hh : ∀ k : Fin jE.eval, s.store.read tag hb (ho.eval + k) = some (h k))
    (hS : s.store.shape[S]? = some (tag, NE.eval)) (hSV : S = Vb → NE.eval * jE.eval = 0)
    (hSh : S = hb → jE.eval = 0) :
    ∃ s', exec I (gemv tag NE jE Vb 0 hb ho S 0).run s = some s' ∧
      s.store.writeBlock tag S 0 (Array.ofFn (V *ᵥ h)) = some s'.store := by
  have hR : IsRelErrSem (fun _ => (0 : ℝ)) (fun _ x => x) (fun _ _ => True) I.sem :=
    hI ▸ isRelErrSem_exactSem
  have hZ : AddsZeroExactly (fun _ x => x) I.sem := hI ▸ addsZeroExactly_exactSem
  have key : ∀ (x : ℕ) (xo : IExp ℕ), S ≠ x →
      (∀ k : Fin jE.eval, s.store.read tag x (xo.eval + k) = some (h k)) →
      ∃ s', exec I (gemv tag NE jE Vb 0 x xo S 0).run s = some s' ∧
        s.store.writeBlock tag S 0 (Array.ofFn (V *ᵥ h)) = some s'.store := by
    intro x xo hSx hx
    obtain ⟨st', W, hrun, hst, ΔA, hΔ, hW⟩ := IsRelErrSem.exec_gemv_eq_add_mulVec I tag s hR hZ
      NE jE Vb 0 x xo S 0 V h (by norm_num) (fun i k => ⟨_, hV i k, rfl⟩)
      (fun k => ⟨_, hx k, rfl⟩) (fun e => Or.inr (by simp [hSV e]))
      (fun e => absurd e hSx)
      (fun i hi => ⟨0, Store.exists_write_eq_some_of_getElem?_shape 0 hS (by simpa using hi)⟩)
    have hΔ0 : ΔA = 0 := by
      ext i k
      simpa [roundingFactor] using hΔ i k
    refine ⟨st', hrun, ?_⟩
    convert hst using 2
    · rfl
    ext i hi₁ hi₂
    · simp
    · simp only [Array.getElem_ofFn, Array.getElem_map, List.getElem_toArray, List.getElem_range]
      rw [show W i = W (⟨i, by simpa using hi₁⟩ : Fin NE.eval) from rfl, hW, hΔ0, add_zero]
  by_cases hj0 : jE.eval = 0
  · have heq : exec I (gemv tag NE jE Vb 0 hb ho S 0).run s =
        exec I (gemv tag NE jE Vb 0 (S + 1) 0 S 0).run s := by
      simp only [run_gemv, exec_named, exec_seq, exec_alloc, exec_loop, hj0,
        List.range_zero, List.foldlM_nil]
    rw [heq]
    exact key (S + 1) 0 (by omega) fun k => absurd k.2 (by omega)
  · exact key hb ho (fun e => hj0 (hSh e)) hh

/-- The body of an exact pass of `NLAlib.cgsPass`, on a store with its two scratch buffers
`S` ($N$ cells) and `S + 1` (one cell) allocated, as a frame. -/
private theorem exec_cgsPass_body (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb S : ℕ) (wo ho : IExp ℕ) (st : St P ℝ C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : Holds st.store tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, st.store.read tag wb (wo.eval + i) = some (w i))
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb)
    (hsS : st.store.shape[S]? = some (tag, NE.eval))
    (htS : st.store.shape[S + 1]? = some (tag, 1)) (hwS : 0 < NE.eval → wb < S)
    (hVS : 0 < NE.eval * jE.eval → Vb < S) (hhS : 0 < jE.eval → hb < S) :
    ∃ out : St P ℝ C, exec I ((forRange jE fun i =>
        dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>= fun _ =>
        gemv tag NE jE Vb 0 hb ho S 0 >>= fun _ => ins (.lit tag ⟨S + 1, 0⟩ (-1)) >>= fun _ =>
        axpy (ι := ι) tag ⟨S + 1, 0⟩ S 0 wb wo NE).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin NE.eval, out.store.read tag wb (wo.eval + i) = some ((w - V *ᵥ (Vᵀ *ᵥ w)) i)) ∧
      (∀ i : Fin jE.eval, out.store.read tag hb (ho.eval + i) = some ((Vᵀ *ᵥ w) i)) ∧
      ∀ q b i, b ≠ S → b ≠ S + 1 → ¬(b = wb ∧ wo.eval ≤ i ∧ i < wo.eval + NE.eval) →
        ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        out.store.read q b i = st.store.read q b i := by
  have hR : IsRelErrSem (fun _ => (0 : ℝ)) (fun _ x => x) (fun _ _ => True) I.sem :=
    hI ▸ isRelErrSem_exactSem
  rw [exec_run_bind I
    (b := forRange jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) (fun _ => rfl)]
  obtain ⟨σ₁, hrun₁, hsh₁, hh₁, hfr₁⟩ := exec_forRange_dot_exactSem I hI tag NE jE Vb wb hb wo ho
    st V w hV hw hhlen hne
  rw [show (forRange (ι := ι) jE fun i => dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run
    = .seq (.loop jE fun i => (dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE).run) .skip
    from rfl, exec_seq_skip, hrun₁, Option.bind_some,
    exec_run_bind I (b := gemv tag NE jE Vb 0 hb ho S 0) (fun _ => rfl)]
  have hrd₁ : ∀ {q b i}, b ≠ hb → σ₁.store.read q b i = st.store.read q b i :=
    fun hb' => hfr₁ _ _ _ fun h => hb' h.1
  obtain ⟨σ₂, hrun₂, hst₂⟩ := exec_gemv_exactSem I hI tag NE jE Vb hb S ho σ₁ V (Vᵀ *ᵥ w)
    (fun i k => by rw [hrd₁ (Ne.symm (hne (Fin.pos i) (Fin.pos k)).2)]; exact hV i k) hh₁
    (hsh₁ ▸ hsS)
    (fun e => by by_contra h; exact absurd (hVS (Nat.pos_of_ne_zero h)) (by omega))
    (fun e => by by_contra h; exact absurd (hhS (Nat.pos_of_ne_zero h)) (by omega))
  rw [hrun₂, Option.bind_some,
    exec_run_bind I (b := ins (.lit tag ⟨S + 1, 0⟩ (-1))) (fun _ => rfl)]
  obtain ⟨s₃, hs₃⟩ := Store.exists_write_eq_some_of_getElem?_shape ((-1 : ℚ) : ℝ)
    ((Store.shape_of_writeBlock_eq_some hst₂).trans hsh₁ ▸ htS) Nat.one_pos
  rw [show (ins (ι := ι) (.lit tag ⟨S + 1, 0⟩ (-1))).run = .seq (.instr (.lit tag ⟨S + 1, 0⟩ (-1)))
    .skip from rfl, exec_seq_instr_lit I (by rw [hI]; rfl) hs₃, exec_skip, Option.bind_some]
  have hrd₃ : ∀ {q b i}, b ≠ S + 1 → b ≠ S → s₃.read q b i = σ₁.store.read q b i := fun h₁ h₂ => by
    rw [Store.read_of_write_eq_some_of_ne hs₃ (Or.inl h₁),
      Store.read_of_writeBlock_eq_some_of_ne hst₂ (Or.inl h₂)]
  obtain ⟨σ₄, W, hrun₄, hst₄, hW⟩ := IsRelErrSem.exec_axpy I tag
    { σ₂ with store := s₃, cnt := σ₂.cnt + I.charge (OpKind.lit tag) } hR ⟨S + 1, 0⟩ S 0 wb wo NE
    ((-1 : ℚ) : ℝ) (fun i => if h : i < NE.eval then (V *ᵥ (Vᵀ *ᵥ w)) ⟨i, h⟩ else 0)
    (fun i => if h : i < NE.eval then w ⟨i, h⟩ else 0) (by norm_num)
    ⟨_, Store.read_of_write_eq_some hs₃, rfl⟩
    (fun i hi => ⟨_, by
      rw [IExp.eval_zero, Store.read_of_write_eq_some_of_ne hs₃ (Or.inl (by omega)),
        Store.read_of_writeBlock_eq_some_of_lt hst₂ (by simpa using hi)]
      simp [hi], rfl⟩)
    (fun i hi => ⟨w ⟨i, hi⟩, by
      have := hwS (by omega)
      rw [hrd₃ (b := wb) (by omega) (by omega), hfr₁ _ _ _ fun h => by
        rcases Nat.eq_zero_or_pos jE.eval with hj | hj
        · omega
        · exact (hne (by omega) hj).1 h.1.symm]
      exact hw ⟨i, hi⟩, by simp [hi]⟩)
    (fun e i hi => by have := hwS (by omega); simp only at e; omega)
    (fun e i hi => by have := hwS (by omega); omega)
  refine ⟨σ₄, hrun₄, ?_, fun i => ?_, fun k => ?_, fun q b i hbS hbS₁ hwb hhb => ?_⟩
  · rw [Store.shape_of_writeBlock_eq_some hst₄, Store.shape_of_write_eq_some hs₃,
      Store.shape_of_writeBlock_eq_some hst₂, hsh₁]
  · obtain ⟨θ, δ, hθ, hδ, hWi⟩ := hW i i.2
    have hθ0 : θ = 0 := abs_nonpos_iff.mp (by simpa [roundingFactor] using hθ)
    have hδ0 : δ = 0 := abs_nonpos_iff.mp hδ
    rw [Store.read_of_writeBlock_eq_some_of_lt hst₄ (by simp)]
    simp [hWi, hθ0, hδ0]
    ring
  · have := hhS (Fin.pos k)
    rw [Store.read_of_writeBlock_eq_some_of_ne hst₄ (by
        rcases Nat.eq_zero_or_pos NE.eval with hN | hN
        · exact Or.inr (by
            simp only [Array.size_map, List.size_toArray, List.length_range, hN]; omega)
        · exact Or.inl (hne hN (Fin.pos k)).1), hrd₃ (by omega) (by omega),
      hh₁ k]
  · rw [Store.read_of_writeBlock_eq_some_of_ne hst₄ (by
        by_cases h : b = wb
        · exact Or.inr (by simp only [Array.size_map, List.size_toArray, List.length_range]; omega)
        · exact Or.inl h), hrd₃ hbS₁ hbS, hfr₁ q b i hhb]

/-- An allocation whose body succeeds from the store with the fresh buffer pushed. -/
private theorem exists_exec_alloc (I : Interp P ι ℝ C) (p : P) (len : IExp ℕ)
    (body : ℕ → Stmt P ι ℕ ℕ) (st : St P ℝ C) (Q : Store P ℝ → Prop)
    (h : ∀ σ : St P ℝ C, σ.store = st.store.push (p, Array.replicate len.eval none) →
      ∃ out, exec I (body st.store.size) σ = some out ∧ Q out.store.pop) :
    ∃ out, exec I (.alloc p len body) st = some out ∧ Q out.store := by
  obtain ⟨out, h₁, h₂⟩ := h { st with
    store := st.store.push (p, Array.replicate len.eval none)
    cur := Function.update st.cur p (st.cur p + len.eval)
    peak := Function.update st.peak p (max (st.peak p) (st.cur p + len.eval))
    curW := st.curW + len.eval * I.width p
    peakW := max st.peakW (st.curW + len.eval * I.width p) } rfl
  rw [exec_alloc, h₁]
  exact ⟨_, rfl, h₂⟩

/-- One exact pass of `NLAlib.cgsPass`, as a frame: the reduced vector at (`wb`, `wo`), the
coefficients at (`hb`, `ho`), every other cell and the shape kept. -/
private theorem exec_cgsPass_exactSem (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st : St P ℝ C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : Holds st.store tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, st.store.read tag wb (wo.eval + i) = some (w i))
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : 0 < NE.eval → 0 < jE.eval → hb ≠ wb ∧ hb ≠ Vb) :
    ∃ out : St P ℝ C, exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧
      out.store.shape = st.store.shape ∧
      (∀ i : Fin NE.eval, out.store.read tag wb (wo.eval + i) = some ((w - V *ᵥ (Vᵀ *ᵥ w)) i)) ∧
      (∀ i : Fin jE.eval, out.store.read tag hb (ho.eval + i) = some ((Vᵀ *ᵥ w) i)) ∧
      ∀ q b i, ¬(b = wb ∧ wo.eval ≤ i ∧ i < wo.eval + NE.eval) →
        ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        out.store.read q b i = st.store.read q b i := by
  have hrun : (cgsPass (ι := ι) tag NE jE Vb wb wo hb ho).run = .seq (.alloc tag NE fun s =>
      .alloc tag 1 fun t => ((forRange jE fun i =>
        dot tag ⟨hb, ho + .var i⟩ Vb (NE * .var i) wb wo NE) >>= fun _ =>
        gemv tag NE jE Vb 0 hb ho s 0 >>= fun _ => ins (.lit tag ⟨t, 0⟩ (-1)) >>= fun _ =>
        axpy tag ⟨t, 0⟩ s 0 wb wo NE).run) .skip := rfl
  rw [hrun, exec_seq_skip]
  set S := st.store.size
  have hlt : ∀ {b}, (∃ n, st.store.shape[b]? = some n) → b < S := fun ⟨n, hn⟩ => by
    simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp hn).1
  have hVlt : ∀ (i : Fin NE.eval) (k : Fin jE.eval), Vb < S := fun i k =>
    Store.lt_size_of_read_eq_some (hV i k)
  have hwlt : ∀ i : Fin NE.eval, wb < S := fun i => Store.lt_size_of_read_eq_some (hw i)
  have hhlt : ∀ k < jE.eval, hb < S := fun k hk =>
    let ⟨len, hl, _⟩ := hhlen k hk
    hlt ⟨_, hl⟩
  refine exists_exec_alloc I tag NE _ st (fun s => s.shape = st.store.shape ∧
    (∀ i : Fin NE.eval, s.read tag wb (wo.eval + i) = some ((w - V *ᵥ (Vᵀ *ᵥ w)) i)) ∧
    (∀ i : Fin jE.eval, s.read tag hb (ho.eval + i) = some ((Vᵀ *ᵥ w) i)) ∧
    ∀ q b i, ¬(b = wb ∧ wo.eval ≤ i ∧ i < wo.eval + NE.eval) →
      ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) → s.read q b i = st.store.read q b i)
    fun σ₁ hσ₁ => ?_
  refine exists_exec_alloc I tag 1 _ σ₁ (fun s => Store.shape s.pop = st.store.shape ∧
    (∀ i : Fin NE.eval, Store.read s.pop tag wb (wo.eval + i) = some ((w - V *ᵥ (Vᵀ *ᵥ w)) i)) ∧
    (∀ i : Fin jE.eval, Store.read s.pop tag hb (ho.eval + i) = some ((Vᵀ *ᵥ w) i)) ∧
    ∀ q b i, ¬(b = wb ∧ wo.eval ≤ i ∧ i < wo.eval + NE.eval) →
      ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        Store.read s.pop q b i = st.store.read q b i)
    fun σ₂ hσ₂ => ?_
  have hsz₁ : σ₁.store.size = S + 1 := by rw [hσ₁, Array.size_push]
  rw [hsz₁]
  have hrd₂ : ∀ {q b i}, b < S → σ₂.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσ₂, Store.read_push_of_lt (by omega), hσ₁, Store.read_push_of_lt hb]
  have hsh₂ : ∀ {b}, b < S → σ₂.store.shape[b]? = st.store.shape[b]? := fun hb => by
    rw [hσ₂, Store.getElem?_shape_push_of_lt _ (by omega), hσ₁,
      Store.getElem?_shape_push_of_lt _ hb]
  obtain ⟨σ, hrunσ, hshσ, hwσ, hhσ, hfrσ⟩ := exec_cgsPass_body I hI tag NE jE Vb wb hb S wo ho σ₂
    V w (fun i k => by rw [hrd₂ (hVlt i k)]; exact hV i k)
    (fun i => by rw [hrd₂ (hwlt i)]; exact hw i)
    (fun i hi => by rw [hsh₂ (hhlt i hi)]; exact hhlen i hi) hne
    (by rw [hσ₂, Store.getElem?_shape_push_of_lt _ (by omega), hσ₁,
      Store.getElem?_shape_push_size])
    (by rw [hσ₂, ← hsz₁, Store.getElem?_shape_push_size, IExp.eval_one])
    (fun h => hwlt ⟨0, h⟩) (fun h => hVlt ⟨0, Nat.pos_of_mul_pos_right h⟩
      ⟨0, Nat.pos_of_mul_pos_left h⟩) (fun h => hhlt 0 h)
  have hszσ : σ.store.size = S + 2 := by
    rw [← Store.size_shape, hshσ, Store.size_shape, hσ₂, Array.size_push, hsz₁]
  have hpop : ∀ {q b i}, b < S → Store.read σ.store.pop.pop q b i = σ.store.read q b i :=
    fun hb => by
      rw [Store.read_pop_of_lt (by simp [hszσ]; omega), Store.read_pop_of_lt (by omega)]
  refine ⟨σ, hrunσ, ?_, fun i => (hpop (hwlt i)).trans (hwσ i),
    fun k => (hpop (hhlt k k.2)).trans (hhσ k), fun q b i h₁ h₂ => ?_⟩
  · rw [Store.shape_pop, Store.shape_pop, hshσ, hσ₂, hσ₁]
    simp [Store.shape]
  · by_cases hbS : b < S
    · rw [hpop hbS, hfrσ q b i (by omega) (by omega) h₁ h₂, hrd₂ hbS]
    · rw [Store.read_eq_none_of_size_le (by simp [hszσ]; omega),
        Store.read_eq_none_of_size_le (by omega)]

/-- The $j$ exact additions of `NLAlib.cgs2` write $\mathbf{h}_1 + \mathbf{h}_2$ into the
coefficient block and nothing else. -/
private theorem exec_forRange_add_exactSem (I : Interp P ι ℝ C) (hI : I.sem = exactSem)
    (tag : P) (jE : IExp ℕ) (hb T : ℕ) (ho : IExp ℕ) (st : St P ℝ C) (h₁ h₂ : Fin jE.eval → ℝ)
    (hh₁ : ∀ k : Fin jE.eval, st.store.read tag hb (ho.eval + k) = some (h₁ k))
    (hh₂ : ∀ k : Fin jE.eval, st.store.read tag T k = some (h₂ k)) (hT : 0 < jE.eval → T ≠ hb) :
    ∃ s', exec I (forRange jE fun i =>
        ins (ι := ι) (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run st =
        some s' ∧ s'.store.shape = st.store.shape ∧
      (∀ k : Fin jE.eval, s'.store.read tag hb (ho.eval + k) = some ((h₁ + h₂) k)) ∧
      ∀ q b i, ¬(b = hb ∧ ho.eval ≤ i ∧ i < ho.eval + jE.eval) →
        s'.store.read q b i = st.store.read q b i := by
  rw [show (forRange (ι := ι) jE fun i =>
      ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run = .seq (.loop jE
      fun i => (ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨T, .var i⟩)).run) .skip
    from rfl, exec_seq_skip]
  obtain ⟨s', hrun, hsh, hval, hfr⟩ := exists_exec_loop_eq_some_of_write I (n := jE) (st := st)
    tag hb ho.eval (fun k => if h : k < jE.eval then (h₁ + h₂) ⟨k, h⟩ else 0)
    fun k hk s hs hs' => by
      obtain ⟨n, hn, hlt⟩ := Store.exists_getElem?_shape_of_read_eq_some (hh₁ ⟨k, hk⟩)
      obtain ⟨s'', hs''⟩ := Store.exists_write_eq_some_of_getElem?_shape
        (if h : k < jE.eval then (h₁ + h₂) ⟨k, h⟩ else 0) (hs ▸ hn) hlt
      have hx : s.store.read tag hb (ho.eval + k) = some (h₁ ⟨k, hk⟩) := by
        rw [hs' _ _ _ (by omega)]; exact hh₁ ⟨k, hk⟩
      have hy : s.store.read tag T k = some (h₂ ⟨k, hk⟩) := by
        rw [hs' _ _ _ fun h => hT (by omega) h.1]; exact hh₂ ⟨k, hk⟩
      have hv : I.sem.bin tag .add (h₁ ⟨k, hk⟩) (h₂ ⟨k, hk⟩) =
          some (if h : k < jE.eval then (h₁ + h₂) ⟨k, h⟩ else 0) := by
        rw [hI, dif_pos hk]; rfl
      refine ⟨{ s with store := s'', cnt := s.cnt + I.charge (.bin tag .add) }, ?_, hs''⟩
      rw [exec_seq_instr_bin I (dst := ⟨hb, ho + .var k⟩) (x := ⟨hb, ho + .var k⟩)
        (y := ⟨T, .var k⟩) hx hy hv hs'', exec_skip]
  exact ⟨s', hrun, hsh, fun k => by simpa [k.2] using hval k k.2, hfr⟩

/-- The body of `NLAlib.cgs2` under exact arithmetic, on the store with the scratch buffer of the
second coefficients pushed: popping that buffer gives the two block writes. -/
private theorem exec_cgs2_body (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P)
    (NE jE : IExp ℕ) (Vb wb hb : ℕ) (wo ho : IExp ℕ) (st σ₀ : St P ℝ C)
    (V : Matrix (Fin NE.eval) (Fin jE.eval) ℝ) (w : Fin NE.eval → ℝ)
    (hV : Holds st.store tag Vb 0 V)
    (hw : ∀ i : Fin NE.eval, st.store.read tag wb (wo.eval + i) = some (w i))
    (hwlen : ∀ i < NE.eval, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len)
    (hhlen : ∀ i < jE.eval, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : hb ≠ wb ∧ hb ≠ Vb ∧ wb ≠ Vb)
    (hσ₀ : σ₀.store = st.store.push (tag, Array.replicate jE.eval none)) {mid fin : Store P ℝ}
    (hmid : st.store.writeBlock tag wb wo.eval (Array.ofFn
      ((w - V *ᵥ (Vᵀ *ᵥ w)) - V *ᵥ (Vᵀ *ᵥ (w - V *ᵥ (Vᵀ *ᵥ w))))) = some mid)
    (hfin : mid.writeBlock tag hb ho.eval
      (Array.ofFn (Vᵀ *ᵥ w + Vᵀ *ᵥ (w - V *ᵥ (Vᵀ *ᵥ w)))) = some fin) :
    ∃ out : St P ℝ C, exec I (cgsPass tag NE jE Vb wb wo hb ho >>= fun _ =>
      cgsPass tag NE jE Vb wb wo st.store.size 0 >>= fun _ => forRange jE fun i =>
        ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩
          ⟨st.store.size, .var i⟩)).run σ₀ = some out ∧ out.store.pop = fin := by
  set w₁ := w - V *ᵥ (Vᵀ *ᵥ w)
  set T := st.store.size
  have hlt : ∀ {b}, (∃ n, st.store.shape[b]? = some n) → b < T := fun ⟨n, hn⟩ => by
    simpa [Store.size_shape] using (Array.getElem?_eq_some_iff.mp hn).1
  have hwlt : 0 < NE.eval → wb < T := fun h => hlt ⟨_, (hwlen 0 h).choose_spec.1⟩
  have hhlt : 0 < jE.eval → hb < T := fun h => hlt ⟨_, (hhlen 0 h).choose_spec.1⟩
  have hVlt : 0 < NE.eval → 0 < jE.eval → Vb < T := fun h₁ h₂ =>
    Store.lt_size_of_read_eq_some (hV ⟨0, h₁⟩ ⟨0, h₂⟩)
  have hrd₀ : ∀ {q b i}, b < T → σ₀.store.read q b i = st.store.read q b i := fun hb => by
    rw [hσ₀, Store.read_push_of_lt hb]
  have hsh₀ : ∀ {b}, b < T → σ₀.store.shape[b]? = st.store.shape[b]? := fun hb => by
    rw [hσ₀, Store.getElem?_shape_push_of_lt _ hb]
  rw [exec_run_bind I (b := cgsPass tag NE jE Vb wb wo hb ho) (fun _ => rfl)]
  obtain ⟨o₁, hrun₁, hsh₁, hw₁, hh₁, hfr₁⟩ := exec_cgsPass_exactSem I hI tag NE jE Vb wb hb wo ho
    σ₀ V w (fun i k => by rw [hrd₀ (Store.lt_size_of_read_eq_some (hV i k))]; exact hV i k)
    (fun i => by rw [hrd₀ (hwlt (Fin.pos i))]; exact hw i)
    (fun i hi => by rw [hsh₀ (hhlt (by omega))]; exact hhlen i hi) fun _ _ => ⟨hne.1, hne.2.1⟩
  rw [hrun₁, Option.bind_some, exec_run_bind I (b := cgsPass tag NE jE Vb wb wo T 0)
    (fun _ => rfl)]
  have hTshape : o₁.store.shape[T]? = some (tag, jE.eval) := by
    rw [hsh₁, hσ₀, Store.getElem?_shape_push_size]
  obtain ⟨o₂, hrun₂, hsh₂, hw₂, hh₂, hfr₂⟩ := exec_cgsPass_exactSem I hI tag NE jE Vb wb T wo 0
    o₁ V w₁ (fun i k => by
      rw [hfr₁ _ _ _ (fun h => hne.2.2 h.1.symm) (fun h => hne.2.1 h.1.symm),
        hrd₀ (Store.lt_size_of_read_eq_some (hV i k))]
      exact hV i k)
    hw₁
    (fun i hi => ⟨_, hTshape, by simpa using hi⟩)
    fun h₁ h₂ => ⟨by have := hwlt h₁; omega, by have := hVlt h₁ h₂; omega⟩
  rw [hrun₂, Option.bind_some]
  obtain ⟨o₃, hrun₃, hsh₃, hh₃, hfr₃⟩ := exec_forRange_add_exactSem I hI tag jE hb T ho o₂
    (Vᵀ *ᵥ w) (Vᵀ *ᵥ w₁) (fun k => by
      have := hhlt (Fin.pos k)
      rw [hfr₂ _ _ _ (fun h => hne.1 h.1) (fun h => by omega), hh₁ k])
    (fun k => by simpa using hh₂ k) fun h => by have := hhlt h; omega
  refine ⟨o₃, hrun₃, ?_⟩
  have hsz₃ : o₃.store.size = T + 1 := by
    rw [← Store.size_shape, hsh₃, hsh₂, hsh₁, Store.size_shape, hσ₀, Array.size_push]
  have hpop : ∀ {q b i}, b < T → Store.read o₃.store.pop q b i = o₃.store.read q b i :=
    fun hb => Store.read_pop_of_lt (by omega)
  refine eq_of_read_writeBlock_writeBlock (Ne.symm hne.1) ?_ (fun i hi => ?_) (fun k hk => ?_)
    (fun q b i h₁ h₂ => ?_) hmid hfin
  · rw [Store.shape_pop, hsh₃, hsh₂, hsh₁, hσ₀]
    simp [Store.shape]
  · rw [Array.size_ofFn] at hi
    rw [hpop (hwlt (by omega)), hfr₃ _ _ _ (fun h => hne.1 h.1.symm), hw₂ ⟨i, hi⟩]
    simp [hi]
  · rw [Array.size_ofFn] at hk
    rw [hpop (hhlt (by omega)), hh₃ ⟨k, hk⟩]
    simp [hk]
  · simp only [Array.size_ofFn] at h₁ h₂
    by_cases hbT : b < T
    · rw [hpop hbT, hfr₃ q b i h₂, hfr₂ q b i h₁ (fun h => by omega), hfr₁ q b i h₁ h₂,
        hrd₀ hbT]
    · rw [Store.read_eq_none_of_size_le (by simp [hsz₃]; omega),
        Store.read_eq_none_of_size_le (by omega)]

/-- **CGS2 in exact arithmetic** (C2): under exact real arithmetic, from a state whose buffer `Vb`
holds $\mathbf{V}$ ($N \times j$) and `wb` holds $\mathbf{w}$ at `wo`, `NLAlib.cgs2` succeeds and
writes exactly $\mathbf{w}_2 = \mathbf{w}_1 - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}_1$,
$\mathbf{w}_1 = \mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w}$, at (`wb`, `wo`) and
$\mathbf{V}^{\mathsf{T}}\mathbf{w} + \mathbf{V}^{\mathsf{T}}\mathbf{w}_1$ at (`hb`, `ho`), and
nothing else. No hypothesis on $\mathbf{V}$. No printed source.
Proof: unfold `NLAlib.cgs2`, `NLAlib.cgsPass`; the $j$ dots by `NLAlib.Computation.exec_dot`
(exact semantics: the sum $\mathbf{v}_c^{\mathsf{T}}\mathbf{w}$), the product by
`NLAlib.Computation.exec_gemv`, the update by `NLAlib.Computation.exec_axpy` with the literal
$-1$ exact under `NLAlib.Computation.exactSem`; scoped scratch is freed (the frames of
`NLAlib/Computation/ScalarFrames.lean`); the second pass on $\mathbf{w}_1$, then the $j$ additions.
M, about 120 lines. -/
theorem exec_cgs2_exactSem (I : Interp P ι ℝ C) (hI : I.sem = exactSem) (tag : P) {N j : ℕ}
    (NE jE : IExp ℕ) (hN : NE.eval = N) (hj : jE.eval = j) (Vb wb hb : ℕ) (wo ho : IExp ℕ)
    (st : St P ℝ C) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ)
    (hV : Holds st.store tag Vb 0 V)
    (hw : ∀ i : Fin N, st.store.read tag wb (wo.eval + i) = some (w i))
    (hwlen : ∀ i < N, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len)
    (hhlen : ∀ i < j, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : hb ≠ wb ∧ hb ≠ Vb ∧ wb ≠ Vb) :
    ∃ (out : St P ℝ C) (mid : Store P ℝ),
      exec I (cgs2 tag NE jE Vb wb wo hb ho).run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn
        ((w - V *ᵥ (Vᵀ *ᵥ w)) - V *ᵥ (Vᵀ *ᵥ (w - V *ᵥ (Vᵀ *ᵥ w))))) = some mid ∧
      mid.writeBlock tag hb ho.eval
        (Array.ofFn (Vᵀ *ᵥ w + Vᵀ *ᵥ (w - V *ᵥ (Vᵀ *ᵥ w)))) = some out.store := by
  subst hN hj
  have hrun : (cgs2 (ι := ι) tag NE jE Vb wb wo hb ho).run = .seq (.alloc tag jE fun h₂ =>
      (cgsPass tag NE jE Vb wb wo hb ho >>= fun _ => cgsPass tag NE jE Vb wb wo h₂ 0 >>= fun _ =>
        forRange jE fun i =>
          ins (.bin tag .add ⟨hb, ho + .var i⟩ ⟨hb, ho + .var i⟩ ⟨h₂, .var i⟩)).run) .skip := rfl
  set w₁ := w - V *ᵥ (Vᵀ *ᵥ w)
  obtain ⟨mid, hmid⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := st.store)
    (p := tag) (b := wb) (off := wo.eval) (xs := Array.ofFn (w₁ - V *ᵥ (Vᵀ *ᵥ w₁)))
    fun i hi => hwlen i (by simpa using hi)
  obtain ⟨fin, hfin⟩ := Store.exists_writeBlock_eq_some_of_getElem?_shape (s := mid) (p := tag)
    (b := hb) (off := ho.eval) (xs := Array.ofFn (Vᵀ *ᵥ w + Vᵀ *ᵥ w₁)) fun i hi => by
      rw [Store.shape_of_writeBlock_eq_some hmid]; exact hhlen i (by simpa using hi)
  obtain ⟨out, hrun', hout⟩ : ∃ out : St P ℝ C,
      exec I (cgs2 tag NE jE Vb wb wo hb ho).run st = some out ∧ out.store = fin := by
    rw [hrun, exec_seq_skip]
    refine exists_exec_alloc I tag jE _ st (fun s => s = fin) fun σ₀ hσ₀ => ?_
    exact exec_cgs2_body I hI tag NE jE Vb wb hb wo ho st σ₀ V w hV hw hwlen hhlen hne hσ₀
      hmid hfin
  exact ⟨out, mid, hrun', hmid, hout ▸ hfin⟩

/-- **One rounded classical Gram–Schmidt pass** (C3): under the standard model, `NLAlib.cgsPass`
succeeds, writes only the reduced vector at (`wb`, `wo`) and the coefficients at (`hb`, `ho`),
and if $\|\mathbf{V}^{\mathsf{T}}\mathbf{V} - \mathbf{I}\|_2 \le \eta_0 \le 1/100$ and
$(N + j + 2)u \le 1/100$, the decoded coefficients $\mathbf{h}_1$ and vector $\mathbf{w}_1$
satisfy, with $c_1$ =
`NLAlib.cgsPassBound`, <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$,
$\|\mathbf{h}_1 - \mathbf{V}^{\mathsf{T}}\mathbf{w}\|$,
$\|\mathbf{w} - \mathbf{V}\mathbf{h}_1 - \mathbf{w}_1\|$,
$\|\mathbf{w}_1 - (\mathbf{w} - \mathbf{V}\mathbf{V}^{\mathsf{T}}\mathbf{w})\| \le
c_1\|\mathbf{w}\|$. [Higham2002, §19.8] for the classical bounds.
Proof: unfold `NLAlib.cgsPass`. The dots:
`NLAlib.Computation.IsRelErrSem.exec_dot_abs_sum_mul_sub_le`
($|\mathbf{e}_h| \le \gamma_N|\mathbf{V}|^{\mathsf{T}}|\mathbf{w}|$), so
$\|\mathbf{e}_h\| \le \gamma_N\|\mathbf{V}\|_{\mathsf F}\|\mathbf{w}\|$
(`NLAlib.norm_toLp_map_abs_mulVec_abs_le`-type comparison and
`NLAlib.frobNorm_le_sqrt_of_specNorm_gram_sub_one_le`). The product:
`NLAlib.Computation.IsRelErrSem.exec_gemv_abs_mulVec_sub_le` ($\gamma_j|\mathbf{V}||\mathbf{h}_1|$).
The literal $-1$ is rounded (`IsRelErrSem.lit_err`) and the update by
`NLAlib.Computation.IsRelErrSem.exec_axpy` ($\gamma_2$, $u$). Collect: the three bounds hold with
$(1+\eta_0)\sqrt j(\gamma_N + \gamma_j) + 4u \le c_1$ (bounds on $\gamma_n$
under
$(N+j+2)u \le 1/100$, $\sqrt j \le \sqrt{j+1}$). Frames from the kernel lemmas and the scoped
allocation. M, about 200 lines. -/
theorem IsRelErrSem.exec_cgsPass {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    {N j : ℕ} (NE jE : IExp ℕ) (hN : NE.eval = N) (hj : jE.eval = j) (Vb wb hb : ℕ)
    (wo ho : IExp ℕ) (st : St P K C) (V : Matrix (Fin N) (Fin j) ℝ) (w : Fin N → ℝ)
    (hV : HoldsDecoded st.store dec tag Vb 0 V)
    (hw : ∀ i : Fin N, ∃ x, st.store.read tag wb (wo.eval + i) = some x ∧ dec tag x = w i)
    (hwlen : ∀ i < N, ∃ len, st.store.shape[wb]? = some (tag, len) ∧ wo.eval + i < len)
    (hhlen : ∀ i < j, ∃ len, st.store.shape[hb]? = some (tag, len) ∧ ho.eval + i < len)
    (hne : hb ≠ wb ∧ hb ≠ Vb ∧ wb ≠ Vb) (hu : u tag < 1) :
    ∃ (out : St P K C) (W : Fin N → K) (Hw : Fin j → K) (mid : Store P K),
      exec I (cgsPass tag NE jE Vb wb wo hb ho).run st = some out ∧
      st.store.writeBlock tag wb wo.eval (Array.ofFn W) = some mid ∧
      mid.writeBlock tag hb ho.eval (Array.ofFn Hw) = some out.store ∧
      ∀ η₀ : ℝ, specNorm (Vᵀ * V - 1) ≤ η₀ → η₀ ≤ 1 / 100 →
        ((N + j + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100 →
        ‖WithLp.toLp 2 ((fun i => dec tag (Hw i)) - Vᵀ *ᵥ w)‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ ∧
        ‖WithLp.toLp 2 (w - V *ᵥ (fun i => dec tag (Hw i)) - fun i => dec tag (W i))‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ ∧
        ‖WithLp.toLp 2 ((fun i => dec tag (W i)) - (w - V *ᵥ (Vᵀ *ᵥ w)))‖ ≤
          cgsPassBound N j (u tag) η₀ * ‖WithLp.toLp 2 w‖ := by
  sorry

/-- **CGS2 is a certified orthogonalization routine** (C6): under the standard model, for
$\eta_0 \le 1/100$, $(N + j + 2)u \le 1/100$ and $c_1 =$ `NLAlib.cgsPassBound` $N\,j\,u\,\eta_0$
(that is, <!-- value cgsPassBound N j u \eta_0 -->$2(1+\eta_0)\sqrt{j+1}\,(N+j+2)\,u$)
$\le 1/100$, `NLAlib.cgs2` meets `NLAlib.Computation.IsOrthRoutine` at
$(\eta_0, 2c_1, 3c_1, 2(\eta_0 + c_1)^2)$ with `pre = True`. No printed source;
`docs/design/Krylov-LanczosReorth.md` §1.3.
Proof: `composable`: `NLAlib.cgs2` is a `scope` of one emitted block, so
`NLAlib.Computation.executionComposable_single` applies (unfold `Builder.scope`, `ContT.run`).
`run`: unfold `NLAlib.cgs2`; first pass by `NLAlib.Computation.IsRelErrSem.exec_cgsPass` into `hb`,
second by
the same lemma into the scratch buffer (fresh handle, disjoint from `Vb`, `wb`, `hb`), the $j$
additions by `IsRelErrSem.bin_err` one cell at a time (`forRange` induction as in
`NLAlib.Computation.exec_forRange_dot_add`), the scratch freed by the scoped allocation
(`NLAlib/Computation/Allocation.lean`), then the frame as two block writes; the guarantee by
`NLAlib.isOrthErr_of_two_passes` with $4u \le c_1$ (from the definition, $j \ge 0$, $N + j + 2
\ge 2$). L, about 300 lines; the frame bookkeeping is the bulk (see
`NLAlib.Computation.IsMatvecErr.exec_apply`
for the block-write pattern). -/
theorem IsRelErrSem.isOrthRoutine_cgs2 {u : P → ℝ} {dec : P → K → ℝ} (I : Interp P ι K C)
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem) (hz : AddsZeroExactly dec I.sem) (tag : P)
    {N j : ℕ} (NE jE : IExp ℕ) (hN : NE.eval = N) (hj : jE.eval = j) (Vb wb hb : ℕ)
    (wo ho : IExp ℕ) {η₀ : ℝ} (hη₀ : 0 ≤ η₀) (hη : η₀ ≤ 1 / 100)
    (hu : ((N + j + 2 : ℕ) : ℝ) * u tag ≤ 1 / 100)
    (hc : cgsPassBound N j (u tag) η₀ ≤ 1 / 100) :
    IsOrthRoutine I dec tag N j η₀ (2 * cgsPassBound N j (u tag) η₀)
      (3 * cgsPassBound N j (u tag) η₀) (2 * (η₀ + cgsPassBound N j (u tag) η₀) ^ 2)
      (fun _ => True) Vb wb hb wo ho (cgs2 tag NE jE Vb wb wo hb ho) := by
  sorry

end Computation

end NLAlib
