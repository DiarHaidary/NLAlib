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
  sorry

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
  sorry

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
  sorry

namespace Computation

variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]

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
  sorry

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
