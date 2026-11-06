/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.RandomMatrix.Computation.DeflationTargets
public import NLAlib.RandomMatrix.Computation.NewtonSchulzSignTargets
public import NLAlibScaffold.Matrix.Computation.DeflationProgram
public import NLAlibScaffold.Matrix.Computation.InterpMachine
public import NLAlibScaffold.Matrix.Computation.NewtonSchulzSignProgram
public import NLAlibScaffold.RandomMatrix.Computation.ComplexTape

/-!
# The SIGN and DEFLATE targets: transfer of the shallow guarantees (scaffold, blocked on HDIAG)

**This file depends on theorems of the HDIAG stage that are not on this branch** (they are
statements of `NLAlibScaffold/` on `design/hdiag`, being proved on `integrate/hdiag`): the
accuracy of the Newton–Schulz sign algorithm, [Shah2024, Theorem 2.6]
(`FloatMachine.IsAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le` there), and the
failure probability of deflation, [Shah2024, Theorem 3.3]
(`FloatMachine.IsAccurate.measureReal_not_exists_specNorm_mul_sub_deflate_le_le` there). Its
proof sketches name them in prose; its statements are not in the targets file of this stage
(`pilot/compdyn-s1cd-targets.json`) and are dispatched when HDIAG lands. Design note
`docs/design/Computation-SignDeflatePrograms.md`, §5.

The first statement is new for HDIAG: the stopping test of the shallow algorithm passes within
$N_0 + 1$ steps, which the proof of [Shah2024, Theorem 2.6] on `design/hdiag` shows (its step
(2)) but does not state; the program needs it for success. The other two are the proofs of the
proposed targets `NLAlib.MatrixFreeRoundedProbNewtonSchulzSign` and
`NLAlib.MatrixFreeRoundedProbDeflate`: the refinement theorems of this stage turn the shallow
guarantees into guarantees about the registered trees.

## Main results

* `NLAlib.FloatMachine.IsAccurate.exists_le_newtonSchulzTest_iterate`: the shallow test passes.
* `NLAlib.matrixFreeRoundedProbNewtonSchulzSign`, `NLAlib.matrixFreeRoundedProbDeflate`: the
  targets.
-/

@[expose] public section

open scoped Matrix
open MeasureTheory ProbabilityTheory

namespace NLAlib

open Computation

/-- **The Newton–Schulz test passes within the step count**: under the hypotheses of the accuracy
theorem of the Newton–Schulz sign algorithm (the machine contract
`NLAlib.FloatMachine.IsAccurate` $u$ $\tau$ $\Omega$ with product constant $\mu$, $\mu(n) \ge 0$,
$u \ge 0$, $0 \le \tau$, $2n\tau \le 1$, $9(n + 1) \le \Omega$, the stored $\mathbf{A}$ with
Hermitian decoding, $\|\mathbf{A}\|_2 \le \bar b$, every eigenvalue of modulus at least $a > 0$,
$0 < \bar\varepsilon \le 1/2$ and
$640\,n^{3/2}(8 + \mu(n))(N_0 + 1)u \le (a/\bar b)\bar\varepsilon$ for
$N_0 = N(a/(2\bar b), \bar\varepsilon/(16n))$), the stopping test at the computed threshold
$\mathrm{fl}(\bar\varepsilon/\mathrm{fl}(4n))$ passes at some iterate $k \le N_0 + 1$ of the
rounded step from the stored $\mathbf{A}/b$. [Shah2024, proof of Theorem 2.6].
Owner: the HDIAG stage (`integrate/hdiag`), which proves it with Theorem 2.6, or restates that
theorem to return the pass index; not dispatched from COMPDYN.
Proof: step (2) of the proof of the accuracy theorem on `design/hdiag` (the scalar chains of the
eigenvalues reach $\lvert 1 - x^2\rvert \le \varepsilon/(16n)$ within $\lceil N_0 \rceil$ steps,
`NLAlib.newtonSchulzSteps`; the computed test matrix is within $1.21\mu u + u(\cdots)$ of
$\mathbf{A}_k^2 - \mathbf{I}$ and the stored threshold within $(1 \pm u)^2$ of
$\varepsilon/(4n)$), stated separately. L (a share of the HDIAG proof, about 60 lines once that
proof's invariant is a lemma). -/
theorem FloatMachine.IsAccurate.exists_le_newtonSchulzTest_iterate {F : Type*}
    {M : FloatMachine F ℝ ℂ} {dec : F → ℝ} {u τ Ω cN : ℝ} {μ μQ : ℕ → ℝ} {n : ℕ}
    (hM : M.IsAccurate dec u τ Ω μ μQ cN) (hμ : 0 ≤ μ n) (hu₀ : 0 ≤ u) (hτ₀ : 0 ≤ τ)
    (hτ : τ * (2 * n) ≤ 1) (hΩ : 9 * (n + 1) ≤ Ω) {A : Matrix (Fin n) (Fin n) (F × F)}
    (hA : (decodeMatrix dec A).IsHermitian) {a : ℝ} {b ε : F} (ha : 0 < a)
    (hspec : ∀ x ∈ spectrum ℝ (decodeMatrix dec A), a ≤ |x|)
    (hb : specNorm (decodeMatrix dec A) ≤ dec b) (hε : 0 < dec ε) (hε₁ : dec ε ≤ 1 / 2)
    (hu : 640 * n * √(n : ℝ) * (8 + μ n) *
      (newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1) * u ≤ a / dec b * dec ε) :
    ∃ k : ℕ, (k : ℝ) ≤ newtonSchulzSteps (a / (2 * dec b)) (dec ε / (16 * n)) + 1 ∧
      newtonSchulzTest M (M.div ε (M.ofNat (4 * n)))
        ((newtonSchulzRounded M)^[k] (M.hermScale A b)) = true := by
  sorry

/-- **The target of the Newton–Schulz sign algorithm as a program holds**
(`NLAlib.MatrixFreeRoundedProbNewtonSchulzSign`). [Shah2024, Theorem 2.6], for the program.
Proof: fix the data and an interpretation meeting the contracts; let `M` be the machine of the
semantics at `p` (`NLAlib.Computation.ScalarSem.toFloatMachine`) with the routine `mmR` of the
kernel, the floor conversion and the QR routine and samplers of the machine $M_0$ the contracts
provide; `NLAlib.Computation.isAccurate_toFloatMachine` (scaffold) makes it accurate at $u$,
floor $0$, range $\Omega$. The interpretation with the rounded tape has the same semantics and
kernels, so for every $\omega$: the shallow test passes at some $k \le N_0 + 1 \le F$
(`NLAlib.FloatMachine.IsAccurate.exists_le_newtonSchulzTest_iterate`, scaffold), so the run
succeeds (`NLAlib.newtonSchulzSignProg.exists_exec_compiled`, scaffold, with $u < 1$ and
$\bar b \ne 0$ from the hypotheses: $a \le \|\mathbf{A}\|_2 \le \bar b$ by
`Matrix.IsHermitian.eigenvalues_mem_spectrum_real` and `NLAlib.abs_eigenvalue_le_specNorm`-style
bounds, and $640 \cdot 8 \cdot u \le 1/2$); its output is `NLAlib.newtonSchulzSign` on `M`
(`NLAlib.newtonSchulzSignProg.holds_of_exec_compiled`, scaffold, with
`NLAlib.Computation.IsRelErrSem.decidesFlags`), which is within $\bar\varepsilon$ of
$\operatorname{sign}(\mathbf{A})$ by the HDIAG accuracy theorem (Theorem 2.6 there). The failure
set is empty, of measure $0$. M, about 60 lines. -/
theorem matrixFreeRoundedProbNewtonSchulzSign : MatrixFreeRoundedProbNewtonSchulzSign := by
  sorry

/-- **The target of randomized deflation as a program holds**
(`NLAlib.MatrixFreeRoundedProbDeflate`). [Shah2024, Theorem 3.3], for the program.
Proof: fix the data and an interpretation meeting the contracts; let `M` be the machine of the
semantics at `p` with the kernels' routines, the floor conversion, the uniform sampler of $M_0$
and the normal sampler `NLAlib.Computation.ScalarSem.gaussianNormal` of $\rho_{\mathrm{g}} =
\rho(\mathrm{gaussian}, 0, \cdot)$; it is accurate at $u$, floor $0$, range $\Omega$
(`NLAlib.Computation.isAccurate_toFloatMachine` with
`NLAlib.Computation.isNormalSampler_gaussianNormal`, scaffold; the tape contract at range
$2\Omega$ gives `hρ`). For every $\omega$ the run succeeds
(`NLAlib.deflateProg.exists_exec_compiled`, scaffold, $u \le 1$ from $(c + 3)u \le 1/10$), and its
output is `NLAlib.deflate` on the tape machine
(`NLAlib.deflateProg.holds_of_exec_compiled`, scaffold), which by position independence of
$\rho$ and `NLAlib.deflate_tapeNormal_eq_deflate_gaussianNormal` (scaffold) is `NLAlib.deflate`
on `M` with the ideal sample `NLAlib.Computation.tapeComplexMatrix` of $\xi(\omega)$. That sample
has the law `NLAlib.complexGaussianMatrix`
(`NLAlib.Computation.hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw`, scaffold), so the failure set
is contained in the event bounded by the HDIAG deflation theorem (Theorem 3.3 there, with
$\tau = 0$, $c_{\mathrm N} = 2(c + 3)$: its floor conditions hold at $\tau = 0$), and
`MeasureTheory.measureReal_mono` concludes. M, about 70 lines. -/
theorem matrixFreeRoundedProbDeflate : MatrixFreeRoundedProbDeflate := by
  sorry

end NLAlib
