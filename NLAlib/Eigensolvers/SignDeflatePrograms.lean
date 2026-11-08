/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Eigensolvers.RandomizedDeflation
public import NLAlib.RandomMatrix.Computation.DeflationTargets
public import NLAlib.Matrix.Computation.NewtonSchulzSign.Accuracy
public import NLAlib.RandomMatrix.Computation.NewtonSchulzSignTargets
public import NLAlib.Matrix.Computation.DeflationProgram
public import NLAlib.Matrix.Computation.NewtonSchulzSignProgram
public import NLAlib.RandomMatrix.Computation.ComplexTape

/-!
# The SIGN and DEFLATE targets: transfer of the shallow guarantees

The proofs of the targets `NLAlib.MatrixFreeRoundedProbNewtonSchulzSign` and
`NLAlib.MatrixFreeRoundedProbDeflate`: the refinement theorems of the Newton–Schulz sign and
deflation programs turn the shallow guarantees into guarantees about the registered trees. They use
the accuracy of the Newton–Schulz sign algorithm, [Shah2024, Theorem 2.6]
(`NLAlib.FloatMachine.IsArithAccurate.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le`),
its step count (`NLAlib.FloatMachine.IsArithAccurate.exists_le_newtonSchulzTest_iterate`: the
shallow test passes within $N_0 + 1$ steps, which the program needs for success), and the failure
probability of deflation, [Shah2024, Theorem 3.3] (in
`NLAlib/Eigensolvers/RandomizedDeflation.lean`). Both need only the arithmetic contract
`NLAlib.FloatMachine.IsArithAccurate` of the machine of the semantics, with the routines the
program calls; the routines and samplers the program does not call are given arbitrary values.

## Main results

* `NLAlib.matrixFreeRoundedProbNewtonSchulzSign`, `NLAlib.matrixFreeRoundedProbDeflate`: the
  targets.
-/

@[expose] public section

open scoped Matrix
open MeasureTheory ProbabilityTheory

namespace NLAlib

open Computation

/-- **The Newton–Schulz sign algorithm as a program, in finite precision** (the target
`NLAlib.MatrixFreeRoundedProbNewtonSchulzSign` holds): the registered tree
`newtonSchulzSignProg.compiled`, run under any interpretation whose semantics meets the standard
model at unit roundoff $u \ge 0$ with every value in range, exact literals up to $1$ and the exact
floor conversion, whose product kernel meets `NLAlib.IsMatMulErr` at $u$ with constant $\mu$,
$\mu(N) \ge 0$, range $9(N + 1) \le \Omega$, on a stored $N \times N$ input with Hermitian
decoding $\mathbf{A}$, $\|\mathbf{A}\|_2 \le b$, every eigenvalue of modulus at least $a > 0$,
$0 < \varepsilon \le 1/2$, $N_0 = N(a/(2b), \varepsilon/(16N))$ (`NLAlib.newtonSchulzSteps`),
$$640\,N^{3/2}\,(8 + \mu(N))\,(N_0 + 1)\,u \le \frac{a}{b}\,\varepsilon$$
and step limit $F \ge N_0 + 1$, succeeds with probability $1$ within its operation and cell counts
and returns a stored $\mathbf{Y}$, the decoding of
$\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$, with
$\|\operatorname{sign}(\mathbf{A}) - \bar{\mathbf{Y}}\|_2 \le \varepsilon$. [Shah2024, Theorem 2.6],
there for the algorithm, not a program.
Result: newton-schulz-sign-rounded-program -/
theorem matrixFreeRoundedProbNewtonSchulzSign : MatrixFreeRoundedProbNewtonSchulzSign := by
  intro P ι _ p mm K _ dec u Ω μ
  refine MatrixFreeRoundedProb.of_exec (fun _ _ _ h => h) ?_ ?_
  · intro N n x I st hI hex
    obtain ⟨F, rfl⟩ : ∃ F, n = ![F] := ⟨n 0, by ext i; fin_cases i; rfl⟩
    obtain ⟨hc, hm⟩ := newtonSchulzSignProg.cnt_le_of_exec_compiled (fun k => congrFun hI k) p N F
      hex
    refine ⟨by simpa [inputState] using hc, fun q => ?_⟩
    have h := hm q
    by_cases hq : q = p
    · subst hq
      simp [inputState, EntryLayout.size_toArray, pairLayout] at h ⊢
      omega
    · simpa [inputState, hq] using h
  intro N n hN x hpre I ρ hidx hC _ _ Ω' _ μ' ξ _
  have hlit : IsExactIntLit dec I.sem 1 := hidx.intLit
  obtain ⟨A, ε, b⟩ := x
  obtain ⟨hherm, hu0, hμ, hΩ, hb, hε, hε₁, a, ha, hspec, hu, hF⟩ := hpre
  obtain ⟨hsem, mmR, hmmK, hmmE⟩ := hC
  have hN' : 0 < N := hN
  -- the program uses neither the QR routine nor the samplers: any values serve
  let qrR : QRMap (K × K) := fun A => (Matrix.of fun _ _ => default, A)
  let unif : K → ℝ → K := fun s _ => s
  let normal : ℂ → K × K := fun _ => default
  set M := I.sem.toFloatMachine p (fun x => ⌊dec p x⌋₊) mmR qrR unif normal with hMdef
  have hM : M.IsArithAccurate (dec p) u 0 Ω μ := isArithAccurate_toFloatMachine Ω hsem hlit p hmmE
  -- the scale `b` is at least `a`, so positive
  have hx := hherm.eigenvalue_mem_spectrum (k := 0) (by simpa using hN')
  have hab : a ≤ dec p b :=
    ((hspec _ hx).trans (hherm.abs_eigenvalue_le_specNorm 0)).trans hb
  have hb₀ : 0 < dec p b := ha.trans_le hab
  -- `u < 1`
  have hN₁ : (1 : ℝ) ≤ N := by exact_mod_cast hN'
  have hsN : 1 ≤ √(N : ℝ) := Real.one_le_sqrt.mpr hN₁
  have hS0 : 0 ≤ newtonSchulzSteps (a / (2 * dec p b)) (dec p ε / (16 * N)) :=
    newtonSchulzSteps_nonneg (by positivity)
      (by rw [div_le_iff₀ (by positivity)]; linarith) (by positivity)
      (by rw [div_le_iff₀ (by positivity)]; nlinarith)
  have hab₁ : a / dec p b * dec p ε ≤ 1 / 2 := by
    have : a / dec p b ≤ 1 := (div_le_one hb₀).mpr hab
    nlinarith [div_pos ha hb₀]
  have hC8 : 5120 ≤ 640 * N * √(N : ℝ) * (8 + μ N) *
      (newtonSchulzSteps (a / (2 * dec p b)) (dec p ε / (16 * N)) + 1) := by
    have h1 : (640 : ℝ) ≤ 640 * N * √(N : ℝ) := by nlinarith
    have h2 : (5120 : ℝ) ≤ 640 * N * √(N : ℝ) * (8 + μ N) := by nlinarith
    nlinarith
  have hu1 : u < 1 := by nlinarith
  -- the test passes within the step limit
  obtain ⟨k, hk, htest⟩ := hM.exists_le_newtonSchulzTest_iterate hμ hu0 le_rfl (by simp)
    (by linarith) hherm ha hspec hb hε hε₁ hu
  have hkF : k ≤ n 0 := by
    have : (k : ℝ) ≤ n 0 := hk.trans hF
    exact_mod_cast this
  have hn : n = ![n 0] := by ext i; fin_cases i; rfl
  have hset : {ω | ¬ ∃ st', (newtonSchulzSignProg.compiled p mm).exec
      { I with tape := fun d i => ρ d i (ξ ω d i) } N n
      (inputState p (List.ofFn (![(pairLayout.toArray A).map some, #[some ε, some b],
        Array.replicate (2 * (N * N)) none]))) = some st' ∧
      ∃ Y : Matrix (Fin N) (Fin N) (K × K), pairLayout.Holds st'.store p 2 0 Y ∧
        specNorm (cfc Real.sign (decodeMatrix (dec p) A) - decodeMatrix (dec p) Y) ≤
          dec p ε} = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun ω hω => hω ?_
    rw [hn]
    obtain ⟨st', h⟩ := newtonSchulzSignProg.exists_exec_compiled (toNat := fun x => ⌊dec p x⌋₊)
      (mmR := mmR) (qrR := qrR) (unif := unif) (normal := normal)
      (I := { I with tape := fun d i => ρ d i (ξ ω d i) }) hmmK hsem hlit p hu1 N (n 0) hN' A ε b
      hb₀.ne' ⟨k, hkF, htest⟩
    refine ⟨st', h, _, newtonSchulzSignProg.holds_of_exec_compiled (toNat := fun x => ⌊dec p x⌋₊)
      (mmR := mmR) (qrR := qrR) (unif := unif) (normal := normal) hmmK p
      (hsem.decidesFlags hlit p) N (n 0) A ε b h, ?_⟩
    exact hM.specNorm_cfc_sign_sub_decodeMatrix_newtonSchulzSign_le hμ hu0 le_rfl (by simp)
      (by linarith) hherm ha hspec hb hε hε₁ hu (by
        have : (k : ℝ) ≤ n 0 := hk.trans hF
        linarith)
  simp only at hset ⊢
  rw [hset, measureReal_empty]

/-- **Randomized deflation as a program, in finite precision** (the target
`NLAlib.MatrixFreeRoundedProbDeflate` holds): the registered tree `deflateProg.compiled`, run under
any interpretation whose semantics meets the standard model at unit roundoff $u \ge 0$ with every
value in range and exact indices, whose kernels meet `NLAlib.IsMatMulErr` and `NLAlib.IsQRErr` at
$u$ with constants $\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$, on a tape of standard complex
Gaussian draws rounded by a position-independent rounding meeting
`NLAlib.Computation.IsTapeRounding` with constant $c \ge 0$, $(c + 3)u \le 1/10$: if
$\mathbf{U}, \mathbf{V} \in \mathbb{C}^{N \times r}$, $r \le N$, have orthonormal columns,
$\mathbf{S}$ is invertible, the stored $\widetilde{\mathbf{A}}$ decodes within $\beta \le 1$ of
$\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$, $t \ge 0$, $x > 0$,
$$\bar m = (\|\mathbf{S}\|_2 + 2)\|\mathbf{S}^{-1}\|_2\,\frac{\sqrt2\,(2\sqrt N + t)}{x} \,,$$
$\bar m\beta \le 1/5$, $(4\mu_{\mathrm{QR}}(N) + 8\sqrt N\,(c + 3) + 2\mu_{\mathrm{MM}}(N))u \le
\beta$ and $2(\|\mathbf{S}\|_2 + 1)\sqrt2\,(2\sqrt N + t) \le \Omega$, then the probability that
the run fails, exceeds its operation and cell counts, or returns a stored $\mathbf{Q}$ (the
decoding of $\mathsf{deflate}(\widetilde{\mathbf{A}}, r)$) with no unitary $\mathbf{W}$ such that
$\|\mathbf{U}\mathbf{W} - \bar{\mathbf{Q}}\|_2 \le 6\bar m\beta$ is at most
$2e^{-t^2/2} + r^2x^2$. [Shah2024, Theorem 3.3], there for the algorithm, not a program.
Result: deflate-rounded-program -/
theorem matrixFreeRoundedProbDeflate : MatrixFreeRoundedProbDeflate := by
  intro P ι _ p mm qr K _ dec u Ω μM μQ c
  refine MatrixFreeRoundedProb.of_exec (fun _ _ _ h => h) ?_ ?_
  · intro N n x I st hI hex
    obtain ⟨r, rfl⟩ : ∃ r, n = ![r] := ⟨n 0, by ext i; fin_cases i; rfl⟩
    obtain ⟨hc, hm⟩ := deflateProg.cnt_le_of_exec_compiled (fun k => congrFun hI k) p N r hex
    refine ⟨by simpa [inputState] using hc, fun q => ?_⟩
    have h := hm q
    by_cases hq : q = p
    · subst hq
      simp [inputState, EntryLayout.size_toArray, pairLayout] at h ⊢
      omega
    · simpa [inputState, hq] using h
  intro N n hr d hpre I ρ hidx hC hρ _ Ω' _ μ' ξ hξ
  have hlit : IsExactIntLit dec I.sem 2 := hidx.intLit
  obtain ⟨hU, hV, hS, hβ, hβ₁, ht, hx, hc, hu0, hcu, hmβ, hu, hΩ⟩ := hpre
  obtain ⟨hsem, ⟨mmR, hmmK, hmmE⟩, qrR, hqrK, hqrE⟩ := hC
  obtain ⟨⟨hρr, -⟩, hρi⟩ := hρ
  set ρg : ℝ → K := ρ .gaussian 0 with hρg
  have hlit1 : IsExactIntLit dec I.sem 1 := fun q j hj => hlit q j (hj.trans (by norm_num))
  have hρg' : ∀ y : ℝ, |y| ≤ 2 * Ω → |dec p (ρg y) - y| ≤ c * u * |y| := fun y hy => by
    have := hρr .gaussian 0 y hy
    rwa [max_eq_left (abs_nonneg y)] at this
  -- deflation uses no uniform sampler: any value serves
  let unif : K → ℝ → K := fun s _ => s
  set M := I.sem.toFloatMachine p (fun x => ⌊dec p x⌋₊) mmR qrR unif
    (I.sem.gaussianNormal p ρg) with hMdef
  have hM : M.IsArithAccurate (dec p) u 0 Ω μM := isArithAccurate_toFloatMachine Ω hsem hlit1 p hmmE
  have hnormal : IsNormalSampler (decodeComplex (dec p)) u (2 * (c + 3)) 0 Ω M.normal :=
    isNormalSampler_gaussianNormal hsem hlit p hρg' hc hu0 hcu
  have hG := hasLaw_tapeComplexMatrix_of_hasLaw_tapeLaw hξ N
  have : IsProbabilityMeasure μ' := hG.isProbabilityMeasure
  have hDP :=
    hM.measureReal_not_exists_specNorm_mul_sub_deflate_le_le_of_hasLaw_complexGaussianMatrix
    hqrE hnormal hr hU hV hS rfl hβ hβ₁ ht hx hmβ hu (by positivity) (by simpa using hx.le) hΩ hG
  have hu1 : u ≤ 1 := by nlinarith
  have hn : n = ![n 0] := by ext i; fin_cases i; rfl
  refine le_trans (measureReal_mono fun ω hω => ?_) hDP
  simp only [Set.mem_ofPred_eq] at hω ⊢
  rintro ⟨W, hW, hWb⟩
  refine hω ?_
  obtain ⟨st', h⟩ := deflateProg.exists_exec_compiled
    (mmR := mmR) (qrR := qrR)
    (I := { I with tape := fun d i => ρ d i (ξ ω d i) }) hmmK hqrK hsem hlit p hu1 N (n 0) d.A
  have hQ := deflateProg.holds_of_exec_compiled (toNat := fun x => ⌊dec p x⌋₊) (mmR := mmR)
    (qrR := qrR) (unif := unif) (I := { I with tape := fun d i => ρ d i (ξ ω d i) })
    hmmK hqrK p N (n 0) d.A h
  have htape : (fun i => ρ .gaussian i (ξ ω .gaussian i)) = fun i => ρg (ξ ω .gaussian i) :=
    funext fun i => hρi .gaussian i 0 _
  have hQ' : pairLayout.Holds st'.store p 1 0
      (deflate M (n 0) d.A (tapeComplexMatrix (ξ ω .gaussian) N)) := by
    rw [hMdef, ← deflate_tapeNormal_eq_deflate_gaussianNormal, ← htape]
    exact hQ
  have key : ∀ A' : Matrix (Fin N) (Fin N) (K × K),
      (deflateProg.compiled p mm qr).exec { I with tape := fun d i => ρ d i (ξ ω d i) } N ![n 0]
        (inputState p [(pairLayout.toArray A').map some, Array.replicate (2 * (N * n 0)) none]) =
          some st' →
      (deflateProg.compiled p mm qr).exec { I with tape := fun d i => ρ d i (ξ ω d i) } N n
        (inputState p [(pairLayout.toArray A').map some, Array.replicate (2 * (N * n 0)) none]) =
          some st' := by
    intro A' hA'; rw [hn]; exact hA'
  exact ⟨st', key _ h, _, hQ', W, hW, hWb⟩

end NLAlib
