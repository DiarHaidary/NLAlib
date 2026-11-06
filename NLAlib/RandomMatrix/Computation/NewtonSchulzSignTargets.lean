/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.NewtonSchulzSignProgramTree
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.Matrix.Functions.HermitianCalculus
public import NLAlib.Polynomial.Approximation.NewtonSchulz
public import NLAlib.RandomMatrix.Tape
public import Mathlib.Data.Real.Sign

/-!
# The Newton–Schulz sign algorithm as a program: the target

The target statement of the Newton–Schulz sign algorithm as a program (proposed, stage COMPDYN
S1d; to be registered in `docs/targets.toml` with the maintainer's approval):
`NLAlib.MatrixFreeRoundedProbNewtonSchulzSign`. The registered tree
`NLAlib.newtonSchulzSignProg.compiled`, run under every semantics meeting the standard model with
unbounded exponent and every matrix-multiplication kernel meeting the normwise contract of
[Shah2024, Definition 1.1], computes the sign of a stored Hermitian matrix to the accuracy of
[Shah2024, Theorem 2.6], in the rounded probabilistic model with failure probability $0$ (the
program draws nothing). Its proof transfers the shallow theorem about `NLAlib.newtonSchulzSign`
through the refinement theorems of the design note `docs/design/Computation-SignDeflatePrograms.md`.

## Main definitions

* `NLAlib.MatrixFreeRoundedProbNewtonSchulzSign`: the target.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- **The target of the Newton–Schulz sign algorithm as a program**, in the rounded
probabilistic model. For every type of tags $P$ with decidable equality, every type of kernel
names $\iota$, every tag $p$, kernel name `mm`, carrier $K$ with decoding `dec`, unit roundoff
$u$, range $\Omega$ and product constant $\mu$, the registered tree
`newtonSchulzSignProg.compiled p mm` satisfies: for all sizes $N \ge 1$ and $n = (F)$ (the step
limit), every stored $N \times N$ matrix $\mathbf{A}$ of complex pairs and stored $\varepsilon$,
$b$, held at tag $p$ in declared buffers $0$ (interleaved, column-major) and $1$ (the two cells),
with declared buffer $2$ of $2N^2$ empty cells, under every interpretation whose semantics meets
the standard model at $u$ with every value in range (`IsRelErrSem`, unbounded exponent, no
underflow), whose literal $1$ is exact, whose kernel `mm` is a routine on pairs
(`IsMatMulKernel`, interleaved layout) meeting `IsMatMulErr` at $u$, floor $0$, range $\Omega$ and
constant $\mu$, on a carrier that admits a machine meeting `FloatMachine.IsAccurate` at $u$, floor
$0$ and range $\Omega$, and every tape: if the decoding (written $\mathbf{A}$) is Hermitian,
$u \ge 0$, $\mu(N) \ge 0$, $9(N + 1) \le \Omega$, $\|\mathbf{A}\|_2 \le \bar b$,
$0 < \bar\varepsilon \le 1/2$ (decoded values) and there is $a > 0$ below the modulus of every
eigenvalue of $\mathbf{A}$ with, for $N_0 = N(a/(2\bar b), \bar\varepsilon/(16N))$
(`newtonSchulzSteps`),
$$640\,N^{3/2}\,(8 + \mu(N))\,(N_0 + 1)\,u \le \frac{a}{\bar b}\,\bar\varepsilon \quad\text{and}
\quad N_0 + 1 \le F,$$
then with probability $1$ the program succeeds and ends with a stored matrix $\mathbf{Y}$ in
declared buffer $2$ whose decoding satisfies
$\|\operatorname{sign}(\mathbf{A}) - \bar{\mathbf{Y}}\|_2 \le \bar\varepsilon$. [Shah2024,
Theorem 2.6], for the program. -/
def MatrixFreeRoundedProbNewtonSchulzSign : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (mm : ι) (K : Type) [Inhabited K] (dec : P → K → ℝ)
    (u Ω : ℝ) (μ : ℕ → ℝ),
    MatrixFreeRoundedProb p (newtonSchulzSignProg.compiled p mm) (fun N _ => 0 < N)
      (fun N _ => Matrix (Fin N) (Fin N) (K × K) × K × K)
      (fun N _ x => ![(pairLayout.toArray x.1).map some, #[some x.2.1, some x.2.2],
        Array.replicate (2 * (N * N)) none])
      (fun _ _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧
        IsExactIntLit dec I.sem 1 ∧
        (∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μ mmR) ∧
        ∃ (M₀ : FloatMachine K ℝ ℂ) (μM μQ : ℕ → ℝ) (cN : ℝ),
          M₀.IsAccurate (dec p) u 0 Ω μM μQ cN)
      (fun _ => True)
      (fun N n x => (decodeMatrix (dec p) x.1).IsHermitian ∧ 0 ≤ u ∧ 0 ≤ μ N ∧
        9 * (N + 1) ≤ Ω ∧ specNorm (decodeMatrix (dec p) x.1) ≤ dec p x.2.2 ∧
        0 < dec p x.2.1 ∧ dec p x.2.1 ≤ 1 / 2 ∧
        ∃ a : ℝ, 0 < a ∧ (∀ y ∈ spectrum ℝ (decodeMatrix (dec p) x.1), a ≤ |y|) ∧
          640 * N * √(N : ℝ) * (8 + μ N) *
              (newtonSchulzSteps (a / (2 * dec p x.2.2)) (dec p x.2.1 / (16 * N)) + 1) * u ≤
            a / dec p x.2.2 * dec p x.2.1 ∧
          newtonSchulzSteps (a / (2 * dec p x.2.2)) (dec p x.2.1 / (16 * N)) + 1 ≤ n 0)
      (fun N _ x st => ∃ Y : Matrix (Fin N) (Fin N) (K × K), pairLayout.Holds st.store p 2 0 Y ∧
        specNorm (cfc Real.sign (decodeMatrix (dec p) x.1) - decodeMatrix (dec p) Y) ≤
          dec p x.2.1)
      (fun _ _ _ => 0)

end NLAlib
