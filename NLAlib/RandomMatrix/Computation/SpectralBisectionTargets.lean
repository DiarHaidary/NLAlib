/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.SpectralBisectionProgramTree
public import NLAlib.Matrix.Computation.SpectralBisection
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.RandomMatrix.Tape

/-!
# Randomized spectral bisection as a program: the target

The target statement of randomized spectral bisection as a program (proposed, stage COMPDYN S2b;
to be registered in `docs/targets.toml` with the maintainer's approval):
`NLAlib.MatrixFreeRoundedProbEigh`. The registered tree `NLAlib.eighProg.compiled`, run under
every semantics meeting the standard model with unbounded exponent, exact integer literals, the
exact floor conversion to indices and multiplication that does not enlarge by a factor of modulus
at most one, every matrix-multiplication and QR kernel meeting the normwise contracts of
[Shah2024, Definition 1.1] and [Shah2024, Definition 1.2], and every position-independent
rounding of the tape meeting the tape-rounding contract, returns with probability at least
$1 - \theta$ an approximate diagonalization with residual $2\varepsilon R_0$ and $\mathbf{U}$
within $\varepsilon/3$ of unitary: [Shah2024, Theorem 4.2] for a program of the model of
computation. Its proof transfers the shallow theorem about `NLAlib.eigh` through the refinement
theorems of the design note `docs/design/Computation-EighProgram.md`.

## Main definitions

* `NLAlib.EighData`: the stored input.
* `NLAlib.MatrixFreeRoundedProbEigh`: the target.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- **The stored input of randomized spectral bisection** of size $N$: the stored matrix and the
stored $R_0$, $\varepsilon$, $\beta$. -/
structure EighData (K : Type) (N : ℕ) where
  /-- The stored $N \times N$ matrix of complex pairs. -/
  A : Matrix (Fin N) (Fin N) (K × K)
  /-- The stored bound $R_0$ on the spectral norm. -/
  R₀ : K
  /-- The stored tolerance $\varepsilon$. -/
  ε : K
  /-- The stored accuracy $\beta$ of the sign and deflation steps. -/
  β : K

/-- **The target of randomized spectral bisection as a program**, in the rounded probabilistic
model. For every type of tags $P$ with decidable equality, every type of kernel names $\iota$, every
tag $p$, kernel names `mm`, `qr`, carrier $K$ with decoding `dec`, unit roundoff $u$, range
$\Omega$, kernel constants $\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$, tape-rounding constants $c(d)$
and failure probability $\theta$, the registered tree `eighProg.compiled p mm qr` satisfies, at all
sizes $N$ and $n = (\ell, F)$ (the depth counter and the sign step limit), for every stored input
`x` (declared buffers $0$: the matrix, interleaved and column-major; $1$: $R_0$, $\varepsilon$,
$\beta$; $2$, $3$: $2N^2$ and $N$ empty cells), under every interpretation whose semantics meets the
standard model at $u$ with every value in range (`IsRelErrSem`), exact integer literals up to
$N + 4$ (`IsExactIntLit`), the exact floor conversion (`IsExactToNat`) and `MulShrinks`, whose
kernels are routines on pairs meeting `IsMatMulErr` and `IsQRErr` at $u$, floor $0$, range $\Omega$,
and every rounding $\rho$ of the tape meeting `IsTapeRounding` at range $2\Omega$, independent of
the position and with countable range and measurable fibres in each distribution: if the decoded
matrix is Hermitian with $\|\mathbf{A}\|_2 \le R_0$, and the hypotheses of the shallow [Shah2024,
Theorem 4.2] for `NLAlib.eigh` (`NLAlib/Eigensolvers/SpectralBisection/Global.lean`) hold at the
machine roundoff $u_{\mathrm M} = (c(\mathrm{uniform}) + 1)u$ (the rounded shift adds the tape
rounding of the seed) and normal-sampler constant $c_{\mathrm N} = 2(c(\mathrm{gaussian}) + 3)$,
with $(c(\mathrm{gaussian}) + 3)u \le 1/10$, then the probability that the run fails or ends with
stored $\mathbf{U}$, $\mathbf{d}$ in declared buffers $2$, $3$ that are not an approximate
diagonalization of $\mathbf{A}$ with residual $2\varepsilon R_0$ and singular values within
$\varepsilon/3$ of $1$ is at most $\theta$. [Shah2024, Theorem 4.2], for the program. -/
def MatrixFreeRoundedProbEigh : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (mm qr : ι) (K : Type) [Inhabited K]
    (dec : P → K → ℝ) (u Ω θ : ℝ) (μM μQ : ℕ → ℝ) (c : Dist → ℝ),
    MatrixFreeRoundedProb p (eighProg.compiled p mm qr) (fun _ _ => True)
      (fun N _ => EighData K N)
      (fun N _ x => ![(pairLayout.toArray x.A).map some, #[some x.R₀, some x.ε, some x.β],
        Array.replicate (2 * (N * N)) none, Array.replicate N none])
      (fun N _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧
        IsExactIntLit dec I.sem (N + 4) ∧ IsExactToNat dec I.sem ∧ MulShrinks dec I.sem ∧
        (∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mmR) ∧
        ∃ qrR : QRMap (K × K), IsQRKernel I qr pairLayout qrR ∧
          IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qrR)
      (fun ρ => IsTapeRounding dec p u 0 (2 * Ω) c ρ ∧
        (∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y) ∧
        ∀ g : Dist, (Set.range (ρ g 0)).Countable ∧ ∀ z, MeasurableSet (ρ g 0 ⁻¹' {z}))
      (fun N n x =>
        let uM := (c .uniform + 1) * u
        let cN := 2 * (c .gaussian + 3)
        let ℓ := n 0
        let Nst := newtonSchulzSteps (θ / (32 * N * (N + 1) * ℓ * (ℓ + 1))) (dec p x.β / (16 * N))
        (decodeMatrix (dec p) x.A).IsHermitian ∧
        specNorm (decodeMatrix (dec p) x.A) ≤ dec p x.R₀ ∧ 0 < dec p x.R₀ ∧
        0 < dec p x.ε ∧ dec p x.ε ≤ 2⁻¹ ^ 15 ∧ 0 < θ ∧ θ ≤ 1 ∧ bisectionDepth (dec p x.ε) ≤ ℓ ∧
        0 < dec p x.β ∧
        dec p x.β ≤ dec p x.ε * √θ / (2880 * ℓ * N * √(N : ℝ) *
          (2 * √(N : ℝ) + √(2 * Real.log (16 * N / θ)))) ∧
        0 ≤ u ∧ 0 ≤ c .uniform ∧ 0 ≤ c .gaussian ∧ (c .gaussian + 3) * u ≤ 1 / 10 ∧
        Monotone μM ∧ Monotone μQ ∧ 0 ≤ μM 0 ∧ 0 ≤ μQ 0 ∧
        640 * N * √(N : ℝ) * (8 + μM N) * (Nst + 1) * (16 * N * (N + 1) * ℓ * (ℓ + 1)) * uM ≤
          θ * dec p x.β ∧
        (4 * μQ N + 4 * √(N : ℝ) * (cN + 1) + 2 * μM N + 1) * uM ≤ dec p x.β ∧
        Nst ≤ n 1 ∧
        16 * (2 * dec p x.R₀ + N + 2 * ℓ + √(Real.log (16 * N / θ))) ≤ Ω)
      (fun N _ x st => ∃ (U : Matrix (Fin N) (Fin N) (K × K)) (d : Fin N → K),
        pairLayout.Holds st.store p 2 0 U ∧ (∀ i : Fin N, st.store.read p 3 i = some (d i)) ∧
        IsApproxDiagonalization (decodeMatrix (dec p) x.A) (decodeMatrix (dec p) U)
          (fun i => dec p (d i)) (2 * dec p x.ε * dec p x.R₀) (dec p x.ε / 3))
      (fun _ _ _ => θ)

end NLAlib
