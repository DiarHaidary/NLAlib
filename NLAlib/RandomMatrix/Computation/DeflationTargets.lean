/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.DeflationProgramTree
public import NLAlib.Matrix.Computation.KernelContracts
public import NLAlib.RandomMatrix.Tape

/-!
# Randomized deflation as a program: the target

The target statement of randomized deflation as a program (proposed, stage COMPDYN S1d; to be
registered in `docs/targets.toml` with the maintainer's approval):
`NLAlib.MatrixFreeRoundedProbDeflate`. The registered tree `NLAlib.deflateProg.compiled`, run
under every semantics meeting the standard model with unbounded exponent, every
matrix-multiplication and QR kernel meeting the normwise contracts of [Shah2024, Definition 1.1]
and [Shah2024, Definition 1.2], and every rounding of the Gaussian tape meeting the tape-rounding
contract, returns an approximate orthonormal basis of the range of a stored matrix close to a
matrix of rank $r$, with the failure probability of [Shah2024, Theorem 3.3]. Its proof transfers
the shallow theorem about `NLAlib.deflate` through the refinement theorems of the design note
`docs/design/Computation-SignDeflatePrograms.md`.

## Main definitions

* `NLAlib.DeflationData`: the declared data and the analysis parameters of the target.
* `NLAlib.MatrixFreeRoundedProbDeflate`: the target.
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

open Computation

/-- **The data of the deflation target** at size $N$ and rank $r$: the stored $N \times N$
matrix $\widetilde{\mathbf{A}}$ of complex pairs (the declared input), the factors
$\mathbf{U}$, $\mathbf{S}$, $\mathbf{V}$ of the rank-$r$ matrix it approximates, its distance
bound $\beta$, and the parameters $t$ (norm tail) and $x$ (small ball) of the failure
probability. -/
structure DeflationData (K : Type) (N r : ℕ) where
  /-- The stored matrix. -/
  A : Matrix (Fin N) (Fin N) (K × K)
  /-- The left factor, with orthonormal columns. -/
  U : Matrix (Fin N) (Fin r) ℂ
  /-- The right factor, with orthonormal columns. -/
  V : Matrix (Fin N) (Fin r) ℂ
  /-- The invertible middle factor. -/
  S : Matrix (Fin r) (Fin r) ℂ
  /-- The bound on the distance of the decoded stored matrix from
  $\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}}$. -/
  β : ℝ
  /-- The norm-tail parameter. -/
  t : ℝ
  /-- The small-ball parameter. -/
  x : ℝ

/-- **The target of randomized deflation as a program**, in the rounded probabilistic model.
For every type of tags $P$ with decidable equality, every type of kernel names $\iota$, every
tag $p$, kernel names `mm`, `qr`, carrier $K$ with decoding `dec`, unit roundoff $u$, range
$\Omega$, constants $\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$ and tape-rounding constant $c$, the
registered tree `deflateProg.compiled p mm qr` satisfies: for all sizes $N$ and $n = (r)$ with
$r \le N$ and every `DeflationData` $d$ (stored $\widetilde{\mathbf{A}}$ at tag $p$ in
declared buffer $0$, interleaved and column-major, declared buffer $1$ of $2Nr$ empty cells),
under every interpretation whose semantics meets the standard model at $u$ with every value in
range (`IsRelErrSem`) and index exact at `dec` up to $2$ (the model's clause), whose kernels
`mm` and `qr` are routines on pairs (`IsMatMulKernel`, `IsQRKernel`, interleaved layout)
meeting `IsMatMulErr` and `IsQRErr` at $u$, floor $0$, range $\Omega$ and constants
$\mu_{\mathrm{MM}}$, $\mu_{\mathrm{QR}}$, and every rounding $\rho$ of the
tape meeting `IsTapeRounding` at $u$, floor $0$, range $2\Omega$ and constant $c$ for every
distribution and independent of the position: if $\mathbf{U}$, $\mathbf{V}$ have orthonormal
columns, $\mathbf{S}$ is invertible, $\|\mathbf{U}\mathbf{S}\mathbf{V}^{\mathsf{H}} -
\widetilde{\mathbf{A}}\|_2 \le \beta \le 1$ (decoded), $t \ge 0$, $x > 0$, $0 \le c$,
$(c + 3)u \le 1/10$, $u \ge 0$, and with
$$\bar m = (\|\mathbf{S}\|_2 + 2)\|\mathbf{S}^{-1}\|_2\,\frac{\sqrt2\,(2\sqrt N + t)}{x} \,,$$
$\bar m\beta \le 1/5$,
$(4\mu_{\mathrm{QR}}(N) + 8\sqrt N\,(c + 3) + 2\mu_{\mathrm{MM}}(N))u \le \beta$ and
$2(\|\mathbf{S}\|_2 + 1)\sqrt2\,(2\sqrt N + t) \le \Omega$, then the probability that the
program, run on the rounded tape $\rho \circ \xi$ for an ideal tape $\xi$ of the tape law, fails,
exceeds the counts `deflateCount p mm qr N r` or $10N^2 + 2Nr + 2$ cells at tag `p` (declared
buffers and scratch; none at other tags, the read-only data counted on top), or ends without an
$N \times r$ stored matrix $\mathbf{Q}$ in declared buffer $1$ such that some unitary
$\mathbf{W}$ has $\|\mathbf{U}\mathbf{W} - \bar{\mathbf{Q}}\|_2 \le 6\bar m\beta$ is at most
$2e^{-t^2/2} + r^2x^2$. [Shah2024, Theorem 3.3], for the program. -/
def MatrixFreeRoundedProbDeflate : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (mm qr : ι) (K : Type) [Inhabited K]
    (dec : P → K → ℝ) (u Ω : ℝ) (μM μQ : ℕ → ℝ) (c : ℝ),
    MatrixFreeRoundedProb p (deflateProg.compiled p mm qr) (fun N n => n 0 ≤ N)
      (fun N n => DeflationData K N (n 0))
      (fun N n d => ![(pairLayout.toArray d.A).map some, Array.replicate (2 * (N * n 0)) none])
      dec (fun _ _ => 2) (fun N n => deflateCount p mm qr N (n 0))
      (fun N n q => if q = p then 10 * (N * N) + 2 * (N * n 0) + 2 else 0)
      (fun _ _ I => IsRelErrSem (fun _ => u) dec (fun _ _ => True) I.sem ∧
        (∃ mmR : MatMulMap (K × K), IsMatMulKernel I mm pairLayout mmR ∧
          IsMatMulErr (decodeComplex (dec p)) u 0 Ω μM mmR) ∧
        ∃ qrR : QRMap (K × K), IsQRKernel I qr pairLayout qrR ∧
          IsQRErr (decodeComplex (dec p)) u 0 Ω μQ qrR)
      (fun ρ => IsTapeRounding dec p u 0 (2 * Ω) (fun _ => c) ρ ∧
        ∀ (g : Dist) (i j : ℕ) (y : ℝ), ρ g i y = ρ g j y)
      (fun N _ d => HasOrthonormalCols d.U ∧ HasOrthonormalCols d.V ∧ IsUnit d.S ∧
        specNorm (d.U * d.S * d.Vᴴ - decodeMatrix (dec p) d.A) ≤ d.β ∧ d.β ≤ 1 ∧ 0 ≤ d.t ∧
        0 < d.x ∧ 0 ≤ c ∧ 0 ≤ u ∧ (c + 3) * u ≤ 1 / 10 ∧
        (specNorm d.S + 2) * specNorm d.S⁻¹ * (√2 * (2 * √(N : ℝ) + d.t)) / d.x * d.β ≤ 1 / 5 ∧
        (4 * μQ N + 4 * √(N : ℝ) * (2 * (c + 3)) + 2 * μM N) * u ≤ d.β ∧
        2 * (specNorm d.S + 1) * (√2 * (2 * √(N : ℝ) + d.t)) ≤ Ω)
      (fun N n d st => ∃ Q : Matrix (Fin N) (Fin (n 0)) (K × K),
        pairLayout.Holds st.store p 1 0 Q ∧ ∃ W : Matrix (Fin (n 0)) (Fin (n 0)) ℂ,
          HasOrthonormalCols W ∧ specNorm (d.U * W - decodeMatrix (dec p) Q) ≤
            6 * ((specNorm d.S + 2) * specNorm d.S⁻¹ * (√2 * (2 * √(N : ℝ) + d.t)) / d.x) * d.β)
      (fun _ n d => 2 * Real.exp (-d.t ^ 2 / 2) + (n 0 : ℝ) ^ 2 * d.x ^ 2)

end NLAlib
