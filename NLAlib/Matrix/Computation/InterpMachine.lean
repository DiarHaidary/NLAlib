/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.KernelContracts

/-!
# The floating-point machine of a value semantics

A shallow algorithm written over a `NLAlib.FloatMachine` ([Shah2024, Section 1.2]) and a program
of the model of computation compute the same thing when the machine's operations are the
program's instructions. `NLAlib.Computation.ScalarSem.toFloatMachine sem p …` is that machine:
its scalar operations are the operations of the value semantics `sem` at tag `p` (a literal for
$0$, $1$ and each natural number, the four arithmetic operations, negation and the comparison
$\le$), and its black boxes are the routines that the kernel contracts
`NLAlib.Computation.IsMatMulKernel` and `NLAlib.Computation.IsQRKernel` name. A failed operation
reads as `default`; a successful run of a program performs only operations that succeed, so on
such a run the machine and the program agree operation by operation, one rounding each (design
note `docs/design/Computation-SignDeflatePrograms.md`).

The machine's normal sampler is built from the tape as the program builds it:
`NLAlib.Computation.ScalarSem.tapeNormal` multiplies two stored Gaussian draws by the stored
$\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$ (`NLAlib.Computation.ScalarSem.sqrtHalf`), and
`NLAlib.Computation.ScalarSem.gaussianNormal` is the same sampler on an ideal complex Gaussian
sample, for a tape rounding that does not depend on the position.
`NLAlib.Computation.tapeComplexMatrix` is the ideal complex Gaussian matrix that a tape of real
draws defines, and `NLAlib.Computation.tapeIndexMatrix` the positions of its entries.

## Main definitions

* `NLAlib.Computation.ScalarSem.toFloatMachine`: the machine of a semantics and routines.
* `NLAlib.Computation.ScalarSem.DecidesFlags`: the comparison that a loop on a flag cell needs.
* `NLAlib.Computation.ScalarSem.sqrtHalf`, `NLAlib.Computation.ScalarSem.tapeNormal`,
  `NLAlib.Computation.ScalarSem.gaussianNormal`: the normal sampler of a program.
* `NLAlib.Computation.tapeComplexMatrix`, `NLAlib.Computation.tapeIndexMatrix`.

## Main results

The machine contract of `NLAlib.Computation.ScalarSem.toFloatMachine` under the standard model,
and the kernel specifications against it, are in the design note
`docs/design/Computation-SignDeflatePrograms.md` (stage COMPDYN S1c).
-/

@[expose] public section

namespace NLAlib.Computation

variable {P K : Type} [Inhabited K]

/-- **The floating-point machine of the value semantics `sem` at tag `p`**, with the black boxes
`mm`, `qr`, the conversion `toNat` and the samplers `unif`, `normal`: zero, one and the
conversion of a natural number $k$ are the literals $0$, $1$ and $k$; addition, subtraction,
multiplication and division are the binary operations; negation is the unary one; the
comparison is $\le$. A failed operation gives `default` (a failed comparison `false`). -/
def ScalarSem.toFloatMachine {Su Sg : Type*} (sem : ScalarSem P K) (p : P) (toNat : K → ℕ)
    (mm : MatMulMap (K × K)) (qr : QRMap (K × K)) (unif : K → Su → K) (normal : Sg → K × K) :
    FloatMachine K Su Sg where
  zero := (sem.lit p 0).getD default
  one := (sem.lit p 1).getD default
  ofNat k := (sem.lit p (k : ℚ)).getD default
  add x y := (sem.bin p .add x y).getD default
  sub x y := (sem.bin p .sub x y).getD default
  mul x y := (sem.bin p .mul x y).getD default
  div x y := (sem.bin p .div x y).getD default
  neg x := (sem.un p .neg x).getD default
  le x y := (sem.cmp p .le x y).getD false
  toNat := toNat
  mm := mm
  qr := qr
  unif := unif
  normal := normal

/-- **The semantics decides flags** at tag `p`: the literals $0$ and $1$ succeed, and the
equality test tells them apart ($0 \ne 1$, $1 = 1$). A program that keeps a pass or fail flag in a
cell and loops on it needs this. Under the standard model with an exact literal $1$ it holds. -/
def ScalarSem.DecidesFlags (sem : ScalarSem P K) (p : P) : Prop :=
  ∃ z o : K, sem.lit p 0 = some z ∧ sem.lit p 1 = some o ∧ sem.cmp p .eq z o = some false ∧
    sem.cmp p .eq o o = some true

/-- **The stored $\sqrt{1/2}$** of the semantics `sem` at tag `p`:
$\mathrm{fl}(\sqrt{\mathrm{fl}(1/2)})$, from the literals $1$ and $2$ by a division and a square
root, as the program computes it. -/
def ScalarSem.sqrtHalf (sem : ScalarSem P K) (p : P) : K :=
  (sem.un p .sqrt ((sem.bin p .div ((sem.lit p 1).getD default)
    ((sem.lit p ((2 : ℕ) : ℚ)).getD default)).getD default)).getD default

/-- **The normal sampler of a tape** of stored real draws $x$: sample $k$ is
$(\mathrm{fl}(x_{2k}s), \mathrm{fl}(x_{2k+1}s))$ with $s$ the stored $\sqrt{1/2}$
(`NLAlib.Computation.ScalarSem.sqrtHalf`), the real and imaginary parts of a stored complex
Gaussian. -/
def ScalarSem.tapeNormal (sem : ScalarSem P K) (p : P) (x : ℕ → K) : ℕ → K × K := fun k =>
  ((sem.bin p .mul (x (2 * k)) (sem.sqrtHalf p)).getD default,
    (sem.bin p .mul (x (2 * k + 1)) (sem.sqrtHalf p)).getD default)

/-- **The normal sampler of a tape rounding** $\rho$ on an ideal complex sample $z$: the stored
draws $\rho(\sqrt2\operatorname{Re} z)$ and $\rho(\sqrt2\operatorname{Im} z)$ times the stored
$\sqrt{1/2}$, each product rounded. With $z$ the ideal sample $(\xi_{2k} + i\xi_{2k+1})/\sqrt2$
of a tape $\xi$ it is `NLAlib.Computation.ScalarSem.tapeNormal` on the stored tape
$\rho \circ \xi$. -/
noncomputable def ScalarSem.gaussianNormal (sem : ScalarSem P K) (p : P) (ρ : ℝ → K) :
    ℂ → K × K := fun z =>
  ((sem.bin p .mul (ρ (√2 * z.re)) (sem.sqrtHalf p)).getD default,
    (sem.bin p .mul (ρ (√2 * z.im)) (sem.sqrtHalf p)).getD default)

/-- **The ideal complex Gaussian matrix of a tape** of real draws $x$: entry $(i, j)$ of the
$N \times N$ matrix is $(x_{2(i + Nj)} + i\,x_{2(i + Nj) + 1})/\sqrt2$, column-major. -/
noncomputable def tapeComplexMatrix (x : ℕ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℂ :=
  Matrix.of fun i j => ⟨x (2 * (i + N * j)) / √2, x (2 * (i + N * j) + 1) / √2⟩

/-- **The sample positions** of an $N \times N$ matrix drawn column-major: entry $(i, j)$ is
sample $i + Nj$ (its two real draws at tape positions $2(i + Nj)$ and $2(i + Nj) + 1$). -/
def tapeIndexMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℕ :=
  Matrix.of fun i j => i + N * j

end NLAlib.Computation
