/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.Primitives

/-!
# Entrywise operations on stored Hermitian matrices

The cheap steps of a dense eigensolver (a diagonal shift, a scaling, the Hermitian part of a
computed product, a trace) touch every entry once. Here they are **built from the scalar
operations of a `NLAlib.FloatMachine`**, real and imaginary parts separately, as IEEE complex
arithmetic does, so their error bounds follow from the machine's contract rather than being
assumed. Hermitian structure is kept by construction: `NLAlib.FloatMachine.hermFrom` computes
the strict upper triangle and the real diagonal and mirrors the rest with the machine's exact
negation, so its decoding is exactly Hermitian whatever the rounding does with signs.

## Main definitions

* `NLAlib.FloatMachine.hermFrom`: a stored Hermitian matrix from its upper triangle and diagonal.
* `NLAlib.FloatMachine.hermShift`, `NLAlib.FloatMachine.hermScale`,
  `NLAlib.FloatMachine.hermAvg`: $\mathbf{X} - c\mathbf{I}$, $\mathbf{X}/c$,
  $(\mathbf{X} + \mathbf{X}^{\mathsf{H}})/c$, stored Hermitian.
* `NLAlib.FloatMachine.negMat`, `NLAlib.FloatMachine.conjTransposeMat`,
  `NLAlib.FloatMachine.identityMat`, `NLAlib.FloatMachine.zeroMat`: exact operations.
* `NLAlib.FloatMachine.traceRe`: the rounded sum of the real parts of the diagonal.

## Main results

Bounds on these operations are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

namespace NLAlib

namespace FloatMachine

variable {F Su Sg : Type*} (M : FloatMachine F Su Sg)

/-- **A stored Hermitian matrix from its upper triangle and diagonal**: the entry $(i, j)$ is
`up i j` for $i < j$, the conjugate (exact negation of the imaginary part) of `up j i` for
$i > j$, and $(\mathrm{dg}(i), 0)$ on the diagonal. -/
def hermFrom {k : ℕ} (up : Fin k → Fin k → F × F) (dg : Fin k → F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  Matrix.of fun i j =>
    if i < j then up i j else if j < i then ((up j i).1, M.neg (up j i).2) else (dg i, M.zero)

/-- **Shift by a stored scalar**, $\mathbf{X} - c\mathbf{I}$ stored Hermitian: the diagonal real
parts are $\mathrm{fl}(\operatorname{Re}\mathbf{X}_{i,i} - c)$, the upper triangle is copied. -/
def hermShift {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) (c : F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  M.hermFrom (fun i j => X i j) fun i => M.sub (X i i).1 c

/-- **Division by a stored scalar**, $\mathbf{X}/c$ stored Hermitian: every part of the upper
triangle and every diagonal real part divided by $c$ and rounded. -/
def hermScale {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) (c : F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  M.hermFrom (fun i j => (M.div (X i j).1 c, M.div (X i j).2 c)) fun i => M.div (X i i).1 c

/-- **The scaled Hermitian part**, $(\mathbf{X} + \mathbf{X}^{\mathsf{H}})/c$ stored Hermitian:
on the upper triangle the parts of $\mathbf{X}_{i,j} + \overline{\mathbf{X}_{j,i}}$ are computed,
rounded, then divided by $c$ and rounded; on the diagonal $2\operatorname{Re}\mathbf{X}_{i,i}/c$
likewise. -/
def hermAvg {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) (c : F) :
    Matrix (Fin k) (Fin k) (F × F) :=
  M.hermFrom
    (fun i j => (M.div (M.add (X i j).1 (X j i).1) c, M.div (M.sub (X i j).2 (X j i).2) c))
    fun i => M.div (M.add (X i i).1 (X i i).1) c

/-- **Entrywise negation** of a stored matrix (exact). -/
def negMat {m n : Type*} (X : Matrix m n (F × F)) : Matrix m n (F × F) :=
  X.map fun z => (M.neg z.1, M.neg z.2)

/-- **The conjugate transpose** of a stored matrix (exact: a transpose and a negation). -/
def conjTransposeMat {m n : Type*} (X : Matrix m n (F × F)) : Matrix n m (F × F) :=
  Matrix.of fun i j => ((X j i).1, M.neg (X j i).2)

/-- **The stored identity matrix.** -/
def identityMat (k : ℕ) : Matrix (Fin k) (Fin k) (F × F) :=
  Matrix.of fun i j => if i = j then (M.one, M.zero) else (M.zero, M.zero)

/-- **The stored zero matrix.** -/
def zeroMat (m n : Type*) : Matrix m n (F × F) :=
  Matrix.of fun _ _ => (M.zero, M.zero)

/-- **The rounded trace of the real parts**: $s_0 = 0$, $s_{i+1} =
\mathrm{fl}(s_i + \operatorname{Re}\mathbf{X}_{i,i})$, from the left. -/
def traceRe {k : ℕ} (X : Matrix (Fin k) (Fin k) (F × F)) : F :=
  (List.finRange k).foldl (fun s i => M.add s (X i i).1) M.zero

end FloatMachine

end NLAlib
