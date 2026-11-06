/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.EntrywiseRounding

/-!
# The matrix sign function by the Newton–Schulz iteration on a floating-point machine

`NLAlib.newtonSchulzSign M ε b N A` approximates the sign $\operatorname{sign}(\mathbf{A})$ of a
stored nonsingular Hermitian $\mathbf{A}$ with $\|\mathbf{A}\|_2 \le b$ by the inverse-free
iteration $\mathbf{A}_{k+1} = \tfrac12\mathbf{A}_k(3\mathbf{I} - \mathbf{A}_k^2)$ from
$\mathbf{A}_0 = \mathbf{A}/b$ ([Shah2024, Algorithm 1]), written over a `NLAlib.FloatMachine`:
two black-box products per step and the entrywise operations of
`NLAlib/Matrix/Computation/EntrywiseRounding.lean`. Each step stores the rounded Hermitian part
of the computed product, which [Shah2024] leaves implicit; the threshold $\varepsilon/(4n)$ of
the stopping test is computed by the machine; the iteration stops when every part of every entry
of the computed $\mathrm{mm}(\mathbf{A}_k, \mathbf{A}_k) - \mathbf{I}$ is at most the threshold
in absolute value, or after $N$ steps. The definitions are computable: they use the machine and
`ℕ` only.

## Main definitions

* `NLAlib.newtonSchulzRounded`: one step.
* `NLAlib.newtonSchulzTest`: the stopping test.
* `NLAlib.newtonSchulzLoop`, `NLAlib.newtonSchulzSign`: the iteration and the algorithm.

## Main results

The one-step error and the accuracy of the algorithm are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

namespace NLAlib

variable {F Su Sg : Type*} {n : ℕ}

/-- **One rounded Newton–Schulz step** on the machine `M`: with $\mathbf{X} =
\mathrm{mm}(\mathbf{A}, \mathbf{A})$ and $\mathbf{B} = -(\mathbf{X} - 3\mathbf{I})$ (rounded
shift, exact negation), the result is the stored Hermitian
$(\mathbf{Y} + \mathbf{Y}^{\mathsf{H}})/4$ for $\mathbf{Y} = \mathrm{mm}(\mathbf{A}, \mathbf{B})$
(`NLAlib.FloatMachine.hermAvg`), which in exact arithmetic is
$g(\mathbf{A}) = \tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$. [Shah2024, (2.4)], there
without the Hermitian part.
Algorithm: newton-schulz-sign -/
def newtonSchulzRounded (M : FloatMachine F Su Sg) (A : Matrix (Fin n) (Fin n) (F × F)) :
    Matrix (Fin n) (Fin n) (F × F) :=
  M.hermAvg (M.mm A (M.negMat (M.hermShift (M.mm A A) (M.ofNat 3)))) (M.ofNat 4)

/-- **The Newton–Schulz stopping test** at the stored threshold $\eta$: every real and imaginary
part of every entry of $\mathbf{T} = \mathrm{mm}(\mathbf{A}, \mathbf{A}) - \mathbf{I}$ (rounded
shift) lies in $[-\eta, \eta]$, by the machine's comparisons. [Shah2024, Algorithm 1], there
$\|\mathbf{I} - \mathbf{T}\|_{\max} \le \eta$. -/
def newtonSchulzTest (M : FloatMachine F Su Sg) (η : F) (A : Matrix (Fin n) (Fin n) (F × F)) :
    Bool :=
  let T := M.hermShift (M.mm A A) M.one
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    M.le (M.neg η) (T i j).1 && M.le (T i j).1 η && M.le (M.neg η) (T i j).2 && M.le (T i j).2 η

/-- **The Newton–Schulz loop** with at most $N$ steps: return $\mathbf{A}$ if it passes the test
at threshold $\eta$ (`NLAlib.newtonSchulzTest`) or $N = 0$, and otherwise continue from the
rounded step `NLAlib.newtonSchulzRounded`.
Algorithm: newton-schulz-sign -/
def newtonSchulzLoop (M : FloatMachine F Su Sg) (η : F) :
    ℕ → Matrix (Fin n) (Fin n) (F × F) → Matrix (Fin n) (Fin n) (F × F)
  | 0, A => A
  | N + 1, A =>
    if newtonSchulzTest M η A then A else newtonSchulzLoop M η N (newtonSchulzRounded M A)

/-- **The Newton–Schulz sign algorithm** $\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$
with at most $N$ steps, for stored $\varepsilon$ and $b$: the loop `NLAlib.newtonSchulzLoop` at
the computed threshold $\mathrm{fl}(\varepsilon/\mathrm{fl}(4n))$ from the stored Hermitian
$\mathbf{A}/b$ (`NLAlib.FloatMachine.hermScale`). [Shah2024, Algorithm 1], there with no step
limit.
Algorithm: newton-schulz-sign -/
def newtonSchulzSign (M : FloatMachine F Su Sg) (ε b : F) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) (F × F)) : Matrix (Fin n) (Fin n) (F × F) :=
  newtonSchulzLoop M (M.div ε (M.ofNat (4 * n))) N (M.hermScale A b)

end NLAlib
