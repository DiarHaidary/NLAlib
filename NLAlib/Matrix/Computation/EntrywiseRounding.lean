/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Entrywise rounding of Hermitian matrices

The cheap steps of a dense eigensolver (a diagonal shift, a scaling, the Hermitian part of a
computed product) touch every entry once and round it. This file models them by a **rounding
function** $\mathrm{fl} : \mathbb{R} \to \mathbb{R}$ applied to the exact result, real and
imaginary parts separately: `NLAlib.IsRoundingFn u τ Ω fl` says that
$\lvert \mathrm{fl}(x) - x \rvert \le u \max(\lvert x \rvert, \tau)$ for
$\lvert x \rvert \le \Omega$. With $\tau = 0$ and no range limit this is the standard model with
unbounded exponent [Higham2002, (2.4)]; the floor $\tau$ (gradual underflow) and the range
$\Omega$ (overflow) are kept so that a bounded-exponent model satisfies the same predicate on
its normal range (design note `docs/design/Eigensolvers-HermitianDiagonalization.md`, §12).

Hermitian structure is kept by construction: `NLAlib.roundHermitian` rounds the upper triangle
and the real diagonal and mirrors the rest, so its output is exactly Hermitian whatever the
rounding does with signs; `NLAlib.roundDiag` rounds only the real parts of the diagonal, the
model of $\mathbf{X} - c\mathbf{I}$ and $\mathbf{I} \pm \mathbf{X}$ computed in place.

## Main definitions

* `NLAlib.IsRoundingFn`: the error contract of a rounding function.
* `NLAlib.roundScalar`: rounding of the real and imaginary parts.
* `NLAlib.roundDiag`, `NLAlib.roundHermitian`: rounded Hermitian matrices.
* `NLAlib.roundedSum`: left-to-right rounded summation.

## Main results

Bounds on these operations are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*}

/-- `IsRoundingFn u τ Ω fl`: **the rounding function `fl` has relative error at most $u$ above
the floor $\tau$ on the range $[-\Omega, \Omega]$**: for every real $x$ with
$\lvert x \rvert \le \Omega$,
$\lvert \mathrm{fl}(x) - x \rvert \le u \max(\lvert x \rvert, \tau)$. At $\tau = 0$ this is the
standard model [Higham2002, (2.4)] for a function of the exact result; $\tau > 0$ is an absolute
error below $\tau$, as gradual underflow gives, and $\Omega$ the overflow threshold. -/
def IsRoundingFn (u τ Ω : ℝ) (fl : ℝ → ℝ) : Prop :=
  ∀ x : ℝ, |x| ≤ Ω → |fl x - x| ≤ u * max |x| τ

/-- **Rounding of a scalar**: the real and imaginary parts of $z$ rounded by $\mathrm{fl}$,
$\mathrm{fl}(\operatorname{Re} z) + \mathrm{fl}(\operatorname{Im} z)\,i$; over $\mathbb{R}$ this
is $\mathrm{fl}(z) + \mathrm{fl}(0) \cdot 0 = \mathrm{fl}(z)$. -/
noncomputable def roundScalar (fl : ℝ → ℝ) (z : 𝕜) : 𝕜 :=
  (fl (RCLike.re z) : 𝕜) + (fl (RCLike.im z) : 𝕜) * RCLike.I

/-- **Rounding of the diagonal**: the matrix with diagonal entries
$\mathrm{fl}(\operatorname{Re} \mathbf{X}_{i,i})$ and off-diagonal entries those of
$\mathbf{X}$. For Hermitian $\mathbf{X}$ it is Hermitian; it is how $\mathbf{X} - c\mathbf{I}$,
$3\mathbf{I} - \mathbf{X}$ and $\tfrac12(\mathbf{I} \pm \mathbf{X})$ are stored when only the
diagonal is computed. -/
noncomputable def roundDiag [DecidableEq n] (fl : ℝ → ℝ) (X : Matrix n n 𝕜) : Matrix n n 𝕜 :=
  Matrix.of fun i j => if i = j then (fl (RCLike.re (X i i)) : 𝕜) else X i j

/-- **Rounding to a Hermitian matrix**: the entries above the diagonal rounded by
`NLAlib.roundScalar`, the diagonal entries $\mathrm{fl}(\operatorname{Re} \mathbf{X}_{i,i})$, and
the entries below the diagonal the conjugates of those above. It is exactly Hermitian for every
$\mathbf{X}$ and every rounding function, and for Hermitian $\mathbf{X}$ it is the entrywise
rounding of $\mathbf{X}$ with its symmetry kept. -/
noncomputable def roundHermitian [LinearOrder n] (fl : ℝ → ℝ) (X : Matrix n n 𝕜) :
    Matrix n n 𝕜 :=
  Matrix.of fun i j =>
    if i < j then roundScalar fl (X i j)
    else if j < i then star (roundScalar fl (X j i))
    else (fl (RCLike.re (X i i)) : 𝕜)

/-- **Rounded summation** of $x_0, \dots, x_{k-1}$ from the left:
$s_0 = 0$, $s_{i+1} = \mathrm{fl}(s_i + x_i)$, and the result is $s_k$. -/
noncomputable def roundedSum (fl : ℝ → ℝ) {k : ℕ} (x : Fin k → ℝ) : ℝ :=
  (List.ofFn x).foldl (fun s y => fl (s + y)) 0

end NLAlib
