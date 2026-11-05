/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Matrix.Computation.EntrywiseRounding
public import NLAlib.Matrix.Computation.Primitives
public import NLAlib.Matrix.Spectral.HermitianPart

/-!
# The matrix sign function by the Newton–Schulz iteration in finite precision

`NLAlib.newtonSchulzSign mm fl ε b N A` approximates the sign $\operatorname{sign}(\mathbf{A})$
of a nonsingular Hermitian $\mathbf{A}$ with $\|\mathbf{A}\|_2 \le b$ by the inverse-free
iteration $\mathbf{A}_{k+1} = \tfrac12\mathbf{A}_k(3\mathbf{I} - \mathbf{A}_k^2)$ from
$\mathbf{A}_0 = \mathbf{A}/b$, each step two calls of a matrix-multiplication routine `mm`
and entrywise rounding by `fl` ([Shah2024, Algorithm 1]). Each step is made exactly Hermitian by
storing the rounded Hermitian part of the computed product (`NLAlib.roundHermitian`), which
[Shah2024] leaves implicit; the iteration stops when every entry of the computed
$\mathbf{I} - \mathbf{A}_k^2$ has real and imaginary parts at most $\varepsilon/(4n)$ in absolute
value, or after `N` steps.

## Main definitions

* `NLAlib.newtonSchulzRounded`: one rounded step.
* `NLAlib.IsNewtonSchulzConverged`: the stopping test.
* `NLAlib.newtonSchulzLoop`, `NLAlib.newtonSchulzSign`: the iteration and the algorithm.

## Main results

The one-step error and the accuracy of the algorithm are in the design note
`docs/design/Eigensolvers-HermitianDiagonalization.md` (stage HDIAG).
-/

@[expose] public section

open scoped Matrix

namespace NLAlib

variable {𝕜 : Type*} [RCLike 𝕜] {n : ℕ}

/-- **One rounded Newton–Schulz step**: with $\mathbf{X} = \mathrm{mm}(\mathbf{A}, \mathbf{A})$,
$\mathbf{B}$ the matrix $3\mathbf{I} - \mathbf{X}$ with its diagonal rounded
(`NLAlib.roundDiag`) and $\mathbf{Y} = \mathrm{mm}(\mathbf{A}, \mathbf{B})$, the result is the
rounded Hermitian matrix (`NLAlib.roundHermitian`) of
$\tfrac14(\mathbf{Y} + \mathbf{Y}^{\mathsf{H}})$, which in exact arithmetic is
$g(\mathbf{A}) = \tfrac12\mathbf{A}(3\mathbf{I} - \mathbf{A}^2)$.
[Shah2024, (2.4)], there without the Hermitian part.
Algorithm: newton-schulz-sign -/
noncomputable def newtonSchulzRounded (mm : MatMulMap 𝕜) (fl : ℝ → ℝ)
    (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  roundHermitian fl ((2⁻¹ : ℝ) • hermitianPart
    (mm A (roundDiag fl ((3 : ℝ) • (1 : Matrix (Fin n) (Fin n) 𝕜) - mm A A))))

/-- **The Newton–Schulz stopping test** at threshold $\eta$: every entry of $\mathbf{T}$, the
matrix $\mathbf{I} - \mathrm{mm}(\mathbf{A}, \mathbf{A})$ with its diagonal rounded, has real and
imaginary parts of absolute value at most $\eta$. [Shah2024, Algorithm 1], there
$\|\mathbf{T}\|_{\max} \le \eta$; comparisons of stored numbers are exact. -/
def IsNewtonSchulzConverged (mm : MatMulMap 𝕜) (fl : ℝ → ℝ) (η : ℝ)
    (A : Matrix (Fin n) (Fin n) 𝕜) : Prop :=
  ∀ i j, |RCLike.re (roundDiag fl (1 - mm A A) i j)| ≤ η ∧
    |RCLike.im (roundDiag fl (1 - mm A A) i j)| ≤ η

open Classical in
/-- **The Newton–Schulz loop** with at most $N$ steps: return $\mathbf{A}$ if it passes the
stopping test at threshold $\eta$ (`NLAlib.IsNewtonSchulzConverged`) or $N = 0$, and otherwise
continue from the rounded step `NLAlib.newtonSchulzRounded`.
Algorithm: newton-schulz-sign -/
noncomputable def newtonSchulzLoop (mm : MatMulMap 𝕜) (fl : ℝ → ℝ) (η : ℝ) :
    ℕ → Matrix (Fin n) (Fin n) 𝕜 → Matrix (Fin n) (Fin n) 𝕜
  | 0, A => A
  | N + 1, A =>
    if IsNewtonSchulzConverged mm fl η A then A
    else newtonSchulzLoop mm fl η N (newtonSchulzRounded mm fl A)

/-- **The Newton–Schulz sign algorithm**
$\mathsf{newtonSchulzSign}(\mathbf{A}, \varepsilon, b)$ with at most $N$ steps: the loop
`NLAlib.newtonSchulzLoop` at threshold $\varepsilon/(4n)$ from the rounded Hermitian matrix of
$\mathbf{A}/b$. [Shah2024, Algorithm 1], there with no step limit.
Algorithm: newton-schulz-sign -/
noncomputable def newtonSchulzSign (mm : MatMulMap 𝕜) (fl : ℝ → ℝ) (ε b : ℝ) (N : ℕ)
    (A : Matrix (Fin n) (Fin n) 𝕜) : Matrix (Fin n) (Fin n) 𝕜 :=
  newtonSchulzLoop mm fl (ε / (4 * n)) N (roundHermitian fl (b⁻¹ • A))

end NLAlib
