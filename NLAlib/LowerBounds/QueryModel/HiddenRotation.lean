/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import Mathlib.Probability.Independence.Basic
public import NLAlib.Krylov.Basic.BlockSpace
public import NLAlib.LowerBounds.QueryModel.Basic
public import NLAlib.RandomMatrix.Gaussian.Basic

/-!
# The hidden-rotation oracle and Krylov couplings

The hard instances of the matrix–vector lower bounds for linear systems, low-rank approximation
and matrix functions are $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$ with a fixed
$\mathbf{D}$ and a Haar orthogonal $\mathbf{U}$. The lower bounds hold even for the stronger
oracle $\mathbf{x} \mapsto (\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$
([Shamir2026, Section 2]), `hiddenRotationOracle U D`, which reveals the rotated query
$\mathbf{v} = \mathbf{U}^{\mathsf{H}}\mathbf{x}$ besides the product. Its responses are two-sided
queries to $\mathbf{U}$, $(\mathbf{0}, \mathbf{x}) \mapsto \mathbf{U}^{\mathsf{H}}\mathbf{x}$ and
then $(\mathbf{D}\mathbf{v}, \mathbf{0}) \mapsto \mathbf{U}\mathbf{D}\mathbf{v}$, so an algorithm
against it runs as the algorithm `QueryAlgorithm.hiddenRotationSimulation D alg` against
`twoSidedMulVec U`, to which the stabilizer form of deferred decision applies
(`NLAlib.QueryAlgorithm.IsMeasurable.identDistrib_prodMk_mul_of_isRightUnitarilyInvariant`).

A **Krylov coupling** (`IsKrylovCoupling`) is the conclusion of the coupling theorem of the
scaffold: after $p$ passes, the rotated output $\mathbf{U}^{\mathsf{H}}\mathbf{W}$ of the
algorithm lies in the block Krylov space
$\mathcal{K}_{p+1}(\mathbf{D}, [\mathbf{U}^{\mathsf{H}}\mathbf{B}, \mathbf{G}])$ of $\mathbf{D}$,
for a standard Gaussian $\mathbf{G}$ with one column per query and per output column, independent
of the rotated initial data $\mathbf{U}^{\mathsf{H}}\mathbf{B}$. Design note
`docs/design/LowerBounds-HiddenRotationLowerBounds.md`.

## Main definitions

* `NLAlib.hiddenRotationOracle`: $\mathbf{x} \mapsto (\mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}
  \mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$.
* `NLAlib.QueryAlgorithm.hiddenRotationSimulation`, `NLAlib.QueryAlgorithm.hiddenRotationDecode`:
  the `2q`-round two-sided algorithm against $\mathbf{U}$ that runs a `q`-query algorithm against
  the hidden-rotation oracle, and the decoding of its history.
* `NLAlib.IsKrylovCoupling`: a Gaussian block Krylov coupling of a rotated output.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

/-- The **hidden-rotation oracle** of $\mathbf{A} = \mathbf{U}\mathbf{D}\mathbf{U}^{\mathsf{H}}$:
the query $\mathbf{x}$ returns $(\mathbf{A}\mathbf{x}, \mathbf{U}^{\mathsf{H}}\mathbf{x})$, the
product and the query in the hidden coordinates. It is stronger than the matrix–vector oracle,
which is its first component (`QueryAlgorithm.comapResponse Prod.fst`). [Shamir2026, Theorem 1],
the oracle (2) there. -/
def hiddenRotationOracle {𝕜 n : Type*} [Fintype n] [NonUnitalNonAssocSemiring 𝕜] [Star 𝕜]
    (U D : Matrix n n 𝕜) (x : n → 𝕜) : (n → 𝕜) × (n → 𝕜) :=
  ((U * D * Uᴴ) *ᵥ x, Uᴴ *ᵥ x)

namespace QueryAlgorithm

variable {𝕜 n β : Type*} {q : ℕ}

/-- The decoding of the hidden-rotation simulation: from a history of `2 * i` two-sided rounds,
the responses $(\mathbf{A}\mathbf{x}_l, \mathbf{U}^{\mathsf{H}}\mathbf{x}_l)$ of the simulated
algorithm, the first component of the odd round and the second of the even round before it. -/
def hiddenRotationDecode {i : ℕ} (h : Fin (2 * i) → (n → 𝕜) × (n → 𝕜)) :
    Fin i → (n → 𝕜) × (n → 𝕜) :=
  fun l => ((h ⟨2 * l + 1, by have := l.isLt; omega⟩).1, (h ⟨2 * l, by have := l.isLt; omega⟩).2)

/-- The **hidden-rotation simulation**: from an algorithm with `q` queries to
`hiddenRotationOracle U D`, an algorithm with `2q` rounds against `twoSidedMulVec U` with the
same output. Round `2l` is the left query $(\mathbf{0}, \mathbf{x}_l)$, which returns
$\mathbf{v}_l = \mathbf{U}^{\mathsf{H}}\mathbf{x}_l$ in the second component; round `2l + 1` is
the right query $(\mathbf{D}\mathbf{v}_l, \mathbf{0})$, which returns
$\mathbf{U}\mathbf{D}\mathbf{v}_l = \mathbf{A}\mathbf{x}_l$ in the first. What the transcript
reveals about $\mathbf{U}$ is its action on the vectors $\mathbf{v}_l$, $\mathbf{D}\mathbf{v}_l$.
With $\mathbf{D} = \mathbf{I}$ the rounds are those of `QueryAlgorithm.gramSimulation`. -/
def hiddenRotationSimulation [Fintype n] [NonUnitalNonAssocSemiring 𝕜] (D : Matrix n n 𝕜)
    (alg : QueryAlgorithm (n → 𝕜) ((n → 𝕜) × (n → 𝕜)) q β) :
    QueryAlgorithm ((n → 𝕜) × (n → 𝕜)) ((n → 𝕜) × (n → 𝕜)) (2 * q) β where
  query j h :=
    if hj : j % 2 = 0 then
      (0, alg.query (j / 2) (hiddenRotationDecode (h ∘ Fin.castLE (by omega))))
    else
      (D *ᵥ (h ⟨j - 1, by omega⟩).2, 0)
  output h := alg.output (hiddenRotationDecode h)

end QueryAlgorithm

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- A **Krylov coupling** at depth $s$ of a random $n \times k$ matrix $\mathbf{V}$ with initial
block $\mathbf{G}_0$ ($n \times c$) and $\mathbf{D} \in \mathbb{R}^{n \times n}$: a standard
Gaussian $n \times c'$ matrix $\mathbf{G}$, independent of $\mathbf{G}_0$, such that almost
surely the range of $\mathbf{V}$ lies in the block Krylov space
$$\mathcal{K}_s(\mathbf{D}, [\mathbf{G}_0, \mathbf{G}]) = \operatorname{range}[\mathbf{G}_0,
\mathbf{G}, \mathbf{D}\mathbf{G}_0, \mathbf{D}\mathbf{G}, \dots, \mathbf{D}^{s-1}\mathbf{G}_0,
\mathbf{D}^{s-1}\mathbf{G}] \,.$$
So every column of $\mathbf{V}$ is $\sum_j f_j(\mathbf{D})\mathbf{g}_j$ over the columns
$\mathbf{g}_j$ of $[\mathbf{G}_0, \mathbf{G}]$, with polynomials of degree less than $s$. The
coupling theorem of the scaffold gives one for the rotated output
$\mathbf{V} = \mathbf{U}^{\mathsf{H}}\mathbf{W}$ of a $p$-pass algorithm against
`hiddenRotationOracle U D` at depth $p + 1$, with
$\mathbf{G}_0 = \mathbf{U}^{\mathsf{H}}\mathbf{B}$; lower bounds take it as their hypothesis and
need no query model. -/
structure IsKrylovCoupling (μ : Measure Ω) {n c k c' : Type*} [Fintype n] [DecidableEq n]
    [Fintype c] [Fintype k] [Fintype c'] (D : Matrix n n ℝ) (s : ℕ) (G₀ : Ω → Matrix n c ℝ)
    (V : Ω → Matrix n k ℝ) (G : Ω → Matrix n c' ℝ) : Prop where
  /-- The coupled block is a standard Gaussian matrix. -/
  hasLaw_gaussianMatrix : HasLaw G (gaussianMatrix n c') μ
  /-- It is independent of the initial block. -/
  indepFun : IndepFun G₀ G μ
  /-- Almost surely the range of `V` lies in the block Krylov space of `[G₀, G]`. -/
  ae_range_le : ∀ᵐ ω ∂μ, LinearMap.range (V ω).mulVecLin ≤
    blockKrylovSpace D (Matrix.fromCols (G₀ ω) (G ω)) s

end NLAlib
