/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Estimation.Trace.HutchPlusPlusProgramTree
public import NLAlib.Estimation.Trace.HutchPlusPlusTail
public import NLAlib.RandomMatrix.Tape

/-!
# Hutch++ as a program: the targets

The target statements of Hutch++ as a program, each about a tree of
`NLAlib/Estimation/Trace/HutchPlusPlusProgramTree.lean`:
* `NLAlib.MatrixFreeHutchpp`: the registered tree `NLAlib.hutchppProg.compiled` computes
  `NLAlib.hutchpp` of the matrices it draws, in the matrix-free model;
* `NLAlib.MatrixFreeProbHutchpp`: the Gaussian tail of the same tree, in the probabilistic
  matrix-free model;
* `NLAlib.StoredEntriesDenseHutchpp`: the dense tree `NLAlib.hutchppProg.compiledDense`, in the
  stored-entries model;
* `NLAlib.StoredEntriesCooHutchpp`: the sparse tree `NLAlib.hutchppProg.compiledCoo` of a public
  pattern, in the stored-entries model.

The statements are the library's, reviewed and registered in `docs/targets.toml`; a change to
one, or to a definition it unfolds to, needs the maintainer's approval (CONTRIBUTING §11). Their
proofs are in `NLAlib/Estimation/Trace/HutchPlusPlusProgram.lean`. Design:
`docs/design/Computation.md` (F1, F8).

## Main definitions

* `NLAlib.hutchppCount`: the operation counts of the program.
* `NLAlib.MatrixFreeHutchpp`, `NLAlib.MatrixFreeProbHutchpp`: the matrix-free targets.
* `NLAlib.StoredEntriesDenseHutchpp`, `NLAlib.StoredEntriesCooHutchpp`: the stored-entries
  targets.
-/

@[expose] public section

open MeasureTheory
open scoped Matrix

namespace NLAlib

open Computation

/-- The counts of `NLAlib.hutchppProg` when $\mathbf{A}\mathbf{S}$ has full column rank, with
$J = k(k-1)/2$: 2 loads, $2k + \ell$ matrix-vector products, $N(k + \ell)$ draws,
$2NJ + 2Nk + 2Nk\ell + N\ell$ multiplications, $2NJ + 2Nk + 2Nk\ell + N\ell + k + \ell + 1$
additions, $Nk + 1$ divisions, $k$ square roots, $NJ + 2Nk + Nk\ell + N\ell$ conjugations,
$J + k\ell$ negations, $J + 3k + k\ell + \ell + 3$ literals and $k$ comparisons. -/
noncomputable def hutchppCount {P ι : Type} (p : P) (o : ι) (d : Dist) (N k ℓ : ℕ) :
    OpCount P ι :=
  Finsupp.single (.load p o) 2 + Finsupp.single (.matvec p o) (2 * k + ℓ) +
  Finsupp.single (.draw p d) (N * (k + ℓ)) +
  Finsupp.single (.bin p .mul) (2 * N * k.choose 2 + 2 * N * k + 2 * N * k * ℓ + N * ℓ) +
  Finsupp.single (.bin p .add)
    (2 * N * k.choose 2 + 2 * N * k + 2 * N * k * ℓ + N * ℓ + k + ℓ + 1) +
  Finsupp.single (.bin p .div) (N * k + 1) + Finsupp.single (.un p .sqrt) k +
  Finsupp.single (.un p .conj) (N * k.choose 2 + 2 * N * k + N * k * ℓ + N * ℓ) +
  Finsupp.single (.un p .neg) (k.choose 2 + k * ℓ) +
  Finsupp.single (.lit p) (k.choose 2 + 3 * k + k * ℓ + ℓ + 3) + Finsupp.single (.cmp p) k

/-- **The target of Hutch++ as a program**, in the matrix-free model. For every type of tags $P$
with decidable equality, every type of oracle names $\iota$, every tag $p$, oracle name $o$ and
distribution $d$ and every `RCLike` field $\Bbbk$, the registered tree
`hutchppProg.compiled p o d` satisfies: for all sizes $N$ and $n = (k, \ell)$ with $\ell \ge 1$,
every $N \times N$ matrix $\mathbf{A}$ over $\Bbbk$ (every oracle name means $\mathbf{A}$) and
every tape $\xi$, under exact arithmetic, run from a state holding only one declared output
cell (empty) at tag $p$, the program succeeds within the counts `hutchppCount p o d N k ℓ` and
$2N(k + \ell) + 4$ cells at tag $p$ besides the output (none at any other tag), and its output is
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the $N \times k$
matrix drawn from the tape of $d$ from position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix
drawn after it, column-major. No hypothesis on the rank of $\mathbf{A}\mathbf{S}$. -/
def MatrixFreeHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (𝕜 : Type) [RCLike 𝕜],
    MatrixFree (𝕜 := 𝕜) p (hutchppProg.compiled p o d) (fun _ n => 0 < n 1) (fun _ _ => Unit)
      (fun _ _ _ => ![Array.replicate 1 none]) (fun N n => hutchppCount p o d N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun N n _ A ξ st => st.store.read p 0 0 = some
        (hutchpp A (tapeMatrix (ξ d) 0 N (n 0)) (tapeMatrix (ξ d) (N * n 0) N (n 1))))

/-- **The target of the deviation of Hutch++ as a program**, in the probabilistic matrix-free
model, for the program that draws its own Gaussian test matrices. For every type of tags $P$ with
decidable equality, every type of oracle names $\iota$, every tag $p$ and oracle name $o$, every
rank $r$, every $\delta > 0$ and every $\tau \ge 0$, the registered tree
`hutchppProg.compiled p o .gaussian` satisfies: let the tape have the law of the tape
(`tapeLaw`: the tape of the Gaussian distribution an i.i.d. sequence of standard Gaussians,
independent of the others); for all sizes $N$ and $n = (k, \ell)$ with $k \ge 1$, $\ell \ge 1$
and <!-- value subgaussianEmbeddingDim {\cdot 1} r (1/2) (\delta/2) -->
$k \ge 25 \cdot 1^2 (r \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, and every real $N \times N$ matrix
$\mathbf{A}$ (every oracle name means $\mathbf{A}$), with
$\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, the probability that the
program, run under exact arithmetic from a state holding only one declared output cell at tag
$p$, fails to compute, within the counts `hutchppCount p o .gaussian N k ℓ` and
$2N(k + \ell) + 4$ cells at tag $p$ besides the output, a value $v$ with
$\lvert \operatorname{tr}\mathbf{A} - v \rvert < \tau$ is
at most <!-- value subgaussianRangeFinderFactor {\cdot 1} --> <!-- value hansonWrightConstant -->
$$\delta + 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{(1 + 5\cdot 1/2)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{\sqrt{1 + 5\cdot 1/2}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor 1` and the constant in the exponent is
`hansonWrightConstant`. -/
def MatrixFreeProbHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (r : ℕ) (δ : ℝ), 0 < δ → ∀ τ : ℝ, 0 ≤ τ →
    MatrixFreeProb (𝕜 := ℝ) p (hutchppProg.compiled p o .gaussian)
      (fun _ n => 0 < n 0 ∧ 0 < n 1 ∧ subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ n 0)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none])
      (fun N n => hutchppCount p o .gaussian N (n 0) (n 1))
      (fun N n q => if q = p then 2 * N * (n 0 + n 1) + 4 else 0)
      (fun _ _ _ A st => ∃ v, st.store.read p 0 0 = some v ∧ |A.trace - v| < τ)
      (fun _ n _ A => δ + 2 * Real.exp (-(hansonWrightConstant *
        min (n 1 * τ ^ 2 / (subgaussianRangeFinderFactor 1 * frobNorm (A - truncatedSVD A r) ^ 2))
          (n 1 * τ / (√(subgaussianRangeFinderFactor 1) * frobNorm (A - truncatedSVD A r))))))

/-- **The target of dense Hutch++**, in the stored-entries model. For every type of tags $P$ with
decidable equality, every type of oracle names $\iota$, every tag $p$, oracle name $o$ and
distribution $d$ and every `RCLike` field $\Bbbk$, the registered tree
`hutchppProg.compiledDense p o d` (Hutch++ with its oracle calls served by
`NLAlib.Computation.denseImpl`) satisfies: for all sizes $N$ and $n = (k, \ell)$ with
$\ell \ge 1$, all entries $v$, of which the first $N^2$ are the read-only data, so that the matrix
is $\mathbf{A} = (v_{i + Nj})_{i, j}$ (column-major), and every tape $\xi$, under exact
arithmetic with no oracle, run from a state holding only one declared output cell at tag $p$,
the program succeeds within the counts `hutchppCount p o d N k ℓ` in which each matrix-vector
product is replaced by $N^2$ multiplications, additions and reads and $N$ literals and each load
costs nothing (`substCount (denseCost N)`), and $2N(k + \ell) + 5 + N^2$ cells at tag $p$
besides the output, counting the $N^2$ read-only entries (one cell at any other tag), and its
output is $\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the
$N \times k$ matrix drawn from the tape of $d$ from position $0$ and $\mathbf{G}$ the
$N \times \ell$ matrix drawn after it, column-major. -/
def StoredEntriesDenseHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (𝕜 : Type) [RCLike 𝕜],
    StoredEntries (𝕜 := 𝕜) p (hutchppProg.compiledDense p o d) (fun _ n => 0 < n 1)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none]) (fun N _ => N * N)
      (fun N n => substCount (denseCost N) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then N * N else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (Matrix.of fun (i j : Fin N) => vals (i + N * j)) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1))))

/-- **The target of sparse Hutch++** for a public COO pattern, in the stored-entries model. For
every type of tags $P$ with decidable equality, every type of oracle names $\iota$, every tag
$p$, oracle name $o$ and distribution $d$, every pattern (a list of positions $(i, j)$, unrolled
into the program, its index storage not counted) and every `RCLike` field $\Bbbk$, the tree
`hutchppProg.compiledCoo p o d pattern` (Hutch++ with its oracle calls served by
`NLAlib.Computation.cooImpl`; one tree per pattern) satisfies: for all sizes $N$ and
$n = (k, \ell)$ with $\ell \ge 1$ and every position of the pattern in $[0, N)^2$, all values $v$,
of which the first $\mathit{nnz}$ (the length of the pattern) are the read-only data, so that the
matrix is `cooMatrix pattern v` (entry $(i, j)$ the sum of the values at the pattern's entries at
$(i, j)$), and every tape $\xi$, under exact arithmetic with no oracle, run from a state holding
only one declared output cell at tag $p$, the program succeeds within the counts
`hutchppCount p o d N k ℓ` in which each matrix-vector product is replaced by $\mathit{nnz}$
multiplications, additions and reads and $N$ literals and each load costs nothing
(`substCount (cooCost N nnz)`), and $2N(k + \ell) + 5 + \mathit{nnz}$ cells at tag $p$ besides
the output, counting the read-only values (one cell at any other tag), and its output is
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{A}$ is
`cooMatrix pattern v`, $\mathbf{S}$ the $N \times k$ matrix drawn from the tape of $d$ from
position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix drawn after it, column-major. -/
def StoredEntriesCooHutchpp : Prop :=
  ∀ (P ι : Type) [DecidableEq P] (p : P) (o : ι) (d : Dist) (pattern : List (ℕ × ℕ))
    (𝕜 : Type) [RCLike 𝕜],
    StoredEntries (𝕜 := 𝕜) p (hutchppProg.compiledCoo p o d pattern)
      (fun N n => 0 < n 1 ∧ ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N)
      (fun _ _ => Unit) (fun _ _ _ => ![Array.replicate 1 none]) (fun _ _ => pattern.length)
      (fun N n => substCount (cooCost N pattern.length) (hutchppCount p o d N (n 0) (n 1)))
      (fun N n q => (if q = p then 2 * N * (n 0 + n 1) + 4 else 0) + 1 +
        if q = p then pattern.length else 0)
      (fun N n _ vals ξ st => st.store.read p 0 0 = some
        (hutchpp (cooMatrix pattern vals) (tapeMatrix (ξ d) 0 N (n 0))
          (tapeMatrix (ξ d) (N * n 0) N (n 1))))

end NLAlib
