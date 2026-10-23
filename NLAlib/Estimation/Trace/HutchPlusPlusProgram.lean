/-
Copyright (c) 2026 NLAlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NLAlib contributors
-/
module

public import NLAlib.Computation.Dense
public import NLAlib.Computation.Sparse
public import NLAlib.Estimation.Trace.HutchPlusPlusTail
public import NLAlib.Matrix.Factorizations.GramSchmidtProgram
public import NLAlib.RandomMatrix.Tape

/-!
# Hutch++ as a program

`NLAlib.hutchppProg` is Hutch++ as a program over memory buffers: it draws an $N \times k$ sketch
and $N \times \ell$ probes from the tape, forms $\mathbf{Y} = \mathbf{A}\mathbf{S}$ with one oracle
call, orthonormalises $\mathbf{Y}$ in place by rank-revealing modified Gram–Schmidt, projects the
probes in place, forms $\mathbf{A}[\mathbf{Q}\ \mathbf{G}']$ with a second call, and writes
$\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) +
\operatorname{tr}(\mathbf{G}'^{\mathsf{H}}\mathbf{A}\mathbf{G}')/\ell$ into its output cell.

Under exact arithmetic it computes `NLAlib.hutchpp` of the matrices drawn from the tape, with 2
loads, $2k + \ell$ matrix-vector products, the operation counts `NLAlib.hutchppCount` and
$2N(k + \ell) + 4$ cells of memory besides its output (`NLAlib.runsWithin_hutchppProg`). With a
Gaussian tape, the tail bound of Gaussian Hutch++ transfers to the program with no new
probability. With the oracle implemented by a dense matrix or by a matrix in coordinate form, the
substitution theorem gives the totals in arithmetic operations and memory. Design:
`docs/design/Computation.md` (§5, §6).

## Main definitions

* `NLAlib.hutchppProg`, `NLAlib.hutchppCount`.

## Main results

* `NLAlib.runsWithin_hutchppProg`: the realisation.
* `NLAlib.measureReal_not_runsWithin_hutchppProg_le_of_hasLaw_iidSequence`: the Gaussian tail of
  the program that draws its own test matrices.
* `NLAlib.runsWithin_substOracle_hutchppProg_denseImpl`,
  `NLAlib.runsWithin_substOracle_hutchppProg_cooImpl`: dense and sparse Hutch++.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace NLAlib

open Computation Computation.Builder

section Program

variable {P ι VB VI : Type}

/-- **Hutch++ as a program.** It draws an $N \times k$ sketch $\mathbf{S}$ and $N \times \ell$
probes $\mathbf{G}$ from the tape of `d`, forms $\mathbf{Y} = \mathbf{A}\mathbf{S}$ (load 1),
orthonormalises $\mathbf{Y}$ in place by rank-revealing modified Gram–Schmidt into
$\mathbf{Q}$, projects the probes in place,
$\mathbf{G}' = (\mathbf{I} - \mathbf{Q}\mathbf{Q}^{\mathsf{H}})\mathbf{G}$, forms
$\mathbf{A}[\mathbf{Q}\ \mathbf{G}']$ (load 2, batched), and writes
$\operatorname{tr}(\mathbf{Q}^{\mathsf{H}}\mathbf{A}\mathbf{Q}) +
\operatorname{tr}(\mathbf{G}'^{\mathsf{H}}\mathbf{A}\mathbf{G}')/\ell$ into `out`.
[MeyerMuscoMuscoWoodruff2021, Algorithm 1]. -/
def hutchppProg (p : P) (o : ι) (d : Dist) (N k ℓ : IExp VI) (out : Cell VB VI) :
    Builder P ι VB VI Unit := do
  let B ← alloc p (N * (k + ℓ))
  scope do
    let S ← alloc p (N * k)
    forRange (N * k) fun i => ins (.draw p d ⟨S, .var i⟩)
    stmt (.apply o p B 0 S 0 k)
  forRange (N * ℓ) fun i => ins (.draw p d ⟨B, N * k + .var i⟩)
  gramSchmidtProg p N k B
  let t ← alloc p 2
  forRange ℓ fun j => orthAgainst p N B k B (N * (k + .var j)) ⟨t, 0⟩
  let C ← alloc p (N * (k + ℓ))
  stmt (.apply o p C 0 B 0 (k + ℓ))
  ins (.lit p out 0)
  forRange k fun j => do
    dot p ⟨t, 0⟩ B (N * .var j) C (N * .var j) N
    ins (.bin p .add out out ⟨t, 0⟩)
  ins (.lit p ⟨t, 1⟩ 0)
  forRange ℓ fun j => do
    dot p ⟨t, 0⟩ B (N * (k + .var j)) C (N * (k + .var j)) N
    ins (.bin p .add ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.litIdx p ⟨t, 0⟩ ℓ)
  ins (.bin p .div ⟨t, 1⟩ ⟨t, 1⟩ ⟨t, 0⟩)
  ins (.bin p .add out out ⟨t, 1⟩)

end Program

section Statements

variable {𝕜 : Type} [RCLike 𝕜] {P ι : Type} [DecidableEq P]

/-- The counts of `NLAlib.hutchppProg` when $\mathbf{A}\mathbf{S}$ has full column rank, with
$J = k(k-1)/2$: 2 loads, $2k + \ell$ matrix-vector products, $N(k + \ell)$ draws,
$2NJ + 2Nk + 2Nk\ell + N\ell$ multiplications, $2NJ + 2Nk + 2Nk\ell + N\ell + k + \ell + 1$
additions, $Nk + 1$ divisions, $k$ square roots, $NJ + 2Nk + Nk\ell + N\ell$ conjugations,
$J + k\ell$ negations, $J + 3k + k\ell + \ell + 3$ literals and $k$ comparisons. -/
noncomputable def hutchppCount (p : P) (o : ι) (d : Dist) (N k ℓ : ℕ) : OpCount P ι :=
  Finsupp.single (.load p o) 2 + Finsupp.single (.matvec p o) (2 * k + ℓ) +
  Finsupp.single (.draw p d) (N * (k + ℓ)) +
  Finsupp.single (.bin p .mul) (2 * N * k.choose 2 + 2 * N * k + 2 * N * k * ℓ + N * ℓ) +
  Finsupp.single (.bin p .add)
    (2 * N * k.choose 2 + 2 * N * k + 2 * N * k * ℓ + N * ℓ + k + ℓ + 1) +
  Finsupp.single (.bin p .div) (N * k + 1) + Finsupp.single (.un p .sqrt) k +
  Finsupp.single (.un p .conj) (N * k.choose 2 + 2 * N * k + N * k * ℓ + N * ℓ) +
  Finsupp.single (.un p .neg) (k.choose 2 + k * ℓ) +
  Finsupp.single (.lit p) (k.choose 2 + 3 * k + k * ℓ + ℓ + 3) + Finsupp.single (.cmp p) k

/-- **Hutch++ as a program computes Hutch++**: under exact arithmetic over $\Bbbk$, with every
oracle name the matrix $\mathbf{A}$ and the tape $\xi$, and $\ell \ge 1$, the program run from a
single output cell succeeds within the counts `hutchppCount p o d N k ℓ` and
$2N(k + \ell) + 4$ cells besides the output, and its output is
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$, where $\mathbf{S}$ is the $N \times k$
matrix drawn from the tape of `d` from position $0$ and $\mathbf{G}$ the $N \times \ell$ matrix
drawn after it, column-major. No hypothesis on the rank of $\mathbf{A}\mathbf{S}$.
[MeyerMuscoMuscoWoodruff2021, Algorithm 1]; there with the costs stated in matrix-vector
products only.
Result: hutchpp-program -/
theorem runsWithin_hutchppProg (p : P) (o : ι) (d : Dist) {N k ℓ : ℕ} (hℓ : 0 < ℓ)
    (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (exactInterp (fun _ => A) ξ)
      ((hutchppProg p o d (.const N) (.const k) (.const ℓ) ⟨0, .const 0⟩).run)
      (inputState p [Array.replicate 1 none]) (hutchppCount p o d N k ℓ)
      (fun q => if q = p then 2 * N * (k + ℓ) + 4 else 0)
      (fun st => st.store.read p 0 0 =
        some (hutchpp A (tapeMatrix (ξ d) 0 N k) (tapeMatrix (ξ d) (N * k) N ℓ))) := by
  sorry

/-- **The deviation of Hutch++ as a program**: let the tape of the Gaussian distribution be an
i.i.d. sequence of standard Gaussians, $k \ge 1$, $\ell \ge 1$. If $\delta > 0$
and <!-- value subgaussianEmbeddingDim {\cdot 1} r (1/2) (\delta/2) -->
$k \ge 25 \cdot 1^2 (r \log 21 + \log(2/(\delta/2)))/(16C (1/2)^2)$,
with <!-- value subgaussianJLConstant -->$C = 1/36$, then for every real
$N \times N$ matrix $\mathbf{A}$ and every $\tau \ge 0$, with
$\mathbf{E}_r = \mathbf{A} - \llbracket\mathbf{A}\rrbracket_r$, the probability that the program
fails to compute, within the counts `hutchppCount` and $2N(k + \ell) + 4$ cells, a value $v$ with
$\lvert \operatorname{tr}\mathbf{A} - v \rvert < \tau$ is
at most <!-- value subgaussianRangeFinderFactor {\cdot 1} --> <!-- value hansonWrightConstant -->
$$\delta + 2\exp\Bigl(-\frac{1}{196}\min\Bigl(
\frac{\ell\tau^2}{(1 + 5\cdot 1/2)\|\mathbf{E}_r\|_{\mathsf{F}}^2},
\frac{\ell\tau}{\sqrt{1 + 5\cdot 1/2}\,\|\mathbf{E}_r\|_{\mathsf{F}}}\Bigr)\Bigr)\,;$$
the size is `subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2)`, $C$ is `subgaussianJLConstant`, the
factor is `subgaussianRangeFinderFactor 1` and the constant in the exponent is
`hansonWrightConstant`. From `NLAlib.runsWithin_hutchppProg`, the tape laws and the Gaussian tail
`NLAlib.measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix`, through
`NLAlib.Computation.measureReal_not_runsWithin_le`.
[MeyerMuscoMuscoWoodruff2021, Theorem 4 and §5, Algorithm 3]; there with unspecified constants
and for the algorithm, not a program.
Result: hutchpp-program-tail -/
theorem measureReal_not_runsWithin_hutchppProg_le_of_hasLaw_iidSequence
    {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] (p : P) (o : ι)
    {N k ℓ : ℕ} [NeZero k] (hℓ : 0 < ℓ) (A : Matrix (Fin N) (Fin N) ℝ)
    {ξ : Ω → Dist → ℕ → ℝ}
    (hξ : HasLaw (fun ω => ξ ω .gaussian) (iidSequence (gaussianReal 0 1)) μ) {r : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hs : subgaussianEmbeddingDim 1 r (1 / 2) (δ / 2) ≤ k) {τ : ℝ} (hτ : 0 ≤ τ) :
    μ.real {ω | ¬ RunsWithin (exactInterp (fun _ => A) (ξ ω))
      ((hutchppProg p o .gaussian (.const N) (.const k) (.const ℓ) ⟨0, .const 0⟩).run)
      (inputState p [Array.replicate 1 none]) (hutchppCount p o .gaussian N k ℓ)
      (fun q => if q = p then 2 * N * (k + ℓ) + 4 else 0)
      (fun st => ∃ v, st.store.read p 0 0 = some v ∧ |A.trace - v| < τ)} ≤
      δ + 2 * Real.exp (-(hansonWrightConstant *
        min (ℓ * τ ^ 2 / (subgaussianRangeFinderFactor 1 * frobNorm (A - truncatedSVD A r) ^ 2))
          (ℓ * τ / (√(subgaussianRangeFinderFactor 1) * frobNorm (A - truncatedSVD A r))))) := by
  have h := measureReal_abs_trace_sub_hutchpp_ge_le_of_hasLaw_gaussianMatrix A
    (hasLaw_tapeMatrix_of_hasLaw_iidSequence hξ 0 N k)
    (hasLaw_tapeMatrix_of_hasLaw_iidSequence hξ (N * k) N ℓ)
    (indepFun_tapeMatrix_of_hasLaw_iidSequence hξ N k ℓ) hδ (by simpa using hs) hτ
  refine measureReal_not_runsWithin_le (G := fun v => |A.trace - v| < τ)
    (fun ω => runsWithin_hutchppProg p o .gaussian hℓ A (ξ ω)) ?_
  simpa only [not_lt, Fintype.card_fin] using h

/-- **Dense Hutch++**: with the oracle served by `NLAlib.Computation.denseImpl` from the
$N \times N$ matrix $\mathbf{A}$ held as read-only data of $N^2$ cells, under exact arithmetic
and $\ell \ge 1$, the substituted program computes the value of
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$ (the store of an exact run of
`NLAlib.hutchppProg`), with the counts `hutchppCount` in which each matrix-vector product is
replaced by $N^2$ multiplications, additions and reads and $N$ literals and each load costs
nothing, and $2N(k + \ell) + 5 + N^2$ cells of memory besides its output. No printed source.
Result: hutchpp-program-dense -/
theorem runsWithin_substOracle_hutchppProg_denseImpl (p : P) (o : ι) (d : Dist) {N k ℓ : ℕ}
    (hℓ : 0 < ℓ) (A : Matrix (Fin N) (Fin N) 𝕜) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (denseInterp A ξ p)
      (((hutchppProg p o d (.const N) (.const k) (.const ℓ) ⟨0, .const 0⟩).run).substOracle
        fun o p dst dOff src sOff cols => denseImpl (.const N) o p dst dOff src sOff cols)
      ((inputState p [Array.replicate 1 none] : St P 𝕜 (OpCount P ι)).withCnt 0)
      (substCount (denseCost N) (hutchppCount p o d N k ℓ))
      (fun q => (if q = p then 2 * N * (k + ℓ) + 4 else 0) + 1 +
        (denseInterp (ι := ι) A ξ p).romSize q)
      (fun st' => ∃ st : St P 𝕜 (OpCount P ι), st.store.read p 0 0 =
          some (hutchpp A (tapeMatrix (ξ d) 0 N k) (tapeMatrix (ξ d) (N * k) N ℓ)) ∧
        st'.store = st.store ∧ st'.pos = st.pos ∧ st'.cur = st.cur) :=
  RunsWithin.substOracle (I := exactInterp (fun _ => A) ξ) (I' := denseInterp A ξ p) rfl rfl
    (fun _ => rfl) (fun _ => rfl) rfl (fun _ => rfl) (implementsOracle_denseImpl A ξ p) rfl
    (fun q => by simp only [inputState]; exact le_rfl) le_rfl
    (runsWithin_hutchppProg p o d hℓ _ ξ)

/-- **Sparse Hutch++**: with $\mathbf{A}$ in coordinate form, `nnz` stored values held as
read-only data and counted as constant memory, the pattern unrolled into the implementation
`NLAlib.Computation.cooImpl` (its index storage not counted), under exact arithmetic and
$\ell \ge 1$, the substituted program computes the value of
$\mathsf{hutchpp}(\mathbf{A}, \mathbf{S}, \mathbf{G})$ for the matrix `cooMatrix pattern vals`,
with the counts `hutchppCount` in which each matrix-vector product is replaced by `nnz`
multiplications, additions and reads and $N$ literals and each load costs nothing, and
$2N(k + \ell) + 5 + \mathit{nnz}$ cells of memory besides its output. No printed source.
Result: hutchpp-program-sparse -/
theorem runsWithin_substOracle_hutchppProg_cooImpl (p : P) (o : ι) (d : Dist) {N k ℓ : ℕ}
    (hℓ : 0 < ℓ) (pattern : List (ℕ × ℕ)) (hpat : ∀ ij ∈ pattern, ij.1 < N ∧ ij.2 < N)
    (vals : ℕ → 𝕜) (ξ : Dist → ℕ → ℝ) :
    RunsWithin (cooInterp (N := N) pattern vals ξ p)
      (((hutchppProg p o d (.const N) (.const k) (.const ℓ) ⟨0, .const 0⟩).run).substOracle
        fun o p dst dOff src sOff cols => cooImpl (.const N) pattern o p dst dOff src sOff cols)
      ((inputState p [Array.replicate 1 none] : St P 𝕜 (OpCount P ι)).withCnt 0)
      (substCount (cooCost N pattern.length) (hutchppCount p o d N k ℓ))
      (fun q => (if q = p then 2 * N * (k + ℓ) + 4 else 0) + 1 +
        (cooInterp (N := N) (ι := ι) pattern vals ξ p).romSize q)
      (fun st' => ∃ st : St P 𝕜 (OpCount P ι), st.store.read p 0 0 =
          some (hutchpp (cooMatrix pattern vals) (tapeMatrix (ξ d) 0 N k)
            (tapeMatrix (ξ d) (N * k) N ℓ)) ∧
        st'.store = st.store ∧ st'.pos = st.pos ∧ st'.cur = st.cur) :=
  RunsWithin.substOracle (I := exactInterp (fun _ => cooMatrix (N := N) pattern vals) ξ)
    (I' := cooInterp (N := N) pattern vals ξ p) rfl rfl (fun _ => rfl) (fun _ => rfl) rfl
    (fun _ => rfl) (implementsOracle_cooImpl pattern hpat vals ξ p) rfl
    (fun q => by simp only [inputState]; exact le_rfl) le_rfl
    (runsWithin_hutchppProg p o d hℓ _ ξ)

end Statements

end NLAlib
