# Connecting Krylov guarantees to implementations

Design, 2026-11-04. User request: a library-wide pass linking algorithmic theory to particular
implementations. The coverage inventory is in `Implementation-Coverage.md`; this note owns the
Lanczos and integration interfaces. CG and rounded normalization have separate reviewed notes.
The stored and oracle CG/Lanczos exact targets now have complete library proofs. Stored CG and Lanczos
also have complete rounded execution-to-run/backward theorems; see the
[integration record](Krylov-Implementation-Integration.md). The implementation
interfaces below are goals unless identified there as completed.

## Required chain and scope

One fixed operation order is written in the existing Computation language. Its compiled tree
must be shown to execute that order. Exact arithmetic connects its outputs to the existing
mathematical recurrence; scalar rounding contracts connect the same tree's decoded outputs to
`CGRun` or `LanczosRun`. The existing stability theorems are then applied to those outputs.
Concrete rounding semantics already include `gridSem` (round-to-nearest binary grid, unbounded
exponent). Its standard-model certificate is proved. `Float` remains an executable test
interpreter, with no IEEE format certificate. Samplers, general matrix-function postprocessing
and bounded-exponent range invariants remain separate explicit obligations.

Pure matrix and approximation lemmas are reusable theory; the implementation obligation applies
to an algorithm output named in a guarantee. A recurrence satisfying local error assumptions is
not by itself evidence that a particular program satisfies them. No new theorem may assume its
desired local error bounds as an alleged execution-to-model proof.

## Lanczos operation order

Paige order, matching `lanczosStep` and `LanczosRun`: initialize by the existing `nrm2` followed
by `rscl`; for each step compute a matvec, subtract the previous-vector term, take the inner
product for alpha, subtract the current-vector term, run `nrm2`, and divide componentwise when
the norm is nonzero. The zero-norm branch writes a zero next column and performs no division.
The buffers contain the input vector, computed basis, alpha and beta arrays, and computed input
norm, and the final previous vector. The implementation records the actual rounded input norm; it never assumes exact initial
normalization. Guarded zero continuation agrees with the existing total exact recurrence.
The active finite-precision prefix stops at the first zero off-diagonal coefficient; zero input
is handled without inventing a positive-length `LanczosRun`.

The selected stored-matrix tree loads the column-major ROM matrix into one scoped buffer,
then runs the existing `gemv` kernel. Its normwise rounded execution bounds come from
`Matrix/Computation/BLAS.lean`, with explicit dimension and matrix dependence. This fixes the
actual nested-loop arithmetic to be connected to the local-error run.

## Initial-direction and output transfer

The baseline scaled function theorem assumes
`b = ‖WithLp.toLp 2 b‖ • L.normalizedV 1`. Componentwise rounded division generally changes
the initial direction, so this equality is not an execution invariant. Add a compositional
transfer in `Krylov/FinitePrecision/LanczosFunctions.lean`:

```lean
theorem LanczosRun.norm_cfc_mulVec_sub_le_of_norm_sub_smul_le
    (L : LanczosRun n k) {a a' M E s τ ζ : ℝ} {f : ℝ → ℝ}
    (hs : spectrum ℝ L.H ⊆ Set.Icc a a')
    (hM : 0 ≤ M) (hf : ∀ x ∈ Set.Icc a a', |f x| ≤ M)
    (hs0 : 0 ≤ s)
    (hE : ‖WithLp.toLp 2
      (cfc f L.H *ᵥ L.normalizedV 1 - L.functionApprox f)‖ ≤ E)
    (b y : Fin n → ℝ)
    (hinit : ‖WithLp.toLp 2 (b - s • L.normalizedV 1)‖ ≤ τ)
    (hpost : ‖WithLp.toLp 2 (s • L.functionApprox f - y)‖ ≤ ζ) :
    ‖WithLp.toLp 2 (cfc f L.H *ᵥ b - y)‖ ≤ M * τ + s * E + ζ
```

This costs only the function magnitude, not a residual-to-error condition-number conversion.
The bounded-function precision theorem supplies `E`; a kernel-level initialization certificate
supplies `τ` and the actually computed scale `s`; a concrete postprocessor or its explicit error
certificate supplies `ζ`. This transfer adds no interface, new arithmetic or named bound.

## Target approval and integration

The programs guide (`docs/contributing/programs.md`) requires every new top-level program to have
a registered compiled tree and a maintainer-approved target. The concrete proposals were first
checked outside `NLAlib`.
The maintainer approved both exact statements and identified programs on 2026-11-04. Their
unchanged trees, counts and target bodies are now in the library with the complete proofs
`storedEntriesConjugateGradient` and `storedEntriesLanczos`. The separately approved oracle
variants add `matrixFreeConjugateGradient` and `matrixFreeLanczos`; the registry now has nine
targets and seven trees. Every previous registry entry, allowlist, ratchet and pin remains
unchanged. The naming-check notation correction was separately approved.

Stored CG and Lanczos rounded execution/backward corollaries are supporting theorems on
their registered compiled trees, with no new rounded target. CG also retains its direct
physical-energy comparison; Lanczos retains its actual initial-direction certificate. Any new rounded
target must be concrete and reviewable before its own approval; the existing exact-target
approval does not authorize an unspecified replacement statement.

## Placement and reuse

- Existing Computation `ScalarSem`, `IsRelErrSem`, `AddsZeroExactly`, `exec`, first-order
  `Prog`, `nrm2`, `rscl`, `dot`, `axpy` and dense matvec programs are the only arithmetic API.
- Existing `CGState`, `lanczosState`, `CGRun`, `LanczosRun` are the only recurrence/model API.
- Norm and near-unit-vector bounds belong in `Computation/BLAS/Normalization.lean`.
- Normwise matrix/vector kernel corollaries belong in `Matrix/Computation/BLAS.lean`.
- Initial-direction/output transfer belongs with the finite-precision function vector.
- Stale implementation claims are corrected in their owning module documentation.

Mathlib does not provide this library's program execution or rounding interfaces. The transfer
uses the existing `specNorm_cfc_le`, `norm_toLp_mulVec_le`, linearity and the norm triangle
inequality; no alternative functional calculus, floating-point model or norm is introduced.

## 2026-11-04 concrete Lanczos proposal

The concrete proposal was staged in `proposals/krylov/Lanczos.lean` (since removed).
It loads the column-major
ROM matrix into a scoped dense buffer once, and uses existing `gemv` on that buffer. This
amends the earlier proposed dense substitution: no rounded accuracy theorem for `denseImpl`
is assumed. The same executed `gemv` is covered by the rounded matrix kernel adapters, so
matrix-vector local errors can be derived from its actual operations.

Six declared buffers at the arithmetic tag are, in order:

| Buffer | Size | Meaning |
| --- | --- | --- |
| 0 | `N` | input vector, unchanged |
| 1 | `N*(q+1)` | all basis columns from initial direction through state `q` |
| 2 | `q` | diagonal coefficients `alpha j`, zero-based |
| 3 | `q+1` | `beta j`, including initial `beta 0=0` |
| 4 | `1` | actually computed input norm |
| 5 | `N` | previous vector of the final state |

The scoped workspace contains the loaded matrix (`N²` cells), one work vector (`N`), and two
scalar cells (exact zero and a negative coefficient). Existing `gemv`, `dot` and `nrm2` need at
most one further temporary cell. Copies do not perform arithmetic.

Initialization writes the previous vector and initial beta to zero, computes the input norm
with `nrm2`, and tests that computed norm. A zero norm writes a zero initial column and performs
no division. A nonzero norm copies the input into the initial column and calls `rscl` using
the stored norm. Each step executes the following fixed order:

1. `gemv` of the current column into the work vector;
2. negation of stored beta and `axpy` of the previous vector;
3. `dot` of current column with that updated work vector, producing alpha;
4. negation of stored alpha and `axpy` of the current vector;
5. `nrm2` of the final work vector, producing the next beta;
6. copy of the current column into the previous-vector buffer;
7. test of the next beta, writing a zero next column without division if zero, otherwise
   copying the work vector into that column and executing `rscl`.

The requested number of steps always executes, including zero continuation. In exact
arithmetic this is precisely the existing total `lanczosState` recurrence, for every real
matrix and input vector, including nonsymmetric matrices, zero input, zero dimension and
terminal breakdown. Orthonormality and Krylov approximation statements still require their
existing mathematical hypotheses; the execution target does not assume them.

The proposed program and symbolic compiled-tree signatures are:

```lean
def lanczosProg {P ι VB VI : Type} (tag : P) (N q : IExp VI)
    (b V alpha beta inputNorm prev : VB) : Builder P ι VB VI Unit

def lanczosProg.compiled {P ι : Type} (tag : P) : Prog P ι 1 6
```

The componentwise count bound, before any cost weighting, is

```lean
noncomputable def lanczosCount {P ι : Type} (tag : P) (N q : ℕ) : OpCount P ι :=
  Finsupp.single (.rom tag) (N ^ 2) +
  Finsupp.single (.bin tag .mul) (N + q * (N ^ 2 + 4 * N)) +
  Finsupp.single (.bin tag .add) (N + q * (N ^ 2 + 4 * N)) +
  Finsupp.single (.un tag .conj) (N + 2 * q * N) +
  Finsupp.single (.bin tag .div) (N * (q + 1)) +
  Finsupp.single (.un tag .sqrt) (q + 1) +
  Finsupp.single (.un tag .neg) (2 * q) +
  Finsupp.single (.lit tag) (2 * N + 3 + q * (2 * N + 2)) +
  Finsupp.single (.cmp tag) (q + 1) +
  Finsupp.single (.copy tag) (N + 2 * q * N)
```

The branch bound permits both the zero-writing cost and the nonzero copying/division cost
componentwise. Only one branch is executed. The scalar-cell peak, including the immutable ROM,
loaded matrix, declared buffers and all scratch, is

```lean
fun N q p => if p = tag then 2 * N ^ 2 + N * (q 0 + 4) + 2 * q 0 + 5 else 0
```

The proposed exact target is `StoredEntriesLanczos : Prop`. Its outer quantifiers are only
`∀ (P ι : Type) [DecidableEq P] (tag : P)`, followed by `StoredEntries` on that exact compiled
tree with a `True` size predicate. The access model universally quantifies dimensions, an
arbitrary real input vector and arbitrary real ROM values. For
`A i j = vals (i + N*j)`, its postcondition preserves the input in buffer 0 and states that actual buffer 1 holds
`lanczosMatrix A b (q+1)`, buffer 2 holds `lanczosAlpha A (lanczosState A b j)`, buffer 3 holds
`(lanczosState A b j).beta`, buffer 4 holds `‖WithLp.toLp 2 b‖`, and buffer 5 holds
`(lanczosState A b q).prev`. Thus it includes the actual current column and beta of the final
state as well as every intermediate recurrence coefficient. No output or local-error bound is
an execution premise. The target is only a proposed definition until approved and registered;
a checked definition does not constitute its realization proof.

The step body is inlined in the sole top-level `lanczosProg`, so registration will not orphan
a separate helper program under the direct registered-tree ownership check. The symbolic
compiled tree still represents the same operation order. The checked kernel bridge
`exec_nrm2_rscl_eq_lanczosState_cur` specializes actual norm/division executions to exact
arithmetic and identifies the resulting candidate with `(lanczosState A b 0).cur`; it is
explicitly not a realization proof of the surrounding copies, guards or loop.

## Exact target approval, 2026-11-04

The maintainer explicitly approved both exact target statements in the conversation:
“Approve both exact target statements.” This covers `StoredEntriesConjugateGradient` and
`StoredEntriesLanczos`, their identified program trees, output and input-preservation
postconditions, guards, proposed count bounds and cell-memory bounds. The statements and
programs are fixed during proof development. This approval clears the registration boundary
for these two exact targets; it does not assert that their propositions have been proved.
No additional approval is required for their eventual registration with complete proofs.
Any substantive statement or program change requires a new review. Rounded target statements
and machine-format refinement are separate obligations.
