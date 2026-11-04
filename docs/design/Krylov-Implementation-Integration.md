# Concrete Krylov implementations and their guarantees

2026-11-04. Both stored-entry and matrix-free CG and Lanczos have approved exact targets and
complete program proofs. The stored CG program also constructs its finite-precision run and
backward model from primitive execution. Whole rounded Lanczos construction is the next
increment; its local precision and normalization helpers are already checked.

## Programs and targets

| Program | Target and proof | Mathematical output |
|---|---|---|
| `cgProg.compiled` | `StoredEntriesConjugateGradient`, `storedEntriesConjugateGradient` | Preserved input and legal status for every real matrix; for SPD matrices, x/r/p equal the total exact CG recurrence |
| `cgOracleProg.compiled` | `MatrixFreeConjugateGradient`, `matrixFreeConjugateGradient` | The same guarded outputs with one oracle call per active step and no stored matrix |
| `lanczosProg.compiled` | `StoredEntriesLanczos`, `storedEntriesLanczos` | All basis columns, alpha/beta coefficients, input norm, previous vector and retained input |
| `lanczosOracleProg.compiled` | `MatrixFreeLanczos`, `matrixFreeLanczos` | The same outputs, using one oracle call per requested Paige step |

Builders and compiled trees live in the respective `CGProgramTree`, `CGOracleProgramTree`,
`LanczosProgramTree` and `LanczosOracleProgramTree` files. Target/count definitions live in
the corresponding `*Targets.lean` files; the final `*Program.lean` theorem has its target
constant as its entire type. Compilation/instantiation equations are kernel checked.
All targets include zero dimension, zero input, zero steps and terminal continuation.

Oracle memory is `5*N+11` cells for CG and `N*(q+4)+2*q+5` for Lanczos. Oracle internal storage
and arithmetic are outside this access model. The stored targets retain their original
ROM-inclusive bounds, adding `2*N^2` to these formulas. Counts distinguish each oracle load
from its column matvec and include actual scalar, copy and guard operations.

## Independent resource analysis and shared execution

`Computation/StaticCost.lean` folds the actual first-order tree into operation counts and
additional cell/bit workspace. It proves bounds for successful execution under arbitrary
scalar/oracle semantics; numerical correctness and success are proved separately.
`CGProgramStaticCost`, `CGOracleProgramStaticCost`, `LanczosProgramStaticCost` and
`LanczosOracleStaticCost` establish the approved closed-form bounds from those trees.
Read-only memory is added once by the existing resource interface.

Generic scalar/ROM and BLAS frames remain in Computation. The certified builder-composition
property applies to single-statement emitters and their certified compositions; it does not
assert that arbitrary builders with escaping allocations compose that way.
`Computation/Allocation.lean` and the two `*ProgramScope.lean` files describe actual scoped
allocations, arbitrary word widths and cleanup. Shared declared-state constructors and
Lanczos output-preservation lemmas avoid duplicating initialization/cleanup proofs.
Backend-specific matrix-vector prefixes reuse the same scalar and vector phases.
No replacement arithmetic semantics, recurrence or local-error run model is introduced.

## Complete rounded CG bridge

`CGProgramRounded.lean` proves `CGImplementation.exec_rounded_compiled` on the unchanged
stored-entry compiled tree. Inputs are actual declared buffer words, column-major ROM words,
their decodings and the existing `IsRelErrSem`/`AddsZeroExactly` contracts. It derives the
initializer, cached norms, guards, divisions, full loop, cleanup and decoded output ties.
It assumes no initialized numerical header, local defects or `CGRun` as input.

Write `epsilon = 4*N^2*u` and `kappa = a'/a`. The explicit conditions are `u < 1`,
`epsilon <= 1/100`, symmetric A with spectrum in `[a,a']`, `a > 0`, and
`q^2*sqrt(q)*epsilon*kappa^2 <= 1/10^5`. Zero input/dimension/steps are separate proved branches.
Otherwise the result supplies an existing `CGRun N m`, `0 < m <= q`, tied to the actual
returned x/r/p words. A shorter prefix has zero terminal residual; remaining iterations
execute the actual status-skip branch. Literal one decodes to a positive flag within u of one;
status statements retain that flag rather than silently replacing it with exact one.

`CGProgramRoundedBackward.lean` composes this execution theorem with the existing backward and
physical-energy theory. It gives the canonical SPD model, explicit perturbation radius,
exact matching model step lengths and computed residual norms, and a comparison of the actual
iterate's squared energy error with exact CG's error on the model. The model-distance term
`2*norm(b)^2*delta/a^2` and existing local `150*m^2*epsilon*kappa*norm(b)^2/a` remainder stay
separate. The comparison uses energy directly, without converting a residual-gap estimate.
See [the rounded bridge](CG-Rounded-Program-Bridge.md) and
[the backward theorem](CG-Rounded-Backward.md).

## Rounded Lanczos and remaining endpoints

`LanczosProgramRounding.lean` proves that `16*(N+1)^2*u` controls the actual dense kernels and
squared normalization defect under its local small-roundoff condition.
`Computation/BLAS/NormalizationFrames.lean` handles the executed norm, preserved norm word,
intervening copies and component division. It proves norm residual, near-unit and initial
normalized-direction bounds from actual primitive execution.
The complete `LanczosRun` extraction, zero tail and compiled backward corollary remain the
[next increment](Lanczos-Rounded-Program-Bridge.md). The backward-analysis horizon is distinct
from these local arithmetic conditions.

The arithmetic contracts use an unbounded range. Float smoke executions do not certify an
IEEE format, overflow/underflow behavior or arbitrary external oracle accuracy. Matrix-function
postprocessing, preconditioning and other algorithm families remain separately tracked in
[the coverage inventory](Implementation-Coverage.md).

## Preserved approvals and mathematical contracts

The maintainer approved both new oracle statements and trees. Their four program/tree/count/
target bodies are unchanged from each reviewed proposal. The registry contains nine targets
and seven trees; every pre-existing entry and build pin remains exactly unchanged.
The small naming-check correction for zero and conditional notation was separately approved;
checks, allowlists and ratchets were not bypassed.

The prior main integration retained the approved explicit `k*epsilon <= 1/100` conditions on
five Lanczos spectral/quadrature/function bounds, with unchanged conclusions. The run interface
keeps only its local accuracy condition. Primitive bridges use the primary product factor
`(1-u)^(-n)-1` and its existing rational upper comparison.
