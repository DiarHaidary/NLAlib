# Integrating the approved concrete Krylov implementations

2026-11-04. The maintainer approved `StoredEntriesConjugateGradient` and
`StoredEntriesLanczos` and their identified program trees. Their exact statements, operation
order, declared inputs and outputs, count formulas and ROM-inclusive memory bounds remain
fixed. Both use the existing Computation language and its exact stored-entry model.

## Library placement

The canonical builders and compiled trees live in `Krylov/LinearSystems/CGProgramTree.lean`
and `Krylov/Processes/LanczosProgramTree.lean`. Their count functions and approved statements
live in `CGTargets.lean` and `LanczosTargets.lean`. Their exact execution and loop proofs live
in their own algorithm topics, upstream of the files proving the respective target constants.

Generic scalar/ROM frames and the certified builder-composition property live in
`Computation/ScalarFrames.lean`; generic actual BLAS frames and zero initialization live in
`Computation/BLAS/Frames.lean`; the exact guarded-normalization execution lives in
`Computation/BLAS/GuardedNormalization.lean`. These modules use the existing semantics and
store; they define no algorithm program, replacement arithmetic model, or new interpretation.
The composition property is proved for single-statement-emitting builders and compositions
of certified prefixes. It does not assert that arbitrary continuation builders, including
escaping allocations, have that property.

The Lanczos stored loop invariant and CG store context are algorithm-specific proof objects
in their algorithm topics. All generic proof consumers refer to the shared Computation
lemmas. Existing mathematical recurrences remain unchanged; public exact CG stopping and
nonzero-direction lemmas provide the implementation guard facts.

The initial proposal snapshots remain development/reference material outside the library.
Temporary exact proof staging was replaced by the canonical library modules. Rounded proposals
now import those canonical APIs directly, with no copied exact program or exact proof module
in their dependency closure.
Only the two approved targets and their two compiled trees are added to the registry; all
existing approved target and tree entries retain their hashes and statements. An independent
read-only review confirmed that all eight program, compiled-tree, count and
target declaration bodies match the approved proposal checkpoint `741a5710` modulo whitespace.
The registry update also preserved every old entry and toolchain pin exactly. The resulting
target checker and full stage check passed, as recorded below.

## Verification and scope

Each algorithm theorem has the approved target constant as its entire type. It composes the
actual ROM loading, initializer, executed loop, branches, scoped allocations and cleanup,
identifies every promised output cell, and proves the fixed operation and memory bounds.
The first-order compilation/instantiation equations are checked by the kernel. Fourteen Float
smoke cases execute the same compiled trees and verify outputs, branches, every count kind,
ROM-inclusive peak memory, workspace release and tape nonuse. They complement the proofs;
they do not certify the Float arithmetic contract or an IEEE implementation.

Generic rounded kernel proofs and initialization-direction/output transfers are already in
the library. Complete rounded execution-to-`CGRun`/`LanczosRun` constructors, matrix-function
postprocessing, preconditioning and the other algorithm families remain separately tracked
in the implementation coverage inventory. No exact-arithmetic program theorem is relabeled
as a rounded or finite-word machine theorem.

## Rounded CG checkpoint and next obligations

The checked proposal `CGRoundedRun.lean` proves
`CGImplementation.cgRun_one_of_initial_dot_execution`. It constructs the existing
`CGRun N 1` from the actual guarded first iteration and the initial self-dot execution, with
physical x/r/p output reads and the actual cached, step-length and direction-coefficient
words. Its arithmetic parameter is the input-only conservative bound `4 * N^2 * u`.
It assumes the existing relative-error contract and exact addition of zero, a correctly
initialized decoded header, provenance of the initial self-dot word, nonzero input, positive
dimension, a symmetric matrix with spectrum in `[a,a']`, and the explicit precision conditions
`epsilon <= 1/100` and `3 * epsilon * a' <= a`, where `a > 0`. Local-error bounds and a `CGRun`
are conclusions, not premises. These conditions suffice to justify the actual first
curvature guard before division.

This proposal does not yet derive the initialized header from the entire ROM/literal/copy
initializer. It also does not compose arbitrary successful prefixes or prove guard success
through a requested horizon. Those are the next rounded CG obligations; zero input and zero
dimension need their own rounded initialization branches. For Lanczos, the next composition
must use the actual nrm2-on-input, copy, rscl order and prove the full decoded initialized run.
Neither exact program correctness nor the one-step proposal supplies those missing proofs.

## Completed validation, 2026-11-04

`LEAN_NUM_THREADS=2 bash scripts/stage_check.sh` exited 0 after the helper naming fixes:
555 proved modules, zero Lean build warnings, 16,701 declarations audited without axiom
violations, and 17,005 constants replayed through the kernel. Program and target checks report
zero violations for seven targets and five concrete trees. Metadata, citations, 67 registered
bounds and all 35,974 math spans pass. Source rules report zero new errors; the existing 73
ratchet entries and review warnings remain. The duplicate scan has the same six private-only
classes as the foundation checkpoint, with no private/public or public/public duplicates.

Fourteen actual compiled-tree Float smoke cases pass in `NLAlibTools.KrylovSmoke`. The six
rounded CG proposal modules were separately checked with warnings fatal and have zero source
rule errors or warnings in the source-only check. They are outside the library replay roots.
The explorer preview builds from fresh library extraction; its 16 algorithm-page tests pass,
and generated data confirms both program members, proved targets and cost/output result
placement. The companion changes are on `update/krylov-implementation-bridges`.
