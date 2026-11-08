# Kernel-call audit corrections

The manual review of PR #59 found two behavioral defects in its new kernel-call path.
These corrections preserve the existing program trees and mathematical target statements.

## Empty blocks

`Computation.blockDisjoint` originally rejected an empty block whose offset lies strictly
inside a nonempty block in the same buffer. For example, `(0, 2, 0)` and `(0, 0, 4)` have no
common cell, but the original endpoint-only comparison returned false. The shared
`Interp.kcallStore` leaf therefore rejected some valid calls with zero-dimensional operands.

The test now accepts either zero length. The theorem `blockDisjoint_eq_true_iff` proves that
the Boolean test agrees exactly with absence of a common cell, including empty ranges.
Reads, writes, operand counts, returned lengths and nonempty overlap checks are unchanged.
An empty block visits no cell: `Store.readBlock` of length zero and `Store.writeBlock` of an
empty array succeed at every handle, tag and offset (`Store.writeBlock_eq_some_of_size_eq_zero`),
so no handle, tag or offset check applies to it. A call with empty operands still has to pass
the operand-count check, and its kernel has to succeed and return arrays of the declared
lengths. (An earlier version of this note said that an empty block is still checked against
the store; that was wrong.)

The certified-routine frames of PR #69 (`RoutineFrames.lean`) were first proved against the
endpoint-only test. Their `blockDisjoint_iff` now lists the two empty cases, and
`blockDisjoint_iff_of_pos` keeps the endpoint form for nonempty blocks, which is the form the
frame proofs use. The CGS call sites discharge the other direction from distinct handles and
needed no change. `blockDisjoint_of_ne_or_le` supplies the sufficient endpoint test to callers
with arbitrary lengths. The kernel contracts check preservation at a particular cell with
`blockDisjoint_eq_true_iff`. Membership in a block already proves that block is nonempty.

The review's `KernelCallEmptyBlocks.lean` witness exercises empty input/output and
output/output overlap, rejects real overlap and malformed returned lengths, and checks
the resulting stores. It is included with the local review artifacts.

## Exported kernel identity

The NumPy emitter originally ignored the kernel identifier and emitted one anonymous
`kernel(...)` callback. Distinct kernel operations could therefore call the same implementation.
`emitF` takes a total kernel-name function. `emitProg` accepts that same function as `kname`
or a partial binding as `kernelName`. Omitted bindings leave every kernel unbound.
An emitted unbound call raises `NotImplementedError` when reached. A non-inlined `named` node
continues to delegate its whole body to its external implementation, whose internal calls
remain its responsibility. Existing programs without kernel calls retain their previous
calling convention.

The tools build executes two distinct kernels under a loop in both inline modes and checks
their order and output, then tests completely missing and partially supplied bindings.
Bindings and the Python implementations remain the caller's responsibility; the exporter
is still an unverified translation.

## Target approval

The closure walk includes the whole interpreter for targets whose execution model uses it.
Changing `blockDisjoint` therefore changes their fingerprints even for trees without kernel calls.

The target statements, tree definitions, registry and approval file are untouched. The
target gate must continue to reject the old fingerprints until the maintainer reviews this
semantic correction and refreshes the registry and its approval under the
[programs guide](../contributing/programs.md).
An otherwise successful build or kernel replay does not satisfy that approval gate.

The same review corrects contract prose about exact comparisons, layout round trips and
outer probability, and records the implemented S1 vocabulary in the
[vocabulary guide](../contributing/vocabulary.md).
Those documentation corrections do not change their contracts.
