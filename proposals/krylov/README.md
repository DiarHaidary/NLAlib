# Concrete Krylov implementation proposals

These files are checked work toward connecting the existing theory to particular buffer
programs. They are outside `NLAlib`, are not imported by the library, and do not register or
prove a new whole-program target. A checked target definition is a proposition, not its proof.

| Implementation | Fixed operations and outputs | Proposed exact target |
|---|---|---|
| [ConjugateGradient.lean](ConjugateGradient.lean) | Cached squared residual Hestenes–Stiefel CG, zero start, ROM-loaded dense matrix, three computed vectors, status and input preservation; no square root | `StoredEntriesConjugateGradient`: successful guarded execution for all real inputs, with exact `cgState` output correspondence for SPD matrices, proposed counts and footprint |
| [Lanczos.lean](Lanczos.lean) | Paige-order dense Lanczos, actual norm and division, stored basis and coefficients, computed input norm, previous vector and input preservation; explicit zero continuation | `StoredEntriesLanczos`: successful execution agrees with the total `lanczosState` recurrence for all real matrices and vectors, with proposed counts and footprint |

The programs compile once into first-order trees at symbolic sizes. Both use the existing
Computation language and interpretations; no alternative arithmetic interface is introduced.
The exact claims bind the compiled tree before quantifying sizes, matrix entries and input.
Their budgets are proposed componentwise upper bounds, still requiring whole-program proofs.

Partial execution proofs include the actual ROM loading loop in
[CGInitialization.lean](CGInitialization.lean), the actual two-instruction CG direction loop
in [CGDirectionUpdate.lean](CGDirectionUpdate.lean), and the nonzero exact normalization
kernel bridge in the Lanczos proposal. These establish the stated local executions and
storage facts, not the complete program realization.

The library already supplies checked rounded kernel consumers in
[Normalization.lean](../../NLAlib/Computation/BLAS/Normalization.lean) and
[Matrix BLAS](../../NLAlib/Matrix/Computation/BLAS.lean). The next proofs must compose them
with actual guards, allocations, loop invariants, status and zero-step behavior to construct
`CGRun` and `LanczosRun`. Neither a desired local error nor an already constructed run may
be assumed in place of that missing construction. The matrix-function endpoint additionally
requires a concrete small-matrix function evaluator and final output arithmetic certificate.

On 2026-11-04 the maintainer explicitly approved both exact target statements and their
identified programs. Their statements, guards, output promises and budgets are now fixed.
`AGENTS.md` rule 2 and `CONTRIBUTING.md` section 5.5 permit registration within this approval;
the programs will enter the library with complete proofs of those statements. No target
registry, approved hash, existing target, check or allowlist has yet changed. These files
are not counted as completed whole-program implementation coverage. An IEEE backend and concrete random generator remain separate from
all-range relative-error and ideal-tape contracts.

See the [coverage inventory](../../docs/design/Implementation-Coverage.md),
[CG design](../../docs/design/Krylov-CG-Implementation.md) and
[Lanczos integration design](../../docs/design/Krylov-Implementation-Bridge.md) for the
interfaces, mathematical hypotheses and remaining obligations.

## Checked checkpoint

The library foundation passes the full stage check: 536 proved modules, no build warnings,
16,318 declarations audited with no axiom violations, and 16,548 constants replayed through
the kernel. The registered baseline program/target checks, source rules, citations, named
bounds and LaTeX checks pass. This checkpoint does not import the proposal programs.

The proposal definitions and the displayed local execution lemmas were checked separately.
`Smoke.lean` additionally passes fourteen actual compiled-tree Float examples, covering all
outputs, guards, the 23 operation-count components and peak memory including ROM. The executable
budget evaluators are proved equal to the proposed target formulas. These tests complement
the partial execution proofs; they do not prove a whole-program target or a Float contract.
