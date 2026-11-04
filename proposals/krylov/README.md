# Krylov implementation development files

These files retain the checked development of the concrete CG and Lanczos implementations.
They are outside `NLAlib` and are not library imports. The maintainer approved both exact
program/target statements on 2026-11-04; their complete proofs are now in the library:

| Program | Approved target | Complete library proof |
|---|---|---|
| Cached squared-residual Hestenes–Stiefel CG, zero start, guarded curvature and stopping | `StoredEntriesConjugateGradient` | [CGProgram.lean](../../NLAlib/Krylov/LinearSystems/CGProgram.lean), `storedEntriesConjugateGradient` |
| Paige-order Lanczos, actual norm and division, explicit zero continuation | `StoredEntriesLanczos` | [LanczosProgram.lean](../../NLAlib/Krylov/Processes/LanczosProgram.lean), `storedEntriesLanczos` |

The approved program trees, statements, counts and memory formulas are unchanged. Both
proofs include ROM loading, initialization, actual loops and branches, every promised output,
input preservation and workspace cleanup. The fourteen compiled-tree Float examples now
also live in [NLAlibTools/KrylovSmoke.lean](../../NLAlibTools/KrylovSmoke.lean); these check
selected executions and resources, without certifying Float arithmetic.

The `CGRounded*.lean` files develop actual phase execution under the existing relative-error
contract. They are checked supporting work, not registered rounded targets. The remaining
whole-program obligations include rounded initialization, successful-prefix composition into
`CGRun`, and a horizon theorem excluding unwanted curvature breakdown. A complete rounded
`LanczosRun` constructor and concrete matrix-function postprocessing are also outstanding.
Neither a desired local error nor an already constructed run can replace those proofs.

See the [coverage inventory](../../docs/design/Implementation-Coverage.md),
[CG design](../../docs/design/Krylov-CG-Implementation.md), and
[integration record](../../docs/design/Krylov-Implementation-Integration.md) for the
mathematical hypotheses, source placement and verification status.
