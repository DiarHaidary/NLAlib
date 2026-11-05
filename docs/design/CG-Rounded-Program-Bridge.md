# Rounded execution of the stored-entry CG program

Status: all eleven supporting canonical modules checked with warnings fatal. The full
registered-tree execution, decoded final outputs and unchanged resource budgets are proved.
Canonical supporting-library promotion is checked; no new numerical target is added.
The complete build passed 3106 jobs with warnings fatal; source rules and actual
pretty-printed signature naming checks both report zero violations.
The approved `cgProg`, compiled tree, exact target and count definitions are unchanged.
No new arithmetic semantics, iteration interface, numerical target or Result id is introduced.
The end theorem is about actual execution of `cgProg.compiled` under the existing scalar
contract, not a rounded instance of an unregistered target model.

## Arithmetic and decoded input

Use `IsRelErrSem u dec (fun _ _ => True) I.sem` and `AddsZeroExactly dec I.sem`.
The range is explicitly unbounded; this is not an IEEE overflow/underflow theorem. Input
words and ROM words decode to the mathematical input `b` and stored column-major matrix
`A`. The initial declared store has five buffers, with only buffer 0 initialized. The
three canonical scoped allocations provide buffers 5, 6, 7 with the existing layout.
For positive dimension use the existing budget `eps = 4*N^2*u(tag)` and `eps <= 1/100`.
The zero-dimensional case needs `u(tag) < 1` independently: its zero budget does not imply
that inequality. All cases assume nonnegative `u` through the existing contract.

Literal zero decodes exactly to zero. Literal one decodes to a value `flag` satisfying
`abs(flag-1) <= u(tag)`; therefore `flag > 0` when `u(tag) < 1`. Negation decodes to `-flag`.
The program's statuses are exactly the decoded values 0, flag, -flag, never silently 1/-1.

## Checked increments

1. `exec_rounded_initialization I tag hsem hz st N A b values hshape hb hrom hsmall`:
   the displayed canonical preallocated initializer actually returns `header`; return
   `nu theta flag`, `StoreContext tag dec N A b <0,b,b> nu
   (if b=0 then flag else 0) flag header.store`, `flag>0`,
   `nu=norm(b)^2*(1+theta)`, `abs(theta)<=eps`, `nu>=0`, and `nu=0 <-> b=0`.
   Also retain the actual pre-dot/cached states and their execution/cache word provenance,
   full input/matrix frames, shape and unchanged tape positions/current memory. This proves
   ROM loading, both literals and exact negation, zero iterate fill, two input copies,
   initial self-dot and the actual initial status guard; none is assumed as an initialized
   numerical state. For N=0 give a separate theorem with nu=0, b=0, status=flag.

2. General active-prefix extraction: from those actual initialization facts and an actual
   sequence of canonical active iterations whose executed curvature comparisons are true,
   construct `R : CGRun N m` for each `0<m`, with `R.A=A`, `R.b=b`, `R.eps=eps`.
   The construction retains prior extracted data when extending R. The exported theorem
   ties the final actual x/r/p/cache and last executed product/curvature/gamma/delta words
   to R's fields; it does not export a universal read-history of every intermediate header. Every local
   defect follows from the existing checked phase execution lemmas. Successful comparisons
   are trace facts for this intermediate extraction theorem, not input-only horizon claims.
   Positivity of nu follows from the preceding self-dot and actual active status. No CGRun
   or desired local-error bound appears as a premise of the end-to-end theorem.
   The m=0 branch returns the actual initialized x/r/p/cache/status, with no CGRun 0.

3. Input-only horizon theorem: for N>0, symmetric A, spectrum(A) subset [a,a'], a>0,
   and `q^2*sqrt(q)*eps*(a'/a)^2 <= 1/10^5` (q>0), actual execution completes the
   requested q-loop. It returns m<=q completed active steps; either m=q with decoded
   status 0 and nonzero residual, or status=flag with zero residual and m<=q. Once status
   is flag, all remaining loop iterations execute the actual skip branch and preserve the
   terminal state. For m>0 return the CGRun and all actual-state ties from (2); for m=0
   identify b=0 and x=0,r=p=b,nu=0,status=flag. Negative status is excluded, and division
   never fails. This does not promise nonzero residuals for q iterations or invent a
   positive-length CGRun after zero termination.

   The induction closes using the existing CGRun terminal direction bound
   `rho_m <= 2*norm(p_m)`, a-priori P/K bounds and the horizon inequality. Thus active
   residual implies nonzero direction at the next header. The actual matvec/dot errors
   and spectral curvature lemma imply the next curvature guard is true. Initial active
   p=b is nonzero directly. There is no assumption of unproved Euclidean monotonicity.
   The q=0, b=0 and N=0 cases execute initialization and guarded skips separately.

4. Wrap the actual allocations, initializer, q-loop and scope release to obtain
   `exists out, Prog.exec I (cgProg.compiled tag) N ![q] initial = some out` together with
   preserved input/output/status and the disjunction in (3). Use the generic StaticCost
   theorem to relate actual execution to resource bounds independently.
   No cost Result id or target declaration is added in these supporting modules.

## Placement and dependencies

The eleven canonical rounded CG modules reuse CGProgramDirection/Body, ScalarFrames,
BLAS Frames and Matrix/Computation/BLAS. The generic literal-zero frame helper
uses an actual literal-zero word, and the existing exact fill API reuses that same helper.
The prefix proof extends the existing CGRun record, keeping previously extracted fields
below m and the new executed phase at m. Proof-history bookkeeping is not a second run model.
The mathematical dependency needed for horizon continuation is a public corollary of
CGBackward a-priori P/K bounds and CGRunModel terminal direction control under the same
input-only horizon inequality. Energy/residual consequences then apply to the extracted
CGRun and the actual decoded final iterate, with the terminal zero case handled explicitly.

## Validation

Each coherent increment is checked with LEAN_NUM_THREADS=2 and warnings fatal in the isolated
CG checkout. No unchecked sources/artifacts are published. Source rules must report zero
errors/warnings; proof/file limits remain 80/1500 lines. Parent owns final integration and
any proposed target or additional named numerical-bound approval.

## Canonical supporting modules

The eleven checked prototype modules are promoted, with unchanged theorem statements and
fixed program/target/count bodies, under `NLAlib/Krylov/LinearSystems`:

| Prototype | Canonical module |
| --- | --- |
| CGImplementationRoundoff | CGProgramRounding |
| CGRoundedExecution | CGProgramRoundedKernels |
| CGRoundedStep | CGProgramRoundedStep |
| CGRoundedStop | CGProgramRoundedStop |
| CGRoundedBody | CGProgramRoundedBody |
| CGRoundedRun | CGProgramRoundedRun |
| CGRoundedInitialization | CGProgramRoundedInitialization |
| CGRoundedPrefix | CGProgramRoundedPrefix |
| CGRoundedHorizon | CGProgramRoundedHorizon |
| CGRoundedProgram | CGProgramRoundedWorkspace |
| CGRoundedCompiled | CGProgramRounded |

The generic actual literal-zero fills move to Computation/BLAS/Frames; the original exact
fill signatures are preserved and their proofs reuse the generic word-level execution.
Prototype helper names are normalized before first library publication:

| Prototype helper | Canonical helper |
| --- | --- |
| composable_rounded_preload | executionComposable_rounded_preload |
| composable_rounded_vectors | executionComposable_rounded_vectors |
| composable_rounded_initialization | executionComposable_rounded_initialization |
| initial_context_of_pairing_write | storeContext_of_pairing_write |
| rounded_prefix_smallness | mul_sq_sqrt_mul_mul_le_of_le |
