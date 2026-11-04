# Rounded stored-entry Lanczos execution: design assessment

Status: local precision and executed normalization helpers are checked; whole-program
rounded Lanczos construction is the next increment. No new numerical target is introduced.
The registered dense Lanczos tree, exact target and operation/count bodies remain frozen.
The completed canonical CG bridge is checked and published independently of this extension.

## Reusable facts and actual operation order

Use the existing IsRelErrSem contract with unbounded range, AddsZeroExactly, decoded input
words and column-major ROM words. Computation BLAS already supplies actual executed gemv,
dot, axpy, nrm2 and rscl traces with normwise errors and store-write provenance. The new
arbitrary-word literal-zero fill in Frames covers the canonical initialization/tail loops.
The exact Lanczos storage and scoped allocation proofs can be reused or generalized without
an alternative numerical interface.

The actual initializer loads A, writes zero beta/previous vector, computes nrm2(b), then
branches on its decoded zero. The nonzero branch copies b to the first basis column and
rscl divides that copied column by the stored computed norm. In each iteration it computes
matvec, negative previous beta and axpy, dot for alpha, negative alpha and axpy, nrm2 for
next beta, copies current basis to previous, then writes zero or copies/rescales the next
basis column. nrm2 and rscl are separated by an actual copy, so the convenience theorem
exec_nrm2_rscl cannot be substituted as though the program calls a combined kernel. Its
scalar/norm algebra can be reused with the actual copy frame and norm-word provenance.

## Checked input-only local budget

`lanczosImplementationRoundoffBound N u` is epsilon = 16*(N+1)^2*u(tag), defined in
`LanczosProgramRounding.lean`. This is a separate budget from stored CG. Under nonnegative
unit roundoff and epsilon <= 1/100:

- (N+1)*u <= 1/1600, so the nrm2/rscl window and all divisors used after a nonzero norm test
  are justified by existing successful-execution and zero/positive norm theorems.
- The squared normalization defect is <= 12*(N+1)*u <= epsilon by the existing public
  normalizationRoundingFactor_le theorem; this is the extra condition absent from CG.
- Dense matvec error is <= gamma_N*sqrt(N) <= 2*N*sqrt(N)*u <= epsilon.
- Ordered dot error gamma_N <= 2*N*u <= epsilon, and two-operation axpy error
  gamma_2 <= 4*u <= epsilon, including all cross terms retained in the checked adapters.
- Component division gives the Lanczos normalization residual norm <= u*norm(z), hence
  <= epsilon*norm(z). Negation and copies are exact on decodings/words as appropriate.

Completion and run-prefix extraction require only local epsilon <= 1/100, for every q.
Backward/spectral conclusions separately assume m*epsilon <= 1/100 for the extracted active
prefix, or the sufficient input-only q*epsilon <= 1/100. No accumulated horizon is needed
to justify the actual program completion. The q=0 initializer still computes and divides
by a rounded norm when its input is nonzero, so its local bound remains necessary.
Unlike the CG formula, this bound also controls u at N=0. These scalar comparisons are
checked in `LanczosProgramRounding.lean`. The actual
norm/copy/divide provenance and direction estimate are checked in
`Computation/BLAS/NormalizationFrames.lean`.

## Output and stopping semantics

Prove a supporting theorem on the same actual lanczosProg.compiled.exec, with input/storage,
scalar-contract and precision premises only. Derive all LanczosRun fields from primitive
execution; neither LanczosRun nor desired local defects are inputs.

For decoded b nonzero and q>0, return a positive prefix m<=q and L:LanczosRun N m with
L.H=A, L.epsilon equal to the approved implementation budget. Actual basis/coefficient
words through the active prefix decode to L.v, L.alpha and L.beta. The first zero computed
beta is permitted at m, and no beta before m is zero. The terminal normalized-vector field
is conditional on beta_m!=0, exactly as required by the existing run model.

The canonical program continues every requested iteration after beta=0; it does not have
CG's status-skip loop. Prove the zero tail by actual zero arithmetic and frames: subsequent
basis columns, alpha and beta are zero. Do not pad L with zero vectors, since its near-unit
premises would fail. Return the active prefix and actual padded outputs separately. The
full q-loop still pays its actual operations, controlled by the existing static-cost lemma.

For b=0 (including N=0), actual nrm2 is zero, initialization writes a zero first column,
and every subsequent iteration writes the zero tail. No positive-length LanczosRun is
constructed. For q=0, return the actual initial norm/normalized first column or its zero
branch, with no LanczosRun 0. All divisions occur only after nonzero norm comparisons.

## Input direction and backward model

Return the stored input norm s>=0 and the actual normalized initial direction certificate
norm(b-s*normalizedV_1) <= (2*u+gamma_(N+1))*norm(b). The input norm need not equal the exact
norm, and the computed basis vectors need not have norm exactly one. Existing normalization
lemmas supply both this mismatch and the squared near-unit defects needed by LanczosRun.

For m>0 apply the existing Lanczos backward-model API to the extracted L, retaining its
explicit perturbation bounds and the horizon m*epsilon<=1/100 inherited from m<=q. Export
actual coefficient/basis and scaled input-direction ties. The existing physical transfer
formula M*tau+s*E+zeta can be used by a later consumer, but this implementation bridge makes
no matrix-function postprocessing, eigensolver or returned matrix-function-vector claim.

## Minimum remaining proof work

1. Generic decoded initializer/store invariant for the existing Lanczos layout and norm word.
2. Actual gemv/axpy/dot/nrm2/copy/rscl per-step defects with retained frames.
3. Existing LanczosRun prefix construction and actual zero-tail induction.
4. Scoped compiled-tree execution, decoded outputs and static-cost/backward consequences.

All checks run in the isolated verification checkout, two Lean threads and one build at a
time, warnings fatal. No registry/target/check changes are made by this supporting work.
