# Rounded execution and backward models of the stored Lanczos program

The full stored-program bridge is checked. It uses the existing scalar contracts, original
compiled tree, approved counts and existing `LanczosRun`; it introduces no replacement
arithmetic semantics, numerical run interface or registered target.

## Inputs and local precision

`LanczosImplementation.exec_rounded_compiled` in `LanczosProgramRounded.lean` takes actual
six-buffer input storage, decoded input b, column-major ROM words decoding to symmetric A,
standard operation charges, `IsRelErrSem` with unbounded safe range and `AddsZeroExactly`.
Output buffers need not be initialized. The only precision condition is

    epsilon = lanczosImplementationRoundoffBound N u = 16*(N+1)^2*u <= 1/100.

There is no accumulated q*epsilon condition for program completion or run construction.
`LanczosProgramRounding.lean` proves all required scalar windows and bounds: ordered dot,
dense matvec, two-operation axpy, component division and squared normalization defect.
The formula includes N=0 and controls u there. CG's different 4*N^2*u allowance is not used
for Lanczos normalization.

## Actual primitive order and initialization

The initializer loads A, writes initial beta/previous-vector zeros, executes nrm2(b), then
writes a zero first basis column or copies b and divides that copied column by the computed
norm. Each Paige step executes gemv, negation/axpy, dot, negation/axpy, nrm2, previous-column
copy, and guarded zero-fill or copy/rscl for the next column. No convenience theorem silently
replaces that norm/copy/divide order with a different combined kernel.

`Computation/BLAS/NormalizationFrames.lean` retains the actual norm execution and norm word
through intervening guards/copies. `Matrix/Computation/BLASNegAxpy.lean` shares the two executed
negation/subtraction adapters. Actual local errors, sign/zero facts and successful divisions
are derived; they are not initialized-state or desired-local-error premises.

The final theorem retains the stored norm s and initial computed column v1. It proves
s>=0, s=0 iff b=0, a norm error bounded by gamma_(N+1)*norm(b), the raw rescaling residual
norm(b-s*v1)<=u*norm(b), and

    norm(b-s*normalized(v1)) <= (2*u+gamma_(N+1))*norm(b).

The backward model therefore does not assume that b is exactly parallel to the initial
computed column. Here gamma_n is the existing primary product factor (1-u)^(-n)-1.

## Active prefix and actual output buffers

For q>0 and b nonzero, execution supplies 0<m<=q and an existing `LanczosRun N m`, with H=A
and epsilon equal to the implementation allowance. All actual declared output words decode
to its vectors and coefficients, including the full allocated basis/alpha/beta arrays,
computed input norm, retained input and final previous vector.

The active run stops at the first computed zero beta. Its terminal next vector is proved
zero by the actual guard. Later program iterations still execute and write zero columns and
coefficients; those outputs are retained separately through default-zero run functions.
The previous vector can be nonzero at the first zero continuation, because its multiplier is
zero. A zero tail is not appended as near-unit vectors to `LanczosRun`.

For q=0 or b=0 (including N=0), the theorem returns the actual initialized/zero outputs and
norm certificates without inventing `LanczosRun N 0`. Arbitrary finite q is permitted under
local precision because this arithmetic contract has unbounded range.

## Exact model and explicit input-only radii

`LanczosImplementation.exec_rounded_compiled_backward` in `LanczosProgramRoundedBackward.lean`
selects the nonzero-input/positive-budget case. It retains actual execution, decoded outputs,
resources, norm/direction certificates and active-prefix ties. The canonical Hermitian
matrix B=R.backwardH and unit start d=R.dilatedStart reproduce the active tridiagonal T_m,
dilated basis and terminal beta exactly.

A radius depending only on N, q, u and norm(A), valid with local precision alone, is

    1000*q^2*epsilon*(1+(1+epsilon)*sum_(i<q)(1+8*epsilon)^(i+1))*norm(A).

It bounds the Frobenius difference from the block-diagonal dilation of A. Coefficient growth
is explicit and this bound may become large. The same model also satisfies:

- 400*q^3*epsilon*norm(A) when q*epsilon<=1/100;
- 1000*q^2*epsilon*norm(A) when q^2*epsilon<=1/1000.

These are applications of the existing backward theory, not newly assumed defects. The
model/spectral statements concern the active prefix m. If m<q, the full padded T_q has extra
zero eigenvalues, which need not be near the input spectrum. Raw computed columns need not
be orthogonal; the exact model's orthonormal basis lives in the dilated space.

## Proof placement and resources

The rounded modules separate decoded StoreContext, primitive Step/Commit/Execution, actual
Zero continuation, existing-Run constructors, RoundedPrefix bookkeeping, full loop and
Preallocated ROM/initializer composition. `LanczosProgramRounded.lean` proves the actual
compiled-tree allocation/body/release identity and final decoded outputs.
`LanczosProgramScope.lean` shares generic allocation and cleanup with exact/oracle proofs.

`LanczosProgramStaticCost.lean` analyzes the unchanged tree independently of numerical
correctness. The rounded theorem reuses its approved count formula and additional workspace
N^2+N+3 cells with the corresponding bit-width bound. Initial declared storage and external
ROM are handled by the existing resource model.

Matrix-function evaluation/postprocessing and an IEEE format/range certificate remain
separate obligations. Float smoke executions check selected executions, not those contracts.
