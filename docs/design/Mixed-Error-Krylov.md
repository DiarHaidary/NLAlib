# Extending Krylov analysis to relative and absolute errors

2026-11-05. The maintainer requested bringing the mixed-error setting toward the existing
relative-only coverage. This extends the arithmetic design in
[Finite-Precision-Arithmetic.md](Finite-Precision-Arithmetic.md), without changing programs,
registered targets, checks or build pins.

## Reuse and limits

Use the existing `Computation.AbsRelErr`, `IsArithErrSem`, `AddsZeroExactly`, BLAS execution
traces, `LanczosData` and `NormalizedLanczosData`. The existing general execution theorems
already accept an arbitrary error relation and explicit safe-range obligations. Do not
introduce a second scalar contract or repeat the backward matrix-function theory.

The current `CGRun` and `LanczosRun` contain genuinely relative-only properties: a zero
norm cache implies a zero vector; positive quotients cannot round to zero; normalization
errors scale with the vector being normalized. These do not follow from mixed errors.
In addition, an error inequality alone does not preserve signs. A mixed-error theorem
must retain a positivity margin, a backend sign certificate, or a conditional active prefix.
No completion or nonbreakdown theorem may silently assume these conclusions.

## Shared vector error layer

Add `Computation/VectorErrors.lean`. All vector statements involving `AbsRelErr` belong in
Computation; raw scalar or norm lemmas absent from Mathlib belong in ForMathlib. Use arbitrary
finite index types where possible. Existing Mathlib tools found: `EuclideanSpace.norm_toLp_le_norm_toLp`,
`EuclideanSpace.norm_eq`, `PiLp.norm_toLp_const`, norm addition/smul inequalities. Existing
relative-only vector lifting is private in `CGProgramRoundedKernels.lean`; it is not a competing
public interface. Search for each additional raw inequality before proving it.

Primary exact statement shape (implicit finite index type `n`):

```lean
theorem AbsRelErr.norm_sub_le
    (h : forall i : n, AbsRelErr u eta (x i) (z i))
    (hu : 0 <= u) (heta : 0 <= eta) :
    norm (WithLp.toLp 2 (x-z)) <=
      u * norm (WithLp.toLp 2 x) + Real.sqrt (Fintype.card n) * eta
```

For multiplication followed by addition, allow separate `um,ua,etam,etaa`:

```lean
theorem norm_sub_add_smul_le_of_absRelErr
    (hq : forall i, AbsRelErr um etam (a*x i) (q i))
    (hz : forall i, AbsRelErr ua etaa (y i+q i) (z i))
    (hum : 0 <= um) (hua : 0 <= ua) (hetam : 0 <= etam) (hetaa : 0 <= etaa) :
    norm (WithLp.toLp 2 ((y+a • x)-z)) <=
      ua * norm (WithLp.toLp 2 y) +
      (um+ua+um*ua)*abs a*norm (WithLp.toLp 2 x) +
      Real.sqrt (Fintype.card n)*((1+ua)*etam+etaa)
```

Uniform-allowance corollaries are instantiations, not separate proofs. Zero absolute
allowance recovers a relative-only bound. No dimension/precision smallness condition is
needed for these local inequalities.

Scalar additions to `Underflow.lean` should supply explicit additive-defect or multiplicative
representations only when needed by consumers, with nonzero/magnitude margins stated. Do
not convert absolute errors to relative errors by dividing by an unproved positive quantity.
The planned absorption bridge is `AbsRelErr.relErr_of_le`: from
`eta <= (v-u)*abs a` and `0 <= v`, conclude `RelErr v a z`. Its scale-separated corollary
`AbsRelErr.relErr_of_abs_ge` assumes `0 < tau <= abs a` and uses the visible coefficient
`u+eta/tau`. A nonzero-output lemma uses the explicit margin `eta < (1-u)*abs a`.

## BLAS execution and dense products

Extend the existing generic BLAS mixed-error consumer using the vector layer. Add mixed
`axpy` and dense matrix/vector/matrix-product execution bounds, retaining successful execution
and write/frame conclusions. Range requirements may be discharged from input bounds; observed
intermediate finiteness is not an input-only theorem.

For an N-term dot write, in this note only,
`P=(1+u)^(2*N)` and `D=N*P*(2+u)*eta`. The existing mixed trace bound gives
`abs(sum x_i*y_i-z) <= (P-1)*sum abs(x_i*y_i)+D` and the next-accumulation range bound.
Lift rows to a norm bound, with an additive `sqrt(M)*D` for M output rows. A dense square
spectral-norm corollary may use the existing `sqrt(N)` conversion, with all factors explicit.
Do not hide `eta` in an operator-error coefficient by dividing by a possibly zero input norm.
The old purely homogeneous `IsMatvecRoutine` contract therefore cannot describe the whole
mixed bound without either a scale margin or a justified extension.

## CG updates, residual gap and physical errors

Use the actual kernels: residual self-dot, division, both axpy updates and the inline direction
update. Add mixed bounds/range success from the existing arbitrary-error execution lemmas,
not another CG recurrence or program tree. A positive quotient has a positive computed value
only under its explicit mixed-error margin.

The residual-gap identity needs neither relative divisions nor normalized directions.
For `g_j=b-A*x_j-r_j`, given

```lean
s j = A *v p j + es j
x (j+1) = x j + alpha j • p j + ex j
r (j+1) = r j - alpha j • s j + er j
```

prove `g_(j+1)=g_j+alpha_j*es_j-A*ex_j-er_j`, then

```lean
norm g_k <= norm g_0 + sum j in range k,
  abs (alpha j)*norm (es j) + specNorm A*norm (ex j) + norm (er j)
```

Generalize once to arbitrary conformable real/complex matrices if existing norm API permits.
Use a direct theorem on the update equations before adding any new run record. Instantiate
with mixed local vector budgets to expose the absolute contributions. Recover the existing
CGRun gap theorem as a consumer where practical. Physical solution-error bounds should use
the iterate-update defect directly whenever this avoids an extra condition-number factor.

Reviewed active-prefix transfer: `Krylov/FinitePrecision/CGRunMixed.lean` adds
`CGRun.ofAbsRelErr`, a constructor of the existing run rather than a new record. It takes
actual data arrays and update equations, a base relative budget `u>=0`, target `u<=eps<=1/100`,
and nodewise absolute allowances. Every local normwise envelope `u*S+eta` has an explicit
margin `eta<=(eps-u)*S`; cache and division margins use the exact scalar magnitude. Actual
cache and curvature positivity on steps taken are independent hypotheses. Relative scalar
witnesses are selected with `AbsRelErr.relErr_of_le`; other defects are absorbed algebraically.
All supplied data arrays and error vectors are retained definitionally. This permits reuse
of every applicable existing CGRun theorem on a scale-certified prefix, while correctly
excluding a zero-cache underflow endpoint with a nonzero residual. It is not an input-only
proof that an execution remains in that regime.

## Lanczos normalization and existing backward theory

The first common normalization statement takes an explicitly nonzero computed divisor beta
and component mixed division errors. It gives

```lean
norm (WithLp.toLp 2 (x-beta • y)) <=
  u*norm (WithLp.toLp 2 x)+abs beta*Real.sqrt (Fintype.card n)*eta
```

For the naive norm kernel, bound the self-dot cache and subsequent square root separately.
The squared-cache to norm estimate retains the actual error coefficient and holds for every
nonnegative coefficient, without a smallness window. Smallness margins enter only when a
near-unit or nonzero-continuation conclusion is wanted.
Its no-overflow premise must cover squared products and sums, even when the final true norm
would itself fit. Expose the computed norm/divisor and a margin before asserting near-unit
output or nonzero continuation. Keep a raw zero-cache small-vector certificate at breakdown.

The supplied NumLean `Sqrt.lean` is proof material for actual Float sqrt accuracy and range
success, under the same provenance/redistribution record as the existing local port. A direct
checked Float sqrt theorem may be added without a parallel full scalar contract. If needed
by more than one operation consumer, factor a minimal operation-family interface and review
its exact statement first.

Existing `LanczosData.recurrenceError` and adjacent-inner-product certificates already feed
the normalized backward model and spectral/matrix-function results. First derive their
defect bounds from mixed local operations; reuse the existing backward results. The fixed-q
program's zero padding additionally needs exact-zero operation facts; arbitrary absolute
errors alone permit spurious values at zero. Restrict a theorem to an active prefix until
that backend obligation is discharged.

A concrete next bridge can use representability, rather than assuming sign and exact-zero
preservation as new primitives. The planned binary-word separation statement is
`IsBinaryRep fmt z -> z=0 or 2^fmt.minExponent <= abs z`. If the output word satisfies that
separation, `eta < 2^fmt.minExponent` and `u<=1`, a mixed error certificate implies that a
nonnegative exact result has a nonnegative decoding. At an exact result of zero it forces
a zero decoding. IEEE nearest rounding has half-subnormal absolute allowance, so the strict
separation holds. These backend implications are not yet formalized by this extension;
they provide a route to norm-cache sign and exact-zero continuation using the same arithmetic
contract. Decoded comparisons and whole-loop range invariants remain separate obligations.

## Files, review, and completion criteria

Reviewed addition: the shared raw vector bound belongs in the existing
`ForMathlib/Analysis/InnerProductSpace/PiL2.lean`, as
`EuclideanSpace.norm_toLp_le_mul_add_of_forall_abs_le`. Its hypotheses are nonnegative
coefficients and coordinate bounds `abs e_i <= u*abs x_i+eta`; its conclusion is the
corresponding Euclidean bound with `sqrt(card n)*eta`. Supporting norm-of-coordinate-norm
and norm-of-constant facts are bridges to Mathlib's `EuclideanSpace.norm_eq` and
`PiLp.norm_toLp_const`, not new vector notions.

Planned additions are `Computation/VectorErrors.lean`, mixed BLAS consumers, CG kernel/gap
consumers and Lanczos normalization/sqrt consumers. Each additional file is recorded when its
exact API is reviewed. No new program, tree, target or unexplained named constant is planned.
New definitions, if genuinely required, receive vocabulary rows and Mathlib bridges.

Reviewed file allocation: extend `Computation/BLAS/Underflow.lean` with the mixed
`exec_axpy_norm_sub_le_of_absRelErr`, `exec_gemv_abs_sum_mul_sub_le_of_absRelErr` and
`exec_gemm_abs_sum_mul_sub_le_of_absRelErr` consumers. Put Frobenius/spectral norm corollaries
in `Matrix/Computation/Underflow.lean`, whose statements need matrix norms. Generalize the
existing arbitrary-error direction loop in `Krylov/LinearSystems/CGProgramDirection.lean`,
and add `CGProgramUnderflowKernels.lean` as its mixed numerical consumer. Generic rectangular
residual-gap and physical-update perturbation bounds go in `Matrix/Computation/ResidualGap.lean`.
Lanczos normalization algebra goes in `Computation/NormalizationErrors.lean`; measured
recurrence and adjacent-inner bounds go in `Krylov/FinitePrecision/LanczosDefects.lean`.
The minimal sqrt proof adaptation belongs in `ForMathlib/Data/Float/Sqrt.lean`, with actual
finite-word execution in `Computation/IEEESqrt.lean`. The exact decoder and maximum-finite-grid
bridges already proved for IEEE arithmetic are shared, rather than copied privately.

Acceptance requires strict module builds, extracted naming and placement checks, environment
lint, the standard axiom audit and complete `scripts/stage_check.sh` success. Report coverage
precisely: local/active-prefix or conditional backward results do not establish unconditional
whole-loop IEEE convergence. Record what genuinely remains rather than adding it as a premise
disguised as a proved property.

## Reviewed normalization and Lanczos proof slice

The Float/normalization audit reviewed this plan on 2026-11-05; the parent implementation
review approved these four topic files before code was written:

* `ForMathlib/Data/Float/Sqrt.lean`: adapt the supplied NumLean square-root proof to the
  already imported core Float model. Prove canonical rounding, mixed square-root accuracy,
  and nearest-grid facts, retaining explicit format assumptions wherever needed.
* `Computation/IEEESqrt.lean`: prove `exists_un_finiteFloatSem_sqrt` for every finite word
  whose decoded value is nonnegative. Its conclusion supplies actual checked square-root
  success, a nonnegative output decoding, and
  `AbsRelErr binary64.unitRoundoff binary64.underflowBound (Real.sqrt a) z`.
  Result finiteness is derived, not a premise. Native runtime refinement remains outside
  the logical certificate. No new complete scalar contract is introduced.
* `Computation/NormalizationErrors.lean`: derive a norm estimate from an explicit nonnegative
  self-dot cache and mixed square-root error. With `r` the exact nonnegative norm,
  `AbsRelErr alpha E (r^2) s`, `s >= 0`, `0 <= alpha <= 1`, and
  `AbsRelErr us etas (Real.sqrt s) q`, bound
  `abs (r-q)` by `(alpha+us*(1+alpha))*r+(1+us)*Real.sqrt E+etas`.
  For component divisions, use the shared vector error lemma and retain the computed
  positive divisor. If `D` bounds `norm (x-q*y)` and `A` bounds `abs (norm x-q)`, then
  `t=(D+A)/q` gives the squared near-unit estimate `t*(2+t)`; any nonzero continuation
  claim states its margin explicitly. The separately exposed linear estimate is
  `abs_norm_sub_one_le_of_div_of_absRelErr`; the squared estimate is its short consumer.
  `norm_sub_smul_inv_norm_le_of_div_of_absRelErr` additionally bounds the input-direction
  mismatch by `2*D+A`, including a zero decoded output through total inversion.
* `Krylov/FinitePrecision/LanczosDefects.lean`: work with the existing `LanczosData` and
  measured local operation equations. Recurrence error is at most `Eu+Ew+Ez+D`.
  Adjacent inner product is at most `Ealpha+abs alpha*g+norm v*(Ez+D)`, where `g`
  bounds the squared norm defect. These are numerical implications, not assumed
  successful execution or a second run model. Existing normalized backward and
  matrix-function results remain the downstream consumers.

Generic positivity of a mixed self-dot, exact zero equivalences, fixed-budget zero padding,
and an unconditional full IEEE Lanczos loop are deliberately absent from these statements.

## CG operation and physical-error amendment (2026-11-05)

Generalize the existing operational proof in `Krylov/LinearSystems/CGProgramDirection.lean`
to `IsArithErrSem.exec_cg_direction_update`, retaining the old relative theorem as a wrapper.
The generic result takes the existing error relation and safe predicate plus, for each
component, safety of `a*p_i` and of every `r_i+q` related to that product. It preserves the
same actual loop, state/count identity, memory usage and cell frame. Its output contains
the two primitive error relations, rather than assuming a desired vector defect.

Add `Krylov/LinearSystems/CGProgramUnderflowKernels.lean`, importing only lower operation
and vector-error files. It owns `IsArithErrSem.exec_cg_division`, with the actual divisor
nonzero and exact quotient safe, returning execution/count/frame and the supplied error
relation. It also lifts the actual direction loop through the shared mixed vector lemma.
The old relative division result becomes a wrapper where the import graph permits this;
neither mixed result asserts a positive computed coefficient. Zero is a permitted output.

Add `Matrix/Computation/ResidualGap.lean` for the generic update equations. Matrices may be
rectangular over any `RCLike` field, with arbitrary finite row and column index types.
For `s_j=A*p_j+es_j`, `x_(j+1)=x_j+alpha_j*p_j+ex_j` and
`r_(j+1)=r_j-alpha_j*s_j+er_j`, prove the one-step identity and cumulative estimate

```lean
norm (b - A *v x k - r k) <= norm (b - A *v x 0 - r 0) +
  sum j in range k,
    norm (alpha j) * norm (es j) + specNorm A * norm (ex j) + norm (er j)
```

No symmetry, positivity, quotient or nonzero-step assumption is needed. The same file
holds the local physical-energy perturbation bound

```lean
norm (quadForm A (e+d) - quadForm A e) <=
  specNorm A * (2*norm e*norm d + norm d^2)
```

This applies directly to the iterate-update defect, with `e=xstar-x-alpha*p` and
`d=-ex`, without converting residual error into solution error. The existing
`quadForm_add_right` and `norm_star_dotProduct_mulVec_le` provide the matrix algebra.
It is a local update-error result, not a convergence theorem. No second CG run structure,
new program tree, target or named numerical constant is introduced.

The existing relative `CGRun.norm_sub_mulVec_x_sub_r_succ_le` consumes this common
one-step defect bound. Its statement and numerical coefficients are unchanged; the relative
budgets are substituted only after the generic residual-gap estimate has been obtained.
