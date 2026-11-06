# Finite-format arithmetic and execution

2026-11-05. Requested scope: bounded floating point with gradual underflow, Lean `Float`,
IEEE formats and other arithmetic backends; SciLean is one possible consumer. The primary
prototype is the existing CG program's residual computation in bounded binary floating
point. Fixed-point arithmetic is a secondary interface test. The model does not replace
the registered algorithms or silently extend their relative-error theorems to IEEE.

## Intended users and guarantees

Numerical analysts need local errors, overflow conditions and subnormal behavior. TCS
users also need precision as a parameter, word lengths, operation/query counts and
explicit hypotheses behind a bit-complexity bound. Backend implementers need small
certificates that can be proved independently of an algorithm or a vector library.

Keep four obligations distinct:

1. Representation: what words encode, their finite range, and their storage width.
2. Arithmetic: successful primitive operations satisfy an error relation; range/domain
   conditions imply success. NaN and infinity have no faithful real decoding.
3. Execution: the actual program produces the recorded primitive/kernel trace.
4. Resources: the program tree supplies operation and logical workspace bounds; weighted
   charges require backend cost certificates to become bit-operation or runtime bounds.

A finite final result alone is not an input-only guarantee that an algorithm avoids
overflow. An equality of returned values alone is not an execution-cost correspondence.

For a TCS theorem the precision parameters and their dependence on dimension, condition
number and requested accuracy must stay visible. Binary significand precision controls
relative error; the smallest exponent controls the absolute underflow allowance; the
largest exponent controls the range certificate. A symbolic precision tag may carry
those choices while its interpretation supplies the corresponding word width. They are
independent obligations: increasing precision does not itself prevent overflow.

An arithmetic operation count is not yet a bit-operation bound. Keep counts by kind and
precision tag, then use the existing weighted charges or proved instruction substitution
for a chosen implementation. For example, a schoolbook integer multiplication cost can
depend quadratically on word width, whereas a hardware word-RAM model may assign unit
cost. Neither choice is built into the numerical error relation. Oracle-internal work,
index/address calculations, control overhead, conversions and native kernel scratch
space must be included explicitly before claiming a complete machine-runtime bound.
Finite word encodings certify representability, not the actual heap layout of a Lean
integer implementation. Input quantization from an exact mathematical problem is also a
separate error from arithmetic performed on the already stored input.

## Existing objects, searches, and sources

Reuse `ScalarSem`, `IsArithErrSem`, `IsRelErrSem`, `IsDotTrace`, `StaticCost`,
`Prog.staticCost`, `Interp.width` and operation charges. `IsArithErrSem` already takes an
arbitrary error relation and a safe exact-result predicate; no parallel scalar contract
is needed for the prototype. The successful-execution and range requirements in its
kernel theorems remain explicit.

Searched the pinned Mathlib `Data/FP/Basic.lean`, real rounding and approximation APIs,
and NLAlib's arithmetic contracts and BLAS rounding proofs. Mathlib's experimental FP
implementation contains unsafe operations and does not provide the needed certified
arithmetic contract. Use Lean core's `Float.Model.Format` directly for IEEE layout and
its logical `Float.Model` operations, rather than introducing a second IEEE type.
No existing mixed absolute-relative primitive error predicate was found.

The supplied NumLean archive has `IEEEBinary`, proved binary32/64 scalar error bounds,
and underflow-aware kernel bounds. The minimal core-model proof chain has now been adapted
to the existing Lean/Mathlib 4.33.1 pin, with explicit exponent-layout hypotheses. The port
and its provenance are detailed below. No private mandatory dependency or build-pin change
is needed. Native kernel replacements remain a separate trust obligation.

Arithmetic provenance: Higham, *Accuracy and Stability of Numerical Algorithms*, second
edition, sections 2.2 and 3.1. The prototype uses conservative geometric accumulation
instead of requiring a rational gamma bound with an implicit smallness premise. Gradual
underflow introduces an absolute term; overflow is handled by an explicit exact-result
range condition, rather than absorbed into a relative-error constant.

## Interfaces and exact statement shapes

The first core addition is a relation, not a backend type class:

```lean
def AbsRelErr (u eta a z : Real) : Prop := abs (a - z) <= u * abs a + eta
```

Its constructor is the raw inequality. The API transports existing `RelErr`, recovers
`RelErr` when the absolute allowance is zero and `u` is nonnegative, composes multiplication
and addition defects, and certifies the magnitude compatible with a computed zero:

```lean
theorem RelErr.absRelErr (h : RelErr u a z) (heta : 0 <= eta) :
    AbsRelErr u eta a z

theorem AbsRelErr.relErr (h : AbsRelErr u 0 a z) (hu : 0 <= u) :
    RelErr u a z

theorem AbsRelErr.abs_add_sub_le
    (hm : AbsRelErr um etam a q) (ha : AbsRelErr ua etaa (b + q) z)
    (hua : 0 <= ua) :
    abs (b + a - z) <= ua * abs b + (um + ua + um * ua) * abs a +
      (1 + ua) * etam + etaa
```

Consumers instantiate the existing contract with
`fun p op => AbsRelErr (u p) (eta p op)`. This permits exact, fixed-point and IEEE-style
error allowances, operation-specific underflow, and mixed precision through existing
tags. It does not assert that deterministic error bounds suffice for stochastic-rounding
martingale results; those need a separate probabilistic certificate.

Precision tags do not by themselves prove that a stored word belongs to its tag's physical
format. A concrete mixed binary32/binary64 backend needs tag-validity invariants or an
appropriate dependent/sum-carrier adapter. The present Float endpoint uses one binary64
format. Likewise, the first arithmetic certificate covers the existing four binary
arithmetic operations; fused operations, IEEE status flags and additional rounding modes
need their own execution contracts when introduced.

For concrete IEEE representation, `IsBinaryRep fmt a` states a bounded signed-integer
mantissa and bounded exponent representation of the real value. Its format is core's
`Float.Model.Format`; it adds no arithmetic operations. The Float backend proves its
finite-word decoding meets this predicate and exposes a checked `ScalarSem` that rejects
nonfinite operands/results. The separate `IEEE.lean` adapter now proves scalar accuracy
and range success on its finite-word carrier, using core's actual logical Float operations.

## CG proof of concept

Use the actual `dot` kernel called by the registered CG tree to compute its cached
squared residual. Existing pure-relative analysis proves the cache is zero exactly when
the vector is zero. This equivalence is false in finite formats with underflow.

For `N` terms and nonnegative `u, eta`, prove a mixed-error dot trace bound of the form

```lean
abs ((sum i, r i ^ 2) - nu) <=
  ((1 + u) ^ (2*N) - 1) * (sum i, r i ^ 2) +
  N * (1 + u) ^ (2*N) * (2 + u) * eta
```

Then expose the actual kernel execution, its returned word and store frame, followed by
the stopping certificate

```lean
nu = 0 ->
  norm (WithLp.toLp 2 r) ^ 2 <=
    (N * (1 + u) ^ (2*N) * (2 + u) * eta) / (2 - (1 + u) ^ (2*N))
```

with `0 < 2 - (1+u)^(2*N)` explicit. Empty kernels remain meaningful. Range assumptions
remain present in the execution theorem. No new CG recurrence, program tree, target,
global no-overflow assertion, or all-iterations convergence claim is introduced.

## Files and vocabulary

| File | Objects and consumers |
| --- | --- |
| `Computation/Underflow.lean` | `AbsRelErr`, its raw inequality constructor/API, relative-only transport; BLAS, CG, future algorithms |
| `Computation/BLAS/Underflow.lean` | accumulated mixed-error bounds on actual dot traces and executions |
| `Krylov/LinearSystems/CGProgramUnderflow.lean` | CG self-dot and zero-cache residual certificate |
| `Computation/Float.lean` | checked Float semantics, finite decoding, core-format representation and execution certificates |
| `Computation/BinaryFloat.lean`, `BinaryFloatSem.lean` | general bounded binary quantizer, finite carrier, scalar accuracy and range success |
| `Computation/IEEE.lean` | actual Lean Float scalar arithmetic and exact-zero-addition certificates |
| `ForMathlib/Data/Float/*.lean` | upstream-candidate core-model rounding, packing and arithmetic proofs |
| `Krylov/LinearSystems/CGProgramBinaryFloat.lean`, `CGProgramIEEE.lean` | mathematical bounded-format and actual binary64 CG residual-dot execution |

Add the vocabulary rows with their bridges to CONTRIBUTING when the corresponding
definitions exist. Keep scalar real inequalities about NLAlib's error relation in its
Computation topic; do not create a competing real analysis library. The adapted NumLean proof chain consumes these interfaces; the original private package
is not a library dependency.

## Next stages and limits

After this prototype: propagate operation-dependent absolute terms through full CG/Lanczos;
establish whole-loop input-based range invariants or explicit exceptional outcomes;
instantiate weighted costs for finite-word backends. Fixed-point and arbitrary precision endpoints should use the
same scalar contract, not inherit IEEE-specific representation assumptions.

Existing approved targets and build pins are unchanged. Formal numerical claims are
conditional on their stated contracts; the prototype must not advertise an end-to-end
IEEE CG theorem. Cost and workspace results remain the existing independently proved
ones for the actual program trees.

## Implemented scope and read-back

The general error API is independent of binary formats, a scalar implementation, and a
vector library. `IsBinaryRep` is confined to the concrete binary representation layer.
The generic kernel theorem consumes the existing range-aware arithmetic contract.

| Layer | Implemented evidence | Remaining obligation |
| --- | --- | --- |
| Mixed arithmetic errors | `AbsRelErr`, error composition, zero/positivity certificates, relative-only compatibility | probabilistic certificates for randomized rounding, if needed |
| Lean Float representation | binary64 exponent/significand bounds and an injective 64-bit encoding | other concrete encodings as consumers require |
| Checked Float arithmetic | finite-word carrier, erasure to checked primitives, proved scalar mixed-error accuracy and forward range success | arbitrary rational literal accuracy; native runtime refinement |
| Bounded binary floating point | finite carrier, variable normal spacing, uniform subnormals, scalar accuracy and range-success contract | independently shifted exponent windows and additional rounding modes |
| Bounded fixed point (secondary) | computable finite carrier, positive-scale accuracy and range-success contract | a certified native packed implementation and its costs |
| CG residual kernel | actual execution and write/read; bounded binary and actual Float specializations with input-only range conditions | whole-loop finite-format CG and a true-residual gap bound |
| Resource accounting | existing unchanged program-tree operation/workspace proofs; execution regressions on both backends | costs of underlying machine arithmetic, addressing and native storage |

The concrete bounded binary and IEEE CG theorems quantify over the actual interpreter and
store. Their scalar semantics equal the chosen backend; vector entries decode to the stated
residual; the destination is writable without overwriting the source. The input norm/range
inequality suffices for successful execution and the numerical bound. There is no assumed
backend-accuracy certificate left to discharge in these specializations. The separate
fixed-point specialization exercises the same general interface at zero relative error.

`NLAlibTools/FinitePrecisionSmoke.lean` runs the original compiled CG tree rather than
another recurrence. It checks all returned scalar words exactly, operation budgets, logical
bit memory including initial buffers and ROM, and workspace cleanup on successful cases.
It exercises normal arithmetic, budget exhaustion, underflow-induced zero caches and
checked failure on overflow. These regressions complement the proofs; they do not prove
all Float executions accurate or certify the native runtime of integer/rational kernels.

## Amendment: constructive bounded fixed-point endpoint (2026-11-05)

To exercise the interface independently of IEEE and SciLean, add
`Computation/FixedPoint.lean`. The carrier is the finite set of integers of absolute value
at most a natural-number limit, decoded on a grid with arbitrary positive natural scale:

```lean
abbrev FixedPoint (limit : Nat) := {w : Int // abs w <= (limit : Int)}
def fixedPointDecode (scale : Nat) {limit : Nat} (w : FixedPoint limit) : Real :=
  (w.val : Real) / (scale : Real)
def fixedPointSem {P : Type} (scale limit : Nat) : ScalarSem P (FixedPoint limit)

theorem isArithErrSem_fixedPointSem {P : Type} (scale limit : Nat)
    (hscale : 0 < scale) :
    IsArithErrSem (fun _ _ => AbsRelErr 0 (1 / (scale : Real)))
      (fun _ => fixedPointDecode scale)
      (fun _ a => abs a <= (limit : Real) / (scale : Real))
      (fixedPointSem (P := P) scale limit)

theorem addsZeroExactly_fixedPointSem {P : Type} (scale limit : Nat)
    (hscale : 0 < scale) :
    AddsZeroExactly (fun _ => fixedPointDecode scale)
      (fixedPointSem (P := P) scale limit)
```

Addition and subtraction are checked exact integer operations. Multiplication, division
and rational literals compute with rationals, round down to the grid, and reject a rounded
integer outside the carrier. Division by zero is rejected. Negation and real conjugation
are exact. Comparisons use the integer order; conversion keeps the same grid. Square root
and bit operations are not supplied by this endpoint; the certificate concerns the four
arithmetic operations of `IsArithErrSem` only. Scale zero has no accuracy certificate.

The rounding theorem bounds absolute error by `1 / scale`; the range-success theorem uses
the conservative exact-value condition `abs a <= limit / scale`. The zero-addition theorem
allows the endpoint to instantiate the existing dot-product execution theorem. This does
not certify a fixed native representation or runtime: the mathematical carrier is finite,
while its implementation uses Lean integers/rationals and their costs remain separate.
Mixed-error traces and their CG consumers use the same existing operation/error interface.

Mathlib reuse: rational arithmetic and the `Int.floor_le`, `Int.lt_floor_add_one`, and
`Int.le_floor` laws. Searched for bounded fixed-point semantics and a contract bridge, none
found in Mathlib or NLAlib. No new program tree or target is introduced.

## Amendment: bounded binary floating-point quantization (2026-11-05)

The main floating-point prototype must use variable spacing. Fixed point remains only an
independent interface example. Add `Computation/BinaryFloat.lean`, reusing core
`Float.Model.Format` and the existing `IsBinaryRep` predicate. Write `p = fmt.mantissaBits`,
`emin = fmt.minExponent`, and `emax` for the upper significand exponent in `IsBinaryRep`.
For a nearest-integer selector `r : Real -> Int`, require the existing error interface
`forall x, AbsRelErr 0 (1/2) x (r x : Real)`. This admits every nearest tie policy, including
ties to even. It does not identify Mathlib's ties-up `round` with Lean's `Float` arithmetic.

```lean
noncomputable def binaryFloatRound (fmt : Float.Model.Format)
    (r : Real -> Int) (x : Real) : Real :=
  let e := fmt.targetExponent (Int.log 2 (abs x) + 1)
  (r (x / (2 : Real)^e) : Real) * (2 : Real)^e

theorem absRelErr_binaryFloatRound (hround : forall x, AbsRelErr 0 (1/2) x (r x)) :
  AbsRelErr ((2 : Real)⁻¹ ^ fmt.mantissaBits) ((2 : Real)^fmt.minExponent / 2)
    x (binaryFloatRound fmt r x)

theorem isBinaryRep_binaryFloatRound (he : 2 <= fmt.exponentBits)
    (hround : forall x, AbsRelErr 0 (1/2) x (r x))
    (hx : abs x <= fmt.maxFinite) :
  IsBinaryRep fmt (binaryFloatRound fmt r x)

theorem binaryFloatRound_eq_self (hround : forall x, AbsRelErr 0 (1/2) x (r x))
    (hx : IsBinaryRep fmt x) : binaryFloatRound fmt r x = x
```

The exponent is `max (floor(log2(abs x))+1-p) emin`: spacing scales with magnitude in the
normal range and stays at `2^emin` only in the subnormal range. The accuracy theorem gives
relative error `2^-p` plus the half-subnormal spacing. This additive allowance is a uniform
bound over all magnitudes; the normal-region theorem removes it. Mantissa carry is renormalized by
halving the boundary mantissa and incrementing its exponent; the input range hypothesis
excludes a carry beyond `emax`. Add `Float.Model.Format.maxFinite_pos`, `IsBinaryRep.abs_le` and
`IsBinaryRep.neg` for the checked finite-carrier backend. Grid exactness supplies exact
zero addition and establishes that this is a floating-point quantizer, not fixed-point
rounding over the whole range.

The subsequent backend can reject exact results outside `[-fmt.maxFinite, fmt.maxFinite]`
before rounding; that is an explicit conservative overflow guard. The real mathematical
quantizer is noncomputable and has no claim to be native IEEE execution. Its numerical
accuracy and finite-range certificates are proved independently of the separate Lean
`Float` correspondence layer. The CG consumer must instantiate this bounded floating-point
endpoint rather than advertise a fixed-point example as the floating-point prototype.

Reuse searched: `Real.roundNearest_mem_floatGrid`, `Real.abs_sub_roundNearest_le` and
`Real.roundNearest_eq_self_of_mem_floatGrid` provide the unbounded-format proof patterns;
`Int.log` supplies the binade bounds; core `Format.targetExponent` supplies the lower clamp.
No bounded binary mixed-error arithmetic endpoint exists in the pinned Mathlib or NLAlib.
The tie-independent integer selection and mixed absolute-relative interface are shared;
no second IEEE bit layout or abstract scalar execution model is introduced.

The binary quantizer also exposes two behavior certificates. In the normal range,
`fmt.minExponent <= Int.log 2 (abs x)+1-fmt.mantissaBits`, the error satisfies the pure
relative interface `RelErr (2^-p) x (binaryFloatRound fmt r x)` without an additive term.
At the positive quarter-subnormal value `x = 2^(fmt.minExponent-2)`, every nearest integer
selector rounds to zero. The latter is independent of the tie policy because the scaled
input is `1/4`, strictly closer to zero than to another integer. These statements make the
normal/subnormal distinction explicit; neither assumes globally uniform spacing.

## Amendment: input-only fixed-point CG range certificate (2026-11-05)

Add `IsDotTrace.abs_add_le_of_absRelErr_zero` to `Computation/BLAS/Underflow.lean`.
For a prefix of length `k < N` with absolute arithmetic allowance `eta >= 0`, and a next
product `q` satisfying the same allowance, prove the input-only accumulation estimate

```lean
theorem IsDotTrace.abs_add_le_of_absRelErr_zero
    (h : IsDotTrace (fun _ => AbsRelErr 0 eta) x y k s)
    (heta : 0 <= eta) (hkn : k < N)
    (hq : AbsRelErr 0 eta (x k * y k) q) :
    abs (s k + q) <= (sum i in range N, abs (x i * y i)) + 2*N*eta
```

The existing mixed-error theorem simplifies to prefix error at most `2*k*eta` when
`u = 0`. The accumulation estimate then bounds every exact next sum in the range premises
of the actual dot execution theorem. Each exact next product is bounded by the total
sum of absolute products. Thus `sumAbsProducts + 2*N*eta <= L` discharges those range
premises from the inputs and a safe radius `L`; it is not a hypothesis about observed
intermediate states.

Add `Krylov/LinearSystems/CGProgramFixedPoint.lean`, importing the concrete fixed-point
endpoint and the generic CG underflow consumer. Its execution theorem uses the endpoint's
proved arithmetic and exact-zero-addition certificates, with the input condition

```lean
norm (WithLp.toLp 2 r) ^ 2 + 2*N/(scale : Real) <= (limit : Real)/(scale : Real)
```

It proves actual CG residual-dot execution, the destination store write/read, and
`abs (norm r ^ 2 - nu) <= 2*N/scale`. A zero cache therefore certifies
`norm r ^ 2 <= 2*N/scale`. The theorem keeps arbitrary positive scale, limit and dimension,
including dimension zero; layout and writable-cell conditions remain explicit. This is a
fully instantiated bounded arithmetic result for the kernel used by the registered CG
trees, not a full solver theorem or a native fixed-point runtime certificate.

## Finite Float carrier amendment (2026-11-05)

The raw `checkedFloatSem` is an operational interpreter, not a candidate instance of
`IsArithErrSem`: the raw type contains NaN and infinities, while that contract requires
negation/conjugation success for every word and specifies success through real decoding.
A junk decoding of nonfinite words cannot supply those obligations.

Add `FiniteFloat := {x : Float // x.isFinite = true}` and a `finiteFloatSem` obtained by
proof-erased lifting of the checked interpreter's already finite outputs. Prove that
forgetting the subtype returns exactly `checkedFloatSem` for literals, arithmetic, unary
operations, comparisons and conversion; inherit its injective 64-bit word encoding.
The lift adds no further finiteness checks. This valid-word carrier is the IEEE
arithmetic-contract endpoint; its scalar accuracy and range-success proofs are now in
`IEEE.lean`. Representation alone makes no numerical or runtime claim and changes no
existing program tree.

The general impossibility theorem `not_isArithErrSem_checkedFloatSem` formalizes the raw
carrier obstruction, independently of the chosen error relation or real decoding. The
accuracy adapter targets `finiteFloatSem`, not the raw interpreter. The
current raw rational-literal implementation converts numerator and denominator
separately; a full literal accuracy/range contract needs additional work. This does not
affect the arithmetic interface's zero-literal guarantee in the present prototype.

## Amendment: bounded binary floating-point CG prototype (2026-11-05)

The maintainer clarified that the priority is bounded floating point, with approximately
constant relative precision in the normal range and a fixed grid only in the subnormal
range. The fixed-point example remains a secondary illustration; no further fixed-point
features are planned here.

Extend `Computation/BLAS/Underflow.lean` with mixed-error range control for arbitrary
nonnegative `u` and `eta`. Write `P_N = (1+u)^(2*N)` only as notation in this note. For a
dot prefix of length `k < N`, prove

```lean
theorem IsDotTrace.abs_add_le_of_absRelErr
    (h : IsDotTrace (fun _ => AbsRelErr u eta) x y k s)
    (hu : 0 <= u) (heta : 0 <= eta) (hkn : k < N)
    (hq : AbsRelErr u eta (x k * y k) q) :
    abs (s k + q) <=
      (1+u)^(2*N) * (sum i in range N, abs (x i * y i)) +
      N * (1+u)^(2*N) * (2+u) * eta
```

The corresponding right side bounds every exact next accumulation and dominates each
exact product magnitude. Requiring it to lie inside the backend's safe representable
radius therefore discharges every intermediate range condition using only the inputs,
dimension, precision and exponent limits.

Add `Krylov/LinearSystems/CGProgramBinaryFloat.lean` to instantiate the existing actual
CG residual-dot theorem with the bounded binary floating-point endpoint's proved scalar
contract. The result retains the kernel execution, destination write/read, mixed-error
bound and absolute-underflow zero-cache certificate. The input-only range condition is

```lean
(1+u)^(2*N) * norm r ^ 2 + N*(1+u)^(2*N)*(2+u)*eta <= maxFinite
```

This does not introduce a CG tree, change a target, assert native IEEE equivalence, or
claim full-loop convergence. Representation and arithmetic model certificates belong
to the bounded binary endpoint; the CG file only consumes their general interfaces.

The generic CG consumer also gets an input-only execution wrapper in
`CGProgramUnderflow.lean`, shared by the binary model and later finite IEEE adapters:

```lean
theorem IsArithErrSem.exec_cg_self_dot_of_absRelErr_of_abs_le
    (h : IsArithErrSem (fun p _ => AbsRelErr (u p) (eta p)) dec safe I.sem)
    (hz : AddsZeroExactly dec I.sem)
    -- existing store, layout, and nonnegative-allowance arguments
    (hsafe : forall a, abs a <= L -> safe tag a)
    (hrange : (1+u tag)^(2*N) * norm r ^ 2 +
      N*(1+u tag)^(2*N)*(2+u tag)*eta tag <= L) :
    -- the same actual execution, destination write/read, mixed error and zero-cache
    -- certificate as exec_cg_self_dot_of_absRelErr
```

This wrapper leaves no trace-prefix range hypothesis to a consumer. Its binary-format
corollary supplies the scalar and exact-zero-addition certificates from the bounded
floating-point semantics rather than accepting them as independent premises.

## Bounded binary scalar semantics (2026-11-05)

`Computation/BinaryFloatSem.lean` supplies the scalar interpretation of the bounded
binary quantizer in `BinaryFloat.lean`. It is a mathematical floating-point model, not
an asserted replacement for native Float operations. Its carrier contains only values
represented by the format; this avoids the invalid-word issue of the raw Float carrier.

```lean
abbrev BinaryFloat (fmt : Float.Model.Format) := {x : Real // IsBinaryRep fmt x}

noncomputable def binaryFloatSem {P : Type} (fmt : Float.Model.Format)
    (he : 2 <= fmt.exponentBits) (r : Real -> Int)
    (hround : forall x, AbsRelErr 0 (1/2) x (r x : Real)) :
    ScalarSem P (BinaryFloat fmt)
```

The integer rounding selector may use any nearest tie policy. Its certificate bounds
rounding by half an integer unit; no theorem identifies Mathlib's ties-up rule with
IEEE ties-to-even. The format's exponent floor produces the uniform subnormal lattice,
while normal values retain floating precision. The finite upper range is checked before
rounding; this conservative overflow policy is explicit and is not claimed to reproduce
every native IEEE overflow boundary.

Prove the existing arithmetic contract with relative allowance
`(2 : Real)⁻¹ ^ fmt.mantissaBits`, absolute allowance `2 ^ fmt.minExponent / 2`, and safe
exact-result predicate `abs a <= fmt.maxFinite`. Negation/conjugation are exact;
adding zero is exact because the quantizer fixes represented values. Division rejects a
zero divisor. The first endpoint leaves square root and bit operations unsupported;
CG's present arithmetic needs only the four certified binary operations. Tags share one
format, and precision/range/word-cost choices remain independent interfaces.

The scalar certificate names are `isArithErrSem_binaryFloatSem` and
`addsZeroExactly_binaryFloatSem`, each taking `fmt`, `he`, `r`, `hround`. No new program,
target, build pin or private dependency is introduced.

## Concrete Lean Float proof port (2026-11-05)

The supplied NumLean proof material elaborates against the existing Lean 4.33 pin after
making the two-exponent-bit condition explicit and adapting a few core lemma names.
The initial compatibility audit incorrectly treated `unpack_pack_unpack` as a missing core
lemma; it is proved by NumLean itself. The arithmetic adapter can therefore be proved
locally without a private dependency or a toolchain change.

Proof provenance: `NumLean-master.zip`, SHA-256
`01041d582ff6189102e567ecb9bfc8cb1b21cda0c0ffc840245fd116465904cc`.
Source topics are `NumLean/Data/Scalars/IEEE/{Basic,Mantissa,Round,Pack,Ops}.lean`,
`NumLean/Mathlib/Rounding/BinaryFormat.lean`, and the small natural-logarithm helper.
The archive contains no commit metadata, author headers, LICENSE or COPYING file.
Attribution to NumLean is retained; the archive does not establish redistribution terms
for the original proof code. No upstream license or permission is inferred from the archive;
its redistribution terms remain unconfirmed in this provenance record.

Place pure facts about core Float types in upstream-candidate modules
`ForMathlib/Data/Float/{Basic,Mantissa,BinaryFormat,Rounding,Pack,Operations,Literals}.lean`
and the searched logarithm lemma in `ForMathlib/Data/Nat/Log2.lean`. No statement there
uses Computation vocabulary. The concrete arithmetic contract belongs in
`Computation/IEEE.lean`, where successful checked operations are decoded to real values,
accuracy follows from the core operation proofs, and exact-result range conditions
suffice for finite output. The proof follows the actual native Float logical definitions;
it does not identify native rounding with the separate mathematical ties-up model.

The adapter establishes `IsArithErrSem` and `AddsZeroExactly` on `FiniteFloat`, with
binary64 unit roundoff and underflow spacing, including genuine forward range-success
clauses. The upstream Float zero-literal fact uses `import all Init.Data.OfScientific`
because Lean 4.33 has not exposed the definition of `Float.ofNat`; Batteries uses the same
import for that reason. This changes proof visibility, not the arithmetic operations, axioms or build pins.
The proof chain must pass the existing standard-axiom audit and kernel replay.

Format constants use the upstream-style core API `Format.maxFinite`, `unitRoundoff`,
`underflowBound`, and `maxExponentBound`. The mathematical-model endpoint also uses this shared
maximum-finite-value API, so consumers have one spelling for the same quantity.

## Actual Lean Float CG residual certificate (2026-11-05)

Add `Krylov/LinearSystems/CGProgramIEEE.lean`. The actual finite-word scalar endpoint is
now certified by `isArithErrSem_finiteFloatSem` and `addsZeroExactly_finiteFloatSem`, so
the generic input-only CG residual-kernel theorem can be instantiated without an abstract
backend-accuracy assumption. Keep the exact binary64 constants visible:

```lean
u = (2 : Real)^(-53 : Int)
eta = (2 : Real)^(-1075 : Int)
M = ((2 : Real)^53 - 1) * (2 : Real)^(971 : Int)
```

The theorem `CGImplementation.exec_self_dot_of_sem_eq_finiteFloatSem` takes an
interpretation over `FiniteFloat`, with `I.sem = finiteFloatSem`, the existing store/layout
and writable-destination conditions, and the input-only range condition
`(1+u)^(2*N) * norm r^2 + N*(1+u)^(2*N)*(2+u)*eta <= M`. It concludes actual execution of
the CG residual `dot`, its destination store write/read, and the decoded cache's mixed
error bound. When `(1+u)^(2*N) < 2`, a zero cache certifies
`norm r^2 <= N*(1+u)^(2*N)*(2+u)*eta / (2-(1+u)^(2*N))`.

The scalar certificate proves forward range success at the full finite binary64 magnitude;
no extra safety margin or observed intermediate-finiteness hypothesis is introduced. This
certifies the actual Lean Float logical operations on finite words in the checked endpoint,
not native runtime replacement correctness, an arbitrary rational-literal pipeline, or a
complete CG loop. The residual is the decoded recursive vector supplied to the kernel;
the true residual of a computed iterate still needs the residual-gap analysis.

## Mixed-error theory extension (2026-11-05)

The reviewed [mixed-error design](Mixed-Error-Krylov.md) extends the local prototype toward
the existing relative-only coverage. The arithmetic/run interfaces and approved program
trees are retained. The main statement read-back is:

| Layer | New result | Scope and conditions |
| --- | --- | --- |
| Scalar errors | Absolute-to-relative absorption and multiplication-back of a rounded quotient | Explicit scale margins for relative transfer; quotient defect bound also permits a zero computed quotient |
| Vector errors | Mixed Euclidean error and axpy/division composition | Separate multiplication/addition allowances; absolute terms scale with square root of dimension |
| BLAS | Actual axpy/gemv/gemm execution, component and Frobenius/spectral bounds | Input-only safe-radius conditions discharge intermediate range obligations |
| CG kernels | Generic division/direction execution with counts and store frames | Actual nonzero divisor and safe exact-result conditions; no assumption that a positive quotient stays positive |
| Residual gap | Arbitrary rectangular real/complex update equations and accumulated defect bound | Includes initial gap and zero step lengths; no scalar relative model, positivity, SPD or horizon hypothesis |
| Physical updates | Direct quadratic-error perturbation | Uses the iterate-update defect directly, without residual-to-error conversion |
| Float sqrt | Actual finite-word sqrt success, nonnegative output, mixed accuracy | Nonnegative finite input; native runtime correctness remains a separate boundary |
| Normalization | Squared-cache to norm, linear/squared near-unit error and direction mismatch | Computed divisor and absolute terms remain explicit; positive-divisor and continuation margins are stated |
| Lanczos data | Arbitrary local equations give measured recurrence and adjacent-inner defects | Reuses existing data/backward theory; old relative identities are corollaries |
| CG run transfer | `CGRun.ofAbsRelErr` preserves actual data in the existing relative run | Absolute defects fit local relative-budget margins, with actual positive cache/curvature on the active prefix |

The remaining implementation work is whole-loop finite-range and guard certification,
including exact-zero behavior at underflow continuation. Mixed error inequalities alone
do not imply sign preservation, exact-zero arithmetic or the absence of overflow. No such
property is added as an unproved conclusion of the new bounds.
