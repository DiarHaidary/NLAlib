# Rounded BLAS in Euclidean norms

## Scope and placement

`NLAlib/Matrix/Computation/BLAS.lean` supplies normwise corollaries of the actual
`dot`, `axpy` and `gemv` executions already proved in
`NLAlib/Computation/BLAS/RoundingErrors.lean`. The Computation topic cannot import
the Matrix vocabulary `frobNorm` and `specNorm`; Matrix can import Computation.
These are supporting arithmetic adapters, not new programs, cost targets or
machine arithmetic instances. The arithmetic contract remains the existing
input-only `IsRelErrSem` contract with every value in range. In particular these
results do not certify unrestricted IEEE execution.

The proofs retain successful execution and the exact single-cell or block write
witnesses. Their only additional hypotheses are the existing small-roundoff
windows, decoded input storage, writable output cells and non-overlap conditions.
No hypothesis assumes the normwise conclusion. Empty vector dimensions and zero
inputs remain permitted.

## Existing material and reuse

The three componentwise error theorems are
`IsRelErrSem.exec_dot_abs_sum_mul_sub_le`, `IsRelErrSem.exec_axpy`, and
`IsRelErrSem.exec_gemv_abs_mulVec_sub_le`. Their operation order and storage
claims are inherited unchanged. Cauchy–Schwarz is
`EuclideanSpace.abs_dotProduct_le_norm`; the matrix bounds are
`norm_toLp_mulVec_le_frobNorm_mul` and
`frobNorm_le_sqrt_card_mul_specNorm`. The source for the scalar bounds is
[Higham2002, §§2.2, 3.1, 3.5].

Searches in Mathlib PiL2/PiLp and NLAlib found no finite-coordinate Euclidean
norm monotonicity lemma with arbitrary `RCLike` coordinates. Add the following
upstream candidate to `ForMathlib/Analysis/InnerProductSpace/PiL2.lean`:

```lean
theorem EuclideanSpace.norm_toLp_le_norm_toLp
    {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] {x y : n → 𝕜}
    (h : ∀ i, ‖x i‖ ≤ ‖y i‖) :
    ‖WithLp.toLp 2 x‖ ≤ ‖WithLp.toLp 2 y‖
```

## Public interfaces

The following common variables and dot hypotheses are abbreviated only in this
design record. The source declarations spell out each storage hypothesis:

```lean
variable {P ι K C : Type} [DecidableEq P] [AddMonoid C]
  (I : Interp P ι K C) (p : P) (st : St P K C)
  {dec : P → K → ℝ} {u : P → ℝ}
  (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
```

`IsRelErrSem.exec_dot_abs_dotProduct_sub_le` takes precisely the arguments and
hypotheses of `exec_dot_abs_sum_mul_sub_le`: `hz`, `dst`, `x`, `xo`, `y`, `yo`,
`n`, `xs`, `ys`, `hn`, `hx`, `hy`, `hdx`, `hdy`, `hdst`. Its conclusion is:

```lean
∃ st' w, exec I (dot p dst x xo y yo n).run st = some st' ∧
  st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
  |(fun i : Fin n.eval => xs i) ⬝ᵥ (fun i : Fin n.eval => ys i) - dec p w| ≤
    roundingFactor n.eval (u p) * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ *
      ‖WithLp.toLp 2 (fun i : Fin n.eval => ys i)‖
```

`IsRelErrSem.exec_dot_self_relErr` specializes those arguments to a self-dot
(`y = x`, `yo = xo`, `ys = xs`, retaining one read/disjointness premise). It
returns the identical execution/write witnesses and

```lean
RelErr (roundingFactor n.eval (u p))
  (‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ ^ 2) (dec p w)
```

`IsRelErrSem.exec_axpy_norm_sub_le` takes precisely all arguments and hypotheses
of `exec_axpy` and returns its execution/block-write witnesses together with

```lean
‖WithLp.toLp 2 (fun i : Fin n.eval => ys i + av * xs i - dec p (W i))‖ ≤
  roundingFactor 2 (u p) *
    (‖WithLp.toLp 2 (fun i : Fin n.eval => ys i)‖ +
      |av| * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖)
```

`IsRelErrSem.exec_gemv_norm_sub_le_frobNorm_mul` takes precisely all arguments
and hypotheses of `exec_gemv_abs_mulVec_sub_le`, including rectangular dimensions
`m n : IExp ℕ`, and returns its execution/block-write witnesses together with

```lean
‖WithLp.toLp 2 (M *ᵥ xv - fun i : Fin m.eval => dec p (W i))‖ ≤
  roundingFactor n.eval (u p) * frobNorm M * ‖WithLp.toLp 2 xv‖
```

`IsRelErrSem.exec_gemv_norm_sub_le_specNorm_mul` has identical inputs/witnesses,
with the final estimate

```lean
‖WithLp.toLp 2 (M *ᵥ xv - fun i : Fin m.eval => dec p (W i))‖ ≤
  roundingFactor n.eval (u p) * √(n.eval : ℝ) * specNorm M * ‖WithLp.toLp 2 xv‖
```

## Validation and integration

Check the generic helper and new module with serialized targeted Lean builds,
then run the applicable rules checker. Root integration owns umbrella imports
and the coverage-audit amendment. No constants, vocabulary, result identifiers,
registered programs or target approvals change.

## Checked implementation, 2026-11-04

The reviewed interfaces above are implemented without signature changes. The
generic comparison and all five actual-execution adapters pass
`LEAN_NUM_THREADS=2 lake --wfail build
NLAlib.ForMathlib.Analysis.InnerProductSpace.PiL2 NLAlib.Matrix.Computation.BLAS`
(2467 jobs). The source rules check passes with zero errors and warnings.

The axpy proof keeps the complete two-operation scalar expression supplied by
`exec_axpy`; it does not discard products of errors. The self-dot proof handles
zero squared norm separately, without dividing by zero. The gemv comparison uses
the number of columns, and neither its proof nor its statement requires nonempty
row or column types. The new module constructs no complete `CGRun` or
`LanczosRun`; those remain consumers of these local execution guarantees.
