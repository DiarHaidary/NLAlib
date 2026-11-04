# Rounded Euclidean norm and normalization kernels

2026-11-04. Design reviewed before proofs; final implementation recorded below.
This work connects the existing `nrm2` and
`rscl` programs to decoded real vector bounds under `IsRelErrSem`; it introduces no program,
compiled tree, cost target, or floating point semantics.

## Existing material and searches

`BLAS.nrm2` runs `dot x x`, including its ordered accumulation, and then one rounded square
root in place. `BLAS.rscl` performs componentwise division by the stored scalar. Reuse
`IsRelErrSem.exec_dot_abs_sum_mul_sub_le`, `IsRelErrSem.exec_rscl`, `sqrt_ok`, `sqrt_err`,
`exec_run_bind`, `exec_seq_instr_un`, and store read/write preservation. Mathlib searches found
square-root algebra and Euclidean norm sum-of-squares identities; searched for a rounded norm
kernel or a relative perturbation theorem for a rounded square root, none. No second dot,
division, semantics, store, or uniform scalar accuracy interface is introduced.

The implementation follows `CONTRIBUTING.md`, the rules digest and the Computation topic rules.

## Objects and vocabulary

Put the following scalar bounds in `Computation/BLAS/Normalization.lean` alongside their
kernel consumers. Parent integration owns their registry and vocabulary entries.

| Concept | Spelling | Bridge |
| --- | --- | --- |
| rounded dot-then-square-root norm error | existing `roundingFactor (n+1) u` | the dot and square-root errors compose through the existing rounding-product bound |
| squared norm defect after rounded division | `normalizationRoundingFactor n u` | `t (2+t)`, where `t=(u+γ_(n+1))/(1-γ_(n+1))` |

The new factor is total; statements require `(n+1)*u<1` and `γ_(n+1)<1`. No division by a vanishing `1-γ_(n+1)` is used in a theorem. The comparison API proves normalization defect at most `12(n+1)u` when `(n+1)u≤1/100`. Unit roundoff is not substituted for the algorithm's accumulated error parameter.

No new hypothesis predicate is needed: use `IsRelErrSem`, `AddsZeroExactly`, decoded storage,
and explicit scalar small-roundoff hypotheses. No hypothesis assumes a returned error bound.

## Statement shapes

The core interface follows existing rounded BLAS theorems with arbitrary stored carrier `K`:

```lean
theorem IsRelErrSem.exec_nrm2_abs_norm_sub_le
    {P ι K C : Type} [DecidableEq P] [AddMonoid C]
    (I : Interp P ι K C) (p : P) (st : St P K C)
    {dec : P → K → ℝ} {u : P → ℝ}
    (h : IsRelErrSem u dec (fun _ _ => True) I.sem)
    (hz : AddsZeroExactly dec I.sem)
    (dst : Cell ℕ ℕ) (x : ℕ) (xo n : IExp ℕ) (xs : ℕ → ℝ)
    (hn : (n.eval + 1 : ℕ) * u p < 1)
    (hsmall : roundingFactor (n.eval + 1) (u p) < 1)
    (hx : ∀ i < n.eval, ∃ w,
      st.store.read p x (xo.eval+i) = some w ∧ dec p w = xs i)
    (hdx : dst.buf = x → ∀ i < n.eval, dst.idx.eval ≠ xo.eval+i)
    (hdst : ∃ v s₁, st.store.write p dst.buf dst.idx.eval v = some s₁) :
    ∃ st' w, exec I (nrm2 p dst x xo n).run st = some st' ∧
      st.store.write p dst.buf dst.idx.eval w = some st'.store ∧
      0 ≤ dec p w ∧
      |‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖ - dec p w| ≤
        roundingFactor (n.eval + 1) (u p) *
          ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖
```

A decoded finite-vector wrapper uses `HoldsDecoded` with a one-column matrix. Zero input
returns decoded zero; nonzero input returns a strictly positive decoding. These follow from
the relative bound and `γ_(n+1)<1`, and cover the zero-length norm call as well.

The normalization theorem takes the same input/storage hypotheses and a positive input norm,
then returns the actual two sequential execution witnesses: first `nrm2`, then `rscl` with the
computed norm word. If the output words are `W`, its decoded vector is `y_i=dec p (W i)`, and
the computed norm is `q`, the conclusions include

```lean
‖WithLp.toLp 2 (fun i : Fin n.eval => xs i - q * y i)‖ ≤
  u p * ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖
```

and

```lean
|‖WithLp.toLp 2 y‖^2 - 1| ≤ normalizationRoundingFactor n.eval (u p)
```

The norm residual comes from the *actual rounded division*: `q*y_i=xs_i*(1+δ_i)`, so
`|δ_i|≤u`; no exact rescaling after rounded `nrm2` is substituted into the program.

The same actual executions also certify the initial direction:

```lean
‖WithLp.toLp 2 ((fun i : Fin n.eval => xs i) -
  q • (‖WithLp.toLp 2 y‖⁻¹ • y))‖ ≤
    (2 * u p + roundingFactor (n.eval + 1) (u p)) *
      ‖WithLp.toLp 2 (fun i : Fin n.eval => xs i)‖
```

This feeds the physical Lanczos output transfer without assuming rounded division preserves
input direction. `RelErr.norm_sub_smul_inv_norm_le` derives it from the executed division
errors, the computed nonnegative norm, and the reverse triangle inequality.

## Proof plan

1. Use the existing dot execution theorem and sum-of-squares identity to bound the squared
   norm result by `γ_n`. Its nonnegativity follows from `γ_n<1`, implied by `γ_(n+1)<1`.
2. Invoke `sqrt_ok` on that actual word, then `sqrt_err`. The identity
   `|r-sqrt(s)|*(r+sqrt(s))=|r²-s|` gives error at most `γ_n*r`. The final relative error
   is at most `γ_n + u (1+γ_n)≤γ_(n+1)`, using existing rounding-product algebra.
3. Reuse the unchanged-input reads after the norm's scalar write, then invoke existing `rscl`.
4. Convert the componentwise division errors to a Euclidean norm bound. The reverse triangle
   inequality gives `|‖y‖-1|≤t`; therefore `|‖y‖²-1|≤t(2+t)`.
5. Prove small-roundoff comparisons to turn these scalar factors into Lanczos local accuracy
   budgets with explicit dimension dependence.

## Consumers and files

`Computation/BLAS/Normalization.lean` owns the normalization factor, their numerical API, norm execution,
zero/nonzero behavior, and sequential norm/division normalization. The design record is this
file. Future Lanczos and Gram-Schmidt realization theorems consume the executions, scalar norm
error, normalization residual, and near-unit bound. They remain in their own algorithm topics.
The existing private `nrm2_run` theorem in `Computation/BLAS.lean` is promoted to documented public `run_nrm2`, with its internal use updated. No program definition changes. The generic pointwise-to-norm helper `RelErr.norm_sub_le` reuses the existing relative-error interface and is also available to CG implementation bridges.

## Arithmetic scope

The bounds use explicit factors with `O(nu)` comparisons and existing rounding-product algebra.
The all-values-in-range premise
is the same idealized arithmetic contract used by the existing rounded kernels; overflow,
underflow, and a scaled robust norm algorithm are outside this implementation.

## Validation and read-back

The public norm theorem proves that the concrete kernel succeeds and overwrites only its norm
cell with a word decoding to a nonnegative real whose forward norm error is bounded by
`γ_(n+1)` times the input norm. It covers zero-length vectors. The explicit zero-input
corollary returns decoded zero, and the positive-input corollary returns a strictly positive
norm word. The finite-vector wrapper takes existing `HoldsDecoded` rather than a new storage
predicate.

The public normalization theorem returns *both* successful execution states, their exact scalar
and block writes, the computed positive norm, its relative error, the rescaling residual, and
the squared unit-norm defect and the initial-direction mismatch. All error conclusions are derived from the input storage and
standard arithmetic contract. The assumptions contain no output error certificate.

Targeted `lake lean` and `lake build ... --wfail` passed with no Lean warnings. Full-library
stage checks and registry integration are owned by the parent task; no check or target file
was changed here.

## Current rounding-factor API

After integration with main, `roundingFactor n u` is the primary compound factor
`(1-u)^(-n)-1`. The old rational expression `n*u/(1-n*u)` is used only as an upper comparison
under the existing precision windows. Kernel and normalization statement signatures, including
zero-length cases and the `12*(n+1)*u` comparison, are preserved.
