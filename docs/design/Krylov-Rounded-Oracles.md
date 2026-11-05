# Rounded Krylov proofs through a certified matvec routine

2026-11-05. Requested by the maintainer: the rounded oracle result is primary; dense
execution is an instance certified from its floating-point kernel, not a separate solver
analysis. Existing approved trees, target statements and count definitions are unchanged.

## Contract and consumers

Reuse `IsRelErrSem` for scalar arithmetic and `IsMatvecErr` for external oracle accuracy.
A shared execution certificate `IsMatvecRoutine` connects either a stored `gemv` or an
oracle `apply` to the same decoded product and raw block-write frame. It includes successful
execution and `ExecutionComposable`; it assumes only the input block, writable output and
an explicit backend store precondition (loaded matrix entries for dense, `True` for oracle).
The error coefficient is absolute operator error: `c * norm(x)`. Relative error uses
`c = eta * specNorm A`. It does not assert one fixed backward matrix for successive calls.

The core certificate has this shape (all carriers, charges and word widths are arbitrary):

```lean
structure IsMatvecRoutine (I : Interp P ι K C) (dec : P → K → ℝ) (tag : P)
    {N : ℕ} (A : Matrix (Fin N) (Fin N) ℝ) (c : ℝ)
    (pre : Store P K → Prop) (src dst : ℕ) (sOff dOff : IExp ℕ)
    (routine : Builder P ι ℕ ℕ Unit) : Prop where
  composable : ExecutionComposable I routine
  run : ∀ st x, pre st.store →
    (∀ i : Fin N, ∃ w, st.store.read tag src (sOff.eval + i) = some w ∧
      dec tag w = x i) →
    (∀ i < N, ∃ len, st.store.shape[dst]? = some (tag, len) ∧ dOff.eval + i < len) →
    ∃ (out : St P K C) (W : Fin N → K), exec I routine.run st = some out ∧
      st.store.writeBlock tag dst dOff.eval (Array.ofFn W) =
        some out.store ∧
      ‖WithLp.toLp 2 (A *ᵥ x - fun i : Fin N => dec tag (W i))‖ ≤
        c * ‖WithLp.toLp 2 x‖
```

CG and Lanczos phase, prefix and loop proofs consume that certificate. Dense and oracle
instances have their own initialization and scope cleanup; counts continue to come from
`StaticCost` on the actual registered trees. Scalar errors and matvec accuracy are separate
inputs. A common run tolerance must cover both; dense instantiation recovers the existing
implementation budgets and old top-level theorem statements.

## Reuse and placement

Searched Mathlib floating-point modules and NLAlib execution contracts: no rounded oracle
execution or routine certificate. Reuse `IsMatvecErr`, `Store.readBlock_eq_some_map_range`,
`Store.exists_writeBlock_eq_some_of_getElem?_shape`, existing block-write frames,
`ExecutionComposable`, and `IsRelErrSem.exec_gemv_norm_sub_le_specNorm_mul`.
The latter supplies `roundingFactor N u * sqrt N * specNorm A` for dense matvecs.
No new arithmetic semantics, run models, access models, target statements or named constants.

Files: `Computation/MatvecRoutine.lean` owns the routine certificate and oracle execution;
`Matrix/Computation/MatvecRoutine.lean` owns its dense instance; existing Krylov rounded phase/loop
files own their backend-parametric proofs and stored/oracle corollaries. New files or changes
to this split are recorded here as implementation proceeds.

## Implemented API and allowance selection

Both `CGOracleImplementation.exec_rounded_compiled` and
`LanczosOracleImplementation.exec_rounded_compiled` take:

```lean
(hsem : IsRelErrSem u dec (fun _ _ => True) I.sem)
(v : P → ℝ) (hv : ∀ p, u p ≤ v p) (η : ℝ)
(hmv : IsMatvecErr I o dec tag A (η * specNorm A))
```

They require `η ≤ cgImplementationRoundoffBound N (v tag)` or its Lanczos counterpart,
respectively. The chosen common run budget also satisfies the existing local/horizon
conditions. The proof uses `IsRelErrSem.mono` and `IsMatvecErr.mono`; changing the allowance
changes no arithmetic operations. For positive CG dimension, take
`v tag = max (u tag) (η / (4*N^2))` to obtain run tolerance `max (4*N^2*u, η)`.
Lanczos uses denominator `16*(N+1)^2`, which is positive also at zero dimension.
The original zero cases remain available; empty CG products have zero operator error.

The dense wrappers use `v = u` and the certified dense matvec, retaining their exact public
compiled execution and backward theorem statements. Scalar/vector phases, prefix extension,
curvature positivity, normalization, horizon induction and terminal skipping are shared.
Only backend loading, oracle application and outer program packaging differ.

Implementation amendment: `CGOracleProgramRoundedInitialization.lean` proves the actual
no-ROM initializer, reusing all rounded primitive kernels; `CGOracleProgramRounded.lean`
and `LanczosOracleProgramRounded.lean` package actual compiled execution and all decoded
outputs/resources. `StoreContext` and prefix bookkeeping infer the matrix-storage flag;
the default remains the old dense specialization. `Computation/Allocation.lean` supplies
shared `St.shape_allocate` and `St.read_allocate_of_lt`; these are generic allocation API,
with no new data definition or numerical premise.

No Mathlib deviation is introduced: the new certificate describes NLAlib imperative
execution, for which Mathlib has no counterpart (searched). Its raw constructor is its
record constructor; concrete oracle and dense constructors are proved.
