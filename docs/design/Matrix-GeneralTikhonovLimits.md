# Variational endpoints of general Tikhonov regularization

Design date: 2026-11-02. This completes the endpoint clauses of the original
`general-form-tikhonov-gsvd` card, after the shared objective and coordinate limits.

## Scope and interfaces

Use the existing `IsGSVD`, `IsLeastSquaresSolution`, `IsMinOn`, `gsvdTikhonovFilter`, and
`gsvdPenaltyKernelSolution`. No new endpoint predicate, residual energy, or penalty-limit
interface is needed. All six results are over `RCLike` and arbitrary finite indices.
Common kernels are allowed for both variational meanings; uniqueness requires exactly the
existing condition `LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥`.

The zero endpoint is the least-penalty least-squares solution selected by the GSVD coordinates;
it need not be `pinv A *ᵥ b`. The infinite endpoint minimizes the data residual over the entire
penalty kernel. Statements minimize the Euclidean norm, reusing the library's established
least-squares convention; squared norms are internal proof expressions only.

## Exact signatures

```lean
variable {𝕜 : Type*} [RCLike 𝕜] {m n p : Type*}
  [Fintype m] [Fintype n] [Fintype p] [DecidableEq n]
  {A : Matrix m n 𝕜} {L : Matrix p n 𝕜}
  {X : Matrix n n 𝕜} {c s : n → ℝ}

theorem IsGSVD.isLeastSquaresSolution_gsvdTikhonovFilter_zero
    (h : IsGSVD A L X c s) (b : m → 𝕜) :
    IsLeastSquaresSolution A b (gsvdTikhonovFilter A X c s b 0)

theorem IsGSVD.isMinOn_norm_mulVec_gsvdTikhonovFilter_zero
    (h : IsGSVD A L X c s) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (L *ᵥ x)‖)
      {x | IsLeastSquaresSolution A b x} (gsvdTikhonovFilter A X c s b 0)

theorem IsGSVD.mulVec_gsvdPenaltyKernelSolution
    (h : IsGSVD A L X c s) (b : m → 𝕜) :
    L *ᵥ gsvdPenaltyKernelSolution A X c s b = 0

theorem IsGSVD.isMinOn_norm_sub_mulVec_gsvdPenaltyKernelSolution
    (h : IsGSVD A L X c s) (b : m → 𝕜) :
    IsMinOn (fun x => ‖WithLp.toLp 2 (b - A *ᵥ x)‖)
      (LinearMap.ker L.mulVecLin) (gsvdPenaltyKernelSolution A X c s b)

theorem IsGSVD.eq_gsvdTikhonovFilter_zero_of_isMinOn
    (h : IsGSVD A L X c s)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥)
    (b : m → 𝕜) {x : n → 𝕜} (hx : IsLeastSquaresSolution A b x)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (L *ᵥ y)‖)
      {y | IsLeastSquaresSolution A b y} x) :
    x = gsvdTikhonovFilter A X c s b 0

theorem IsGSVD.eq_gsvdPenaltyKernelSolution_of_isMinOn
    (h : IsGSVD A L X c s)
    (hker : LinearMap.ker A.mulVecLin ⊓ LinearMap.ker L.mulVecLin = ⊥)
    (b : m → 𝕜) {x : n → 𝕜} (hx : L *ᵥ x = 0)
    (hmin : IsMinOn (fun y => ‖WithLp.toLp 2 (b - A *ᵥ y)‖)
      (LinearMap.ker L.mulVecLin) x) :
    x = gsvdPenaltyKernelSolution A X c s b
```

All six statements share `Result: general-form-tikhonov-gsvd`. Membership and minimization
are separate, independently usable statements; private paired proofs may support them.
The latter two statements establish uniqueness. No additional public existential wrapper
is needed.

## Reuse, placement, and consumers

One new topic file `Matrix/Pseudoinverse/GeneralTikhonovLimits.lean` imports
`GeneralTikhonov.lean` and Mathlib's inner-product convexity module. Mathlib's
`le_of_tendsto_of_tendsto`, `le_of_tendsto`, and
`norm_midpoint_lt_iff` supply limit ordering and strict norm convexity. The finite filter's
minimizer theorem and its two existing coordinate limits supply the variational endpoints.
The zero endpoint sends squared objective inequalities to the limit; comparison with an
arbitrary least-squares solution then gives its minimal penalty. At infinity, comparison with
the zero vector bounds the penalty by `‖b‖²/β`; comparison with any kernel vector gives the
constrained residual minimum. No generic penalty-limit theory is added.

Uniqueness reuses `IsLeastSquaresSolution.mulVec_eq` for equal data fits and strict convexity
at the midpoint for equal penalty images or constrained residuals. A private midpoint lemma
may share this proof-only step. Equality then follows from the common-kernel condition.

Consumers include parameter continuation, equality of independent regularized solvers, and
the identification of penalty-biased least-squares limits. The library's constrained
least-squares `IsMinOn` interface remains the only one.

## Provenance and exclusions

Read committed `tchen-research/NLAlib` at
`77514ce42a0e437d837797a063ac161f41022730` through `git show origin/main`:
`NLAlib/Matrix/Basic/GeneralTikhonovEndpoints.lean` and
`NLAlib/ForMathlib/Analysis/PenaltyLimits.lean`.
Their endpoint content is consolidated with native APIs; the source-only predicates
`IsMinimumPenaltyLeastSquares`, `IsPenaltyKernelLeastSquares`, and the broad generic
penalty-limit lemmas are not ported. The formulas and endpoint claims are documented as
derived statements, without a printed-source attribution for this particular formulation.
No convergence rates, statistical assumptions, nonquadratic penalties, or infinite-dimensional
claims are introduced.

## Review

Integration review accepted the endpoint scope and existing-interface proof approach on
2026-11-02, requesting separate membership and minimization statements under rule T11.
The exact signatures above incorporate that approved adjustment before proof implementation.
