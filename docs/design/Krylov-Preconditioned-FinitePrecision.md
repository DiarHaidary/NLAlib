# Preconditioned CG and Lanczos in finite precision

Design, 2026-11-02. The maintainer clarified the interface: a new `PCGRun` with a
`MatvecOracle` for the preconditioner. The amendment below supersedes the initial proposal
to modify `CGRun`. The earlier sections retain the mathematical motivation and future
analysis obligations; they do not describe completed convergence results.

## Amendment: an oracle-backed PCG run

The immediate implementation is a new run model, preserving `CGRun`. It introduces:

```lean
structure MatvecOracle {𝕜 : Type*} [RCLike 𝕜] {m n : Type*}
    [Fintype m] [Fintype n] (A : Matrix m n 𝕜) where
  mulVec : (n → 𝕜) → m → 𝕜
  ε : ℝ
  ε_nonneg : 0 ≤ ε
  norm_sub_mulVec_le : ∀ x,
    ‖WithLp.toLp 2 (A *ᵥ x - mulVec x)‖ ≤ ε * specNorm A * ‖WithLp.toLp 2 x‖
```

This is a total, deterministic approximate action, not a linear map. The matrix `A` is
the fixed reference operator; no additivity or positivity of the returned action is
assumed. Its structure constructor takes the raw function and accuracy certificate.
`MatvecOracle.ofMatrix` supplies exact multiplication at tolerance zero; `mulVec_zero` and
`mulVec_eq_of_ε_eq_zero` connect the contract to Mathlib's matrix action. The oracle is
rectangular and over `RCLike`, so it can also serve Lanczos and other matrix algorithms.

The existing `Computation.IsMatvecErr` has this normwise contract with an absolute constant
`c`, but additionally concerns encoded arrays, decoding and execution success. Use
`c = ε * specNorm A` when constructing an implementation adapter. Do not identify a total
function on all mathematical vectors with an encoded-word oracle without an encoding and
success proof. No such execution adapter is claimed by this run-model addition.

`PCGRun n k` has real `Fin n` matrices `A, M`, a field
`preconditioner : MatvecOracle M`, `M.PosDef`, and the physical sequences and arithmetic
defects listed below. It keeps `A.IsHermitian`, `k > 0`, `ε ≥ 0` and `ε ≤ 1/100`, as
well as positivity of `ν` and `μ` at successful steps. The final `ν` is allowed to be zero
and is assumed nonnegative. The oracle tolerance is independent of the arithmetic `ε`.

The defining oracle equation is `z j = preconditioner.mulVec (r j)` for `j ≤ k`, including
zero. Initialization is `x 0 = 0`, `r 0 = b`, `p 0 = z 0`. There is no stored `ez` or
assumed exact initial application: its error is the derived vector `M *ᵥ r j - z j`.
The scalar equation is additive,
`ν j = r j ⬝ᵥ z j + eν j`, with
`|eν j| ≤ ε * ‖WithLp.toLp 2 (r j)‖ * ‖WithLp.toLp 2 (z j)‖`.
The remaining equations and operand-relative error bounds follow `CGRun`, with `z (j+1)`
replacing `r (j+1)` in the direction update and its error bound. The constructor is the
raw record of these equations and bounds; it requires no split run or convergence theorem.

The first API includes these signatures (with `P : PCGRun n k`):

```lean
theorem PCGRun.norm_mulVec_sub_z_le (j : ℕ) (hj : j ≤ k) :
    ‖WithLp.toLp 2 (P.M *ᵥ P.r j - P.z j)‖ ≤
      P.preconditioner.ε * specNorm P.M * ‖WithLp.toLp 2 (P.r j)‖

theorem PCGRun.norm_mulVec_sub_p_zero_le :
    ‖WithLp.toLp 2 (P.M *ᵥ P.b - P.p 0)‖ ≤
      P.preconditioner.ε * specNorm P.M * ‖WithLp.toLp 2 P.b‖

noncomputable def CGRun.toPCGRun (C : CGRun n k) : PCGRun n k
```

The last constructor uses `M = 1`, the exact identity oracle, `z = r`, and
`eν j = ‖WithLp.toLp 2 (r j)‖² * θ j`. Its iterates, residuals and scalar recurrence
are unchanged. It proves the existing model embeds without changing existing proofs.
Zero residual implies zero oracle output and zero computed scalar, even with nonzero
tolerances. Add the exact residual-gap recurrence and the zero-error bridge to `pcgState`
as checks on the model's mathematical content.

The local precision premise follows the subsequent `Krylov-FinitePrecision-Runs.md`
generalization: no accumulated horizon is imposed by either run structure, so the identity
embedding remains unconditional. This updated interface passed the full repository audit
in `/tmp/krylov-local-precision-stage.log` on 2026-11-02.

Files and consumers for this implementation:

* `Matrix/Basic/MatvecOracle.lean`: the reusable oracle, exact constructor and basic API.
* `Krylov/FinitePrecision/PCGRun.lean`: the new run, initialization and application-error API,
  exact-arithmetic specialization, and embedding of `CGRun`.
* `CONTRIBUTING.md`: vocabulary rows for these two new interfaces and their bridges.
* `NLAlib.lean`: generated imports. No program targets or checking infrastructure changes.

Mathlib search found no bounded-error matvec oracle. Its exact action is already
`Matrix.mulVec`; use that directly. No weighted norm is introduced. The design review
checked that additive scalar errors accommodate an inexact application, initialization
actually calls the oracle, and neither a Euclidean contract nor SPD of `M` alone is
misrepresented as sufficient for the eventual preconditioned convergence bounds.

The new model is the foundation for the remaining PCG/Lanczos analysis. Transporting it
to a common backward theorem, proving effective tolerances, and implementing the paired
Lanczos run remain subsequent work; none follows merely from introducing this structure.

## Conventions and reuse

Keep the library convention: `M` approximates `A⁻¹` and is applied by multiplication.
Assume a fixed positive definite `M`; for analysis choose an invertible factor
`M = C * Cᴴ`. The split operator is `H = Cᴴ * A * C`. The implementation need not form `C`.
Require `A.PosDef` for CG and only `A.IsHermitian` for Lanczos.

The PCG run stays over real matrices on `Fin n`, matching `CGRun` and `LanczosRun`. Extending the scalar and index types of that whole development is a
separate change. Matrix identities that do not depend on those run structures should use
`RCLike` and arbitrary finite index types.

Read and reuse:

* `Krylov/LinearSystems/PCG.lean`: the iterate, split-system equivalence, spectral bounds.
* `Krylov/LinearSystems/PCGRecurrence.lean`: the physical recurrence and its exact split bridge.
* `Krylov/Processes/PreconditionedLanczos.lean`: paired residual-like and solution-like vectors.
* `Krylov/FinitePrecision/{CGRun,CGRunModel,CGBackward,CGAccuracy}.lean`: local-error model,
  local orthogonality, backward realization, residual gap and attainable accuracy.
* `Krylov/FinitePrecision/{LanczosRun,LanczosData,Normalized,BackwardBounds}.lean`:
  perturbed recurrence, Gram commutator and dilation bounds.
* `Matrix/Inequalities/Order.lean`: `spectrum_mul_conjTranspose_mul` and spectral equivalence.
* Mathlib `Analysis/Matrix/PosDef.lean`: `Matrix.toNormedAddCommGroup` and
  `Matrix.toInnerProductSpace` already implement weighted geometry.

Searches found no preconditioned finite-precision run model in these Mathlib and NLAlib
sources. Do not introduce a second SPD predicate, a new matrix norm, or a global weighted
inner-product instance. Initially express weighted quantities through explicit transformed
Euclidean vectors and existing `quadForm`; any later named norm needs its own vocabulary
row and bridge to Mathlib.

## Geometry and the quantities the bounds should control

With `M = C Cᵀ`, transform physical CG quantities by

```
H = Cᵀ A C,  b̂ = Cᵀ b,
x̂ = C⁻¹ x,  p̂ = C⁻¹ p,  r̂ = Cᵀ r,  ŝ = Cᵀ s.
```

Then `‖r̂‖² = rᵀ M r`, `‖p̂‖² = pᵀ M⁻¹ p`, and the physical A-energy error is
exactly the split H-energy error. The condition number in convergence bounds is that of
`H`, equivalently the ratio of positive spectral endpoints for `M A`. Never apply a
Euclidean symmetric-matrix theorem directly to `M A`.

The transformed residual gap is

```
b̂ - H x̂ - r̂ = Cᵀ (b - A x - r).
```

Expose this weighted gap first. A Euclidean bound for the physical residual requires an
explicit conversion factor, for example `specNorm ((Cᵀ)⁻¹)`. Such factors must not disappear
into the preconditioned condition number. Similarly, a physical matvec error transforms as
`Cᵀ es`; its relative bound with respect to `‖H‖ ‖p̂‖` must be proved, not assumed to have
the same unit roundoff as the original matvec.

## Remaining analysis obligations

The oracle-backed record and its exact specializations are a foundation, not a convergence
proof. In split coordinates the preconditioner error contributes to the initial direction,
the direction updates and the scalar numerator. A Euclidean oracle error certificate must
be converted to the appropriate weighted error bounds with explicit conditioning factors.
Do not construct an ordinary `CGRun` from a general `PCGRun` by dropping these terms.

The independent `PCGRun` is the maintainer's chosen interface. The earlier suggestion to
change `CGRun` is superseded; existing CG proofs and their model remain unchanged.

For a paired preconditioned Lanczos run, retain `D = Z - M V`. Given the physical equation
`A Z = V T + β v_next e_lastᵀ + F`, the split vectors `Q = Cᵀ V` satisfy

```
H Q = Q T + β (Cᵀ v_next) e_lastᵀ + Cᵀ F - Cᵀ A D.
```

This identifies where an inexact application enters the Lanczos recurrence. Scalar-product
and near-normalization estimates are also required before a `LanczosRun` can be built.
The reusable oracle can supply the application error to that future paired run model.

## Validation and status

Implemented the two new modules and vocabulary rows. Both modules build with warnings fatal.
Source rules pass. A Lean regression example in `/tmp/pcg-oracle-regression.lean` constructs
one step for `A = M = I` with an oracle that returns twice its input, arithmetic tolerance
zero and oracle tolerance one. Its initial direction differs from `M b`; its terminal
residual and numerator are zero and its iterate solves the system. Thus the record admits
an inexact first application and terminal zero without asserting the first direction is exact.

The structural regression checks exercise `CGRun.toPCGRun` and `PCGRun.state_eq_pcgState`.
The axiom read-back for the exact-oracle lemma, exact PCG bridge and CG embedding lists only
`propext`, `Classical.choice` and `Quot.sound`.

Full validation completed with `scripts/stage_check.sh` exit 0 on the isolated snapshot
`/home/ubuntu/work/pcg-oracle-validation`. The snapshot avoids concurrent updates in the
original checkout; both new Lean files were compared byte-for-byte with the original after
validation. The log is `/tmp/pcg-stage-check-final.log`, with detailed logs in
`/tmp/pcg-validation-checks/nlalib-stage-check/`. All 512 modules built with warnings fatal;
axiom audit, linters, freshness, kernel replay, fixtures, programs, targets, references,
constants, LaTeX and the 109-rule check passed. The duplicate report found no new overlap
involving either new module. The rules report retains existing baseline entries and review
warnings elsewhere in the library.

The exact oracle constructor is named `MatvecOracle.ofMatrix`. The earlier name `exact`
collided with the name checker's interpretation of an unrelated existing theorem's
`of_exact` suffix; the constructor was renamed without altering that theorem or the checks.
The final regression is `/tmp/pcg-oracle-regression.lean`, with output in
`/tmp/pcg-oracle-regression-final.log`.

There is no execution-level oracle adapter, preconditioned backward-error theorem or
preconditioned attainable-accuracy theorem in this change. Those require the remaining
analysis above. No program targets, checks, build pins or existing CG run definitions changed.
