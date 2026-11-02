# Local arithmetic assumptions and accumulated Krylov errors

Design, 2026-11-02. The user requested continuing the explicit-error investigation for both
Lanczos and CG. Independent review accepted the in-place interface change described here.

## Objects and interfaces

Generalize `LanczosRun`, `CGRun`, and `PCGRun` in place: replace the field
`k_mul_ε_le : (k : ℝ) * ε ≤ 1 / 100` with `ε_le : ε ≤ 1 / 100`. Preserve all arithmetic
equations, error bounds, symmetry assumptions, positivity of taken divisions, and terminal
breakdown conventions. Remove the old derived theorems named `ε_le`, now structure projections.
This separates local accuracy from accumulated-error hypotheses without creating parallel
raw and restricted run structures. There are no new Mathlib deviations.

The existing polynomial estimates keep their conclusions and acquire an explicit horizon
argument `hsmall : (k : ℝ) * L.ε ≤ 1 / 100` or the corresponding argument for `C`.
Existing a priori CG results already assume the stronger conditioning-dependent horizon;
derive the weaker premise internally, retaining those public signatures.

`CGRun.take` copies the local field. `LanczosRun.ofLE` takes the new local accuracy bound.
`CGRun.toPCGRun` stays unconditional, because PCG's unused horizon field is generalized too.
`overRelaxedCGRun` retains its explicit horizon argument: its proof of successful directions
uses that condition independently of the run interface.

Migration: record constructors now supply `ε_le`, rather than `k_mul_ε_le`. An old horizon
certificate implies the new field because the structures already require `k≥1` and `ε≥0`.
Callers of polynomial convenience theorems pass their horizon certificate as the new first
explicit argument. No model matrices, sequences, or error conclusions are redefined.

## Statement shapes and consumers

Lanczos adds the finite-sum coefficient bound, including exact arithmetic without division:

```lean
theorem LanczosRun.β_le_geom_sum {j : ℕ} (hj : j ≤ k) :
    L.β j ≤ (1 + L.ε) * specNorm L.H *
      ∑ i ∈ Finset.range j, (1 + 8 * L.ε) ^ (i + 1)
```

Expose the coefficient-certificate estimate in `BackwardBounds.lean`:

```lean
theorem LanczosRun.frobNorm_backwardH_sub_dilatedH_le_of_coefficients_le {B : ℝ}
    (hH : specNorm L.H ≤ B)
    (hα : ∀ j < k, |L.α (j + 1)| ≤ B) (hβ : ∀ i ≤ k, L.β i ≤ B) :
    frobNorm (L.backwardH - L.dilatedH) ≤
      normalizedBackwardBound k (15 * L.ε * B) (10 * L.ε * B)
```

The geometric corollary uses the common envelope
`B = 2 * (1 + (1 + ε) * ∑ i ∈ range k, (1 + 8 * ε) ^ (i + 1)) * specNorm H`
and concludes:

```lean
theorem LanczosRun.frobNorm_backwardH_sub_dilatedH_le_geom_sum :
    frobNorm (L.backwardH - L.dilatedH) ≤
      lanczosSmallRoundoffBackwardFactor k * L.ε *
        (1 + (1 + L.ε) * ∑ i ∈ Finset.range k, (1 + 8 * L.ε) ^ (i + 1)) * specNorm L.H
```

The existing constant `lanczosSmallRoundoffBackwardFactor` is reused at value `1000*k^2`.
This all-horizon bound may grow rapidly. The cubic small-horizon and rational absorption
bounds remain useful alternatives; the latter needs only its own quadratic condition.

CG adds two named bounds in `CGRunModel.lean`, registered in `docs/constants.toml` and the
vocabulary table, to keep later numerical improvements out of consumers:

```lean
noncomputable irreducible_def cgLineSearchFactor (m : ℕ) (ε : ℝ) : ℝ :=
  41 / 10 * ε * ∑ i ∈ Finset.range m, (1 + 31 / 10 * ε) ^ i
noncomputable irreducible_def cgAdjacentInnerFactor (m : ℕ) (ε : ℝ) : ℝ :=
  13 * ε * ∑ i ∈ Finset.range m, (1 + 31 / 10 * ε) ^ i
```

Their APIs give nonnegativity, monotonicity in `m`, and comparisons with `5*m*ε` and
`16*m*ε` when `m*ε≤1/100`. The constants come from the existing local forcing estimates;
they are not asserted to be printed literature constants. New general theorem shapes:

```lean
theorem CGRun.abs_p_dotProduct_r_succ_le_geom_sum {P K : ℝ}
    (hP : ∀ j < k, ‖WithLp.toLp 2 (C.p j)‖ ≤ P * C.ρ j)
    (hK : ∀ j < k, specNorm C.A * C.γ j * ‖WithLp.toLp 2 (C.p j)‖ ^ 2 ≤ K * C.ρ j ^ 2)
    {j : ℕ} (hj : j < k) :
    |C.p j ⬝ᵥ C.r (j + 1)| ≤ cgLineSearchFactor (j + 1) C.ε * (1 + P + K) * C.ρ j ^ 2
```

The adjacent-inner-product version needs only the `P,B` certificates and gives
`cgAdjacentInnerFactor (j+1) ε * (specNorm A * (1+P)^2 + B*(1+P))`.
The posterior backward theorem also needs only `P,B`, with
`f = 8*ε*(specNorm A*(1+P)^2+B)` and
`p = cgAdjacentInnerFactor k ε*(specNorm A*(1+P)^2+B*(1+P))`.
The old linear APIs retain `K` for compatibility; its nonnegativity permits weakening the
new bound to the existing expression.
Existing linear statements become explicit-horizon corollaries. A finite sum is used instead
of a quotient to preserve the zero-error case.

## Placement, reuse, and validation

Lanczos files affected: `LanczosRun`, `LocalErrors`, `Recurrence`, `Paige`, `Normalized`,
`Backward`, `BackwardSpectral`, `NormalizedBackward`, and `BackwardBounds`. Exact identities
and model constructions stay horizon-free. Only their polynomial error estimates propagate
the explicit horizon.

CG files affected: `CGRun`, `CGRunModel`, `CGBackward`, `CGAccuracy`, `OverRelaxedCG`, and the
identity-preconditioner bridge in `PCGRun`. Generic spectral-to-residual transfer needs no
horizon. True-residual and forward bounds still need the stated spectral/error hypotheses.

Reuse the existing normalized recurrence/dilation backend. Mathlib's geometric-sum and
finite-sum order API is the first choice for accumulated factors; searched Mathlib has no
algorithm-specific CG/Lanczos run model. No target, checker, baseline, or build pin changes.
Each result is reviewed against terminal breakdown, zero precision, and zero-step sums.
Run warning-fatal builds and the full stage audit before reporting completion.

## Validation completed

Independent mathematical review accepted the geometric recurrences, coefficient envelopes,
zero-precision cases, and terminal-breakdown handling. The existing CG backward-error and
attainable-accuracy modules compile with the generalized interfaces.

The full `scripts/stage_check.sh` completed with exit 0 on 2026-11-02:
512 proved modules built with zero compiler warnings; the axiom audit checked 15,731
declarations with zero violations; kernel replay checked 15,961 constants across 517 modules
with zero violations. All 14 Lean linters, program/target checks, references, 54 registered
constants, and mathematical-documentation checks passed. The 109-rule check reported zero
errors, 73 baseline entries, and 494 heuristic warnings. Duplicate reporting found eight
private-only classes and no duplicate public statements. The complete log is
`/tmp/krylov-local-precision-stage.log` in the working environment.

This establishes accumulation bounds for arbitrary finite successful runs at local
`ε ≤ 1/100`; it does not assert unrestricted CG convergence. Deriving input-only CG
certificates with explicit spectral margins remains subsequent work.
