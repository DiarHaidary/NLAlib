# Powers converging to a fixed idempotent

Status (2026-10-29): Bounded review accepted and implementation completed. Targeted single-module
Lean checks passed; full integration validation passed (see the BI1 integration report). User reopening plus Matrix standing
approval
covers these existing-interface additions. Place all results in
`Matrix/Spectral/PowerBounds.lean`, preserving the concurrent Richardson result.
No new definition or chosen projector. Source is backend
`Matrix/Spectral/ProjectorDeflationPowers.lean` at commit `77514ce`.

## Exact implemented statements

```lean
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem sub_pow_succ_eq_pow_succ_sub {K : Type*} [Ring K]
    (T P : Matrix n n K) (hP : IsIdempotentElem P)
    (hTP : T * P = P) (hPT : P * T = P) (k : ℕ) :
    (T - P) ^ (k + 1) = T ^ (k + 1) - P

theorem tendsto_pow_iff_specRadius_sub_lt_one {𝕜 : Type*} [RCLike 𝕜]
    (T P : Matrix n n 𝕜) (hP : IsIdempotentElem P)
    (hTP : T * P = P) (hPT : P * T = P) :
    Filter.Tendsto (fun k : ℕ => T ^ k) Filter.atTop (nhds P) ↔
      specRadius (T - P) < 1

theorem exists_forall_specNorm_pow_sub_le_mul_pow {𝕜 : Type*} [RCLike 𝕜]
    (T P : Matrix n n 𝕜) (hP : IsIdempotentElem P)
    (hTP : T * P = P) (hPT : P * T = P)
    {r : ℝ} (hr : specRadius (T - P) < r) :
    ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, specNorm (T ^ k - P) ≤ C * r ^ k
```

## Provenance and reuse

The first ports `matrix_sub_projector_pow_succ`. Its simple induction helper
`matrix_pow_mul_eq_of_mul_eq` remains private unless another file needs it.
The second includes the source
`tendsto_matrix_pow_projector_of_deflated_spectralRadius_lt_one` and strengthens it
to equivalence; use eventual positive exponents and existing
`tendsto_pow_zero_iff_specRadius_lt_one`. The third ports
`exists_specNorm_matrix_pow_sub_projector_le_geometric` with a positive witness.
Apply existing `exists_forall_specNorm_pow_le_mul_pow` to `T-P` with epsilon
`r-specRadius(T-P)`, then enlarge the witness by `specNorm (1-P)` to handle zero.
These are generic RCLike statements instead of the source's real-only complexification.
Search of local Mathlib Algebra declarations found no matching named positive-power
subtraction formula; do not add a generic ForMathlib abstraction without a consumer.

## Scope and review notes

`P` may be zero, nonorthogonal, or nontrivial; normality and diagonalizability are
unnecessary. The matrix may be empty. At exponent zero the difference is `1-P`,
so the positive-power identity must not be stated for all exponents. Both absorption
hypotheses are essential. The norm-bound rate is automatically positive by
`specRadius_nonneg`. The statement is the standard prefixed existential bound,
following the existing PowerBounds API rather than introducing a named constant.
Its docstring states that this is an O(r^k) estimate, with C depending on T,P,r.
Consumers include fixed-projector limits and deflation-based iterative convergence.
Backend source locators are verified; printed book locators have not been verified
and will not be asserted in supporting docstrings. No new objects or imports needed.

Bounded review accepted by probability agent on 2026-10-29; all scopes and names
accepted, no interface changes. Implementation and targeted Lean checks passed; parent owns full integration validation.
