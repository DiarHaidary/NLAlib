# CG error-tracking research integration

Date: 2026-11-04. Source branch: `github/research/cg-error-tracking-rebased`,
commit `7147d4ac`; comparison base is current main `4c190365`.

This is a selective mathematical integration. Program trees, targets, count formulas,
registries and scalar semantics are outside this change. A later actual-execution bridge
can instantiate these results after deriving a `CGRun`; its run precision is not identified
with scalar unit roundoff.

## Existing objects and overlap

Reuse `CGRun`, `quadForm`, the actual computed decrements `γ i * ρ i ^ 2`,
`cgTridiagonal`, the full-horizon `backwardH`, and `CGAccuracy`'s input-only window
`k^2 * sqrt k * ε * (a'/a)^2 ≤ 10^-5`. Introduce no new hypothesis interface.

Current `CGEnergy` already supplies direct physical-energy convergence, retaining coefficient
one on the decrement sum and remainder `cgEnergyFactor j = 135j^2`. Current
`CGEnergyEstimator` already supplies delayed absolute reliability with
`cgEnergyEstimatorFactor j d = 150d(j+d)` and the canonical absolute physical/model
comparison. Those statements stay unchanged.

The research branch's coarse `200k^2` estimator remainder is dominated by current delayed
reliability, and its final `2*10^4 k^2 sqrt(k)` model-comparison theorem collides by name with
our stronger canonical theorem. Neither duplicate coarse result will be added. Instead,
retain the genuinely different decrement-relative bound and the exact one-step identity.
The inverse-tridiagonal result will use the stronger existing local remainder
`cgEnergyEstimatorFactor 0 (j+1)` rather than the branch's `200k^2`.

## Files and reuse

* `CGRunSpectrum.lean`: extract reusable spectral/Rayleigh/solution facts currently private
  to `CGAccuracy`. It imports `CGBackward`, introducing no matrix or run interface.
* `CGAccuracy.lean`: replace the extracted private proofs with calls to that shared API.
  Every existing public signature must remain unchanged.
* `CGErrorTracking.lean`: exact one-step identity, relative decrement estimates, the direct
  model-decrement comparison and inverse-tridiagonal identity. Import `CGEnergyEstimator`
  to reuse the canonical stronger absolute estimator API; do not duplicate it.

Mathlib was searched for norm/quadForm spectral inequalities. The extraction currently uses
existing `Matrix.IsHermitian.eigenvalue_last_mul_le_re_quadForm`,
`re_quadForm_le_eigenvalue_zero_mul`, `spectrum_subset_iff` and Euclidean norm identities.
Existing matrix Loewner/Rayleigh API is available for short proof replacements if useful.
The tridiagonal consumer reuses `sq_mul_inv_cgTridiagonal_zero_zero`; the model comparison
reuses `CGRun.quadForm_backwardH_sub_cgIterate_sub_quadForm_backwardH_sub_cgIterate`.

## Numerical API proposed for review

The branch's 60 and affine 36j+16 coefficients are input-only allowances proved in this
arithmetic model, not printed source constants. Proposed named irreducible bounds are
`cgEnergyTrackingRelativeFactor k := 60 * (k : ℝ)` and
`cgEnergyTrackingUpdateFactor j := 36 * (j : ℝ) + 16`, each with nonnegativity and an upper
comparison API. Root owns their vocabulary and constants registry entries. The underlying
line-search and curvature estimates may remain proof-local rather than creating public
numeric APIs duplicated from existing accuracy work.

## Exact headline signature proposals

The exact one-step identity is independent of the smallness window:

```lean
theorem quadForm_sub_x_sub_quadForm_sub_x_succ_eq {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
    {j : ℕ} (hj : j < k) :
    quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + 1)) =
      C.γ j * C.ρ j ^ 2 + 2 * C.γ j * (C.p j ⬝ᵥ C.r j - C.ρ j ^ 2) -
        (C.γ j ^ 2 * (C.p j ⬝ᵥ (C.A *ᵥ C.p j)) - C.γ j * C.ρ j ^ 2) +
        2 * C.γ j * (C.p j ⬝ᵥ (C.b - C.A *ᵥ C.x j - C.r j)) +
        2 * (C.ex j ⬝ᵥ (C.A *ᵥ (xs - C.x j - C.γ j • C.p j))) - quadForm C.A (C.ex j)
```

The relative delayed allowance is useful when the measured decrement is small. Its additive
part is still explicit; it does not assert finite-precision energy monotonicity:

```lean
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_sum_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d)) -
        ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2| ≤
      cgEnergyTrackingRelativeFactor k * C.ε * (a' / a) * ∑ i ∈ Finset.Ico j (j + d), C.γ i * C.ρ i ^ 2 +
        cgEnergyTrackingUpdateFactor (j + d) * d * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)
```

The backward-model decrement comparison cancels the initial model-distance term:

```lean
theorem abs_quadForm_sub_x_sub_quadForm_sub_x_add_sub_backwardH_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {xs' : Fin n × Fin (k + 1) → ℝ}
    (hxs' : C.backwardH *ᵥ xs' = C.dilatedRhs) {j d : ℕ} (hjd : j + d ≤ k) :
    |quadForm C.A (xs - C.x j) - quadForm C.A (xs - C.x (j + d)) -
        (quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 j) -
          quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 (j + d)))| ≤
      cgEnergyTrackingRelativeFactor k * C.ε * (a' / a) *
          (quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 j) -
            quadForm C.backwardH (xs' - cgIterate C.backwardH C.dilatedRhs 0 (j + d))) +
        cgEnergyTrackingUpdateFactor (j + d) * d * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)
```

The inverse-tridiagonal theorem uses current absolute reliability directly, avoiding an
unnecessary residual-to-energy condition-number conversion:

```lean
theorem abs_quadForm_sub_x_succ_sub_sub_inv_cgTridiagonal_le {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j + 1 ≤ k) :
    |quadForm C.A (xs - C.x (j + 1)) -
        (quadForm C.A xs - ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgTridiagonal C.γ C.ρ (j + 1))⁻¹ 0 0)| ≤
      cgEnergyEstimatorFactor 0 (j + 1) * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)
```

The current absolute physical/model comparison remains the canonical theorem of that name.
No new assumption of computed/model iterate closeness is introduced.

## Review and validation

Audit all three branch files for unsupported proof features, public-signature changes and
consumer conflicts. Keep files under1500 lines and proofs under80 lines; move only the three
owned mathematical files. Check the imported branch material and affected existing energy
consumers with two Lean threads and warnings fatal, then run source rules. Root owns the
umbrella, metadata and final integrated full-stage check.

## Amendment: current-main pairing and terminal direction

Current main additionally has the public `CGRun.abs_p_dotProduct_r_sub_le` bound with
coefficient `26j`, absent from the research branch. Preserve it and its short lower-bound
corollary; the branch's weaker `26k` variant is only a proof-local relaxation.

The rounded-program horizon bootstrap consumes the following input-only terminal corollary
in `CGRunSpectrum.lean` (no next-curvature assumption):

```lean
theorem p_ne_zero_of_r_ne_zero {a a' : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hr : C.r k ≠ 0) : C.p k ≠ 0
```

Derive the certificates P=2κ and K=21κ/20 from the existing public a-priori results,
then apply `CGRun.norm_r_le_two_mul_norm_p`. A nonzero terminal residual excludes a zero
terminal direction. This preserves the CGRun structure.
