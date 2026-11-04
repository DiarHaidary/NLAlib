# CG convergence on unions of tiny spectral intervals

Date: 2026-11-04.

## Objects and interfaces

No new objects, named constants or hypothesis interfaces. Use `CGRun`, `quadForm`,
`residualMinimax`, Mathlib real polynomials and sets directly. The spectral set is an arbitrary
`S : Set ℝ` containing
`⋃ i ∈ Set.Iio n, Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ)`.
This keeps the individual intervals instead of their convex hull. There is no new §5.3 row.
The full-run small-roundoff hypothesis remains the existing scalar hypothesis (H).

## Statements

All statements have `{n k : ℕ} (C : CGRun n k)` and use the full run's backward model.
In the discussion, mathematical letters denote existing expressions: Δ denotes
`2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2`,
and R denotes
`cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)`.
These abbreviations are expanded in the Lean statements; no new definitions are added.

```lean
theorem CGRun.quadForm_sub_x_le_sq_mul_add_of_polynomial
    {a a' δ η : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ δ)
    {S : Set ℝ}
    (hS : (⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ)) ⊆ S)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
    {j : ℕ} (hj : j ≤ k) {p : ℝ[X]}
    (hp : p.degree ≤ j) (hp₀ : p.eval 0 = 1)
    (hη : ∀ x ∈ S, |p.eval x| ≤ η) :
    quadForm C.A (xs - C.x j) ≤
      η ^ 2 * (quadForm C.A xs +
        2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2) +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
      cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)

theorem CGRun.ρ_sq_le_mul_sq_mul_of_polynomial
    {a a' δ η : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ δ)
    {S : Set ℝ}
    (hS : (⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ)) ⊆ S)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b)
    {j : ℕ} (hj : j ≤ k) {p : ℝ[X]}
    (hp : p.degree ≤ j) (hp₀ : p.eval 0 = 1)
    (hη : ∀ x ∈ S, |p.eval x| ≤ η) :
    C.ρ j ^ 2 ≤ (a' + a / 2) * η ^ 2 * (quadForm C.A xs +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2)
```

A compact-set minimax corollary replaces η by `residualMinimax S j`. Compactness only supplies
bounded polynomial images; finite unions of closed bounded intervals satisfy it. The polynomial
statements need no compactness, strict positive precision or nonzero terminal residual.
Both permit `j = 0` and `j = k`.

## Consumers and files

`NLAlib/Krylov/FinitePrecision/CGSpectralConvergence.lean` owns these convergence results and
proof-local helpers, in order: backward spectral-set inclusion; model energy estimate;
physical polynomial estimate; computed residual estimate; minimax corollaries if clean.
A reusable normalized-data spectral localization belongs in `BackwardSpectral.lean`, supplied by
the parallel spectral work. No other additions outside this file.
The downstream consumer chooses a polynomial for separated clusters or a compact union of
intervals, then applies the theorem directly; there is no condition-number replacement of S.

## Material and searches

Read Greenbaum–Liu–Chen (2021), §1.3, equation (9),
<https://arxiv.org/html/1905.05874v2#S1.SS3>. The formal result supplies explicit additive physical
energy discrepancies from the existing model comparison, whereas the source discusses the tiny
interval minimax factor qualitatively. It does not assert equivalence to a specific floating
point implementation beyond `CGRun`'s existing hypotheses.

Searched pinned Mathlib matrix spectrum, functional calculus and residual polynomial API:
no finite-precision CG convergence theorem exists. Reuse Mathlib `cfc_mono`,
`IsCompact.bddAbove_image`, `le_ciInf`, `le_ciSup` and the existing NLAlib exact-CG results
`Matrix.PosDef.re_quadForm_sub_cgIterate_le`,
`Matrix.PosDef.re_quadForm_sub_cgIterate_le_residualMinimax_sq_mul`.
Use `CGRun.norm_cgState_backwardH_r_of_posDef`,
`CGRun.abs_quadForm_backwardH_sub_quadForm_le` and
`CGRun.quadForm_sub_x_le_quadForm_backwardH_sub_cgIterate_add` directly.
No new spelling, Mathlib deviation, duplicate exact-CG theorem or named bound is introduced.

## Review questions

Recommendation: retain the arbitrary superset S and a certified δ in the general theorem, so
users can supply the current a priori backward bound or any tighter established bound. Keep
physical comparisons under (H); do not claim a general-certificate physical result that the
existing energy analysis does not establish.

## Amendment: shared matrix inequality and localization (2026-11-04)

Approved by integration review. Generic localization is implemented for `LanczosData` with the
existing unit-column Gram hypothesis in `BackwardSpectral.lean`; one-line normalized wrappers
live in `NormalizedBackward.lean`, where that structure is defined. `CGRun` has a one-line
wrapper, so both matrix-function and CG consumers use the same localization.

The residual companion consumes a shared inequality in `Matrix/Norms/Loewner.lean`:

```lean
theorem Matrix.PosSemidef.norm_toLp_mulVec_sq_le
    {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) {u : ℝ}
    (hu : A ≤ u • (1 : Matrix n n 𝕜)) (x : n → 𝕜) :
    ‖WithLp.toLp 2 (A *ᵥ x)‖ ^ 2 ≤ u * RCLike.re (quadForm A x)
```

Its home is the matrix norm/Loewner topic because it converts a Loewner upper bound into a
vector norm bound. Mathlib search found `cfc_pow_id`, `cfc_const_mul_id`, `cfc_mono` and
`le_algebraMap_iff_spectrum_le`, which give the matrix inequality directly; no exact existing
vector-energy statement found. Replace the existing private real-PD helper in `CGBackward`
by a call to this general PSD statement, avoiding a duplicate argument. No new import cycle:
the shared proof uses Mathlib functional calculus already available to Loewner.

The compact minimax corollary is implemented with the following exact statement (the variables
`{n k : ℕ} (C : CGRun n k)` remain fixed):

```lean
theorem CGRun.quadForm_sub_x_le_residualMinimax_sq_mul_add {a a' δ : ℝ} (ha : 0 < a)
    (hs : spectrum ℝ C.A ⊆ Set.Icc a a')
    (hsmall : (k : ℝ) ^ 2 * Real.sqrt k * C.ε * (a' / a) ^ 2 ≤ 1 / 10 ^ 5)
    (hgap : frobNorm (C.backwardH - C.dilatedH) ≤ δ) {S : Set ℝ}
    (hcompact : IsCompact S)
    (hS : (⋃ i ∈ Set.Iio n,
      Set.Icc (eigenvalue C.A i - δ) (eigenvalue C.A i + δ)) ⊆ S)
    {xs : Fin n → ℝ} (hx : C.A *ᵥ xs = C.b) {j : ℕ} (hj : j ≤ k) :
    quadForm C.A (xs - C.x j) ≤
      residualMinimax S j ^ 2 * (quadForm C.A xs +
        2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2) +
      2 * ‖WithLp.toLp 2 C.b‖ ^ 2 * (cgBackwardFactor k * C.ε * (a' / a) * a') / a ^ 2 +
      cgEnergyFactor j * C.ε * (a' / a) * (‖WithLp.toLp 2 C.b‖ ^ 2 / a)
```

## Amendment: reusable minimax monotonicity (2026-11-04)

Integration review identified the minimax comparison as general scalar approximation API.
Move it out of the CG proof into `Polynomial/Chebyshev/Residual.lean`, beside the definition and
basic minimax inequalities, with no new imports:

```lean
theorem residualMinimax_mono {s t : Set ℝ} (ht : IsCompact t)
    (hst : s ⊆ t) (q : ℕ) : residualMinimax s q ≤ residualMinimax t q
```

The compact upper set ensures bounded polynomial images, avoiding the total supremum's junk
value on an unbounded set. The CG minimax theorem consumes this public comparison. Mathlib
has no residual minimax definition; scalar order lemmas and `IsCompact.bddAbove_image` supply
the proof. This is a support theorem, with no new result id or vocabulary.
