# Fixed-batch nuclear-norm lower bounds

2026-10-26. Scope authorized by the maintainer's “okay fine just do 1” following the
trace-based nuclear extension proposal. This note fixes that proposal's concrete statements
for review before proofs. Independent review accepted the mathematical argument and API,
including the dated amendments below.

## Scope and objects

Extend the completed fixed-batch Frobenius result to nuclear norm (Schatten exponent one).
Use the same real PSD hard family, query model, Gaussian overlap estimate, K7 coupling,
Yao interface, `equispacedGaussianFactor`, `equispacedQueryFactor`, and
`equispacedAccuracyBound`. Introduce one exact numerical definition, registered in `docs/constants.toml`:

```lean
irreducible_def equispacedNuclearTailFactor (r : ℕ) : ℝ :=
  ((r : ℝ) + 1) * (r + 2) / 2
```

Its consumer API is positivity and its defining identity. No new predicates, norm definitions,
or Mathlib deviations are introduced.

For positive target rank K, natural batch count r (including zero),
0 < ε ≤ 1/(512·4^(r+1)(r+1)(r+2)^2), and
m = floor(K/(ε(r+1)(r+2))), success probability at least one half on every PSD matrix
of dimension K+(r+1)m forces q > K/(256·4^(r+1)(r+1)(r+2)ε).
Success means nuclear error ≤ (1+ε) times the optimal nuclear error, with no square.
Arbitrary dimensions, other Schatten exponents, expectation bounds and optimized r dependence
are outside scope. The completed Frobenius API is preserved.

## Exact headline interfaces

All signatures are in `namespace NLAlib`, with section variables

```lean
variable {k m : Type*} [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
```

The final theorem omits the two `DecidableEq` instances just as its Frobenius counterpart does.
The deterministic theorem uses the stronger hidden-rotation oracle and the randomized theorem
uses ordinary matrix-vector responses, exactly as the existing coupling/reduction requires.

```lean
theorem QueryAlgorithm.IsPassStructured.measureReal_nuclearNorm_sub_mul_lt_le_of_pass_lt_of_hasLaw_haarFrame
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {r q : ℕ}
    {alg : QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      ((k ⊕ (Fin (r + 1) × m) → ℝ) × (k ⊕ (Fin (r + 1) × m) → ℝ)) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    {pass : ℕ → ℕ} (hpass : alg.IsPassStructured pass) (hp : ∀ i < q, pass i < r)
    (halg : alg.IsMeasurable)
    {U : Ω → Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasLaw U (haarFrame (k ⊕ (Fin (r + 1) × m))
      (k ⊕ (Fin (r + 1) × m))) μ)
    (hwidth : equispacedGaussianFactor r * (q + Fintype.card k) ≤ Fintype.card m) :
    μ.real {ω | nuclearNorm
      (U ω * Matrix.diagonal (equispacedLevelSpectrum k m r) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).2) <
      Fintype.card m * equispacedNuclearTailFactor r + 2 * (Fintype.card k : ℝ) / 3} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r)))
```

```lean
theorem exists_le_measureReal_nuclearNorm_sub_mul_ge_of_pass_lt
    {r q : ℕ} (hwidth : equispacedGaussianFactor r * (q + Fintype.card k) ≤ Fintype.card m)
    {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ] :
    ∃ U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      HasOrthonormalCols U ∧
      1 - ((r : ℝ) + 2) *
        Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r))) ≤
      ρ.real {s | let A := U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ
        let output := (alg s).run A.mulVec
        equispacedNuclearTailFactor r * Fintype.card m +
          2 * (Fintype.card k : ℝ) / 3 ≤
            nuclearNorm (A - output.1 * output.2)}
```

```lean
theorem div_lt_of_forall_le_measureReal_nuclearNorm_sub_mul_le_of_pass_lt
    [Nonempty k] {r : ℕ} {ε : ℝ} {q : ℕ} (hε : 0 < ε)
    (hεr : ε ≤ equispacedAccuracyBound r)
    (hm : Fintype.card m = ⌊(Fintype.card k : ℝ) /
      (ε * ((r : ℝ) + 1) * (r + 2))⌋₊) {S : Type*} [MeasurableSpace S]
    {alg : S → QueryAlgorithm (k ⊕ (Fin (r + 1) × m) → ℝ)
      (k ⊕ (Fin (r + 1) × m) → ℝ) q
      (Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ × Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ)}
    (halg : QueryAlgorithm.IsMeasurableFamily alg) {pass : S → ℕ → ℕ}
    (hpass : ∀ s, (alg s).IsPassStructured (pass s)) (hp : ∀ s, ∀ i < q, pass s i < r)
    (ρ : Measure S) [IsProbabilityMeasure ρ]
    (hsucc : ∀ A : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ,
      A.PosSemidef → 1 / 2 ≤ ρ.real {s |
        nuclearNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ≤
          (1 + ε) * nuclearNorm (A - truncatedSVD A (Fintype.card k))}) :
    Fintype.card k / (equispacedQueryFactor r * ε) < q
```

## Deterministic statements and argument

Add the following structural statements to `FiniteSpectrum.lean` under the same section
variables as above (r is explicit):

```lean
theorem HasOrthonormalCols.nuclearNorm_sub_truncatedSVD_eq_mul_equispacedNuclearTailFactor
    (r : ℕ)
    {U : Matrix (k ⊕ (Fin (r + 1) × m)) (k ⊕ (Fin (r + 1) × m)) ℝ}
    (hU : HasOrthonormalCols U) :
    nuclearNorm (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ -
      truncatedSVD (U * Matrix.diagonal (equispacedLevelSpectrum k m r) * Uᴴ)
        (Fintype.card k)) =
      Fintype.card m * equispacedNuclearTailFactor r

theorem le_nuclearNorm_diagonal_sub_mul_of_equispacedLevelSpectrum
    (r : ℕ)
    (W : Matrix (k ⊕ (Fin (r + 1) × m)) k ℝ)
    (M : Matrix k (k ⊕ (Fin (r + 1) × m)) ℝ) :
    Fintype.card m * equispacedNuclearTailFactor r +
      (Fintype.card k - ∑ i : k, rangeProjector W (Sum.inl i) (Sum.inl i)) ≤
      nuclearNorm (Matrix.diagonal (equispacedLevelSpectrum k m r) - W * M)
```

Write D for the hard diagonal, P = rangeProjector W, Q = 1-P, and
capture = Σ_head P_ii. Trace duality and specNorm Q ≤ 1 give
nuclearNorm(D-WM) ≥ trace(Q(D-WM)) = trace(QD).
Every tail eigenvalue is at most r+1, the head eigenvalue is r+2, and
trace P = rank W ≤ K; therefore trace(PD) ≤ (r+1)K+capture.
Since trace D = (r+2)K + OPT₁, the missed mass bound is OPT₁+K-capture.
This argument does not assume the residual is PSD or that W has full column rank.
The same argument after orthogonal change of coordinates gives the rotated form.

The existing good Gaussian event bounds capture by K/4, hence nuclear excess is at least
3K/4. Use failure threshold OPT₁+2K/3, strictly below this for K>0.
For K=0, the strict lower-tail event is empty because its threshold is the optimum;
handle that case directly if needed by the deterministic proof.
The tail mass is OPT₁ = m(r+1)(r+2)/2, so ε OPT₁ ≤ K/2 < 2K/3.
Reuse the existing floor width and exceptional-probability arithmetic without changing constants:
under q ≤ K/(equispacedQueryFactor r·ε), width holds and the bad probability is <1/2.
Yao then contradicts the universal half-success hypothesis. The dimension and accuracy
cutoff are exactly the existing final theorem's, not merely asymptotically equivalent.

## Placement, search and proof plan

- `LowerBounds/LowRank/FiniteSpectrum.lean`: nuclear tail factor, exact nuclear optimum and deterministic
  missed-mass bound, following the corresponding Frobenius statements. These concern the
  specific hard family and belong in LowerBounds. Expected addition: 120–220 lines.
- `LowerBounds/LowRank/NuclearMinimax.lean`: the three headline statements above and rotated
  good-overlap consequence. Import `Minimax` and nuclear-norm continuity. Expected size:
  300–500 lines, below the file limits.
- `LowerBounds/LowRank/Minimax.lean`: promote existing shared private
  `measureReal_exists_mem_blockKrylovSpace_gt_quarter_le_of_hasLaw_gaussianMatrix`, `equispacedGaussianFactor_mul_add_le_and_mul_le_of_floor`, and
  `mul_exp_neg_div_lt_half` to public documented API, with no duplicated proofs.
  The existing Gaussian quarter-overlap bound is reused unchanged.
- `RandomMatrix/Haar/Basic.lean`: move the shared general Haar joint-event helper out of
  Minimax and expose it as `le_measureReal_hasOrthonormalCols_and_ge`, unchanged statement.
- `Matrix/Norms/Nuclear.lean`: add the general RCLike projected-error trace bound.
  Its exact interface is
  ```lean
  theorem re_trace_sub_rangeProjector_mul_le_nuclearNorm_sub_mul
      {𝕜 : Type*} [RCLike 𝕜] {n b : Type*} [Fintype n] [Fintype b]
      (A : Matrix n n 𝕜) (W : Matrix n b 𝕜)
      (M : Matrix b n 𝕜) :
      RCLike.re (A - rangeProjector W * A).trace ≤ nuclearNorm (A - W * M)
  ```
  This is generic matrix norm API, with no PSD assumption.

The projected trace helper uses Nuclear’s existing transitive projector imports;
  the dependency amendment below records why its initial candidate home was rejected.

Search order followed: Mathlib matrix spectrum/PSD API, then NLAlib norms, projector,
truncation, continuity and lower-bound files. Mathlib has the Hermitian spectral theorem
and `Matrix.IsHermitian.trace_eq_sum_eigenvalues`; no hard-family nuclear loss theorem found.
NLAlib already supplies `norm_trace_conjTranspose_mul_le_nuclearNorm_mul_specNorm`,
`norm_trace_le_nuclearNorm`, `HasOrthonormalCols.nuclearNorm_mul_left`,
`HasOrthonormalCols.nuclearNorm_mul_conjTranspose_right`,
`Matrix.PosSemidef.nuclearNorm_eq_re_trace`, `continuous_nuclearNorm`,
`trace_rangeProjector`, `rank_rangeProjector`, and star-projector norm API.
Use `continuous_nuclearNorm.measurable` for error-event measurability.
The existing Frobenius optimum proof in `FiniteSpectrum` provides the eigenvalue ordering;
reuse its spectral reasoning and `(lpGauge 1).matrixNorm_sub_truncatedSVD_le_of_rank_le`
with `lpGauge_one_matrixNorm` for the upper bound, rather than infer
nuclear optimum from Frobenius norm comparison. `RotationInvariant.lean` has a private
nuclear two-level truncation bound, but its spectrum and conclusion do not replace this result.
No prototype proof is imported or copied: the completed `LowerBounds-FixedBatches.md`,
`FiniteSpectrum.lean`, `Minimax.lean`, and `HiddenRotation.lean` supply the mathematical material.
There is no printed source for this new all-algorithm fixed-batch nuclear statement;
its public headline docstring will say “No printed source.” with a distinct result id.

Dependency order: exact optimum and missed-mass inequality; rotated overlap consequence;
deterministic Haar tail through the unchanged K7 and quarter-overlap estimate; randomized
worst-case via unchanged Yao; final query inversion through shared floor/probability lemmas.
Consumers are downstream lower-bound arguments applying the final theorem directly, or using
the distributional/worst-case statements with their own accuracy or success thresholds.
No caller supplies an information-theoretic certificate or conclusion-equivalent assumption.

Before proof dispatch, review these signatures and ensure the skeleton elaborates with the
repository options. Scaffold `FiniteSpectrum` imports its NLAlib counterpart; scaffold
`NuclearMinimax` imports its NLAlib counterpart, existing `Minimax`, and scaffold `FiniteSpectrum`, so deferred dependencies
are available. Implementation acceptance uses named module builds, standard-axiom audit,
linters, rules/names, references/constants, regenerated imports, ledger/status, and duplicate/reuse
checks as in CONTRIBUTING §9–11. The earlier authorization to commit and open a PR remains in force; merging is outside scope.

2026-10-26 review: accepted by independent mathematical/API review with the precise names,
shared Gaussian API promotion and Haar-helper relocation above. Implementation proceeds under
the maintainer’s explicit instruction to do the proposed nuclear extension.

2026-10-26 dependency amendment: the generic projected trace inequality lives in
`Matrix/Norms/Nuclear.lean`, the owner of nuclear trace duality. Putting it in the
projector-norm file creates the cycle Projector → Nuclear → KyFanNorm → Lidskii →
SingularValueInequalities → Projector. Nuclear already imports the projector API through
its spectral dependencies, so its existing imports suffice. No temporary misplaced copy remains.

2026-10-26 public-name review: the newly shared helpers use conclusion-based names
`equispacedGaussianFactor_mul_add_le_and_mul_le_of_floor`, `mul_exp_neg_div_lt_half`,
and `measureReal_exists_mem_blockKrylovSpace_gt_quarter_le_of_hasLaw_gaussianMatrix`.
No public preexisting name is removed; these were private implementation helpers.
