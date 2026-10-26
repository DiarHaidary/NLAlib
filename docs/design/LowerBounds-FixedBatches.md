# Fixed-batch Frobenius low-rank lower bounds

**Status: implemented and validated (2026-10-26).**

2026-10-26. Branch `stage/lbc-fixed-batches` (started as `design/lbc-fixed-batches`), based on
`stage/lbc` at `668dcd5`.
This is the first extension requested after completion of LB-C: generalize its Frobenius
lower bound from two batches to every fixed batch budget. The input dimensions are those of
an explicit equispaced hard family. The existing two-pass API and its better constants remain
unchanged. The completed K7 is reused as a theorem, without changing its statement or proof.

## 1. Scope and read-back

For each `r : ℕ`, nonempty target-rank index type `k`, and sufficiently small positive `ε`,
choose a tail multiplicity

$$m=\left\lfloor\frac{|k|}{\varepsilon(r+1)(r+2)}\right\rfloor.$$

Every measurable randomized algorithm that uses at most `r` batches and succeeds with probability
at least one half on every PSD input of dimension `|k| + (r+1)m` needs

$$q>\frac{|k|}{256\,4^{r+1}(r+1)(r+2)\,\varepsilon}.$$

Success means **squared** Frobenius error at most `(1 + ε)` times the optimal squared error,
matching the current library API. This proves the fixed-`r` rate `Ω_r(k/ε)` in chosen dimensions.
It does not claim a sharp dependence on `r`. It includes `r = 0`: the hypotheses then assert a
zero-query algorithm succeeds on all inputs, and the conclusion rules this out. No positivity
hypothesis on `r` is needed by the argument. The final result assumes `[Nonempty k]`.

An unsquared target `‖A-X‖ ≤ (1+ε) OPT` can later instantiate the squared theorem at
`η = (1+ε)^2-1 ≤ 3ε` for `ε ≤ 1`, losing a factor three in the query denominator and accuracy
cutoff. That corollary is outside this first implementation.

**Out:** arbitrary ambient dimensions and zero-padding reductions; Schatten norms; expectation
versions; the optimized polynomial `r^{-3}` construction using shifted Chebyshev nodes; a sharp
round-query tradeoff; spectral-norm extensions; changing any existing two-pass statement.

## 2. Objects, interfaces and constants

Use existing objects directly:

- `equispacedLevelSpectrum k m r`, with index type `k ⊕ (Fin (r + 1) × m)`;
- `QueryAlgorithm`, `QueryAlgorithm.IsMeasurableFamily`, `QueryAlgorithm.IsPassStructured`;
- `HasLaw`, `haarFrame`, `gaussianMatrix`, `HasOrthonormalCols`;
- `blockKrylovSpace`, `rangeProjector`, `frobNorm`, `truncatedSVD`, `Matrix.PosSemidef`.

No new hypothesis predicate or structure is introduced. The batch index remains a natural number
because its order and recursion carry the mathematics. The model still counts vector queries;
a batch label is bounded per seed by `∀ i < q, pass s i < r`. Algorithms output `(W, M)`, so the
explicit approximation `W * M` has rank at most `|k|` without a separate rank assumption.

Introduce five total real-valued numerical definitions, documented and registered in
`docs/constants.toml` before skeleton validation:

```lean
irreducible_def equispacedInterpolationFactor (r : ℕ) : ℝ := 4 ^ (r + 1)
irreducible_def equispacedGaussianFactor (r : ℕ) : ℝ :=
  64 * equispacedInterpolationFactor r
irreducible_def equispacedTailFactor (r : ℕ) : ℝ :=
  ((r : ℝ) + 1) * (r + 2) * (2 * r + 3) / 6
irreducible_def equispacedQueryFactor (r : ℕ) : ℝ :=
  256 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2)
irreducible_def equispacedAccuracyBound (r : ℕ) : ℝ :=
  1 / (512 * 4 ^ (r + 1) * ((r : ℝ) + 1) * (r + 2) ^ 2)
```

The interpolation factor is deliberately coarse: the exact coefficient-square sum is
`Nat.choose (2*r+2) (r+1) - 1`, but its upper bound `4^(r+1)` suffices here. Positivity and the
explicit one-sided comparisons are the consumer API; later tightening changes bodies and those
comparisons. The tail factor is the exact sum of squares of the positive tail levels, not a
probability bound. All definitions are meaningful at `r = 0`; there are no junk denominator cases.

Required numerical API: positivity of all five quantities, `1 ≤ equispacedInterpolationFactor r`,
`equispacedGaussianFactor r = 64 * equispacedInterpolationFactor r`,
`equispacedQueryFactor r = 4 * equispacedGaussianFactor r * (r+1)*(r+2)`, and
`equispacedAccuracyBound r = 1 / (2*(r+2)*equispacedQueryFactor r)`.

## 3. Headline statement shapes

The following sections use ordinary Lean section variables

```lean
variable {Ω S k m : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
  [Fintype k] [Fintype m] [DecidableEq k] [DecidableEq m]
  {μ : Measure Ω} {r q : ℕ}
```

### 3.1 Deterministic algorithm, Haar input

```lean
theorem QueryAlgorithm.IsPassStructured.measureReal_frobNorm_sub_mul_sq_lt_le_of_pass_lt_of_hasLaw_haarFrame
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
    μ.real {ω | frobNorm
      (U ω * Matrix.diagonal (equispacedLevelSpectrum k m r) * (U ω)ᴴ -
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).1 *
        (alg.run (hiddenRotationOracle (U ω)
          (Matrix.diagonal (equispacedLevelSpectrum k m r)))).2) ^ 2 <
      Fintype.card m * equispacedTailFactor r + (2 * (r : ℝ) + 3) * Fintype.card k / 2} ≤
      (r + 2) * Real.exp (-(Fintype.card m / (2 * equispacedGaussianFactor r)))
```

The `let` expressions only abbreviate matrices and outputs, not proof terms or extra hypotheses.
The primary theorem is a tail, before any sample-size inversion. It does not assume nonempty `k`.

### 3.2 Randomized algorithm, worst-case hard input

```lean
theorem exists_le_measureReal_frobNorm_sub_mul_sq_ge_of_pass_lt
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
        equispacedTailFactor r * Fintype.card m +
          ((2 * r + 3 : ℕ) : ℝ) / 2 * Fintype.card k ≤
            frobNorm (A - output.1 * output.2) ^ 2}
```

The returned hard input is PSD because every level of the fixed diagonal is positive and the
returned `U` has orthonormal columns. This is proved as supporting API, not assumed by Yao.

### 3.3 Explicit relative-error query bound

```lean
theorem div_lt_of_forall_le_measureReal_frobNorm_sub_mul_sq_le_of_pass_lt
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
        frobNorm (A - ((alg s).run A.mulVec).1 * ((alg s).run A.mulVec).2) ^ 2 ≤
          (1 + ε) * frobNorm (A - truncatedSVD A (Fintype.card k)) ^ 2}) :
    Fintype.card k / (equispacedQueryFactor r * ε) < q
```

No opaque `HasLowerBound` premise, spectral certificate supplied by the caller, unproved
information lemma, or conclusion-equivalent hypothesis is permitted. The constants are explicit
and precede no dimension-dependent existential. A `2/3` success guarantee immediately implies
the stated `1/2` guarantee; no separate proof of the same lower bound is needed.

## 4. Mathematical decomposition and checked constant arithmetic

Write `t = r+1`, `T = (r+1)(r+2)`, `Δ = 2r+3`, `C = 4^(r+1)` and `A = 64C`.
The hard diagonal has head `r+2` with multiplicity `|k|` and tail levels `1,…,r+1` each with
multiplicity `|m|`. Its optimal squared error is `|m|*T*Δ/6`.

1. Finite differences at `1,…,r+2` give, for `deg P ≤ r`,
   `P(r+2) = Σ_{j=0}^r (-1)^(r-j) choose(r+1,j) P(j+1)`.
   Cauchy–Schwarz gives coefficient-square sum at most `C`. Apply it separately to each column
   polynomial in `mem_blockKrylovSpace_iff`.
2. Generalize the current deterministic interpolation bound: lower tail Gram bounds
   `s² I ≤ G_jᴴG_j` and head spectral norm at most `S` imply
   `s² Σ_head z_i² ≤ C*S²*‖z‖²` for depth `r+1`.
3. The existing Gaussian singular-value inequalities and a union over `r+1` tail blocks give,
   for `γ > 2`, head fraction `9C/(γ-2)²` outside an event of probability at most
   `(r+2) exp(-|m|/(2γ²))`, assuming `|k| ≤ |b|` and `γ²|b| ≤ |m|`.
4. Choose `γ = 8 sqrt C`. Since `C ≥ 1`, `γ-2 ≥ 6 sqrt C`, so the head fraction is at most
   `1/4`, and `γ²=A`. The projector trace argument already used in `FewPasses` then bounds the
   output head mass by `|k|/4`.
5. The deterministic loss bound is
   `‖D-WM‖_F² ≥ |m|*T*Δ/6 + Δ*(|k|-headMass)`.
   Hence the good Gaussian event gives excess at least `3Δ|k|/4`, strictly above the primary
   theorem's excess threshold `Δ|k|/2`. K7 gives depth `r+1` and width `q+|k|` for every algorithm.
6. Apply the existing Yao interface exactly as in the two-pass theorem, using PSD hard inputs.
7. Set `x=|k|/(εT)` and `|m|=floor x`. The accuracy bound gives
   `x ≥ 8A(r+2)|k| ≥ 8A(r+2)`, so `x≥2` and `|m|≥x/2≥4A(r+2)`.
   If `q≤x/(4A)`, then `Aq≤x/4`; the same accuracy bound gives `A|k|≤x/4`. Thus
   `A(q+|k|)≤x/2≤|m|`, satisfying the Gaussian width condition.
8. Put `y=|m|/(2A)≥2(r+2)`. Since `exp y≥1+y>2(r+2)`, the bad probability is strictly less
   than `1/2`. Meanwhile `ε*OPT² ≤ Δ|k|/6 < Δ|k|/2`, so every relative-error success lies
   strictly below the primary failure threshold. Contradiction proves `q>x/(4A)`.

This gives `equispacedQueryFactor = 4AT` and `equispacedAccuracyBound = 1/(8AT(r+2))`.
The dimension is `|k|+(r+1)floor(|k|/(εT))`, of order `|k|/(ε(r+2))` for fixed `r`.
There is no claim here for every dimension or an optimal dependence on `r`.

## 5. Files, placement and reuse

The current `FewPasses.lean` is already over the advisory 1000-line threshold; do not append this
stage wholesale there. Preserve every existing theorem and constant.

| File | Additions and reason | Expected size |
|---|---|---:|
| `Polynomial/Interpolation/DividedDifference.lean` | Scalar interpolation factor/API and generic polynomial extrapolation inequality; scalar polynomial topic, lower layer. | +100–160 lines |
| `LowerBounds/LowRank/FiniteSpectrum.lean` | Tail/Gaussian factors, optimum, PSD hard-instance API, general loss-overlap, deterministic and Gaussian Krylov capture; imports existing `FewPasses` for the unchanged hard-family definition. | 650–950 lines |
| `LowerBounds/LowRank/Minimax.lean` | Query/accuracy factors, deterministic algorithm tail, randomized worst-case and explicit query bound, using K7 and Yao. | 600–950 lines |

If initial skeleton work uses fewer files, record the exact split before proof dispatch. A scalar
polynomial theorem must not import a constant declared in `LowerBounds`: its factor belongs to
the polynomial file, or the scalar statement uses the explicit `4^(r+1)` and the lower-layer
consumer rewrites its named factor. No new matrix/probability vocabulary row is needed; the five
numerical definitions get constants-registry entries and vocabulary references as required.

Every scaffold topic imports its `NLAlib` counterpart, existing `FewPasses`, K7/Yao, and the
scaffold topics containing dependencies. `Minimax` additionally imports scaffold `FiniteSpectrum`;
`FiniteSpectrum` imports scaffold polynomial interpolation if that proof remains deferred.

Material searched/read:

- `FewPasses.lean`: current two-pass Frobenius optimum, loss, interpolation, Gaussian union bound,
  projector head-mass argument, Yao and floor arithmetic. Reuse the route; preserve the stronger
  existing two-pass constants. Shared generic helpers must be promoted at their mathematical home
  or consumed through public API, rather than copied across files.
- `HiddenRotation.lean`: finished arbitrary-`r` K7 and its empty-initial-block range corollary.
- `Polynomial/Interpolation/DividedDifference.lean`:
  `sum_neg_one_pow_mul_choose_mul_eval_eq_zero` supplies the identity.
- Mathlib `Data/Nat/Choose/Vandermonde`: `Nat.sum_range_choose_sq` supplies the exact squared
  coefficient sum if used; `Nat.sum_range_choose` and
  `Finset.sum_sq_le_sq_sum_of_nonneg` give the coarse factor.
- Mathlib square-power sum searched: no direct `sum_range_sq` API found. The real scalar identity
  `6*Σ_{j=0}^r(j+1)^2=(r+1)(r+2)(2r+3)` has a short induction. A public scalar lemma would go in
  `ForMathlib/Algebra/BigOperators/Intervals.lean`; otherwise keep the evaluation proof local to
  the optimum theorem, without a new general public declaration.
- `~/nlalib-harness/reports/OP5-TwoPassMinimax.md`, Proposition E and §3.2/§4: mathematical source,
  no printed source for the new all-algorithm fixed-batch rate. Internal notes are not citations
  in public library docstrings.

No new Mathlib deviation or hypothesis interface is proposed. The existing real Gaussian/Haar
laws determine the scalar field of the probabilistic statements; there are no transpose twins.

## 6. Proof dispatch and acceptance

Suggested dependency waves:

1. Numerical positivity/API, polynomial extrapolation and exact tail energy.
2. General deterministic loss and Krylov capture.
3. Gaussian capture tail and inversion to head fraction `1/4`.
4. Deterministic algorithm tail using K7, then randomized worst-case using Yao.
5. Floor/query-bound arithmetic, final explicit theorem and D8 move.

Each worker owns one declaration or planned small bundle. The statements are fixed before
proofs; no worker may add assumptions or weaken a constant to finish. Use the existing harness
statement/build/axiom checks. One build per machine; named module targets and memory limits follow
`CONTRIBUTING` §10. No commit or push is authorized by this design task.

Before declaring the extension complete: no `sorry` in its library modules; public final target
has only the standard three axioms; full build `--wfail`; environment linters; extraction-backed
rules/naming; constants, references, ledger and regenerated imports; duplicate/reuse report;
read-back checked against the signature above. Final module splits stay below 1500 lines and
proofs below 80 lines. The original two-pass public API must still build unchanged.

## 7. Approval questions

Recommended approval is the chosen-dimension, squared-error statement above, with the five
conservative explicit constants and `r : ℕ` including zero. This is the requested first extension.
No decision about all dimensions, Schatten norms or optimized `r` dependence is needed.

The maintainer must approve this concrete note and the compiled statement skeleton before proof
dispatch (`AGENTS.md` item 2 and `CONTRIBUTING.md` §8/§11). This draft records no such approval.


## 8. Prepared design artifacts

The five numerical definitions are registered in `docs/constants.toml`. The proposed scaffold
has two finite-spectrum structural statements (the exact optimum and interpolation inequality)
and the three headline minimax statements above. It compiles with exactly five expected
`declaration uses sorry` warnings and no other warnings at initial preparation. Implementation
has now started under the recorded maintainer approval.

Mathematical review: accepted after checking the explicit constants, PSD-only final hypothesis,
`r = 0`, empty intermediate index types, the floor conditions and probability strictness.
Maintainer approved this written note on 2026-10-26 ("Approve and implement").


### Implementation placement amendment (2026-10-26)

Four existing proof-local helpers are needed by the new files: `norm_sq_mulVec_single_eq`,
`sq_mul_sum_sq_le_sum_sq_mulVec`, `sum_head_mass_sq_le`, and `measureReal_le_prod_fst`.
They are temporarily exposed in `FewPasses` to unblock the dependency build. Before completion,
the projector facts move to `Matrix/Basic/Projector`, the Gram inequality to `Matrix/Basic/Gram`,
and the product-measure fact to the corresponding `ForMathlib/MeasureTheory/Measure` topic.
The real symmetry of a star projector is already `Matrix.IsHermitian.apply`; no duplicate
symmetry theorem is exported. The existing two-pass public statements are preserved.


## 9. Implementation read-back (2026-10-26)

All proposed results and supporting arguments are proved with the three headline signatures
unchanged. The scalar estimates, finite-spectrum geometry and algorithmic bounds occupy their
planned mathematical topics. The four shared helpers were moved to their proper Matrix and
ForMathlib owners, and all temporary compatibility aliases were removed. The scaffold is empty.
The implementation branch is `stage/lbc-fixed-batches`; it preserves the existing two-pass API.
The numerical constants remain exactly those approved above. Final full-library validation is
recorded in `docs/port/status.md`.
