# Regression relative-error rates

Design approved after bounded independent review, 2026-10-16; implementation authorized. The user-authorized available-agent fallback continues because
the historical Opus/Fable/Sonnet model names are unavailable. Branch: `feat/regression-rates`.
Read with CONTRIBUTING, PORT_PROBABILITY D2–D6, PORT_LOWRANK D8 and S6/S7, and
`Regression-Organization.md`.

## Scope, consumers and placement

Publish two expected squared-Frobenius relative-error pairs (Gaussian/Haar), then one generic
injection-plus-AMM tail and two high-probability pairs (Gaussian/CountSketch). These serve callers
of `sketchAndSolve`, future Solvers, and a Regression Rates family in the explorer. Multiple RHS
columns are handled together; no dependence on the number of RHS columns enters sample rates.
No new objects, interfaces, parallel algorithm spelling, random-design copies or new law APIs.

Sequential files (never parallel proof builds):

1. `RandomMatrix/Gaussian/BlockMoments.lean`: move the existing public
   `gaussianProjectionFactor_le_one_add_of_three_mul_div_le` unchanged from
   `LowRank/Gaussian/RangeFinder.lean` to the Gaussian projection factor's owner. Its subject is
   the factor, not RSVD. The LowRank file already imports BlockMoments; preserve name and proof,
   delete the old copy, and check its consumers. No alias or duplicate helper.
2. `Regression/SketchAndSolve.lean` (772 lines before additions): add two residual-integrability
   bridges and the two expected explicit/asymptotic pairs. Target about 970 lines; if real code
   would exceed about 1000, record and review a topic split before proceeding. Do not preemptively
   split Gaussian from Haar because their existing proofs share private helpers.
3. `Regression/Oblivious.lean` (421 lines): add the single generic AMM-tail consumer below.
   Existing HasJLMoment tails remain primary and are not duplicated. Expected size below 500.
4. New `Regression/Gaussian.lean`: Gaussian high-probability relative residual, explicit size
   corollary and its asymptotic form. Import Regression.Oblivious and Sketching.Gaussian.Gaussian;
   optional import Regression.SketchAndSolve only if needed for documented shared API, not proofs.
5. New `Regression/CountSketch.lean`: the corresponding CountSketch pair over `RCLike`, importing
   Regression.Oblivious and Sketching.Sparse.CountSketchEmbedding. Expected about 160–220 lines.

The two family modules are topics, not a cross-family Rates dump. Regression remains below
LowRank and above Sketching. No Regression import of LowRank is permitted. Outside-stage
additions are only the named-factor helper relocation in item 1, whose lower home is required
for reuse. Regenerate root imports for the two new modules.

## Search and mathematical sources

Search order completed before drafting signatures:

* Mathlib: searched `Mathlib/LinearAlgebra/Matrix` and all Mathlib for `sketchAndSolve`, sketched
  regression and these relative-residual statements: none. No Mathlib bridge/API replacement is
  introduced. Mathlib's `HasLaw`, `Integrable`, `Measure.real` remain the probability interfaces.
* NLAlib: exact Gaussian/Haar residual identities and oblique-residual integrability are in
  Regression.SketchAndSolve. Residual-specific integrability names are absent, so two rewrite
  bridges are useful. The factor comparison helper already exists in LowRank.Gaussian.RangeFinder
  and must move, not be re-proved. Regression.Oblivious has HasJLMoment fixed/random-design tails,
  but no `RCLike` arbitrary-AMM-tail regression consumer. CountSketch AMM is already `RCLike` in
  Sketching.Sparse.CountSketch, and its embedding/OSI sizes are in CountSketchEmbedding.
  Gaussian has a second JL moment and Gaussian injection sizes. LowRank.Oblivious.CountSketch
  demonstrates the same injection+AMM proof pattern; it cannot be imported upward.
* Prototype: read `LowRank/Nystrom/SketchedRegression.lean` and `GaussianNystrom.lean` under
  `/home/tyler/Documents/prove2me/lean/NLAlib`. They expose deterministic fitted-core/split and
  Gaussian assembly with old `frobSq`, Fin types and parallel algorithm names. Reuse the
  mathematics only; current Matrix/Regression APIs already replace that machinery. No new port
  mapping is warranted for fresh corollaries of existing ported results.
* Local primary source: `/home/tyler/Documents/NLA-papers-repo/papers/2605.19096/source/content.tex`,
  Theorem 2.1 (`thm:partial-isometry`), §2.1 remarks, gives both exact mean-square factors and the
  explicit dimension reading. Cite `[EpperlyWebber2026, Theorem 2.1 and §2.1]`, real case; our
  rank-plus-one asymptotic reading includes rank zero uniformly. The input identities retain
  `[TroppYurtseverUdellCevher2017, Lemma A.5]` where appropriate.
* Local primary source: `/home/tyler/Documents/prove2me/books/woodruff_14.pdf`, Theorem 23 and its
  proof (printed pp. 33–34) explicitly uses the normal-equation/Pythagorean split, constant
  injection and approximate multiplication. Cite `[Woodruff2014, Theorem 23]`: source has sparse
  real vector regression, constant success probability and unsquared objective; here matrix RHS,
  explicit failure δ and squared objective. The CountSketch rate here is the refined separate
  injection+AMM accounting, not a claim that the source prints the same bound. Gaussian HP uses
  the same route with this library's second-moment bound, not an optimal Gaussian tail claim.

No fresh citation locator is invented. Existing refs suffice. No Mathlib deviation is introduced.

## Common exact signature context

The following are signatures to implement, not skeleton declarations or proofs. Unqualified
names live in `namespace NLAlib`. For ordinary declarations use:

```lean
open MeasureTheory ProbabilityTheory
open scoped Matrix MatrixOrder ComplexOrder
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {𝕜 : Type*} [RCLike 𝕜]
variable {m n r p : Type*} [Fintype m] [Fintype n] [Fintype r] [Fintype p]
variable [DecidableEq m]
```

Expectation declarations are real, with `S : Ω → Matrix p m ℝ` or
`Q : Ω → Matrix m p ℝ`. The least-squares optimum is always written
`frobNorm ((1 - rangeProjector A) * B) ^ 2`; no new OPT definition. Every asymptotic `C,ε₀`
comes before all types, measures, matrices and parameters, and its explicit target is in the
same file. The main theorems retain existing result IDs, with bidirectional named links.

## Expected relative residual: exact signatures

Two bridge declarations have no new mathematics and no Result tag:

```lean
theorem integrable_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_gaussianMatrix
    {S : Ω → Matrix p m ℝ} (hS : HasLaw S (gaussianMatrix p m) μ)
    (A : Matrix m n ℝ) (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2) μ

theorem integrable_frobNorm_sub_mul_sketchAndSolve_sq_of_hasLaw_haarFrame
    [DecidableEq p] {Q : Ω → Matrix m p ℝ} (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (A : Matrix m n ℝ)
    (hA : A.rank + 2 ≤ Fintype.card p) (B : Matrix m r ℝ) :
    Integrable (fun ω => frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2) μ
```

The explicit bounds use the source factor directly, with a natural-rank integrability condition
and the exact polynomial inequality equivalent to `p ≥ rank A + 1 + rank A / ε`:

```lean
theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_gaussianMatrix
    {S : Ω → Matrix p m ℝ} (hS : HasLaw S (gaussianMatrix p m) μ)
    (A : Matrix m n ℝ) (B : Matrix m r ℝ) {ε : ℝ} (hε : 0 < ε)
    (hA : A.rank + 2 ≤ Fintype.card p)
    (hp : (A.rank : ℝ) ≤ ε * ((Fintype.card p : ℝ) - A.rank - 1)) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2

theorem integral_frobNorm_sub_mul_sketchAndSolve_sq_le_one_add_mul_of_hasLaw_haarFrame
    [DecidableEq p] {Q : Ω → Matrix m p ℝ} (hQ : HasLaw Q (haarFrame m p) μ)
    (hpm : Fintype.card p ≤ Fintype.card m) (A : Matrix m n ℝ)
    (B : Matrix m r ℝ) {ε : ℝ} (hε : 0 < ε)
    (hA : A.rank + 2 ≤ Fintype.card p)
    (hp : (A.rank : ℝ) ≤ ε * ((Fintype.card p : ℝ) - A.rank - 1)) :
    ∫ ω, frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2 ∂μ ≤
      (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2
```

The Haar sufficient size matches Gaussian; its exact finite-population factor is smaller.
Do not optimize that threshold or claim the Gaussian threshold is necessary for Haar.
Both explicit docs carry `Result: sketch-and-solve-expected-error`.

```lean
theorem exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω m n r p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        [Fintype r] [Fintype p] [DecidableEq m] (μ : Measure Ω) (S : Ω → Matrix p m ℝ)
        (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε : ℝ),
        HasLaw S (gaussianMatrix p m) μ → 0 < ε → ε ≤ ε₀ →
        C * (((A.rank : ℝ) + 1) / ε) ≤ Fintype.card p →
        ∫ ω, frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2 ∂μ ≤
          (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2

theorem exists_forall_integral_frobNorm_sub_mul_sketchAndSolve_sq_le_of_hasLaw_haarFrame :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω m n r p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        [Fintype r] [Fintype p] [DecidableEq m] [DecidableEq p] (μ : Measure Ω)
        (Q : Ω → Matrix m p ℝ) (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε : ℝ),
        HasLaw Q (haarFrame m p) μ → Fintype.card p ≤ Fintype.card m →
        0 < ε → ε ≤ ε₀ → C * (((A.rank : ℝ) + 1) / ε) ≤ Fintype.card p →
        ∫ ω, frobNorm (B - A * sketchAndSolve A (Q ω)ᴴ B) ^ 2 ∂μ ≤
          (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2
```

Suggested witnesses `C=3`, `ε₀=1`: use the existing moved factor comparison at rank `A.rank+1`,
then monotonicity in rank, giving the required integrability and factor bound. Apply the exact
identity directly if using that route avoids unnecessary conversion back through `hp`; either
way the asymptotic proof must instantiate the explicit theorem. No rank-positive hypothesis.
The `+1` gives a uniform nonzero size threshold; rank-zero recovery itself is exact and no
spurious `0/0` probability or moment claim is used. Empty dimensions and zero RHS are allowed.

## Generic AMM-tail consumer: exact signature

Here `S : Ω → Matrix p m 𝕜`, `A : Matrix m n 𝕜`, `B : Matrix m r 𝕜`.

```lean
theorem HasSubspaceInjection.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_one_add_mul_le
    [IsFiniteMeasure μ] {S : Ω → Matrix p m 𝕜} {A : Matrix m n 𝕜}
    {a δ δ' ε : ℝ} (h : HasSubspaceInjection S A a δ μ) (ha : 0 < a)
    (hε : 0 ≤ ε) (B : Matrix m r 𝕜)
    (hAMM : μ.real {ω | a * √ε * frobNorm ((1 - rangeProjector A) * B) <
      frobNorm (rangeProjector A * (S ω)ᴴ * S ω * ((1 - rangeProjector A) * B))} ≤ δ') :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ + δ'
```

Proof plan: the exact orthogonal error split and
`IsSubspaceInjection.matrixNorm_obliqueProjector_mul_le` specialize to the Frobenius norm;
outside injection failure and the AMM event, the excess squared is at most `ε * OPT²`.
Use a union bound in `μ.real`. No measurability premise is added just to state an outer-measure
bound. The AMM tail is an input estimate, not a new hypothesis predicate; this follows the
existing arbitrary-AMM-tail consumer in LowRank.Oblivious.RangeFinder. It is mathematically
necessary to preserve complex CountSketch support. Tag `Result: sketch-and-solve-ls`.

Existing `HasJLMoment.measure_frobNorm_sub_mul_sketchAndSolve_sq_gt_le` remains the real generic
JL-moment API and already yields relative error when `rank A * η² ≤ ε a²`. Gaussian uses it;
no duplicate wrapper is proposed. Existing vector embedding consequences remain in Embedding;
no additional embedding-only family rates, which would have worse ε dependence, are introduced.

## Gaussian high-probability pair: exact signatures

```lean
theorem measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix p m ℝ} (hG : HasLaw G (gaussianMatrix p m) μ)
    (A : Matrix m n ℝ) (B : Matrix m r ℝ) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hp : gaussianInjectionDim A.rank (1 / 2) (δ / 2) ≤ Fintype.card p)
    (hp' : 16 * ((A.rank : ℝ) + 1) ≤ ε * δ * Fintype.card p) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A
        (G ω) B) ^ 2} ≤ δ

theorem exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω m n r p : Type} [MeasurableSpace Ω] [Fintype m] [Fintype n]
        [Fintype r] [Fintype p] [DecidableEq m] (μ : Measure Ω) (G : Ω → Matrix p m ℝ)
        (A : Matrix m n ℝ) (B : Matrix m r ℝ) (ε δ : ℝ),
        HasLaw G (gaussianMatrix p m) μ → 0 < ε → ε ≤ ε₀ →
        0 < δ → δ ≤ 1 / 2 →
        C * (((A.rank : ℝ) + 1) / (ε * δ)) ≤ Fintype.card p →
        μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
          frobNorm (B - A * sketchAndSolve A
            (G ω) B) ^ 2} ≤ δ
```

The named injection dimension is currently
`4(√d + √(2 log(1/δ)))²/η²`, at `η=1/2,δ/2` above. Show that value with a marker in the doc.
Use the Gaussian normalized sketch's JL moment at
`η = √(ε/(4*(rank A+1)))`: its failure `2/(pη²) ≤ δ/2` and the coefficient
`rank A*η²/(1/2)² ≤ ε`. The conclusion concerns the unnormalized Gaussian `G`: use the existing
`sketchAndSolve_smul_sketch` to remove its nonzero normalization, with nonempty rows derived
from `hp'`, not assumed redundantly. This is a scaling bridge, not a new probability argument.
Verified asymptotic witnesses are `C=128, ε₀=1`: at failure `δ/2`, the injection dimension is at
most `32r + 64 log(2/δ)`. For `δ≤1/2`, `log(2/δ)≤2/δ`; moreover
`32r + 128/δ ≤ 128(r+1)/(εδ)` for `ε≤1, δ≤1/2`, since after multiplication by δ the left
side is at most `16r+128≤128(r+1)`. This absorbs the log term into the displayed rate.
For the explicit Gaussian HP theorem, handle `δ≥1` by the probability bound first; invoke the
injection dimension theorem only in the remaining `δ<1` branch, without adding a weaker δ restriction.
This is a second-moment sufficient rate, not the best logarithmic-in-failure Gaussian result.
Tag both docs `Result: sketch-and-solve-ls`, and link the exact pair bidirectionally.

## CountSketch high-probability pair: exact signatures

```lean
theorem measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch
    [DecidableEq p] {S : Ω → Matrix p m 𝕜} (hS : HasLaw S (countSketch p m) μ)
    (A : Matrix m n 𝕜) (B : Matrix m r 𝕜) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hp : countSketchRows A.rank (1 / 2) (δ / 2) ≤ Fintype.card p)
    (hp' : 16 * ((A.rank : ℝ) + 1) ≤ ε * δ * Fintype.card p) :
    μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
      frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ

theorem exists_forall_measureReal_frobNorm_sub_mul_sketchAndSolve_sq_gt_le_of_hasLaw_countSketch :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ {Ω 𝕜 m n r p : Type} [MeasurableSpace Ω] [RCLike 𝕜] [Fintype m]
        [Fintype n] [Fintype r] [Fintype p] [DecidableEq m] [DecidableEq p]
        (μ : Measure Ω) (S : Ω → Matrix p m 𝕜) (A : Matrix m n 𝕜)
        (B : Matrix m r 𝕜) (ε δ : ℝ),
        HasLaw S (countSketch p m) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
        C * ((((A.rank : ℝ) + 1) ^ 2 + ((A.rank : ℝ) + 1) / ε) / δ) ≤
          Fintype.card p →
        μ.real {ω | (1 + ε) * frobNorm ((1 - rangeProjector A) * B) ^ 2 <
          frobNorm (B - A * sketchAndSolve A (S ω) B) ^ 2} ≤ δ
```

Use injection `a=1/2,δ/2` and CountSketch's own `RCLike` AMM with
`η=√(ε/(4*(rank A+1)))`; the projector Frobenius norm squared is `rank A`.
The generic AMM consumer's excess threshold is at least `η√(rank A)*OPT`, so its failure
is at most `2/(pη²) ≤ δ/2`. Handle zero projector or residual by an empty strict event rather
than call an AMM theorem requiring two nonzero inputs. Verified asymptotic witnesses `C=16,
ε₀=1` dominate both explicit requirements. CountSketch rows are unscaled one-sign-per-column
sketches, not Gaussian-normalized. Tag `Result: sketch-and-solve-ls` and link the pair.

## Degenerate cases, scope boundaries and verification

Rank zero: every pair uses rank-plus-one in its asymptotic threshold, avoiding an impossible
zero-size claim. Gaussian/CountSketch HP lower size forces nonempty p. Haar carries p≤m
and explicit integrability rank+2≤p. Rank deficiency is allowed; no full-column-rank A hypothesis.
Zero optimal residual gives exact recovery on the injection event; zero B/empty RHS and empty
ambient/column types must not be discharged by an invalid division. All bound equations show
expectations of squared residuals, never squared expectations. HP failure is strict `>` because
it is the complement of a non-strict good error bound; using `≥` would fail for zero residual.

No new numerical definition is needed: only existing gaussianInjectionDim, countSketchRows and
projection factors are used, plus small explicit source/proof constants. Docstrings show current
registered values with markers and use square-bracket `\mathbb{P}[...]` events. At least one
member of each explicit/asymptotic pair carries its Result id. New Rates entries are added only
after Lean proofs, extraction and source-hash validation; catalogue labels must distinguish
expectation from high probability and show the rank-plus-one threshold and Haar cap.

Implementation was authorized after bounded review. Implement in
the file order above, one proof file at a time. Log capped two-thread module builds and
`lake lean ... -- -M 8000`, then complete root audit/lint/import checks, refs/constants/LaTeX,
reuse checks on the new headline theorems and the duplicate report. Do not repeat overlapping
root/stage gates without a new failure or change. Update status and design report; leave the
ledger unchanged unless an actual prototype mapping changes.

## Review questions / recommendations

1. Accept the uniformly rank-zero-safe `rank+1` asymptotics rather than excluding rank zero.
2. Keep Gaussian HP at the existing second-moment rate in this bounded stage; logarithmic δ
   improvements require higher-moment/concentration work and are not implied by the signatures.
3. Keep the shared expected theorems in SketchAndSolve unless implementation shows a real file
   budget issue; the two new HP family modules avoid moving existing shared private helpers.
4. `[DecidableEq m]` is present for the identity/range-projector expressions, including all
   asymptotic binders; any additional genuinely necessary elaboration instance is documented
   before implementation without weakening a theorem.
5. Constants 128 (Gaussian HP) and 16 (CountSketch HP) are verified witnesses, not exported
   named universal constants; the proofs establish the corresponding size arithmetic.

## Implementation amendment: integrability instances (2026-10-16)

The residual-integrability bridges omit `[DecidableEq m]` because their types contain no identity
matrix or range projector; `classical` supplies it internally for rewriting the existing oblique
lemma. Explicit bound hypotheses and asymptotic types retain it. This removes an unused-instance
linter warning and does not weaken any mathematical statement. The positive ε parameter in the
explicit expected bounds is retained for its sample-size reading; its proof binder is `_hε`
because the polynomial size hypothesis already supplies the inequality used by the proof.

## Stage implementation read-back (2026-10-16)

All eleven planned new declarations are proved. The existing Gaussian factor comparison helper
was relocated unchanged to RandomMatrix.Gaussian.BlockMoments; its LowRank consumer still
builds through its pre-existing direct import. No new object, interface, named constant or
prototype mapping was introduced. No proof or statement of a pre-existing theorem changed.

* Expected Gaussian/Haar: two integrability bridges and two explicit/asymptotic pairs in
  Regression.SketchAndSolve (930 lines). The squared Frobenius regression residual expectation
  is at most `(1+ε)` times the squared optimal orthogonal residual when rank+2≤p and
  rank≤ε(p−rank−1); Haar additionally has p≤m. Both asymptotic pairs use absolute witnesses
  C=3, ε₀=1 and the rank-zero-safe size `(rank+1)/ε`. The exact expectation identities remain
  the mathematical input, with the Haar factor bounded by the Gaussian one.
* Generic AMM tail: Regression.Oblivious consumes a finite-measure injection tail, a>0, ε≥0
  and the supplied residual multiplication tail at a√ε·OPT. The strict relative-error failure
  probability is at most δ+δ′, over any RCLike field. The proof uses the existing exact split,
  oblique-projection norm bound and a union bound. No measurability or isotropy hypothesis is
  added to this outer-measure statement.
* Gaussian high probability: Regression.Gaussian uses the existing second JL moment and
  constant injection. Its formal result is for the unnormalized Gaussian sketch, using the
  existing scale-invariance lemma. δ≥1 is handled before the injection theorem. The explicit
  two-budget size yields the `(1+ε)` squared relative residual with failure at most δ; the
  asymptotic pair has C=128, ε₀=1 and `(rank+1)/(εδ)`, for δ≤1/2. This is not a claim of optimal
  Gaussian failure dependence.
* CountSketch high probability: Regression.CountSketch uses the generic AMM consumer and the
  direct CountSketch AMM theorem over RCLike. The two explicit budgets yield the same squared
  relative residual event; C=16, ε₀=1 gives `((rank+1)^2+(rank+1)/ε)/δ`. The proof separately
  handles zero projector or zero optimal residual, without calling an AMM theorem requiring
  nonzero inputs. No real-only JL-moment specialization is used.

Per-file validation passed sequentially with LEAN_NUM_THREADS=2: BlockMoments and the existing
LowRank Gaussian RangeFinder target builds; SketchAndSolve, Oblivious, Gaussian and CountSketch
module builds and `lake lean ... -- -M 8000` checks. Final per-file logs have no warnings.
References (40 asymptotic forms), constants and LaTeX checks passed. The four expectation
headlines' reuse report confirms the exact identities/factor APIs, with each asymptotic proof
instantiating its explicit theorem. Logs: `/tmp/nlalib-regression-rates-checks`.

Independent bounded reviews found no mathematical blockers for the design and each implemented
topic. Both new modules are registered in `NLAlib.lean`; the full integration gates below passed.
No commit or push was made by the implementation or validation agents. The ledger was reviewed
and remains unchanged: these are fresh corollaries, and moving the helper changes no existing
declaration-key mapping or prototype disposition.

## Final library validation (2026-10-16)

Sequential two-thread validation passed, with logs in `/tmp/nlalib-regression-rates-checks`:

* Full `NLAlib NLAlibScaffold` build: 3873 jobs, zero warnings. Both root import-generation
  checks passed. The four new or expanded Regression module target builds and single-file
  `lake lean ... -- -M 8000` checks, plus the moved-helper owner and consumer target builds,
  had already passed and were not repeated.
* Axiom audit: 7235 reachable declarations, zero violations. Environment lint: 14 linters,
  4994 declarations plus 2241 generated declarations, zero errors. Duplicate report: 4597
  library theorems, zero duplicate classes.
* References: 55 bibliography keys and 40 asymptotic forms, zero problems. Named bounds:
  25 entries, 5460 docstrings, 259 markers on 255 spans, zero problems. KaTeX: 18047 math
  spans in those docstrings, zero problems. Whitespace checks passed.
* Reuse covers all eleven new public declarations. The integrability bridges rewrite existing
  oblique-residual results; expected bounds use exact Gaussian/Haar identities and factor
  comparisons; Gaussian HP uses the existing JL-moment regression consumer; CountSketch HP
  uses the new generic AMM consumer and existing complex-compatible moment estimate. Each
  asymptotic proof instantiates its explicit theorem.
* Source inspection confirms the 300-module import graph is acyclic and Regression imports no
  LowRank module. The audit confirms no new `sorry` or forbidden axiom is reachable. The
  existing projection-factor helper was moved unchanged, without a second declaration.
* Fresh extraction `/tmp/nlalib-regression-rates-explore.json` contains 301 modules (including
  the root) and 3466 public declarations. All eleven new declarations are present and proved;
  all 301 extraction-time module source hashes match the current checkout bytes.

These checks cover the full-library gates required by CONTRIBUTING §9. A second overlapping
`stage_check.sh` build/audit/lint/duplicate run was omitted because there was no new failure or
source change requiring repetition. Explorer metadata and browser integration consume this fresh
extraction and are reported separately; no unproved rate is advertised.
