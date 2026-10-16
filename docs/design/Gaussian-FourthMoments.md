# Design: Gaussian fourth moments

Written 2026-10-16 on `feat/gaussian-fourth-moments`. Design only; signatures below
are the implementation contract, subject to bounded review. The Probability standing approval
covers this routine extension: no new carrier, vocabulary, global instance or hypothesis
interface. The requested Opus/Fable aliases are unavailable in this tool environment; the
orchestrator records its available-model author/reviewer fallback in the stage report.

## Scope and objects

Finish the explicit omission in RandomMatrix-R2 §0: fourth-order Wick for linear forms,
the exact fourth moment of a Gaussian sandwich, and exact Gaussian approximate matrix
multiplication (AMM), with its dimension-free factor-two bound. Consumers are Gaussian sketch
variance analyses, the existing Sketching AMM interfaces, and later randomized low-rank error
analyses. Exact formulas expose information that a JL-derived AMM bound discards.

Use the existing real laws `gaussianVector n`, `gaussianMatrix m n`, Mathlib `HasLaw`,
`⬝ᵥ`, `*ᵥ`, `frobNorm`, and `ᴴ`. No new objects or interfaces, no `frobSq`, no matrix linear-form
wrapper, no pairings datatype, no transpose twins. Gaussian laws remain real under D4; this is
not an assertion about circular complex Gaussian laws, whose fourth moments differ.

## Search and reuse

Searched pinned Mathlib first (`Probability/Distributions/Gaussian` and a tree-wide search for
Wick/Isserlis): no fourth mixed-moment or pairings identity found. Reuse
`memLp_id_gaussianReal'`, `HasGaussianLaw.memLp`, `HasLaw.memLp_comp_iff`,
`HasLaw.integral_comp`, and finite-sum/Holder integral APIs instead of proving moment finiteness.
Mathlib's existing Gaussian/independence notions are used directly, so no deviation entry.

Then searched current NLAlib. `Distributions/Gaussian.lean` already owns
`integral_pow_four_of_hasLaw_gaussianReal`, `hasLaw_dotProduct_of_hasLaw_gaussianVector`,
`hasGaussianLaw_dotProduct_of_hasLaw_gaussianVector`, `isIsotropic_of_hasLaw_gaussianVector`.
`QuadraticForm/Moments.lean` already proves `memLp_quadForm`,
`integral_norm_quadForm_sub_trace_sq`, and `variance_quadForm_of_hasLaw_gaussianVector`;
use this algebra for Gaussian quadratic forms, do not duplicate its independent-coordinate
fourth-moment case split. Its mixed-coordinate helper is private: no reaching through a
private name. Fourth linear forms can instead follow from polarization of the scalar fourth
moment (or a public, topic-appropriate helper if needed and recorded before adding it).
`RandomMatrix/Gaussian/Moments.lean` already has the unsandwiched fourth moment; keep it there
and do not restate it. Reuse `hasLaw_uncurry_of_hasLaw_gaussianMatrix`,
`frobNorm_eq_norm_toLp_uncurry`, `frobNorm_kronecker`, `frobNorm_sq_eq_sum`,
`frobNorm_conjTranspose`, and existing Frobenius product bounds.
The private vectorization proof in Moments is not a public API; reproduce neither its
private name nor an alternative public object. A direct entry expansion is adequate.

Finally read prototype `RandomMatrix/Gaussian/Moments/{FourthMoment,ApproxMultiplication}.lean`
and `Probability/Gaussian/Moments/{WickPairings,Isserlis}.lean`. Reuse their contractions as
proof material, generalized from `Fin` to finite types and rewritten in current vocabulary.
The prototype's recursive `GaussianPairings`, pairing-position lists, covariance-matrix wrapper,
measure/HasLaw twins and arbitrary-order recursion are deliberately excluded. Full arbitrary
order Wick needs a separate stage with an actual higher-order consumer and a reviewed pairings
representation; fourth-order Wick here needs only its three explicit contractions.

## Exact APIs and ownership

All signatures below are inside `namespace NLAlib`, with

```lean
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {a b m n k : Type*} [Fintype a] [Fintype b] [Fintype m] [Fintype n] [Fintype k]
```

### 1. `Probability/Distributions/GaussianMoments.lean` (new)

This is the home of moments of Gaussian vectors and their linear images, independent of
random-matrix vocabulary. Import Gaussian and QuadraticForm/Moments as needed. In order:

```lean
theorem integrable_dotProduct_mul_four_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) (u v w z : n → ℝ) :
    Integrable (fun ω => (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) *
      (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω)) μ

theorem integral_dotProduct_mul_four_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) (u v w z : n → ℝ) :
    ∫ ω, (u ⬝ᵥ g ω) * (v ⬝ᵥ g ω) * (w ⬝ᵥ g ω) * (z ⬝ᵥ g ω) ∂μ =
      (u ⬝ᵥ v) * (w ⬝ᵥ z) + (u ⬝ᵥ w) * (v ⬝ᵥ z) +
        (u ⬝ᵥ z) * (v ⬝ᵥ w)

theorem integrable_norm_mulVec_pow_four_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix m n ℝ) :
    Integrable (fun ω => ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4) μ

theorem integral_norm_mulVec_pow_four_of_hasLaw_gaussianVector {g : Ω → n → ℝ}
    (hg : HasLaw g (gaussianVector n) μ) (A : Matrix m n ℝ) :
    ∫ ω, ‖WithLp.toLp 2 (A *ᵥ g ω)‖ ^ 4 ∂μ =
      frobNorm A ^ 4 + 2 * frobNorm (Aᴴ * A) ^ 2
```

No additional covariance-law theorem is required: the four linear forms are already jointly
Gaussian with arbitrary singular covariance. General centered `HasGaussianLaw` Isserlis is
reserved for a consumer holding that hypothesis directly. The norm identity can use the
existing Gaussian quadratic-form variance of `Aᴴ * A`, plus isotropic mean and trace bridges.
The four-form theorem consumes scalar fourth moments or quadratic-form polarization.

### 2. `RandomMatrix/Gaussian/FourthMoment.lean` (new)

Owns fourth moments of matrix linear images and centered Gaussian Gram products. Import 1
and existing Gaussian/Moments; no Sketching import. In order:

```lean
theorem integrable_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix m n ℝ} (hG : HasLaw G (gaussianMatrix m n) μ)
    (A : Matrix a m ℝ) (B : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (A * G ω * B) ^ 4) μ

theorem integral_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix m n ℝ} (hG : HasLaw G (gaussianMatrix m n) μ)
    (A : Matrix a m ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * G ω * B) ^ 4 ∂μ =
      (frobNorm A ^ 2 * frobNorm B ^ 2) ^ 2 +
        2 * frobNorm (Aᴴ * A) ^ 2 * frobNorm (B * Bᴴ) ^ 2

theorem integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix m n ℝ} (hG : HasLaw G (gaussianMatrix m n) μ)
    (A : Matrix a m ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * G ω * B) ^ 4 ∂μ ≤
      3 * (frobNorm A ^ 2 * frobNorm B ^ 2) ^ 2

theorem integrable_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (A * (G ω * (G ω)ᴴ) * B -
      (Fintype.card k : ℝ) • (A * B)) ^ 2) μ

theorem integral_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * (G ω * (G ω)ᴴ) * B -
      (Fintype.card k : ℝ) • (A * B)) ^ 2 ∂μ =
      (Fintype.card k : ℝ) * (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (A * B) ^ 2)
```

The unnormalized identity belongs here: it is about a centered Gaussian Gram matrix, needs
no sketch object or positive sketch dimension, and is reusable for Wishart fluctuations.
The arbitrary rectangular `B` states multiplication directly; the prototype's `Nᴴ` form is
obtained by substitution. Exact constants 2 and 3 are small mathematical literals (§5.2),
not named adjustable bounds.

### 2 continued: normalized Gaussian AMM in the same file

The normalized formula remains a Gaussian matrix moment with a deterministic scalar, so it
belongs in `RandomMatrix/Gaussian/FourthMoment.lean` too. Sketching consumes this lower-layer
API directly; no extra topic file or wrapper is needed. In order, under `[Nonempty k]` for the two expectation statements (not integrability):

```lean
theorem integrable_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    Integrable (fun ω => frobNorm (A * ((Fintype.card k : ℝ)⁻¹ •
      (G ω * (G ω)ᴴ)) * B - A * B) ^ 2) μ

theorem integral_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix [Nonempty k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * ((Fintype.card k : ℝ)⁻¹ •
      (G ω * (G ω)ᴴ)) * B - A * B) ^ 2 ∂μ =
      (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (A * B) ^ 2) / Fintype.card k

theorem integral_frobNorm_mul_smul_gram_mul_sub_sq_le_of_hasLaw_gaussianMatrix [Nonempty k]
    {G : Ω → Matrix n k ℝ} (hG : HasLaw G (gaussianMatrix n k) μ)
    (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    ∫ ω, frobNorm (A * ((Fintype.card k : ℝ)⁻¹ •
      (G ω * (G ω)ᴴ)) * B - A * B) ^ 2 ∂μ ≤
      2 * frobNorm A ^ 2 * frobNorm B ^ 2 / Fintype.card k
```

The formulas use the right-sketch orientation `n × k`; a left sketch is obtained via `Gᴴ`
and the existing law bridge. Do not introduce a normalized Gaussian distribution or a second
scaling definition. A public `HasAMM` consequence is unnecessary if the current JL-moment
consumer already supplies it; only add a direct interface corollary when it improves that API
and list its exact signature in a dated amendment first.

## Integrability, boundaries, and proof checks

Every integral inequality has an immediately available integrability companion. `HasLaw`
supplies probability and a.e. measurability; do not demand either again. Scalar Gaussian
linear forms are in L4; Holder gives integrability of four products; finite sums give all
matrix companions. Normalized integrability at empty `k` is the integrable constant
`frobNorm (A * B) ^ 2`, not zero. The normalized identity and bound require `[Nonempty k]`:
when `k` is empty, the sketch is zero and the error is generally nonzero, whereas division by
zero gives zero. All other index types may be empty; every unnormalized identity is valid
without rank or positivity assumptions. Zero factors and singular matrices are allowed.

Prefer the shorter existing quadratic-form variance proof where it applies; use the fourth
linear-form identity for cross terms. No Stein bounded-derivative theorem applies directly to
cubic polynomial tests; do not force a polynomial-growth calculus extension for this stage.

## Provenance and execution

Prototype formal result names: `integral_linForm_mul_four_gaussianMatrix`,
`integral_frobSq_mul_gaussianMatrix_mul_sq`,
`integral_frobSq_mul_gram_mul_transpose_sub` and their transport variants. Record these against
new declarations in the ledger. Preserve result ids `gaussian-frob-fourth-moment` and
`gaussian-amm`; the vector four-form may use `gaussian-fourth-moment`.
For citations use existing `MartinssonTropp2020`, `HalkoMartinssonTropp2011`, `Woodruff2014`
only where the printed result is actually present: HMT Proposition 10.1 is second moment,
not provenance for an asserted printed fourth-moment formula. Docstrings must state that the
fourth/AMM identities are consequences of Gaussian fourth moments. Verify a precise Isserlis
bibliographic entry/label before citing it; do not copy prototype unpublished-project citations.

Ownership and execution are strictly sequential: one proof agent owns file 1, report/review;
then one owns file 2, report/review; then wrap up both files. Do not write proofs
before bounded design review. Any helper outside these two homes requires a dated placement
amendment; no exceptions currently planned. At wrap-up register imports, update ledger/status,
run the contract checks with one build at a time and logs, and leave theorem read-backs for the
branch's eventual PR. Do not commit or push unless explicitly asked.

## Open questions and choices

No enduring interface question needs a maintainer stop. Chosen: fourth order only, existing
HasLaw interfaces, vector moments in Probability, Gaussian Gram fluctuations in RandomMatrix,
normalized AMM alongside Gaussian Gram fluctuations in RandomMatrix. A general-covariance arbitrary-order Wick API remains separate.

## 2026-10-16 implementation guidance from reuse review

`Sketching/Sparse/CountSketch.lean` AMM section was inspected: its private
`sum_sum_frobNorm_of_mul_star_sq` and
`sum_sum_frobInner_of_mul_star_transpose` are distribution-free deterministic contractions.
Do not independently reprove these if the Gaussian AMM proof needs precisely their statements.
Move them, with public names/docstrings and call-site updates, to
`Matrix/Norms/Frobenius.lean`, their topic owner, as a sequential preliminary amendment/file
pass if required. That optional pass must be approved in the bounded design review before
proof work starts; otherwise use the vector four-form route without copying these helpers.
Similarly, publishing the existing mixed-coordinate fourth-moment helper belongs in
`Probability/QuadraticForm/Moments.lean` and must precede its use, with the changed file owned
sequentially. No new moment hypothesis interface is warranted. The preferred baseline remains
the two new files above and the existing public quadratic-form algebra.

## 2026-10-16 bounded review and first-file implementation

The independent bounded review approved this design without blockers. File 1 uses scalar
fourth-moment polarization for Wick and the existing Gaussian quadratic-form variance for
the norm identity. No placement changes or helper extractions were needed.

## 2026-10-16 stage report

Execution location: `/tmp/nlalib-gaussian-fourth-moments`, branch
`feat/gaussian-fourth-moments`, base `0daf947`. The independent bounded design review approved
implementation before proofs. Both sequential proof files subsequently received independent
bounded reviews approving their mathematics and placement, contingent on clean compilation;
both module builds and per-file `lake lean ... -- -M 8000` checks passed. Requested
Opus/Fable/Sonnet/Haiku aliases were not exposed by the available tools; the orchestrator used
available GPT-6.1-Sol author, proof, independent review, and mechanical integration agents and
recorded that fallback explicitly. After validation, the user requested a local commit;
no push was requested.

### Delivered statements, read back from Lean

All laws and matrices below are real, all index types arbitrary finite types. The only
probabilistic hypothesis is the existing `HasLaw`; it supplies probability and a.e.
measurability. No new object, hypothesis interface, global instance, named adjustable constant,
helper extraction, or placement deviation was introduced. There are twelve public theorems
in the two designed topic files.

- `integrable_dotProduct_mul_four_of_hasLaw_gaussianVector`: the product of any four fixed
  linear forms of a standard Gaussian vector is integrable.
- `integral_dotProduct_mul_four_of_hasLaw_gaussianVector`: its expectation is the sum of the
  three products of paired dot products; arbitrary singular covariance between the four forms
  is allowed.
- `integrable_norm_mulVec_pow_four_of_hasLaw_gaussianVector`: the fourth power of the
  Euclidean norm of any fixed matrix times that vector is integrable.
- `integral_norm_mulVec_pow_four_of_hasLaw_gaussianVector`: that fourth moment is
  `frobNorm A ^ 4 + 2 * frobNorm (Aᴴ * A) ^ 2`.
- `integrable_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix`: the fourth power of the
  Frobenius norm of any fixed sandwich `A * G * B` is integrable.
- `integral_frobNorm_mul_mul_pow_four_of_hasLaw_gaussianMatrix`: its expectation is
  `(frobNorm A ^ 2 * frobNorm B ^ 2) ^ 2 +
  2 * frobNorm (Aᴴ * A) ^ 2 * frobNorm (B * Bᴴ) ^ 2`.
- `integral_frobNorm_mul_mul_pow_four_le_of_hasLaw_gaussianMatrix`: the same expectation is
  at most `3 * (frobNorm A ^ 2 * frobNorm B ^ 2) ^ 2`.
- `integrable_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix`: the squared Frobenius
  norm of `A * (G * Gᴴ) * B - card k • (A * B)` is integrable for `G : Matrix n k ℝ`.
- `integral_frobNorm_mul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix`: that expectation is
  `card k * (frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (A * B) ^ 2)`.
- `integrable_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix`: normalized AMM
  squared error is integrable even for an empty sketch type.
- `integral_frobNorm_mul_smul_gram_mul_sub_sq_of_hasLaw_gaussianMatrix`: for a nonempty sketch
  type its expectation is
  `(frobNorm A ^ 2 * frobNorm B ^ 2 + frobNorm (A * B) ^ 2) / card k`.
- `integral_frobNorm_mul_smul_gram_mul_sub_sq_le_of_hasLaw_gaussianMatrix`: for a nonempty
  sketch type the expectation is at most `2 * frobNorm A ^ 2 * frobNorm B ^ 2 / card k`.

Every other index type may be empty. All unnormalized formulas allow empty sketch types;
zero factors and rank-deficient matrices are included. No positivity, rank, or independence
hypotheses were added. Normalized expectation formulas require nonempty `k`, as designed.
Full arbitrary-order Wick, recursive pairings, and a general centered `HasGaussianLaw`
interface remain deliberately excluded.

### Integration and provenance

Both modules are registered by `mk_all`, which includes untracked files through filesystem
traversal unless `--git` is supplied. The root diff adds exactly their two imports.
`Isserlis1918` supplies the verified fourth-order provenance. Result ids are
`gaussian-fourth-moment`, `gaussian-frob-fourth-moment`, and `gaussian-amm`. The old R2 scope cut
has a dated amendment linking this follow-up.

Exactly twelve existing R2-cut ledger entries were reconsidered, with every other entry
preserved. Sandwich and normalized AMM measure/HasLaw twins now map to their consolidated
HasLaw theorems; the old AMM conjunction note points to the separately named factor-two bound.
Matrix four-linear-form and coordinate-four-form entries map to the vector theorem using the
uncurry law and, for coordinates, basis-vector specialization. Generic product-entry Fubini
wrappers and second-linear-form wrappers remain explicitly not reproduced, with existing
Mathlib/isotropy routes stated. The atlas check accounts for all twelve declarations in the
two prototype modules. No general all-order Isserlis result is claimed ported.

### Validation and reuse

Final checks passed, with one Lean process group at a time and `LEAN_NUM_THREADS=2` for builds.
Logs are execution artifacts under `/tmp/nlalib-gaussian-fourth-checks`. After validation the
worktree was relocated to `/home/tyler/Documents/NLA-lib/nlalib-gaussian-fourth-moments` for
durable delivery. The user subsequently requested a local commit; no push was requested.

- Explicit `lake build NLAlib NLAlibScaffold`: 3860 jobs, zero warnings
  (`full-build.log`). Both new files also passed the proof agents' individual module builds
  and `lake lean <file> -- -M 8000` checks; the final Wick change was docstring-only.
- Required `scripts/stage_check.sh`: exit 0, 287 proved modules, zero unproved modules;
  its cached explicit-module build completed 3856 jobs with zero warnings (`stage-check.log`).
  Its axiom audit found 6950 declarations and zero violations; its 14 linters found zero errors
  in 4856 declarations plus 2094 generated declarations. The stage script uses
  `lake env lean -M 8000` internally for audit/lint; individual proof-file checks used
  `lake lean` with project options as required.
- References: 55 keys, zero problems. Constants: 24 constants, 5295 docstrings, 226 value
  markers on 222 spans, zero problems. Both are included in `stage-check.log`.
- Duplicate report inspected, including potential swallowed errors: 4461 library theorems,
  zero duplicate classes, no diagnostics (`nlalib-stage-check/duplicates.log`).
- Both generated roots passed `mk_all --check` (`mk_all-NLAlib-check.log` and
  `mk_all-NLAlibScaffold-check.log`).
- KaTeX: 5295 docstrings, 16678 math spans, zero problems (`latex.log`). Existing local
  `node_modules` was linked into the execution worktree; no dependency installation was needed.
- Targeted reuse completed for all twelve public theorems (`reuse.log`), without warnings or
  errors. The vector norm moment consumes quadratic-form variance and isotropic mean; the
  sandwich consumes the vector norm moment via the Gaussian uncurry law, Kronecker identities,
  and Frobenius bridges; the centered Gram contraction consumes the private bilinear
  quadratic-form moment; normalized AMM consumes that centered formula and Frobenius
  submultiplicativity. Wick uses polarization of scalar fourth moments through topic-local
  private helpers. No distribution-free contraction helper was copied from CountSketch.
- `git diff --check`, forbidden proof-token search, exact twelve-entry ledger-diff check,
  nonnull ledger-target resolution, and prototype atlas coverage all passed. The two new
  files contain 182 and 300 lines. No scaffold statement or `sorry` was added.

The final bounded stage review approved the read-backs, mappings, placement, scope, and docs,
contingent on these clean checks. No interface or placement flag remains open.
