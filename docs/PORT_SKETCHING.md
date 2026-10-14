# Port brief: the Sketching round

For the orchestrating agent building `NLAlib/Sketching/`. Read `CONTRIBUTING.md` in full first
(above all §5.1 on `L2Operator`, §5.2 "Numerical bounds", §5.4, §7 and the skeleton rule), then
`docs/design/Probability-REPORT.md` (what the layers below export, their constants, the
orchestrator's decisions and the open work), `docs/design/Mathlib-deviations.md`, and the survey
this brief is built on, `docs/port/inventory-sketching.md` (cited below as "the inventory").
Status: **draft, 2026-10-14; §2 part (a) open for the maintainer**, part (b) taken by the
orchestrator and open to correction.

## 0. What this is and is not

- **The goal** is the layer that the randomized algorithms (range finding with structured test
  matrices, sketch-and-solve, sketch-and-precondition, generalized Nyström, Hutch++) will prove
  their theorems on: a small set of sketch properties stated once, the deterministic and
  probabilistic consequences of each proved once, and the standard sketch families shown to have
  them. A downstream theorem takes a property and knows nothing about the distribution
  (`CONTRIBUTING.md` §5.4, "A conclusion is an interface too").
- **The prototype** (`~/Documents/prove2me/lean/NLAlib/Sketching/`, read-only; about 150 files,
  31.5k lines, 1873 declarations, no `sorry`) is material, not a template. The inventory found one
  deterministic predicate (real) and no probabilistic one; five conclusion shapes for the
  embedding over six families; JL and approximate matrix multiplication (AMM) as inline events
  with no caller; sample sizes inline; the SRHT in four variants; and 1702 declarations in a
  sparse block proving one trace-moment bound for one i.i.d. model.
- **Scope of the round**: the property predicates and their API; the Gaussian, Haar, sub-Gaussian
  (Rademacher), row-sampling, SRHT and CountSketch families with their embedding and JL
  theorems; sampling without replacement as far as the SRHT needs it; the sparse embeddings
  (SparseStack, OSNAP) to the extent fixed by D6. The Probability round left two entries for this
  one: sub-Gaussian Johnson–Lindenstrauss and the Haar JL in Dasgupta–Gupta form
  (`Probability-REPORT.md` §6.1 item 5, §6.3).
- **Not in scope**: the randomized algorithms (later rounds), except the deterministic
  consequences of an embedding (S0); complex Gaussian, Haar and sign laws (parallel definitions
  later, `Probability-REPORT.md` §4 item 11); fast JL with a sparse projection, Kac walks, tensor
  sketches, LESS embeddings, lower bounds; approximating leverage scores; the prototype's sparse
  machinery unless D6 says otherwise; finite precision.

## 1. Process

As in the Probability round (`docs/PORT_PROBABILITY.md` §1), with its amendments:

- **Consumers first.** Each stage's design note opens with what the layers above will use from it.
  Here the inventory's §3 is blunt: no formalised consumer uses a subspace embedding, a JL
  property or AMM, because sketch-and-solve, sketch-and-precondition, Nyström PCG and Hutch++'s
  error bound are atlas `candidate`s. The consumers are therefore the statements those
  algorithms need (§5 of this brief), and S0 proves the deterministic half of them in this round
  as the test that the predicates are usable.
- **Degenerate-case checklist** for every statement (`PORT_PROBABILITY.md` §3.2), plus the
  sketching cases: `d = 0` (no columns, the embedding holds trivially), `card k = 0` (no sketch
  rows), a sampling probability `p i = 0` (division by zero in the sampling sketch; the
  domination hypothesis must force the row of `U` to vanish there), `U` without full column rank
  (the predicate is relative to `Uᴴ * U`), parameters `a ≤ 0` or `b < a`.
- **File budget.** Up to about twenty-five statements and about 1000 lines per skeleton file, or
  the note names its split in advance.
- **Duplicate search** against Mathlib and the built `NLAlib/` before a statement enters a
  skeleton; a lemma a second file could want is public from the start.
- **Skeleton rule**: never a `sorry` in a proved file; new statements go in a new skeleton file.
- **Delegation** as in `docs/port/status.md`'s standing instructions (Opus drafts and proves,
  Fable reviews, Sonnet does bookkeeping; every `Agent` call passes `model`).
- **Approval.** The maintainer decides §2 part (a) before any skeleton depends on it. Part (b) and
  everything else proceeds without a stop and is recorded in the stage's note. A question of the
  (a) kind that arises later is added to §2, marked open, and the work that depends on it waits.
- **Design checkpoint** for the maintainer after S2: the predicates of S0 and S1 have then met
  their first two families, before the remaining six stages build on them.
- **Deviations from Mathlib** get an entry in `Mathlib-deviations.md` in their commit. None is
  expected: `HasLaw`, `Measure.pi`, `uniformOn` and the Loewner order are used as Mathlib has them.
- **Ledger.** The ledger accounts for the 1873 public declarations of the prototype's
  `Sketching/` (most of the sparse block with the reason fixed by D6), and for the two
  sub-Gaussian JL entries carried over from the Probability round.

## 2. Decisions

### 2(a) Decisions for the maintainer

Each with options, a recommendation, the reason and the rework a change after the round would
cost. They fix what every later layer takes as a hypothesis.

**D1. The deterministic embedding predicate.** Every embedding theorem of the round concludes it
and every consumer takes it.
- (a) Symmetric, one parameter: `IsSubspaceEmbedding S U ε`, the Loewner sandwich
  `(1 - ε) • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U) ≤ (1 + ε) • (Uᴴ * U)` (the inventory's §10.1).
- (b) Two parameters: `IsSubspaceEmbedding S U a b`, a structure with fields
  `lower : a • (Uᴴ * U) ≤ (S * U)ᴴ * (S * U)` and `upper : (S * U)ᴴ * (S * U) ≤ b • (Uᴴ * U)`,
  `a b : ℝ`; the `ε` form is the instance `a = 1 - ε`, `b = 1 + ε`, written so in statements,
  with no second predicate.
- (c) The prototype's norm form `∀ x, (1 - ε) ‖U x‖² ≤ ‖S U x‖² ≤ (1 + ε) ‖U x‖²`, as a `def`.
Common to all: `S : Matrix k n 𝕜`, `U : Matrix n p 𝕜` with any finite index types, any `U` (no
orthonormality, no full rank), over `𝕜`; API: the norm form as an `iff`, the Gram form
`a • 1 ≤ (S * U)ᴴ * (S * U)` for `HasOrthonormalCols U`, the singular-value form, monotonicity in
the parameters, `of_range_le` (an embedding of `U` is one of every `V` with
`range V ≤ range U`), invariance under `U` into `U * C`, scaling `c • S` (parameters times
`‖c‖ ^ 2`), composition (`S₂ * S₁`, parameters multiply), measurability of
`{ω | IsSubspaceEmbedding (S ω) U a b}` for measurable `S`.
*Recommendation (b).* The two sides have different natural constants: a Gaussian sketch has
`(1 ∓ (√d + t) / √k) ^ 2`, and forcing one `ε` early is what produced the prototype's `3 * a ≤ ε`
and `ε ≤ 1` side conditions (the inventory, §10.1). R3's conclusions plug in with no rescaling
(an unnormalized Gaussian `G` has `a = (√k - √d - t) ^ 2`, `b = (√k + √d + t) ^ 2`). The
consumers depend on the ratio: sketch-and-solve's residual factor is `√(b / a)`, the condition
number of the preconditioned matrix is at most `√(b / a)` (`CONTRIBUTING.md` §5.3, "spectral
equivalence"), so a two-parameter predicate states them without a division by `1 - ε`. Scaling
and composition are exact in (b) and lossy in (a). A one-sided upper statement is the instance
`a = 0`; a one-sided lower statement stays the raw Loewner half, which is §5.3 vocabulary.
*Rework:* every embedding statement of this round and every consumer.

**D2. The probabilistic predicates and their carrier.**
- Random variable, not law: a random matrix `S` on `(Ω, μ)` with values in `Matrix k n 𝕜`, as in
  the Probability round's D2; the law form is `HasLaw.id`, and each predicate gets a
  `HasLaw.…_iff` lemma (it depends on the law of `S` only). Options for the shape: (i)
  `Prop`-valued `def`s or structures on `(S, μ)`; (ii) classes on a measure on matrices, as
  `IsLeftUnitarilyInvariant` is; (iii) no predicate, the tail written in each theorem.
  *Recommendation (i):* instance search cannot supply real parameters, and (iii) is the
  prototype's failure.
- `HasSubspaceEmbedding S U a b δ μ := μ.real {ω | ¬ IsSubspaceEmbedding (S ω) U a b} ≤ δ`: a
  fixed `U` (sketch-and-solve, sketch-and-precondition, leverage sampling).
- `IsObliviousSubspaceEmbedding S d a b δ μ`: `HasSubspaceEmbedding S U a b δ μ` for every
  `U : Matrix n n 𝕜` with `U.rank ≤ d`. Options for the quantifier: (α) rank-bounded square
  matrices on the ambient type, as stated; (β) every `U : Matrix n (Fin d) 𝕜`; (γ) every
  submodule of `EuclideanSpace 𝕜 n` of `finrank ≤ d`. *Recommendation (α):* no quantification
  over types, no `Fin`, and `of_range_le` (through `rangeProjector U'`) gives every
  `U' : Matrix n p 𝕜` of rank at most `d` in one line. The
  API proves the transfer a two-sketch consumer needs: an oblivious `S` independent of a random
  `U` of rank at most `d` embeds it with the same `δ` (Fubini).
- **JL.** `HasJLProperty S ε δ μ`: for every `x` with `‖WithLp.toLp 2 x‖ = 1`,
  `μ.real {ω | ε ≤ |‖WithLp.toLp 2 (S ω *ᵥ x)‖ ^ 2 - 1|} ≤ δ` (unit vectors, since at `x = 0` the
  non-strict event is everything). `HasJLMoment S ε δ p μ`, Kane and Nelson's moment property:
  for every unit `x`, `|‖S x‖² - 1| ^ p` is integrable with integral at most `ε ^ p * δ`. Options:
  (A) both, with JL moment implying the JL property (Markov), the JL lemma for `N` points (union
  bound), and AMM; (B) the JL property only, AMM from second moments per family. *Recommendation
  (A):* one hypothesis gives all three consequences for every family that has it (Gaussian, Haar,
  sub-Gaussian, CountSketch at `p = 2`), replacing the prototype's three inline shapes.
- **AMM** is a theorem, not a predicate: its conclusion
  `μ.real {ω | ε * frobNorm A * frobNorm B ≤ frobNorm (Aᴴ * (S ω)ᴴ * S ω * B - Aᴴ * B)} ≤ δ` is
  derived once from `HasJLMoment` (and once, as an exact second moment, for row sampling). A
  predicate is added if a consumer takes it as a hypothesis.
- `HasGramTraceMoment S U q B μ`: for `HasOrthonormalCols U`, the error
  `E = (S * U)ᴴ * (S * U) - 1` has `re (trace (E ^ (2 * q)))` integrable with integral at most
  `B`. One lemma gives `HasSubspaceEmbedding S U (1 - ε) (1 + ε) (B / ε ^ (2 * q)) μ` from
  `specNorm E ^ (2 * q) ≤ re (trace (E ^ (2 * q)))` for Hermitian `E` (`TracePowers.lean` has the
  opposite bound; the note searches for this one).
  CountSketch is `q = 1`, the sparse laws are general `q`. The oblivious form quantifies over
  `U` outside, as in (α).
*Rework:* every probabilistic sketching statement, and every consumer hypothesis.

**D3. Which families are first-class this round, and over which field.** "First-class" means: a
named law, theorems concluding the D1 and D2 predicates in tail form, and named sample sizes.

| family | law | field | concludes | stage |
|---|---|---|---|---|
| Gaussian | `gaussianMatrix k n`, scaled by `(√k)⁻¹` | ℝ | OSE, JL, JL moment | S2 |
| Haar rows `√(n/k) Qᴴ` | `haarFrame n k` | ℝ | OSE, JL, JL moment, exact isotropy | S2 |
| independent sub-Gaussian rows, Rademacher | `iIndepFun`, `IsSubgaussianVector`, `IsIsotropic` per row; `rademacherMatrix` an instance | ℝ | OSE, JL, JL moment | S3 |
| row sampling (leverage, importance) | `Measure.pi fun _ => samplingMeasure p` on indices | `𝕜` | fixed-`U` embedding, AMM | S4 |
| SRHT and SRFT | signs and a uniform subset (or i.i.d. indices) on a hypothesis `H` | `𝕜` | OSE | S6 |
| CountSketch | uniform hash and signs | ℝ | OSE through trace moment `q = 1`, JL moment `p = 2` | S7 |
| SparseStack, OSNAP | per D6 | ℝ | OSE through trace moments | S8 |

Options: (a) all seven, sparse per D6; (b) drop the Haar sketch and the SRFT; (c) add fast JL
and LESS. *Recommendation (a).* Orthonormal sketches are first-class by the maintainer's
standing instruction (`status.md`, Probability inputs item 4) and are cheap given R5; the SRHT
over `𝕜` with `H` a hypothesis covers Walsh (real) and Fourier (complex) with one proof. Real
laws (Gaussian, Haar, signs, hashes) conclude the `𝕜` predicates at `𝕜 = ℝ`; their complex
analogues, later, conclude the same predicates without a rename. *Rework:*
low for adding a family later; moderate for the field of the SRHT and sampling theorems.

**D4. How a sketch family is carried.**
- (a) Each family is a law on matrices, `countSketch k n : Measure (Matrix k n ℝ)`, defined as
  the pushforward of its primitive randomness under a public constructor
  (`countSketchMatrix h σ`, `srhtMatrix H ξ s`, `samplingSketch p ι`), and theorems take
  `HasLaw S (countSketch k n) μ`, as for `gaussianMatrix` and `haarFrame`; proofs work on the
  primitive space and transport by the predicates' `HasLaw` lemmas.
- (b) Theorems take the primitives (`HasLaw h …`, `HasLaw σ …`) and conclude about the composite
  `fun ω => countSketchMatrix (h ω) (σ ω)` (the prototype).
*Recommendation (a):* the user holds a sketch, not a hash; one hypothesis per theorem; the same
form as the laws below. The constructor stays public for users who build the sketch from their
own randomness, with the bridge `hasLaw_countSketchMatrix`. The Gaussian and sub-Gaussian
sketches need no new law: `HasLaw G (gaussianMatrix k n) μ` and a scale in the statement.
*Rework:* every family theorem.

**D5. Dimensions, failure probabilities and sample sizes.**
- Sketch and subspace dimensions are index types (`S : Matrix k n 𝕜`, `[Fintype k]`), sizes
  entering as `Fintype.card k`; no `Fin`, no `[NeZero]`. Alternative: `ℕ` sizes with `Fin` (the
  prototype). *Recommendation:* index types, as the Matrix and Probability layers do.
- The primary theorem of each family is a tail in the family's natural parameter (Gaussian
  `2 exp (-t ^ 2 / 2)` at `a, b = (√k ∓ (√d + t)) ^ 2`; sampling `2 d exp (-ε ^ 2 k / (3 L))`;
  the moment route `B / ε ^ (2 q)`), concluding `HasSubspaceEmbedding` or the oblivious form with
  `δ` equal to that tail. The `δ` form with a size hypothesis is a corollary.
- Sample sizes are real-valued named definitions (`gaussianEmbeddingDim d ε δ : ℝ`,
  `samplingSize d L ε δ`, `srhtRowBound n d δ`, `countSketchRows d ε δ`), entering as
  `gaussianEmbeddingDim d ε δ ≤ Fintype.card k`; no ceilings or rounding in statements (the
  prototype's rounded sparse parameters are why its theorems cannot be applied to a sketch of a
  given size). By `CONTRIBUTING.md` §5.2 each is an `irreducible_def` with positivity,
  monotonicity and a one-sided explicit comparison, unless its body is the source's formula.
*Rework:* every family theorem and every consumer that inverts a size.

**D6. The size of the sparse block.** The inventory (§5, §9) finds the 95-file chain correct
but fragile: `Fin` indices, the `FiniteLaw` and `Frame` substrates duplicating `Measure` and
`HasOrthonormalCols`, sizes fixed by rounding, the source an unpublished manuscript, and no
consumer.
- (a) CountSketch proved (S7); SparseStack and OSNAP scaffolded (S8): laws defined, the hollow
  Gram identity and the trace-moment Markov step proved and shared, the general-parameter
  trace-moment bound `B(d, q, m, s)` one `sorry` per law in `NLAlibScaffold`, the headline in
  tail form proved from it, constants (`3 + √2`, `c_b < 1.582`) behind names.
- (b) As (a), plus a port of the prototype's comparison step (i.i.d. ternary model, convex order),
  leaving only the Fock and band bounds scaffolded.
- (c) The full port, rewritten against `Measure`.
*Recommendation (a)*, as the inventory recommends; (b) is attractive because S5's convex-order
lemma is the same argument, and may follow at the end of the round if the maintainer wants it.
(c) is about 25k lines for one hypothesis no consumer takes. *Rework:* low for (a) to (b) later,
since the scaffold statement is the interface either proof must meet.

### 2(b) Decisions the orchestrator takes

Stated here so that the maintainer can overrule them; otherwise binding on the stage notes.

**D7. Deterministic consequences live in Sketching.** S0 proves, from `IsSubspaceEmbedding S U a b`
alone: sketch-and-solve (for `U` the matrix `[A, y]`, a minimizer of `‖S (A x - y)‖` has residual
at most `√(b / a)` times the optimum, through `IsLeastSquaresSolution`); the condition number of
`A` preconditioned by the `R` factor of `S * A` is at most `√(b / a)`; AMM with `A = B = U`
implies the embedding. They are about the predicate, not an algorithm, and test that D1 is usable.

**D8. Leverage scores** are `leverageScore A i := re (rangeProjector A i i)`, any shape and rank,
with `∑ i, leverageScore A i = rank A` and, for `HasOrthonormalCols U`, the squared row norm. The
domination hypothesis of a sampling theorem is `∀ i, leverageScore U i ≤ L * p i`; leverage
sampling is `p = leverageScore U / d` with `L = d`, and `β`-approximate scores are `L = d / β`.
`ProjectorPair.lean` already has the diagonal of a projector; the note searches for overlap.

**D9. One sampling theorem.** For i.i.d. indices with law `samplingMeasure p` and the sketch
`(k p_i)^{-1/2} e_iᵀ` per row, the Gram matrix is a sum of `k` independent PSD atoms with mean
`Uᴴ * U` and bound `L / k`; `measureReal_specNorm_sum_sub_one_ge_le` gives the fixed-`U`
embedding with `δ = 2 d exp (-ε ^ 2 k / (3 L))`, and the one-sided Chernoff forms give the
lower and upper halves with their own exponents. Leverage sampling and the SRHT with replacement
are corollaries; uniform sampling is `p` uniform with `L` the card times the largest score.

**D10. Sampling without replacement** is the law `uniformOn {f | Function.Injective f}` on maps
from `k` to `n` (Mathlib's `uniformOn`, no new definition). The matrix tail comes from one
comparison, Hoeffding's (sampling without replacement is dominated by i.i.d. sampling in convex
order), proved once through a conditional barycenter, applied to
`fun A => re (trace (exp (θ • A)))`, then P5a's `…_of_integral_le` trace forms. It is general
probability: `NLAlib/Probability/ConvexOrder.lean`. The prototype's coupling is material.

**D11. SRHT over `𝕜`.** `H : Matrix n n 𝕜` is a hypothesis, `HasOrthonormalCols H` and
`‖H i j‖ ^ 2 = 1 / card n`, with `walshHadamard` (normalized, real) and `fourierMatrix`
(complex) as instances. The flattening step (row norms of `H D U` at most `L` outside `δ / 2`)
uses `HasSubgaussianMGF.sum_const_mul_of_iIndepFun` on real and imaginary parts, so its constant
is the one valid over both fields; a sharper real form is added only if a consumer needs it. One
tail theorem per sampling model (with and without replacement), combined with the flattening
event by one sections lemma (`measureReal` of a product, conditioned on the first factor). One
row bound `srhtRowBound`; the prototype's manuscript, capped-width and Walsh variants are not
ported (a dominated bound by §5.2 rule 6).

**D12. Constants.** Written in the statement where the proof reaches the source's: Dasgupta and
Gupta's exponent `k (ε ^ 2 / 4 - ε ^ 3 / 6)`, the Gaussian Gram tails, Tropp's Chernoff exponents,
CountSketch's `(d ^ 2 + d) / (m ε ^ 2)`. Named with an `irreducible_def` otherwise:
`subgaussianJLConstant` (from P1's centred square `(32 c², 4 c)` and Bernstein; the prototype
had `1 / (256 e²)`), the SRHT flattening constant, the sparse constants. Sub-Gaussian sample sizes
are written in R3's shape (`Probability-REPORT.md` §4, item 17).

**D13. The Haar sketch** is `(√(card n / card k)) • Qᴴ` for `HasLaw Q (haarFrame n k) μ` and
`card k ≤ card n`. JL: `Qᴴ * x` for a unit `x` has the law of the first `k` coordinates of
`uniformSphereVector n` (left invariance and the square Haar frame), so the tail is Dasgupta and
Gupta's Lemma 2.2 from the χ² MGFs already built. Embedding: `Uᴴ * Q * Qᴴ * U` equals
`(Gᴴ * U)ᴴ * (Gᴴ * G)⁻¹ * (Gᴴ * U)` for the Gaussian `G` with `Q = polarFactor G`, bounded by four
R3 tails with a union bound (no independence needed). Exact isotropy `E [Sᴴ * S] = 1` and
`specNorm S = √(card n / card k)` almost surely are stated, since a Gaussian has neither.

**D14. Names.** Predicates as in D1, D2; family laws `gaussianMatrix` (existing), `haarFrame`
(existing), `rademacherMatrix k n` (an `abbrev` for the product of `rademacherMeasure`, if no
existing spelling covers it), `countSketch k n`, `srht H k`, `sparseStack …`, `osnap …`. Tails
follow the tail-prefix rule (`CONTRIBUTING.md` §4): `HasJLMoment.measure_…` inside a namespace,
`measureReal_…` at root. Family theorems are named by the predicate and the law,
`isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix`, never by the source.

**D15. Layout.** `Sketching/` with `Properties/` (S0, S1), `Gaussian/` (S2, S3), `Sampling/`
(S4, S5), `Structured/` (S6), `Sparse/` (S7, S8); files by topic, fixed in each stage note.

**D16. Bibliography.** The SRHT paper and the Freedman paper are both Tropp 2011: the SRHT key is
`Tropp2011a`, `Tropp2011` keeps its meaning. Docstrings citing the prototype's unpublished
manuscripts (`sh:sparse`, `sh:exact-s`, `sh:count-second`) cite published sources (§7) or none.

## 3. Conventions the stages follow

Subject to §2; inherited from `PORT_PROBABILITY.md` §2 D2, D3, D5 and §3.

- Tails in failure form, non-strict events, `μ.real`; never `1 - δ ≤ μ.real {good}`. Every
  expectation upper bound beside its `integrable_…` companion. `[IsProbabilityMeasure μ]` only
  where `HasLaw` with a probability law does not imply it.
- Euclidean norms `‖WithLp.toLp 2 x‖`; matrix norms by the Matrix layer's names (`specNorm`,
  `frobNorm`); matrix integrals under `open scoped Matrix.Norms.L2Operator` only (§5.1).
- A fixed-`U` theorem assumes `HasOrthonormalCols U` only if its proof needs it; general `U`
  is one corollary by `of_range_le`.
- Halves with different constants (Chernoff's exponents) are two theorems, joined by a union bound.

## 4. Stages

In dependency order; each gets a design note `docs/design/Sketching-<Stage>.md`. Consumers are
the statements of §5; material is prototype paths under `Sketching/` unless marked.

- **S0 The embedding predicate.** `IsSubspaceEmbedding` (D1) and its API; the measurability of
  its event; the deterministic consequences of D7. Files: `Properties/SubspaceEmbedding.lean`,
  `Properties/LeastSquares.lean`. Consumers: every later stage; sketch-and-solve,
  sketch-and-precondition, generalized Nyström. Material: `Properties/SubspaceEmbedding/` (5
  files, 320 lines; the `iff` forms are reusable, the `Fin` transport is not).
- **S1 Probabilistic predicates.** `HasSubspaceEmbedding`, `IsObliviousSubspaceEmbedding`,
  `HasJLProperty`, `HasJLMoment`, `HasGramTraceMoment` (D2), each with its `HasLaw` lemma; JL
  moment to JL property (Markov) and to the JL lemma for `N` points; JL moment to AMM; the trace
  moment to the embedding (Markov on `tr E ^ (2 q)`); composition of two independent sketches
  (`δ₁ + δ₂`); the oblivious transfer to an independent random `U`. Files: `Properties/Oblivious`,
  `Properties/JohnsonLindenstrauss`, `Properties/MatrixMultiplication`, `Properties/TraceMoment`.
  Consumers: S2 to S8; range finding with a sketch independent of the test matrix. Material:
  `Properties/JL/JL.lean`, `Properties/ApproxMatrixMultiplication/` (the `∫⁻` statement restated
  in Bochner form), `Sparse/MomentMethod/GramTail.lean` (the Markov step).
- **S2 Gaussian and Haar sketches.** Gaussian: the oblivious embedding from R3's Gram sandwich in
  natural parameters, the JL tail in Dasgupta–Gupta form from the χ² MGF, the JL moment from the
  tail (`integral_le_of_measureReal_ge_le`), sample-size corollaries (`gaussianEmbeddingDim`).
  Haar: D13. Files: `Gaussian/Gaussian.lean`, `Gaussian/Haar.lean`. Consumers: LowRank's test
  matrices, sketch-and-solve. Material: `Gaussian/GaussianEmbedding.lean`, `Properties/JL/JL.lean`;
  `RandomMatrix/{Gaussian,Haar}` of this library. **Maintainer checkpoint after S2.**
- **S3 Sub-Gaussian sketches.** Independent isotropic sub-Gaussian rows: the JL tail by Bernstein
  for centred squares (P1's `hasSubexponentialMGF_sq_sub_integral`,
  `measure_sum_ge_le_of_iIndepFun`), which closes the Probability round's open entry; the JL
  moment; the oblivious embedding from R3's rows theorem (rows of `X * U` stay isotropic and
  sub-Gaussian by `IsIsotropic.mulVec`, `IsSubgaussianVector.mulVec` when `HasOrthonormalCols U`);
  the Rademacher sketch as the instance. File: `Gaussian/SubGaussian.lean`. Consumers: users with
  sign sketches. Material: the prototype's `RandomMatrix/SubGaussian/` JL statements (the two
  ledger entries), `Properties/JL`.
- **S4 Row sampling.** The sampling sketch over `𝕜`; leverage scores (D8); D9's theorem and its
  corollaries; column-row sampling for AMM with the exact variance (Drineas, Kannan and
  Mahoney) and its domination form. Files: `Sampling/Leverage.lean`, `Sampling/RowSampling.lean`,
  `Sampling/MatrixMultiplication.lean`. Consumers: sketch-and-solve with leverage sampling,
  Nyström with column sampling, S6. Material: `Sampling/{Leverage,LeverageSampling,
  SamplingMultiplication,SamplingMultiplicationBounds}.lean` (846 lines; the prototype's form is
  over `ℂ`, here `𝕜`).
- **S5 Sampling without replacement.** D10: the uniform injection law, Hoeffding's convex-order
  comparison (in `Probability/ConvexOrder.lean`), the matrix Chernoff tails without replacement,
  and the row-sampling theorem of S4 for a uniform subset. Files: `Probability/ConvexOrder.lean`,
  `Sampling/WithoutReplacement.lean`. Consumers: S6, S8 (if D6 (b)). Material:
  `Sampling/{SamplingWithoutReplacement,SamplingWithoutReplacementTails}.lean` and the seven
  `Uniform*` files (about 1140 lines; `uniformOn` should absorb the counting and marginal files).
- **S6 SRHT.** D11: the sketch `√(n / k) • Pᵀ * H * diagonal ξ`, flattening, the two sampling
  models through S4 and S5, the oblivious embedding, `srhtRowBound`, the Walsh and Fourier
  instances. Files: `Structured/Flattening.lean`, `Structured/SRHT.lean`. Consumers: HMT §11
  range finding, sketch-and-precondition (Blendenpik's use). Material: `Structured/` (5 files,
  1001 lines; one of the two row bounds is ported, the other is dominated).
- **S7 CountSketch.** The law (uniform hash times signs), the hollow Gram identity (public: S8
  reuses it), the exact mean of `frobNorm G ^ 2` for the Gram error `G`, `HasGramTraceMoment` at
  `q = 1`, the oblivious embedding with `(d ^ 2 + d) / (m ε ^ 2)`, the JL moment at `p = 2` and
  hence AMM. File: `Sparse/CountSketch.lean`. Material: `Sparse/CountSketch*.lean` (4 files,
  425 lines, already in the target shape) and the prototype's
  `integral_quadForm_sq_rademacherVector_of_diag_zero` if `QuadraticForm/Moments.lean` lacks it.
- **S8 Sparse embeddings.** Per D6 (a): the SparseStack and OSNAP laws as measures on matrices
  (the `FiniteLaw` substrate not ported), the trace-moment bound in general parameters
  `(s, b, q)` as one scaffold theorem per law, the oblivious embedding in tail form proved from it
  through S1, the named parameters as real-valued definitions with the prototype's values as
  comparisons. Files: `Sparse/SparseStack.lean`, `Sparse/OSNAP.lean`, scaffolds under
  `NLAlibScaffold/Sketching/Sparse/`. Material: `Sparse/{SparseStack,SparseStackLaw,
  UniformSparse,SparseLaws,SparseEmbedding}.lean`, `Sparse/MomentMethod/{GramError,GramTail,
  MomentParameters,ParameterConstants}.lean`, and the internal general-parameter tail
  `SparseSketch.concrete_band_bound_le_beta` (the inventory, §5) as the scaffold's statement.

Expected size, from the prototype's line counts after removing twins: S0 and S1 about 1200 lines
together, S2 600, S3 400, S4 900, S5 900, S6 700, S7 450, S8 600 plus scaffolds.

## 5. What the following rounds need from this one

From the inventory's §3, §7 and §10, and the atlas candidates:

- **Solvers** (sketch-and-solve, sketch-and-precondition, Blendenpik and LSRN, sketch-and-project):
  `HasSubspaceEmbedding S U a b δ μ` for the fixed `U = [A, y]` or `U = A`, and S0's deterministic
  residual and condition-number bounds, so that a solver theorem is S0 composed with any family's
  tail. Sketch-and-project keeps its own hypothesis (`λ • 1 ≤ E [(Sᴴ A)⁺ (Sᴴ A)]`), which this
  round does not touch.
- **LowRank**: the oblivious predicate and its transfer to a random subspace independent of the
  sketch (generalized Nyström sketches twice); SRHT and sparse test matrices for the range finder
  through the embedding (HMT §11), beside the Gaussian and Haar block moments already built; the
  Haar sketch's exact isotropy.
- **Estimation**: Hutch++ and XTrace error bounds through AMM and the JL moment; isotropy itself
  is already `IsIsotropic`.
- **Stability of the interfaces**: the predicates of D1 and D2 are the hypotheses of every later
  sketching statement; a later family (complex Gaussian, LESS, fast JL) concludes them without a
  new predicate, and a later improvement of a family's tail changes a body or adds a theorem
  (§5.2 rules 4 and 6), never a predicate.

## 6. Not ported

The `_of_hasLaw` and finite-index transport twins; the success-form statements and the
`.toReal` and `ENNReal.ofReal` copies; the SRHT manuscript, capped-width and Walsh duplicates;
the `MainConclusions` bundles; `Frame` and `FiniteLaw`; under D6 (a), `Bands/`, `FockModel/`,
`IIDComparison/` and the rounding files of `MomentMethod/` (ledgered with that reason); the dead
`Bands/Light/ZeroBlock.lean`; real and complex twins of one result.

## 7. Literature to check

Locators marked "to confirm" are from the prototype or from memory; check them before citing.

- Woodruff 2014 (`Woodruff2014`, in the bibliography), chapter 2: §2.1 subspace embeddings
  (Gaussian and CountSketch), §2.2 matrix multiplication and the JL moment property, §2.4
  leverage-score sampling, §2.5 regression; theorem numbers to confirm.
- Martinsson and Tropp 2020 (`MartinssonTropp2020`): §8 (embeddings and oblivious subspace
  embeddings) and §9 (Gaussian, orthonormal, sparse, SRTT, sampling; §9.6 leverage scores per the
  prototype); §10 for sketch-and-solve and preconditioning; subsection numbers to confirm.
- Dasgupta and Gupta, "An elementary proof of a theorem of Johnson and Lindenstrauss", Random
  Structures and Algorithms 22 (2003): Lemma 2.2 and Theorem 2.1 (the prototype cites "Lem 2",
  "Thm 2").
- Achlioptas, "Database-friendly random projections", J. Comput. System Sci. 66 (2003):
  Theorem 1.1 (sign sketches).
- Vershynin 2018 (`Vershynin2018`): §5.3 (JL via concentration of the norm), §2.8 (Bernstein),
  §4.6 (rows, already cited).
- Kane and Nelson, "Sparser Johnson–Lindenstrauss transforms", J. ACM 61 (2014): the JL moment
  property and its matrix-multiplication consequence (Theorem 6.2, to confirm).
- Sarlós, "Improved approximation algorithms for large matrices via random projections",
  FOCS 2006: Lemma 6 (AMM from JL), as cited by the prototype.
- Drineas, Kannan and Mahoney, "Fast Monte Carlo algorithms for matrices I", SIAM J. Comput. 36
  (2006): Lemma 4 and Theorem 1 (column-row sampling), to confirm.
- Drineas, Mahoney, Muthukrishnan and Woodruff, "Fast approximation of matrix coherence and
  statistical leverage", JMLR 13 (2012): §1 and §2 (definition of leverage scores, as cited by
  the prototype).
- Tropp 2015 (`Tropp2015`): the matrix Chernoff chapter and its row-sampling example; locator to
  confirm (the round report lists Tropp 2015's chapter labels as unverified).
- Tropp, "Improved analysis of the subsampled randomized Hadamard transform", Adv. Adapt. Data
  Anal. 3 (2011): the main theorem, the flattening lemma and the sampling lemma (numbers to
  confirm).
- Ailon and Chazelle, "The fast Johnson–Lindenstrauss transform and approximate nearest
  neighbors", SIAM J. Comput. 39 (2009): provenance of the randomized Hadamard step.
- Halko, Martinsson and Tropp 2011 (`HalkoMartinssonTropp2011`): §4.6 and §11 (SRFT test
  matrices).
- Hoeffding, "Probability inequalities for sums of bounded random variables", JASA 58 (1963):
  Theorem 4 (sampling without replacement), cited 45 times in the prototype.
- Gross and Nesme, "Note on sampling without replacing from a finite collection of matrices",
  arXiv:1001.2738 (2010): the matrix form of Hoeffding's comparison.
- Clarkson and Woodruff, "Low-rank approximation and regression in input sparsity time",
  J. ACM 63 (2017; STOC 2013): CountSketch as a subspace embedding.
- Nelson and Nguyen, "OSNAP: faster numerical linear algebra algorithms via sparser subspace
  embeddings", FOCS 2013: the `s = 1` bound `(d ^ 2 + d) / (δ ε ^ 2)` and the OSNAP law (theorem
  numbers to confirm).
- Cohen, "Nearly tight oblivious subspace embeddings by trace inequalities", SODA 2016: the
  trace-moment route for OSNAP, the published form of S1's `HasGramTraceMoment` step.
- Chenakkod, Dereziński, Dong and Rudelson, "Optimal embedding dimension for sparse subspace
  embeddings", STOC 2024: candidate published source of the SparseStack parameters
  `m ∼ (d + log (d / δ)) / ε ^ 2`, `s ∼ log (d / δ) / ε`; the maintainer to confirm whether it is
  the prototype's manuscript `sh:sparse` or which paper is.
- For S0: Rokhlin and Tygert, "A fast randomized algorithm for overdetermined linear
  least-squares regression", PNAS 105 (2008), and Avron, Maymounkov and Toledo, "Blendenpik",
  SIAM J. Sci. Comput. 32 (2010): the preconditioning consequence of an embedding.

## 8. Done

The round is done when every stage is implemented (S8 per D6), `NLAlib` and `NLAlibScaffold`
build with no warnings, `scripts/Audit.lean` and `scripts/Lint.lean` are clean, `check_refs.py`
passes, the ledger accounts for the prototype's `Sketching/` and the two carried-over JL
entries, `docs/port/status.md` lists what is in `NLAlibScaffold` with a difficulty estimate each,
and `docs/design/Sketching-REPORT.md` reports as `Probability-REPORT.md` did, with its §4 listing
the orchestrator's decisions and marking any of the §2(a) kind.
