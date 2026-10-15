# Port brief: the Sketching round

For the orchestrating agent building `NLAlib/Sketching/`. Read `CONTRIBUTING.md` in full first
(above all §5.1 on `L2Operator`, §5.2 "Numerical bounds", §5.4, §7 and the skeleton rule), then
`docs/design/Probability-REPORT.md` (what the layers below export, their constants, the
orchestrator's decisions and the open work), `docs/design/Mathlib-deviations.md`, and the survey
this brief is built on, `docs/port/inventory-sketching.md` (cited below as "the inventory").
Status: **draft, 2026-10-14, revised the same day after the maintainer's answers.** D1 to D5 are
approved as recommended. D6 is revised: the sparse embeddings are deferred, and §4a records what
they need. The oblivious subspace injection (OSI) is added to D1 and D2 by the orchestrator; it is
not costly to reverse. The prototype's unpublished manuscripts are dropped as sources (D16).
Part (b) is taken by the orchestrator and open to correction.

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
  theorems; sampling without replacement as far as the SRHT needs it; the oblivious subspace
  injection of Camaño, Epperly, Meyer and Tropp 2025 (cited "CEMT" below) as the one-sided
  companion of the embedding (D1, D2). The Probability round left two entries for this
  one: sub-Gaussian Johnson–Lindenstrauss and the Haar JL in Dasgupta–Gupta form
  (`Probability-REPORT.md` §6.1 item 5, §6.3).
- **Not in scope**: the randomized algorithms (later rounds), except the deterministic
  consequences of an embedding (S0); complex Gaussian, Haar and sign laws (parallel definitions
  later, `Probability-REPORT.md` §4 item 11); fast JL with a sparse projection, Kac walks, tensor
  sketches, LESS embeddings, SparseRTT and Khatri–Rao sketches, lower bounds; approximating
  leverage scores; SparseStack, OSNAP and the prototype's sparse machinery (D6; §4a records what
  they need); finite precision.

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
  domination hypothesis must force the row of `U` to vanish there, and the sketch is then not
  isotropic), `U` without full column rank (the predicate is relative to `Uᴴ * U`), parameters
  `a ≤ 0` (an injection then holds trivially) or `b < a`.
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
  their first two families, before the remaining five stages build on them.
- **Deviations from Mathlib** get an entry in `Mathlib-deviations.md` in their commit. None is
  expected: `HasLaw`, `Measure.pi`, `uniformOn` and the Loewner order are used as Mathlib has them.
- **Ledger.** The ledger accounts for the 1873 public declarations of the prototype's
  `Sketching/` (the SparseStack and OSNAP block as deferred, with D6 and §4a as the reason), and
  for the two sub-Gaussian JL entries carried over from the Probability round.

## 2. Decisions

### 2(a) Decisions for the maintainer

Each with options, a recommendation, the reason and the rework a change after the round would
cost. They fix what every later layer takes as a hypothesis. The maintainer answered on
2026-10-14; each decision records the answer.

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
`a = 0`. The event in CEMT's Definition 1.1 is (b) with `a = α`, `b = β`, which they call
injectivity and dilation.
*Rework:* every embedding statement of this round and every consumer.
**Maintainer, 2026-10-14: approved as recommended, (b).**

*Addition by the orchestrator, 2026-10-14; not costly to reverse, so not a maintainer decision:
the lower half gets a name.* It is `IsSubspaceInjection S U a : Prop := a • (Uᴴ * U) ≤
(S * U)ᴴ * (S * U)`, a plain `def` that unfolds to the Loewner half, so no bridge is needed. The
field `lower` of `IsSubspaceEmbedding` has this type; `upper` is unchanged. The draft said a
one-sided lower statement "stays the raw Loewner half"; that is withdrawn, because D2's OSI needs
a named deterministic event. Its API is the lower half of the list above, proved once and used by
`IsSubspaceEmbedding`:
- the norm form;
- the Gram form `a • 1 ≤ (S * U)ᴴ * (S * U)` for orthonormal `U`;
- the singular-value form;
- monotonicity, `of_range_le` and `U * C`;
- scaling, and composition with an embedding (lower parameters multiply);
- measurability of the event;
- `IsSubspaceInjection.injective`: for `0 < a`, `S` is injective on `range U`. Sketch-and-solve
  and the range finder use this fact.

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
  predicate is added if a consumer takes it as a hypothesis. Woodruff 2014, Theorem 13, has the
  factor `3 ε` where the event above has `ε`. The stage note writes the constant its proof
  reaches; by polarization that is `ε` over ℝ at `p = 2`. If the constant is not the source's, it
  is named per D12.
- `HasGramTraceMoment S U q B μ`: for `HasOrthonormalCols U`, the error
  `E = (S * U)ᴴ * (S * U) - 1` has `re (trace (E ^ (2 * q)))` integrable with integral at most
  `B`. One lemma gives `HasSubspaceEmbedding S U (1 - ε) (1 + ε) (B / ε ^ (2 * q)) μ` from
  `specNorm E ^ (2 * q) ≤ re (trace (E ^ (2 * q)))` for Hermitian `E`. That bound exists:
  `specNorm_pow_le_re_trace_pow` (`Matrix/Norms/SchattenPowers.lean`), with `(Eᴴ * E) ^ q =
  E ^ (2 * q)`. CountSketch is the only instance this round, at `q = 1`. The deferred sparse
  laws (§4a) need general `q`, which is why `q` stays a parameter. The oblivious form quantifies
  over `U` outside, as in (α).
*Rework:* every probabilistic sketching statement, and every consumer hypothesis.
**Maintainer, 2026-10-14: approved as recommended: (i), (α), (A).**

**OSI.** *Addition by the orchestrator, 2026-10-14; not costly to reverse, so not a maintainer
decision.*

*What CEMT prove with it.* CEMT (arXiv:2508.21189) call a random matrix an `(r, α)`-OSI when two
things hold (Definition 1.2; Proposition 1.15 gives the Gram form):
- it is isotropic, `E ‖Ωᴴ x‖² = ‖x‖²` for every `x`;
- for each fixed `r`-dimensional subspace, the lower half of the embedding holds with
  probability at least `19/20`.

No dilation bound is assumed. This is enough, with error a constant times `1/α` of the optimum,
for:
- the randomized SVD (Theorem 2.2);
- Nyström (Corollary 2.5);
- sketch-and-solve least squares, with the injection needed only on `range A`, not on `[A, B]`
  (Theorem 2.7, through the error formula of Lemma 2.6);
- generalized Nyström with two OSIs (Corollary 2.8).

All four rest on Lemma 2.1, "OSIs respect orthogonality": for `Qᴴ Q⊥ = 0`,
`‖B (Q⊥ᴴ Ω) (Qᴴ Ω)†‖_F² ≤ (C/α) ‖B‖_F²` with probability `9/10`. The proof is `σ_min² ≥ α` plus
Markov on the numerator, whose mean is `‖B‖_F²` by isotropy.

*What it buys.* The dilation is the half that sparse sketches control badly:
- SparseStack is an OSI at `k = O(r)`, `ζ = O(log r)` (Imported Theorem 1.8, from Tropp 2025,
  Remark 6.5; proof in Appendix B). The best OSE results need `k = O(r log r)` (Cohen 2016) or
  `ζ = O(log³ r)` (Chenakkod et al.); see Table 3.
- SparseRTT (Theorem 4.2) and Khatri–Rao (Theorems 5.1, 5.2) are further OSI families, analysed
  through the injection alone (§1.5).

With the predicate, later rounds get weaker hypotheses, and the deferred sparse families (§4a)
have an interface waiting for them.

*Shape.* In this library's orientation `S = Ωᴴ : Matrix k n 𝕜` acts on the left.
- `IsIsotropicSketch S μ`: a structure with two fields, as `IsIsotropic` is for vectors:
  `memLp : ∀ i j, MemLp (fun ω => S ω i j) 2 μ`, and
  `integral_conjTranspose_mul_self : ∫ ω, (S ω)ᴴ * S ω ∂μ = 1` (the integral under the
  `L2Operator` scope, `CONTRIBUTING.md` §5.1). API:
  - the `iff` with CEMT's (1.2), `∀ x, ∫ ‖S ω *ᵥ x‖² = ‖x‖²` (polarization);
  - `E ‖S * M‖_F² = ‖M‖_F²`;
  - `of_rows`: `(√card k)⁻¹ • X` is isotropic when each row of `X` is `IsIsotropic`;
  - the `HasLaw` lemma;
  - composition with an independent isotropic sketch.
- `HasSubspaceInjection S U a δ μ := μ.real {ω | ¬ IsSubspaceInjection (S ω) U a} ≤ δ` for a
  fixed `U`. It follows from `HasSubspaceEmbedding S U a b δ μ`, whose failure event is larger.
- `IsObliviousSubspaceInjection S d a δ μ`: a structure with two fields,
  `isotropic : IsIsotropicSketch S μ` and
  `injection : ∀ U : Matrix n n 𝕜, U.rank ≤ d → HasSubspaceInjection S U a δ μ` (the quantifier
  of (α)). An `IsObliviousSubspaceEmbedding S d a b δ μ` together with `IsIsotropicSketch S μ`
  gives it (`.toInjection`); the converse fails. CEMT's `19/20` becomes `δ`. Their
  `α ∈ (0, 1]` becomes any real `a`; the predicate is vacuous for `a ≤ 0`. The oblivious
  transfer to an independent random `U` is proved for this predicate too, because generalized
  Nyström applies it to `range (A Ω)`.
- Consequences proved in S1, which test the predicate as S0 tests D1:
  - Lemma 2.1 in tail form, `μ.real {ω | t * frobNorm B ^ 2 / a ≤ frobNorm (B * (S ω * Q⊥)ᴴ *
    pinv ((S ω * Q)ᴴ)) ^ 2} ≤ δ + 1 / t`, from S0's deterministic half and Markov. At `B = 0` the
    non-strict event is everything; the note fixes the hypothesis or the event.
  - Sketch-and-solve with an OSI, `‖A x̃ - y‖² ≤ (1 + t / a) ‖r‖²` outside `δ + 1 / t`, from
    S0's error formula.

*Families with an OSI theorem this round.* Every isotropic family gets one:
- Gaussian `(√k)⁻¹ • G`, Haar, and the sampling-based SRHT, from their lower halves alone. These
  have better constants than the two-sided forms: the Gaussian tail is `exp (-t ^ 2 / 2)`
  instead of `2 exp (-t ^ 2 / 2)`, and matrix Chernoff's lower tail is
  `d exp (-ε ^ 2 k / (2 L))` instead of `2 d exp (-ε ^ 2 k / (3 L))` (Tropp 2015, Theorem 5.1.1,
  (5.1.5), and its weakening after (5.1.8)).
- Rademacher and sub-Gaussian rows, and CountSketch, as corollaries of their OSE.
- Row sampling gets `HasSubspaceInjection` for its fixed `U`, by the lower Chernoff tail. It is
  isotropic only when every `p i > 0`.

The families whose OSI parameters beat their OSE (SparseStack, SparseIID, SparseRTT, Khatri–Rao)
are not in this round.

*Consumers* (the inventory's §3):
- LowRank:
  - the range finder R1, R2 through HMT Theorem 9.1, which is already distribution-free (CEMT
    Theorem 2.2);
  - HMT §11, whose Theorem 11.2 uses only the lower half (CEMT §1.4);
  - Nyström R5 (Corollary 2.5);
  - generalized Nyström R6 (Corollary 2.8; two independent OSIs and the transfer).
- Solvers: sketch-and-solve (Theorem 2.7). It gives a constant factor only, so the `√(b / a)`
  bound from the embedding (D7) stays.

Not served:
- sketch-and-precondition and Blendenpik, which bound a condition number and so need both
  halves;
- sketch-and-project, which keeps its own hypothesis;
- Estimation: CEMT do not treat trace estimation, and Hutch++ and XTrace keep AMM and the JL
  moment.

*Rework if reversed:* the OSI corollaries and S1's two consequences; downstream statements
restated with the embedding.

**D3. Which families are first-class this round, and over which field.** "First-class" means: a
named law, theorems concluding the D1 and D2 predicates in tail form, and named sample sizes.

| family | law | field | concludes | stage |
|---|---|---|---|---|
| Gaussian | `gaussianMatrix k n`, scaled by `(√k)⁻¹` | ℝ | OSE, OSI, JL, JL moment | S2 |
| Haar rows `√(n/k) Qᴴ` | `haarFrame n k` | ℝ | OSE, OSI, JL, JL moment, exact isotropy | S2 |
| independent sub-Gaussian rows, Rademacher | `iIndepFun`, `IsSubgaussianVector`, `IsIsotropic` per row; `rademacherMatrix` an instance | ℝ | OSE, OSI, JL, JL moment | S3 |
| row sampling (leverage, importance) | `Measure.pi fun _ => samplingMeasure p` on indices | `𝕜` | fixed-`U` embedding and injection, AMM | S4 |
| SRHT and SRFT | signs and a uniform subset (or i.i.d. indices) on a hypothesis `H` | `𝕜` | OSE, OSI | S6 |
| CountSketch | uniform hash and signs | ℝ | OSE through trace moment `q = 1`, OSI, JL moment `p = 2` | S7 |

Options: (a) all six (the draft's seven, less the sparse row per the revised D6); (b) drop the
Haar sketch and the SRFT; (c) add fast JL and LESS. *Recommendation (a).* Orthonormal sketches
are first-class by the maintainer's standing instruction (`status.md`, Probability inputs
item 4) and are cheap given R5; the SRHT over `𝕜` with `H` a hypothesis covers Walsh (real) and
Fourier (complex) with one proof. Real laws (Gaussian, Haar, signs, hashes) conclude the `𝕜`
predicates at `𝕜 = ℝ`; their complex analogues, later, conclude the same predicates without a
rename. *Rework:* low for adding a family later; moderate for the field of the SRHT and sampling
theorems.
**Maintainer, 2026-10-14: approved as recommended, (a); SparseStack and OSNAP leave the table
under the revised D6.**
*Amended 2026-10-15* (`docs/design/Sketching-S7.md` §8 item 2): CountSketch's field is `𝕜`, real signs coerced, as S6's `srhtMatrix`.

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
**Maintainer, 2026-10-14: approved as recommended, (a).**

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
**Maintainer, 2026-10-14: approved as recommended.**

**D6. The size of the sparse block.** The inventory (§5, §9) finds the 95-file chain correct
but fragile: `Fin` indices, the `FiniteLaw` and `Frame` substrates duplicating `Measure` and
`HasOrthonormalCols`, sizes fixed by rounding, no published source for its general-parameter
bound, and no consumer. The draft offered three options: (a) CountSketch proved and SparseStack
and OSNAP scaffolded; (b) (a) plus the comparison step; (c) the full port. It recommended (a).
**Maintainer, 2026-10-14: revised.** The simple families go ahead, with CountSketch proved in
full (S7). SparseStack and OSNAP are held off this round, with no scaffold: the infrastructure
they need is not there yet, and may need changes in lower-level parts of the package first. §4a
says what is missing, so that a later round can start from it. The prototype's sparse block is
ledgered as deferred, with §4a as the reason. *Rework:* none this round. The later round adds
families that conclude this round's predicates (`HasGramTraceMoment` at general `q`, the OSE, the
OSI) and needs no new predicate.

### 2(b) Decisions the orchestrator takes

Stated here so that the maintainer can overrule them; otherwise binding on the stage notes.

**D7. Deterministic consequences live in Sketching.** S0 proves, from `IsSubspaceEmbedding S U a b`
alone: sketch-and-solve (for `U` the matrix `[A, y]`, a minimizer of `‖S (A x - y)‖` has residual
at most `√(b / a)` times the optimum, through `IsLeastSquaresSolution`); the condition number of
`A` preconditioned by the `R` factor of `S * A` is at most `√(b / a)`; AMM with `A = B = U`
implies the embedding. From `IsSubspaceInjection S A a` alone, with `0 < a`, it proves two more:
- the error formula of sketched least squares (CEMT Lemma 2.6): every sketched minimizer `x̃`
  satisfies `‖A x̃ - y‖² ≤ ‖r‖² + ‖S *ᵥ r‖² / a`, where `r = (1 - rangeProjector A) *ᵥ y` is the
  optimal residual;
- the deterministic half of CEMT Lemma 2.1: `frobNorm (B * (S * Q⊥)ᴴ * pinv ((S * Q)ᴴ)) ^ 2 ≤
  frobNorm (B * (S * Q⊥)ᴴ) ^ 2 / a` for orthonormal `Q`.
S1 turns both into tails under isotropy (D2, OSI). These consequences are about the predicates,
not an algorithm, and test that D1 is usable.

**D8. Leverage scores** are `leverageScore A i := re (rangeProjector A i i)`, any shape and rank,
with `∑ i, leverageScore A i = rank A` and, for `HasOrthonormalCols U`, the squared row norm. The
domination hypothesis of a sampling theorem is `∀ i, leverageScore U i ≤ L * p i`; leverage
sampling is `p = leverageScore U / d` with `L = d`, and `β`-approximate scores are `L = d / β`.
`ProjectorPair.lean` already has the diagonal of a projector; the note searches for overlap.

**D9. One sampling theorem.** For i.i.d. indices with law `samplingMeasure p` and the sketch
`(k p_i)^{-1/2} e_iᵀ` per row, the Gram matrix is a sum of `k` independent PSD atoms with mean
`Uᴴ * U` and bound `L / k`; `measureReal_specNorm_sum_sub_one_ge_le` gives the fixed-`U`
embedding with `δ = 2 d exp (-ε ^ 2 k / (3 L))`, and the one-sided Chernoff forms give the
lower and upper halves with their own exponents (Tropp 2015, Theorem 5.1.1: (5.1.5) lower,
(5.1.6) upper). The lower half is the fixed-`U` injection of D2. Leverage sampling and the SRHT
with replacement are corollaries; uniform sampling is `p` uniform with `L` the card times the
largest score.

**D10. Sampling without replacement** is the law `uniformOn {f | Function.Injective f}` on maps
from `k` to `n` (Mathlib's `uniformOn`, no new definition). The matrix tail comes from one
comparison, Hoeffding's (sampling without replacement is dominated by i.i.d. sampling in convex
order), proved once through a conditional barycenter, applied to
`fun A => re (trace (exp (θ • A)))`, then P5a's `…_of_integral_le` trace forms. It is general
probability: `NLAlib/Probability/ConvexOrder.lean`. The prototype's coupling is material. The
comparison is stated for a Markov kernel with a barycenter identity, values in a
finite-dimensional real vector space and any convex `f`, not only for `re tr exp`. This costs
nothing now, and the deferred sparse comparison (§4a, Route 1, item 1) needs it.

**D11. SRHT over `𝕜`.** `H : Matrix n n 𝕜` is a hypothesis, `HasOrthonormalCols H` and
`‖H i j‖ ^ 2 = 1 / card n`, with `walshHadamard` (normalized, real) and `fourierMatrix`
(complex) as instances. The flattening step (row norms of `H D U` at most `L` outside `δ / 2`)
uses `HasSubgaussianMGF.sum_const_mul_of_iIndepFun` on real and imaginary parts, so its constant
is the one valid over both fields; a sharper real form is added only if a consumer needs it. One
tail theorem per sampling model (with and without replacement), combined with the flattening
event by one sections lemma (`measureReal` of a product, conditioned on the first factor). One
row bound `srhtRowBound`; the prototype's second row bound and its capped-width and Walsh
variants are not ported (a dominated bound by §5.2 rule 6).

**D12. Constants.** Written in the statement where the proof reaches the source's: Dasgupta and
Gupta's exponent `k (ε ^ 2 / 4 - ε ^ 3 / 6)`, the Gaussian Gram tails, Tropp's Chernoff exponents,
CountSketch's `(d ^ 2 + d) / (m ε ^ 2)` (the proof's; attributed to Nelson and Nguyen, unconfirmed,
§7). Named with an `irreducible_def` otherwise: `subgaussianJLConstant` (from P1's centred
square `(32 c², 4 c)` and Bernstein; the prototype had `1 / (256 e²)`) and the SRHT flattening
constant. *Amended 2026-10-15* (`docs/design/Sketching-S3.md` §7 Q1, §8): sub-Gaussian
embeddings and their sample sizes go through JL plus a net (`subgaussianJLDim`,
`subgaussianEmbeddingDim`); R3's rows route (`Probability-REPORT.md` §4, item 17) is dominated
in every regime and dropped (CONTRIBUTING §5.2, rule 6). Sign sketches carry Dasgupta and Gupta's
exponent (Achlioptas) and S2's `jlDim`.

**D13. The Haar sketch** is `(√(card n / card k)) • Qᴴ` for `HasLaw Q (haarFrame n k) μ` and
`card k ≤ card n`. JL: `Qᴴ * x` for a unit `x` has the law of the first `k` coordinates of
`uniformSphereVector n` (left invariance and the square Haar frame), so the tail is Dasgupta and
Gupta's Lemma 2.2 from the χ² MGFs already built (Vershynin, Lemma 5.3.2, is the same fact for
a random projection). Embedding: `Uᴴ * Q * Qᴴ * U` equals
`(Gᴴ * U)ᴴ * (Gᴴ * G)⁻¹ * (Gᴴ * U)` for the Gaussian `G` with `Q = polarFactor G`, bounded by four
R3 tails with a union bound (no independence needed); the injection needs two of them. Exact
isotropy (`IsIsotropicSketch`, D2) and
`specNorm S = √(card n / card k)` almost surely are stated, since a Gaussian has neither.

**D14. Names.** Predicates as in D1, D2; family laws `gaussianMatrix` (existing), `haarFrame`
(existing), `rademacherMatrix k n` (an `abbrev` for the product of `rademacherMeasure`, if no
existing spelling covers it), `countSketch k n`, `srht H k`. Tails
follow the tail-prefix rule (`CONTRIBUTING.md` §4): `HasJLMoment.measure_…` inside a namespace,
`measureReal_…` at root. Family theorems are named by the predicate and the law,
`isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix`,
`isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`, never by the source. The OSI names
follow CEMT's term "injection": `IsSubspaceInjection`, `HasSubspaceInjection`,
`IsObliviousSubspaceInjection`, and `IsIsotropicSketch`.

**D15. Layout.** `Sketching/` with `Properties/` (S0, S1), `Gaussian/` (S2, S3), `Sampling/`
(S4, S5), `Structured/` (S6), `Sparse/` (S7, and the deferred families of §4a later); files by
topic, fixed in each stage note.

**D16. Bibliography.** The SRHT paper and the Freedman paper are both Tropp 2011: the SRHT key is
`Tropp2011a`, `Tropp2011` keeps its meaning. New key: `CamanoEpperlyMeyerTropp2025`. The
prototype's unpublished manuscripts are not cited anywhere (maintainer, 2026-10-14). A ported
statement whose docstring cited one cites the published source that states it (§7). If there
is none, it cites nothing, and its docstring says that it is proved without a literature source.
In this round that concerns CountSketch's exact second moment (S7).

## 3. Conventions the stages follow

Subject to §2; inherited from `PORT_PROBABILITY.md` §2 D2, D3, D5 and §3.

- Tails in failure form, non-strict events, `μ.real`; never `1 - δ ≤ μ.real {good}`. Every
  expectation upper bound beside its `integrable_…` companion. `[IsProbabilityMeasure μ]` only
  where `HasLaw` with a probability law does not imply it.
- A guarantee `X ≤ c` fails on `{c < X}`: a tail that negates a guarantee takes its exact failure
  set, as `HasSubspaceEmbedding` does with `¬ IsSubspaceEmbedding`, so degenerate cases need no
  hypothesis; threshold events (`{t ≤ X}`) stay non-strict. (`docs/design/Sketching-S1.md` §7 Q1,
  adopted 2026-10-14.)
- Euclidean norms `‖WithLp.toLp 2 x‖`; matrix norms by the Matrix layer's names (`specNorm`,
  `frobNorm`); matrix integrals under `open scoped Matrix.Norms.L2Operator` only (§5.1).
- A fixed-`U` theorem assumes `HasOrthonormalCols U` only if its proof needs it; general `U`
  is one corollary by `of_range_le`.
- Halves with different constants (Chernoff's exponents) are two theorems, joined by a union bound.

## 4. Stages

In dependency order; each gets a design note `docs/design/Sketching-<Stage>.md`. Consumers are
the statements of §5; material is prototype paths under `Sketching/` unless marked. The draft's S8
(sparse embeddings) is removed by the revised D6; §4a takes its place.

- **S0 The embedding and injection predicates.**
  - Content: `IsSubspaceInjection` and `IsSubspaceEmbedding` (D1) with their API; the
    measurability of their events; the deterministic consequences of D7, including the two that
    use only the injection (CEMT Lemma 2.6 and the deterministic half of Lemma 2.1).
  - Files: `Properties/SubspaceEmbedding.lean`, `Properties/LeastSquares.lean`.
  - Consumers: every later stage; sketch-and-solve, sketch-and-precondition, the range finder,
    Nyström and generalized Nyström.
  - Material: `Properties/SubspaceEmbedding/` (5 files, 320 lines; the `iff` forms are reusable,
    the `Fin` transport is not).
- **S1 Probabilistic predicates.**
  - Predicates (D2), each with its `HasLaw` lemma: `IsIsotropicSketch`, `HasSubspaceInjection`,
    `HasSubspaceEmbedding`, `IsObliviousSubspaceInjection`, `IsObliviousSubspaceEmbedding`,
    `HasJLProperty`, `HasJLMoment`, `HasGramTraceMoment`.
  - Consequences:
    - JL moment to JL property (Markov), to the JL lemma for `N` points, and to AMM;
    - the trace moment to the embedding (Markov on `tr E ^ (2 q)`);
    - OSE plus isotropy to OSI;
    - composition of two independent sketches (`δ₁ + δ₂`);
    - the oblivious transfer to an independent random `U`, for both oblivious predicates;
    - CEMT Lemma 2.1 and sketch-and-solve with an OSI, in tail form.
  - Files: `Properties/Isotropic`, `Properties/Oblivious`, `Properties/Injection`,
    `Properties/JohnsonLindenstrauss`, `Properties/MatrixMultiplication`,
    `Properties/TraceMoment`.
  - Consumers: S2 to S7; range finding with a sketch independent of the test matrix; generalized
    Nyström.
  - Material: `Properties/JL/JL.lean`; `Properties/ApproxMatrixMultiplication/` (the `∫⁻`
    statement restated in Bochner form); `Sparse/MomentMethod/GramTail.lean` (the Markov step);
    CEMT §2.1 and §2.4 (no prototype material for the OSI).
- **S2 Gaussian and Haar sketches.**
  - Gaussian: the oblivious embedding from R3's Gram sandwich in natural parameters; the OSI from
    its lower half; the JL tail in Dasgupta–Gupta form from the χ² MGF; the JL moment from the
    tail (`integral_le_of_measureReal_ge_le`); sample-size corollaries (`gaussianEmbeddingDim`).
  - Haar: D13, with the OSI from the lower half.
  - Files: `Gaussian/Gaussian.lean`, `Gaussian/Haar.lean`.
  - Consumers: LowRank's test matrices, sketch-and-solve.
  - Material: `Gaussian/GaussianEmbedding.lean`, `Properties/JL/JL.lean`;
    `RandomMatrix/{Gaussian,Haar}` of this library.
  - **Maintainer checkpoint after S2.**
- **S3 Sub-Gaussian sketches.**
  - Content, for independent isotropic sub-Gaussian rows:
    - the JL tail by Bernstein for centred squares (P1's `hasSubexponentialMGF_sq_sub_integral`,
      `measure_sum_ge_le_of_iIndepFun`; Vershynin, Exercise 5.3.3), which closes the Probability
      round's open entry;
    - the JL moment;
    - the oblivious embedding from R3's rows theorem: rows of `X * U` stay isotropic and
      sub-Gaussian by `IsIsotropic.mulVec` and `IsSubgaussianVector.mulVec` when
      `HasOrthonormalCols U`;
    - the OSI as a corollary;
    - the Rademacher sketch as the instance.
  - File: `Gaussian/SubGaussian.lean`.
  - Consumers: users with sign sketches.
  - Material: the prototype's `RandomMatrix/SubGaussian/` JL statements (the two ledger entries),
    `Properties/JL`.
- **S4 Row sampling.**
  - Content: the sampling sketch over `𝕜`; leverage scores (D8); D9's theorem and its
    corollaries, with the lower Chernoff half as `HasSubspaceInjection`; isotropy when every
    `p i > 0`; column-row sampling for AMM with the exact variance (Drineas, Kannan and
    Mahoney; Martinsson and Tropp §7.3) and its domination form.
  - Files: `Sampling/Leverage.lean`, `Sampling/RowSampling.lean`,
    `Sampling/MatrixMultiplication.lean`.
  - Consumers: sketch-and-solve with leverage sampling, Nyström with column sampling, S6.
  - Material: `Sampling/{Leverage,LeverageSampling,SamplingMultiplication,
    SamplingMultiplicationBounds}.lean` (846 lines; the prototype's form is over `ℂ`, here `𝕜`).
- **S5 Sampling without replacement.**
  - Content (D10): the uniform injection law; Hoeffding's convex-order comparison, in the
    generality D10 fixes; the matrix Chernoff tails without replacement; the row-sampling
    theorem of S4 for a uniform subset.
  - Files: `Probability/ConvexOrder.lean`, `Sampling/WithoutReplacement.lean`.
  - Consumers: S6, and the deferred sparse comparison (§4a).
  - Material: `Sampling/{SamplingWithoutReplacement,SamplingWithoutReplacementTails}.lean` and
    the seven `Uniform*` files (about 1140 lines; `uniformOn` should absorb the counting and
    marginal files).
- **S6 SRHT.**
  - Content (D11): the sketch `√(n / k) • Pᵀ * H * diagonal ξ`; flattening; the two sampling
    models through S4 and S5; the oblivious embedding, and the OSI from the lower Chernoff half;
    `srhtRowBound`; the Walsh and Fourier instances.
  - Files: `Structured/Flattening.lean`, `Structured/SRHT.lean`.
  - Consumers: HMT §11 range finding, sketch-and-precondition (Blendenpik's use).
  - Material: `Structured/` (5 files, 1001 lines; one of the two row bounds is ported, the other
    is dominated).
- **S7 CountSketch.**
  - Content:
    - the law (uniform hash times signs);
    - the hollow Gram identity, public because the deferred sparse families reuse it;
    - the exact mean of `frobNorm G ^ 2` for the Gram error `G`;
    - `HasGramTraceMoment` at `q = 1`;
    - the oblivious embedding with `(d ^ 2 + d) / (m ε ^ 2)`, and the OSI as a corollary;
    - the JL moment at `p = 2`, and hence AMM.
  - Sources: Woodruff 2014, Theorem 14 (the JL moment at `p = 2` from `2 / (ε ^ 2 δ)` rows,
    after Thorup and Zhang) and Theorem 9 (the embedding at `O(d ^ 2 / (δ ε ^ 2))` rows, after
    Meng–Mahoney and Nelson–Nguyen); CEMT Lemma B.1 (the second moment of a CountSketch).
    Proved without a literature source, and said so in its docstring: the exact identity for
    `E frobNorm G ^ 2`. Its consequence `(d ^ 2 + d) / m` is attributed to Nelson and
    Nguyen, unconfirmed (§7).
  - File: `Sparse/CountSketch.lean`.
  - Material: `Sparse/CountSketch*.lean` (4 files, 425 lines, already in the target shape), and
    the prototype's `integral_quadForm_sq_rademacherVector_of_diag_zero` if
    `QuadraticForm/Moments.lean` lacks it.

Expected size, from the prototype's line counts after removing twins: S0 and S1 about 1400 lines
together (the OSI adds about 200), S2 650, S3 400, S4 950, S5 900, S6 750, S7 450.

## 4a. Deferred: SparseStack and OSNAP, and what they need

Not this round (D6). This section is written for the round that takes them up. Its sources:
- the inventory, §5 and §9;
- the prototype's `Sketching/Sparse/` and its notes `docs/SKETCH_INTERFACE.md` and
  `docs/SPARSE_INTEGRATION.md`, read only;
- CEMT §3, §7.3 and Appendix B.

There are two routes. Each concludes this round's predicates unchanged.

**Already supplied.**
- By this round:
  - `HasGramTraceMoment` at general `q`, the two oblivious predicates, `IsIsotropicSketch`;
  - the trace-moment Markov step (S1);
  - the hollow Gram identity and the CountSketch second moments (S7; CEMT Lemma B.1 is the same
    computation);
  - the uniform-injection law and the convex-order comparison (S5, stated as D10 now requires).
- By the layers below:
  - `specNorm_pow_le_re_trace_pow` (`Matrix/Norms/SchattenPowers.lean`);
  - convexity of `A ↦ re tr f(A)` (`convexOn_re_trace_cfc`, `Matrix/Functions/TraceFunctions.lean`);
  - product and uniform laws (`Measure.pi`, `uniformOn`);
  - Gaussian concentration for Lipschitz functions, and the Sudakov–Fernique and Gordon
    comparisons (`Probability/Distributions/`);
  - noncommutative Khintchine for Gaussian and Rademacher series (P5c).

**Route 1: an OSE through trace moments.** This is the prototype's route. Its published analogue
is Cohen 2016, which is not in hand. Missing:
1. *Comparison with an i.i.d. model:* `E tr G_sparse ^ (2q) ≤ c ^ (4q) E tr G_iid ^ (2q)`, with
   `c = (1 - (1 - 1/b) ^ b)⁻¹ < 1.582`, by a sign-symmetric coupling and convex order (prototype
   `IIDComparison/`, 18 files, 4.7k lines). The general step is S5's lemma. The coupling is
   specific to sparse sketches and belongs in Sketching. OSNAP adds a fill/thin coupling for
   positions sampled without replacement, on S5's injection law.
2. *Moment bounds for the i.i.d. sparse model.* This is the main gap: `E tr G_iid ^ (2q) ≤
   d (3β) ^ (2q)` for entries in `{0, ±√b}`, with `β = (3 + √2)(√(D/m) + D/m + (2q + 1)/s)` and
   `D = d + 2q + 1`. The prototype's proof (`FockModel/`, `Bands/`: 67 files, about 16.6k lines)
   needs three things the library does not have:
   - in Probability, an orthonormal product-polynomial basis of `L²` of a finite product law
     (Mathlib has no orthogonal-polynomial bases for discrete laws);
   - the trace moment written as a vacuum matrix element of a multiplication operator in that
     basis;
   - in the Matrix layer, a ladder bound for graded operators, `‖P₀ T ^ (2q) P₀‖ ≤ (3β) ^ (2q)`
     from band norms at most `β`.

   A more general toolkit could replace it, if a published proof uses one:
   - a public decoupling inequality for chaos in independent random vectors, with convex `F` on
     Hermitian matrices. Vershynin's Theorem 6.1.1 and Exercise 6.1.4 are the scalar and
     Hilbert-space forms; the library has decoupling only inside Hanson–Wright's off-diagonal MGF
     bound.
   - matrix moment bounds, of Khintchine or Rosenthal type, for sums with sparse bounded
     coefficients, beyond P5c's Gaussian and Rademacher series.

   No proof of this bound is in hand for either toolkit, so the later round chooses a published
   proof first. No published source states the prototype's general-parameter bound.
3. *Optional:* `k`-wise independence as a predicate on the marginals of a `Measure` (the
   prototype's `MatchesUpTo`, without `FiniteLaw`), for hashing with limited independence.
   Woodruff 2014, Theorems 9 and 14, state the CountSketch case.
4. Real-valued named parameters (D5) in place of the prototype's rounded `q`, `s`, `m`.

**Route 2: an OSI through Gaussian comparison.** This is CEMT's route (Imported Theorem 1.8 and
Appendix B, from Tropp 2025, Theorem 2.3). It gives SparseStack at `k = O(d)`, `ζ = O(log d)`,
better than any OSE result. Missing:
1. Tropp's comparison theorem for the minimum eigenvalue of a sum of i.i.d. random psd matrices
   against a Gaussian model with the same mean and a dominating variance (CEMT Imported
   Theorem 7.5; Tropp 2025 is not in hand). New, in RandomMatrix.
2. Self-adjoint Gaussian matrix models with what CEMT Table 6 uses:
   - GOE over ℝ, or GUE over ℂ, which needs the complex Gaussian laws of
     `Probability-REPORT.md` §6.3;
   - invariance under `Qᴴ · Q` (CEMT Lemma 7.6);
   - `E λmax ≤ 2 √d`, reachable from Sudakov–Fernique;
   - the weak variance `σ*²`.
3. The CountSketch second moment in CEMT's form (Lemma B.1), which S7 has in another form.

Route 2 proves only the injection. That is what LowRank and sketch-and-solve take (D2). A
consumer that needs both halves, such as sketch-and-precondition, needs Route 1.

**OSNAP** (exactly `s` nonzeros per column, positions sampled without replacement; CEMT's
SparseUniform, Definition 3.1) has an OSE through Cohen 2016 at `k = O(d log d)`. CEMT give no OSI
theorem for it (§3.2.1), so Route 1 with the fill/thin coupling is its only known path.

## 5. What the following rounds need from this one

From the inventory's §3, §7 and §10, and the atlas candidates:

- **Solvers** (sketch-and-solve, sketch-and-precondition, Blendenpik and LSRN, sketch-and-project):
  `HasSubspaceEmbedding S U a b δ μ` for the fixed `U = [A, y]` or `U = A`, and S0's deterministic
  residual and condition-number bounds, so that a solver theorem is S0 composed with any family's
  tail. A constant-factor sketch-and-solve needs only `IsObliviousSubspaceInjection` on `range A`
  (CEMT Theorem 2.7; S1). Preconditioning needs both halves. Sketch-and-project keeps its own
  hypothesis (`λ • 1 ≤ E [(Sᴴ A)⁺ (Sᴴ A)]`), which this round does not touch.
- **LowRank**: the oblivious predicates and their transfer to a random subspace independent of
  the sketch (generalized Nyström sketches twice); the OSI as the hypothesis of the range finder,
  Nyström and generalized Nyström (CEMT Theorem 2.2, Corollaries 2.5 and 2.8, through S1's form of
  Lemma 2.1); SRHT and CountSketch test matrices through it (HMT §11), beside the Gaussian and Haar
  block moments already built; the Haar sketch's exact isotropy. Sparse test matrices with
  `k = O(d)` wait for §4a.
- **Estimation**: Hutch++ and XTrace error bounds through AMM and the JL moment; isotropy itself
  is already `IsIsotropic`.
- **Stability of the interfaces**: the predicates of D1 and D2 are the hypotheses of every later
  sketching statement; a later family (complex Gaussian, LESS, fast JL, SparseStack, OSNAP,
  SparseRTT) concludes them without a new predicate, and a later improvement of a family's tail
  changes a body or adds a theorem (§5.2 rules 4 and 6), never a predicate.

## 6. Not ported

The `_of_hasLaw` and finite-index transport twins; the success-form statements and the
`.toReal` and `ENNReal.ofReal` copies; the second SRHT row bound and the capped-width and Walsh
duplicates; the `MainConclusions` bundles; `Frame` and `FiniteLaw`; real and complex twins of one
result. Deferred rather than dropped, and ledgered with D6 and §4a as the reason: the SparseStack
and OSNAP block (`Bands/`, `FockModel/`, `IIDComparison/`, `FiniteLaw/`, `MomentMethod/` except
the Markov step S1 ports, `SparseStack*`, `UniformSparse`, `SparseLaws`, `SparseEmbedding*`,
`SparseFiniteIndex`). The dead `Bands/Light/ZeroBlock.lean` is not ported at all.

## 7. Literature

The maintainer supplied PDFs in `~/Documents/prove2me/books/` (2026-10-14). Locators below marked
**confirmed** were checked against them. Those marked "to confirm" come from the prototype or from
memory and must be checked before they are cited.

### 7.1 In hand

- **Woodruff 2014** (`Woodruff2014`; the PDF is arXiv v3, February 2015, of the FnT monograph).
  Results are numbered consecutively, not by section. Confirmed:
  - §2.1 subspace embeddings: Definitions 1 to 3 (subspace embedding, OSE, JLT); Theorem 4
    (Gaussian JL); Theorem 6 (Gaussian OSE, `k = Θ((d + log (1/δ)) / ε²)`); Theorem 7 (SRHT);
    Theorem 8 (Clarkson–Woodruff CountSketch); Theorem 9 (CountSketch OSE at
    `O(d² / (δ ε²))` rows, after Meng–Mahoney and Nelson–Nguyen, through the trace-moment Markov
    step that S1 ports).
  - §2.2 matrix multiplication: Definition 12 (the JL moment property, after Kane–Nelson);
    Theorem 13 (AMM from it, with `3 ε`; see D2); Theorem 14 (CountSketch has the JL moment at
    `p = 2` from `2 / (ε² δ)` rows, after Thorup–Zhang).
  - §2.4 leverage scores: Definition 16, Theorem 17, Fact 1 (matrix Chernoff in Bernstein form).
  - §2.5 regression: Theorems 21 and 23.
- **Martinsson and Tropp 2020** (`MartinssonTropp2020`). Confirmed:
  - §7.3 approximate matrix multiplication by sampling: Theorem 7.2, matrix Monte Carlo; §7.3.3,
    importance sampling.
  - §8.1, the definition of an embedding.
  - §8.6, the JL example.
  - §8.7, subspace embeddings: §8.7.2 is the Gaussian analysis from Theorem 8.4.
  - §8.9, random partial isometries (the Haar sketch).
  - §9.2, sparse sign matrices.
  - §9.3, SRTTs.
  - §9.6, coordinate sampling: §9.6.1 coherence and leverage; §9.6.3 leverage score sampling.
  - §10.3, sketch-and-solve; §10.5, sketch-and-precondition.
- **Halko, Martinsson and Tropp 2011** (`HalkoMartinssonTropp2011`; the PDF is arXiv v2,
  December 2010). Confirmed: §4.6, the SRFT; Theorem 9.1, the deterministic bound; §11,
  Theorem 11.1 (the SRFT preserves geometry) and Theorem 11.2 (error bounds).
- **Tropp 2015** (`Tropp2015`). Confirmed: Theorem 5.1.1, matrix Chernoff, with (5.1.5) the lower
  and (5.1.6) the upper tail; after (5.1.8), the weakened lower tail
  `d exp (-(1 - t)² μmin / (2 L))`. Corrected: the book has no i.i.d. row-sampling example. The
  nearest examples are §5.2 (a random column submatrix, by Bernoulli selection, through Chernoff)
  and §6.2, Corollary 6.2.1, and §6.4 (sampling and randomized matrix multiplication, through
  Bernstein). The chapter 7 labels the Probability report lists as unverified were not checked
  here.
- **Vershynin** (`Vershynin2018`). The PDF is the draft of 13 February 2020, not the 2018 print.
  Its section numbers agree with those already cited from the print (§4.6). Its theorem numbers
  are taken from the draft; they are believed to agree with the print but were not checked
  against it, so a docstring that gives a theorem number says "2020 draft" or is checked against
  the print first. From the draft:
  - §2.8: Theorems 2.8.1 and 2.8.2 and Corollary 2.8.3 (Bernstein);
  - §4.6: Theorem 4.6.1 (two-sided bound on sub-Gaussian matrices);
  - §5.3: Theorem 5.3.1 (JL through a random projection), Lemma 5.3.2 (random projection of a
    fixed vector, D13) and Exercise 5.3.3 (JL with sub-Gaussian matrices, S3);
  - §6.1: Theorem 6.1.1, Remark 6.1.3 and Exercise 6.1.4 (decoupling, §4a).
- **Camaño, Epperly, Meyer and Tropp 2025** (`CamanoEpperlyMeyerTropp2025`, new;
  "Faster linear algebra algorithms with structured random matrices", arXiv:2508.21189).
  Confirmed:
  - Definitions 1.1 (OSE with `α`, `β`) and 1.2 (OSI); Proposition 1.15 (spectral form);
  - Lemma 2.1, Theorem 2.2, Corollary 2.5, Lemma 2.6, Theorem 2.7, Corollary 2.8;
  - Imported Theorem 1.8 (SparseStack OSI), Table 3, Definitions 1.7 and 3.1;
  - §7.1 (fourth moments, after Oliveira 2016), §7.3 (Gaussian comparison: Imported Theorem 7.5,
    Lemma 7.6, Table 6), §7.4 (matrix concentration);
  - Appendix B and Lemma B.1.

  Also, through its citations: Tropp 2011, Lemma 3.3 is the SRHT flattening lemma, and its §3.3
  holds the lower-bound example (CEMT cites both as [111]).
- In hand but not cited by this brief: Tropp and Webber 2023, Horn and Johnson, Trefethen 2013,
  Gautschi 2004.

### 7.2 Still missing (all locators to confirm)

- Dasgupta and Gupta, "An elementary proof of a theorem of Johnson and Lindenstrauss", Random
  Structures Algorithms 22 (2003): Lemma 2.2 and Theorem 2.1 (the prototype cites "Lem 2",
  "Thm 2").
- Achlioptas, "Database-friendly random projections", J. Comput. System Sci. 66 (2003):
  Theorem 1.1 (sign sketches). Woodruff §2.1 cites it without a number.
- Kane and Nelson, "Sparser Johnson–Lindenstrauss transforms", J. ACM 61 (2014): the JL moment
  property and AMM (Theorem 6.2 per the prototype). Woodruff cites it without a number. Until it
  is checked, docstrings cite Woodruff, Definition 12 and Theorem 13.
- Sarlós, FOCS 2006: Lemma 6 (AMM from JL), as cited by the prototype.
- Drineas, Kannan and Mahoney, SIAM J. Comput. 36 (2006): Lemma 4 and Theorem 1 (column-row
  sampling). Martinsson and Tropp §7.3 is the confirmed fallback.
- Drineas, Mahoney, Muthukrishnan and Woodruff, JMLR 13 (2012): §1 and §2 (leverage scores).
  Martinsson and Tropp §9.6.1 is the confirmed fallback.
- Tropp, "Improved analysis of the subsampled randomized Hadamard transform", Adv. Adapt. Data
  Anal. 3 (2011) (`Tropp2011a`): the main theorem and the sampling lemma. Lemma 3.3 (flattening)
  is confirmed only secondhand, through CEMT.
- Ailon and Chazelle, SIAM J. Comput. 39 (2009): provenance of the randomized Hadamard step.
- Hoeffding, JASA 58 (1963): Theorem 4 (sampling without replacement), cited 45 times in the
  prototype.
- Gross and Nesme, arXiv:1001.2738 (2010): the matrix form of Hoeffding's comparison.
- Clarkson and Woodruff, J. ACM 63 (2017): CountSketch as a subspace embedding (Woodruff,
  Theorem 8, restates it).
- Nelson and Nguyen, FOCS 2013: the `s = 1` bound `(d ^ 2 + d) / (δ ε ^ 2)` and the OSNAP law.
  Woodruff, Theorem 9, confirms `O(d² / (δ ε²))` but not the constant.
- Cohen, SODA 2016: the trace-moment route for sparse embeddings (`k = O(d log d)`,
  `ζ = O(log d)`, as restated by Martinsson and Tropp §9.2 and CEMT §1.5.1). Needed for §4a.
- Chenakkod, Dereziński, Dong and Rudelson, STOC 2024, and Chenakkod, Dereziński and Dong,
  ICALP 2025: SparseStack OSEs at `k = O(d)`, `ζ = O(log³ d)` (CEMT, Table 3 and §1.5.1). For §4a.
- Tropp, "Comparison theorems for the minimum eigenvalue of a random positive-semidefinite
  matrix", arXiv:2501.16578 (2025): Theorem 2.3 and Remark 6.5, the source of CEMT's Imported
  Theorems 1.8 and 7.5. For §4a.
- Oliveira, Probab. Theory Related Fields 166 (2016): Theorem 1.1 (OSI from fourth moments).
  Not used this round.
- For S0: Rokhlin and Tygert, PNAS 105 (2008), and Avron, Maymounkov and Toledo, "Blendenpik",
  SIAM J. Sci. Comput. 32 (2010): the preconditioning consequence of an embedding. Martinsson and
  Tropp §10.5 is the confirmed fallback.

## 8. Done

The round is done when every stage S0 to S7 is implemented, `NLAlib` and `NLAlibScaffold`
build with no warnings, `scripts/Audit.lean` and `scripts/Lint.lean` are clean, `check_refs.py`
passes, the ledger accounts for the prototype's `Sketching/` and the two carried-over JL
entries, `docs/port/status.md` lists what is in `NLAlibScaffold` with a difficulty estimate each,
and `docs/design/Sketching-REPORT.md` reports as `Probability-REPORT.md` did, with its §4 listing
the orchestrator's decisions and marking any of the §2(a) kind, and its §6 carrying §4a
forward as the entry for the round that takes up SparseStack and OSNAP.
