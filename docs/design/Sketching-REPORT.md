# Sketching round: final report

Date: 2026-10-15. Branch `main`.

This is the report that `docs/PORT_SKETCHING.md` §8 asks for: what the Sketching layer offers,
what the maintainer and the orchestrator decided, what was deferred and what it needs, and what
is open. The per-stage detail is in the design notes `docs/design/Sketching-S0.md` to
`Sketching-S7.md`; each ends with its review amendments (§8), which override §0 to §7 where they
disagree, and the later ones carry skeleton notes and wrap-up records.

Abbreviations used below: OSE and OSI, oblivious subspace embedding and oblivious subspace
injection; JL, Johnson and Lindenstrauss; AMM, approximate matrix multiplication; CEMT, Camaño,
Epperly, Meyer and Tropp 2025; HMT, Halko, Martinsson and Tropp 2011; MT, Martinsson and Tropp
2020; D1 to D16, the decisions of the brief `docs/PORT_SKETCHING.md` §2; S0 to S7, this round's
stages; M3, P1, R3 and the like, stages of the earlier Matrix, Probability and RandomMatrix
rounds; "rule 4" and "rule 6", the numbered rules under "Numerical bounds" in `CONTRIBUTING.md`
§5.2 (incomparable bounds coexist under distinguishing names; a dominated result is reproved
from the better one or deprecated).

## 1. Summary

The round built the layer that randomized algorithms will prove their theorems on: two
deterministic predicates (subspace embedding and its lower half, the subspace injection), eight
probabilistic ones, their deterministic and probabilistic consequences proved once, and the
sketch families (Gaussian, Haar, sub-Gaussian rows, Rademacher, row sampling with and without
replacement, SRHT in two sampling models, CountSketch) shown to conclude them with explicit
constants and named sample sizes. Every statement is proved; no `sorry` anywhere. The work ran
from the brief (`ca32ca1`, `65dcdb5`, 2026-10-14) through the stage commits to the registration
(`e725d6b`) and the two wrap-ups (`4e75edb`, `a0f9b23`, 2026-10-15): 40 commits in that range
(four merges), including library-wide work done alongside (LaTeX docstrings, the
`pseudoConditionNumber` rename, the explore viewer `scripts/Explore.lean`).

- `NLAlib/Sketching/`: 21 files, 9,522 lines, 322 public declarations (by declaration keyword:
  282 theorems, 16 definitions, 5 structures, 10 `irreducible_def` constants and sizes, 6
  instances, 1 `abbrev`, 2 deprecated aliases), and 137 private helpers. Per file in §1.1.
- Lower layers: 10 new files (`Probability/ConvexOrder`, `Probability/Distributions/UniformInjection`,
  `Probability/MatrixConcentration/ChernoffWithoutReplacement`, `RandomMatrix/Haar/Sphere`,
  `Matrix/Structured/BoundedOrthonormal`, `Matrix/Basic/FromCols`,
  `ForMathlib/Probability/Independence/Basic`, `ForMathlib/Analysis/SpecialFunctions/Log/Deriv`,
  `ForMathlib/Data/Finset/Max`, `ForMathlib/MeasureTheory/MeasurableSpace/Defs`), 2,004
  lines, and additions to `ChiSquare`, `SubGaussian/Square`, `SubGaussianVector/Norm`, `Tail`,
  `Law`, `Distributions/{Rademacher,Sampling}`, `Haar/Basic`, `Matrix/Basic/Orthonormal`,
  `Structured/{Walsh,Circulant}`, `ForMathlib/LinearAlgebra/Matrix/{ConjTranspose,PosDef}`: 61
  public declarations below `Sketching/` in all (the itemization in §2.4; the
  `pseudoConditionNumber` renames left out).
- Final stage check (`scripts/stage_check.sh`, 2026-10-15, after this report's ledger pass): 250
  proved modules, 0 not yet; build with 0 warnings; audit 6015 declarations, 0 violations; lint 0
  errors in 4271 declarations; 46 bibliography keys, 0 problems. The output is quoted in §7.
- Ledger (§1.2): 1886 entries tagged `S0` to `S7`, 90 with a target, 1796 with a reason and no
  target, 1674 of them deferred SparseStack and OSNAP material. `scripts/ledger_missing.py`
  reports 0 of 1905 unaccounted for under the round's prefixes, and `scripts/ledger_check.py`
  reports one missing target, the pre-existing structure field `IsSVD.eq` (M3), which its
  textual parser does not see.

| Stage | Headline results | Files (public declarations) |
|---|---|---|
| S0 | `IsSubspaceInjection S U a`, `IsSubspaceEmbedding S U a b` (Loewner halves of `(S U)ᴴ (S U)` against `a • Uᴴ U`, `b • Uᴴ U`) with norm, Gram, singular-value, range, scaling, composition and measurability API; sketch-and-solve residual `≤ √(b/a)` times the optimum; preconditioned `pseudoConditionNumber (A M) ^ 2 ≤ b / a`; CEMT Lemma 2.6 (`‖A x̃ - y‖² ≤ ‖r‖² + ‖S r‖² / a`) and the deterministic half of Lemma 2.1 | `Properties/SubspaceEmbedding` (29), `Properties/LeastSquares` (13, two of them deprecated aliases), `Matrix/Basic/FromCols` (2) |
| S1 | `IsIsotropicSketch`, `HasSubspaceInjection`, `HasSubspaceEmbedding`, `IsObliviousSubspaceInjection`, `IsObliviousSubspaceEmbedding`, `HasJLProperty`, `HasJLMoment`, `HasGramTraceMoment`, each with its `HasLaw` lemma; JL moment to JL property (Markov), JL lemma for `N` points with `choose N 2`, AMM with constant `ε` over `ℝ`; trace moment to embedding `B / ε^(2q)`; OSE plus isotropy to OSI; composition (`δ₁ + δ₂`, parameters multiply); transfer to an independent random `U`; CEMT Lemma 2.1 and sketch-and-solve with an OSI as tails `δ + 1/t` | `Properties/{Isotropic (12), FixedSubspace (14), Oblivious (15), Injection (6), JohnsonLindenstrauss (14), MatrixMultiplication (5), TraceMoment (6)}` |
| S2 | Gaussian `(√k)⁻¹ G`: OSE `(1 ∓ (√d + t)/√k)²` outside `2 e^{-t²/2}`, OSI outside `e^{-t²/2}`, JL `2 exp (-k (ε²/4 - ε³/6))` for every `ε ≥ 0`, JL moment at `p = 2` exactly `2/(k ε²)`, sizes `gaussianEmbeddingDim`, `gaussianInjectionDim`, `jlDim`. Haar `√(n/k) Qᴴ`: exact isotropy, `specNorm = √(n/k)` a.s., the a.s. upper half `n/k`, OSE and OSI by the Gaussian transfer, the complement route near `k = n`, the exact `k = n` case, JL with the Gaussian exponent, JL moment `2 (n - k)/(k (n + 2) ε²)`. χ² Chernoff tails in Dasgupta–Gupta form; the uniform sphere's projected law, tails and fourth moment | `Gaussian/{Gaussian (27), Haar (11), HaarEmbedding (8)}`, `Distributions/ChiSquare` (+4), `Haar/Sphere` (7) |
| S3 | Independent isotropic sub-Gaussian rows: JL `2 exp (-(1/64) k min (ε²/c², ε/c))`, JL moment `(16 c² - 1)/(k ε²)`, OSE `1 ∓ ε` outside `2 · 9^d · exp (-(1/64) k min (ε²/(4c²), ε/(2c)))` through JL plus a `1/4`-net, OSI, sizes; entries through a bridge; rows with `E ⟨X, x⟩⁴ ≤ 3 ‖x‖⁴` get Dasgupta and Gupta's exponent; `rademacherMatrix` with JL `2 exp (-k (ε²/4 - ε³/6))`, OSE and OSI `2 · 9^d exp (-k (ε²/16 - ε³/48))`, sizes through `jlDim` | `Gaussian/{SubGaussian (20), Rademacher (12)}`, `SubGaussian/Square` (+1), `Law` (+1), `Log/Deriv` (5) |
| S4 | `leverageScore` (any shape and rank, over `𝕜`), `coherence`, `leverageScoreDistribution`; `samplingSketch k p` (pushforward, D4) with isotropy for positive weights; fixed-`U` injection `1 - ε` outside `rank U · e^{-ε² k/(2L)}` and embedding `1 ∓ ε` outside `2 rank U · e^{-ε² k/(3L)}` under `leverageScore U i ≤ L p i`; sizes `samplingSize`, `samplingInjectionSize`; AMM unbiasedness, exact second moment and domination bound `L ‖A‖_F ‖B‖_F / k` with tails | `Sampling/{Leverage (17), RowSampling (33), MatrixMultiplication (7)}` |
| S5 | Uniform injections `uniformOn {f : k → n | Injective f}` (Mathlib's measure): mass, invariance, marginals; the kernel form of convex order and Hoeffding's comparison (sampling without replacement is dominated by i.i.d. sampling for every continuous convex `f`), in a real Banach space; matrix Chernoff without replacement (source and simplified forms); `samplingSketchWithoutReplacement k n` with S4's exponents and sizes | `Probability/{ConvexOrder (2), Distributions/UniformInjection (6), MatrixConcentration/ChernoffWithoutReplacement (6)}`, `Sampling/WithoutReplacement` (13) |
| S6 | `IsBoundedOrthonormal F β`; flattening: all leverage scores of `F D U` at most `β (d + 2√(d t) + 2t)/n` outside `n e^{-t}`; flatten-then-sample transfers for any independent random unitary; `srht k F`, `srhtWithReplacement k F` with isotropy, `S Sᴴ = (n/k) • 1` and `specNorm S = √(n/k)` a.s. (without replacement); OSE and OSI for both models with S4's exponents at `L = β (d + 2√(d t) + 2t)` plus the flattening failure `n e^{-t}`, sizes at `L = β · srhtRowBound n d (δ/2)`; the general Hsu–Kakade–Zhang tail `P(c (‖A‖_F² + 2 ‖Aᴴ A‖_F √t + 2 ‖A‖² t) ≤ ‖A x‖²) ≤ e^{-t}` over `𝕜`; the sub-gamma Chernoff inversion; the sections lemma | `Structured/{Flattening (9), SRHT (23)}`, `Matrix/Structured/BoundedOrthonormal` (5), `SubGaussianVector/Norm` (+2), `Tail` (+1), `Independence/Basic` (1), `Walsh` (+1), `Circulant` (+1) |
| S7 | `countSketch k n` over `𝕜` (real signs coerced); general Gram entry formula and the hollow identity; isotropy; exact trace second moment `E |tr (M (Sᴴ S - 1))|² = (‖M‖_F² + ⟨M, Mᵀ⟩_F - 2 ∑ |M i i|²)/m`; exact AMM identity and bound `2 ‖A‖_F² ‖B‖_F²/m` over `𝕜`; Gram mean; `HasGramTraceMoment` at `q = 1` with `(d² + d)/m`; OSE and OSI with failure `(d² + d)/(m ε²)`; JL moment `2/(m ε²)` at `p = 2`; size `countSketchRows` and Woodruff's `2/(ε² δ)` | `Sparse/CountSketch` (28), `Distributions/Sampling` (+2), `MeasurableSpace/Defs` (1) |

### 1.1 Files

| File | Lines | Public | Of which definitions, structures, constants, instances |
|---|---|---|---|
| `Properties/SubspaceEmbedding.lean` | 453 | 29 | `IsSubspaceInjection` (def), `IsSubspaceEmbedding` (structure) |
| `Properties/LeastSquares.lean` | 310 | 13 | none; 2 deprecated aliases (`conditionNumber` spellings) |
| `Properties/Isotropic.lean` | 297 | 12 | `IsIsotropicSketch` |
| `Properties/FixedSubspace.lean` | 197 | 14 | `HasSubspaceInjection`, `HasSubspaceEmbedding` |
| `Properties/Oblivious.lean` | 252 | 15 | `IsObliviousSubspaceEmbedding`, `IsObliviousSubspaceInjection` |
| `Properties/Injection.lean` | 221 | 6 | none |
| `Properties/JohnsonLindenstrauss.lean` | 389 | 14 | `HasJLProperty`, `HasJLMoment` |
| `Properties/MatrixMultiplication.lean` | 466 | 5 | none |
| `Properties/TraceMoment.lean` | 140 | 6 | `HasGramTraceMoment` |
| `Gaussian/Gaussian.lean` | 697 | 27 | `gaussianEmbeddingDim`, `gaussianInjectionDim`, `jlDim` |
| `Gaussian/Haar.lean` | 411 | 11 | none |
| `Gaussian/HaarEmbedding.lean` | 687 | 8 | none |
| `Gaussian/SubGaussian.lean` | 624 | 20 | `subgaussianJLConstant`, `subgaussianJLDim`, `subgaussianEmbeddingDim` |
| `Gaussian/Rademacher.lean` | 324 | 12 | `rademacherMatrix` (abbrev), its instance |
| `Sampling/Leverage.lean` | 212 | 17 | `leverageScore`, `coherence`, `leverageScoreDistribution` |
| `Sampling/RowSampling.lean` | 823 | 33 | `samplingSketchMatrix`, `samplingSketch`, `samplingSize`, `samplingInjectionSize`, an instance |
| `Sampling/MatrixMultiplication.lean` | 387 | 7 | none |
| `Sampling/WithoutReplacement.lean` | 504 | 13 | `samplingSketchWithoutReplacement`, an instance |
| `Structured/Flattening.lean` | 430 | 9 | `srhtRowBound` |
| `Structured/SRHT.lean` | 744 | 23 | `srhtMatrix`, `srht`, `srhtWithReplacement`, two instances |
| `Sparse/CountSketch.lean` | 954 | 28 | `countSketchMatrix`, `countSketch`, `countSketchRows`, an instance |

The largest file is `CountSketch.lean` (954 lines); none is over the 1000-line guideline after
the wrap-up split `Haar.lean` (1091 lines).

### 1.2 Ledger

`docs/port/ledger.json` grows from 3673 to 5553 entries. The round's entries, by stage (entries,
with target):

| Stage | Entries | With target | Content |
|---|---|---|---|
| S0 | 13 | 12 | `Properties/SubspaceEmbedding/` (5 files); the `Fin` reindexing cut (D5) |
| S1 | 9 | 3 | `Properties/JL/JL.lean`'s `jl_lemma`, the four AMM declarations (`∫⁻` forms cut, private steps), `Sparse/MomentMethod/GramTail.lean` (the Markov step ported, the three SparseStack tails deferred) |
| S2 | 13 | 11 | the other seven JL declarations, `Gaussian/GaussianEmbedding.lean`; four lower-layer entries of the prototype's `ChiSquare` and `ForMathlib.Analysis.Real`, earlier booked by P3 as cut or private, now mapped to the public `ChiSquare` tails and `Real.log_one_add_le_cubic`, `Real.log_one_sub_le_quadratic` |
| S3 | 2 | 2 | the two sub-Gaussian JL entries the Probability round left open (`RandomMatrix/SubGaussian/SubGaussianJL.lean`), now `hasJLProperty_of_isSubgaussianVector` and `hasJLProperty_of_iIndepFun_entry` |
| S4 | 40 | 16 | `Sampling/{Leverage,LeverageSampling,SamplingMultiplication,SamplingMultiplicationBounds}` |
| S5 | 56 | 9 | `Sampling/SamplingWithoutReplacement*` and the `Uniform*` files except `UniformCollision`; `ForMathlib/Data/ExactRowSubset` (D10) |
| S6 | 52 | 23 | `Structured/` (5 files); `ForMathlib/Probability/FiniteProductEvents` (one lemma to the sections lemma, the `Finite` twins not ported) |
| S7 | 1701 | 14 | `Sparse/CountSketch*` (4 files), `Sampling/UniformCollision`, M5's `sum_offDiagonal_frame_contractions_eq` (subsumed by the AMM identity), and the deferred block: 1671 SparseStack and OSNAP declarations (`deferred, PORT_SKETCHING D6 and §4a`) and the 6 of the dead `Bands/Light/ZeroBlock.lean` (not ported at all, brief §6) |

The ledger's `conditionNumber` targets (28 entries of M4, M6, M7, M9) now point at the
`pseudoConditionNumber` names of commit `503070b`; the deprecated aliases remain. The
`note` of `NLAlib.conditionNumber` (a usability-audit sentence from another session) is kept as
it stood. `scripts/ledger_check.py` now recognises `irreducible_def` (it reported `srhtRowBound` as
missing).

## 2. What a user gets

Conventions (brief §3): tails in failure form with `μ.real`; a guarantee `X ≤ c` fails on
`{c < X}`, so a tail that negates a guarantee takes its exact failure set and needs no
hypothesis in degenerate cases, while threshold events stay non-strict (S1 §7 Q1); Euclidean norms
`‖WithLp.toLp 2 x‖`; matrix integrals under `Matrix.Norms.L2Operator`; sizes as index types,
`Fintype.card k`, no `Fin`; sizes and non-source constants as `irreducible_def`s with positivity,
monotonicity and a one-sided comparison (D5, CONTRIBUTING §5.2).

### 2.1 Predicates

| Predicate | Meaning | Consequences proved once |
|---|---|---|
| `IsSubspaceInjection S U a` (def) | `a • (Uᴴ U) ≤ (S U)ᴴ (S U)` | norm, Gram and singular-value forms; `mono`, `of_range_le`, `U * C`; scaling (`‖c‖² a`, `smul_real`), composition; closed event, measurability; injectivity on `range U` for `0 < a`; CEMT Lemma 2.6 and the deterministic half of Lemma 2.1 |
| `IsSubspaceEmbedding S U a b` (structure, `lower`, `upper`) | both Loewner halves | as above, both halves; sketch-and-solve `√(b/a)`; preconditioning `pseudoConditionNumber (A M) ^ 2 ≤ b / a` for any `M` with `HasOrthonormalCols (S A M)` and the QR corollary |
| `IsIsotropicSketch S μ` | `MemLp 2` entries and `∫ (S ω)ᴴ S ω = 1` | CEMT's (1.2) as an iff; `E ‖S M‖_F² = ‖M‖_F²`; `(√k)⁻¹ X` for isotropic rows; composition of independent sketches |
| `HasSubspaceInjection`, `HasSubspaceEmbedding` | failure probability of the fixed-`U` event at most `δ` | `mono`, `of_range_le`, orthonormal-column constructors from singular-value tails, the union of halves |
| `IsObliviousSubspaceInjection S d a δ μ` (structure) | isotropy and the injection for every `U` of rank at most `d` | `.hasSubspaceInjection` for any shape, constructors over orthonormal `U`, transfer to an independent random `V`, composition |
| `IsObliviousSubspaceEmbedding S d a b δ μ` | the embedding for every square `U` of rank at most `d` | as above; `.isObliviousSubspaceInjection` with isotropy |
| `HasJLProperty S ε δ μ` | unit-vector JL tail | JL lemma for any finite family (`choose N 2 · δ`); OSE through a `1/4`-net, `9^(d · finrank ℝ 𝕜) δ` at `1 ∓ 2ε` |
| `HasJLMoment S ε δ p μ` (`p : ℝ`) | `E |‖S x‖² - 1|^p ≤ ε^p δ` for unit `x` | JL property (Markov); AMM over `ℝ` with constant `ε` for `p ≥ 2`; OSE `1 ∓ ε d` |
| `HasGramTraceMoment S U q B μ` | `E re tr (E^{2q}) ≤ B` for the Gram error of orthonormal `U` | embedding `1 ∓ ε` outside `B / ε^{2q}` and the oblivious form |

### 2.2 Families

| Family | Law and constructor | Concludes |
|---|---|---|
| Gaussian | `HasLaw G (gaussianMatrix k n) μ`, sketch `(√k)⁻¹ • G`, real | OSE, OSI, JL, JL moment, isotropy, sizes |
| Haar | `HasLaw Q (haarFrame n k) μ`, sketch `√(n/k) • Qᴴ`, real | OSE (three shapes), OSI, JL, JL moment, exact isotropy, a.s. norm and upper half |
| sub-Gaussian rows | `iIndepFun` rows, `IsSubgaussianVector` proxy `c`, `IsIsotropic`; entries through `iIndepFun_row_of_iIndepFun_entry` | JL, JL moment, OSE, OSI, sizes |
| Rademacher | `rademacherMatrix k n` | JL, JL moment (exact second moment), OSE, OSI, isotropy, three sizes |
| row sampling | `samplingSketch k p`, `samplingSketchMatrix p ι`, over `𝕜` | fixed-`U` injection and embedding, isotropy for positive weights, AMM, sizes |
| sampling without replacement | `samplingSketchWithoutReplacement k n` | fixed-`U` injection and embedding at uniform weights, coherence form, isotropy, sizes |
| SRHT | `srht k F`, `srhtWithReplacement k F`, `srhtMatrix F ξ ι`, over `𝕜`, `IsBoundedOrthonormal F β` | OSE and OSI for both models, isotropy, partial isometry, sizes; Walsh and Fourier through the two instance lemmas |
| CountSketch | `countSketch k n`, `countSketchMatrix h σ`, over `𝕜` | OSE, OSI, JL moment, AMM, `HasGramTraceMoment` at `q = 1`, isotropy, sizes |

### 2.3 Main theorems by topic

**Deterministic (S0).** `IsSubspaceEmbedding.norm_sub_mulVec_le` (residual `√(b/a)` times the
optimum, for any `U` whose range contains `range A` and `y`), `…_sq_le`, `…_sq_le_of_fromCols`;
`IsSubspaceEmbedding.pseudoConditionNumber_mul_sq_le`, `…_inv_sq_le_of_isQR`, the Loewner pair
`inv_smul_one_le_conjTranspose_mul_self`, `conjTranspose_mul_self_le_inv_smul_one`;
`IsSubspaceInjection.norm_sub_mulVec_sq_le` (CEMT Lemma 2.6), `…frobNorm_sub_mul_pinv_mul_sq_le`
(matrix right-hand side), `…frobNorm_mul_pinv_sq_le` (Lemma 2.1, deterministic half).

**Probabilistic consequences (S1).** `HasJLMoment.hasJLProperty`,
`HasJLProperty.measure_exists_abs_norm_mulVec_sq_sub_ge_le`,
`HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le` (AMM, with the event D2 fixes),
`HasGramTraceMoment.hasSubspaceEmbedding`, `IsObliviousSubspaceEmbedding.mul`,
`IsObliviousSubspaceEmbedding.measure_not_isSubspaceEmbedding_le_of_indepFun` (transfer),
`HasSubspaceInjection.measure_frobNorm_mul_pinv_sq_gt_le` and
`HasSubspaceInjection.measure_norm_sub_mulVec_sq_gt_le` (CEMT Lemma 2.1 and Theorem 2.7 as tails,
`δ + 1/t`), with oblivious twins; `HasJLProperty.isObliviousSubspaceEmbedding` (net step).

**Families (S2 to S7).** `isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix`,
`isObliviousSubspaceInjection_of_hasLaw_gaussianMatrix`, `hasJLProperty_of_hasLaw_gaussianMatrix`,
`hasJLMoment_of_hasLaw_gaussianMatrix`; `isObliviousSubspaceEmbedding_of_hasLaw_haarFrame` (lower
`(1 - (√d + t)/√k)² / (1 + (√k + s)/√n)²`, upper `n/k`, failure `e^{-t²/2} + e^{-s²/2}`), the
`…_of_lt_sqrt_sub_sqrt` shape, and the fixed-`U` exact case
`HasOrthonormalCols.hasSubspaceEmbedding_of_hasLaw_haarFrame_of_card_add_eq`;
`hasJLProperty_of_isSubgaussianVector`,
`hasJLProperty_of_isSubgaussianVector_of_integral_pow_four_le`,
`isObliviousSubspaceEmbedding_of_isSubgaussianVector`, `…_of_hasLaw_rademacherMatrix`;
`hasSubspaceEmbedding_of_hasLaw_samplingSketch`, `hasSubspaceInjection_of_hasLaw_samplingSketch`,
`integral_frobNorm_conjTranspose_mul_sub_sq_of_hasLaw_samplingSketch` (exact
`(∑ ‖A i‖² ‖B i‖² / p i - ‖Aᴴ B‖_F²)/k` under a support condition);
`ConvexOn.integral_uniformOn_injective_le_integral_pi` (Hoeffding),
`hasSubspaceEmbedding_of_hasLaw_samplingSketchWithoutReplacement`;
`measureReal_not_forall_leverageScore_mul_diagonal_le_of_hasLaw_rademacherVector` (flattening),
`hasSubspaceEmbedding_mul_of_indepFun_of_leverageScore_le` (transfer),
`isObliviousSubspaceEmbedding_of_hasLaw_srht`, `…_srhtWithReplacement`, `ae_specNorm_eq_of_hasLaw_srht`;
`integral_norm_trace_mul_conjTranspose_mul_self_sub_one_sq_of_hasLaw_countSketch`,
`hasGramTraceMoment_of_hasLaw_countSketch`, `isObliviousSubspaceEmbedding_of_hasLaw_countSketch`,
`hasJLMoment_of_hasLaw_countSketch`.

### 2.4 Lower-layer additions

- Probability: χ² Chernoff tails in Dasgupta–Gupta form and the weighted χ² transform
  (`ChiSquare`, +4; Laurent–Massart and the small ball now follow from them and keep their names);
  `measureReal_abs_sum_sq_div_card_sub_one_ge_le_of_iIndepFun` (`Square`, `E Y⁴ ≤ 3`);
  `iIndepFun_row_of_iIndepFun_entry` (`Law`); `measureReal_ge_le_exp_neg_of_mgf_le` (`Tail`,
  sub-gamma Chernoff); `IsSubgaussianVector.measure_sum_mul_sq_ge_le` and
  `.measure_norm_mulVec_sq_ge_le` (`Norm`; `measure_norm_sq_ge_le` reproved from the latter); six
  Rademacher facts in `𝕜` (`Rademacher`); the collision probability and `sum_const_inv_card`
  (`Sampling`); `UniformInjection` (6), `ConvexOrder` (2), `ChernoffWithoutReplacement` (6).
- RandomMatrix: `Haar/Sphere` (7: the projected law of a uniform unit vector, its two one-sided
  tails and the two-sided tail in Dasgupta and Gupta's form, the invariance lemma made public at
  the wrap-up, the fourth moment and its integrability); `measurable_inv_norm_smul`
  (`Haar/Basic`).
- Matrix: `IsBoundedOrthonormal` with the Hadamard bridge, `transpose`, `conjTranspose`, `one_le`;
  Walsh and Fourier instances; `FromCols` (2); `hasOrthonormalCols_replicateCol`,
  `HasOrthonormalCols.mulVec_injective_of_mul` (`Orthonormal`).
- ForMathlib, each an upstream candidate: `Real.log_one_add_le_cubic` (for `u > -1`),
  `…_of_nonpos`, `Real.log_one_sub_le_quadratic`, `Real.neg_log_one_sub_le`,
  `Real.log_nine_le_nine_div_four`; `Finset.exists_le_lt_of_forall_lt`;
  `Matrix.conjTranspose_mul_eq_sum_vecMulVec`; `Matrix.PosSemidef.conjTranspose_mul_mul_same'`;
  `DiscreteMeasurableSpace.eq_top`; `ProbabilityTheory.IndepFun.measureReal_mem_le_add` (sections);
  `Matrix.instSecondCountableTopology`.

## 3. Numerical constants

Rule (`CONTRIBUTING.md` §5.2; brief D5, D12): the source's constant, when the proof reaches it,
is written in the statement; any other is an `irreducible_def` with a one-sided comparison.

| Name | Body | Note |
|---|---|---|
| `gaussianEmbeddingDim d ε δ` | `9 (√d + √(2 log (2/δ)))² / ε²` | the Gaussian OSE size; the prototype's `18 (d + 2 log (2/δ))/ε²` is its comparison |
| `gaussianInjectionDim d ε δ` | `4 (√d + √(2 log (1/δ)))² / ε²` | the Gaussian OSI size |
| `jlDim ε δ` | `log (2/δ) / (ε²/4 - ε³/6)` | Gaussian, Haar and Rademacher JL; junk for `ε ≥ 3/2` |
| `subgaussianJLConstant` | `1/64` | prototype `1/(256 e²)`; Vershynin's `c` unspecified |
| `subgaussianJLDim c ε δ` | `c² log (2/δ) / (subgaussianJLConstant ε²)` | |
| `subgaussianEmbeddingDim c d ε δ` | `4 c² (d log 9 + log (2/δ)) / (subgaussianJLConstant ε²)` | at most `576 c² (d + log (2/δ))/ε²` |
| `samplingSize d L ε δ` | `3 L log (2d/δ) / ε²` | row sampling, both models, SRHT |
| `samplingInjectionSize d L ε δ` | `2 L log (d/δ) / ε²` | the lower half |
| `srhtRowBound n d δ` | `d + 2 √(d log (n/δ)) + 2 log (n/δ)` | at most `(√d + √(2 log (n/δ)))²`; Tropp's `(√d + √(8 log (n/δ)))²` (through HMT Theorem 11.1) |
| `countSketchRows d ε δ` | `(d² + d) / (δ ε²)` | the proof's constant, not attributed (§6.2) |

Written in statements: Dasgupta and Gupta's exponent `k (ε²/4 - ε³/6)` (Gaussian, Haar, rows with
`E ⟨X, x⟩⁴ ≤ 3`, Rademacher); the Gaussian Gram tails `(1 ∓ (√d + t)/√k)²` with `2 e^{-t²/2}` (one
side `e^{-t²/2}`); Tropp's Chernoff exponents `2L` lower, `3L` upper, `2d` two-sided; AMM from the
JL moment with `ε` (Woodruff's Theorem 13 has `3ε`; `1` is optimal, S1 §7 Q2); the moment constants
`16 c² - 1` (sub-Gaussian) and exact second moments (Gaussian `2/k`, Haar `2(n - k)/(k(n + 2))`,
Rademacher, CountSketch `2/m`); CountSketch's `(d² + d)/(m ε²)` and Woodruff's `2/(ε² δ)` rows for
the JL moment (Theorem 14).

## 4. Decisions

### 4.1 The maintainer's

1. **D1 to D5, approved as recommended (2026-10-14).** D1 (b): the two-parameter
   `IsSubspaceEmbedding S U a b`. D2 (i), (α), (A): `Prop`-valued predicates on a random matrix,
   oblivious quantification over rank-bounded square `U`, both JL predicates. D3 (a): six
   first-class families. D4 (a): each family is a law on matrices, the pushforward of a public
   constructor. D5: index types, tails in natural parameters, real-valued named sizes. D6 revised:
   SparseStack and OSNAP deferred with no scaffold (§6.1). The prototype's unpublished manuscripts
   are dropped as sources (D16).
2. **The S2 design checkpoint, passed (2026-10-15).** The predicates of S0 and S1 had met the
   Gaussian and Haar families; S3 to S7 were built on them unchanged.
3. **The pseudo-condition number (2026-10-14, `503070b`).** `conditionNumber` is renamed
   `pseudoConditionNumber` across the Matrix layer, with deprecated aliases: it ignores zero
   singular values, so it is the classical `σ_max/σ_min` only at full column rank. S0's
   preconditioning theorems use the new name.
4. **`Matrix.instSecondCountableTopology` (2026-10-14, `503070b`).** Mathlib has no second
   countability instance for matrices, so `Measurable.add` and `AEMeasurable.add` failed on
   matrix-valued functions; the instance is recorded beside deviation 12.

### 4.2 The orchestrator's

Each was recorded in the note cited and reviewed by a Fable agent before skeletons. **§2 kind**
marks a decision that fixes an interface or amends a maintainer-approved decision and was taken
without a stop; there are three (items 14, 15, 18).

S0 and S1 (2026-10-14):
1. Brief D1, D2: the OSI is added. `IsSubspaceInjection` names the lower half (the `lower` field
   of `IsSubspaceEmbedding`), with `IsIsotropicSketch`, `HasSubspaceInjection`,
   `IsObliviousSubspaceInjection` after CEMT. Not costly to reverse; its consumers are LowRank's
   range finder, Nyström and constant-factor sketch-and-solve.
2. S1 Q1: failure events negate the guarantee (`{c < X}` for `X ≤ c`); thresholds stay
   non-strict. Added to the brief's §3.
3. S0 Q1 to Q4: sketch-and-solve for any `U` whose range contains `range A` and `y`;
   preconditioning for any `M` with `HasOrthonormalCols (S A M)`; every minimizer, through
   `IsLeastSquaresSolution`; `IsSubspaceInjection` a `def`, not an `abbrev`.
4. S1 Q2, Q3: AMM over `ℝ` only, constant `ε` (over `ℂ` the JL moment gives only `√2 ε`,
   sharply); `HasJLMoment` takes `p : ℝ`. Q4: oblivious constructors over orthonormal
   `U : Matrix n p 𝕜`. Q5: `FixedSubspace.lean` split from `Oblivious.lean`.

S2 (2026-10-14, reviewed the same day):
5. Q1: no new Gaussian or Haar sketch law (`gaussianSketch` waits for a consumer holding `S`).
   Q3: JL in Dasgupta–Gupta form for every `ε ≥ 0`. Q4: JL moment at `p = 2` only, exact.
6. §8 items 2 and 3, replacing Q6: the Haar upper half is the deterministic `n/k` (`Q Qᴴ ≤ 1`);
   the lower half near `k = n` goes through the complement `Q⊥`, an incomparable shape kept beside
   the transfer shape (rule 4).

S3 (2026-10-15):
7. Q1: the sub-Gaussian OSE goes through JL plus a net; R3's rows route is dominated in every
   regime and dropped (rule 6). This amends D12 (a part (b) decision) in the brief.
8. Q2: Bernstein for centred squares, not Hanson–Wright. Q3: `subgaussianJLConstant` in
   Vershynin's two-regime shape. Q5: entries through a bridge, not twins.
9. Q6, decided yes: Rademacher with Gaussian constants (Achlioptas), through a rows theorem for
   `E ⟨X, x⟩⁴ ≤ 3 ‖x‖⁴` and the new lower log bound for `-1 < u ≤ 0`; the Bernstein sign JL is not
   dominated (better for `ε ≳ 1.43`) and both docstrings say so.

S4 (2026-10-15):
10. §8 item 1, the **law-definition pattern**: a law whose primitive randomness lives on a data or
    sketch index is the pushforward of its constructor with the needed measurable space fixed by
    `letI := ⊤` inside the body, and its finite-mixture form is a lemma; no statement carries an
    instance on the index. D4 unamended; adopted as the pattern for S5, S6 and S7. The draft's
    mixture definition was rejected on review (its reason was false).
11. Q3: tails in `U.rank` for any `U` (the dominant form, rule 6). Q4: simplified Chernoff
    exponents only. Q5: `coherence` named. Q6 with §8 item 6: the AMM identity takes the support
    condition `p i = 0 → A i = 0 ∨ B i = 0`, not `hpos`; §8 item 3 adds the D2-shaped AMM tail.
12. Q7 and Q8, deferred: sub-isotropy for S1's CEMT tails, and spectral-norm AMM (§6.1).

S5 (2026-10-15):
13. Q1: four files, adding `UniformInjection` and `ChernoffWithoutReplacement` to the brief's two.
    Q2: Probability statements carry `[MeasurableSpace n] [MeasurableSingletonClass n]` on the
    population index; Sketching statements do not. Q3 with §8 item 9: the comparison in a real
    Banach space for any continuous convex `f` on a closed convex set (D10's finite-dimensional
    space is an instance). Q4: the Hoeffding kernel private. Q9: the law's name
    `samplingSketchWithoutReplacement`.

S6 (2026-10-15):
14. **§2 kind.** Q1, decided as (iii): the flattening constant comes from the general
    Hsu–Kakade–Zhang tail over `𝕜` (a new Probability theorem), giving `β (d + 2√(dt) + 2t)` over
    `ℝ` and `ℂ` alike with no field factor. It fixes the constant of every SRHT statement; the
    note flagged it hard to reverse.
15. **§2 kind.** Q2, decided as (c) packaged as an interface: `IsBoundedOrthonormal F β`
    (`HasOrthonormalCols F` and `card n * ‖F i j‖² ≤ β`) replaces D11's literal hypothesis and
    Mathlib's `IsHadamard`, admitting the discrete cosine and Hartley transforms (`β = 2`); a new
    interface in the Matrix layer, with deviation entry 18 (§5).
16. Q3 with §8 item 13: laws `srht k F` and `srhtWithReplacement k F`, sketch index first, amending
    D14's `srht H k`. Q4: the flatten-then-sample transfers are public, generic in the random
    unitary. Q5: the sections lemma goes to `ForMathlib`. Q6: sizes reuse S4's at
    `L = β · srhtRowBound n d (δ/2)`, no `srhtSize`. Q8: no Walsh or Fourier family twins.
17. Skeleton note: both transfers take `hδ₁ : 0 ≤ δ₁` (false without it).

S7 (2026-10-15):
18. **§2 kind.** Q1 with §8 item 2: CountSketch's law is over `𝕜` with real signs coerced, as
    `srhtMatrix` is. It amends the field column of D3, a maintainer-approved table; the brief
    carries the dated amendment under D3. The review judged it not hard to reverse (`𝕜 = ℝ` is an
    instance), but it changes a maintainer decision.
19. Q2: the trace form is the primary exact identity, the AMM and Gram forms its instances. Q4
    with §8 item 4: the OSE's `(d² + d)/(m ε²)` is the proof's constant and is not attributed.
    Q5: `countSketchRows` named; the JL size inline as Woodruff's. Q6: AMM over `𝕜` directly
    (twice as good over `ℂ` as S1's route). Q7: the collision probability is a public Probability
    lemma with general weights. Q8: full independence only. §8 item 11:
    `DiscreteMeasurableSpace.eq_top` replaces S6's private copy.

## 5. Mathlib deviations

| Entry | Deviation | Status |
|---|---|---|
| 12 (companion) | `Matrix.instSecondCountableTopology`, the instance Mathlib lacks, beside the global matrix σ-algebra | maintainer, 2026-10-14; deleted when Mathlib has it |
| 18 | `IsBoundedOrthonormal F β` in place of `Matrix.IsHadamard` as the SRHT hypothesis: strictly weaker (admits DCT and DHT), generality not convenience | orchestrator, S6 Q2; bridge `Matrix.IsHadamard.isBoundedOrthonormal_inv_sqrt_smul` and the Walsh and Fourier instances proved |

Everything else is used as Mathlib has it: `HasLaw`, `Measure.pi`, `uniformOn` (on injections,
D10), the Loewner order, `ConvexOn.map_integral_le`.

## 6. Open work

### 6.1 Deferred, and what it needs

1. **SparseStack and OSNAP** (D6; brief §4a, carried forward here as the entry for the round that
   takes them up). Ledgered: 1671 prototype declarations (`Bands/`, `FockModel/`,
   `IIDComparison/`, `FiniteLaw/`, `MomentMethod/` except the Markov step, `SparseStack*`,
   `UniformSparse`, `SparseLaws`, `SparseEmbedding*`, `SparseFiniteIndex`) plus the three
   SparseStack tails of `GramTail.lean`. Already supplied: `HasGramTraceMoment` at general `q`,
   both oblivious predicates, `IsIsotropicSketch`, the trace-moment Markov step, the hollow Gram
   identity and CountSketch's exact second moments, the uniform-injection law and the
   convex-order comparison in the generality the sparse comparison needs, the collision lemma.
   - Route 1 (an OSE through trace moments; the prototype's; Cohen 2016 is its published analogue,
     not in hand) still needs: the comparison with an i.i.d. model,
     `E tr G_sparse^{2q} ≤ c^{4q} E tr G_iid^{2q}` with `c < 1.582`, by a sign-symmetric coupling
     on S5's comparison (and, for OSNAP, a fill/thin coupling); **moment bounds for the i.i.d.
     sparse model**, the main gap, which in the prototype's proof needs an orthonormal
     product-polynomial basis of `L²` of a finite product law, the trace moment as a vacuum matrix
     element, and a ladder bound for graded operators, or else a public decoupling inequality and
     matrix Khintchine or Rosenthal bounds for sparse bounded coefficients; no published proof of
     the prototype's general-parameter bound is in hand, so the later round chooses one first;
     real-valued named parameters in place of the prototype's rounded `q`, `s`, `m`.
   - Route 2 (an OSI through Gaussian comparison; CEMT's, from Tropp 2025, not in hand) needs
     Tropp's minimum-eigenvalue comparison theorem, self-adjoint Gaussian models (GOE, or GUE with
     the complex Gaussian laws) with `E λmax ≤ 2√d` and the weak variance, and CountSketch's second
     moment in CEMT's Lemma B.1 form (S7 has the exact trace form, which contains it). Route 2
     gives only the injection; sketch-and-precondition needs Route 1.
   - OSNAP has an OSE only through Cohen 2016 at `k = O(d log d)`; CEMT give no OSI for it.
2. **Limited independence** (S7 Q8; brief §4a item 3). Woodruff's Theorems 9 and 14 hold for a
   pairwise-independent hash and 4-wise independent signs, and S7's proofs use only those moments.
   It needs a `k`-wise independence predicate on the marginals of a `Measure`; with it, S7's
   theorems are restated on it and the current ones become corollaries at `countSketch`.
3. **Spectral-norm AMM by sampling** (S4 Q8). MT §7.3 and Tropp 2015 §6.4 give it through matrix
   Monte Carlo; the rectangular Bernstein it needs exists. About 150 lines; no consumer of the
   next rounds asks for it yet.
4. **Sub-isotropy for S1's CEMT tails** (S4 §7 Q7, §8 item 10; an S1 interface question). The
   three fixed-`U` CEMT tails use `IsIsotropicSketch` only through `E ‖S M‖_F² ≤ ‖M‖_F²`. A
   sampling sketch with zero weights has `E Sᴴ S = diagonal 1_{p > 0} ≤ 1`, which suffices. The
   change: replace `hiso` by `MemLp 2` entries plus `∫ (S ω)ᴴ S ω ≤ 1`, or by a predicate with that
   field, under its own §5.4 review. Until then, mixing `p = (ℓ/d + 1/n)/2` restores isotropy at
   `L = 2d` (docstring of `isIsotropicSketch_of_hasLaw_samplingSketch`).
5. Smaller deferrals, each waiting for a consumer: AMM over `𝕜` with `√2 ε` for the JL-moment
   families (S1 Q2; S7 has its own); the JL moment at `p ≠ 2` (S2 Q4); named `gaussianSketch` and
   `haarSketch` laws (S2 Q1); Haar sizes and a sharp Haar embedding near `k = n` (S2 Q6, §6);
   Chernoff source-form exponents and Tropp's `(1 + ι) d log d` SRHT regime (S4 Q4, S6 §6);
   an `IsIncoherentSubspaceInjection` predicate when SparseRTT brings a second sampler (S6 Q4);
   complex Steinhaus signs for HMT's SRFT and for CountSketch (S6 §6, S7 §6); reproving R3's
   sub-Gaussian rows theorem from the JL-plus-net route, which dominates it, keeping its name
   (S3 Q1, not done).

### 6.2 Citation locators still to verify

- **Tropp 2011a** (`Tropp2011a`, the SRHT paper; not in hand): every docstring cites it by key
  only. To check: Theorem 2.2 (matrix Chernoff without replacement), Lemma 3.3 (flattening,
  secondhand through CEMT), Lemma 3.4 (uniform sampling, secondhand through MT), §3.3 (the lower
  bound, through CEMT), Theorem 3.2 (as HMT Remark 11.1 cites it), and the main theorem's number
  (S5 §8 item 3, S6 Q9 and §8 item 5).
- **Hoeffding 1963** (`Hoeffding1963`): Theorem 4, the comparison for continuous convex `f`;
  cited without a number (S5 §8 item 3).
- **Gross and Nesme 2010** (`GrossNesme2010`, arXiv:1001.2738): the number of the matrix
  comparison; cited without one.
- **Boucheron, Lugosi and Massart 2013**, §2.4 for the sub-gamma Chernoff inversion
  (`measureReal_ge_le_exp_neg_of_mgf_le`): the locator came from the review and was not checked
  against the book; the docstring cites the key without it (S6 skeleton notes).
- **Drineas, Kannan and Mahoney 2006**, Lemma 4 and Theorem 1 (column-row sampling): cited by
  name only; MT §7.1 is the confirmed citation for the estimator (S4 Q8).
- **Nelson and Nguyen 2013**: D12 attributed `(d² + d)/(δ ε²)` to them; Woodruff's Theorem 9
  confirms only `O(d²/(δ ε²))`, so the OSE docstring states the constant as the proof's and does
  not attribute it (S7 §8 item 4). Meng and Mahoney 2013 likewise not in hand.
- **Vershynin**: the PDF in hand is the 2020 draft; section numbers agree with the 2018 print,
  theorem numbers (Theorem 4.6.1, Lemma 5.3.2, Exercise 5.3.3, Theorems 2.8.1, 6.1.1) are taken
  from the draft and cited as "2020 draft" until checked against the print (brief §7.1).
- Also not in hand, cited by name with locators to confirm: Dasgupta and Gupta 2003 (Lemma 2.2,
  Theorem 2.1), Achlioptas 2003 (Theorem 1.1; key added), Kane and Nelson 2014 (the JL moment
  property), Hsu, Kakade and Zhang 2012 (Theorem 2.1), Clarkson and Woodruff, Thorup and Zhang,
  Charikar, Chen and Farach-Colton, Foucart and Rauhut (bounded orthonormal systems), Ailon and
  Chazelle, Strassen 1965.

### 6.3 Next-round candidates

- Solvers: sketch-and-solve and sketch-and-precondition are S0 composed with any family's tail;
  Blendenpik through the SRHT OSE; constant-factor sketch-and-solve through any OSI.
- LowRank: the range finder, Nyström and generalized Nyström through the OSI and S1's form of CEMT
  Lemma 2.1; HMT §11 with the SRHT test matrix (`IsBoundedOrthonormal.transpose`,
  `.conjTranspose` carry the hypothesis to HMT's orientation, S6 §8 item 11); the prototype's
  `LowRank/Nystrom/SketchedRegression.lean` (`error_decomp`, `frobSq_error`) should cite S0's
  matrix error formula when it is ported.
- Estimation: Hutch++ and XTrace through AMM and the JL moment.
- The deferred items of §6.1.

## 7. Wrap-up refactors and process notes

- **Registration** (`e725d6b`): the round's modules entered `NLAlib.lean`; unused instance
  arguments dropped for the CI lint.
- **Wrap-up 1** (`4e75edb`): the side files merged into their homes: `ChiSquareTails` into
  `ChiSquare` (Laurent–Massart and the small ball reproved from the new tails, names kept; three
  private copies dropped), `SquareSum` into `SubGaussian/Square`, `IndependentRows` into `Law`,
  `NormMatrix` into `SubGaussianVector/Norm` (`measure_norm_sq_ge_le` reproved from the matrix
  form). One public home for the log inequalities (`ForMathlib/.../Log/Deriv.lean`: the cubic
  bound for `u > -1`, the quadratic and `-log (1 - u)` bounds, `log 9 ≤ 9/4`) and
  `Finset.exists_le_lt_of_forall_lt` (shared by R3 and the net step); the sphere-invariance
  lemma `uniformSphereVector_map_conjTranspose_mulVec_eq` made public; `Oblivious.lean`'s private
  Fubini helper reproved from the sections lemma; the result id `hsu-kakade-zhang` moved to
  `measure_norm_mulVec_sq_ge_le`.
- **Wrap-up 2** (`a0f9b23`): `JohnsonLindenstraussNet` merged into `JohnsonLindenstrauss`
  (`HasJLProperty.hasSubspaceEmbedding`, `.isObliviousSubspaceEmbedding`, and the public
  unit-vector reduction `exists_norm_eq_one_and_norm_mulVec_sq_sub_norm_sq_eq`); `Haar.lean`
  split by topic into `Haar` and `HaarEmbedding`, with the public Gram identity
  `conjTranspose_mul_self_sqrt_card_div_smul_conjTranspose_mul`; duplicated helpers unified as
  public lemmas: `two_mul_exp_le_of_jlDim_le`, `norm_inv_sqrt_card_smul_sq`,
  `norm_inv_sqrt_card_smul_mulVec_sq`, `HasOrthonormalCols.isSubspaceInjection_mul_iff`,
  `.isSubspaceEmbedding_mul_iff`, `hasSubspaceEmbedding_of_rank_eq_zero`,
  `leverageScore_le_mul_const_inv_card`, `pos_of_leverageScore_le_mul_inv_card`,
  `two_mul_mul_exp_le_of_samplingSize_le`, `mul_exp_le_of_samplingInjectionSize_le`,
  `sum_const_inv_card`, `IsBoundedOrthonormal.one_le`, `hasOrthonormalCols_replicateCol`,
  `measurable_inv_norm_smul`, six Rademacher-in-`𝕜` facts; `SRHT.lean`'s private
  `measurableSpace_eq_top` replaced by `DiscreteMeasurableSpace.eq_top`; `RowSampling.lean`'s
  docstrings in LaTeX. File moves change no ledger names.
- **Skeleton rule.** Temporary skeleton files (`ChiSquareTails`, `IndependentRows`, `SquareSum`,
  `NormMatrix`, `JohnsonLindenstraussNet`) kept `sorry` out of proved files; all merged at the
  wrap-ups.
- **False statements caught before or during proofs.** `HasSubspaceEmbedding.hasSubspaceInjection`
  without a finite measure (S1 §8 item 2); "for `ε ≥ 1` the lower JL event is null" (false at
  `ε = 1` for signs, S3 §8 item 1); `samplingSize_mono` without a range hypothesis (S4 skeleton
  notes); the SRHT transfers without `0 ≤ δ₁` (S6 skeleton notes); S7's claim that the transpose
  terms are at most their conjugate-transpose counterparts over `ℂ` (S7 §8 item 1) and a size
  clause at `card k = 1` (item 8).
- **Delegation.** Design notes and skeletons drafted by Opus agents from the orchestrator's
  briefs, each note reviewed by a Fable agent before its skeleton, proofs by Opus agents one file
  at a time, ledger and registration passes by Sonnet agents.
- **Final check.** `TMPDIR=/tmp/claude-1000/p0 scripts/stage_check.sh`, 2026-10-15, after the
  ledger pass:

  ```
  250 proved modules; 0 not yet
  build: Build completed successfully (3818 jobs).; warnings: 0
  audited 6015 declarations reachable through import NLAlib; 0 violations
  -- Found 0 errors in 4271 declarations (plus 1744 automatically generated ones) in NLAlib with 14 linters
  -- All linting checks passed!
  46 bibliography keys; 0 problems
  ```
