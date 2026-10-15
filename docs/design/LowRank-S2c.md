# Design note: LowRank stage S2c, a measurable best rank-k approximation

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decision of 2026-10-15,
"Measurable truncation": a stage S2c supplies a measurable best rank-$k$ approximation map and
instantiates every selector-hypothesis theorem, the spectral truncated RSVD, MT 14.1's expectation
form and truncated GN, so that they become usable), `docs/design/LowRank-S2a.md` (§7 Q3 and §8 items
1, 2 and 15: the selector form, decided as option (a), and option (c), redefining `truncatedSVD`,
"not done now"), `docs/design/LowRank-S3.md` (§3.0 "Measurability of truncated outputs, plainly",
§8 items 5, 6 and 18(iii); S3's selector theorems L8, L9, U2 are proved and registered in
`LowRank/Random/RangeFinder.lean` and `LowRank/Gaussian/RangeFinder.lean`) and
`docs/design/LowRank-S5.md` (§3.0 item 2; its selector theorems NL7, NL8, NU2, NU4, NI4 are drafted,
not reviewed, not written). S6 has no note yet. Over `𝕜`, every shape, rank and truncation rank;
the Gaussian corollaries are real, as the theorems they instantiate. Reviewed 2026-10-15 (2 medium,
11 low, 2 verdicts with no change), amendments in §8, which overrides §0 to §7 where they disagree
(§3 stays as drafted); all accepted, none rejected, five overtaken by the maintainer's change of
plan (§8 item 1). **Decided (maintainer, 2026-10-15): `truncatedSVD` is redefined from a chosen
thin SVD, the lexicographically least one (`svdU`, `svdV`), and is then Borel measurable
(`measurable_truncatedSVD`); no `measurableTruncatedSVD` is added.** The "Additive" and "One new
definition" departures below, Q1, Q2 and Q6 are superseded (§8 items 1, 2, 11). Final count
(§8 item 14): 23 new public declarations (two definitions, one instance) and one redefinition,
about 600 lines, plus K15 to K19 in S5 and K20 in S6.

Departures from the brief, each argued below:
- **Additive; `truncatedSVD` is not redefined.** A selection theorem is measure theory, and the
  Matrix layer has none (maintainer, 2026-10-14: measurability belongs to Probability), so a
  measurable map obtained from one cannot become the definition of a Matrix-layer object. An
  explicit Matrix-layer formula could (§3.1, route (b)), at about two and a half times the cost and
  with a rewrite of a finished, registered file's definition (Q1, Q3).
- **One new definition**, `measurableTruncatedSVD A k`, beside the existence theorem
  `exists_measurable_isBestRankApprox`, so that one fixed measurable choice can be named in
  statements and inside later algorithm definitions (Q1, Q2). It is a second function for "a best
  approximation of rank at most $k$"; the note argues why that is not a second spelling of
  `truncatedSVD` (§1) and leaves the decision to the maintainer (Q1, hard).
- **S5's and S6's corollaries are specified here and written there.** The S5 theorems exist only in
  a draft note and S6 has no note, so S2c cannot add corollaries to them. S2c writes S3's three
  (K12 to K14) and the measurability of Nyström and generalized Nyström (K10, K11), gives S5's five
  corollaries their signatures (K15 to K19) and S6 a template (K20), and asks that S2c be proved
  before S5's skeleton (Q5).
- **The selection theorem is general and lives in `ForMathlib`** (K0): a closed set
  $S \subseteq X \times Y$ with nonempty sections lying locally inside compact sets has a Borel
  measurable section. It is the special case of Kuratowski–Ryll-Nardzewski that the
  best-approximation set satisfies, and it needs no measurable-correspondence theory; full KRN is
  additive later (Q4).
- **Tails need nothing.** S3's P6 and S5's NP6 take no measurability hypothesis and are instantiable
  today. The success-set forms that measurability would add are not stated (§6).

**Mathlib check.** Mathlib has no measurable selection theorem. `grep -i` for Kuratowski,
Ryll-Nardzewski, "measurable selection", `exists_measurable_selection` and `measurable_argmin` finds
only the Kuratowski embedding (`Topology/MetricSpace/Kuratowski.lean`) and
`Probability/Decision/BayesEstimator.lean`, whose module docstring says "Once Mathlib has measurable
selection theorems, we will be able to prove `HasArgminEstimator` under general conditions": the
measurable argmin is a hypothesis there for exactly this reason. Related but not selections:
`MeasurableSet.exists_measurable_proj` (a measurable retraction onto a measurable set),
`exists_measurable_piecewise` (countable gluing), `measurable_find`, the analytic-set and
Lusin–Souslin results (images, not sections). What K0's proof uses: `TopologicalSpace.denseSeq`,
`denseRange_denseSeq`, `Metric.infDist`, `Metric.infDist_lt_iff`, `IsOpen.exists_iUnion_isClosed`,
`TopologicalSpace.metrizableSpaceMetric`, `measurable_find`, `measurable_of_tendsto_metrizable`,
`cauchySeq_of_le_geometric_two`, `IsCompact.tendsto_subseq`, `tendsto_nhds_of_cauchySeq_of_subseq`.

**Missing infrastructure.** Below the Matrix layer: the selection theorem (K0). In the Matrix layer:
the two degenerate cases of `IsBestRankApprox` (K1, K2) and the closedness of the set of best
approximations (K3). In Probability: the measurable choice and its API (K4 to K9), and the
measurability of `generalizedNystrom` and `nystrom` in the test matrices (K10, K11), which S5's and
S6's corollaries need and the library does not have (searched: no `measurable_nystrom`,
`measurable_generalizedNystrom`, `measurable_obliqueProjector`). Nothing from S5 or S6 is needed
for S2c's own statements.

## 0. Scope and consumers

$\mathbf{A}$ : `Matrix m n 𝕜`, a truncation rank $k : \mathbb{N}$ (any value), $\llbracket
\mathbf{A}\rrbracket_k$ = `truncatedSVD A k`, a `Classical.choose` of a singular value decomposition
for each matrix, with no measurability in $\mathbf{A}$. A best approximation is S2a's
`IsBestRankApprox A k Y`. The random outputs are S0's `rsvd A Ω`, `nystrom H Ω`,
`generalizedNystrom A Ω Ψ` at a random test matrix `X : Ω → Matrix n l 𝕜` (and `Ψ : Ω → Matrix m p 𝕜`
for GN). The selector theorems take `(hY : ∀ ω, IsBestRankApprox (Â ω) k (Y ω))
(hYm : AEStronglyMeasurable Y μ)`, and no `Y` satisfying both can be produced today. S2c produces one
for every random output at once: `Y ω = measurableTruncatedSVD (Â ω) k`, measurable as soon as `Â` is.

| Item | Consumers |
|---|---|
| K0, measurable selection from a closed set with compact sections | K4; later, any measurable choice the library needs: SVD factors or eigenvector frames (the set of SVDs with sorted singular values is closed with compact sections), a measurable minimiser of rank-constrained regression (S7's Woodruff Theorem 47 check), Mathlib's `HasArgminEstimator` (upstream) |
| K1, K2, the degenerate cases of the predicate | K8, K9; S3's and S5's exact-recovery branches of selector statements ($\operatorname{rank}\mathbf{H} \le k$ forces $\mathbf{Y} = \mathbf{H}$); users |
| K3, best approximations form a closed set | K4; users taking limits of best approximations (perturbation arguments) |
| K4 to K9, `measurableTruncatedSVD` and its API | K12 to K20; S7 (OSI forms of the same expectations); Solvers (a randomized Nyström preconditioner $\llbracket\hat{\mathbf{H}}\rrbracket_k$ defined as a function of $\omega$ must be a measurable truncation to be a random variable); users with any random output to truncate |
| K10, K11, measurability of GN and Nyström in the test matrices | K15 to K20; S5's and S6's law-free companions (their current routes measure the error through the range finder, these measure the output) |
| K12 to K14, S3 instantiated | users of the truncated RSVD in spectral norm; S7 (comparison with the OSI forms) |
| K15 to K19, S5 instantiated (written in S5's files) | users of fixed-rank Nyström (MT Theorem 14.1); Solvers |
| K20, S6 template (written in S6's files) | users of truncated GN |

Not in S2c: a redefinition of `truncatedSVD` (Q1); the gap-case bridge "`measurableTruncatedSVD`
equals `truncatedSVD` when $\sigma_{k-1} > \sigma_k$" (Q7); full Kuratowski–Ryll-Nardzewski for
weakly measurable correspondences (Q4); success-set tails (§6); anything about S6 beyond the
template.

## 1. Objects

**New definition: `measurableTruncatedSVD A k`** (K5), in `Probability/Measurability/Matrix.lean`: a
best approximation of $\mathbf{A}$ of rank at most $k$, chosen once for all $\mathbf{A}$ so that the
choice is a Borel measurable function of $\mathbf{A}$. It is defined as `(exists_measurable_isBestRankApprox k).choose A`.

*Why a definition and not only the existence theorem.* With K4 alone a user writes
`obtain ⟨T, hTm, hT⟩ := exists_measurable_isBestRankApprox k` and applies a selector theorem, which
works inside one proof. It does not work in a statement or a definition: a later theorem about "the
expected error of the truncated output" has to name the output, and an algorithm defined in the
library as a function of $\omega$ (a randomized preconditioner built from
$\llbracket\hat{\mathbf{H}}\rrbracket_k$, a streaming estimator) has to pick a truncation inside its
body. To be a random variable it must pick a measurable one, and to be composable (an expectation
and a tail about the same estimator, S6's assembly of several lemmas about one $\mathbf{Y}$) it must
pick the same one everywhere. Mathlib's precedent is `AEMeasurable.mk`, a named measurable
representative chosen from an existence statement.

*Why it is not a second spelling of `truncatedSVD`.* The two are different functions: under ties
they may take different values, and neither is defined from the other. They agree wherever the best
approximation is unique ($k = 0$, $\operatorname{rank}\mathbf{A} \le k$, a gap $\sigma_{k-1} >
\sigma_k$), because both are best approximations. CONTRIBUTING §1 rule 4 targets twins and
re-definitions of one object; this is one object (a best rank-$k$ approximation) with a property
(measurability in $\mathbf{A}$) that the existing choice does not have and cannot be proved to have.
The cost is real: the library has two named best approximations, and every statement must pick. The
rule below fixes the pick. This is Q1, for the maintainer.

*Could it equal `truncatedSVD` by construction?* Not additively. `truncatedSVD` is
`Classical.choose` of `exists_isSVD` for each matrix; no theorem can identify it with any particular
best approximation under ties, so no measurable map can be proved equal to it, and its measurability
is not provable from the definition. The only way to make them one function is to redefine
`truncatedSVD`, which is possible only through an explicit Matrix-layer formula (§3.1 route (b); Q1
option (c), Q3).

**Rule for statements** (a §5.3 amendment, two reviews):
- choice-free quantities (every unitarily invariant norm of $\mathbf{C} - \llbracket\mathbf{C}
  \rrbracket_k$; the Frobenius error of truncated RSVD; the trace error of truncated Nyström) are
  stated with `truncatedSVD`, as now;
- choice-dependent quantities under an integral (the spectral error of truncated RSVD and Nyström,
  both errors of truncated GN) are stated twice: the selector form for any measurable choice
  (`hY`, `hYm`; it covers an algorithm's own measurable tie-break) and its instance at
  `measurableTruncatedSVD (Â ω) k`;
- pointwise and tail statements stay on `truncatedSVD` or on any best approximation, as now.

**§5.3 rows** (added by the PR that adds K5; two reviews):

| Concept | Spelling | Bridge |
|---|---|---|
| best rank-$k$ approximation (amended row) | as now (`truncatedSVD A k`; any best approximation `IsBestRankApprox A k Y`); **a measurable choice**, where a statement needs measurability in $\mathbf{A}$: `measurableTruncatedSVD A k`. Equal to `truncatedSVD A k` wherever the best approximation is unique | `isBestRankApprox_measurableTruncatedSVD`, `measurable_measurableTruncatedSVD`, `measurableTruncatedSVD_of_rank_le` |
| truncated outputs (amends S2a's row) | late truncation in the expectation of a choice-dependent error: `measurableTruncatedSVD (rsvd A (X ω)) k`, and likewise for `nystrom` and `generalizedNystrom`; everywhere else as now, `truncatedSVD (rsvd A Ω) k` | K12 to K20 |

The second row is a narrow exception to the maintainer's spelling rule "late truncation stays
`truncatedSVD` of the named output": the error is still $\mathbf{A}$ minus a truncation of the named
output, but the truncation is the measurable one. Recorded under Q1.

**Docstring notation** (CONTRIBUTING §6 item 5, notation table): no new symbol. The row "truncated
SVD (best rank-$k$ approximation)" keeps $\llbracket\mathbf{A}\rrbracket_k$ and adds "also for
`measurableTruncatedSVD`, with the Lean name in words nearby". The sources write
$\llbracket\cdot\rrbracket_k$ for "a best rank-$k$ approximation" without fixing the choice, so the
symbol is accurate for both; the sentence naming the Lean object says which (Q6).

**Mathlib.** Mathlib has no low-rank approximation and no measurable selection: no deviation. The
name `measurableTruncatedSVD` joins "Additions where Mathlib has nothing" in
`docs/design/Mathlib-deviations.md` (one name added to the paragraph, no numbered entry). K0 is an
upstream candidate in `ForMathlib`, declared at the root as `IsClosed.…`, its module docstring
saying so.

**Used directly.** Library: `IsBestRankApprox`, `isBestRankApprox_truncatedSVD`,
`isBestRankApprox_iff`, `IsBestRankApprox.frobNorm_sub`, `IsBestRankApprox.frobNorm_sub_le`,
`truncatedSVD_zero`, `truncatedSVD_of_rank_le`, `Matrix.rank_eq_zero`
(`ForMathlib/LinearAlgebra/Matrix/Rank.lean`), `frobNorm_eq_zero_iff`, `continuous_frobNorm`,
`norm_apply_le_frobNorm`, `isClosed_setOf_rank_le`, `SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD`
with `lpGauge_two_matrixNorm`, `measurable_pinv`, `measurable_rsvd`, `Matrix.instBorelSpace`,
`Matrix.instSecondCountableTopology`, `obliqueProjector`, `generalizedNystrom`, `nystrom`; S3's L8
`integrable_specNorm_sub_sq_of_isBestRankApprox`, L9
`integral_specNorm_sub_sq_add_frobNorm_sub_truncatedSVD_sq_le_of_isBestRankApprox`, U2
`integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`. Mathlib: the list under
"Mathlib check"; `isCompact_univ_pi`, `IsCompact.of_isClosed_subset`, `isClosed_le`,
`AEMeasurable.aestronglyMeasurable`, `Measurable.comp_aemeasurable`, `AEMeasurable.prodMk`.

**Mathlib search** ("searched, none" unless named): a measurable selection or uniformization
theorem (none; see above); a measurable argmin (none; `HasArgminEstimator` is a hypothesis); a
closed-graph or upper-hemicontinuity statement for minimisers (none); measurability of a spectral
projector of a varying Hermitian matrix (none; route (b) only).

## 2. Interfaces

None new. The selector interface is S2a's `IsBestRankApprox` with `AEStronglyMeasurable`, decided
in S2a §8 item 15 and unchanged; S2c supplies an instance of it. K0's hypotheses are raw conditions
on a set (closed, nonempty sections, local compact bound), spelled once, in the one theorem that
takes them; they are Mathlib's vocabulary, not an NLAlib interface. If a second selection theorem
appears (full KRN, Q4), its hypotheses are designed then.

## 3. Statement shapes

`namespace NLAlib` (K0: root namespace, `ForMathlib`), `open scoped Matrix`. Variables
`{𝕜 : Type*} [RCLike 𝕜] {m n l p : Type*}`, `[Fintype _]` on each; no `DecidableEq`. Probability
statements: `{Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → Matrix n l 𝕜}`. Docstrings
are shortened; the full ones are LaTeX throughout and carry the citations of §5.

### 3.0 Degenerate cases

Checked for every statement; the routes say where a case bites.
- *$k = 0$.* The only matrix of rank $0$ is $\mathbf{0}$ (`Matrix.rank_eq_zero`), so the best
  approximation is $\mathbf{0}$ (K1) and `measurableTruncatedSVD A 0 = 0` (K8), as `truncatedSVD_zero`.
  K14 at $k = 0$ reads $\mathbb{E}\|\mathbf{A}\|_2^2 \le \sigma_0(\mathbf{A})^2$, an equality.
- *$\operatorname{rank}\mathbf{A} \le k$*, which includes $k \ge \min(\lvert m\rvert, \lvert n
  \rvert)$ and $\mathbf{A} = \mathbf{0}$. The optimal error is $0$ (`truncatedSVD_of_rank_le`), so the
  only best approximation is $\mathbf{A}$ (K2) and `measurableTruncatedSVD A k = A` (K9).
- *Ties* $\sigma_{k-1}(\mathbf{A}) = \sigma_k(\mathbf{A})$ with $1 \le k < \operatorname{rank}
  \mathbf{A}$. The set of best approximations is infinite (S2a §8 item 2's example), and K5 picks
  one; nothing identifies it with `truncatedSVD A k`. Away from ties the two are equal, because the
  best approximation is unique there; that bridge is not stated (Q7).
- *Different truncation ranks.* K5's choices for $k$ and $k + 1$ are made independently: nothing
  relates their ranges. `truncatedSVD` is built from one SVD for every $k$; K5 is not. No S3 to S6
  statement compares truncations of one random output at two ranks (S5's NU4 compares with the
  population truncation $\llbracket\mathbf{H}\rrbracket_q$, which is choice-free in its norm).
- *Empty index types.* $m$ or $n$ empty: every matrix is $\mathbf{0}$, the set of best approximations
  is $\{\mathbf{0}\}$, K5 is $\mathbf{0}$, every corollary is $0 \le 0$ or its source's degenerate
  case. $l$ empty: `rsvd A X` $= \mathbf{P}_{\mathbf{0}}\mathbf{A} = \mathbf{0}$, so the truncation is
  $\mathbf{0}$; K12 and K13 hold as L8 and L9 do there; K14 excludes it by `hk`. In K0: if $X$ is
  empty the section is the empty function; $Y$ empty forces $X$ empty by `hne`.
- *Fields.* `RCLike 𝕜` is second countable and Borel, so `Matrix m n 𝕜` is a Borel, second
  countable, metrizable space (`Matrix.instBorelSpace`, `Matrix.instSecondCountableTopology`,
  Mathlib's `metrizableSpace_pi` through `inferInstanceAs` if instance search does not unfold
  `Matrix`). K12 and K13 are over `𝕜`; K14 is real, as U2.
- *Measurability of the test matrix.* The selector theorems L8 (and S5's NL7) need no measurability
  of `X`; their instances K12 (and K15) do, since $\omega \mapsto$ `measurableTruncatedSVD (rsvd A
  (X ω)) k` is measurable only through `X`. They take `hX : AEMeasurable X μ`, which the Gaussian
  statements get from `HasLaw`.

### 3.1 Construction routes assessed

The object to select from is, for each $\mathbf{A}$, the set
$$S(\mathbf{A}) = \{\mathbf{Y} : \operatorname{rank}\mathbf{Y} \le k,\ \|\mathbf{A}-\mathbf{Y}
\|_{\mathsf{F}} \le \|\mathbf{A}-\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}\}$$
(`isBestRankApprox_iff`). Both conditions are closed in $(\mathbf{A}, \mathbf{Y})$: the rank set by
`isClosed_setOf_rank_le`, the inequality because the optimal error is continuous in $\mathbf{A}$
(`SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD` at the Frobenius gauge). So the graph of
$S$ is closed (K3), every $S(\mathbf{A})$ is nonempty (Eckart–Young) and bounded,
$\|\mathbf{Y}\|_{\mathsf{F}} \le \|\mathbf{A}\|_{\mathsf{F}} + \|\mathbf{A}-\mathbf{Y}\|_{\mathsf{F}}
\le 2\|\mathbf{A}\|_{\mathsf{F}}$ (optimality against $\mathbf{0}$), locally uniformly in
$\mathbf{A}$.

**(a) A selection theorem (recommended).** A closed-graph correspondence with nonempty sections
that lie locally inside compact sets is upper hemicontinuous with compact values, hence weakly
measurable, and Kuratowski–Ryll-Nardzewski gives a Borel selection. Mathlib has no such theorem
(above), so S2c proves the special case it needs, K0, directly:
1. For closed $C \subseteq Y$, $\{x \mid S_x \cap C \ne \emptyset\}$ is closed (a tube argument
   over the compact $K \cap C$, from the local compact bound; no countability on $X$).
2. For open $W \subseteq Y$, $\{x \mid S_x \cap W \ne \emptyset\}$ is measurable: in a metrizable
   $Y$, $W$ is a countable union of closed sets (`IsOpen.exists_iUnion_isClosed`).
3. Kuratowski–Ryll-Nardzewski's recursion with a dense sequence $(y_i)$ (`denseSeq`): $f_0(x) =
   y_i$ for the least $i$ with $S_x \cap B(y_i, 1) \ne \emptyset$; $f_{j+1}(x) = y_i$ for the least
   $i$ with $S_x \cap B(y_i, 2^{-j-1}) \ne \emptyset$ and $d(y_i, f_j(x)) < 2^{-j} + 2^{-j-1}$. Each
   $f_j$ is measurable (`measurable_find` on step 2's sets and $f_{j-1}$'s preimages of balls),
   $d(f_j(x), S_x) < 2^{-j}$, and $(f_j(x))$ is Cauchy.
4. The limit exists (points of the compact $K_x \supseteq S_x$ lie within $2^{-j}$ of $f_j(x)$; a
   convergent subsequence and Cauchy give convergence), lies in the closed section $S_x$, and is
   measurable (`measurable_of_tendsto_metrizable`).

Then K4 is K0 at $X = Y =$ `Matrix m n 𝕜`, $S$ = K3's set. Size: K0 about 250 lines (the recursion
carrying its invariants is the bulk; estimate range 200 to 320), K3 about 20, K4 about 40. Risk:
the recursion's bookkeeping, not the mathematics. Gain beyond S2c: every later measurable choice in
the library (SVD factors, eigenvector frames, minimisers) is one closedness lemma away, and the
theorem is what Mathlib's `HasArgminEstimator` waits for.

**(b) An explicit piecewise formula.** With $\mathbf{G} = \mathbf{A}^{\mathsf{H}}\mathbf{A}$ and
$\tau = \sigma_k(\mathbf{A})^2$ (the first discarded value, so $k = 0$ needs no case),
- $\mathbf{P}_{>} = \mathbf{P}_{(\mathbf{G}-\tau\mathbf{I})^{+}}$, the projector onto the
  eigenvectors with eigenvalue above $\tau$: `rangeProjector` of the positive part, a continuous
  function of $\mathbf{A}$ (`Continuous.cfc`, or $\frac12(\mathbf{H} + (\mathbf{H}^{\mathsf{H}}
  \mathbf{H})^{1/2})$ through the private `continuous_sqrt_gram` of `Measurability/Matrix.lean`),
  so measurable by `measurable_rangeProjector`;
- $\mathbf{P}_{=} = \mathbf{I} - \mathbf{P}_{\mathbf{G}-\tau\mathbf{I}}$, the eigenspace of $\tau$,
  measurable likewise;
- the tie-break: with $a = \operatorname{rank}\mathbf{P}_{>} \le k$ and $\mathbf{D}_j$ the diagonal
  of the indicator of the first $j$ coordinates (`Fintype.equivFin n`), take the least $j$ with
  $\operatorname{rank}(\mathbf{P}_{=}\mathbf{D}_j) = \min(k - a, \operatorname{rank}\mathbf{P}_{=})$
  (the rank grows by at most one per step) and $\mathbf{\Pi}_t = \mathbf{P}_{\mathbf{P}_{=}
  \mathbf{D}_j}$: Gram–Schmidt of the projections of the standard basis vectors onto the tied
  eigenspace. Measurable on each of the countably many pieces $\{j(\mathbf{A}) = j\}$, which are
  Borel by `measurable_rank`; glued by `measurable_to_countable'` and
  `measurable_from_prod_countable_left`, the pattern of the private `measurable_of_continuousOn_fiber`;
- $\mathbf{Y} = \mathbf{A}(\mathbf{P}_{>} + \mathbf{\Pi}_t)$. When $\tau = 0$ the tie slots lie in
  $\ker\mathbf{A}$ and $\mathbf{Y} = \mathbf{A}$, so $\operatorname{rank}\mathbf{A} \le k$ needs no
  case either.

Correctness: $\mathbf{\Pi} = \mathbf{P}_{>} + \mathbf{\Pi}_t$ is an orthogonal projector of rank at
most $k$ commuting with $\mathbf{G}$, $\|\mathbf{A}-\mathbf{A}\mathbf{\Pi}\|_{\mathsf{F}}^2 =
\operatorname{tr}\mathbf{G} - \operatorname{tr}(\mathbf{\Pi}\mathbf{G})$ and
$\operatorname{tr}(\mathbf{\Pi}\mathbf{G}) = \sum_{\lambda_i > \tau}\lambda_i + (k-a)\tau =
\sum_{i<k}\sigma_i(\mathbf{A})^2$, then `isBestRankApprox_iff` with `frobNorm_sub_truncatedSVD_sq`.
The library has none of the spectral-projector facts this needs (the rank of $\mathbf{P}_{>}$ as a
count of sorted eigenvalues, its trace against $\mathbf{G}$, the range projector of a unitarily
diagonalised matrix): searched `Matrix/`, no spectral projector API. Size: about 400 lines of new
Matrix-layer spectral-projector API, 150 for the formula and its correctness, 80 for its
measurability, so 550 to 700 before the corollaries. Its one advantage is that it is a formula in
the Matrix layer, so it is the only route by which `truncatedSVD` could later be redefined to be
measurable (Q1 option (c)). Its tie-break is nested in $k$ (the $\mathbf{D}_j$ are nested), so it
could even keep `truncatedSVD`'s one-SVD-for-every-$k$ property.

**(c) Simpler routes, none simpler.**
- *Lexicographic minimisation* over $S(\mathbf{A})$: the first coordinate's minimum is lower
  semicontinuous (closed graph, compact sections), hence Borel; the second step minimises over a
  set whose graph is Borel but not closed, and its measurability needs measurable-correspondence
  theory, more than K0.
- *Minimisation over a countable dense set*: the minimum over a countable set of competitors is not
  attained in $S(\mathbf{A})$; making it so by a limit is K0's recursion.
- *A Mathlib `measurable_argmin`*: none exists (above).
- *A perturbation tie-break* ($\lim_{\varepsilon \to 0}$ `truncatedSVD (A + ε • B) k` for a fixed
  $\mathbf{B}$): not well defined at higher-order ties, and nothing about it is measurable.
- *A.e. measurability only* (the corollaries need only `AEStronglyMeasurable`): would follow from a
  null tie set, which is false (S2a §8 item 1, $\mathbf{A} = \mathbf{I}$).

**Recommendation: (a)** (Q3). About 450 lines for the whole stage against 650 to 800 for (b), the
generic theorem is reusable and upstreamable, and the correctness of the selection is free (it lands
in $S(\mathbf{A})$ by construction). The public statements K4 to K20 are the same under either
route, so (b) can replace K4's proof later if Q1(c) is ever taken.

### 3.2 `ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean` (1)

```lean
/-- **Measurable selection from a closed set with compact sections.** Let $S \subseteq X \times Y$
be closed, with every section $S_x = \{y \mid (x, y) \in S\}$ nonempty and locally uniformly inside
compact sets: each $x$ has a neighbourhood $U$ and a compact $K$ with $S_{x'} \subseteq K$ for every
$x' \in U$. If $Y$ is metrizable and second countable, there is a Borel measurable $f : X \to Y$
with $(x, f(x)) \in S$ for every $x$.
[KuratowskiRyllNardzewski1965]; [AliprantisBorder2006, Theorem 18.13]; there for weakly measurable
closed-valued correspondences into a Polish space, here the case of a closed graph with locally
compact sections, which is weakly measurable. Upstream candidate.
Result: measurable-selection -/
theorem IsClosed.exists_measurable_forall_prodMk_mem {X Y : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [TopologicalSpace Y] [MetrizableSpace Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {S : Set (X × Y)}
    (hS : IsClosed S) (hne : ∀ x, ∃ y, (x, y) ∈ S)
    (hK : ∀ x, ∃ U ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧ ∀ x' ∈ U, ∀ y, (x', y) ∈ S → y ∈ K) :
    ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ S
```

Label K0. Route: §3.1 (a), steps 1 to 4, under `letI := TopologicalSpace.metrizableSpaceMetric Y`.
Step 1 is a private lemma of the file (`isClosed_setOf_exists_mem_of_isCompact`, about 40 lines; it
is about closed maps, and is kept private because no second file needs it; it becomes public if
full KRN is added, Q4). The sequence $(f_j)$ is built by `Nat.rec` on the subtype of measurable
functions with $d(f_j(x), S_x) < 2^{-j}$; the limit is `limUnder atTop (f · x)`. Degenerate: $X$
empty (`isEmptyElim`); otherwise $Y$ is nonempty by `hne` and `denseSeq` applies. The sections are
closed as preimages of $S$ under $y \mapsto (x, y)$. Why the closed-graph form and not full KRN:
the closed-graph hypotheses are what a user can check (closedness of a predicate in
$(\mathbf{A}, \mathbf{Y})$, a norm bound), whereas full KRN asks for measurability of $\{x \mid S_x
\cap W \ne \emptyset\}$ for every open $W$, which a user would prove by step 2 anyway.

### 3.3 Matrix layer: `Matrix/Spectral/BestRankApprox.lean` and `Matrix/Perturbation/Continuity.lean` (3)

```lean
/-- The only best approximation of rank $0$ is $\mathbf{0}$. -/
theorem isBestRankApprox_zero_iff {C Y : Matrix m n 𝕜} : IsBestRankApprox C 0 Y ↔ Y = 0
/-- When $\operatorname{rank}\mathbf{C} \le k$, the only best approximation of $\mathbf{C}$ of
rank at most $k$ is $\mathbf{C}$ itself. -/
theorem isBestRankApprox_iff_eq_of_rank_le {C Y : Matrix m n 𝕜} {k : ℕ} (hk : C.rank ≤ k) :
    IsBestRankApprox C k Y ↔ Y = C
/-- **The best approximations form a closed set**: the pairs $(\mathbf{C}, \mathbf{Y})$ with
$\mathbf{Y}$ a best approximation of $\mathbf{C}$ of rank at most $k$ form a closed set, so a limit
of best approximations of convergent matrices is a best approximation of the limit. The truncated
SVD itself is not continuous (it jumps at ties $\sigma_{k-1}(\mathbf{C}) = \sigma_k(\mathbf{C})$);
this is the continuity that survives. -/
theorem isClosed_setOf_isBestRankApprox (k : ℕ) :
    IsClosed {p : Matrix m n 𝕜 × Matrix m n 𝕜 | IsBestRankApprox p.1 k p.2}
```

Labels K1, K2 (`BestRankApprox.lean`, after `isBestRankApprox_iff`), K3 (`Continuity.lean`, after
`SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD`). Routes. *K1:* (⇒) `h.rank_le` and
`Matrix.rank_eq_zero`; (⇐) `truncatedSVD_zero` and `isBestRankApprox_truncatedSVD`. *K2:* (⇒)
`h.frobNorm_sub`, `truncatedSVD_of_rank_le`, `sub_self`, `frobNorm_zero`, `frobNorm_eq_zero_iff`,
`sub_eq_zero`; (⇐) `isBestRankApprox_iff` with rank $\le k$ and error $0$. *K3:* rewrite the set by
`isBestRankApprox_iff` as the intersection of `isClosed_setOf_rank_le k` pulled back by
`continuous_snd` and `isClosed_le` of `continuous_frobNorm.comp (continuous_fst.sub continuous_snd)`
against `(SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD (lpGauge 2 one_le_two) k).comp
continuous_fst` (with `lpGauge_two_matrixNorm`). Degenerate: K1 and K2 are both true at
$\mathbf{C} = \mathbf{0}$ (both say $\mathbf{Y} = \mathbf{0}$); with $m$ or $n$ empty every statement
is about the one matrix $\mathbf{0}$.

### 3.4 `Probability/Measurability/Matrix.lean`: the measurable choice (8)

```lean
/-- **A measurable best rank-$k$ approximation exists**: there is a Borel measurable map $T$ with
$T(\mathbf{A})$ a best approximation of $\mathbf{A}$ of rank at most $k$ for every $\mathbf{A}$.
`truncatedSVD` is chosen separately for each matrix and is not known to be measurable; under ties
$\sigma_{k-1}(\mathbf{A}) = \sigma_k(\mathbf{A})$ the best approximation is not unique. -/
theorem exists_measurable_isBestRankApprox (k : ℕ) :
    ∃ T : Matrix m n 𝕜 → Matrix m n 𝕜, Measurable T ∧ ∀ A, IsBestRankApprox A k (T A)
/-- **The measurable truncated SVD** $\llbracket\mathbf{A}\rrbracket_k$: a best approximation of
$\mathbf{A}$ of rank at most $k$, chosen once for all $\mathbf{A}$ so that it is a Borel measurable
function of $\mathbf{A}$ (`NLAlib.measurable_measurableTruncatedSVD`). Being a best approximation,
it equals `truncatedSVD A k` wherever the best approximation is unique; under ties the two may
differ. Use it where a statement needs measurability in $\mathbf{A}$: the expectation of a
choice-dependent error of a truncated random output (the spectral error of truncated randomized SVD
and Nyström, both errors of truncated generalized Nyström). Choice-free quantities stay with
`truncatedSVD`. The choices for different $k$ are independent. -/
noncomputable def measurableTruncatedSVD (A : Matrix m n 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  (exists_measurable_isBestRankApprox k).choose A
/-- The measurable truncated SVD is a Borel measurable function of the matrix. -/
theorem measurable_measurableTruncatedSVD (k : ℕ) :
    Measurable fun A : Matrix m n 𝕜 => measurableTruncatedSVD A k
/-- **Eckart–Young for the measurable choice**: `measurableTruncatedSVD A k` is a best
approximation of rank at most $k$, so every result about best approximations applies to it. -/
theorem isBestRankApprox_measurableTruncatedSVD (A : Matrix m n 𝕜) (k : ℕ) :
    IsBestRankApprox A k (measurableTruncatedSVD A k)
@[simp] theorem measurableTruncatedSVD_zero (A : Matrix m n 𝕜) : measurableTruncatedSVD A 0 = 0
/-- At or above the rank the measurable truncation is the identity, as `truncatedSVD`. -/
theorem measurableTruncatedSVD_of_rank_le (A : Matrix m n 𝕜) {k : ℕ} (hk : A.rank ≤ k) :
    measurableTruncatedSVD A k = A
/-- Generalized Nyström $(\mathbf{\Omega}, \mathbf{\Psi}) \mapsto \mathsf{gn}(\mathbf{A},
\mathbf{\Omega}, \mathbf{\Psi})$ is a measurable function of the two test matrices. -/
theorem measurable_generalizedNystrom (A : Matrix m n 𝕜) :
    Measurable fun ΩΨ : Matrix n l 𝕜 × Matrix m p 𝕜 => generalizedNystrom A ΩΨ.1 ΩΨ.2
/-- Nyström $\mathbf{\Omega} \mapsto \mathsf{nystrom}(\mathbf{H}, \mathbf{\Omega})$ is a measurable
function of the test matrix. -/
theorem measurable_nystrom (H : Matrix n n 𝕜) :
    Measurable fun Ω : Matrix n l 𝕜 => nystrom H Ω
```

Labels K4 to K11, after `measurable_rsvd` (K10, K11 beside it) and before the polar factor. Routes.
*K4:* K0 at $X = Y =$ `Matrix m n 𝕜`, $S$ = K3's set; `hne` from `isBestRankApprox_truncatedSVD`;
`hK` with $U = \{\mathbf{A}' \mid \|\mathbf{A}'\|_{\mathsf{F}} < \|\mathbf{A}\|_{\mathsf{F}} + 1\}$
(open, `continuous_frobNorm`) and $K = \{\mathbf{Y} \mid \|\mathbf{Y}\|_{\mathsf{F}} \le
2(\|\mathbf{A}\|_{\mathsf{F}} + 1)\}$, compact as a closed subset of the product of closed balls
(`norm_apply_le_frobNorm`, `isCompact_univ_pi`, `IsCompact.of_isClosed_subset`); membership by
`hY.frobNorm_sub_le 0` and the triangle inequality. Instances: `Matrix.instBorelSpace` (so
`OpensMeasurableSpace`), `Matrix.instSecondCountableTopology`, and `MetrizableSpace` by
`inferInstanceAs (MetrizableSpace (m → n → 𝕜))` inside the proof (no global instance, CONTRIBUTING
§7). About 40 lines. *K5:* the definition. *K6, K7:* `.choose_spec.1`, `.choose_spec.2 A`. *K8:* K1
at K7. *K9:* K2 at K7. *K10:* unfold `generalizedNystrom` and `obliqueProjector` to $\mathbf{A}
\mathbf{\Omega}\,(\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}\mathbf{\Omega})^{+}\,\mathbf{\Psi}^{\mathsf{H}}
\mathbf{A}$; `measurable_pinv` composed with `Measurable.matrix_mul` and `.matrix_conjTranspose` of
`measurable_fst`, `measurable_snd`. *K11:* `nystrom H Ω = generalizedNystrom H Ω Ω`, K10 composed with
`measurable_id.prodMk measurable_id`. Degenerate: §3.0; K10 and K11 hold everywhere (`pinv` is total,
`measurable_pinv` is global).

How a user instantiates a selector theorem, in the module docstring: `hY := fun ω =>
isBestRankApprox_measurableTruncatedSVD _ k`, `hYm := ((measurable_measurableTruncatedSVD k).comp
(measurable_rsvd A)).comp_aemeasurable hX |>.aestronglyMeasurable` (as
`integrable_of_posSemidef_of_le` in `Probability/MatrixConcentration/Chernoff.lean` converts a
matrix-valued `AEMeasurable`).

### 3.5 S3 instantiated: `LowRank/Random/RangeFinder.lean` and `LowRank/Gaussian/RangeFinder.lean` (3)

```lean
/-- For a measurable test matrix and every finite measure, the squared spectral error of the
randomized SVD truncated measurably,
$\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2$ with the
truncation `measurableTruncatedSVD`, is integrable. The instance of
`NLAlib.integrable_specNorm_sub_sq_of_isBestRankApprox`. -/
theorem integrable_specNorm_sub_measurableTruncatedSVD_rsvd_sq [IsFiniteMeasure μ]
    (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => specNorm (A - measurableTruncatedSVD (rsvd A (X ω)) k) ^ 2) μ
/-- **Reverse Eckart–Young in expectation, measurable truncation**: for a measurable test matrix,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2 +
\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2 \le \sigma_k(\mathbf{A})^2 +
\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
the left truncation `measurableTruncatedSVD`, the right one `truncatedSVD` (the Frobenius error does
not depend on the choice). [Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a,
Proposition A.8]; [TroppWebber2023, p. 42]. -/
theorem integral_specNorm_sub_measurableTruncatedSVD_rsvd_sq_add_frobNorm_sub_truncatedSVD_sq_le
    [IsProbabilityMeasure μ] (A : Matrix m n 𝕜) (hX : AEMeasurable X μ) (k : ℕ) :
    ∫ ω, specNorm (A - measurableTruncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ +
        frobNorm (A - truncatedSVD A k) ^ 2 ≤
      singularValues A k ^ 2 + ∫ ω, frobNorm (A - truncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ
/-- **The expected spectral error of the truncated randomized SVD**: for a standard Gaussian
$n \times \ell$ test matrix $\mathbf{X}$ and $k + 2 \le \ell$,
$$\mathbb{E}\|\mathbf{A} - \llbracket\mathsf{rsvd}(\mathbf{A}, \mathbf{X})\rrbracket_k\|_2^2 \le
\sigma_k(\mathbf{A})^2 + \frac{k}{\ell - k - 1}\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k
\|_{\mathsf{F}}^2\,,$$
with the output truncated by `measurableTruncatedSVD`; for any other measurable choice,
`NLAlib.integral_specNorm_sub_sq_le_of_isBestRankApprox_of_hasLaw_gaussianMatrix`.
[Gu2015, Theorem 3.4]; [TroppYurtseverUdellCevher2017a, Proposition A.8];
[TroppWebber2023, p. 42]; there a remark on truncated outputs, here explicit.
Result: randomized-svd-expected-error -/
theorem integral_specNorm_sub_measurableTruncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix
    (A : Matrix m n ℝ) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (A - measurableTruncatedSVD (rsvd A (X ω)) k) ^ 2 ∂μ ≤
      singularValues A k ^ 2 +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * frobNorm (A - truncatedSVD A k) ^ 2
```

Labels K12, K13 (`Random/RangeFinder.lean`, after L8 and L9), K14 (`Gaussian/RangeFinder.lean`,
after U2). Routes: one term each, the source theorem at `Y := fun ω => measurableTruncatedSVD (rsvd
A (X ω)) k` with §3.4's `hY` and `hYm` (K14: `hX.aemeasurable`). Degenerate: inherited from L8, L9,
U2 (S3 §3.0), with §3.0 above for $k = 0$ and $\operatorname{rank}\mathbf{A} \le k$ (K8, K9 give
the exact values).

**Docstring edits in the same PRs** (registered files): L8, L9 and U2 replace "Not instantiable
yet: no measurable selector can be exhibited, ..." by "Instantiated at the measurable truncation by
K12 (K13, K14)"; the module docstring of `LowRank/Random/RangeFinder.lean` replaces its paragraph
"Measurability of the truncated output" (its last two sentences: "No such selector can be exhibited
yet ... These statements are the form a measurable selector will instantiate") by the instantiation
recipe and the names K12 to K14; `LowRank/Gaussian/RangeFinder.lean`'s module docstring lists K14.
The sentence "the expectation of the spectral error of that output itself is not stated" in U2
stays true of `truncatedSVD` and is kept.

### 3.6 S5 instantiated (specified here, written in S5's files) (5)

Each is the S5 selector theorem at `Y := fun ω => measurableTruncatedSVD (nystrom H (X ω)) k`,
`hYm` from K11. Hypotheses are those of the S5 statement, plus `hX : AEMeasurable X μ` where the
source takes none (NL7). Names follow S5 Q3: `_of_isBestRankApprox_nystrom` becomes
`_measurableTruncatedSVD_nystrom` in the place of the error.

```lean
theorem _root_.Matrix.PosSemidef.integrable_specNorm_sub_measurableTruncatedSVD_nystrom
    [IsFiniteMeasure μ] (hH : H.PosSemidef) (hX : AEMeasurable X μ) (k : ℕ) :
    Integrable (fun ω => specNorm (H - measurableTruncatedSVD (nystrom H (X ω)) k)) μ
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_measurableTruncatedSVD_nystrom_add_nuclearNorm_sub_truncatedSVD_le
    [IsProbabilityMeasure μ] (hH : H.PosSemidef) (hX : AEMeasurable X μ) (k : ℕ) :
    ∫ ω, specNorm (H - measurableTruncatedSVD (nystrom H (X ω)) k) ∂μ +
        nuclearNorm (H - truncatedSVD H k) ≤
      singularValues H k + ∫ ω, nuclearNorm (H - truncatedSVD (nystrom H (X ω)) k) ∂μ
/-- **The expected spectral error of truncated Nyström** (MT Theorem 14.1) ... with the output
truncated by `measurableTruncatedSVD`. [MartinssonTropp2020, Theorem 14.1];
[TroppYurtseverUdellCevher2017a, Theorem 4.1 (4.2)]. Result: randomized-nystrom-expected-error -/
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_measurableTruncatedSVD_nystrom_le_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) {k : ℕ}
    (hk : k + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - measurableTruncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      singularValues H k +
        (k : ℝ) / ((Fintype.card l : ℝ) - k - 1) * nuclearNorm (H - truncatedSVD H k)
theorem _root_.Matrix.PosSemidef.integral_specNorm_sub_measurableTruncatedSVD_nystrom_le_add_of_hasLaw_gaussianMatrix
    (hH : H.PosSemidef) (hX : HasLaw X (gaussianMatrix n l) μ) (k : ℕ) {q : ℕ}
    (hq : q + 2 ≤ Fintype.card l) :
    ∫ ω, specNorm (H - measurableTruncatedSVD (nystrom H (X ω)) k) ∂μ ≤
      singularValues H k + singularValues H q +
        (q : ℝ) / ((Fintype.card l : ℝ) - q - 1) * nuclearNorm (H - truncatedSVD H q)
-- K19, NI4's instance, with NI4's hypotheses (`hX`, `hXr`, `hk`) as S5 fixes them:
-- `Matrix.PosSemidef.integral_specNorm_sub_measurableTruncatedSVD_nystrom_le_of_isLeftUnitarilyInvariant`
```

`H` is real in K17 to K19, over `𝕜` in K15 and K16, as in S5. Labels K15 (beside NL7,
`LowRank/Random/Nystrom.lean`), K16 (beside NL8, same file), K17, K18
(beside NU2, NU4, `LowRank/Gaussian/Nystrom.lean`), K19 (beside NI4,
`LowRank/Gaussian/RotationInvariant.lean`). K17 and K19 carry NU2's and NI4's result id; K18 NU4's.
S5's docstrings replace "Not instantiable yet" by the name of the instance, and S5 §3.0 item 2's
"not instantiable now" becomes "instantiated at `measurableTruncatedSVD`". If S5 is proved before
S2c, S2c's wrap-up adds K15 to K19 instead; nothing else changes.

### 3.7 S6 template (written in S6's files) (1 or more)

S6's truncated-GN expectations (brief §4.3, "Truncated GN in expectation"; S2a §8 item 15: the
Frobenius error of truncated GN depends on the choice) are stated in the selector form,
`(hY : ∀ ω, IsBestRankApprox (generalizedNystrom A (X ω) (Ψ ω)) k (Y ω))
(hYm : AEStronglyMeasurable Y μ)`, and each gets its instance:

```lean
-- K20, template; S6's note fixes the hypotheses (`hX`, `hΨ`, independence, `ℓ ≥ 4k + 2`, `p ≥ 4ℓ`):
theorem integral_frobNorm_sub_measurableTruncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix
    ... :
    ∫ ω, frobNorm (A - measurableTruncatedSVD (generalizedNystrom A (X ω) (Ψ ω)) k) ^ 2 ∂μ ≤
      truncatedGNFactor k (Fintype.card l) (Fintype.card p) * frobNorm (A - truncatedSVD A k) ^ 2
```

with `hYm` from K10 composed with `hX.aemeasurable.prodMk hΨ.aemeasurable`. The same for a spectral
truncated-GN expectation if S6 states one, and for S7's OSI forms of MT 14.1 and truncated GN.

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean` (new) | 1 (K0) | 250 | Mathlib `MeasureTheory.Constructions.BorelSpace.Metrizable`, `Topology.MetricSpace.HausdorffDistance`, `Topology.Metrizable.Uniformity`, `Topology.Bases`, `MeasureTheory.MeasurableSpace.Constructions` | none |
| 2 | `Matrix/Spectral/BestRankApprox.lean` (registered; side file `Matrix/Spectral/BestRankApproxDegenerate.lean` until proved) | 2 (K1, K2) | +25 | none | none |
| 3 | `Matrix/Perturbation/Continuity.lean` (registered; side file `Matrix/Perturbation/ContinuityBestRankApprox.lean`) | 1 (K3) | +20 | `Matrix/Spectral/BestRankApprox` | none |
| 4 | `Probability/Measurability/Matrix.lean` (registered; side file `Probability/Measurability/BestRankApprox.lean`) | 8 (K4 to K11; one definition) | +110 | file 1, `Matrix/Spectral/BestRankApprox`, `Matrix/Factorizations/NystromGram` | files 1 to 3 |
| 5 | `LowRank/Random/RangeFinder.lean` (registered; side file `LowRank/Random/RangeFinderMeasurable.lean`) | 2 (K12, K13) | +30 | none (imports file 4 already) | file 4 |
| 6 | `LowRank/Gaussian/RangeFinder.lean` (registered; side file `LowRank/Gaussian/RangeFinderMeasurable.lean`) | 1 (K14) | +15 | none | file 4 |

S2c is about 450 lines and 15 public declarations (one definition), plus K15 to K19 (about 60 lines)
in S5 and K20 in S6. Every file stays far under 1000 lines (`Measurability/Matrix.lean` reaches
about 340, `BestRankApprox.lean` about 490). Order: files 1 to 3 are independent; 4 after 1 to 3; 5
and 6 after 4. File 1 is the only one with real proof work; files 2 to 6 are short. Import check:
`Continuity.lean` gains `BestRankApprox.lean`, which does not import `Continuity.lean` transitively
(only `Measurability/Matrix.lean` and `Sketching/Properties/Oblivious.lean` import it), so there is
no cycle.

**Placement** (CONTRIBUTING §8 item 5). Every addition outside the stage's one new file (file 1),
with its home and reason:
- K1, K2, `Matrix/Spectral/BestRankApprox.lean`, after `isBestRankApprox_iff`: the degenerate cases
  of the predicate, beside its other characterizations (B3, B4, B22); no measure theory, Matrix layer.
- K3, `Matrix/Perturbation/Continuity.lean`, after `SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD`:
  topological facts about rank sets and truncations live there (`isClosed_setOf_rank_le`, the
  continuity of the optimal error, whose docstring already says the truncation itself jumps); the
  statement is a continuity property of best approximations, not about the predicate's algebra.
- K4 to K9, `Probability/Measurability/Matrix.lean`: the file of "quantities that are not
  continuous but are Borel measurable" (rank, pseudoinverse, range projector, polar factor,
  Gram–Schmidt); the measurable truncation is one more, and a user looking for a measurable
  truncated SVD looks under `Probability/Measurability/`. The definition lives with its existence
  theorem because it is chosen from it; it cannot live in the Matrix layer (no measure theory).
- K10, K11, the same file, beside `measurable_rsvd`: measurability of the other named outputs as
  functions of their test matrices.
- K12, K13, `LowRank/Random/RangeFinder.lean`, beside L8 and L9; K14,
  `LowRank/Gaussian/RangeFinder.lean`, beside U2: each instance beside the theorem it instantiates,
  where its user finds the selector form.
- K15 to K19 (S5's files) and K20 (S6's): likewise, beside their selector theorems (§3.6, §3.7).
- Docstring edits, not declarations: L8, L9, U2 and the two module docstrings (§3.5); the module
  docstrings of `Measurability/Matrix.lean` ("Main results"), `Continuity.lean` and
  `BestRankApprox.lean`.
- Outside Lean, in the PRs that add K5 and K0: the §5.3 rows of §1 (two reviews), the notation-table
  sentence (§1), the name in `docs/design/Mathlib-deviations.md` "Additions where Mathlib has
  nothing", the bibliography keys of §5.
- **Flags** (placed elsewhere until the wrap-up): each of the five registered homes takes its
  statements only proved (S2a §8 item 18); until then they sit in the side files named in the
  table, each saying it merges into its home. No other flag.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/`; nothing ported, no ledger entries):
- `grep -i` for measurable SVD, measurable selection, selector and measurable eigenvector: no
  selection anywhere. The prototype avoids the question: `LowRank/RandomizedSVD/OptimalError.lean`
  takes a *supplied* measurable frame (`Qf` with `hQf : ∀ i j, Measurable fun x => Qf x i j`) and
  measures only the choice-free optimum (`integrable_frobSq_truncatedRsvdOutput_of_measurable_frame`);
  `Matrix/Perturbation/OptimalErrorContinuity.lean` proves continuity of the optimal Frobenius error
  "without asserting that an arbitrary classical SVD selector is measurable" (the library has it as
  `SymmetricGauge.continuous_matrixNorm_sub_truncatedSVD`); `Matrix/Spectral/QuadraticProbe.lean`,
  `Matrix/Perturbation/EigenvalueVariation.lean` and `RandomMatrix/Gaussian/InverseMoments/Probe.lean`
  say explicitly that no measurable eigenvector selection is involved. Not reproduced: the supplied
  frame hypotheses (a raw hypothesis per theorem; the selector form with `IsBestRankApprox` replaced
  them in S2a).

**Library** (read): `Matrix/Spectral/LowRank.lean` (the definition of `truncatedSVD`: `exists_isSVD`
at `min (card m) (card n)` columns, `.choose`; the private `exists_isSVD_truncatedSVD`, one SVD for
every $k$, is the only access to the definition, used 12 times, all in that file; nothing else
unfolds `truncatedSVD`), `Matrix/Spectral/BestRankApprox.lean`, `Matrix/Perturbation/Continuity.lean`,
`Probability/Measurability/Matrix.lean` (the private `measurable_of_continuousOn_fiber` and
`continuous_sqrt_gram`, which route (b) would make public), `ForMathlib/MeasureTheory/Matrix.lean`,
the selector theorems in `LowRank/Random/RangeFinder.lean`, `LowRank/Gaussian/RangeFinder.lean`,
`LowRank/Gaussian/RangeFinderTail.lean` (P6, no measurability).

**Mathlib** (read): `Probability/Decision/BayesEstimator.lean` (the comment quoted above),
`MeasureTheory/MeasurableSpace/Embedding.lean` (`MeasurableSet.exists_measurable_proj`),
`MeasureTheory/MeasurableSpace/Constructions.lean` (`exists_measurable_piecewise`, `measurable_find`,
`measurable_from_prod_countable_left`), `MeasureTheory/Constructions/BorelSpace/Metrizable.lean`
(`measurable_of_tendsto_metrizable`), `Topology/MetricSpace/HausdorffDistance.lean` (`infDist`,
`IsOpen.exists_iUnion_isClosed`), `Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Continuity.lean`
(`Continuous.cfc`, `ContinuousOn.cfc`, for route (b)).

**Literature** (not in hand; locators to confirm against the books before the PR that adds K0):
- Kuratowski and Ryll-Nardzewski, "A general theorem on selectors", Bull. Acad. Polon. Sci. 13
  (1965), 397 to 403: the theorem.
- Aliprantis and Border, *Infinite Dimensional Analysis*, 3rd ed. (2006): Theorem 18.13
  (Kuratowski–Ryll-Nardzewski), §17.2 (closed graph and upper hemicontinuity of compact-valued
  correspondences), §18.1 (weak measurability).
- Kechris, *Classical Descriptive Set Theory* (1995), Theorem 12.13 (the same theorem), a second
  reference if the first is not obtainable.

**Citations.** New keys `KuratowskiRyllNardzewski1965` and `AliprantisBorder2006` (and
`Kechris1995` if used) enter `docs/references.bib` with file 1. K0 cites them; K3 to K11 are
helpers and bridges and carry no citation; K12 to K20 carry their source theorem's citations, as
listed in §3.5 and §3.6.

**Result ids** (checked against the ids used by S2a, S3 and S5): `measurable-selection` (K0, new);
`randomized-svd-expected-error` (K14, as U2); `randomized-nystrom-expected-error` (K17 to K19, as
NU2, NU4, NI4). K4, K5 and the helpers carry none.

## 6. Cut, and why

- *Redefining `truncatedSVD`*: Q1 option (c). Not now; the additive design is forward-compatible
  (if it is ever done, K5 becomes a deprecated alias of `truncatedSVD` and K12 to K20 deprecated
  restatements).
- *Route (b), the explicit formula*: Q3. Its spectral-projector API (projector onto the eigenvalues
  above a threshold, its rank and trace) is additive and could be wanted for other reasons; no
  consumer now.
- *The gap bridge* `IsBestRankApprox.eq_truncatedSVD_of_singularValues_lt` (with an index-shift
  hypothesis, $\sigma_{k+1} < \sigma_k$ at rank $k + 1$) and its instance for K5: Q7.
- *Full Kuratowski–Ryll-Nardzewski* (weakly measurable closed-valued correspondences into a Polish
  space): Q4. Additive; the natural upstream form.
- *A measurable SVD* (`exists_measurable_isSVD`, measurable singular vectors with sorted values): K0
  applied to the closed set of SVDs with frames in the compact set of orthonormal frames. No
  consumer now; additive.
- *Success-set tails for the measurable truncation*: with K5 the failure event of P6 and NP6 at
  `measurableTruncatedSVD` is measurable, so "probability at least $1 - \delta$ of the good event"
  follows by `measureReal_compl`. One line at the use; no consumer states it.
- *Choice-free corollaries at K5* (the Frobenius error of truncated RSVD, the trace error of truncated
  Nyström, with `measurableTruncatedSVD` in place of `truncatedSVD`): equal to the stated forms by
  `IsBestRankApprox.frobNorm_sub_sq_eq_frobNorm_sub_rsvd_sq_add` at both truncations; one rewrite, and
  the rule of §1 keeps those statements on `truncatedSVD`.
- *Nested measurable truncations* (one measurable choice for every $k$ with nested ranges): would
  need K0 on a product correspondence; no consumer.
- *Pythagoras for every best approximation*, $\|\mathbf{C}\|_{\mathsf{F}}^2 = \|\mathbf{Y}
  \|_{\mathsf{F}}^2 + \|\mathbf{C}-\mathbf{Y}\|_{\mathsf{F}}^2$ (the twin of
  `frobNorm_sq_eq_truncatedSVD_add`, by a scaling argument): K4's local bound needs only
  $\|\mathbf{Y}\|_{\mathsf{F}} \le 2\|\mathbf{C}\|_{\mathsf{F}}$, three lines inside the proof.
  Additive.
- *Composition lemmas* `Measurable.measurableTruncatedSVD`, `AEMeasurable.measurableTruncatedSVD`:
  `.comp` and `.comp_aemeasurable` of K6; the recipe is in the module docstring.

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule, Q1 and Q2 go to the
maintainer; Q3 to Q8 are recorded for review after the fact.

**Q1. What the stage exposes (hard; for the maintainer).** Options:
(a) the existence theorem K4 and a definition `measurableTruncatedSVD` (K5) with its API, the
selector theorems kept, and their instances K12 to K20;
(b) the existence theorem only: no definition, no instances; each selector theorem's docstring gives
the `obtain` recipe;
(c) redefine `truncatedSVD` so that it is measurable, through route (b)'s formula: one function,
and every named-output statement becomes measurable in the maintainer's spelling
(`truncatedSVD (rsvd A (X ω)) k`).
Recommendation (a). Against (b): a statement or an algorithm definition cannot `obtain`; a later
theorem about "the" truncated output, and a Solvers algorithm that truncates inside its body, need a
named measurable choice, and composability needs the same one everywhere (§1). Against (c): a
selection theorem cannot define a Matrix-layer object (no measure theory there), so (c) needs route
(b); its correctness cannot use Eckart–Young, which `LowRank.lean` proves from the current
definition, so the private `exists_isSVD_truncatedSVD` (the definition's only access point, 12 uses)
must be reproved for the formula by exhibiting an SVD adapted to its projector (simultaneous
diagonalisation of $\mathbf{A}^{\mathsf{H}}\mathbf{A}$ and the projector, sorted into the
`Fin (min (card m) (card n))` layout), about 300 to 400 lines on top of route (b)'s 550 to 700, and
a rewrite of the definition of a finished, registered file. About 1000 lines against 450. Cost of
(a): two named best approximations, the rule of §1 for choosing, and a narrow exception to "late
truncation stays `truncatedSVD` of the named output" (only in expectations of choice-dependent
errors). Rework if reversed: to (b), delete K5 to K9 and K12 to K20 (about 120 lines; no other
statement mentions them); to (c) later, deprecate K5 and K12 to K20 and keep K0, K3, K4.

**Q2. The name (moderately hard; for the maintainer).** Options: `measurableTruncatedSVD`;
`measurableBestRankApprox`; `bestRankApproxSelector`. Recommendation `measurableTruncatedSVD`: users
search "truncated SVD", the docstring symbol is $\llbracket\cdot\rrbracket_k$, the name sorts beside
`truncatedSVD`, and every best approximation is mathematically the truncation of some SVD (the
equality case of Eckart–Young, though not proved in the library), so the name is accurate. The
second option matches the predicate `IsBestRankApprox` and avoids suggesting an SVD is computed.
Rework if changed: renames of K5 to K9 and K12 to K20, before any later stage uses them.

**Q3. Route (a), a selection theorem (not hard).** Recommendation (a), for the reasons of §3.1: about
450 lines against 650 to 800, generic and upstreamable, correctness free. Reversible: K4's
statement is the same under either route; only its proof changes. Route (b) stays the path to Q1
option (c).

**Q4. K0's form and home (not hard).** Options: the closed-set form K0 in `ForMathlib`; full KRN
(weakly measurable closed-valued correspondences into a Polish space) in `ForMathlib`; a private
lemma in `Measurability/Matrix.lean`. Recommendation K0 in `ForMathlib`: it has no NLAlib
vocabulary (CONTRIBUTING §2), Mathlib wants it, and its hypotheses are the ones a user checks; full
KRN costs more (a weak-measurability interface, step 2 for arbitrary closed-valued correspondences)
and has no consumer now, and K0 would become its corollary. File name after the Mathlib directory it
would join, `MeasureTheory/Constructions/BorelSpace/`, where `measurable_of_tendsto_metrizable`
lives. The name `IsClosed.exists_measurable_forall_prodMk_mem` spells the conclusion; Mathlib review
may prefer a "selection" name, which is a rename in `ForMathlib` only.

**Q5. Sequencing, and S5 and S6 (not hard).** S2c is proved before S5's skeleton, so S5 writes K15
to K19 beside NL7, NL8, NU2, NU4, NI4 and its docstrings say "instantiated" rather than "not
instantiable"; S5's note gains this at its review (an amendment of §3.0 item 2, §3.2, §3.3, §3.5 and
§4's placement list). S6's note states each choice-dependent expectation in the selector form with
its K20-style instance and uses K10. If S5 is proved first, S2c's wrap-up adds K15 to K19. The
selector theorems stay in every case: they are the general form, and an algorithm's own measurable
tie-break (a specific LAPACK convention, the factored form $\mathbf{Q}\llbracket\mathbf{Q}^{\mathsf{H}}
\mathbf{A}\rrbracket_k$ with a measurable frame) instantiates them directly.

**Q6. Docstring notation (not hard).** Options: the same $\llbracket\cdot\rrbracket_k$ with the Lean
name in words; a decorated symbol for the measurable choice. Recommendation the first: the sources'
symbol already means "a best rank-$k$ approximation", and the notation table's rule for named
constants (symbol plus Lean name nearby) is the precedent. Rework: docstrings only.

**Q7. The gap bridge deferred (not hard).** "`measurableTruncatedSVD A (k + 1) = truncatedSVD A
(k + 1)` when $\sigma_{k+1}(\mathbf{A}) < \sigma_k(\mathbf{A})$" needs the uniqueness of the best
approximation under a gap, through the first-order conditions $\mathbf{Y}^{\mathsf{H}}(\mathbf{C}-
\mathbf{Y}) = \mathbf{0}$, $(\mathbf{C}-\mathbf{Y})\mathbf{Y}^{\mathsf{H}} = \mathbf{0}$ and the
splitting of the spectrum of $\mathbf{C}^{\mathsf{H}}\mathbf{C}$, about 200 lines. Its use would be
to transfer K12 to K20 to `truncatedSVD` on events without ties, and no stage has such an event with
probability one (S2a §8 item 1). Deferred under the rule for very complex material; additive. The
same first-order conditions are the core of "every best approximation is a truncated SVD", which
Q1(c) would also want.

**Q8. Corrections of record (information).** After S2c: S2a §8 item 15's "The library cannot yet
exhibit a measurable selector" and its first bullet, S3 §3.0 item 2 ("The library cannot yet exhibit
such a `Y`"; "L8, L9 and U2 cannot be applied to any concrete algorithm today"), S3 §8 item 18(iii),
and S5 §0 and §3.0 item 2 ("not instantiable now") are superseded. S2a §8 item 15's reason for not
doing option (c) ("needs a measurable eigenvector selection under multiplicities") is replaced by
Q1's: K0 needs no eigenvectors, and the obstacle to (c) is the layer rule and the circularity with
Eckart–Young, not the selection. The brief's "Measurable truncation" decision is met for S3 by
S2c itself and for S5, S6 by K15 to K20 written in those stages (departure 3).

## 8. Amendments from the review (2026-10-15)

Review of this note (fifteen items: two medium, A1 and A2; eleven low; two verdicts with no
change, A9 and A14), all accepted by the orchestrator, none rejected. The review found nothing
mathematically wrong in K0 to K20 as drafted; it confirmed independently that Mathlib has no
measurable selection (the `BayesEstimator` TODO is as quoted), that every Mathlib tool named in
§3.1 (a) exists under that name, that K0 is true as stated without completeness of $Y$, and that
K1 to K3, the degenerate cases and the corollary signatures are right. Its two medium items changed
what the maintainer was choosing between: the lexicographic argmin is viable (A1), and applying the
selection to SVDs gives a measurable SVD and a truncation that is literally a truncated SVD (A2).
The maintainer then decided twice on the same day: first Q1 (a) with `measurableTruncatedSVD` built
as the truncation of a measurable SVD; then, as a change of plan, to redefine `truncatedSVD` itself
from that SVD if no proof depends on the old choice beyond its specification. The check (item 1)
found no such proof, so the redefinition is the plan. Five review items are overtaken by it (A5,
A12, A13, and the KRN-specific parts of A3 and A4); each is recorded where it lands. Where an item
below contradicts §0 to §7, it supersedes them; §3 stays as drafted, and item 14 is the final file
table.

1. **Q1 decided: `truncatedSVD` is redefined from a chosen thin SVD; no second function** (Q1, Q2,
   Q8; the departures "Additive" and "One new definition"; §1 "Objects", "Rule for statements",
   "§5.3 rows"). Record of the two decisions:
   - *First decision (2026-10-15).* Q1 option (a), a public definition with its API, not an
     existence theorem alone; `truncatedSVD` not redefined, for the reviewer's corrected reason
     (A12): the obstacle was the SVD-structure API of `LowRank.lean` (the private
     `exists_isSVD_truncatedSVD` and its 12 uses), not the selection and not the layer rule. The
     definition was to be the truncation of a measurable SVD (A2), so nested in $k$ and named
     `measurableTruncatedSVD` (Q2).
   - *Change of plan (maintainer, same day).* Redefine `truncatedSVD` through that SVD instead,
     provided no proof depends on the old choice beyond its specification. A12's obstacle
     disappears exactly when the new SVD has the old shape: then the 12 uses go through the same
     private lemma, which is reproved from the new SVD's specification in one line.
   - *Dependency check (2026-10-15, whole `NLAlib/` tree).* `truncatedSVD` is defined at
     `Matrix/Spectral/LowRank.lean` line 70 as `h.choose * diagonal (…) * h.choose_spec.chooseᴴ`
     with `h := exists_isSVD A (k := min (card m) (card n)) …` and $\boldsymbol\sigma$ =
     `fun i => singularValues A i`. The only access to the definition is the private
     `exists_isSVD_truncatedSVD` (line 81, proved by `rfl`), used 12 times, all in `LowRank.lean`
     (directly or through the private `exists_isSVD_truncatedSVD_sub`). No other file unfolds it:
     no `unfold`, `delta`, `simp`/`rw` with `truncatedSVD` as a definition, `.eq_def` or
     `choose_spec` on it in any of the 20 files that mention it; the `show` and `rfl` occurrences
     (`Truncation.lean` 230, 275; `BestRankApprox.lean` 393, 405; `ProjectedLowRank.lean` 93;
     `UnitarilyInvariant.lean` 369; `LowRank.lean` 616) are algebraic rewrites and subtype
     equalities about the value, not the definition. The two other `exists_isSVD` calls
     (`Factorizations/Polar.lean` 83, `Majorization/KyFan.lean` 355) make their own choices and are
     never compared with `truncatedSVD`'s. No obstacle: no downstream proof depends on the old
     choice, there is no shape mismatch (the new SVD is built in the identical shape, item 2), and
     no layer problem (below).
   - *Layer check.* The selection theorem's measurability part (K0b, K0) is in `ForMathlib`
     (layer $-1$), below the Matrix layer. The Matrix-layer definition uses no measure theory: the
     chosen SVD is the lexicographically least one (item 2), defined from a purely topological
     `ForMathlib` lemma (K0a, compactness only). Measurability of the chosen SVD and of
     `truncatedSVD` is proved in `Probability/Measurability/Matrix.lean` (layer 1), as the
     maintainer's rule of 2026-10-14 requires. This is why the construction must be the lex
     argmin and not a bare KRN selection: a definition chosen from an existence theorem whose
     statement says `Measurable` would put measure theory into a Matrix-layer definition.
   - *Consequences.* K4 to K9 of §3.4 are replaced by item 6; `measurableTruncatedSVD` and
     `exists_measurable_isBestRankApprox` are not added (the latter is the one term
     `⟨_, measurable_truncatedSVD k, fun A => isBestRankApprox_truncatedSVD A k⟩`, not stated). The
     maintainer's spelling rule "late truncation stays `truncatedSVD` of the named output" holds
     with no exception, so §1's second §5.3 row and its exception are withdrawn and A13 (making the
     exception a named sub-question Q1') is moot. The rule for statements becomes: every truncation
     is spelled `truncatedSVD`; a choice-dependent expectation (the spectral error of truncated
     RSVD and Nyström, both errors of truncated GN) is stated twice, in the selector form (any
     measurable best approximation, covering an algorithm's own tie-break, kept from S3, S5, S6)
     and as its direct corollary at `truncatedSVD` (items 7, 8); choice-free and pointwise
     statements are unchanged. Nestedness in $k$ is automatic (one SVD for every $k$, as before),
     so §3.0's bullet "Different truncation ranks" and §6's "Nested measurable truncations" are
     void. The registered definition keeps its name, type and every lemma; its body and
     docstring change ("The decomposition is chosen" becomes "the decomposition is
     $(\mathsf{svdU}(\mathbf{A}), \mathsf{svdV}(\mathbf{A}))$, the lexicographically least thin
     SVD"). Rework if reversed: restore the old body (one line) and add a separate definition; no
     statement changes.

2. **The chosen SVD: `svdU`, `svdV`, the lexicographically least thin SVD** (A1, A2; §6 "A
   measurable SVD"; Q2). Home `Matrix/Spectral/SVD.lean`, after `exists_isSVD`. Names in the
   library's style for factor pairs (`gramSchmidtQ`, `gramSchmidtR`; `luLower`, `luUpper`): two
   definitions, one choice. The name says what the object is, not a property proved two layers
   up, so "measurable" is not in it; `measurableSVD` (the maintainer's example) would be a
   Matrix-layer name for a Probability theorem. The coordinates are those of
   `Module.finBasis ℝ (Matrix m (Fin r) 𝕜 × Matrix n (Fin r) 𝕜)`, $r$ = `min (card m) (card n)`,
   ordered by `Pi.Lex` (`toLex`, Mathlib `Order/PiLex.lean`, a linear order on
   `Lex (Fin N → ℝ)`). The pair is unique (the coordinate map is injective), so the choice is
   canonical.

   ```lean
   /-- The **left singular vectors of the chosen SVD**: $\mathsf{svdU}(\mathbf{A})$ has $r =
   \min(\lvert m\rvert, \lvert n\rvert)$ orthonormal columns and, with $\mathsf{svdV}(\mathbf{A})$,
   gives $\mathbf{A} = \mathsf{svdU}(\mathbf{A})\,\operatorname{diag}(\sigma_0(\mathbf{A}), \dots,
   \sigma_{r-1}(\mathbf{A}))\,\mathsf{svdV}(\mathbf{A})^{\mathsf{H}}$
   (`NLAlib.isSVD_svdU_svdV`). Among all such thin SVDs it is the one whose real coordinates are
   lexicographically least, so it is a fixed function of $\mathbf{A}$; it is Borel measurable
   (`NLAlib.measurable_svdU`). `NLAlib.truncatedSVD` is built from it. -/
   noncomputable def svdU (A : Matrix m n 𝕜) :
       Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜
   /-- The **right singular vectors of the chosen SVD** $\mathsf{svdV}(\mathbf{A})$; see
   `NLAlib.svdU`. -/
   noncomputable def svdV (A : Matrix m n 𝕜) :
       Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜
   /-- **The chosen SVD is an SVD**: $\mathbf{A} = \mathsf{svdU}(\mathbf{A})\,\boldsymbol{\Sigma}\,
   \mathsf{svdV}(\mathbf{A})^{\mathsf{H}}$ with orthonormal columns and $\boldsymbol{\Sigma} =
   \operatorname{diag}(\sigma_i(\mathbf{A}))_{i<r}$, the singular values in decreasing order. -/
   theorem isSVD_svdU_svdV (A : Matrix m n 𝕜) :
       IsSVD A (svdU A) (fun i => singularValues A i) (svdV A)
   /-- **Construction lemma** (consumed by `NLAlib.measurable_svdU`; not needed for using the
   SVD): $(\mathsf{svdU}(\mathbf{A}), \mathsf{svdV}(\mathbf{A}))$ has the lexicographically least
   coordinates in the basis `Module.finBasis ℝ _` among the thin SVDs of $\mathbf{A}$ with
   $\boldsymbol{\Sigma} = \operatorname{diag}(\sigma_i(\mathbf{A}))_{i<r}$. -/
   theorem toLex_equivFun_svdU_svdV_le {A : Matrix m n 𝕜}
       {U : Matrix m (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜}
       {V : Matrix n (Fin (min (Fintype.card m) (Fintype.card n))) 𝕜}
       (h : IsSVD A U (fun i => singularValues A i) V) :
       toLex ((Module.finBasis ℝ _).equivFun (svdU A, svdV A)) ≤
         toLex ((Module.finBasis ℝ _).equivFun (U, V))
   ```

   Route: a private `exists_isSVD_forall_toLex_le A` (the pair exists with both properties) is K0a
   at the set of thin SVDs of $\mathbf{A}$, nonempty by `exists_isSVD` (the call the old
   definition made) and compact as a closed subset (`isClosed_eq` of `Continuous.matrix_mul`) of
   the product of two Stiefel sets, `isCompact_setOf_hasOrthonormalCols`
   (`Matrix/Subspaces/Frames.lean` line 201, already in the library; `Frames.lean` does not
   import `SVD.lean` transitively, checked, so the new import is cycle-free). `svdU A` and `svdV A`
   are `.choose.1` and `.choose.2` of that one lemma. `FiniteDimensional ℝ` of the matrix product
   by `inferInstanceAs` through the `Matrix` def if instance search does not unfold it. About 60
   lines. Degenerate: $m$ or $n$ empty, $r = 0$ and the pair is the unique pair of empty-column
   matrices; $\mathbf{A} = \mathbf{0}$, every pair of Stiefel frames is an SVD and the lex-least
   one is taken. In `LowRank.lean`:

   ```lean
   /-- The truncated SVD is the chosen SVD with the singular values $\sigma_i(\mathbf{A})$,
   $i \ge k$, set to zero: $\llbracket\mathbf{A}\rrbracket_k = \mathsf{svdU}(\mathbf{A})\,
   \operatorname{diag}(\sigma_0(\mathbf{A}), \dots, \sigma_{k-1}(\mathbf{A}), 0, \dots, 0)\,
   \mathsf{svdV}(\mathbf{A})^{\mathsf{H}}$. -/
   theorem truncatedSVD_def (A : Matrix m n 𝕜) (k : ℕ) :
       truncatedSVD A k = svdU A * Matrix.diagonal (fun i : Fin _ =>
         if (i : ℕ) < k then ((singularValues A i : ℝ) : 𝕜) else 0) * (svdV A)ᴴ
   ```

   The body of `truncatedSVD` becomes the right side; `truncatedSVD_def` is `rfl`; the private
   `exists_isSVD_truncatedSVD` becomes `⟨svdU A, svdV A, isSVD_svdU_svdV A, fun _ => rfl⟩`; nothing
   else in the file changes. The reviewer's alternative of generalising the private truncation
   lemmas to any `IsSVD` (A2, "about 50 lines") is not needed: the definition is itself the
   truncation of the chosen SVD.

3. **K0 by the lexicographic argmin; split into a topological and a measurable part** (A1, A3, A4,
   A15 (i); §3.1, §3.2, Q3, Q4). The maintainer accepted A1's route: each coordinate minimum is
   measurable through a rational intersection of preimages of closed sets, with no metric, dense
   sequence or Cauchy limit. The route needs real coordinates, so $Y$ is a finite-dimensional real
   topological vector space (the matrix spaces and their products are); this is the precise
   statement, narrower than A3's "metrizable, second countable" verdict for the KRN form, which
   stays the upstream-shaped generalisation (Q4, additive).

   K0a, `ForMathlib/Topology/Algebra/Module/FiniteDimension.lean` (new; the Mathlib file of
   `LinearMap.continuous_of_finiteDimensional`, which the coordinates need):

   ```lean
   /-- **A compact set has a lexicographically least point**: for a nonempty compact $K$ in a
   finite-dimensional real Hausdorff topological vector space with a basis $(\mathbf{b}_i)_{i<N}$,
   some $y \in K$ has coordinates lexicographically below those of every point of $K$. Its
   coordinates are $c_i(y) = \min\{c_i(z) : z \in K,\ c_j(z) = c_j(y) \text{ for } j < i\}$, each
   a minimum of a continuous function over a nonempty compact set. Upstream candidate. -/
   theorem IsCompact.exists_forall_toLex_equivFun_le {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
       [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y] {N : ℕ}
       (b : Basis (Fin N) ℝ Y) {K : Set Y} (hK : IsCompact K) (hne : K.Nonempty) :
       ∃ y ∈ K, ∀ z ∈ K, toLex (b.equivFun y) ≤ toLex (b.equivFun z)
   ```

   K0b and K0, `ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean`
   (file 1, as planned):

   ```lean
   /-- **The lexicographically least selection is measurable.** Let $S \subseteq X \times Y$ be
   closed with sections $S_x$ lying locally uniformly inside compact sets (each $x$ has a
   neighbourhood $U$ and a compact $K$ with $S_{x'} \subseteq K$ for $x' \in U$), $Y$ a
   finite-dimensional real topological vector space with a basis. If $f(x) \in S_x$ has
   lexicographically least coordinates in $S_x$ for every $x$, then $f$ is Borel measurable.
   The local compact bound cannot be weakened to compact sections without the projection
   theorems of descriptive set theory (Novikov, Arsenin–Kunugui). Upstream candidate.
   [KuratowskiRyllNardzewski1965]; [AliprantisBorder2006, Theorem 18.13], there an arbitrary
   measurable selection for weakly measurable correspondences into a Polish space, here the
   canonical one for a closed graph with locally compact sections. -/
   theorem IsClosed.measurable_of_forall_toLex_equivFun_le {X Y : Type*} [TopologicalSpace X]
       [MeasurableSpace X] [OpensMeasurableSpace X] [AddCommGroup Y] [Module ℝ Y]
       [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
       [MeasurableSpace Y] [BorelSpace Y] {N : ℕ} (b : Basis (Fin N) ℝ Y) {S : Set (X × Y)}
       (hS : IsClosed S)
       (hK : ∀ x, ∃ U ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧ ∀ x' ∈ U, ∀ y, (x', y) ∈ S → y ∈ K)
       {f : X → Y} (hf : ∀ x, (x, f x) ∈ S ∧
         ∀ y, (x, y) ∈ S → toLex (b.equivFun (f x)) ≤ toLex (b.equivFun y)) :
       Measurable f
   /-- **Measurable selection from a closed set with compact sections**: under the hypotheses of
   `IsClosed.measurable_of_forall_toLex_equivFun_le`, with every section nonempty, there is a
   Borel measurable $f : X \to Y$ with $(x, f(x)) \in S$ for every $x$ (the lexicographically
   least point of each section). [KuratowskiRyllNardzewski1965]; [AliprantisBorder2006,
   Theorem 18.13]. Upstream candidate.
   Result: measurable-selection -/
   theorem IsClosed.exists_measurable_forall_prodMk_mem {X Y : Type*} [TopologicalSpace X]
       [MeasurableSpace X] [OpensMeasurableSpace X] [AddCommGroup Y] [Module ℝ Y]
       [TopologicalSpace Y] [IsTopologicalAddGroup Y] [ContinuousSMul ℝ Y] [T2Space Y]
       [FiniteDimensional ℝ Y] [MeasurableSpace Y] [BorelSpace Y] {S : Set (X × Y)}
       (hS : IsClosed S) (hne : ∀ x, ∃ y, (x, y) ∈ S)
       (hK : ∀ x, ∃ U ∈ 𝓝 x, ∃ K : Set Y, IsCompact K ∧ ∀ x' ∈ U, ∀ y, (x', y) ∈ S → y ∈ K) :
       ∃ f : X → Y, Measurable f ∧ ∀ x, (x, f x) ∈ S
   ```

   Route of K0b (A1, A4 (a)). *Step 1 (closed map, A4 (a)):* for closed $C$, with $U, K$ from
   `hK`, $\{x \in U \mid S_x \cap C \ne \emptyset\}$ is $U$ intersected with the projection of a
   closed subset of $X \times K$, closed by `isClosedMap_fst_of_compactSpace` (`CompactSpace K`
   from `isCompact_iff_compactSpace`); closedness is local. No countability on $X$; about 40
   lines. *Step 2 (coordinates):* $c_i$ = `b.coord i`, continuous by
   `LinearMap.continuous_of_finiteDimensional`; $m_1(x) = \min_{S_x} c_1$, $S_i(x) = \{y \in S_x :
   c_j(y) = m_j(x),\ j < i\}$, $m_i(x) = \min_{S_i(x)} c_i$, by recursion on $i$. *Step 3:*
   $\{x \mid m_i(x) \le t\} = \bigcap_{q \in \mathbb{Q},\, q > 0}\{x \mid \exists y \in S_x,\
   (\forall j < i,\ c_j(y) \le m_j(x) + q) \wedge c_i(y) \le t\}$, (⇐) by
   `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed` at $q = 1/(n+1)$; each set
   on the right is the preimage of the closed set $H_i \subseteq X \times (\operatorname{Fin} i \to
   \mathbb{R}) \times \mathbb{R}$ (closed by step 1) under the measurable $x \mapsto (x, (m_j(x) +
   q)_j, t)$; `Prod.opensMeasurableSpace` applies since the second factor is second countable. So
   each $m_i$ is measurable (`measurable_of_Iic`, induction on $i$). *Step 4:* `hf` gives
   `b.equivFun (f x) = (m_i x)_i` (antisymmetry of the lex order), so $f$ =
   `b.equivFun.symm` composed with a measurable map into `Fin N → ℝ`, measurable since
   `b.equivFun.symm` is continuous. K0 is K0b at `Module.finBasis ℝ Y` with K0a giving $f$ (about
   15 lines). Degenerate: $X$ empty, `isEmptyElim`; $N = 0$, $Y$ is a point. Size: K0a 50 to 70
   lines, K0b and K0 200 to 280, so 250 to 350 for the selection theorem in all (A4's estimate,
   adopted). Imports (A4 (d), A15 (i)): `Topology.Maps.Proper.Basic`,
   `Topology.Algebra.Module.FiniteDimension`, `Order.PiLex`,
   `MeasureTheory.Constructions.BorelSpace.Order`, `Topology.Compactness.Compact`; the metric and
   `Metrizable` imports of §4 file 1 are dropped. Mathlib check for K0a: no lexicographic-minimum
   result on compact sets (no Mathlib file mentions both `IsCompact` and `toLex`). Names: A3 (iii)
   finds `IsClosed.exists_measurable_forall_prodMk_mem` acceptable and a Mathlib rename cheap;
   kept. A3 (i), on completeness of $Y$, is moot for the finite-dimensional form (stated once in
   the module docstring for the KRN generalisation, Q4); A3 (ii) is in K0b's docstring. The KRN
   recursion of §3.1 (a) steps 3 and 4 and A4 (b), (c) are not used.

4. **`MetrizableSpace (Matrix m n α)` in `ForMathlib`** (A6; §3.4 "Instances"). Accepted:
   Mathlib has none (`Topology/Instances/Matrix.lean` has `T2Space` only), and it is the instance
   Mathlib would add, `inferInstanceAs (MetrizableSpace (m → n → α))` through `metrizableSpace_pi`,
   justified as `Matrix.instSecondCountableTopology` was. Home
   `ForMathlib/Topology/Instances/Matrix.lean`, beside that instance, for countable (finite) index
   types and metrizable entries; module docstring extended. The lex route of item 3 no longer
   needs it; it stays for every later matrix-valued limit (`measurable_of_tendsto_metrizable`) and
   the KRN form (Q4), and is cheap (5 lines).

5. **Closedness of the set of SVDs; K3 kept as a user fact** (A2, A8; §3.3). New in
   `Matrix/Perturbation/Continuity.lean`, after `continuous_singularValues`:

   ```lean
   /-- **The thin SVDs with sorted singular values form a closed set**: the triples
   $(\mathbf{A}, \mathbf{U}, \mathbf{V})$ with $\mathbf{A} = \mathbf{U}\operatorname{diag}
   (\sigma_i(\mathbf{A}))_{i<r}\mathbf{V}^{\mathsf{H}}$ and orthonormal columns form a closed
   set, since the singular values are continuous. -/
   theorem isClosed_setOf_isSVD_singularValues {r : ℕ} :
       IsClosed {p : Matrix m n 𝕜 × (Matrix m (Fin r) 𝕜 × Matrix n (Fin r) 𝕜) |
         IsSVD p.1 p.2.1 (fun i => singularValues p.1 i) p.2.2}
   ```

   Route: `IsSVD` is three closed equations and a nonnegativity that holds automatically
   (`singularValues_nonneg`): `HasOrthonormalCols` twice (`isClosed_setOf_hasOrthonormalCols`
   composed with the projections) and `eq` by `isClosed_eq` of `continuous_fst` against the
   product with `continuous_singularValues` inside `Matrix.diagonal`. About 25 lines. K3
   (`isClosed_setOf_isBestRankApprox`) is off the construction's path now; it is kept for the
   consumers of §0 (limits of best approximations), at its drafted home. Placement alternative
   (A8): `BestRankApprox.lean`, importing `Continuity.lean`, was considered, since the statement
   is about `IsBestRankApprox`; `Continuity.lean` won because it already holds
   `isClosed_setOf_rank_le` and the continuity of the optimal error, and K3 is their combination.
   `ProjectedLowRank.lean`'s closure does not reach `Continuity.lean` (checked: the import closure
   of `BestRankApprox.lean` contains `SVD.lean` and `LowRank.lean` but not `Continuity.lean`), so
   the new import is cycle-free.

6. **Measurability API, in `Probability/Measurability/Matrix.lean`** (replaces K4 to K9; A7).

   ```lean
   /-- The left factor of the chosen SVD, $\mathbf{A} \mapsto \mathsf{svdU}(\mathbf{A})$, is
   Borel measurable (it is not continuous: it jumps where singular values meet). -/
   theorem measurable_svdU : Measurable (svdU : Matrix m n 𝕜 → _)
   /-- The right factor of the chosen SVD is Borel measurable. -/
   theorem measurable_svdV : Measurable (svdV : Matrix m n 𝕜 → _)
   /-- **The truncated SVD is Borel measurable**: $\mathbf{A} \mapsto \llbracket\mathbf{A}
   \rrbracket_k$ is measurable for every $k$, though not continuous (it jumps at ties
   $\sigma_{k-1}(\mathbf{A}) = \sigma_k(\mathbf{A})$). So the expectation of any error of a
   truncated random output is defined, and every selector-hypothesis theorem applies at
   `truncatedSVD`. -/
   theorem measurable_truncatedSVD (k : ℕ) : Measurable fun A : Matrix m n 𝕜 => truncatedSVD A k
   /-- Truncation preserves measurability. -/
   theorem Measurable.truncatedSVD {α : Type*} [MeasurableSpace α] {f : α → Matrix m n 𝕜}
       (hf : Measurable f) (k : ℕ) : Measurable fun x => truncatedSVD (f x) k
   /-- Truncation preserves almost-everywhere measurability. -/
   theorem AEMeasurable.truncatedSVD {α : Type*} [MeasurableSpace α] {μ : Measure α}
       {f : α → Matrix m n 𝕜} (hf : AEMeasurable f μ) (k : ℕ) :
       AEMeasurable (fun x => truncatedSVD (f x) k) μ
   ```

   with K10, K11 (`measurable_generalizedNystrom`, `measurable_nystrom`) unchanged. Routes:
   `measurable_svdU` and `measurable_svdV` are `.fst` and `.snd` of K0b at $X$ = `Matrix m n 𝕜`,
   $Y$ = the product of the two factor spaces, $S$ = item 5's set, `hK` with the fixed compact
   set (product of two Stiefel sets; uniform, not merely local, as A2 notes), `hf` from
   `isSVD_svdU_svdV` and `toLex_equivFun_svdU_svdV_le`; instances `Matrix.instBorelSpace`,
   `Matrix.instSecondCountableTopology` (for `Prod.borelSpace`), about 40 lines.
   `measurable_truncatedSVD`: `truncatedSVD_def`, `Measurable.matrix_mul`,
   `Measurable.matrix_conjTranspose`, and the diagonal measurable by `continuous_singularValues`
   (about 15 lines). The composition lemmas are `.comp` and `.comp_aemeasurable` (about 10
   lines, A7: they replace a four-step recipe in nine docstrings; Mathlib's `Measurable.inner`,
   `AEMeasurable.norm` are the precedent). The `.aestronglyMeasurable` step stays at the use, as
   Mathlib does. A user's `hYm`: `((measurable_rsvd A).comp_aemeasurable hX).truncatedSVD k
   |>.aestronglyMeasurable`. A5 (K4's compactness by the proper-space route) is moot: K4 is gone,
   and the compact set here is the existing Stiefel lemma.

7. **K12 to K14 spelled with `truncatedSVD`** (§3.5; A14). Same statements with
   `measurableTruncatedSVD` replaced by `truncatedSVD`, so the names become
   `integrable_specNorm_sub_truncatedSVD_rsvd_sq` (K12),
   `integral_specNorm_sub_truncatedSVD_rsvd_sq_add_frobNorm_sub_truncatedSVD_sq_le` (K13) and
   `integral_specNorm_sub_truncatedSVD_rsvd_sq_le_of_hasLaw_gaussianMatrix` (K14) (no clash:
   checked against the registered names); `hX : AEMeasurable X μ` stays on K12, K13, K14 gets it
   from `HasLaw`. Docstrings drop "with the output truncated by `measurableTruncatedSVD`" and K13's
   "the left truncation `measurableTruncatedSVD`, the right one `truncatedSVD`"; they say "the
   direct form of" the selector theorem, which they name. Routes: one term each, the selector
   theorem at `Y := fun ω => truncatedSVD (rsvd A (X ω)) k` with `hY := fun ω =>
   isBestRankApprox_truncatedSVD _ k` and item 6's `hYm`. §3.0's "K14 at $k = 0$ … an equality"
   reads "holds with equality" (A14). Docstring edits in the same PR (§3.5) change accordingly:
   L8, L9, U2 say "direct form at `truncatedSVD`: K12 (K13, K14)"; U2's sentence "the expectation
   of the spectral error of that output itself is not stated" is now false and is replaced by the
   name of K14; the module docstring of `LowRank/Random/RangeFinder.lean` replaces its
   "Measurability of the truncated output" paragraph by "`truncatedSVD` is Borel measurable
   (`NLAlib.measurable_truncatedSVD`); each selector theorem has its direct form".

8. **K15 to K20 likewise** (§3.6, §3.7, Q5). S5's instances are spelled
   `…_specNorm_sub_truncatedSVD_nystrom…` with `truncatedSVD (nystrom H (X ω)) k`, `hYm` from K11
   and item 6; S6's template K20 is
   `integral_frobNorm_sub_truncatedSVD_generalizedNystrom_sq_le_of_hasLaw_gaussianMatrix`, `hYm`
   from K10. S5's names must be checked against its own late-truncation statements when its
   skeleton is written (S5 has `truncatedSVD (nystrom H (X ω)) k` in the Frobenius and trace
   forms already). The S5 note's amendment under Q5 now reads "direct forms at `truncatedSVD`".

9. **§3.1 (c), the alternatives, corrected** (A1, A10, A11).
   - *Lexicographic minimisation*: the note's claim (second step needs measurable-correspondence
     theory) is withdrawn; A1's rational-intersection argument makes every step closed-set
     measurability, and it is the route taken (item 3).
   - *Minimisation over a countable dense set or a countable family* (A11): not applicable, since
     $S(\mathbf{A})$ is uncountable under ties (a Grassmannian), so no countable family of candidate
     maps covers it; a countable family would be route (b)'s pieces.
   - *A.e. measurability only* (A10): a second reason beyond the non-null tie set ($\mathbf{A} =
     \mathbf{I}$): an a.e. selection is relative to the law of the random output, which differs per
     consumer (Gaussian, Haar, oblivious), so it could not be a library object, and the pointwise
     selector form `∀ ω, IsBestRankApprox …` of L8, L9, U2, NL7, NL8 would weaken to `∀ᵐ`.
   - Route (b), the explicit spectral-projector formula, is no longer "the only route by which
     `truncatedSVD` could later be redefined" (§3.1 (b), Q3): item 1 redefines it through the
     lex-least SVD at a fraction of the cost. Route (b) stays cut (§6).

10. **K1, K2, the degenerate cases, the corollary signatures: checked, no change** (A9, A14).
    K1, K2 stay at their homes (the exact-recovery branches of selector statements and users; K8,
    K9 no longer exist, `truncatedSVD_zero` and `truncatedSVD_of_rank_le` serve). A15 (ii), the
    side-file pattern, and (iii), Kechris 1995 Theorem 12.13 as the Kuratowski–Ryll-Nardzewski
    theorem, are recorded; Aliprantis–Border 18.13 stays "to confirm".

11. **Q2 to Q8 after the decision.** Q2 (the name of a second function): void; the chosen SVD is
    `svdU`, `svdV` (item 2). Q3: the route is the lex-least SVD (item 3), neither (a)'s KRN
    recursion nor (b). Q4: K0 in `ForMathlib` in the finite-dimensional form, with K0a and K0b;
    full KRN additive later. Q5: stands, with direct forms at `truncatedSVD` (item 8). Q6: void
    (no new symbol; $\llbracket\cdot\rrbracket_k$ is `truncatedSVD`, and the factors are written
    $\mathsf{svdU}(\mathbf{A})$, $\mathsf{svdV}(\mathbf{A})$). Q7: stands deferred; its use
    (transferring K12 to K20 to `truncatedSVD`) is gone, so it now serves only "every best
    approximation under a gap is the truncated SVD". Q8, corrections of record, amended: S2a §8
    item 15's option (c) "not done now" is done, in the form of item 1 (not through route (b));
    its reason ("needs a measurable eigenvector selection under multiplicities") is superseded by
    item 1's check; Q8's own sentence "the obstacle to (c) is the layer rule and the circularity
    with Eckart–Young" is withdrawn (A12: it was the SVD-structure API, and the redefinition keeps
    that API's shape). The brief's line "named `measurableTruncatedSVD`; `truncatedSVD` itself is
    not redefined" (`docs/PORT_LOWRANK.md`, "Measurable truncation") is superseded and is updated
    by the orchestrator; S3 §3.0 item 2, S3 §8 item 18(iii), S5 §0 and §3.0 item 2 as listed in Q8.

12. **Docstrings** (CONTRIBUTING §6). LaTeX throughout; named outputs in `\mathsf`:
    $\mathsf{svdU}(\mathbf{A})$, $\mathsf{svdV}(\mathbf{A})$, $\mathsf{rsvd}(\mathbf{A},
    \mathbf{X})$, $\mathsf{nystrom}(\mathbf{H}, \mathbf{X})$, $\mathsf{gn}(\mathbf{A},
    \mathbf{\Omega}, \mathbf{\Psi})$, never the formula they unfold to. No named constant appears in
    S2c's statements (K14's $k/(\ell - k - 1)$ is the source's constant, written in the statement,
    CONTRIBUTING §5.2 rule 2), so `docs/constants.toml` and `scripts/check_constants.py` are not
    involved; K20's `truncatedGNFactor` is S6's, and its docstring value goes through the registry
    markers in S6's files. The §5.3 row "best rank-$k$ approximation" adds the bridge
    `measurable_truncatedSVD`; a new row "a singular value decomposition: any, `IsSVD A U σ V`;
    the library's chosen one, `svdU A`, `svdV A`; bridge `isSVD_svdU_svdV`". Mathlib deviations:
    `svdU`, `svdV` join "Additions where Mathlib has nothing" beside `IsSVD` and `truncatedSVD`
    (no numbered entry); `measurableTruncatedSVD` is not added.

13. **Placement** (CONTRIBUTING §8 item 5; replaces §4's list). Every addition outside the two new
    files (K0a's and file 1), with its home and reason:
    - `Matrix.instMetrizableSpace`, `ForMathlib/Topology/Instances/Matrix.lean`: beside
      `instSecondCountableTopology`, the other topological instance Mathlib lacks for matrices.
    - `svdU`, `svdV`, `isSVD_svdU_svdV`, `toLex_equivFun_svdU_svdV_le`,
      `Matrix/Spectral/SVD.lean` after `exists_isSVD`: a user looking for "the SVD of a matrix"
      looks beside `IsSVD` and its existence theorem; no measure theory.
    - The redefinition of `truncatedSVD` and `truncatedSVD_def`, `Matrix/Spectral/LowRank.lean`,
      in place: the definition stays where it is registered; the equation lemma follows it.
    - K1, K2, `Matrix/Spectral/BestRankApprox.lean` after `isBestRankApprox_iff`: unchanged (§4).
    - `isClosed_setOf_isSVD_singularValues` and K3, `Matrix/Perturbation/Continuity.lean`: the
      file of topological facts about singular values, rank sets and truncations
      (`continuous_singularValues`, `isClosed_setOf_rank_le`); the alternative home for K3 is
      recorded in item 5.
    - `measurable_svdU`, `measurable_svdV`, `measurable_truncatedSVD`, `Measurable.truncatedSVD`,
      `AEMeasurable.truncatedSVD`, K10, K11, `Probability/Measurability/Matrix.lean`: the file of
      "quantities that are not continuous but are Borel measurable"; measurability belongs to
      Probability (maintainer, 2026-10-14).
    - K12, K13 beside L8, L9 in `LowRank/Random/RangeFinder.lean`; K14 beside U2 in
      `LowRank/Gaussian/RangeFinder.lean`; K15 to K19 and K20 beside their selector theorems in
      S5's and S6's files.
    - Docstring edits, not declarations: `truncatedSVD`'s docstring (item 1), L8, L9, U2 and the
      two module docstrings (item 7), the "Main results" of `SVD.lean`, `LowRank.lean`,
      `Continuity.lean`, `BestRankApprox.lean`, `Measurability/Matrix.lean` and
      `ForMathlib/Topology/Instances/Matrix.lean`.
    - Outside Lean: the §5.3 rows and Mathlib-deviations names of item 12; the bibliography keys of
      §5.
    - **Flags.** The additions to `SVD.lean` sit in the side file `Matrix/Spectral/SVDChoice.lean`
      until proved, then merge; the redefinition of `truncatedSVD` is made in place only after the
      merge, in one PR with the reproof of the private lemma (it cannot be a side file: it changes
      a registered body). The other registered homes take their statements only proved, through
      the side files of §4 (S2a §8 item 18). No other flag.

14. **Files, statements and size** (replaces §4's table and count).

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1a | `ForMathlib/Topology/Algebra/Module/FiniteDimension.lean` (new) | 1 (K0a) | 50 to 70 | Mathlib `Topology.Algebra.Module.FiniteDimension`, `Order.PiLex`, `Topology.Compactness.Compact` | none |
| 1 | `ForMathlib/MeasureTheory/Constructions/BorelSpace/MeasurableSelection.lean` (new) | 2 (K0b, K0) | 200 to 280 | file 1a, Mathlib `Topology.Maps.Proper.Basic`, `MeasureTheory.Constructions.BorelSpace.Order` | file 1a |
| 1b | `ForMathlib/Topology/Instances/Matrix.lean` (registered) | 1 (instance) | +5 | Mathlib `Topology.Metrizable.Basic` | none |
| 2a | `Matrix/Spectral/SVD.lean` (registered; side file `SVDChoice.lean`) | 4 (two definitions) | +60 (to about 590) | file 1a, `Matrix/Subspaces/Frames` | file 1a |
| 2b | `Matrix/Spectral/LowRank.lean` (registered) | 1, and the redefinition | +5 (to about 625) | none | file 2a |
| 2 | `Matrix/Spectral/BestRankApprox.lean` (registered; side file as §4) | 2 (K1, K2) | +25 (to about 510) | none | none |
| 3 | `Matrix/Perturbation/Continuity.lean` (registered; side file as §4) | 2 (closed SVD set, K3) | +45 (to about 310) | `Matrix/Spectral/BestRankApprox` | none |
| 4 | `Probability/Measurability/Matrix.lean` (registered; side file as §4) | 7 (item 6, K10, K11) | +100 (to about 330) | file 1, `Matrix/Factorizations/NystromGram` | files 1, 2a, 2b, 3 |
| 5 | `LowRank/Random/RangeFinder.lean` (registered; side file as §4) | 2 (K12, K13) | +30 (to about 290) | none | file 4 |
| 6 | `LowRank/Gaussian/RangeFinder.lean` (registered; side file as §4) | 1 (K14) | +15 (to about 440) | none | file 4 |

S2c: 23 new public declarations (two definitions, `svdU` and `svdV`; one instance; 20
theorems) and one redefinition, about 600 lines (535 to 635: the selection theorem 250 to 350,
the rest about 285), plus K15 to K19 (about 60 lines) in S5 and K20 in S6. Against the drafted
450 lines and 15 declarations: the SVD construction adds about 150 (A2's estimate), and
`measurableTruncatedSVD` with its four API lemmas and the existence theorem are gone. Every
file stays under 1000 lines. Order: 1a and 1b independent; 1 after 1a; 2a after 1a; 2b after
2a is merged; 2 and 3 independent; 4 after 1, 2b and 3; 5 and 6 after 4. Import checks: §4's
(`Continuity.lean` gains `BestRankApprox.lean`, cycle-free) and item 2's (`SVD.lean` gains
`Frames.lean` and file 1a, cycle-free).
