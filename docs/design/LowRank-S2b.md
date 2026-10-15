# Design note: LowRank stage S2b, early truncation and projection-cost-preserving sketches (deterministic)

Status: drafted 2026-10-15 under `docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15: D7 approved,
PCPs in this round with the deterministic part here; the error-spelling rule, every error is
$\mathbf{A}$ minus the named output; the Chen–Persson manuscript's new results ported, never cited,
docstrings saying "proved without a literature source"; D1, D2, D3, D10, D11 to D15; §4.1 items 8
and 9, §5.1, §5.3, §5.4, the S2b entry of §7, §9.3), `docs/design/LowRank-S0.md` (§3 as amended by
§8; proved and registered), `docs/design/LowRank-S1.md` (§8 overrides §3; proved) and
`docs/design/LowRank-S2a.md` (being amended; its §7 Q1 and §8 leave late truncation unnamed and
make the naming of late and early truncated outputs one joint question, prepared here as Q1).
Deterministic, over `𝕜`, every shape, rank and truncation rank. Reviewed 2026-10-15, amendments in
§8, which overrides §0 to §7 where they disagree (§3 stays as drafted); Q1 decided by the maintainer
as (b), Q2 accepted as recommended (§8 items 10, 11). **Maintainer checkpoint after this stage**
(brief §1, §7).

Departures from the brief, each argued below:
- **Early-truncated outputs get names** (`earlyTruncatedRSVD A Ω k`,
  `earlyTruncatedGeneralizedNystrom A Ω Ψ k`), against the brief's D1 table ("no new names"). Their
  only other spelling is a projector form, which the maintainer's error rule makes a bridge, never a
  statement shape. This is the joint naming question with S2a (Q1, hard to reverse); §3 is written
  under its recommendation.
- **The PCP predicate is `IsProjectionCostPreserving A Ã k a b`**, with lower and upper constants
  $a$, $b$ (as `IsSubspaceEmbedding`) and the offset existentially quantified, $\exists c \ge 0$
  (CEMMP's Definition 1 verbatim), not the brief's candidate with $\varepsilon$ and a parameter $c$
  (Q2, hard to reverse: S9's tail form depends on it).
- **The early-truncation core is stated for any frame $\mathbf{Z}$ and any orthogonal projector
  $\mathbf{P}$ of rank at most $k$** that is at least as good on the sketch as the frame's
  competitor; the manuscript's SVD blocks, normalisation $t^{-1/2}\mathbf{\Omega}$ and
  $\min\{1,\lambda\}$ are not in the statements (Q3). The named early-truncated output is one
  instance, any best approximation of the sketch or a measurable selector another (Q7).
- **Woodruff Theorem 61 is in S2b, not S7.** It is the deterministic row-space subspace-embedding
  route (T7), not the OSE-plus-AMM tail the brief attributes to it (Q6).
- **The deterministic split of early-truncated GN** (E8) is stated here beside its definition; S6
  keeps the Gaussian completion (Q10).
- **No uniform-PCP statement for early-truncated GN** in S2b: its second term is bounded only
  probabilistically (S6, S7, S9).
- Correction of record for S9: the $O(k/\varepsilon^2)$ head–tail PCP constructor does not need
  spectral AMM; CEMMP's own short proof uses a head embedding and Frobenius AMM only (Q9).

**Literature checks.** CEMMP is in hand (`/tmp/claude-1000/p0/papers/cemmp_15.pdf`, arXiv:1410.6801
v3): Definition 1 (p. 5, two-sided, $0 \le \varepsilon < 1$, "for some fixed non-negative constant
$c$", rank exactly $k$, rows of $\mathbf{A}$ as data points, projectors on the left, linear sketches
$\tilde{\mathbf{A}} = \mathbf{A}\mathbf{R}$), Definition 2 (p. 6, one-sided), Lemma 3 (p. 6, the
consequence, $\gamma \ge 1$, $c \ge 0$), Lemma 4 (p. 7), Lemmas 5 and 6 (pp. 8 to 9, sufficient
conditions), proof of Theorem 12 (p. 16, the head, tail–tail and tail–head terms of the core),
§7.2 (p. 18, "if we compute the top k singular vectors of our sketch, projecting to these vectors
will give a (1+ε) approximate low rank approximation"), §10.1 (pp. 22 to 23, early truncation in a
stream). Woodruff 2014 Theorem 61 (p. 95, proof pp. 95 to 96) is early truncation under a subspace
embedding of the whole column space, with unsquared $1 \pm \varepsilon$ constants and
$(1+\varepsilon)^4$ in the proof; Theorem 47's rank-$k$ clause is not used here. TYUC SIMAX
(arXiv:1609.00048 v2) §7.3.1, (7.3) (pp. 21 to 22) states early-truncated GN as an algorithm,
$\hat{\mathbf{A}}_{\mathrm{cemmp}}$, credited to CEMMP §10.1, with a final truncation that is the
identity, and reports it as the weakest method in their experiments (§7.4, p. 23). Musco and Musco
2020 is not in hand and is not cited (brief §9.2).

**Missing infrastructure.** Below the Matrix layer: nothing. In the Matrix layer: nothing public;
one proof-local fact (a Loewner bound on $\mathbf{U}^{\mathsf{H}}\mathbf{U}$ for a non-orthonormal
$\mathbf{U}$ bounds Frobenius norms of $\mathbf{U}\mathbf{X}$, the column-sum form of
`mul_frobNorm_sq_le_of_smul_one_le`, for P3). From S0 and S1 (proved, registered): `rsvd`,
`generalizedNystrom`, `obliqueProjector`, `rank_obliqueProjector`,
`frobNorm_one_sub_obliqueProjector_mul_sq`; S1's L2
`exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD` (the top-$k$ reading, used in
docstrings and by consumers). From S2a: nothing; S2b imports neither of S2a's files. Not S2b's to
fill: measurability of early-truncated outputs (Q7), the head–tail constructor (Q9).

## 0. Scope and consumers

$\mathbf{A}$ : `Matrix m n 𝕜`; the test matrix $\mathbf{\Omega}$ : `Matrix n l 𝕜` on the right
(D2); the co-range sketch $\mathbf{\Psi}$ : `Matrix m p 𝕜`, applied as $\mathbf{\Psi}^{\mathsf{H}}$
(D14); a frame $\mathbf{Z}$ : `Matrix n r 𝕜` with $\mathbf{Z}^{\mathsf{H}}\mathbf{Z} = \mathbf{I}$ (S1's
role of $\mathbf{V}_1$); a truncation rank $k : \mathbb{N}$. Early truncation projects onto the range of
a best rank-$k$ approximation of the sketch:
$$\hat{\mathbf{A}}_{\mathrm{et}} = \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A},
\qquad
\hat{\mathbf{A}}_{\mathrm{etGN}} = \mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A}.$$
Throughout, as in S1, $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ (the tail;
$\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k$ in the top-$k$ reading) and the three sketch
quantities of the core are
$$\lambda:\ \lambda\mathbf{I} \preceq \mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z},
\qquad
w = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} - \mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}},
\qquad
\chi = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} - \mathbf{E}\mathbf{Z}\|_{\mathsf{F}}$$
(head subspace injection, tail–tail and tail–head approximate-multiplication errors;
$\mathbf{E}\mathbf{Z} = \mathbf{0}$). In Lean $\lambda$ is the constant `a` of
`IsSubspaceInjection Ωᴴ Z a`.

| Item | Consumers |
|---|---|
| `earlyTruncatedRSVD`, `earlyTruncatedGeneralizedNystrom` and their API (E1 to E8) | S6 (early-truncated GN as shape (a) at $\mathbf{X} = \llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$: E8 then the Gaussian completion identity at the actual rank); S7 (OSE-plus-AMM tails for both outputs); S9 (uniform-PCP corollaries); later, early-truncated RSVD in expectation (brief §8) |
| `IsProjectionCostPreserving`, `mono` (P1, P2) | S9 (`HasProjectionCostPreserving` in tail form and its family corollaries, the head–tail constructor); users with constrained low-rank problems (a set of rank-$k$ projectors, $k$-means) |
| row-space constructor (P3) | T7; S9 (constructor from an OSE of the row space) |
| consequence (P4, CEMMP Lemmas 3 and 4) | T6; users solving a constrained problem on a sketch |
| head–tail split, core, linear form, almost-sure form (T1 to T4) | T5; S7 (OSE-plus-AMM tail: $\lambda$ from an OSE of $\operatorname{range}\mathbf{Z}$, $w$ and $\chi$ from `HasJLMoment` AMM tails); the later expectation (inverse moments of $\min\{1,\lambda\}$, brief §8); users with another best approximation of the sketch or a measurable selector (Q7) |
| early-truncated RSVD, almost-sure form (T5) | S7, the later expectation, users |
| uniform-PCP route (T6) | S9 (corollaries for early-truncated RSVD; for GN with S6 and S7) |
| row-space subspace-embedding route (T7, Woodruff Theorem 61) | S9; users holding a subspace embedding of the row space (SRHT, sparse embeddings at dimension $\operatorname{rank}\mathbf{A}/\varepsilon^2$) |

Not in S2b: anything probabilistic (S6, S7, S9); late truncation (S2a); the head–tail PCP
constructor (S9, Q9); a uniform-PCP bound for early-truncated GN (needs the completion term, S6,
S7, S9); early-truncated RSVD in expectation (brief §8); the draft-only $2\times 2$ lower bound and
the (C4)-dependent direct theorem of the notes (D15, §5).

## 1. Objects

Two new definitions (under Q1's recommendation) and one new predicate (§2). No deviation from
Mathlib: Mathlib has no low-rank approximation and no sketching, so `earlyTruncatedRSVD`,
`earlyTruncatedGeneralizedNystrom` and `IsProjectionCostPreserving` join the paragraph "Additions
where Mathlib has nothing" of `docs/design/Mathlib-deviations.md` (one line, in the commit that
adds them; no numbered entry), as S0's `rsvd` and S2a's `IsBestRankApprox` did.

**§5.3 rows** (added by the PR that adds E1 and P1; two reviews, CONTRIBUTING §9):

| Concept | Spelling | Bridge |
|---|---|---|
| truncated outputs (amends S0's "low-rank approximations from sketches" row and S2a's "truncated outputs" row; Q1) | late, as S2a: `truncatedSVD (rsvd A Ω) k` and so on; early: `earlyTruncatedRSVD A Ω k`, `earlyTruncatedGeneralizedNystrom A Ω Ψ k`; errors `A - earlyTruncatedRSVD A Ω k` (maintainer's rule); docstrings $\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}$, $\mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A}$ | `earlyTruncatedRSVD_mul`; `earlyTruncatedRSVD_of_rank_le`; the definitions unfold to the projector forms |
| projection-cost-preserving sketch (new) | `IsProjectionCostPreserving A Ã k a b`: some offset $c \ge 0$ with $a\,\mathrm{cost}_{\mathbf{A}}(\mathbf{P}) \le \mathrm{cost}_{\tilde{\mathbf{A}}}(\mathbf{P}) + c \le b\,\mathrm{cost}_{\mathbf{A}}(\mathbf{P})$ for every `IsStarProjection P` with `P.rank ≤ k`; the cost is `frobNorm (A - P * A) ^ 2`, never `(1 - P) * A`; the literature's $\varepsilon$ is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$ (two-sided) or $a = 1$ (one-sided), written so | `IsSubspaceEmbedding.isProjectionCostPreserving`; Mathlib: none |
| early-truncation sketch quantities (new) | for a frame `Z`, with `E = A - A * Z * Zᴴ` written out: head `IsSubspaceInjection Ωᴴ Z a`; tail–tail `E * Ω * Ωᴴ * Eᴴ - E * Eᴴ`; tail–head `E * Ω * Ωᴴ * Z - E * Z` (the zero term kept for the AMM shape, S1 §8 item 7); no definitions | `HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le` at $\mathbf{A} := \mathbf{E}^{\mathsf{H}}$, $\mathbf{S} := \mathbf{\Omega}^{\mathsf{H}}$, after `conjTranspose_conjTranspose` |

**Used directly.** Library: `rangeProjector` API (`isStarProjection_rangeProjector`,
`rank_rangeProjector`, `rangeProjector_mul_self`, `IsStarProjection.rangeProjector_eq`,
`frobNorm_rangeProjector_sq`, `IsStarProjection.frobNorm_mul_le`,
`IsStarProjection.frobInner_mul_one_sub_mul`); `truncatedSVD` API (`rank_truncatedSVD_le`,
`rangeProjector_truncatedSVD_mul`, `frobNorm_sub_truncatedSVD_le_of_rank_le`,
`truncatedSVD_of_rank_le`, `truncatedSVD_zero`); S0's `rsvd`, `generalizedNystrom`,
`obliqueProjector`, `rank_obliqueProjector`, `frobNorm_one_sub_obliqueProjector_mul_sq`; Frobenius
API (`frobNorm_sq_eq_re_trace`, `frobInner_le`, `abs_frobInner_le`,
`frobNorm_add_sq_of_frobInner_eq_zero`, `frobNorm_mul_conjTranspose_right`,
`frobNorm_sq_eq_sum_col`, `frobNorm_conjTranspose`); `mul_frobNorm_sq_le_of_smul_one_le`
(`Norms/Loewner.lean`); Sketching (`IsSubspaceInjection`, `IsSubspaceEmbedding`,
`HasOrthonormalCols.isSubspaceInjection_iff`, `isSubspaceInjection_iff_forall_mem_range`,
`isSubspaceEmbedding_iff_forall_mem_range`, `IsSubspaceInjection.mono`). Mathlib:
`Matrix.rank_mul_le_left`, `Matrix.rank_mul_le_right`, `Matrix.rank_le_card_width`,
`Matrix.trace_mul_comm`, `Real.sqrt` API.

**Mathlib search** ("searched, none" unless named): a projection-cost-preserving sketch or coreset; a
projection onto dominant singular vectors of a sketch; a Frobenius-form Loewner congruence for a
general Gram matrix (the column-sum step is proof-local, from `frobNorm_sq_eq_sum_col` and the vector
form of the embedding).

## 2. Interfaces

**New: `IsProjectionCostPreserving A Ã k a b`** (§5.4 review; Q2).
- *Bundles:* the existence of one offset $c \ge 0$ for which the two-sided bound holds at every
  orthogonal projector of rank at most $k$. A `def` with `∃`, not a `structure`: the two halves share
  $c$, so they cannot be separate fields.
- *Leaves separate:* the sketch's form ($\tilde{\mathbf{A}}$ is any matrix with the rows of
  $\mathbf{A}$, so SVD, column-selection and $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ sketches
  fit, not only $\mathbf{A}\mathbf{\Omega}$); randomness (S9's `HasProjectionCostPreserving` is the
  event's tail).
- *Constructors:* P3 (row-space subspace embedding, offset $0$, every $k$ at once); the definition
  itself is the raw condition; the head–tail constructor is S9's (Q9).
- *Mathlib bridge:* none (no Mathlib notion).
- *API:* P2 (`mono`), P4 (the consequence).
- *Statements taking it:* P2, P4, T6; S9's tail form and corollaries.

**Existing spellings used as hypotheses:** `HasOrthonormalCols Z`; `IsSubspaceInjection Ωᴴ Z a`
(the head; S1's spelling); `IsSubspaceEmbedding Ωᴴ Aᴴ a b` (the row space, D2 orientation);
`IsStarProjection P` with `P.rank ≤ k`; S0's rank hypothesis
`(Ψᴴ * truncatedSVD (A * Ω) k).rank = (truncatedSVD (A * Ω) k).rank`; the sketch optimality of
$\mathbf{P}$ against the frame's competitor,
`frobNorm (A * Ω - P * (A * Ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * Ω)`, a raw one-line inequality in three
statements (T2 to T4), under the threshold for a predicate (Q3).

**Not introduced:** a predicate "optimal on the sketch" (Q3); definitions for $w$, $\chi$ (S1 Q4
precedent, Q3); `HasProjectionCostPreserving` (S9); a parameter $c$ or an $\varepsilon$ form of the
PCP predicate (Q2).

## 3. Statement shapes

`namespace NLAlib`, `open scoped Matrix MatrixOrder`. Variables `{𝕜 : Type*} [RCLike 𝕜]
{m n l p r : Type*}`, `[Fintype _]` on each; `[DecidableEq r]` with a frame (`HasOrthonormalCols Z`
is `Zᴴ * Z = 1`); no statement displays `1 : Matrix m m 𝕜`, so no `[DecidableEq m]` (proofs use
`classical`). Docstrings are shortened; the full ones carry the citations of §5 and are LaTeX
throughout (CONTRIBUTING §6 item 5).

**Degenerate cases** (checked for every statement; the per-section notes say where a case bites).
- *Ties* $\sigma_{k-1}(\mathbf{A}\mathbf{\Omega}) = \sigma_k(\mathbf{A}\mathbf{\Omega})$. The
  early-truncated output and its error depend on the choice `truncatedSVD` makes. Example:
  $\mathbf{A} = \operatorname{diag}(2, 1)$, $\mathbf{\Omega} = \operatorname{diag}(\tfrac12, 1)$,
  $k = 1$: $\mathbf{A}\mathbf{\Omega} = \mathbf{I}_2$, and the projector onto
  $\mathbf{e}_1$, $\mathbf{e}_2$ or $(1,1)/\sqrt2$ gives squared Frobenius errors $1$, $4$, $5/2$
  (OPT$^2 = 1$). Every statement holds for every choice: T1 to T4 are about any projector satisfying
  the sketch optimality, and T5 to T7 use only `rank_truncatedSVD_le` and Eckart–Young for
  `truncatedSVD`, true of every choice. The same example is tight for T4 and T6: the frame
  $\mathbf{Z} = \mathbf{e}_1$ has $\lambda = \tfrac14$, $w = \chi = 0$, so T4 allows
  $4/(1-\theta)$; $(\mathbf{A}, \mathbf{A}\mathbf{\Omega})$ is a PCP with $a = \tfrac14$, $b = 1$,
  $c = 0$, and T6 reads $\tfrac14 \cdot 4 \le 1$.
- *$k = 0$.* `truncatedSVD _ 0 = 0`, so both early outputs are $\mathbf{0}$; a projector of rank
  $0$ is $\mathbf{0}$; the PCP at rank $0$ is the scaled Frobenius preservation
  $a\|\mathbf{A}\|_{\mathsf{F}}^2 \le \|\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
  b\|\mathbf{A}\|_{\mathsf{F}}^2$. T2 at $k = 0$: sketch optimality says
  $\|\mathbf{A}\mathbf{\Omega}\| \le \|\mathbf{E}\mathbf{\Omega}\|$ and the claim is
  $\lambda r_1^2 \le 2\chi r_1$, which that gives; T5 at $k = 0$ forces `r` empty (`hk`), so
  $\mathbf{E} = \mathbf{A}$, $\chi = 0$ and the bound is $\|\mathbf{A}\|^2 \le
  \|\mathbf{A}\|^2/((1-\theta)a)$.
- *$k$ at or above $\operatorname{rank}(\mathbf{A}\mathbf{\Omega})$.* The early outputs are the
  untruncated ones (E6, E7); every bound still holds. *$k$ at or above $\operatorname{rank}
  \mathbf{A}$:* in the top-$k$ reading $\mathbf{E} = \mathbf{0}$, $w = \chi = 0$, and T5 forces
  `A - earlyTruncatedRSVD A Ω k = 0` (consistent: a positive injection on a frame containing the row
  space keeps $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) = \operatorname{rank}\mathbf{A} \le k$);
  T6 gives $a\|\mathbf{A}-\hat{\mathbf{A}}_{\mathrm{et}}\|^2 \le 0$. *$k \ge \lvert m \rvert$:* the
  PCP quantifies over every projector, including $\mathbf{I}$, which forces $c = 0$.
- *$\varepsilon \ge 1$, that is $a \le 0$.* The PCP's lower half holds automatically ($c \ge 0$), and
  P4, T6, T7 are vacuous, as in CEMMP ($\varepsilon < 1$ there). T4 and T5 require $0 < a \le 1$; T2
  holds for every real $a$ the injection allows.
- *Empty index types.* `l` empty or $\mathbf{\Omega} = \mathbf{0}$: the outputs are $\mathbf{0}$; sketch
  optimality holds; a positive injection forces `r` empty, so $\mathbf{E} = \mathbf{A}$, $\chi = 0$ and
  T4 reads $\|\mathbf{A}\|^2 \le (\|\mathbf{A}\|^2 + \sqrt{k}\,\|\mathbf{A}\mathbf{A}^{\mathsf{H}}
  \|_{\mathsf{F}})/((1-\theta)a)$, true. `r` empty: $\mathbf{Z} = \mathbf{0}$ is a frame, every
  injection holds, $r_1 = \chi = 0$, and T2 is $\|\mathbf{A}-\mathbf{P}\mathbf{A}\|^2 \le
  \|\mathbf{A}\|^2 + \sqrt{k}\,w$, true for a projector. `m` or `n` empty: every matrix is
  $\mathbf{0}$.
- *Rank-deficient truncation*, $\operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k < k$:
  the projector has rank below $k$, which is why P1 quantifies over rank at most $k$ (with CEMMP's
  "rank $k$" T6 would not apply); E8's rank hypothesis is at the actual rank, so S6's completion
  factor is taken there (brief §1).
- *Scaling.* `earlyTruncatedRSVD A (c • Ω) k = earlyTruncatedRSVD A Ω k` is not provable under ties
  (`truncatedSVD` chooses separately for $c\mathbf{X}$ and $\mathbf{X}$). No statement needs it: T5 to
  T7 are at one $\mathbf{\Omega}$, the normalised one in the consumer's hands, and T2 to T4 separate the
  output's projector from the analysed sketch (Q8).
- *Hermitian, non-PSD inputs*: no Nyström statement in S2b.

### 3.1 `Matrix/Factorizations/SketchedLowRank.lean`: the early-truncated outputs (8)

New section "Early truncation" after the generalized Nyström section. Written proved (the file is
registered, S1 §8 item 16; every proof is one to three lines).

```lean
/-- The **early-truncated randomized SVD**
$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}$: the projection of
$\mathbf{A}$ onto the range of the truncated SVD of the sketch $\mathbf{A}\mathbf{\Omega}$, that is
onto $k$ dominant left singular vectors of the sketch. Rank at most $k$
(`NLAlib.rank_earlyTruncatedRSVD_le`); $\lvert l \rvert$ products with $\mathbf{A}$ and at most $k$
with $\mathbf{A}^{\mathsf{H}}$. Under ties $\sigma_{k-1}(\mathbf{A}\mathbf{\Omega}) =
\sigma_k(\mathbf{A}\mathbf{\Omega})$ it depends on the choice `truncatedSVD` makes, and so does its
error. [Woodruff2014, Theorem 61]; [CohenElderMuscoMuscoPersu2015, §7.2, §10.1]; there with the
sketch on the left and the rows of $\mathbf{A}$ projected. -/
noncomputable def earlyTruncatedRSVD (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    Matrix m n 𝕜 :=
  rangeProjector (truncatedSVD (A * Ω) k) * A
/-- The **early-truncated generalized Nyström approximation**
$\mathbf{\Pi}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k,\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A}$:
generalized Nyström with the range sketch replaced by its truncated SVD. One pass; rank at most $k$
(`NLAlib.rank_earlyTruncatedGeneralizedNystrom_le`). [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)];
there through a basis of $k$ dominant left singular vectors of the sketch, a QR factorization, and a
final truncation that is the identity. -/
noncomputable def earlyTruncatedGeneralizedNystrom (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) (k : ℕ) : Matrix m n 𝕜 :=
  obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ * A
/-- The early-truncated output reproduces the truncated sketch:
$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}\mathbf{\Omega} =
\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$. -/
theorem earlyTruncatedRSVD_mul (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    earlyTruncatedRSVD A Ω k * Ω = truncatedSVD (A * Ω) k
theorem rank_earlyTruncatedRSVD_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜) (k : ℕ) :
    (earlyTruncatedRSVD A Ω k).rank ≤ k
theorem rank_earlyTruncatedGeneralizedNystrom_le (A : Matrix m n 𝕜) (Ω : Matrix n l 𝕜)
    (Ψ : Matrix m p 𝕜) (k : ℕ) : (earlyTruncatedGeneralizedNystrom A Ω Ψ k).rank ≤ k
/-- With $k$ at least the rank of the sketch nothing is truncated:
$\mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A} =
\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}$. -/
theorem earlyTruncatedRSVD_of_rank_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {k : ℕ}
    (hk : (A * Ω).rank ≤ k) : earlyTruncatedRSVD A Ω k = rsvd A Ω
theorem earlyTruncatedGeneralizedNystrom_of_rank_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {k : ℕ} (hk : (A * Ω).rank ≤ k) (Ψ : Matrix m p 𝕜) :
    earlyTruncatedGeneralizedNystrom A Ω Ψ k = generalizedNystrom A Ω Ψ
/-- **Early-truncated generalized Nyström error = early-truncated RSVD error + sketch-and-solve
excess**, exactly, when
$\operatorname{rank}(\mathbf{\Psi}^{\mathsf{H}}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k) =
\operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$: with
$\mathbf{X} = \llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$,
$$\|\mathbf{A} - \mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}^{\mathsf{H}}}\mathbf{A}\|_{\mathsf{F}}^2 =
\|\mathbf{A} - \mathbf{P}_{\mathbf{X}}\mathbf{A}\|_{\mathsf{F}}^2 +
\|\mathbf{\Pi}_{\mathbf{X},\mathbf{\Psi}^{\mathsf{H}}}(\mathbf{A} - \mathbf{P}_{\mathbf{X}}\mathbf{A})
\|_{\mathsf{F}}^2\,.$$
The deterministic half of early-truncated GN: S6 bounds the last term by the Gaussian completion
identity at the actual rank, S7 by a subspace injection. -/
theorem frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Ψ : Matrix m p 𝕜} {k : ℕ}
    (h : (Ψᴴ * truncatedSVD (A * Ω) k).rank = (truncatedSVD (A * Ω) k).rank) :
    frobNorm (A - earlyTruncatedGeneralizedNystrom A Ω Ψ k) ^ 2 =
      frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 +
        frobNorm (obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ *
          (A - earlyTruncatedRSVD A Ω k)) ^ 2
```

Proof routes. *E3:* `Matrix.mul_assoc`, `rangeProjector_truncatedSVD_mul`. *E4:*
`Matrix.rank_mul_le_left`, `rank_rangeProjector`, `rank_truncatedSVD_le`. *E5:*
`Matrix.rank_mul_le_left`, `rank_obliqueProjector`, `Matrix.rank_mul_le_right`,
`rank_truncatedSVD_le`. *E6, E7:* `truncatedSVD_of_rank_le`, then the definitions of `rsvd` and
`generalizedNystrom`. *E8:* `classical`; $\mathbf{A} - \mathbf{\Pi}\mathbf{A} = (\mathbf{I} -
\mathbf{\Pi})\mathbf{A}$ and $\mathbf{A} - \mathbf{P}_{\mathbf{X}}\mathbf{A} = (\mathbf{I} -
\mathbf{P}_{\mathbf{X}})\mathbf{A}$ (`Matrix.sub_mul`, `Matrix.one_mul`), then
`frobNorm_one_sub_obliqueProjector_mul_sq h A`. Degenerate: E8 at $k = 0$ is
$\|\mathbf{A}\|^2 = \|\mathbf{A}\|^2 + 0$; at $\mathbf{\Psi} = \mathbf{I}$ (rank hypothesis automatic)
the oblique projector is $\mathbf{P}_{\mathbf{X}}$ and the last term vanishes; the rank hypothesis is
necessary ($\mathbf{\Psi} = \mathbf{0}$, $\mathbf{A} = \mathbf{\Omega} = \mathbf{I}_2$, $k = 2$: the
oblique projector is $\mathbf{0}$, the left side is $2$, the right side $0$).

### 3.2 `Sketching/Properties/ProjectionCost.lean`: the predicate (4)

```lean
/-- $\tilde{\mathbf{A}}$ is a **rank-$k$ projection-cost-preserving sketch** of $\mathbf{A}$ with
constants $a$, $b$: for some offset $c \ge 0$, independent of the projector, every orthogonal
projector $\mathbf{P}$ of rank at most $k$ has
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\|\tilde{\mathbf{A}} - \mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
b\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2\,.$$
The two-sided form is $a = 1 - \varepsilon$, $b = 1 + \varepsilon$; the one-sided form is $a = 1$.
[CohenElderMuscoMuscoPersu2015, Definitions 1 and 2]; there over $\mathbb{R}$, with $\varepsilon$,
and for projectors of rank exactly $k$; here constants $a$, $b$, any field, rank at most $k$, so
that projectors of smaller rank (a rank-deficient truncation) are covered.
Result: projection-cost-preserving-sketch -/
def IsProjectionCostPreserving (A : Matrix m n 𝕜) (Ã : Matrix m l 𝕜) (k : ℕ) (a b : ℝ) : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ P : Matrix m m 𝕜, IsStarProjection P → P.rank ≤ k →
    a * frobNorm (A - P * A) ^ 2 ≤ frobNorm (Ã - P * Ã) ^ 2 + c ∧
      frobNorm (Ã - P * Ã) ^ 2 + c ≤ b * frobNorm (A - P * A) ^ 2
theorem IsProjectionCostPreserving.mono {A : Matrix m n 𝕜} {Ã : Matrix m l 𝕜} {k k' : ℕ}
    {a a' b b' : ℝ} (h : IsProjectionCostPreserving A Ã k a b) (hk : k' ≤ k) (ha : a' ≤ a)
    (hb : b ≤ b') : IsProjectionCostPreserving A Ã k' a' b'
/-- **A subspace embedding of the row space is a projection-cost-preserving sketch** for every
rank, with offset $0$: if $\mathbf{\Omega}^{\mathsf{H}}$ is a subspace embedding for
$\operatorname{range}\mathbf{A}^{\mathsf{H}}$ with constants $a$, $b$, then
$\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with
the same constants, for every $k$. Its dimension is at least $\operatorname{rank}\mathbf{A}$.
[CohenElderMuscoMuscoPersu2015, §1.1]; [Woodruff2014, proof of Theorem 61]; there transposed. -/
theorem IsSubspaceEmbedding.isProjectionCostPreserving {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {a b : ℝ} (h : IsSubspaceEmbedding Ωᴴ Aᴴ a b) (k : ℕ) :
    IsProjectionCostPreserving A (A * Ω) k a b
/-- **Constrained low-rank approximation through a projection-cost-preserving sketch.** If
$\mathbf{P}$ is $\gamma$-optimal for the sketch against a competitor $\mathbf{P}'$, both orthogonal
projectors of rank at most $k$ and $\gamma \ge 1$, then it is $\gamma b / a$-optimal for
$\mathbf{A}$:
$$a\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\gamma\, b\,\|\mathbf{A} - \mathbf{P}'\mathbf{A}\|_{\mathsf{F}}^2\,.$$
[CohenElderMuscoMuscoPersu2015, Lemmas 3 and 4]; there for the minimizer over a set of rank-$k$
projectors and $(1+\varepsilon)/(1-\varepsilon)$ or $1 + \varepsilon$; here any competitor and
constants $a$, $b$. Result: projection-cost-preserving-sketch -/
theorem IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le {A : Matrix m n 𝕜}
    {Ã : Matrix m l 𝕜} {k : ℕ} {a b : ℝ} (h : IsProjectionCostPreserving A Ã k a b)
    {P P' : Matrix m m 𝕜} (hP : IsStarProjection P) (hPk : P.rank ≤ k)
    (hP' : IsStarProjection P') (hP'k : P'.rank ≤ k) {γ : ℝ} (hγ : 1 ≤ γ)
    (hopt : frobNorm (Ã - P * Ã) ^ 2 ≤ γ * frobNorm (Ã - P' * Ã) ^ 2) :
    a * frobNorm (A - P * A) ^ 2 ≤ γ * b * frobNorm (A - P' * A) ^ 2
```

Proof routes. *P2:* the same $c$; `hPk.trans hk`; the costs are nonnegative, so
`mul_le_mul_of_nonneg_right` on each side. *P3:* $c = 0$. With $\mathbf{Y} = \mathbf{I} - \mathbf{P}$
Hermitian, $\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}} = \|\mathbf{A}^{\mathsf{H}}\mathbf{Y}
\|_{\mathsf{F}}$ and $\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} =
\|\mathbf{\Omega}^{\mathsf{H}}\mathbf{A}^{\mathsf{H}}\mathbf{Y}\|_{\mathsf{F}}$
(`frobNorm_conjTranspose`); each column of $\mathbf{A}^{\mathsf{H}}\mathbf{Y}$ lies in
$\operatorname{range}\mathbf{A}^{\mathsf{H}}$, so the vector form
(`isSubspaceEmbedding_iff_forall_mem_range`) applies column by column and
`frobNorm_sq_eq_sum_col` sums it. The bound holds for every $\mathbf{Y}$, not only for complements of
projectors, which is why $k$ is free. *P4:* obtain $c$; lower half at $\mathbf{P}$, `hopt`, upper half
at $\mathbf{P}'$: $a x \le \gamma(b x' - c) + c = \gamma b x' - (\gamma - 1)c \le \gamma b x'$ by
`hγ` and $0 \le c$ (`nlinarith`). Degenerate: P3 needs no hypothesis on $a$, $b$ or $k$; P4 at
$\gamma = 1$ uses no sign of $c$, and for $\gamma > 1$ the predicate's $c \ge 0$ is what drops the
term $-(\gamma - 1)c$ (CEMMP's last step); at $a \le 0$ P4 is vacuous.

### 3.3 `LowRank/Structural/EarlyTruncation.lean`: the core (4)

All four are about any orthogonal projector $\mathbf{P}$ of rank at most $k$ that is at least as
good on the sketch as $\mathbf{P}_{\mathbf{A}\mathbf{Z}}$, the projector of the frame's competitor
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$; the hypothesis `hopt` is the weakest form
the proof uses. With $\mathbf{P} = \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}$ and
$\lvert r \rvert \le k$ it is Eckart–Young (T5). "Proved without a literature source" on T2 to T5
(D13, §9.3).

```lean
/-- **The head–tail split of a projection residual.** For $\mathbf{Z}$ with orthonormal columns,
any $\mathbf{P}$, and $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 =
\|\mathbf{A}\mathbf{Z} - \mathbf{P}\mathbf{A}\mathbf{Z}\|_{\mathsf{F}}^2 +
\|\mathbf{E} - \mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2\,.$$ -/
theorem HasOrthonormalCols.frobNorm_sub_mul_sq_eq_add {Z : Matrix n r 𝕜}
    (hZ : HasOrthonormalCols Z) (A : Matrix m n 𝕜) (P : Matrix m m 𝕜) :
    frobNorm (A - P * A) ^ 2 =
      frobNorm (A * Z - P * (A * Z)) ^ 2 + frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) ^ 2
/-- **The early-truncation structural bound.** Let $\mathbf{Z}$ have orthonormal columns,
$\mathbf{\Omega}^{\mathsf{H}}$ be a subspace injection for $\operatorname{range}\mathbf{Z}$ with
constant $\lambda$, and $\mathbf{P}$ an orthogonal projector of rank at most $k$ with
$\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} \le
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$. With $r_1 = \|\mathbf{A}\mathbf{Z} -
\mathbf{P}\mathbf{A}\mathbf{Z}\|_{\mathsf{F}}$, $r_2 = \|\mathbf{E} - \mathbf{P}\mathbf{E}\|_{\mathsf{F}}$,
$w = \|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} -
\mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}$ and $\chi = \|\mathbf{E}\mathbf{\Omega}
\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} - \mathbf{E}\mathbf{Z}\|_{\mathsf{F}}$,
$$\lambda r_1^2 + r_2^2 \le \|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w + 2\chi r_1\,.$$
Only the lower side of the head embedding and the two approximate-multiplication errors enter; the
Frobenius preservation of the tail cancels. Proved without a literature source; the sketch
quantities are those of [CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.mul_frobNorm_sub_mul_sq_add_le {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {Z : Matrix n r 𝕜} {a : ℝ} (h : IsSubspaceInjection Ωᴴ Z a)
    (hZ : HasOrthonormalCols Z) {P : Matrix m m 𝕜} (hP : IsStarProjection P) {k : ℕ}
    (hPk : P.rank ≤ k)
    (hopt : frobNorm (A * Ω - P * (A * Ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * Ω)) :
    a * frobNorm (A * Z - P * (A * Z)) ^ 2 +
        frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 +
        √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
          (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) +
        2 * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) *
          frobNorm (A * Z - P * (A * Z))
/-- **The early-truncation structural bound, in the error alone**: for $\lambda \le 1$,
$$\lambda\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le \|\mathbf{E}\|_{\mathsf{F}}^2 +
\sqrt{k}\,w + 2\chi\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}\,.$$
Proved without a literature source. Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.mul_frobNorm_sub_mul_sq_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Z : Matrix n r 𝕜} {a : ℝ} (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z)
    (ha1 : a ≤ 1) {P : Matrix m m 𝕜} (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k)
    (hopt : frobNorm (A * Ω - P * (A * Ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * Ω)) :
    a * frobNorm (A - P * A) ^ 2 ≤
      frobNorm (A - A * Z * Zᴴ) ^ 2 +
        √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
          (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) +
        2 * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) *
          frobNorm (A - P * A)
/-- **The early-truncation bound with all unboundedness in the head constant**: for
$0 < \lambda \le 1$ and $0 < \theta < 1$,
$$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 \le
\frac{\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w}{(1-\theta)\lambda} +
\frac{\chi^2}{\theta(1-\theta)\lambda^2}\,.$$
A random head constant enters as $\min\{1, \lambda\}$ through `NLAlib.IsSubspaceInjection.mono`.
Proved without a literature source. Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.frobNorm_sub_mul_sq_le {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜}
    {Z : Matrix n r 𝕜} {a θ : ℝ} (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z)
    (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1) {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k)
    (hopt : frobNorm (A * Ω - P * (A * Ω)) ≤ frobNorm ((A - A * Z * Zᴴ) * Ω)) :
    frobNorm (A - P * A) ^ 2 ≤
      (frobNorm (A - A * Z * Zᴴ) ^ 2 +
          √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
            (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)) / ((1 - θ) * a) +
        frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) ^ 2 /
          (θ * (1 - θ) * a ^ 2)
```

Proof routes. *T1* (any $\mathbf{P}$): $\mathbf{B} = \mathbf{A} - \mathbf{P}\mathbf{A}$ splits as
$\mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} + (\mathbf{B} - \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}})$
with $\operatorname{Re}\operatorname{tr}(\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{B}^{\mathsf{H}}
\mathbf{B}(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}})) = 0$ (`hZ`, `Matrix.trace_mul_comm`),
`frobNorm_add_sq_of_frobInner_eq_zero`, `frobNorm_mul_conjTranspose_right hZ`; then
$\mathbf{B}\mathbf{Z} = \mathbf{A}\mathbf{Z} - \mathbf{P}\mathbf{A}\mathbf{Z}$ and $\mathbf{B} -
\mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} = \mathbf{E} - \mathbf{P}\mathbf{E}$ (`noncomm_ring`).
*T2*, with $\mathbf{Y} = \mathbf{I} - \mathbf{P}$ (proof-internal, `classical`),
$\mathbf{R}_1 = \mathbf{Y}\mathbf{A}\mathbf{Z}$, $\mathbf{R}_2 = \mathbf{Y}\mathbf{E}$:
1. *Sketch optimality:* `hopt` squared, and $\mathbf{Y}\mathbf{A}\mathbf{\Omega} =
   \mathbf{R}_1\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega} + \mathbf{R}_2\mathbf{\Omega}$, so
   $\|\mathbf{R}_1\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}\|^2 + 2\operatorname{Re}\langle
   \mathbf{R}_1\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}, \mathbf{R}_2\mathbf{\Omega}\rangle_{\mathsf{F}} +
   \|\mathbf{R}_2\mathbf{\Omega}\|^2 \le \|\mathbf{E}\mathbf{\Omega}\|^2$.
2. *Head:* `hZ.isSubspaceInjection_iff` turns `h` into
   $a\mathbf{I} \preceq (\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z})^{\mathsf{H}}\mathbf{\Omega}^{\mathsf{H}}
   \mathbf{Z}$; `mul_frobNorm_sq_le_of_smul_one_le` at $\mathbf{X} = \mathbf{R}_1^{\mathsf{H}}$ and
   `frobNorm_conjTranspose` give $a r_1^2 \le \|\mathbf{R}_1\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}\|^2$.
3. *Tail:* with $\mathbf{W} = \mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}}
   - \mathbf{E}\mathbf{E}^{\mathsf{H}}$, $\|\mathbf{R}_2\mathbf{\Omega}\|^2 - r_2^2 =
   \operatorname{Re}\operatorname{tr}(\mathbf{Y}\mathbf{W}) = \operatorname{Re}\operatorname{tr}\mathbf{W}
   - \operatorname{Re}\operatorname{tr}(\mathbf{P}\mathbf{W})$ (`frobNorm_sq_eq_re_trace`,
   $\mathbf{Y}^{\mathsf{H}}\mathbf{Y} = \mathbf{Y}$, cyclicity), $\operatorname{Re}\operatorname{tr}
   (\mathbf{P}\mathbf{W}) \le \|\mathbf{P}\|_{\mathsf{F}}\,w$ (`frobInner_le`, $\mathbf{P}$ Hermitian),
   $\|\mathbf{P}\|_{\mathsf{F}}^2 = \operatorname{rank}\mathbf{P} \le k$ (`hP.rangeProjector_eq`,
   `frobNorm_rangeProjector_sq`), and $\operatorname{Re}\operatorname{tr}\mathbf{W} =
   \|\mathbf{E}\mathbf{\Omega}\|^2 - \|\mathbf{E}\|^2$.
4. *Cross:* $\langle\mathbf{R}_1\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}, \mathbf{R}_2\mathbf{\Omega}
   \rangle_{\mathsf{F}} = \langle\mathbf{R}_1, \mathbf{Y}\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
   \mathbf{Z}\rangle_{\mathsf{F}} = \langle\mathbf{R}_1, \mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}
   \mathbf{Z} - \mathbf{E}\mathbf{Z}\rangle_{\mathsf{F}}$ ($\mathbf{Y}\mathbf{R}_1 = \mathbf{R}_1$,
   $\mathbf{E}\mathbf{Z} = \mathbf{0}$), so its real part is at least $-\chi r_1$ (`abs_frobInner_le`).
5. `linarith`: the $\|\mathbf{E}\mathbf{\Omega}\|^2$ terms cancel. This is the formalization's
   `et_deterministic` over `𝕜`, for a frame and a projector in place of SVD blocks and a basis.

*T3:* T1 rewrites $\|\mathbf{A} - \mathbf{P}\mathbf{A}\|^2 = r_1^2 + r_2^2$; $a r_2^2 \le r_2^2$
(`ha1`) and $r_1 \le \|\mathbf{A} - \mathbf{P}\mathbf{A}\|$ (T1); T2. *T4:* T3 and Young,
$2\chi s \le \theta a s^2 + \chi^2/(\theta a)$, then divide by $(1-\theta)a > 0$ (`le_div_iff₀`,
`field_simp`, `nlinarith`). Degenerate: `hopt` is necessary ($\mathbf{A} = \mathbf{Z} = \mathbf{\Omega}
= [1]$, $\mathbf{P} = \mathbf{0}$, $k = 0$, $a = 1$: $\mathbf{E} = \mathbf{0}$, so T2 would claim
$1 \le 0$); `ha1` is used by T3 only to absorb $a r_2^2$ (for $a > 1$ apply `h.mono` at $1$);
the rank bound is where $\sqrt{k}$ comes from; §3 list for the rest.

Usage (S7's tail, the top-$k$ reading; S1 Q3):
```lean
obtain ⟨Z, hZ, hZA⟩ :=
  exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD (p := Fin k) A (Fintype.card_fin k) hk
-- on the event `IsSubspaceInjection (Ω ω)ᴴ Z (1 - ε)` and the two AMM events:
have h := (hinj ω).frobNorm_sub_earlyTruncatedRSVD_sq_le hZ (Fintype.card_fin k).le ha ha1 hθ hθ1 A
rw [hZA] at h   -- ‖A - ⟦A⟧ₖ‖² = OPT², and w, χ in terms of A - truncatedSVD A k
```

### 3.4 `LowRank/Structural/EarlyTruncation.lean`: the early-truncated RSVD, three routes (3)

```lean
/-- **Early-truncated randomized SVD, structural bound.** For $\mathbf{Z}$ with orthonormal
columns, $\lvert r \rvert \le k$, $\mathbf{\Omega}^{\mathsf{H}}$ a subspace injection for
$\operatorname{range}\mathbf{Z}$ with constant $0 < \lambda \le 1$, and $0 < \theta < 1$,
$$\|\mathbf{A} - \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}\|_{\mathsf{F}}^2
\le \frac{\|\mathbf{E}\|_{\mathsf{F}}^2 + \sqrt{k}\,w}{(1-\theta)\lambda} +
\frac{\chi^2}{\theta(1-\theta)\lambda^2}\,,$$
for every choice of the truncation. With $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}} =
\llbracket\mathbf{A}\rrbracket_k$ (S1's frame) $\|\mathbf{E}\|_{\mathsf{F}}$ is the optimal error.
Proved without a literature source; the sketch quantities are those of
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12]. Result: early-truncation-structural-bound -/
theorem IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le {Ω : Matrix n l 𝕜}
    {Z : Matrix n r 𝕜} {a θ : ℝ} (h : IsSubspaceInjection Ωᴴ Z a) (hZ : HasOrthonormalCols Z)
    {k : ℕ} (hk : Fintype.card r ≤ k) (ha : 0 < a) (ha1 : a ≤ 1) (hθ : 0 < θ) (hθ1 : θ < 1)
    (A : Matrix m n 𝕜) :
    frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 ≤
      (frobNorm (A - A * Z * Zᴴ) ^ 2 +
          √(k : ℝ) * frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * (A - A * Z * Zᴴ)ᴴ -
            (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)) / ((1 - θ) * a) +
        frobNorm ((A - A * Z * Zᴴ) * Ω * Ωᴴ * Z - (A - A * Z * Zᴴ) * Z) ^ 2 /
          (θ * (1 - θ) * a ^ 2)
/-- **Early truncation through a projection-cost-preserving sketch**: if $\mathbf{A}\mathbf{\Omega}$
is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with constants $a$, $b$, then
$$a\|\mathbf{A} - \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}\|_{\mathsf{F}}^2
\le b\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,,$$
that is $(1+\varepsilon)/(1-\varepsilon)$ times the optimal error in the two-sided form. A
pointwise statement: off the event where the sketch is a PCP the error is bounded only by
$\|\mathbf{A}\|_{\mathsf{F}}^2$, so no expectation bound follows from it; the structural bound
`NLAlib.IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le` gives one.
[CohenElderMuscoMuscoPersu2015, Lemma 3, §7.2]; there with $\varepsilon$ and a set of rank-$k$
projectors. Result: early-truncation-pcp-bound -/
theorem IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le
    {A : Matrix m n 𝕜} {Ω : Matrix n l 𝕜} {k : ℕ} {a b : ℝ}
    (h : IsProjectionCostPreserving A (A * Ω) k a b) :
    a * frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 ≤ b * frobNorm (A - truncatedSVD A k) ^ 2
/-- **Early truncation under a subspace embedding of the row space**: if
$\mathbf{\Omega}^{\mathsf{H}}$ is a subspace embedding for $\operatorname{range}\mathbf{A}^{\mathsf{H}}$
with constants $a$, $b$, then for every $k$
$$a\|\mathbf{A} - \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}\mathbf{A}\|_{\mathsf{F}}^2
\le b\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2\,.$$
[Woodruff2014, Theorem 61]; there transposed, with unsquared constants $1 \pm \varepsilon$
($a = (1-\varepsilon)^2$, $b = (1+\varepsilon)^2$ here) and the conclusion $1 + O(\varepsilon)$.
Result: early-truncation-pcp-bound -/
theorem IsSubspaceEmbedding.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le {A : Matrix m n 𝕜}
    {Ω : Matrix n l 𝕜} {a b : ℝ} (h : IsSubspaceEmbedding Ωᴴ Aᴴ a b) (k : ℕ) :
    a * frobNorm (A - earlyTruncatedRSVD A Ω k) ^ 2 ≤ b * frobNorm (A - truncatedSVD A k) ^ 2
```

Proof routes. Throughout $\hat{\mathbf{P}} = \mathbf{P}_{\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k}$,
`earlyTruncatedRSVD A Ω k = P̂ * A` (definition); $\hat{\mathbf{P}}$ is a star projection
(`isStarProjection_rangeProjector`) of rank at most $k$ (`rank_rangeProjector`,
`rank_truncatedSVD_le`), and $\hat{\mathbf{P}}\mathbf{A}\mathbf{\Omega} = \llbracket\mathbf{A}\mathbf{\Omega}
\rrbracket_k$ (`rangeProjector_truncatedSVD_mul`). *T5:* `hopt` is Eckart–Young against
$\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$, of rank at most $\lvert r \rvert \le k$
(`Matrix.rank_mul_le_left`, `Matrix.rank_mul_le_right`, `Matrix.rank_le_card_width`):
`frobNorm_sub_truncatedSVD_le_of_rank_le`, then $\mathbf{A}\mathbf{\Omega} -
\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega} = \mathbf{E}\mathbf{\Omega}$
(`Matrix.sub_mul`); then T4. *T6:* P4 at $\gamma = 1$, $\mathbf{P} = \hat{\mathbf{P}}$,
$\mathbf{P}' = \mathbf{P}_{\llbracket\mathbf{A}\rrbracket_k}$ (rank at most $k$; $\mathbf{P}'\mathbf{A}
= \llbracket\mathbf{A}\rrbracket_k$ by `rangeProjector_truncatedSVD_mul`); `hopt` is Eckart–Young for
the sketch against $\mathbf{P}'\mathbf{A}\mathbf{\Omega}$, of rank at most $k$. *T7:* T6 at P3.
Degenerate: `hk` is necessary in T5 ($\mathbf{A} = \mathbf{\Omega} = \mathbf{Z} = \mathbf{I}_2$,
$k = 1$, $a = 1$: $\mathbf{E} = \mathbf{0}$, $w = \chi = 0$, and the left side is $1$); T6 and T7 need
no hypothesis on $a$, $b$, $\gamma$ or the sign of $c$; the tie example of §3 is tight for T6; at
$k \ge \operatorname{rank}\mathbf{A}$ T6, T7 give $a\|\mathbf{A} - \hat{\mathbf{A}}_{\mathrm{et}}\|^2
\le 0$, and for $a > 0$ the output is $\mathbf{A}$, which is right
($\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \le k$ then).

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Factorizations/SketchedLowRank.lean` (extended, registered) | 8 (E1 to E8: 2 definitions, 6 theorems) | +110 | `Matrix/Spectral/LowRank` (for `truncatedSVD`, if not already transitive) | S0 |
| 2 | `Sketching/Properties/ProjectionCost.lean` (new) | 4 (P1 to P4: 1 definition, 3 theorems) | 180 | `Sketching/Properties/SubspaceEmbedding`, `Matrix/Norms/Projector` | none |
| 3 | `LowRank/Structural/EarlyTruncation.lean` (new) | 7 (T1 to T7) | 420 | file 1, file 2, `Matrix/Norms/Loewner`, `Matrix/Spectral/LowRank` | files 1, 2 |

S2b is about 710 lines and 19 public declarations (brief: 700). Order in file 3: §3.3, §3.4. Files 1
and 2 are independent of each other and short: one agent may own both (CONTRIBUTING §11); file 1 is
written proved in its registered home (S1 §8 item 16), and a statement that resists goes to a side
file `Matrix/Factorizations/EarlyTruncated.lean` that merges at the wrap-up. File 3's T2 is the one
long proof (the formalization's `et_deterministic` and helpers are about 300 lines over ℝ; over `𝕜`
with the library's Frobenius and projector API, about 200). Under Q1 option (a), file 1 shrinks to E8
in projector form (or nothing: S6 applies S0's lemma), and T5 to T7 are spelled with
`rangeProjector (truncatedSVD (A * Ω) k) * A`.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/`): searched `LowRank/` and `Sketching/`
for early truncation and projection-cost preservation; none. Nothing to ledger.

**The maintainer's formalization** (read-only material, never cited, not ledgered; D13):
`~/Documents/Papers/LRA-paper/formal/LRA/Deterministic/EarlyTruncation.lean` (428 lines, real,
`Fin`-indexed): `et_deterministic` → T2 (over `𝕜`, any frame, any projector, the injection
predicate for `hlam`, the frame competitor in `hopt`); `frobSq_residual_split` → T1 (any $\mathbf{P}$);
`et_almost_sure` → T3 and T4 (`min 1 lam` replaced by `ha1` and `IsSubspaceInjection.mono`);
`sketch_optimality` → proof step of T5 (Eckart–Young, no basis `Qh`, no `IsBestRankApprox`);
`et_head`, `et_tail`, `et_cross`, `trace_W`, `young_aux`, `one_sub_headProj_mul`, the Frobenius helpers →
proof-internal or existing library API; `sketch_optimality_smul`, `gram_of_sketch`,
`et_deterministic_sketch`, `et_almost_sure_sketch` (the normalisation $t^{-1/2}\mathbf{\Omega}$) →
cut (Q8). The notes: `pcps-et-audited.tex` (`prop:et-deterministic`, `cor:et-almost-sure`: T2,
T4; `lem:et-decoupling`, `lem:et-smallball`, `lem:et-inverse-moments` and `thm:etRSVD` are the later
expectation, brief §8; `thm:etGN` is S6's composition); `pcps-audit.md` (item 1, squared costs,
adopted; item 2, no expectation from a PCP, T6's docstring; item 4, the (C4)-free high-probability
corollary, which S7 composes from T3 and Eckart–Young; items 9 and 12, dimensions and the
rank-deficient case, §3 list); `PCPS.tex` and `pcps-direct.tex` (`thm:direct`, `cor:direct` with the
Frobenius-preservation condition (C4): superseded by T2, not ported); `gaussian-pcps.tex`
(`def:pcp`, P1's shape with $\varepsilon$; `thm:mm`, `thm:PCPS`, `cor:lra`: S9 material; `cor:lra` is
CEMMP Lemma 3 at the early-truncation competitor, T6); `main.tex` (`alg:etRSVD`, `alg:etGN`: E1, E2).

**Literature**, locators confirmed against the PDFs:
- CEMMP (arXiv:1410.6801 v3, `/tmp/claude-1000/p0/papers/cemmp_15.pdf`): §1.1 and footnote 1
  (p. 1: subspace embeddings preserve every projection cost, need $O(\operatorname{rank}\mathbf{A})$
  columns); §2.2 (p. 4: $\|\mathbf{A}_{r\setminus k}\|_{\mathsf{F}}^2$ is a lower bound on every cost);
  Definitions 1, 2 (pp. 5 to 6); Lemmas 3, 4 (pp. 6 to 7, proofs: lower half at $\tilde{\mathbf{P}}$,
  $\gamma$-optimality, upper half at $\mathbf{P}^*$, $c \ge 0$ and $\gamma \ge 1$ in the last step);
  Lemmas 5, 6 (pp. 8 to 9: sufficient conditions, offset $c = -\min\{0,\operatorname{tr}\mathbf{E}_2\}$,
  which depends on the sketch, Q2); Lemma 10 (pp. 12 to 13); Theorem 12 and its short proof (pp. 15
  to 16: head embedding for $\mathbf{E}_1$, $\sum_{i\le k}\lvert\lambda_i(\mathbf{E}_2)\rvert \le \sqrt{k}
  \|\mathbf{E}_2\|_{\mathsf{F}}$, the tail–head AMM term for $\mathbf{E}_3$; Frobenius AMM only, Q9);
  §7.2 remark (p. 18) and §10.1 (pp. 22 to 23): early truncation.
- Woodruff 2014: Theorem 61 (p. 95, proof pp. 95 to 96): $\mathbf{S}$ a subspace embedding for the
  column space of $\mathbf{A}$ (unsquared $1 \pm \varepsilon$), $\mathbf{V}\mathbf{V}^{\mathsf{T}}$ the
  projector onto the top $k$ right singular vectors of $\mathbf{S}\mathbf{A}$, conclusion
  $\|\mathbf{A} - \mathbf{A}\mathbf{V}\mathbf{V}^{\mathsf{T}}\|_{\mathsf{F}} \le (1 + O(\varepsilon))
  \|\mathbf{A} - \mathbf{A}_k\|_{\mathsf{F}}$; the proof writes $(1+\varepsilon)^2$ where
  $(1-\varepsilon)^{-2}$ is meant, harmless at $O(\varepsilon)$. Its proof is P3 plus T6.
- TYUC SIMAX (arXiv:1609.00048 v2): §7.3.1, (7.3) (pp. 21 to 22), early-truncated GN
  ($\hat{\mathbf{A}}_{\mathrm{cemmp}} = \mathbf{V}\mathbf{T}^{\dagger}\llbracket\mathbf{U}^{*}\mathbf{W}
  \rrbracket_r$ with $\mathbf{V}$ the $r$ dominant left singular vectors of the range sketch and
  $\mathbf{\Psi}\mathbf{V} = \mathbf{U}\mathbf{T}$; the truncation acts on an $r$-row matrix, so it is
  the identity, and the output is E2 under the rank hypothesis), "the results in Cohen et al. imply"
  $(1+\varepsilon)$ at $\Theta(r/\varepsilon^2)$ for both sketches; §7.4 (p. 23), weakest in their tests.
- Musco and Musco 2020 (arXiv:2004.08434): not in hand; brief §9.3's "Theorem 2, conditions (i) to
  (iii)" and "Definition 1, Corollary 7" are not cited until read (S1 §5's rule for Gittens and
  Mahoney). CEMMP's proof of Theorem 12 carries the same three terms.

**Citations** (keys: `Woodruff2014` and `TroppYurtseverUdellCevher2017` exist;
`CohenElderMuscoMuscoPersu2015` is new and enters with file 2, the STOC 2015 paper with the arXiv v3
eprint, whose numbering the locators use; D13):

| statement | citation | relation to the printed statement |
|---|---|---|
| E1 | [Woodruff2014, Theorem 61]; [CohenElderMuscoMuscoPersu2015, §7.2, §10.1] | there the sketch on the left and rows projected; here transposed, any field |
| E2 | [TroppYurtseverUdellCevher2017, §7.3.1, (7.3)] | there through a basis and QR with a vacuous final truncation; here the oblique projector of the truncated sketch |
| E3 to E8 | none (API and bridges; each docstring says what it is for) | |
| P1 | [CohenElderMuscoMuscoPersu2015, Definitions 1 and 2] | there $\varepsilon$, rank exactly $k$, real; here $a$, $b$, rank at most $k$, `𝕜` |
| P3 | [CohenElderMuscoMuscoPersu2015, §1.1]; [Woodruff2014, proof of Theorem 61] | there a remark and a proof step; here every $k$, offset $0$, constants carried over |
| P4 | [CohenElderMuscoMuscoPersu2015, Lemmas 3 and 4] | there a minimizer over a set; here any competitor, constants $a$, $b$ |
| T1 to T5 | proved without a literature source; sketch quantities as in [CohenElderMuscoMuscoPersu2015, proof of Theorem 12] | D13; the manuscript is never cited |
| T6 | [CohenElderMuscoMuscoPersu2015, Lemma 3, §7.2] | there $\varepsilon$; here $a$, $b$ and the named output |
| T7 | [Woodruff2014, Theorem 61] | there unsquared $1 \pm \varepsilon$, $1 + O(\varepsilon)$; here squared constants $a$, $b$ |

**Result ids** (D11; checked against the ids in `NLAlib/` (`ose-def`, `amm-ose`,
`oblique-projection-error-split`, `truncated-range-finder-structural-bound`, the Eckart–Young ids):
no collision): `projection-cost-preserving-sketch` (P1, P4; one node titled from P1's bold name),
`early-truncation-structural-bound` (T2 to T5; bold head "The early-truncation structural bound"),
`early-truncation-pcp-bound` (T6, T7; new, the uniform routes). The brief's `etrsvd` and `etgn` stay
for the probabilistic theorems (S6, S7, the later expectation). E1 to E8, P2, P3, T1 carry none.

## 6. Cut, and why

- *The manuscript's normalised forms* ($\mathbf{S} = t^{-1/2}\mathbf{\Omega}$, `gram_of_sketch`, the
  `*_sketch` statements) and `min 1 lam`: the consumer passes the normalised test matrix, and
  `IsSubspaceInjection.mono` supplies $\min\{1,\lambda\}$ (Q8).
- *The (C4)-dependent direct theorem* (`thm:direct`, `cor:direct` of the notes): dominated by T2,
  which needs no Frobenius preservation (rule 6; the notes' own audit item 8).
- *A linear high-probability corollary* ($\|\mathbf{A} - \hat{\mathbf{A}}_{\mathrm{et}}\|^2 \le
  \frac{1+\alpha_2}{1-\alpha_1-2\alpha_3}\mathrm{OPT}^2$ on the event): it needs
  $\|\mathbf{E}\|_{\mathsf{F}} \le \|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}$, true only in the
  top-$k$ reading; S7 composes T3 with Eckart–Young there.
- *Named instances of T2 and T3 for `earlyTruncatedRSVD`*: T5 is the consumer-facing form; a user
  wanting T2 or T3 at $\hat{\mathbf{P}}$ gets `hopt` from T5's two-line proof step.
- *A predicate for sketch optimality, definitions of $w$, $\chi$*: Q3.
- *The Frobenius form of a subspace embedding for all left multiples* (P3's column step,
  $a\|\mathbf{U}\mathbf{X}\|_{\mathsf{F}}^2 \le \|\mathbf{S}\mathbf{U}\mathbf{X}\|_{\mathsf{F}}^2$ for a
  non-orthonormal $\mathbf{U}$): proof-local; a candidate public Sketching lemma at the wrap-up if S7
  or S9 needs it again.
- *`range_earlyTruncatedRSVD_le`, a `_def` lemma for E2, the basis form of E2*
  ($\mathbf{Q}(\mathbf{\Psi}^{\mathsf{H}}\mathbf{Q})^{+}\mathbf{\Psi}^{\mathsf{H}}\mathbf{A}$ for a basis
  of $\operatorname{range}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$): no consumer; S0's
  `obliqueProjector_eq_of_range_eq` and `mul_sketchAndSolve` give the basis form in one rewrite.
  Additive.
- *Early truncation as an RSVD with a data-dependent test matrix*
  ($\hat{\mathbf{A}}_{\mathrm{et}} = $ `rsvd A (Ω * rangeProjector (truncatedSVD (A * Ω) k)ᴴ)`, from S1's
  L1): true, no consumer.
- *Early-truncated Nyström*: not in the brief.
- *PCP closedness and measurability, composition of PCPs, the head–tail constructor, CEMMP Lemmas 5
  and 6*: S9 (Q9).
- *A uniform-PCP statement for early-truncated GN*: its completion term is probabilistic (S6, S7, S9).
- *The $2\times 2$ early-truncation lower bound*: draft only (D15).

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule, Q1 and Q2 go to the
maintainer at the checkpoint after S2b; Q1 is the joint naming question S2a's §7 Q1 and §8 defer to
here. The rest proceed as recommended.

**Q1. Names for truncated outputs, late and early, decided jointly (hard; for the maintainer).** The
round has five truncated outputs: late truncation of the RSVD, Nyström and GN (S2a), and early
truncation of the RSVD and GN (S2b). The maintainer's rule spells every error as $\mathbf{A}$ minus
the named output, and makes projector and basis forms bridges, never statement shapes. Late
truncation composes two named functions; early truncation does not: its only spellings are a
projector form or a new name.
- *(a) No names anywhere.* Late `truncatedSVD (rsvd A Ω) k` (S2a as drafted); early
  `rangeProjector (truncatedSVD (A * Ω) k) * A` and `obliqueProjector (truncatedSVD (A * Ω) k) Ψᴴ * A`.
  For: no definitions, nothing to unfold. Against: early-truncated errors are written in the
  projector form the rule excludes (the form `rsvd` was named to avoid); the GN formula is long and
  recurs in S6, S7, S9; docstrings and the explorer have no declaration to point at.
- *(b) Names for early truncation only* (§3 as written). `earlyTruncatedRSVD A Ω k`,
  `earlyTruncatedGeneralizedNystrom A Ω Ψ k`; late stays `truncatedSVD (rsvd A Ω) k`,
  `truncatedSVD (nystrom H Ω) k`, `truncatedSVD (generalizedNystrom A Ω Ψ) k`. The principle: an
  output gets a definition exactly when it is not a composition of named functions. For: both
  families obey the rule; late truncation keeps S2a's advantages (it reads as the sources'
  $\llbracket\hat{\mathbf{A}}\rrbracket_k$, and S2a's general lemmas for `IsBestRankApprox` apply
  with no unfolding); the early names need only the small API of E3 to E8. Against: a user searching
  "truncated randomized SVD" finds `earlyTruncatedRSVD` but no `truncatedRSVD`, and must read the
  module docstring for the late spelling.
- *(c) Names for all five.* Late `def`s with `_def` lemmas (candidates `truncatedRSVD`,
  `truncatedNystrom`, `truncatedGeneralizedNystrom`, or `fixedRankRSVD` and siblings, TYUC's and MT's
  "fixed-rank"), early as in (b). For: one search pattern, symmetric docstrings. Against: three more
  definitions with rank and range API (about 60 lines); every late statement of S2a (its T1 to T12) and
  S3 to S7 changes shape, and each proof unfolds before using B13, B14, B18; `truncatedRSVD` is one
  letter from `truncatedSVD` (`fixedRank…` avoids that).
- *Rejected:* a projector-valued definition such as `rangeProjector (truncatedSVD X k)` under a name:
  the statements would still be projector forms.

Recommendation **(b)**. Spelling `earlyTruncatedRSVD` and `earlyTruncatedGeneralizedNystrom`, word
order and capitals as in `truncatedSVD` and the literature's "early-truncated RSVD"; the theorem
names follow (`frobNorm_sub_earlyTruncatedRSVD_sq_le`). Rework if reversed after S6: the statement
shape of every early-truncated result of S2b, S6, S7, S9 (to (a)), or of every late result of S2a and
S3 to S7 (to (c)). Timing: decide at the checkpoint, before S3's skeleton (S2a Q1's deadline). The S2b
skeleton can proceed under (b): (c) only adds late names, and (a) is a mechanical unfolding inside
S2b.

**Q2. The shape of `IsProjectionCostPreserving` (hard).** Five choices, one recommendation each:
1. *Constants.* (a) $a$, $b$, the library's subspace-embedding convention, $\varepsilon$ written as
   $1 \mp \varepsilon$; (b) $\varepsilon$ as in CEMMP Definition 1. Recommend (a): CEMMP's
   one-sided Definition 2 is $a = 1$, so one predicate covers both definitions and P4 covers both
   Lemmas 3 and 4; P3 carries the embedding's $a$, $b$ unchanged; S9's family corollaries quote the
   Sketching round's constants directly.
2. *Offset.* (a) $\exists c \ge 0$ inside the predicate, CEMMP's "for some fixed non-negative
   constant $c$"; (b) a parameter `c` (the brief's candidate); (c) offset $0$ only. Recommend (a): the
   offset of CEMMP's constructors depends on the sketch ($c = -\min\{0, \operatorname{tr}\mathbf{E}_2\}$,
   Lemma 6), so in S9's tail form, `μ.real {ω | ¬ IsProjectionCostPreserving A (A * Ω ω) k a b} ≤ δ`,
   it must be chosen per $\omega$, which a parameter cannot express; $c \ge 0$ is what Lemma 3
   needs for $\gamma > 1$; (c) excludes CEMMP's constructors. Cost: the two halves cannot be split into
   fields (CONTRIBUTING §5.2's "two-sided bounds are two theorems" does not apply to a predicate whose
   halves share a witness).
3. *Ranks.* At most $k$ (recommended) or exactly $k$ (CEMMP): with "exactly", T6 fails when
   $\operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k < k$ and the predicate is vacuous
   for $k > \lvert m \rvert$.
4. *Arguments.* `A Ã k a b`, data first (recommended; the brief's candidate; as `IsBestRankApprox C k Y`),
   or sketch first as `IsSubspaceEmbedding S U a b`. In the latter the first argument is the sketching
   operator, not sketched data, so the analogy does not carry over; $\tilde{\mathbf{A}}$ is any
   matrix with the rows of $\mathbf{A}$, not only $\mathbf{A}\mathbf{\Omega}$.
5. *Name.* `IsProjectionCostPreserving` (recommended, CEMMP's term) or `IsPCPSketch`.

Rework if changed: P1 to P4, T6, T7 and all of S9.

**Q3. The core's hypothesis form (moderately hard).** Options: (a) as §3.3: any frame $\mathbf{Z}$,
any orthogonal projector of rank at most $k$ with the one-competitor sketch optimality `hopt`,
the head as `IsSubspaceInjection Ωᴴ Z a`, $w$ and $\chi$ written out in AMM shape; (b) the manuscript's
encoding: SVD blocks $\mathbf{A}_1 = \mathbf{U}_1\mathbf{\Sigma}_1\mathbf{V}_1^{\mathsf{H}}$, a basis
`Qh` with $q \le k$ columns, `IsBestRankApprox` of the sketch and $\hat{\mathbf{P}}\mathbf{Y} =
\mathbf{Y}$; (c) (a) with definitions for $w$, $\chi$ or a predicate for the sketch optimality.
Recommendation (a). The general frame is S1's (Q3 there) and costs nothing in the proof (the
competitor $\mathbf{P}_{\mathbf{A}\mathbf{Z}}$ only needs to be a contraction); the general projector
covers `truncatedSVD`'s choice, any other best approximation, and a measurable selector (Q7) with one
statement; the injection is the hypothesis S7 produces (`IsObliviousSubspaceEmbedding` for
$\operatorname{range}\mathbf{Z}$); the AMM shapes match `HasJLMoment`'s events after
`conjTranspose_conjTranspose` (hence $-\mathbf{E}\mathbf{Z}$ kept in $\chi$, S1 §8 item 7). (b)
repeats five hypotheses and fixes a basis (D1 rejected bases for measurability); (c) adds unfolding at
every use (S1 Q4), and the sketch optimality is a one-line inequality in three statements. Rework if
changed: the hypothesis lines of T2 to T5 and S7's uses.

**Q4. Multiplied forms for the PCP routes (not hard).** P4, T6, T7 conclude
$a x \le \gamma b x'$, not $x \le \gamma\frac{b}{a}x'$: no hypothesis $0 < a$, no division, and the
statement is true (vacuous) for $\varepsilon \ge 1$; S2a's reverse Eckart–Young set the precedent of
the subtraction-free shape. The docstrings give the ratio. Additive: a division corollary if S9 wants
one.

**Q5. Placement (not hard).** E1 to E8 beside `rsvd` and `generalizedNystrom` in the Matrix layer (D12);
the predicate in `Sketching/Properties/ProjectionCost.lean` (D12); T1 to T7 in
`LowRank/Structural/EarlyTruncation.lean`. Unlike S2a's general lemmas (S2a Q4), T1 to T4 cannot move
to the Matrix layer: they take Sketching predicates. T1 alone is matrix analysis, kept beside its
consumers. Rework: file moves.

**Q6. Corrections of record (information).** Brief §4.3 ("Early truncation by OSE plus AMM, Woodruff
Theorem 61 shape"), §7 S7 and §9.3: Woodruff Theorem 61 is the subspace-embedding route for the whole
column space (T7, deterministic, S2b), not the OSE-plus-AMM tail, whose published source is the
term-by-term argument of CEMMP's proof of Theorem 12; S7's citation becomes CEMMP. Brief §9.3's
Musco and Musco locators are not cited until the paper is read. Brief §5.1's table: early-truncated GN
has a published algorithmic source, TYUC SIMAX (7.3), credited to CEMMP §10.1. Brief §5.4 "(to
confirm against CEMMP)": confirmed, with rank exactly $k$, $0 \le \varepsilon < 1$ and $c \ge 0$ there.

**Q7. Choice and measurability (not hard; for the S7, S9 notes).** The early-truncated error depends
on `truncatedSVD`'s choice (§3 example) and is not known to be measurable in $\mathbf{\Omega}$. Tails
need no measurability (`measure_mono` holds for any sets), so S7 and S9 state tails on the named
outputs. An expectation (the later etRSVD, brief §8) needs a measurable selector $\mathbf{Y}(\omega)$
of best approximations of $\mathbf{A}\mathbf{\Omega}(\omega)$; T2 to T4 apply to
$\mathbf{P} = \mathbf{P}_{\mathbf{Y}(\omega)}$ unchanged, with `hopt` from the selector's optimality.
This is S2a Q3 option (a), and the reason T2 to T4 take a general projector.

**Q8. Scaling (not hard).** The analysis wants $\lambda \approx 1$, so the user's test matrix is the
normalised one ($t^{-1/2}\mathbf{G}$ for a Gaussian, as D2's per-family lemmas already scale the
Sketching predicates). The named output at $c\mathbf{\Omega}$ cannot be identified with the one at
$\mathbf{\Omega}$ under ties; if a consumer needs the output at the raw $\mathbf{\Omega}$ and the
analysis at the scaled one, T4 applies with `hopt` rescaled (`frobNorm_smul`, both sides scale by
$\lvert c \rvert$). No scalar parameter in T5.

**Q9. The head–tail constructor and spectral AMM (information; for the S9 note).** Brief D7 and §7
S9 hold the $O(k/\varepsilon^2)$ constructor until "spectral AMM exists". CEMMP's short proof of
Theorem 12 (p. 16) uses only a head subspace embedding (for $\mathbf{E}_1$), Frobenius AMM for the
tail–tail term with $\sum_{i\le k}\lvert\lambda_i\rvert \le \sqrt{k}\,\|\cdot\|_{\mathsf{F}}$, Frobenius
AMM for the tail–head term, and the tail's Frobenius preservation; spectral AMM enters only through
Lemmas 10 and 11, for the stable-rank refinement. So S9 can build the constructor from
`IsObliviousSubspaceEmbedding` and the `HasJLMoment` AMM tails that exist, at the cost of
$\log(1/\delta)$ in the dimension. Its deterministic half (CEMMP Lemma 6 at the top-$k$ split, with
offset $c = \max\{0, \|\mathbf{E}\|_{\mathsf{F}}^2 - \|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2\}$, of
the same three terms as T2 plus condition (iv)) belongs to `ProjectionCost.lean` and is S9's to design;
Q2's existential offset is what lets it fit. Recommendation: leave it to S9, which is now unblocked.

**Q10. E8 in S2b (not hard).** The deterministic split of early-truncated GN is one line from S0's
split at $\mathbf{X} = \llbracket\mathbf{A}\mathbf{\Omega}\rrbracket_k$; stating it beside the
definition, in the named form the maintainer's rule asks for, gives S6, S7 and S9 one shared bridge
instead of three unfoldings. S6 keeps the Gaussian completion and the composition with an
early-truncated RSVD bound taken as a hypothesis (brief §7 S6).

## 8. Amendments from the review (2026-10-15)

Review of this note (2 medium, 7 low), all nine amendments accepted by the orchestrator; none
rejected, none corrected on inspection. A1 is taken in its option (i) (item 1). Q1 decided by the
maintainer as (b), Q2 accepted as the review says (items 10, 11); Q3 to Q10 stand as recommended
(item 12), Q6 and Q10 amended by item 3. The review re-derived T2 step by step over `𝕜` (any frame,
any star projection of rank at most $k$, `hopt`, every real $a$), checked T3 to T7 and P3, P4 against
CEMMP's proof of Lemma 3, recomputed the tie example and the three necessity examples, confirmed
the Woodruff Theorem 61 reading from the PDF (P3 plus T6 in D2's orientation, $a = (1-\varepsilon)^2$,
$b = (1+\varepsilon)^2$), and checked that every library name §1 and §3 rely on exists with the
stated shape and that no new name collides. Where an item below contradicts §0 to §7, it supersedes
them; §3 stays as drafted.

1. **A1, T1 is not a LowRank statement** (amends §3.3, §4 file 3's count, §5's map of
   `frobSq_residual_split`, the Result-id paragraph). For any $\mathbf{B}$,
   $\|\mathbf{B}\|_{\mathsf{F}}^2 = \|\mathbf{B}\mathbf{Z}\|_{\mathsf{F}}^2 + \|\mathbf{B} -
   \mathbf{B}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\|_{\mathsf{F}}^2$ is `IsStarProjection.frobNorm_sq_eq_add`
   (`Matrix/Norms/Projector.lean`) at $\mathbf{B}^{\mathsf{H}}$ and $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$
   (`HasOrthonormalCols.isStarProjection_mul_conjTranspose`), with `frobNorm_conjTranspose` and
   `frobNorm_mul_conjTranspose_right`; T1 specialised it to $\mathbf{B} = \mathbf{A} -
   \mathbf{P}\mathbf{A}$ with a decorative $\mathbf{P}$, a one-off shape (CONTRIBUTING §5.2, §8).
   Option (i) is taken: T1 is dropped as a public declaration and the derivation is a private
   lemma of file 3, used by T3 only (T2's route never uses the split). Option (ii), a Matrix-layer
   twin `HasOrthonormalCols.frobNorm_sq_eq_add_mul` beside `IsStarProjection.frobNorm_sq_eq_add`, has
   no consumer outside file 3 and would touch a registered file; it is additive if S7 or S9 wants
   it. File 3 holds six statements (T2 to T7).
2. **A2, the sketch-optimality wording matches `hopt`** (§3.3 opening paragraph; the docstrings of T2
   to T4). The competitor is the matrix $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$,
   not the projector $\mathbf{P}_{\mathbf{A}\mathbf{Z}}$. §3.3's first sentence reads: "All are about
   any orthogonal projector $\mathbf{P}$ of rank at most $k$ whose sketch residual is at most that of
   the frame's competitor $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}\mathbf{\Omega}$,
   $\|\mathbf{A}\mathbf{\Omega} - \mathbf{P}\mathbf{A}\mathbf{\Omega}\|_{\mathsf{F}} \le
   \|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}$ (implied by being at least as good on the sketch as
   $\mathbf{P}_{\mathbf{A}\mathbf{Z}}$)". The same phrase replaces "at least as good on the sketch as
   the frame's competitor" in the third departure bullet.
3. **A3, early-truncated GN: the $\varepsilon$ exponents and the primary bound** (§5 "Literature",
   TYUC entry; E2's docstring; Q6; Q10; §0's consumers row for E1 to E8). **Maintainer decision
   (2026-10-15):** the early-truncated GN bound of the maintainer's notes, $t = O(k/\varepsilon^2)$
   on the right and $s = O(k/\varepsilon)$ on the left, in expectation, is the primary statement,
   ported "proved without a literature source"; TYUC SIMAX is cited for the algorithm, (7.3), only.
   What the sources say (checked by the review): TYUC §7.3.1 states
   $\hat{\mathbf{A}}_{\mathrm{cemmp}}$ as an algorithm and proves nothing about it; its one bound is
   the remark that CEMMP's results imply (1.5) at $\Theta(r/\varepsilon^2)$ for **both** sketch
   sizes, with high probability and unspecified constants. There is no $\varepsilon^3$ for
   early-truncated GN in TYUC. **Correction of record (A3):** the $\varepsilon^{-3}$ figure in the
   maintainer's files is the triangle-inequality baseline for **late**-truncated GN
   (`GN_truncated.tex` line 475, "$s \gtrsim t/\varepsilon^2 = k/\varepsilon^3$"; `table.tex`, the
   commented row "Truncated GN"), which the notes' `thm:tGN` improves to $k/\varepsilon^2$; it is
   not an early-truncation figure. The notes' `thm:etGN` is E8 (this note), the Gaussian completion
   identity at the actual rank $q \le k$ (S6), and `thm:etRSVD`, the early-truncated RSVD in
   expectation (brief §8, deferred). S2b ports no TYUC bound, and E8 is the deterministic half of the
   primary statement, in the named form. Three sentences:
   - (i) E2's docstring, after the TYUC citation: "TYUC state the algorithm and report, from CEMMP,
     a high-probability $(1+\varepsilon)$ bound at $\Theta(r/\varepsilon^2)$ for both sketch sizes
     with unspecified constants; no bound is taken from it. The bounds on this output compose
     `frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq` with a bound on the sketch-and-solve term
     and an early-truncated randomized SVD bound." (Stage names stay out of library docstrings.)
   - (ii) Q6 adds: "The early-truncated GN expectation bound with $t = O(k/\varepsilon^2)$ and
     $s = O(k/\varepsilon)$ has no literature source; S6 states it 'proved without a literature
     source' as a composition (brief §9.3), with the early-truncated RSVD expectation as a
     hypothesis until brief §8's deferral is lifted. The $\varepsilon^3$ exponent is the
     triangle-inequality baseline for late-truncated GN, not an early-truncation figure."
   - (iii) Q10 adds: "S6's statement this round is conditional on $\mathbf{\Omega}$ (the completion
     factor $1 + q/(s - q - 1)$ at $q = \operatorname{rank}\llbracket\mathbf{A}\mathbf{\Omega}
     \rrbracket_k$ times $\|\mathbf{A} - \hat{\mathbf{A}}_{\mathrm{et}}\|_{\mathsf{F}}^2$) or takes
     the early-truncated RSVD bound as a hypothesis; the unconditional $(1+\varepsilon)$ expectation at
     $t = 900k/\varepsilon^2$ waits for brief §8."
4. **A4, the $k \ge \operatorname{rank}\mathbf{A}$ case** (§3 degenerate list; §3.4's "Degenerate"
   paragraph). "For $a > 0$ the output is $\mathbf{A}$, which is right
   ($\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) \le k$ then)" is replaced by: "for $a > 0$ the
   PCP hypothesis at such $k$ forces $c = 0$ (upper half at $\mathbf{P} = \mathbf{P}_{\mathbf{A}}$,
   of rank $\operatorname{rank}\mathbf{A} \le k$) and then $a\|\mathbf{A} -
   \mathbf{P}_{\mathbf{A}\mathbf{\Omega}}\mathbf{A}\|_{\mathsf{F}}^2 \le 0$ (lower half at
   $\mathbf{P}_{\mathbf{A}\mathbf{\Omega}}$), so $\operatorname{range}\mathbf{A} \subseteq
   \operatorname{range}(\mathbf{A}\mathbf{\Omega})$, $\operatorname{rank}(\mathbf{A}\mathbf{\Omega}) =
   \operatorname{rank}\mathbf{A} \le k$, the truncation is the identity and the output is
   $\mathbf{A}$".
5. **A5, column space and row space** ("Literature checks"; T7's docstring). "a subspace embedding
   of the whole column space" reads "a subspace embedding of the whole column space (the row space of
   $\mathbf{A}$ in D2's orientation)". Woodruff's statement has the typo "$\mathbf{S}$ an $m \times d$
   matrix" ($m \times n$ is meant); the implementer need not chase it. T7's docstring says "there
   transposed: Woodruff's column space of $\mathbf{A}$ is the row space here".
6. **A6, Q2 item 2's "cannot be fields" is overstated** (§2 "Bundles"; Q2 item 2). The halves
   cannot be fields of a predicate without an offset argument, but the brief's parameterised
   candidate can be a structure `IsProjectionCostPreservingWithOffset A Ã k a b c` with `lower` and
   `upper` fields (the `IsSubspaceEmbedding` style), and the $\exists$-form is then
   `∃ c, 0 ≤ c ∧ …` of it. Either direction is additive. The recommendation stands (the
   $\exists$-form is the public interface, because S9's tail form chooses $c$ per $\omega$); the
   parameterised structure is the free refinement if S9 or a user needs the offset explicitly (CEMMP
   Lemma 6's $c = -\min\{0, \operatorname{tr}\mathbf{E}_2\}$). §2's "they cannot be separate fields"
   and Q2's "Cost: the two halves cannot be split into fields" read so.
7. **A7, CEMMP's orientation in E1's docstring.** §10.1 is transposed (sketch on the left, the top
   $k$ right singular vectors of the sketch, output $\mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{T}}$);
   §7.2's remark and Definition 1 use this library's orientation ($\tilde{\mathbf{A}} =
   \mathbf{A}\mathbf{R}^{\mathsf{T}}$, projectors on the left). E1 cites "[CohenElderMuscoMuscoPersu2015,
   §10.1], there transposed; [CohenElderMuscoMuscoPersu2015, §7.2], a remark in this orientation".
8. **A8, the usage snippet's branch** (end of §3.3). S1's L2 call
   `exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD (p := Fin k)` needs
   `k ≤ Fintype.card n`; the snippet's comment adds "($k \le \lvert n \rvert$; for larger $k$ the
   output is untruncated by E6 and S1's bound applies)", so the S7 note carries the branch.
9. **A9, bookkeeping** (§1; "Departures from the brief"). §1's Mathlib-deviations line stands
   (`docs/design/Mathlib-deviations.md`, "Additions where Mathlib has nothing", added in the commit
   that adds the definitions). The first departure bullet is no longer a departure: the early names
   are the maintainer's decision (item 10). Corrections of record: brief D1's table ("early
   truncations: no new names") reads "early truncations: `earlyTruncatedRSVD`,
   `earlyTruncatedGeneralizedNystrom` (S2b Q1, maintainer, 2026-10-15)"; S2a §8 item 13's joint
   question is closed as (b), and S2a's statements need no change (late truncation stays unnamed).
10. **Q1 decided by the maintainer as (b): names for the early-truncated outputs only.**
    `earlyTruncatedRSVD A Ω k`, `earlyTruncatedGeneralizedNystrom A Ω Ψ k`; late truncation stays
    `truncatedSVD` of the named output (`truncatedSVD (rsvd A Ω) k`, `truncatedSVD (nystrom H Ω) k`,
    `truncatedSVD (generalizedNystrom A Ω Ψ) k`). The principle: an output gets a definition exactly
    when it is not a composition of named functions. (c) stays additive (S2a §8 item 13). The search
    objection is met by one sentence in `SketchedLowRank.lean`'s module docstring ("late truncation
    is spelled `truncatedSVD (rsvd A Ω) k`"), which replaces its "Truncated variants have no names".
    The brief's "Maintainer decisions" records this.
11. **Q2 accepted as the review says**, all five items: constants $a$, $b$ (strictly more general,
    CEMMP's Definition 2 at $a = 1$); the offset $\exists c \ge 0$ inside the predicate (forced by S9's
    tail form, with item 6's parameterised refinement additive); rank at most $k$ (forced by T6 at a
    rank-deficient truncation and by `mono`; CEMMP §1.1's own phrasing); data-first `A Ã k a b`; the
    name `IsProjectionCostPreserving`.
12. **Q3 to Q10 stand as recommended.** The review checked Q3 (general frame, general projector,
    `hopt` inline), Q4, Q5 (T2 to T4 take Sketching predicates, so cannot move down), Q7, Q8, Q9
    (CEMMP's short proof of Theorem 12 uses only a head embedding and Frobenius AMM) and Q10. Q6 and
    Q10 are amended by item 3.
13. **Placement** (amends §3.1 "Written proved" and §4's last paragraph, as S2a §8 item 18).
    `Matrix/Factorizations/SketchedLowRank.lean` is registered and proved; E1 to E8 go into it only
    once proved. A statement still `sorry` goes into the side file
    `Matrix/Factorizations/EarlyTruncated.lean`, which says it merges into `SketchedLowRank.lean` at
    the wrap-up. Files 2 and 3 are new and may take `sorry` statements.
14. **Files and statements** (amends §4):

    | # | File | Statements | Lines (est.) | Imports (new) | Depends on |
    |---|---|---|---|---|---|
    | 1 | `Matrix/Factorizations/SketchedLowRank.lean` (extended, registered; or its side file, item 13) | 8 (E1 to E8) | +110 | none (`truncatedSVD` is transitive) | S0 |
    | 2 | `Sketching/Properties/ProjectionCost.lean` (new) | 4 (P1 to P4) | 180 | `Sketching/Properties/SubspaceEmbedding`, `Matrix/Norms/Projector` | none |
    | 3 | `LowRank/Structural/EarlyTruncation.lean` (new) | 6 (T2 to T7) | 400 | files 1, 2, `Matrix/Norms/Loewner` | files 1, 2 |

    S2b is 18 public declarations. `CohenElderMuscoMuscoPersu2015` enters `docs/references.bib` with
    file 2.
15. **Docstrings are LaTeX** (CONTRIBUTING §6 item 5), with the notation table; Lean names in
    backticks, never inside `$…$`; T2 to T5 say "proved without a literature source" and cite only
    the published inputs (D13); the Chen–Persson manuscript is never cited.

### Skeleton notes

Written and proved together (2026-10-15); no `sorry`, no side file (item 13's
`Matrix/Factorizations/EarlyTruncated.lean` was not needed). All 18 statements of item 14 are
proved, with the signatures of §3 (T1 dropped by item 1): E1 to E8 in
`Matrix/Factorizations/SketchedLowRank.lean` (now 389 lines, written proved, module docstring
amended by item 10), P1 to P4 in `Sketching/Properties/ProjectionCost.lean` (154 lines), T2 to T7 in
`LowRank/Structural/EarlyTruncation.lean` (374 lines). The two new files are not registered in
`NLAlib.lean`. `CohenElderMuscoMuscoPersu2015` is in `docs/references.bib`; the three names are in
`docs/design/Mathlib-deviations.md`, "Additions where Mathlib has nothing".
- Two public lemmas beyond the note, in file 1, the residual bridges of the maintainer's error rule
  as for `rsvd` and `generalizedNystrom`: `sub_earlyTruncatedRSVD` and
  `sub_earlyTruncatedGeneralizedNystrom` (`A - earlyTruncatedRSVD A Ω k = (1 - P̂) * A`); E8's proof
  uses both.
- Routes as drafted, with two simplifications. T2 never forms $\mathbf{I} - \mathbf{P}$: the tail
  and the cross term go through $\|\mathbf{X} - \mathbf{P}\mathbf{X}\|_{\mathsf{F}}^2 =
  \|\mathbf{X}\|_{\mathsf{F}}^2 - \langle\mathbf{P}, \mathbf{X}\mathbf{X}^{\mathsf{H}}\rangle_{\mathsf{F}}$ and
  $\langle\mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X} - \mathbf{P}\mathbf{X}\rangle_{\mathsf{F}} =
  \langle\mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X}\rangle_{\mathsf{F}}$, so no `DecidableEq m`;
  T4 is one `nlinarith` on $\theta(1-\theta)\lambda^2 s^2 \le \theta\lambda c + \chi^2$ from T3 and
  $(\theta\lambda s - \chi)^2 \ge 0$. P3 is column by column from
  `isSubspaceEmbedding_iff_forall_mem_range`, as §3.2 says.
- Private lemmas (file 3 unless said): the head–tail split (item 1, T3 only); the two star-projection
  identities above; $\langle\mathbf{P}, \mathbf{W}\rangle_{\mathsf{F}} \le \sqrt{k}\,
  \|\mathbf{W}\|_{\mathsf{F}}$ for a star projection of rank at most $k$; in file 2, the Frobenius form
  of a subspace embedding for every $\mathbf{U}\mathbf{C}$ (§6's candidate).
- For the wrap-up: the squared-residual identity is the Frobenius twin of
  `IsStarProjection.frobNorm_sq_eq_add` without the identity matrix and could join
  `Matrix/Norms/Projector.lean`; the orthogonality identity is
  `IsStarProjection.frobInner_mul_one_sub_mul` without the identity; file 2's Frobenius form
  generalizes `mul_frobNorm_sq_le_of_smul_one_le` and `frobNorm_mul_sq_le_of_conjTranspose_mul_self_le`
  from the whole space to the range of any $\mathbf{U}$ and is wanted public if S7 or S9 needs it; the
  $\sqrt{k}$ bound may recur in S9's head–tail constructor.
