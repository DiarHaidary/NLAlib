# Design note: LowRank stage S9, projection-cost-preserving sketches (probabilistic)

Status: drafted 2026-10-16 and reviewed 2026-10-16; §8 records the review's amendments and
supersedes §0 to §7 where they differ. Awaits the maintainer's go-ahead on the cut (§8 item 13),
which also confirms Q1 (a) and the predicate's name (§8 item 7). Drafted under
`docs/PORT_LOWRANK.md` (maintainer decisions of 2026-10-15,
binding: D7, PCPs in this round, deterministic part in S2b and probabilistic part here; every error
spelled as $\mathbf{A}$ minus the named output, `A - earlyTruncatedRSVD A (X ω) k`; docstrings write
outputs as $\mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)$ and
$\mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)$ and show named constants
inside their formulas through value markers; the Chen–Persson manuscript is never cited; D2, D3,
D10 to D15; §5.3, §5.4, the S9 entry of §7, §9.3), the maintainer's instruction of 2026-10-16 ("for
the PCPs this might be a lot of work. Make sure stuff gets placed in the right place in the
library"), and `docs/design/LowRank-S2b.md` (§8 overrides its §3; proved: the predicate
`IsProjectionCostPreserving`, `IsProjectionCostPreserving.mono`, the row-space constructor
`IsSubspaceEmbedding.isProjectionCostPreserving`, the consequence
`IsProjectionCostPreserving.mul_frobNorm_sub_mul_sq_le`, the uniform-PCP early-truncation corollary
`IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le` and the sharper core
`IsSubspaceInjection.frobNorm_sub_mul_sq_le`). S6 and S6b are proved (`LowRank/Gaussian/`); S7 (the
OSI and OSE routes, `LowRank/Oblivious/`) has no note yet. Probabilistic statements are over `𝕜`
wherever their inputs are (CountSketch, the generic constructors), over ℝ where approximate matrix
multiplication from the JL moment property is (D3; `Sketching/Properties/MatrixMultiplication.lean`
is real only). Every shape, rank and target rank (§3.0).

Departures from the brief, each argued below:
- **The head–tail constructor is in the round, not deferred.** The brief (D7, §7 S9) holds the
  $O(k/\varepsilon^2)$ constructor until spectral-norm AMM exists. S2b Q9 found that CEMMP's short
  proof of Theorem 12 needs only a head subspace embedding and Frobenius AMM; this note confirms it
  term by term (§3.3) and states it. What it costs without spectral AMM is the failure probability:
  JL moments at $p = 2$ give $O((k+1)/(\varepsilon^2\delta))$ rows, not
  $O((k + \log(1/\delta))/\varepsilon^2)$. The $\log(1/\delta)$ form, and column sampling, are what
  need spectral AMM; they are deferred with their exact needs (§6, items D1, D2).
- **Four families, not every family.** Gaussian, Rademacher, sub-Gaussian (real) and CountSketch
  (any field) compose from existing OSE and JL-moment results with modest work. Haar, SRHT and
  sampling each need a missing lower-layer piece and are deferred (§6, D2 to D4). Every family with an
  OSE gets a PCP at dimension $\operatorname{rank}\mathbf{A}$ now, through the row-space constructor
  (C4), with no per-family statement.
- **No per-family early-truncation corollaries.** Through a PCP they are dominated by S7's core route
  (S2b's structural bound composed with the same events, fewer of them, better constants) and, for
  Gaussians, by S6b's expectation. S9 states the interface-level corollaries only (U1, U2), the black
  box for a user who holds a PCP from anywhere (§6, Q6).
- **Additions outside the brief's two files**: four projector facts promoted from private lemmas of
  `LowRank/Structural/EarlyTruncation.lean` to `Matrix/Norms/Projector.lean` (both files now need
  them, and `ProjectionCost.lean` cannot import a LowRank file); Frobenius-norm preservation from the
  JL moment property in `Sketching/Properties/MatrixMultiplication.lean`; the family statements in
  each family's own file (§4, "Placement").
- **The tail predicate takes the sketch, not the test matrix** (Q1, hard to reverse):
  `HasProjectionCostPreserving S A k a b δ μ` with $\tilde{\mathbf{A}} = \mathbf{A}\mathbf{S}^{\mathsf{H}}$,
  so that a PCP is a property of the sketch $\mathbf{S}$ exactly as an OSE is, and LowRank consumers
  write it on `fun ω => (X ω)ᴴ` as D2 writes every probabilistic hypothesis.

**Literature checks** (PDFs: CEMMP arXiv:1410.6801 v3 at `/tmp/claude-1000/p0/papers/cemmp_15.pdf`;
Woodruff 2014 at `~/Documents/prove2me/books/woodruff_14.pdf`; page numbers are the printed ones).
- CEMMP Definition 1 (p. 5, two-sided, "some fixed non-negative constant $c$"), Lemma 3 (p. 6),
  Lemma 5 (p. 8), **Lemma 6** (p. 9): $\tilde{\mathbf{C}} = \mathbf{C} + \mathbf{E}_1 + \dots +
  \mathbf{E}_4$ with $-\varepsilon_1\mathbf{C} \preceq \mathbf{E}_1 \preceq \varepsilon_1\mathbf{C}$,
  $\sum_{i\le k}\lvert\lambda_i(\mathbf{E}_2)\rvert \le \varepsilon_2\,\mathrm{OPT}^2$ and the
  **one-sided** trace condition $\operatorname{tr}\mathbf{E}_2 \le \varepsilon_2'\,\mathrm{OPT}^2$,
  cross terms through the $\mathbf{C}^{+}$ semi-inner product, offset
  $c = -\min\{0, \operatorname{tr}\mathbf{E}_2\}$. Lemma 10 (pp. 12 to 14) reduces Lemma 6 to the
  spectral condition $\|\mathbf{B}\mathbf{R}\mathbf{R}^{\mathsf{T}}\mathbf{B}^{\mathsf{T}} -
  \mathbf{B}\mathbf{B}^{\mathsf{T}}\|_2 < \varepsilon$ and a trace condition, for a frame of width
  $m \le 2k$. Lemma 11 (p. 15): five families; families 1 to 3 (dense JL, sparse embedding, OSNAP)
  meet it through stable-rank spectral AMM ([CNW14], not in hand), family 4 (sampling) through
  [HKZ12]. **Theorem 12 and its short proof** (p. 16): $\mathbf{Z} = \mathbf{V}_k$; $\mathbf{E}_1$ by a
  subspace embedding of the rank-$k$ head; $\mathbf{E}_2$ by Frobenius AMM at
  $\varepsilon/\sqrt{k}$ with $\sum_{i\le k}\lvert\lambda_i\rvert \le \sqrt{k}\,\|\mathbf{E}_2\|_{\mathsf{F}}$;
  $\mathbf{E}_3$, $\mathbf{E}_4$ by Frobenius AMM of $(\mathbf{A}_{r\setminus k}, \mathbf{V}_k)$ at
  $\varepsilon/\sqrt{k}$; "for family 1, the required moment bound needs a sketch with dimension
  $O(k\log(1/\delta)/\varepsilon^2)$ … our alternative proof slightly increases the $\delta$
  dependence". No spectral AMM. Theorem 14 (§7.2, p. 18), column sampling, goes through Lemmas 10
  and 11 (spectral AMM). Theorems 7 to 9 (pp. 11 to 12) are deterministic SVD sketches.
- Woodruff 2014: Definition 12 and Theorem 13 (pp. 21 to 22; its proof sums the vector bound over
  columns by Minkowski, the route of J2 below); Theorem 14 (p. 23). Theorem 47 is not used: its
  rank-$k$ clause is flagged false at the claimed size in the maintainer's notes (brief D15), and
  nothing in S9 goes through an affine embedding.
- TYUC SIMAX §7.3.1 (pp. 21 to 22): the remark that CEMMP's results imply $(1+\varepsilon)$ for
  early-truncated GN at $\Theta(r/\varepsilon^2)$ for both sketch sizes, with high probability and
  unspecified constants: U2's provenance.
- Musco and Musco 2020 is not in hand and is not cited (S2b §5). The maintainer's
  `pcps-gaussian.tex` (Remark "The JL-moment route cannot give $k + \log(1/\delta)$") records that its
  Corollary 7's sum form does not follow from the argument given there; S9 claims only what its route
  proves.

**Missing infrastructure, per result** (each a statement of this note):
- Frobenius-norm preservation from the JL moment property, $\mathbb{P}(\varepsilon\|\mathbf{X}\|_{\mathsf{F}}^2
  \le \lvert\|\mathbf{S}\mathbf{X}\|_{\mathsf{F}}^2 - \|\mathbf{X}\|_{\mathsf{F}}^2\rvert) \le \delta$:
  absent (J1 to J3). It is the tail's trace condition of Lemma 6, which AMM in Frobenius norm does not
  give (a trace is not bounded by a Frobenius norm without a rank bound).
- The $\sqrt{k}$ bound $\lvert\langle\mathbf{P}, \mathbf{W}\rangle_{\mathsf{F}}\rvert \le
  \sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$ and the two star-projection identities: private in
  `LowRank/Structural/EarlyTruncation.lean` (S2b skeleton notes, "for the wrap-up"); promoted (L1 to
  L4).
- Everything else exists: the family OSE size forms and their asymptotic forms, the family JL
  moments at $p = 2$, AMM tails (`HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`, real;
  `measureReal_frobNorm_conjTranspose_mul_sub_ge_le_of_hasLaw_countSketch`, any field), S1's top-$k$
  frame `exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`, S2b's predicate, P3, T6 and
  E8.
- For U2 only: S7's random-subspace completion tail (§3.6); U2 waits for it.

## 0. Scope, size and the recommended cut

### 0.1 Notation

$\mathbf{A}$ : `Matrix m n 𝕜`; a random sketch $\mathbf{S}$ : `Ω → Matrix l n 𝕜` in the Sketching
round's orientation, so the sketched matrix is $\tilde{\mathbf{A}} = \mathbf{A}\mathbf{S}^{\mathsf{H}}$
and the test matrix of D2 is $\mathbf{\Omega} = \mathbf{S}^{\mathsf{H}}$; in LowRank files the test
matrix is `X : Ω → Matrix n l 𝕜` (written $\mathbf{\Omega}$ in docstrings, as S6) and the sketch is
`fun ω => (X ω)ᴴ`. A frame $\mathbf{Z}$ : `Matrix n r 𝕜` with $\mathbf{Z}^{\mathsf{H}}\mathbf{Z} =
\mathbf{I}$, the head; the tail $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$,
spelled `A - A * Z * Zᴴ` (S2b, no definition). $\mathrm{OPT} = \|\mathbf{A} -
\llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$. In the Sketching family files the sketch's row type is
`k` (their convention), so there the rank of the PCP is `d`, the dimension of the head embedding.

### 0.2 Items, sizes and the cut

| # | Item | Statements | Lines (est.) | Recommendation |
|---|---|---|---|---|
| 1 | Projector facts promoted to `Matrix/Norms/Projector.lean` (L1 to L4) | 4 | +50, and −35 of private lemmas in `LowRank/Structural/EarlyTruncation.lean` | include |
| 2 | Frobenius-norm preservation from the JL moment property (J1 to J3) | 3 | +80 | include |
| 3 | The tail predicate and `mono` (C1, C2) | 2 | +25 | include |
| 4 | Row-space constructors, fixed and oblivious (C3, C4) | 2 | +25 | include |
| 5 | The deterministic head–tail constructor, CEMMP Lemma 6 at a frame split (C5) | 1 | +140 | include |
| 6 | Its tail form by a union bound, any field (C6) | 1 | +50 | include |
| 7 | OSE plus JL moment, real (C7) | 1 | +70 | include |
| 8 | Gaussian, Rademacher, sub-Gaussian: size form and asymptotic form each (G1, G2, R1, R2, SG1, SG2) | 6 | +200 | include |
| 9 | CountSketch, any field (CS1, CS2) | 2 | +80 | include; flagged (file over budget, §4) |
| 10 | Early-truncated RSVD through a PCP, tail form (U1) | 1 | +20 | include |
| 11 | Early-truncated GN through a PCP and an OSI (U2) | 1 | +35 | include, implemented after S7's completion tail |
| D1 | $O((k + \log(1/\delta))/\varepsilon^2)$ dense families | — | 600 to 900, plus infrastructure | defer (needs stable-rank spectral AMM, or JL moments at $p \approx \log(1/\delta)$ for the weaker product form) |
| D2 | Column sampling (CEMMP Theorem 14) | — | about 300, plus spectral AMM by sampling (about 150) | defer |
| D3 | SRHT at $O(k)$ | — | about 250 | defer (needs an SRHT AMM; `SRHT.lean` is at 1002 lines) |
| D4 | Haar | — | about 70 | defer (needs a Haar OSE sample-size form, Sketching §6.1 item 5) |
| D5 | Law dependence and closedness of the PCP event | — | about 50 | cut, additive |
| D6 | Deterministic SVD-sketch PCPs, CEMMP Lemma 5 and Theorems 7 to 9 | — | about 200 | out of S9 (deterministic; a later deterministic stage) |

**Recommended cut:** items 1 to 11, about 775 lines and 24 public declarations (one definition,
23 theorems), against the brief's 250 plus 400 for the head–tail constructor. The growth is the
family statements (about 280; the brief's "family corollaries" were not sized) and the two
lower-layer pieces (about 130). Item 11 is the last proof of the stage and waits for S7; if S7 is
later than S9's wrap-up, U2 stays in the note as a dependency and S9 closes without it.

### 0.3 Consumers

| Item | Consumers |
|---|---|
| L1 to L4 | C5; S2b's T2 and T3 (their private copies are replaced at the wrap-up); S7's core-route tails |
| J1 to J3 | C6's trace condition for every family; any later Frobenius-preservation user (sketched trace estimation, sketch-and-solve residual estimates) |
| `HasProjectionCostPreserving`, `mono` (C1, C2) | U1, U2; every family statement; users solving a constrained low-rank problem or $k$-means on a sketch (S2b's P4 on the event) |
| C3, C4 | every family with an OSE or a fixed-subspace embedding (SRHT, sampling, Haar included) at dimension $\operatorname{rank}\mathbf{A}$ |
| C5 | C6, and through it every head–tail statement; users with a deterministic sketch meeting the four conditions |
| C6 | C7, CS1; the deferred families (SRHT, sampling, Haar), which plug in their own AMM tails |
| C7 | G1, R1, SG1; any later real family with an OSE and a JL moment |
| G1 to CS2 | users holding a sketch of that family; U1 and U2 at that family |
| U1, U2 | users running early truncation with a sketch known to be a PCP |

Not in S9: anything deterministic about PCPs beyond C5 (S2b; D6); per-family early-truncation
statements (dominated, §6); expectations (a PCP gives none: S2b T6's docstring, pcps-audit item 2).

## 1. Objects

One new definition, the tail predicate (§2). No deviation from Mathlib: Mathlib has no
projection-cost-preserving sketch. `HasProjectionCostPreserving` joins the paragraph "Additions where
Mathlib has nothing" of `docs/design/Mathlib-deviations.md` (one line, in the commit that adds it), as
S2b's names did.

**§5.3 row** (amends S2b's "projection-cost-preserving sketch" row; two reviews, CONTRIBUTING §9):

| Concept | Spelling | Bridge |
|---|---|---|
| projection-cost-preserving sketch | deterministic: `IsProjectionCostPreserving A Ã k a b` (S2b); random: `HasProjectionCostPreserving S A k a b δ μ`, the tail `μ.real {ω \| ¬ IsProjectionCostPreserving A (A * (S ω)ᴴ) k a b} ≤ δ`, the sketch `S : Ω → Matrix l n 𝕜` in the Sketching orientation; on a LowRank test matrix, `fun ω => (X ω)ᴴ`; no oblivious (all-$\mathbf{A}$) predicate | `HasSubspaceEmbedding.hasProjectionCostPreserving`; `IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment`; Mathlib: none |

**Used directly.** S2b: `IsProjectionCostPreserving`, `IsSubspaceEmbedding.isProjectionCostPreserving`
(P3), the private `frobNorm_sq_le_and_le_of_isSubspaceEmbedding` of the same file (C5's head step),
`IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le` (T6),
`frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq` (E8), `sub_earlyTruncatedRSVD`. S1:
`exists_hasOrthonormalCols_mul_mul_conjTranspose_eq_truncatedSVD`. Matrix:
`frobNorm_sub_truncatedSVD_le_of_rank_le`, `truncatedSVD_of_rank_le`, `frobNorm_rangeProjector_sq`,
`IsStarProjection.rangeProjector_eq`, `frobInner_le`, `abs_frobInner_le`, `frobInner_self`,
`frobNorm_sq_eq_re_trace`, `frobNorm_conjTranspose`, `frobNorm_mul_conjTranspose_right`,
`frobNorm_sq_eq_sum_col`, `mul_frobNorm_sq_le_of_smul_one_le`,
`frobNorm_mul_sq_le_of_conjTranspose_mul_self_le`. Sketching: `HasSubspaceEmbedding`,
`IsObliviousSubspaceEmbedding.hasSubspaceEmbedding`, `HasJLMoment`,
`HasJLMoment.measure_frobNorm_conjTranspose_mul_sub_ge_le`, the private `integral_rpow_sum_le` of
`MatrixMultiplication.lean` (J1, J2), the family OSE size forms
(`isObliviousSubspaceEmbedding_of_hasLaw_gaussianMatrix_of_gaussianEmbeddingDim_le`,
`isObliviousSubspaceEmbedding_of_hasLaw_rademacherMatrix_of_jlDim_le`,
`isObliviousSubspaceEmbedding_of_isSubgaussianVector_of_subgaussianEmbeddingDim_le`,
`isObliviousSubspaceEmbedding_of_hasLaw_countSketch_of_countSketchRows_le`), the family JL moments
(`hasJLMoment_of_hasLaw_gaussianMatrix`, `hasJLMoment_of_hasLaw_rademacherMatrix`,
`hasJLMoment_of_isSubgaussianVector`, `hasJLMoment_of_hasLaw_countSketch`) and CountSketch's AMM
tail. Mathlib: `measureReal_mono`, `measureReal_union_le` (no finiteness needed),
`Matrix.rank_conjTranspose`, `Matrix.rank_mul_le_left`, `Real.sqrt` API.

**Mathlib search** ("searched, none" unless named): a projection-cost-preserving sketch or coreset;
Frobenius-norm preservation under a random linear map; the Frobenius norm of a star projection as
its rank (Mathlib has `Matrix.trace` of an idempotent only through `LinearMap.IsProj` and finrank,
not this form; `frobNorm_rangeProjector_sq` is the library's); the star-projection identities L3,
L4 (searched in S2b; none).

## 2. Interfaces

**New: `HasProjectionCostPreserving S A k a b δ μ`** (§5.4 review; Q1).
- *Bundles:* the failure probability of the deterministic predicate at the sketched matrix
  $\mathbf{A}\mathbf{S}(\omega)^{\mathsf{H}}$, in the Sketching round's tail form, exactly as
  `HasSubspaceEmbedding S U a b δ μ` bundles `IsSubspaceEmbedding`. The offset of the event is chosen
  per $\omega$, which S2b's $\exists c \ge 0$ was designed for (S2b Q2 item 2); C5's offset
  $\max\{0, \|\mathbf{E}\|_{\mathsf{F}}^2 - \|\mathbf{E}\mathbf{S}^{\mathsf{H}}\|_{\mathsf{F}}^2\}$ is
  random.
- *Leaves separate:* the law, independence, measurability (none is needed: the predicate bounds the
  real measure of an arbitrary set, and the union bound holds for arbitrary sets).
- *Constructors:* C3 and C4 (row space), C6 (head–tail, from raw tails), C7 (OSE plus JL moment), the
  family statements.
- *Mathlib bridge:* none.
- *API:* C2 (`mono`); U1 and U2 are its consumers in LowRank.
- *Not introduced:* an oblivious predicate "for every $\mathbf{A}$" (Q1); a law-dependence lemma
  and the closedness of the PCP event (D5: the event is closed, as a sup of continuous functions
  below an inf, but no statement needs it); a predicate for AMM tails (they stay raw, as in the
  Sketching round: S2b's §5.3 row "early-truncation sketch quantities").

**Existing spellings used as hypotheses:** `HasOrthonormalCols Z`; `IsSubspaceEmbedding Xᴴ Z a b`
(deterministic head, test orientation as S2b); `HasSubspaceEmbedding S Z a b δ μ`,
`IsObliviousSubspaceEmbedding S d a b δ μ`, `HasJLMoment S ε δ p μ` (sketch orientation); the frame's
optimality `frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k)` (a one-line raw inequality in
C5 and C6, under the threshold for a predicate; Q2); the tail quantities written out as S2b does.

## 3. Statement shapes

`namespace NLAlib`, `open MeasureTheory ProbabilityTheory`, `open scoped Matrix MatrixOrder`.
Variables `{Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {𝕜 : Type*} [RCLike 𝕜]
{l m n r : Type*}`, `[Fintype _]` on each, `[DecidableEq r]` with a frame. In
`ProjectionCost.lean` the sample space is `Ω` (the Sketching convention), so the deterministic
statements' test-matrix binders, `Ω` in S2b, are renamed `X` (a binder rename, no API change;
docstrings keep $\mathbf{\Omega}$). Docstrings are shortened here; the full ones carry §5's citations
and are LaTeX throughout, outputs in `\mathsf`, named constants through value markers (CONTRIBUTING
§5.2 rule 2, §6 item 5).

### 3.0 Degenerate cases (checked for every statement)

- *$k = 0$.* The only projector of rank $0$ is $\mathbf{0}$, and the PCP is the scaled Frobenius
  sandwich $a\|\mathbf{A}\|_{\mathsf{F}}^2 \le \|\tilde{\mathbf{A}}\|_{\mathsf{F}}^2 + c \le
  b\|\mathbf{A}\|_{\mathsf{F}}^2$. Its lower half is free ($c = \|\mathbf{A}\|_{\mathsf{F}}^2$), its
  upper half is upper Frobenius preservation, which a nonempty sketch can fail. Hence the thresholds
  carry $k + 1$, not $k$: at $k = 0$ a threshold $Ck/(\varepsilon^2\delta)$ would allow one Gaussian
  row, and $\mathbb{P}(\chi^2_1 > 1 + \varepsilon) \approx 0.3$. In C5 at $k = 0$, `hZA` holds for
  every frame (a projection residual contracts) and the $\sqrt{k}$ term vanishes; in C7 the head OSE
  at dimension $0$ is trivial and only the Frobenius event remains.
- *$k \ge \lvert n \rvert$.* S1's top-$k$ frame needs $k \le \lvert n \rvert$; C7 and CS1 then take
  $\mathbf{Z} = \mathbf{I}_n$ ($\lvert r \rvert = \lvert n \rvert \le k$, $\mathbf{E} = \mathbf{0}$,
  every AMM and Frobenius event empty, the OSE at dimension $k$ covers $\mathbf{I}_n$). No hypothesis.
- *$k \ge \lvert m \rvert$, or $\operatorname{rank}\mathbf{A} \le k$.* The projector $\mathbf{I}$
  forces $c = 0$ (S2b); here $\mathrm{OPT} = 0$, `hZA` forces $\mathbf{E} = \mathbf{0}$ and C5's offset
  is $0$, consistently. The PCP reduces to the head embedding.
- *$a \le 0$*, or the derived lower constant $\le 0$: the lower half holds automatically ($c \ge 0$);
  every statement stays true. C5 needs $a \le 1 \le b$ (to absorb the tail's cost); a family OSE
  gives $1 \mp \varepsilon$.
- *Signs of the budgets.* C5's $\varepsilon_w, \varepsilon_\chi, \varepsilon_{\mathrm{F}} \ge 0$ are
  needed: at $\mathbf{E} = \mathbf{0}$ the three conditions hold for negative budgets, and
  ($\mathbf{A} = \mathbf{Z} = \mathbf{X} = [1]$, $k = 1$, $a = b = 1$, $\varepsilon_\chi = -1$) the
  projector $\mathbf{I}$ forces $c = 0$, after which $\mathbf{P} = \mathbf{0}$ (cost $1$, sketch cost
  $1$) would need $a + 2 \le 1$.
- *`hZA` is necessary.* $\mathbf{A} = \mathbf{I}_2$, $\mathbf{Z} = \mathbf{0}$ (`r` empty), $k = 1$,
  $\mathbf{X} = \sqrt{2}\,\mathbf{e}_1$ ($2 \times 1$), $a = b = 1$, $\varepsilon_w = \sqrt{2}/2$,
  $\varepsilon_\chi = \varepsilon_{\mathrm{F}} = 0$: the head is void, $\|\mathbf{W}\|_{\mathsf{F}} =
  \sqrt{2} = \varepsilon_w\|\mathbf{E}\|_{\mathsf{F}}^2$, $\|\mathbf{E}\mathbf{X}\|_{\mathsf{F}}^2 = 2 =
  \|\mathbf{E}\|_{\mathsf{F}}^2$, but $\|\mathbf{E}\|_{\mathsf{F}}^2 = 2 > 1 = \mathrm{OPT}^2$, and at
  $\mathbf{P} = \mathbf{e}_2\mathbf{e}_2^{\mathsf{H}}$ the sketch cost is $2$ against the claimed upper
  constant $1 + \sqrt{2}/2$ times the cost $1$. `hZA` is what makes $\|\mathbf{E}\|_{\mathsf{F}}^2$ a
  lower bound on every cost.
- *Frames wider than $k$.* C5 does not need $\lvert r \rvert \le k$ (CEMMP Lemma 10 uses width
  $2k$); at $\mathbf{Z} = \mathbf{I}_n$ it is S2b's P3 for the whole space. C7 and the families use
  width at most $k$, where $\|\mathbf{Z}\|_{\mathsf{F}} = \sqrt{\lvert r \rvert} \le \sqrt{k}$.
- *Empty sketch* (`l` empty): $\tilde{\mathbf{A}} = \mathbf{0}$; a head embedding of a nonempty frame
  forces $a \le 0$; C5's upper half is $c = \|\mathbf{E}\|_{\mathsf{F}}^2 \le \mathrm{cost}$, true. The
  family size hypotheses force `l` nonempty. `m` or `n` empty: every matrix is $\mathbf{0}$.
- *Ties.* No statement depends on a choice: C5 uses `truncatedSVD A k` only through its
  choice-free Frobenius error; U1 and U2 hold for every choice of the truncation (T6, E8).
- *Scaling.* A PCP is not scale-invariant (the offset can absorb a deficit, not a surplus): the
  families state it for the normalised sketch ($\lvert k\rvert^{-1/2}\mathbf{G}$), and U1 is about the
  early-truncated output at that same sketch. The early-truncated output at $c\,\mathbf{\Omega}$ is not
  identified with the one at $\mathbf{\Omega}$ under ties (S2b Q8), so a user runs the algorithm on the
  normalised sketch or passes through S2b's T4 with `hopt` rescaled.
- *Field.* C1 to C6, J1 to J3, CS1, CS2, U1, U2 over `𝕜`; C7 and G, R, SG over ℝ, because Frobenius
  AMM from the JL moment property is real only (its complex form has $\sqrt{2}\,\varepsilon$ and is
  deferred, Sketching §6.1 item 5).
- *Measurability.* None in C1 to C6; C7 and J1 to J3 take `AEMeasurable S μ` (the moment
  integrals); the families get it from `HasLaw`.

### 3.1 Lower layers (7)

**`Matrix/Norms/Projector.lean`** (registered; L1 to L4 enter proved, else a side file, §4). Each is
a fact about a star projection and the Frobenius norm, beside `frobNorm_rangeProjector_sq` and
`IsStarProjection.frobInner_mul_one_sub_mul`.

```lean
/-- The squared Frobenius norm of an orthogonal projector is its rank. -/
theorem _root_.IsStarProjection.frobNorm_sq_eq_rank {P : Matrix m m 𝕜} (hP : IsStarProjection P) :
    frobNorm P ^ 2 = P.rank
/-- An orthogonal projector of rank at most $k$ meets any $\mathbf{W}$ in at most
$\sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$:
$\lvert\langle\mathbf{P}, \mathbf{W}\rangle_{\mathsf{F}}\rvert \le \sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$,
the Ky Fan step $\sum_{i \le k}\lvert\lambda_i(\mathbf{W})\rvert \le \sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}$
in the form the sketching proofs use. [CohenElderMuscoMuscoPersu2015, proof of Theorem 12]. -/
theorem _root_.IsStarProjection.abs_frobInner_le_sqrt_mul_frobNorm {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) {k : ℕ} (hPk : P.rank ≤ k) (W : Matrix m m 𝕜) :
    |frobInner P W| ≤ √(k : ℝ) * frobNorm W
/-- The squared residual of an orthogonal projector:
$\|\mathbf{X} - \mathbf{P}\mathbf{X}\|_{\mathsf{F}}^2 = \|\mathbf{X}\|_{\mathsf{F}}^2 -
\langle\mathbf{P}, \mathbf{X}\mathbf{X}^{\mathsf{H}}\rangle_{\mathsf{F}}$, with no identity matrix. -/
theorem _root_.IsStarProjection.frobNorm_sub_mul_sq_eq_sub_frobInner {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (X : Matrix m q 𝕜) :
    frobNorm (X - P * X) ^ 2 = frobNorm X ^ 2 - frobInner P (X * Xᴴ)
/-- The residual of an orthogonal projector is orthogonal to its range part:
$\langle\mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X} - \mathbf{P}\mathbf{X}\rangle_{\mathsf{F}} =
\langle\mathbf{B} - \mathbf{P}\mathbf{B}, \mathbf{X}\rangle_{\mathsf{F}}$; the identity-free form of
`IsStarProjection.frobInner_mul_one_sub_mul`. -/
theorem _root_.IsStarProjection.frobInner_sub_mul_sub_mul {P : Matrix m m 𝕜}
    (hP : IsStarProjection P) (B X : Matrix m q 𝕜) :
    frobInner (B - P * B) (X - P * X) = frobInner (B - P * B) X
```

Proof routes: L1 is `frobNorm_rangeProjector_sq` after `hP.rangeProjector_eq`; L2 is `abs_frobInner_le`
and L1 with `Real.sqrt_le_sqrt`; L3, L4 are S2b's private `frobNorm_sub_mul_sq_eq` and
`frobInner_sub_mul_sub_mul` verbatim. The private `frobInner_le_sqrt_mul` of
`LowRank/Structural/EarlyTruncation.lean` becomes `le_abs_self` and L2; its two other privates are
deleted for L3, L4 (wrap-up edit, flagged in §4).

**`Sketching/Properties/MatrixMultiplication.lean`** (registered; J1 to J3, over `𝕜`, in their own
section with `S : Ω → Matrix k n 𝕜`, since the file's variables are real).

```lean
theorem HasJLMoment.integrable_abs_frobNorm_mul_sq_sub_rpow (h : HasJLMoment S ε δ p μ)
    (hp : 1 ≤ p) (hS : AEMeasurable S μ) (X : Matrix n q 𝕜) :
    Integrable (fun ω => |frobNorm (S ω * X) ^ 2 - frobNorm X ^ 2| ^ p) μ
/-- **Frobenius-norm preservation from the JL moment property**: for $\varepsilon \ge 0$ and
$p \ge 1$,
$$\mathbb{E}\bigl\lvert\|\mathbf{S}\mathbf{X}\|_{\mathsf{F}}^2 - \|\mathbf{X}\|_{\mathsf{F}}^2\bigr\rvert^p
\le (\varepsilon\|\mathbf{X}\|_{\mathsf{F}}^2)^p\,\delta\,.$$
The trace of the approximate-multiplication error at $\mathbf{A} = \mathbf{B} = \mathbf{X}$, which the
Frobenius bound on that error does not control. Any field: only the vector property is used, column
by column, with Jensen's inequality for the weights
$\|\mathbf{X}_{:,j}\|^2/\|\mathbf{X}\|_{\mathsf{F}}^2$. [Woodruff2014, proof of Theorem 13], the same
summation over columns; [CohenElderMuscoMuscoPersu2015, §7, after Lemma 11], stated there as
standard.
Result: jl-moment-frobenius -/
theorem HasJLMoment.integral_abs_frobNorm_mul_sq_sub_rpow_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 ≤ ε) (hp : 1 ≤ p) (hS : AEMeasurable S μ) (X : Matrix n q 𝕜) :
    ∫ ω, |frobNorm (S ω * X) ^ 2 - frobNorm X ^ 2| ^ p ∂μ ≤ (ε * frobNorm X ^ 2) ^ p * δ
/-- Its tail: for $\varepsilon > 0$, $p \ge 1$ and $\mathbf{X} \ne \mathbf{0}$,
$\mathbb{P}(\varepsilon\|\mathbf{X}\|_{\mathsf{F}}^2 \le \lvert\|\mathbf{S}\mathbf{X}\|_{\mathsf{F}}^2 -
\|\mathbf{X}\|_{\mathsf{F}}^2\rvert) \le \delta$.
Result: jl-moment-frobenius -/
theorem HasJLMoment.measure_abs_frobNorm_mul_sq_sub_ge_le (h : HasJLMoment S ε δ p μ)
    (hε : 0 < ε) (hp : 1 ≤ p) (hS : AEMeasurable S μ) {X : Matrix n q 𝕜} (hX : X ≠ 0) :
    μ.real {ω | ε * frobNorm X ^ 2 ≤ |frobNorm (S ω * X) ^ 2 - frobNorm X ^ 2|} ≤ δ
```

Proof route: $\lvert\|\mathbf{S}\mathbf{X}\|^2 - \|\mathbf{X}\|^2\rvert \le \sum_j \|\mathbf{x}_j\|^2
\lvert\|\mathbf{S}\mathbf{u}_j\|^2 - 1\rvert$ (`frobNorm_sq_eq_sum_col`, $\mathbf{u}_j$ the unit
columns), then the file's `integral_rpow_sum_le` with $Y_j = w_j\lvert\|\mathbf{S}\mathbf{u}_j\|^2 -
1\rvert$, $w_j = \|\mathbf{x}_j\|^2/\|\mathbf{X}\|_{\mathsf{F}}^2$ (zero columns have $w_j = 0$); J3 by
`measureReal_abs_ge_le_integral_rpow_div` as in the AMM tail. Degenerate: $\mathbf{X} = \mathbf{0}$
gives $0 \le 0$ in J2 (for $p > 0$); `q` empty is $\mathbf{X} = \mathbf{0}$.

### 3.2 `Sketching/Properties/ProjectionCost.lean`: the tail predicate and row-space constructors (4)

```lean
/-- The random sketch $\mathbf{S}$ is a **rank-$k$ projection-cost-preserving sketch for
$\mathbf{A}$ with probability $1 - \delta$**: the event that $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ is not
a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with constants $a$, $b$
(`NLAlib.IsProjectionCostPreserving`) has probability at most $\delta$. The offset may depend on
$\omega$. With a test matrix $\mathbf{\Omega}$ the sketch is $\mathbf{\Omega}^{\mathsf{H}}$.
[CohenElderMuscoMuscoPersu2015, Theorem 12], there "with probability at least $1 - O(\delta)$" and
error $O(\varepsilon)$.
Result: projection-cost-preserving-sketch -/
def HasProjectionCostPreserving (S : Ω → Matrix l n 𝕜) (A : Matrix m n 𝕜) (k : ℕ) (a b δ : ℝ)
    (μ : Measure Ω) : Prop :=
  μ.real {ω | ¬ IsProjectionCostPreserving A (A * (S ω)ᴴ) k a b} ≤ δ
theorem HasProjectionCostPreserving.mono [IsFiniteMeasure μ]
    (h : HasProjectionCostPreserving S A k a b δ μ) (hk : k' ≤ k) (ha : a' ≤ a) (hb : b ≤ b')
    (hδ : δ ≤ δ') : HasProjectionCostPreserving S A k' a' b' δ' μ
/-- **A random subspace embedding of the row space is a projection-cost-preserving sketch** for
every rank, with the same constants and failure probability: S2b's row-space constructor on the
event. Its dimension is at least $\operatorname{rank}\mathbf{A}$. -/
theorem HasSubspaceEmbedding.hasProjectionCostPreserving [IsFiniteMeasure μ]
    (h : HasSubspaceEmbedding S Aᴴ a b δ μ) (k : ℕ) : HasProjectionCostPreserving S A k a b δ μ
/-- **An OSE for dimension $d \ge \operatorname{rank}\mathbf{A}$ is a projection-cost-preserving
sketch of $\mathbf{A}$** for every rank. Every family with an OSE (SRHT, Haar and the rest) is one at
dimension $O(\operatorname{rank}\mathbf{A})$ through this; the head–tail constructor
`NLAlib.IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment` removes the rank.
[CohenElderMuscoMuscoPersu2015, §1.1]; [Woodruff2014, proof of Theorem 61]. -/
theorem IsObliviousSubspaceEmbedding.hasProjectionCostPreserving [IsFiniteMeasure μ]
    (h : IsObliviousSubspaceEmbedding S d a b δ μ) {A : Matrix m n 𝕜} (hA : A.rank ≤ d) (k : ℕ) :
    HasProjectionCostPreserving S A k a b δ μ
```

Proof routes: C2, `measureReal_mono` on the inclusion given by S2b's `mono`; C3, inclusion by P3 at
$\mathbf{X} = \mathbf{S}(\omega)^{\mathsf{H}}$ after `Matrix.conjTranspose_conjTranspose`; C4, C3 at
`h.hasSubspaceEmbedding (U := Aᴴ)` with `Matrix.rank_conjTranspose`. Degenerate: no hypothesis on
$a$, $b$, $k$; $\delta < 0$ makes every statement vacuous on both sides.

### 3.3 `Sketching/Properties/ProjectionCost.lean`: the head–tail constructor (3)

The deterministic heart, CEMMP Lemma 6 at a frame split with the short proof of Theorem 12, over
`𝕜`. With $\mathbf{Y} = \mathbf{I} - \mathbf{P}$ (proof-internal), $h = \|\mathbf{Y}\mathbf{A}\mathbf{Z}\|^2$,
$t = \|\mathbf{Y}\mathbf{E}\|^2$, $x = h + t = \|\mathbf{A} - \mathbf{P}\mathbf{A}\|^2$ (the cross term
vanishes, $(\mathbf{I} - \mathbf{Z}\mathbf{Z}^{\mathsf{H}})\mathbf{Z} = \mathbf{0}$),
$\mathbf{W} = \mathbf{E}\mathbf{X}\mathbf{X}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} - \mathbf{E}\mathbf{E}^{\mathsf{H}}$
and $\boldsymbol{\chi} = \mathbf{E}\mathbf{X}\mathbf{X}^{\mathsf{H}}\mathbf{Z} - \mathbf{E}\mathbf{Z}$,
the sketch cost is
$$\|\mathbf{Y}\mathbf{A}\mathbf{X}\|^2 = \underbrace{\|\mathbf{Y}\mathbf{A}\mathbf{Z}\,\mathbf{Z}^{\mathsf{H}}\mathbf{X}\|^2}_{\in[a h,\,b h]}
+ t + \underbrace{\operatorname{tr}\mathbf{W}}_{\|\mathbf{E}\mathbf{X}\|^2 - \|\mathbf{E}\|^2}
- \underbrace{\langle\mathbf{P}, \mathbf{W}\rangle_{\mathsf{F}}}_{\lvert\cdot\rvert \le \sqrt{k}\,\|\mathbf{W}\|_{\mathsf{F}}}
+ 2\underbrace{\operatorname{Re}\langle\mathbf{Y}\mathbf{A}\mathbf{Z}, \boldsymbol{\chi}\rangle_{\mathsf{F}}}_{\lvert\cdot\rvert \le \sqrt{h}\,\|\boldsymbol{\chi}\|_{\mathsf{F}}}.$$
The offset $c = \max\{0, -\operatorname{tr}\mathbf{W}\}$ turns $\operatorname{tr}\mathbf{W} + c$ into
$\max\{\operatorname{tr}\mathbf{W}, 0\} \in [0, \varepsilon_{\mathrm{F}}\|\mathbf{E}\|^2]$, which is
why only the upper half of the tail's Frobenius preservation is needed (CEMMP's one-sided trace
condition), and `hZA` with Eckart–Young gives $\|\mathbf{E}\|^2 \le \mathrm{OPT}^2 \le x$, which makes
every additive error relative. The cross term is bounded by Cauchy–Schwarz on
$\langle\mathbf{Y}\mathbf{A}\mathbf{Z}, \boldsymbol{\chi}\rangle$, not through CEMMP's
$\mathbf{C}^{+}$ semi-inner product.

```lean
/-- **Projection-cost preservation from a head embedding and tail approximate
multiplication.** Let $\mathbf{Z}$ have orthonormal columns and
$\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$ with
$\|\mathbf{E}\|_{\mathsf{F}} \le \|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}$; let
$\mathbf{\Omega}^{\mathsf{H}}$ be a subspace embedding for $\operatorname{range}\mathbf{Z}$ with constants
$a \le 1 \le b$, and for $\varepsilon_w, \varepsilon_\chi, \varepsilon_{\mathrm{F}} \ge 0$
$$\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{E}^{\mathsf{H}} - \mathbf{E}\mathbf{E}^{\mathsf{H}}\|_{\mathsf{F}}
\le \varepsilon_w\|\mathbf{E}\|_{\mathsf{F}}^2,\qquad
\|\mathbf{E}\mathbf{\Omega}\mathbf{\Omega}^{\mathsf{H}}\mathbf{Z} - \mathbf{E}\mathbf{Z}\|_{\mathsf{F}}
\le \varepsilon_\chi\|\mathbf{E}\|_{\mathsf{F}},\qquad
\|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2 \le (1 + \varepsilon_{\mathrm{F}})\|\mathbf{E}\|_{\mathsf{F}}^2\,.$$
Then $\mathbf{A}\mathbf{\Omega}$ is a rank-$k$ projection-cost-preserving sketch of $\mathbf{A}$ with
constants $a - \sqrt{k}\,\varepsilon_w - 2\varepsilon_\chi$ and
$b + \sqrt{k}\,\varepsilon_w + 2\varepsilon_\chi + \varepsilon_{\mathrm{F}}$, with offset
$\max\{0, \|\mathbf{E}\|_{\mathsf{F}}^2 - \|\mathbf{E}\mathbf{\Omega}\|_{\mathsf{F}}^2\}$.
[CohenElderMuscoMuscoPersu2015, Lemma 6 and proof of Theorem 12]; there $\mathbf{Z} = \mathbf{V}_k$,
error budgets summing to $\varepsilon$, real; here any frame whose residual is at most the optimal
one (CEMMP Lemma 10 uses width $2k$), constants $a$, $b$, any `RCLike` field, the cross term by
Cauchy–Schwarz.
Result: pcp-sufficient-conditions -/
theorem IsSubspaceEmbedding.isProjectionCostPreserving_of_hasOrthonormalCols
    {A : Matrix m n 𝕜} {X : Matrix n l 𝕜} {Z : Matrix n r 𝕜} {a b εw εχ εF : ℝ} {k : ℕ}
    (h : IsSubspaceEmbedding Xᴴ Z a b) (hZ : HasOrthonormalCols Z) (ha : a ≤ 1) (hb : 1 ≤ b)
    (hZA : frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k))
    (hεw : 0 ≤ εw) (hεχ : 0 ≤ εχ) (hεF : 0 ≤ εF)
    (hw : frobNorm ((A - A * Z * Zᴴ) * X * Xᴴ * (A - A * Z * Zᴴ)ᴴ -
        (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ) ≤ εw * frobNorm (A - A * Z * Zᴴ) ^ 2)
    (hχ : frobNorm ((A - A * Z * Zᴴ) * X * Xᴴ * Z - (A - A * Z * Zᴴ) * Z) ≤
        εχ * frobNorm (A - A * Z * Zᴴ))
    (hF : frobNorm ((A - A * Z * Zᴴ) * X) ^ 2 ≤ (1 + εF) * frobNorm (A - A * Z * Zᴴ) ^ 2) :
    IsProjectionCostPreserving A (A * X) k (a - √(k : ℝ) * εw - 2 * εχ)
      (b + √(k : ℝ) * εw + 2 * εχ + εF)
/-- **The head–tail constructor, tail form**: under the frame hypotheses of
`NLAlib.IsSubspaceEmbedding.isProjectionCostPreserving_of_hasOrthonormalCols`, if the head embedding
fails with probability $\delta_1$ and the three tail conditions fail with probabilities $\delta_2$,
$\delta_3$, $\delta_4$, the sketch is a rank-$k$ projection-cost-preserving sketch with the same
constants except with probability $\delta_1 + \delta_2 + \delta_3 + \delta_4$ (union bound). The
interface for a family with its own AMM tails (CountSketch over any field; later SRHT, sampling).
[CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
Result: pcp-sufficient-conditions -/
theorem HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasOrthonormalCols [IsFiniteMeasure μ]
    {S : Ω → Matrix l n 𝕜} {Z : Matrix n r 𝕜} {a b δ₁ δ₂ δ₃ δ₄ εw εχ εF : ℝ}
    (h : HasSubspaceEmbedding S Z a b δ₁ μ) (hZ : HasOrthonormalCols Z) (ha : a ≤ 1) (hb : 1 ≤ b)
    {A : Matrix m n 𝕜} {k : ℕ} (hZA : frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k))
    (hεw : 0 ≤ εw) (hεχ : 0 ≤ εχ) (hεF : 0 ≤ εF)
    (hw : μ.real {ω | εw * frobNorm (A - A * Z * Zᴴ) ^ 2 < frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ *
        S ω * (A - A * Z * Zᴴ)ᴴ - (A - A * Z * Zᴴ) * (A - A * Z * Zᴴ)ᴴ)} ≤ δ₂)
    (hχ : μ.real {ω | εχ * frobNorm (A - A * Z * Zᴴ) <
        frobNorm ((A - A * Z * Zᴴ) * (S ω)ᴴ * S ω * Z - (A - A * Z * Zᴴ) * Z)} ≤ δ₃)
    (hF : μ.real {ω | (1 + εF) * frobNorm (A - A * Z * Zᴴ) ^ 2 <
        frobNorm (S ω * (A - A * Z * Zᴴ)ᴴ) ^ 2} ≤ δ₄) :
    HasProjectionCostPreserving S A k (a - √(k : ℝ) * εw - 2 * εχ)
      (b + √(k : ℝ) * εw + 2 * εχ + εF) (δ₁ + δ₂ + δ₃ + δ₄) μ
/-- **An OSE plus the JL moment property gives a projection-cost-preserving sketch**: a real sketch
that is an OSE for dimension $k$ with constants $a \le 1 \le b$ and failure probability $\delta$, and
has the $(\varepsilon, \delta', p)$ JL moment property with $\varepsilon > 0$, $p \ge 2$, is for every
$\mathbf{A}$ a rank-$k$ projection-cost-preserving sketch with constants
$a - 3\sqrt{k}\,\varepsilon$ and $b + 3\sqrt{k}\,\varepsilon + \varepsilon$, except with probability
$\delta + 3\delta'$. No dimension of $\mathbf{A}$ enters. With JL moments at $p = 2$ this is
$O((k+1)/(\varepsilon^2\delta))$ rows; the $(k + \log(1/\delta))/\varepsilon^2$ of CEMMP's Lemma 11
needs stable-rank spectral approximate multiplication. [CohenElderMuscoMuscoPersu2015, proof of
Theorem 12]; there $O(k\log(1/\delta)/\varepsilon^2)$ for dense sign matrices with higher moments,
unspecified constants; here explicit, any $p \ge 2$.
Result: pcp-sufficient-conditions -/
theorem IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment [IsFiniteMeasure μ]
    {S : Ω → Matrix l n ℝ} {k : ℕ} {a b δ ε δ' p : ℝ} (h : IsObliviousSubspaceEmbedding S k a b δ μ)
    (hJL : HasJLMoment S ε δ' p μ) (hS : AEMeasurable S μ) (ha : a ≤ 1) (hb : 1 ≤ b)
    (hε : 0 < ε) (hp : 2 ≤ p) (hδ' : 0 ≤ δ') (A : Matrix m n ℝ) :
    HasProjectionCostPreserving S A k (a - 3 * √(k : ℝ) * ε) (b + 3 * √(k : ℝ) * ε + ε)
      (δ + 3 * δ') μ
```

Proof routes. *C5:* obtain the offset as above; head by the file's private
`frobNorm_sq_le_and_le_of_isSubspaceEmbedding` at $\mathbf{U} = \mathbf{Z}$,
$\mathbf{C} = (\mathbf{Y}\mathbf{A}\mathbf{Z})^{\mathsf{H}}$ with `frobNorm_conjTranspose`; tail by L3,
L4 (no $\mathbf{I} - \mathbf{P}$ formed, as S2b's T2) and L2; cross by `abs_frobInner_le`;
$\|\mathbf{E}\|^2 \le x$ from `hZA` and `frobNorm_sub_truncatedSVD_le_of_rank_le` (rank of
$\mathbf{P}\mathbf{A}$ at most $k$); $\sqrt{h} \le \sqrt{x}$; `nlinarith` on each half. About 120 lines,
split into a head lemma, a tail lemma and the assembly (each private). *C6:* the bad PCP set is inside
the union of the four bad sets (C5 at $\mathbf{X} = \mathbf{S}(\omega)^{\mathsf{H}}$, with
`Matrix.conjTranspose_conjTranspose` and `frobNorm_conjTranspose` for the Frobenius event);
`measureReal_mono`, three `measureReal_union_le`. *C7:* frame $\mathbf{Z}$: S1's top-$k$ frame
(`p := Fin k`) when $k \le \lvert n \rvert$, so `hZA` is `le_of_eq`; $\mathbf{Z} = \mathbf{I}_n$
otherwise. Head: `h.hasSubspaceEmbedding`. If $\mathbf{E} = \mathbf{0}$ the three events are empty;
else AMM at $(\mathbf{E}^{\mathsf{H}}, \mathbf{E}^{\mathsf{H}})$ gives `hw` at $\varepsilon_w = \varepsilon$,
AMM at $(\mathbf{E}^{\mathsf{H}}, \mathbf{Z})$ gives `hχ` at $\varepsilon_\chi = \sqrt{k}\,\varepsilon$
($\|\mathbf{Z}\|_{\mathsf{F}} = \sqrt{\lvert r \rvert} \le \sqrt{k}$), and J3 at
$\mathbf{X} = \mathbf{E}^{\mathsf{H}}$ gives `hF` at $\varepsilon_{\mathrm{F}} = \varepsilon$ (each AMM
event $\{\varepsilon\|\cdot\|\|\cdot\| \le \cdot\}$ contains C6's strict one); then C6.

### 3.4 Family files: Gaussian, Rademacher, sub-Gaussian (6, real)

Each family gets the size form and its asymptotic form (CONTRIBUTING §5.2 rule 3). The size form is
C7 at the family's OSE size form with $(1 \mp \varepsilon/2, \delta/2)$ and the family's JL moment at
$\varepsilon_J = \varepsilon/(8\sqrt{d+1})$: lower constant $1 - \varepsilon/2 - 3\sqrt{d}\,\varepsilon_J
\ge 1 - \varepsilon$, upper $1 + \varepsilon/2 + (3\sqrt{d} + 1)\varepsilon_J \le 1 + \varepsilon$, and
failure $\delta/2 + 3\delta_J$, which is at most $\delta$ under the second size hypothesis; then
`mono`. The integers are the proof's, written inline as S6b's $900k/\varepsilon^2$ (Q8). No per-family
tail form: C7 is the tail form, and both of its inputs are already in closed form in each family's
file (Q4).

**`Sketching/Gaussian/Gaussian.lean`** (registered).

```lean
/-- **A Gaussian sketch is a projection-cost-preserving sketch**, size form: for
$0 < \varepsilon \le 1$, $\delta > 0$ and at
least <!-- value gaussianEmbeddingDim d (\varepsilon/2) (\delta/2) -->
$9 (\sqrt{d} + \sqrt{2 \log(2/(\delta/2))})^2/(\varepsilon/2)^2$ rows (`gaussianEmbeddingDim d (ε / 2)
(δ / 2)`) and at least $768(d+1)/(\varepsilon^2\delta)$ rows, $\mathbf{S} = \lvert k \rvert^{-1/2}
\mathbf{G}$ makes $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$ projection-cost-preserving sketch of
$\mathbf{A}$ with constants $1 \mp \varepsilon$, for every $\mathbf{A}$, except with probability
$\delta$. [CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 1]; there sign matrices,
$O((k + \log(1/\delta))/\varepsilon^2)$ rows through [CNW14], error $O(\varepsilon)$; here the
Gaussian, explicit constants, and $1/\delta$ from second moments. Asymptotic form:
`NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix`.
Result: gaussian-pcp -/
theorem hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card
    (hG : HasLaw G (gaussianMatrix k n) μ) (A : Matrix m n ℝ) (d : ℕ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hk₁ : gaussianEmbeddingDim d (ε / 2) (δ / 2) ≤ Fintype.card k)
    (hk₂ : 768 * ((d : ℝ) + 1) ≤ ε ^ 2 * δ * Fintype.card k) :
    HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) A d (1 - ε) (1 + ε) δ μ
/-- **$O((d+1)/(\varepsilon^2\delta))$ Gaussian rows suffice for a rank-$d$ projection-cost-preserving
sketch** with constants $1 \mp \varepsilon$ and failure probability $\delta$, for $\varepsilon$ and
$\delta$ below absolute constants; the constants come before every dimension. Proved from the size
form with $C = 768$, $\varepsilon_0 = 1$, $\delta \le 1/2$ (its first hypothesis is at most
$648(d+1)/(\varepsilon^2\delta)$ there). [CohenElderMuscoMuscoPersu2015, Theorem 12].
Asymptotic: NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card
Result: gaussian-pcp -/
theorem exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k] [Fintype m]
      [Fintype n] (μ : Measure Ω) (G : Ω → Matrix k n ℝ) (A : Matrix m n ℝ) (d : ℕ) (ε δ : ℝ),
      HasLaw G (gaussianMatrix k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
      C * (((d : ℝ) + 1) / (ε ^ 2 * δ)) ≤ Fintype.card k →
      HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω) A d (1 - ε) (1 + ε)
        δ μ
```

**`Sketching/Gaussian/Rademacher.lean`** (registered). R1
`hasProjectionCostPreserving_of_hasLaw_rademacherMatrix_of_le_card`: as G1 with
`hX : HasLaw X (rademacherMatrix k n) μ`, the head hypothesis the Rademacher OSE size form's at
$(\varepsilon/2, \delta/2)$, `jlDim (ε / 2 / 2) (δ / 2 / 9 ^ d) ≤ Fintype.card k` (docstring marker
`<!-- value jlDim (\varepsilon/4) (\delta/(2 \cdot 9^d)) -->` with its filled template), $0 < \varepsilon
\le 1$, and the same `768 * ((d : ℝ) + 1) ≤ ε ^ 2 * δ * Fintype.card k` (the Rademacher JL moment is
the Gaussian's, $2/(\lvert k \rvert\varepsilon^2)$). [CohenElderMuscoMuscoPersu2015, Theorem 12,
Lemma 11 family 1], the family itself. R2
`exists_forall_hasProjectionCostPreserving_of_hasLaw_rademacherMatrix`, threshold
`C * (((d : ℝ) + 1) / (ε ^ 2 * δ))`.
Result: rademacher-pcp.

**`Sketching/Gaussian/SubGaussian.lean`** (registered). SG1
`hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card`: the hypotheses of
`isObliviousSubspaceEmbedding_of_isSubgaussianVector` (`hind`, `hsub`, `hiso`), `[Nonempty k]`,
$0 < \varepsilon \le 4c$ (the OSE size form needs $\varepsilon/2 \le 2c$), the head hypothesis
`subgaussianEmbeddingDim c d (ε / 2) (δ / 2) ≤ Fintype.card k` (marker
`<!-- value subgaussianEmbeddingDim c d (\varepsilon/2) (\delta/2) -->` and the constant's marker, as
the OSE size form shows them), and
`384 * (16 * (c : ℝ) ^ 2 - 1) * ((d : ℝ) + 1) ≤ ε ^ 2 * δ * Fintype.card k` (the sub-Gaussian JL moment
$(16c^2 - 1)/(\lvert k \rvert\varepsilon^2)$). The route of [CohenElderMuscoMuscoPersu2015, proof of
Theorem 12]; the sub-Gaussian instance is not stated there. SG2
`exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector`, threshold
`C * ((c : ℝ) ^ 2 * ((d : ℝ) + 1) / (ε ^ 2 * δ))`, quantifiers as the sub-Gaussian OSE asymptotic form
($\varepsilon_0 = 1$; isotropy gives $16c^2 \ge 1$, so $\varepsilon \le 4c$).
Result: subgaussian-pcp.

### 3.5 `Sketching/Sparse/CountSketch.lean`: CountSketch over any field (2)

CS1 `hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card` over `𝕜`:
`hS : HasLaw S (countSketch k n) μ`, $\varepsilon, \delta > 0$, $\varepsilon \le 1$,
`countSketchRows d (ε / 2) (δ / 2) ≤ Fintype.card k` (marker
`<!-- value countSketchRows d (\varepsilon/2) (\delta/2) -->` before
$(d^2 + d)/((\delta/2) (\varepsilon/2)^2)$) and `768 * ((d : ℝ) + 1) ≤ ε ^ 2 * δ * Fintype.card k`;
conclusion `HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ`. Route: C6, not C7 (C7 is real):
the frame choice of C7's proof, the CountSketch OSE size form for the head, CountSketch's own AMM tail
(any field) for `hw` and `hχ`, and J3 with `hasJLMoment_of_hasLaw_countSketch` (any field) for `hF`.
[CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 2], $O(k^2/(\varepsilon^2\delta))$ there
as here. CS2 `exists_forall_hasProjectionCostPreserving_of_hasLaw_countSketch`, quantifiers as
`exists_forall_isObliviousSubspaceEmbedding_of_hasLaw_countSketch` (`{𝕜 : Type} [RCLike 𝕜]`
included), threshold `C * (((d : ℝ) + 1) ^ 2 / (ε ^ 2 * δ))`.
Result: sparse-pcp.

### 3.6 `LowRank/Oblivious/EarlyTruncation.lean`: early truncation through a PCP (2)

Variables as S6: `{X : Ω → Matrix n l 𝕜} {Ψ : Ω → Matrix m p 𝕜}`. The hypotheses are on the sketches
`fun ω => (X ω)ᴴ`, `fun ω => (Ψ ω)ᴴ` (D2).

```lean
/-- **Early truncation through a random projection-cost-preserving sketch**: if
$\mathbf{\Omega}^{\mathsf{H}}$ is a rank-$k$ projection-cost-preserving sketch for $\mathbf{A}$ with
constants $a$, $b$ except with probability $\delta$, then
$$a\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2
\le b\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta$, for every choice of the truncations. With a family's constants
$1 \mp \varepsilon$ the factor is $(1+\varepsilon)/(1-\varepsilon)$. For a sketch of a known family
the structural route `NLAlib.IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le` uses fewer
events and gives better constants; this is the form for a sketch known only to be a
projection-cost-preserving sketch. [CohenElderMuscoMuscoPersu2015, Lemma 3, §7.2].
Result: early-truncation-pcp-bound -/
theorem HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le
    [IsFiniteMeasure μ] {A : Matrix m n 𝕜} {k : ℕ} {a b δ : ℝ}
    (h : HasProjectionCostPreserving (fun ω => (X ω)ᴴ) A k a b δ μ) :
    μ.real {ω | b * frobNorm (A - truncatedSVD A k) ^ 2 <
      a * frobNorm (A - earlyTruncatedRSVD A (X ω) k) ^ 2} ≤ δ
/-- **Early-truncated generalized Nyström through a projection-cost-preserving sketch**: with
$\mathbf{\Omega}^{\mathsf{H}}$ as above, $a \ge 0$, and an independent co-range test matrix
$\mathbf{\Psi}$ whose $\mathbf{\Psi}^{\mathsf{H}}$ is an oblivious subspace injection for dimension $k$
with constant $a' > 0$ and failure probability $\delta'$, for $t > 0$
$$a\|\mathbf{A} - \mathsf{earlyTruncatedGN}(\mathbf{A}, \mathbf{\Omega}, \mathbf{\Psi}, k)\|_{\mathsf{F}}^2
\le \Bigl(1 + \frac{t}{a'}\Bigr) b\,\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$$
except with probability $\delta + \delta' + 1/t$. One pass, rank at most $k$.
[TroppYurtseverUdellCevher2017, §7.3.1], the algorithm and the remark that CEMMP's results imply a
$(1+\varepsilon)$ bound at $\Theta(r/\varepsilon^2)$ for both sketch sizes, with unspecified constants.
Result: early-truncation-pcp-bound -/
theorem HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le
    [IsProbabilityMeasure μ] [DecidableEq m] {A : Matrix m n 𝕜} {k : ℕ} {a b δ a' δ' t : ℝ}
    (h : HasProjectionCostPreserving (fun ω => (X ω)ᴴ) A k a b δ μ) (ha : 0 ≤ a)
    (hΨ : IsObliviousSubspaceInjection (fun ω => (Ψ ω)ᴴ) k a' δ' μ) (ha' : 0 < a') (ht : 0 < t)
    (hind : IndepFun X Ψ μ) (hX : AEMeasurable X μ) (hΨm : AEMeasurable Ψ μ) :
    μ.real {ω | (1 + t / a') * b * frobNorm (A - truncatedSVD A k) ^ 2 <
      a * frobNorm (A - earlyTruncatedGeneralizedNystrom A (X ω) (Ψ ω) k) ^ 2} ≤ δ + δ' + 1 / t
```

Proof routes. *U1:* the bad set is inside the PCP's bad set by T6 at
$\mathbf{X}(\omega) = ((\mathbf{X}(\omega))^{\mathsf{H}})^{\mathsf{H}}$; `measureReal_mono`. *U2:* the union
of U1's bad set and the completion's bad set
$\{(1 + t/a')\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}\|^2 < \|\mathbf{A} - \mathsf{earlyTruncatedGN}\|^2\}$,
whose measure is at most $\delta' + 1/t$ by **S7's random-subspace completion tail** (E8, then the
oblique-projector bound `IsSubspaceInjection.frobNorm_obliqueProjector_mul_sq_le` on the event that
$\mathbf{\Psi}^{\mathsf{H}}$ injects the random $\operatorname{range}\llbracket\mathbf{A}\mathbf{X}\rrbracket_k$,
of rank at most $k$, `IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_le_of_indepFun`,
and Markov conditional on $\mathbf{X}$ with the isotropy of $\mathbf{\Psi}^{\mathsf{H}}$). That lemma is
the random-subspace twin of `HasSubspaceInjection.measure_frobNorm_sub_mul_pinv_mul_sq_gt_le`; S7's
note owns its statement and home (Q7). On the good set
$a\|\mathbf{A} - \mathsf{etGN}\|^2 \le a(1 + t/a')\|\mathbf{A} - \mathsf{etRSVD}\|^2 \le
(1 + t/a')\,b\,\mathrm{OPT}^2$ uses $a \ge 0$. Degenerate: $k = 0$, both outputs $\mathbf{0}$; a
rank-deficient truncation is covered because the OSI is for dimension $k \ge$ the actual rank.

## 4. Files

| # | File | Statements | Lines (est.) | Imports (new) | Depends on |
|---|---|---|---|---|---|
| 1 | `Matrix/Norms/Projector.lean` (registered; side file `Matrix/Norms/ProjectorFrobenius.lean` until proved) | 4 (L1 to L4) | +50 | none | none |
| 2 | `Sketching/Properties/MatrixMultiplication.lean` (registered; side file `Sketching/Properties/FrobeniusMoment.lean` until proved) | 3 (J1 to J3) | +80 | none | none |
| 3 | `Sketching/Properties/ProjectionCost.lean` (S2b's, extended) | 7 (C1 to C7) | +310 (to about 465) | `Sketching/Properties/Oblivious`, `Sketching/Properties/MatrixMultiplication`, `Matrix/Spectral/LowRank` | files 1, 2 |
| 4 | `Sketching/Gaussian/Gaussian.lean` (registered; side file `Sketching/Gaussian/GaussianProjectionCost.lean`) | 2 (G1, G2) | +70 | file 3 | file 3 |
| 5 | `Sketching/Gaussian/Rademacher.lean` (registered; side file as for 4) | 2 (R1, R2) | +60 | file 3 | file 3 |
| 6 | `Sketching/Gaussian/SubGaussian.lean` (registered; side file as for 4) | 2 (SG1, SG2) | +70 | file 3 | file 3 |
| 7 | `Sketching/Sparse/CountSketch.lean`, or its embedding half after the split (flag) | 2 (CS1, CS2) | +80 | file 3 | files 2, 3 |
| 8 | `LowRank/Oblivious/EarlyTruncation.lean` (S7's file; created by S9 if S9 comes first) | 2 (U1, U2) | +55 | file 3, `LowRank/Structural/EarlyTruncation` | file 3; S7 for U2 |

S9 is about 775 lines and 24 public declarations (one definition, 23 theorems). Every file stays
under about 1000 lines except file 7 (flag below). **Order:** files 1 and 2 are independent of each
other; file 3 after both; files 4 to 7 are independent of each other after file 3 and short, so one
proof agent may own two of them (CONTRIBUTING §11); file 8 last. Files 1, 2 and 3 can go to one agent
as a short import chain. Two agents are editing Sketching and LowRank files now: every registered
file of the table takes S9's statements only proved and only after its current owner has finished;
until then they sit in the side files named, each saying it merges into its home.

**Placement** (CONTRIBUTING §8 item 5): every declaration with its home and reason.
- L1 to L4, `Matrix/Norms/Projector.lean`: facts about a star projection and the Frobenius norm, beside
  `frobNorm_rangeProjector_sq` (of which L1 is the projector form) and
  `IsStarProjection.frobInner_mul_one_sub_mul` (of which L4 is the identity-free form). Not in
  `ProjectionCost.lean`: they mention no sketch, and S2b's `EarlyTruncation.lean` needs them too.
- J1 to J3, `Sketching/Properties/MatrixMultiplication.lean`: the statement is the trace of the
  approximate-multiplication error at $\mathbf{A} = \mathbf{B} = \mathbf{X}$,
  $\operatorname{tr}(\mathbf{X}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{X} -
  \mathbf{X}^{\mathsf{H}}\mathbf{X})$, a Gram-error moment of a sketched product, which is that file's
  topic; the alternative `JohnsonLindenstrauss.lean` is Q5.
- C1 to C7, `Sketching/Properties/ProjectionCost.lean`: the predicate and every general constructor
  (D12; the maintainer's instruction), whatever the sketch's law. C7 is real only and still belongs
  here: it is a constructor of the predicate from two Sketching predicates.
- G1, G2 in `Gaussian.lean`; R1, R2 in `Rademacher.lean`; SG1, SG2 in `SubGaussian.lean`; CS1, CS2 in
  CountSketch's file: "family X is a PCP at size Y", beside the family's OSE and JL results it
  instantiates.
- U1, U2, `LowRank/Oblivious/EarlyTruncation.lean`: consequences for an algorithm, taking a
  Sketching-round predicate and knowing nothing about the law (D12's `Oblivious/`, "the OSI and OSE
  routes"; brief §7 S9). Not `LowRank/Structural/`: they are tails. Not `LowRank/Random/`: that
  directory holds law-free integrability and measurability facts, not consequences of a sketch
  property.
- **Flags** (placed elsewhere until resolved):
  - File 7: `Sparse/CountSketch.lean` is 957 lines with about 30 statements; CS1 and CS2 take it past
    the budget. Proposed: split it at S9's wrap-up into `Sparse/CountSketch.lean` (the law, its
    moments, AMM) and `Sparse/CountSketchEmbedding.lean` (OSE, OSI, JL moment, sizes, PCP), the
    `Haar.lean` / `HaarEmbedding.lean` precedent; until the split, CS1 and CS2 sit in the side file
    `Sketching/Sparse/CountSketchProjectionCost.lean`, which says it merges into the embedding half.
    The split touches a file a current agent may be editing, so it waits for that agent.
  - `Gaussian.lean` already has 27 statements against the guideline of about 25; G1 and G2 make 29,
    at 865 lines. No split is proposed (the topic is one); recorded for the wrap-up.
  - The private lemmas of `LowRank/Structural/EarlyTruncation.lean` replaced by L2 to L4 are deleted
    at the wrap-up, after L1 to L4 are in their home and that file's current owner has finished.
  - If S9 is implemented before S7, file 8 is created by S9 with U1 only, in its final home; U2 waits
    for S7's completion tail. Not a misplacement.
  - ProjectionCost.lean's S2b statements get the binder rename `Ω` to `X` (§3): an edit to S2b's
    proved statements' binders, no API change.

## 5. Material

**Prototype** (read-only, `~/Documents/prove2me/lean/NLAlib/`): no projection-cost-preserving
sketches (S2b §5). Nothing to ledger.

**The maintainer's notes** (read-only material, never cited; D13):
- `gaussian-pcps.tex`: `def:pcp` (S2b's P1 with $\varepsilon$); `thm:mm` (Musco and Musco's four
  conditions (i) to (iv), two-sided (iv), offset $0$): C5, with the frame generalised and (iv)
  one-sided, CEMMP Lemma 6's form; `lem:se` (Davidson–Szarek): replaced by the library's Gaussian OSE;
  `lem:amm` (the exact Gaussian AMM second moment): not needed, since `hasJLMoment_of_hasLaw_gaussianMatrix`
  with S1's AMM gives the same $2/t$ (brief §9.3 lists it "if needed"); `lem:frob` (Laurent–Massart,
  $169\log(8/\delta)/\varepsilon^2$): not ported, J3 serves every family and its cost is dominated by
  the AMM term's $1/\delta$; `thm:PCPS` (sizes $\max\{49(\sqrt{k}+\sqrt{2\log(8/\delta)})^2/\varepsilon^2,
  288k/(\varepsilon^2\delta), 169\log(8/\delta)/\varepsilon^2\}$): G1's shape, other constants;
  `cor:lra`: S2b's T6 and U1.
- `~/Documents/Papers/PCPS/pcps-gaussian.tex`: the split at $p$ (the index with
  $\sigma_j^2 \ge \mathrm{OPT}^2/k$) and the $(k + \log(1/\delta))/\varepsilon^2$ Gaussian theorem
  through Borell–TIS, Davidson–Szarek, Laurent–Massart and concentration on a convex set: D1, deferred
  (heavy, and no literature source). Remark "A Chebyshev-only variant" confirms that second moments give
  $O(k/(\varepsilon^2\delta))$, S9's route; Remark "The JL-moment route cannot give
  $k + \log(1/\delta)$" is why the asymptotic thresholds carry $1/\delta$ and why Musco–Musco
  Corollary 7 is not cited.
- `pcps-audit.md`: item 3 (the uniform Gaussian PCPS, high probability only), item 2 (no expectation
  from a PCP: U1's docstring), item 12 (the rank-deficient case needs the embedding on the actual row
  space: C4, and C5's `hZA`).
- `PCPS.tex`, `pcps-direct.tex`: superseded by S2b's core (S2b §5); `pcps-expectation.tex`: S6b.

**Literature** (the checks above): CEMMP Definition 1, Lemmas 3, 5, 6, 10, 11, Theorems 7 to 9, 12, 14;
Woodruff 2014 Definition 12, Theorems 13, 14, 61; TYUC SIMAX §7.3.1.

**Citations** (keys exist: `CohenElderMuscoMuscoPersu2015`, `Woodruff2014`,
`TroppYurtseverUdellCevher2017`; no new key):

| statement | citation | relation to the printed statement |
|---|---|---|
| L2 | [CohenElderMuscoMuscoPersu2015, proof of Theorem 12] | there the Ky Fan sum of a symmetric error; here the inner product with a projector |
| L1, L3, L4 | none (helpers) | |
| J2, J3 | [Woodruff2014, proof of Theorem 13]; [CohenElderMuscoMuscoPersu2015, §7] | there the summation step inside AMM and a remark; here the trace, any field, any $p \ge 1$ |
| C1 | [CohenElderMuscoMuscoPersu2015, Theorem 12] | there "probability $1 - O(\delta)$", error $O(\varepsilon)$ |
| C3, C4 | [CohenElderMuscoMuscoPersu2015, §1.1]; [Woodruff2014, proof of Theorem 61] | as S2b's P3, on the event |
| C5, C6 | [CohenElderMuscoMuscoPersu2015, Lemma 6, proof of Theorem 12] | there $\mathbf{V}_k$, budgets summing to $\varepsilon$, real, the $\mathbf{C}^{+}$ semi-inner product; here any optimal frame, constants $a$, $b$, any field, Cauchy–Schwarz |
| C7 | [CohenElderMuscoMuscoPersu2015, proof of Theorem 12] | there $O(k\log(1/\delta)/\varepsilon^2)$, unspecified constants; here explicit, $p \ge 2$ |
| G1, G2 | [CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 1] | there sign matrices and $(k + \log(1/\delta))/\varepsilon^2$; here Gaussian, $1/\delta$, explicit |
| R1, R2 | the same | there the family itself, with $\log(1/\delta)$ |
| SG1, SG2 | the route of [CohenElderMuscoMuscoPersu2015, proof of Theorem 12] | the instance is not stated there |
| CS1, CS2 | [CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 2] | the same $k^2/(\varepsilon^2\delta)$; here any field, explicit |
| U1 | [CohenElderMuscoMuscoPersu2015, Lemma 3, §7.2] | the tail form at the early-truncated output |
| U2 | [TroppYurtseverUdellCevher2017, §7.3.1] | there a remark with unspecified constants; here explicit, $\delta + \delta' + 1/t$ |

No statement of S9 is new to the manuscript, so none says "proved without a literature source".

**Result ids** (checked against `NLAlib/` and `explore/results.toml`, which has no PCP entry; no
collision): `projection-cost-preserving-sketch` (C1, as S2b's P1), `pcp-sufficient-conditions` (C5 to
C7; new), `jl-moment-frobenius` (J2, J3; new), `gaussian-pcp`, `rademacher-pcp`, `subgaussian-pcp`,
`sparse-pcp` (new, named as the family OSE ids), `early-truncation-pcp-bound` (U1, U2; S2b's id for the
uniform route). L1 to L4, C2 to C4 carry none.

## 6. Cut, and why

- **D1, the $(k + \log(1/\delta))/\varepsilon^2$ head–tail constructor** (CEMMP Theorem 12 as stated,
  through Lemmas 10 and 11). Exactly what it needs: spectral-norm approximate multiplication
  $\|\mathbf{M}^{\mathsf{H}}\mathbf{S}^{\mathsf{H}}\mathbf{S}\mathbf{M} - \mathbf{M}^{\mathsf{H}}\mathbf{M}\|_2
  \le \varepsilon$ for $\mathbf{M}$ of stable rank at most $k$ with $\|\mathbf{M}\|_2 \le 1$, for the
  oblivious families ([CNW14], Cohen, Nelson and Woodruff 2016; not in hand and not the sampling
  spectral AMM of Sketching §6.1 item 3, which is matrix Bernstein for sampling), plus Lemma 10's
  reduction (a block matrix $\mathbf{B}$ of the head frame of width $2k$ and the scaled tail, the
  trace condition (18)). Cheaper partial routes, each also deferred: JL moments at
  $p \approx \log(1/\delta)$ (Sketching §6.1 item 5, "the JL moment at $p \ne 2$") give only the
  product $k\log(1/\delta)/\varepsilon^2$ through C7 unchanged; for Gaussians, the maintainer's split
  at $p$ with Borell–TIS and convex-set concentration (no literature source). C7 and C5 are the
  interfaces any of these plugs into; a later dominating Gaussian theorem supersedes G2 by rule 6
  (Q3). Size: 600 to 900 lines plus the AMM infrastructure.
- **D2, column sampling** (CEMMP §7.2, Theorem 14; ridge leverage scores, Cohen, Musco and Musco 2017).
  Needs: a sampling distribution from a frame and the tail (a definition, with its domination facts,
  $\|\mathbf{z}_i\|^2 \le 2k\,p_i$, $\|\mathbf{e}_i\|^2 \le 2\|\mathbf{E}\|_{\mathsf{F}}^2 p_i$), the
  Frobenius-preservation identity for a sampling sketch (each row of $\mathbf{S}\mathbf{M}$ is a scaled
  row of $\mathbf{M}$, so $\|\mathbf{S}\mathbf{M}\|_{\mathsf{F}}^2$ is the AMM of the row-norm vector,
  about 40 lines), and then C6 with the existing leverage-score embedding and sampling AMM gives
  $O(k\log k/\varepsilon^2 + k/(\varepsilon^2\delta))$ rows (about 300 lines). CEMMP's own route needs
  spectral AMM by sampling (Sketching §6.1 item 3, about 150 lines). Non-oblivious; no consumer this
  round. The row-space form (C3 with the existing sampling embedding of $\operatorname{range}\mathbf{A}^{\mathsf{H}}$)
  is available now.
- **D3, SRHT at dimension $O(k)$.** Needs an SRHT AMM tail (a row-norm flattening lemma for a general
  matrix under the randomized transform, then sampling AMM conditionally, about 150 lines) and room:
  `Structured/SRHT.lean` is 1002 lines and is split first. The row-space PCP (C4 with the SRHT OSE)
  is available now at $O(\operatorname{rank}\mathbf{A}\log)$.
- **D4, Haar.** The Haar JL moment exists; the Haar OSE has tails in $(t, s)$ but no sample-size form
  (Sketching §6.1 item 5, "Haar sizes"), so G1's shape cannot be stated without inverting it first.
  About 70 lines after that form exists. C7 applies to Haar now for a user who inverts the tail.
- **D5, law dependence and closedness** (`isClosed_setOf_isProjectionCostPreserving`,
  `HasLaw.hasProjectionCostPreserving_iff`): true and about 50 lines; no statement needs them.
  Additive.
- **D6, the deterministic SVD-sketch PCPs** (CEMMP Lemma 5, Theorems 7 to 9: $\llbracket\mathbf{A}\rrbracket_{\lceil k/\varepsilon\rceil}$
  and near-optimal projections are one-sided PCPs). Deterministic, about 200 lines, for
  `ProjectionCost.lean` in a later deterministic stage; no consumer this round.
- **Per-family early-truncation corollaries through a PCP** (G1 composed with U1, and so on): not
  deferred but cut. Under the same events (head constant $1 - \varepsilon_h$, budgets as in C5),
  S2b's structural bound gives about $1 + \varepsilon_h + \sqrt{k}\,\varepsilon_w + 2\varepsilon_\chi$
  to first order where the PCP route gives about
  $1 + 2\varepsilon_h + 2\sqrt{k}\,\varepsilon_w + 4\varepsilon_\chi + \varepsilon_{\mathrm{F}}$, and needs neither
  the upper head bound nor the Frobenius event; S7 states those per family, and S6b the Gaussian
  expectation. Rule 6.
- **A tail form of S2b's P4 for a random $\gamma$-optimal projector** (constrained low-rank
  approximation, $k$-means): two lines from C1 and `measureReal_mono` at the user's projector; no
  consumer. Additive.
- **A per-family tail form** in natural parameters: C7 applied to two closed-form tails already in
  each family's file (Q4). Additive.
- **An oblivious predicate**: Q1.

## 7. Questions and decisions

Hard-to-reverse items are marked **(hard)**. Under the round's approval rule the maintainer decides the
hard ones; the rest proceed as recommended and are recorded here.

**Q1. The tail predicate's shape (hard).** Options: (a) `HasProjectionCostPreserving S A k a b δ μ`
on the sketch $\mathbf{S}$ : `Ω → Matrix l n 𝕜`, event at $\mathbf{A}\mathbf{S}(\omega)^{\mathsf{H}}$,
sketch first like `HasSubspaceEmbedding S U a b δ μ`; (b) on the test matrix $\mathbf{X}$ :
`Ω → Matrix n l 𝕜`, event at $\mathbf{A}\mathbf{X}(\omega)$, data first like S2b's
`IsProjectionCostPreserving A Ã`; (c) on the random sketched matrix
$\tilde{\mathbf{A}}$ : `Ω → Matrix m l 𝕜`; (d) any of these plus an oblivious form
`∀ A : Matrix m n 𝕜, …` for a fixed `m`. Recommendation (a). A PCP is a property of the sketch, as an OSE
is: the family statements then conclude about the same term as their OSE
(`fun ω => (√(Fintype.card k : ℝ))⁻¹ • G ω`), C3 to C7 take Sketching hypotheses on $\mathbf{S}$ and
conclude on $\mathbf{S}$ with no `ᴴ`, and LowRank consumers write it on `fun ω => (X ω)ᴴ`, exactly as D2
writes `IsObliviousSubspaceInjection (fun ω => (X ω)ᴴ) …`. (b) puts a `conjTranspose_conjTranspose` in
every family statement or constructor; (c) costs `fun ω => A * (S ω)ᴴ` at every use and gains only
non-linear sketches, which no theorem has; (d) adds nothing a theorem argument does not (every
consumer has one $\mathbf{A}$), and a predicate quantifying over all row types is awkward. The name
follows `HasSubspaceEmbedding`; `δ` and `μ` last as there. Rework if changed: C1 to C7, every family
statement, U1, U2.

**Q2. The head–tail constructor's hypotheses (not hard).** Options: (a) as §3.3: any frame with
`frobNorm (A - A * Z * Zᴴ) ≤ frobNorm (A - truncatedSVD A k)`, three nonnegative budgets $\varepsilon_w$,
$\varepsilon_\chi$, $\varepsilon_{\mathrm{F}}$, one-sided Frobenius preservation, constants
$a - \sqrt{k}\varepsilon_w - 2\varepsilon_\chi$ and $b + \sqrt{k}\varepsilon_w + 2\varepsilon_\chi + \varepsilon_{\mathrm{F}}$;
(b) Musco–Musco's form, $\mathbf{Z} = \mathbf{V}_k$ by `A * Z * Zᴴ = truncatedSVD A k`, one $\varepsilon$
split in fixed proportions, two-sided (iv), offset $0$; (c) CEMMP Lemma 6 verbatim with
$\mathbf{E}_1, \dots, \mathbf{E}_4$ as hypotheses on $\tilde{\mathbf{C}}$. Recommendation (a): the
inequality covers wider frames (CEMMP Lemma 10's $2k$, $\mathbf{Z} = \mathbf{I}$, which recovers P3) and
S1's frame by `le_of_eq`; separate budgets are what the AMM tails produce (the tail–head budget carries
$\|\mathbf{Z}\|_{\mathsf{F}}$); the constants are the exact sum of the four budgets, CEMMP's
$\varepsilon_1 + \varepsilon_2 + \varepsilon_2' + \varepsilon_3 + \varepsilon_4$, not proof constants
in rule 2's sense; one-sided (iv) is weaker as a hypothesis and is what S2b's $\exists c$ was for. (c)
writes hypotheses on Gram matrices no consumer has. Rework if changed: C5, C6 and the proofs of C7 and
CS1; no family statement exposes it.

**Q3. $1/\delta$ in the thresholds, and the later $\log(1/\delta)$ (not hard).** The family asymptotic
forms state $C(d+1)/(\varepsilon^2\delta)$ (CountSketch $(d+1)^2$), which is what second moments prove
and is CEMMP's family-2 rate. The literature's dense rate $(k + \log(1/\delta))/\varepsilon^2$ waits for
D1. Options: (a) state them now; when a dominating Gaussian theorem arrives, the current asymptotic form
is reproved from it or deprecated by rule 6, and the explicit `_of_le_card` forms keep their names
(their hypotheses differ, rule 4); (b) state no asymptotic form until D1. Recommendation (a): rule 3
requires the asymptotic form of every sample-size result, and the $(d+1)$, not $d$, is forced by
$k = 0$ (§3.0).

**Q4. No per-family tail form (not hard).** CONTRIBUTING's "tails, not sample sizes" is met by C7 (the
tail) and by the family OSE and JL-moment tails, already in closed form in each file; a per-family tail
would be C7 applied to two lemmas, with constants such as
$(1 - (\sqrt{d}+t)/\sqrt{\lvert k\rvert})^2 - 3\sqrt{d}\,\varepsilon$. Recommendation: size forms and
asymptotic forms only; a tail form is additive if a user wants one. Alternative: four more statements,
about 80 lines.

**Q5. Homes of J1 to J3 and L1 to L4 (not hard).** J: `MatrixMultiplication.lean` (the trace of the
Gram error; the file's weighted-Jensen helper is a proof convenience, not the reason) or
`JohnsonLindenstrauss.lean` (the JL property for a matrix's columns in aggregate; it would need that
helper made public in a Probability home). Recommendation `MatrixMultiplication.lean`. L: promote to
`Matrix/Norms/Projector.lean` and delete S2b's privates, or keep private copies in both
`ProjectionCost.lean` and `EarlyTruncation.lean`, which `scripts/Duplicates.lean` reports.
Recommendation: promote. Rework: file moves.

**Q6. Family coverage and the early-truncation corollaries (not hard).** Recommendation: Gaussian,
Rademacher, sub-Gaussian and CountSketch now; Haar, SRHT and sampling deferred with their needs (§6, D2
to D4; each already has the row-space PCP through C3 or C4); the early-truncation corollaries at the
interface only (U1, U2), the per-family ones cut as dominated by S7's core route. Alternative: G1
composed with U1 per family (four statements and four asymptotic forms, about 150 lines), each a
corollary a user can write in three lines and each worse than its S7 twin.

**Q7. U2 and S7 (not hard; coordination).** U2 needs the random-subspace completion tail: for
$\mathbf{\Psi}$ independent of $\mathbf{X}$ with an OSI for dimension $k$,
$\mathbb{P}\bigl((1 + t/a')\|\mathbf{A} - \mathsf{earlyTruncatedRSVD}\|^2 <
\|\mathbf{A} - \mathsf{earlyTruncatedGN}\|^2\bigr) \le \delta' + 1/t$. It is S7's "early-truncated GN
through it" (brief §7 S7) and S7's core-route GN tail needs it too. Recommendation: S7's note states it
(its natural home is S7's `LowRank/Oblivious/EarlyTruncation.lean`, or `Sketching/Properties/Injection.lean`
if S7 states it for a general random subspace, beside
`IsObliviousSubspaceInjection.measure_not_isSubspaceInjection_le_of_indepFun`), and S9 implements U2
after it. If S9 is first, S9 ships U1 and leaves U2 here.

**Q8. Inline integers in the size forms (not hard).** The size forms' second hypothesis carries the
proof's integer ($768$, $384(16c^2 - 1)$), written inline as S6b's
`900 * (k : ℝ) ≤ ε ^ 2 * Fintype.card l` and CountSketch's Theorem 14 form; the head hypothesis uses
the family's named size with its value marker. Options: (a) inline; (b) a named size
`projectionCostAMMRows d ε δ` with nonnegativity, monotonicity and a comparison, registered.
Recommendation (a): the integer appears in four statements of one stage, its asymptotic forms hide it,
and an improvement changes the integer, not a name. (b) is additive if a fifth family repeats it.

**Q9. Corrections of record (information).**
- Brief D7 and §7 S9 ("the head–tail constructor … when CEMMP is in hand and spectral AMM exists"):
  CEMMP's short proof needs only Frobenius AMM (S2b Q9, confirmed term by term here). Spectral AMM is
  needed for the $\log(1/\delta)$ dependence (stable-rank AMM for oblivious sketches, [CNW14], which is
  not Sketching §6.1 item 3) and for column sampling (which is).
- Brief §5.4 ("`HasJLMoment` and `IsObliviousSubspaceEmbedding` supply the Frobenius parts for
  Gaussian, sub-Gaussian, Rademacher and CountSketch"): they supply the head and the AMM parts; the
  tail's Frobenius preservation is new (J1 to J3), and CountSketch goes through its own AMM, since
  JL-moment AMM is real only.
- Brief §7 S9 sizes (250 plus 400): about 775 (§0.2).
- CEMMP's "$O(k/\varepsilon^2)$" for families 1 to 3 is $O((k + \log(1/\delta))/\varepsilon^2)$
  through [CNW14]; their own short proof gives $O(k\log(1/\delta)/\varepsilon^2)$ (p. 16). S9's
  $O((k+1)/(\varepsilon^2\delta))$ is at constant $\delta$ the same $O(k/\varepsilon^2)$ and is
  documented as such.

## 8. Amendments from the review (2026-10-16)

Review of this note (eleven amendments: one high, A1; four medium, A2, A3, B4, C1; six low, A4,
A5, B5 to B8; besides them, verifications A6 and B1 to B3, information B10 and B11, the name B9,
the cut C2, the sequencing C3 and two verdicts), all eleven accepted by the orchestrator; none
rejected. Four points are corrected or extended on inspection: B4's named size takes the family's
JL constant as an argument, since without it the sub-Gaussian statement keeps an inline proof
constant, contrary to B4's own reason (item 4); the weighted-Jensen helper that A2 makes public is
a conjunction and is split by §5.2 (item 2); `Gaussian.lean` has 30 public declarations, not 27
(item 6); and the corrected cut counts 28 public declarations and about 720 lines, not 23 and 640,
because C2 leaves out the named size's three API lemmas and the two Tail statements, and its line
sum is short (item 13). The review found the mathematics sound: C5 rederived term by term with
exact constants, the §3.0 counterexamples, C7's budgets and the family arithmetic ($768$,
$384(16c^2 - 1)$, the absorption of the head size at $\delta \le 1/2$), J1 to J3 over any field,
the $(d+1)$ forced by $k = 0$, the reading of CEMMP Lemma 6 and Theorem 12, and every deferral
(B1 to B3, B11). Q1 is decided as (a), which the review found dominant, with the name fixed now
(item 7). Where an item below contradicts §0 to §7, it supersedes them; §3's signatures stand
except as amended here.

1. **A1, the head–tail split is promoted as L5** (§0.2 item 1, §3.1, §3.3 C5's route, §4
   placement). C5's identity $x = h + t$, $\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 =
   \|\mathbf{A}\mathbf{Z} - \mathbf{P}\mathbf{A}\mathbf{Z}\|_{\mathsf{F}}^2 + \|\mathbf{E} -
   \mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2$, is S2b's private `frobNorm_sub_mul_sq_eq_add`
   (`LowRank/Structural/EarlyTruncation.lean`, lines 121 to 137, checked); the draft used it in
   §3.3 without listing it, and `ProjectionCost.lean` cannot import a LowRank file. It goes to
   `Matrix/Norms/Projector.lean` beside `IsStarProjection.frobNorm_sq_eq_add`, of which it is the
   transpose at $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$, for any $\mathbf{P}$, in the
   `HasOrthonormalCols` namespace:
   ```lean
   /-- **The head–tail split of a projection residual** for a frame $\mathbf{Z}$ and any
   $\mathbf{P}$: with $\mathbf{E} = \mathbf{A} - \mathbf{A}\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$,
   $$\|\mathbf{A} - \mathbf{P}\mathbf{A}\|_{\mathsf{F}}^2 =
   \|\mathbf{A}\mathbf{Z} - \mathbf{P}\mathbf{A}\mathbf{Z}\|_{\mathsf{F}}^2 +
   \|\mathbf{E} - \mathbf{P}\mathbf{E}\|_{\mathsf{F}}^2\,;$$
   `IsStarProjection.frobNorm_sq_eq_add` at $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$, transposed. -/
   theorem HasOrthonormalCols.frobNorm_sub_mul_sq_eq_add {Z : Matrix n r 𝕜}
       (hZ : HasOrthonormalCols Z) (A : Matrix m n 𝕜) (P : Matrix m m 𝕜) :
       frobNorm (A - P * A) ^ 2 =
         frobNorm (A * Z - P * (A * Z)) ^ 2 + frobNorm (A - A * Z * Zᴴ - P * (A - A * Z * Zᴴ)) ^ 2
   ```
   Proof: S2b's, verbatim (`classical` inside, so no `DecidableEq` in the statement). No new
   import: `Projector.lean` imports `Matrix/Basic/OrthonormalBasis` (which brings
   `HasOrthonormalCols.isStarProjection_mul_conjTranspose`) and `Matrix/Norms/Compare`
   (`HasOrthonormalCols.frobNorm_mul_conjTranspose_right`). C5's route reads: $x = h + t$ by L5 at
   $\mathbf{Z}$ and $\mathbf{P}$; the head by the private
   `frobNorm_sq_le_and_le_of_isSubspaceEmbedding`; the tail by L3, L4 and L2. All four privates of
   S2b's file (`frobInner_sub_mul_sub_mul`,
   `frobNorm_sub_mul_sq_eq`, `frobInner_le_sqrt_mul`, `frobNorm_sub_mul_sq_eq_add`, lines 85 to
   137) are deleted at the wrap-up for L4, L3, L2 (with `le_abs_self`) and L5, once that file's
   owner has finished. Item 1 of §0.2 becomes five statements, about +65 and −50.
2. **A2 and Q5 decided: J1 to J3 go to `Sketching/Properties/JohnsonLindenstrauss.lean`**
   (§3.1, §4 file 2 and its placement line, Q5). By topic the statement is the JL moment property
   of $\mathbf{S}$ summed over the columns of $\mathbf{X}$, the matrix twin of
   `HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le`, and its names are that lemma's with
   `frobNorm_mul` for `norm_mulVec`; the draft's reason (a Gram-error trace) was about the proof's
   relation to AMM, which §8 item 5 of CONTRIBUTING excludes. The JL file's variables are already
   over `𝕜` with `S : Ω → Matrix k n 𝕜`, so J1 to J3 need no separate section: they form a
   subsection "Frobenius-norm preservation" after
   `HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le` and before "From the JL property to
   subspace embeddings", and join the module docstring's main
   results. Names and signatures as §3.1. J2's docstring keeps the AMM remark as a remark and names
   its vector twin. The weighted-Jensen helper becomes public in `Probability/Tail.lean` (a fact
   about real random variables, no NLAlib vocabulary; the JL file already imports it). On
   inspection the private `integral_rpow_sum_le` of `MatrixMultiplication.lean` returns
   `Integrable … ∧ ∫ … ≤ K`, and the two halves are used separately (J1 and the AMM integrability
   need the first, J2 and the AMM bound the second), so §5.2 splits it; the integrability needs no
   weights:
   ```lean
   /-- For $r \ge 1$ and nonnegative $Y_i$ with each $Y_i^r$ integrable, $(\sum_i Y_i)^r$ is
   integrable. -/
   theorem integrable_rpow_sum {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ} (hY0 : ∀ i ω, 0 ≤ Y i ω)
       {r : ℝ} (hr : 1 ≤ r) (hm : AEStronglyMeasurable (fun ω => (∑ i, Y i ω) ^ r) μ)
       (hint : ∀ i, Integrable (fun ω => Y i ω ^ r) μ) :
       Integrable (fun ω => (∑ i, Y i ω) ^ r) μ
   /-- **Weighted Jensen for a sum of nonnegative random variables**: for $r \ge 1$, if
   $\mathbb{E}[Y_i^r] \le w_i^r K$ for nonnegative weights $w_i$ summing to one, with $Y_i = 0$
   where $w_i = 0$, then $\mathbb{E}[(\sum_i Y_i)^r] \le K$. -/
   theorem integral_rpow_sum_le {ι : Type*} [Fintype ι] {Y : ι → Ω → ℝ}
       (hY0 : ∀ i ω, 0 ≤ Y i ω) {r : ℝ} (hr : 1 ≤ r)
       (hm : AEStronglyMeasurable (fun ω => (∑ i, Y i ω) ^ r) μ) {w : ι → ℝ} (hw0 : ∀ i, 0 ≤ w i)
       (hw1 : ∑ i, w i = 1) (hwY : ∀ i, w i = 0 → ∀ ω, Y i ω = 0)
       (hint : ∀ i, Integrable (fun ω => Y i ω ^ r) μ) {K : ℝ}
       (hK : ∀ i, ∫ ω, Y i ω ^ r ∂μ ≤ w i ^ r * K) :
       ∫ ω, (∑ i, Y i ω) ^ r ∂μ ≤ K
   ```
   Routes: the first by `Real.rpow_arith_mean_le_arith_mean_rpow` at the uniform weights
   ($(\sum_i Y_i)^r \le \lvert\iota\rvert^{r-1}\sum_i Y_i^r$), after a Mathlib search
   (`memLp_finset_sum` with `MemLp.integrable_norm_rpow'` may already give it; an exact overlap is
   a one-line proof citing it); the second is the private proof with the first for integrability.
   `Tail.lean` gains the import `Mathlib.Analysis.MeanInequalitiesPow`. The move is a pure pass
   (Sonnet) before J1 to J3 are written; `MatrixMultiplication.lean` loses about 45 lines and its
   private copy. Net: JL file +80 (to about 450 lines, 16 public declarations), `Tail.lean` +55 of
   which 45 moved (to about 275, 9), `MatrixMultiplication.lean` −45.
3. **A3, S9 creates no LowRank file; U1 and U2 are handed to S7** (§0.2 items 10, 11, §3.6, §4
   file 8 and its flag, Q6's interface clause, Q7). `LowRank/Oblivious/EarlyTruncation.lean` is
   S7's file, with S7's module docstring and topic (brief §7 S7: early truncation by OSE plus AMM,
   and early-truncated GN through it); U1 and U2 are the PCP-hypothesis twins of those two
   statements (rule 4) and belong beside them, and U2 cannot be proved before S7's completion tail
   anyway. The hand-off, for S7's note (`docs/design/LowRank-S7.md`, in design now):
   - *What moves.* U1
     `HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedRSVD_sq_gt_le` and U2
     `HasProjectionCostPreserving.measure_mul_frobNorm_sub_earlyTruncatedGeneralizedNystrom_sq_gt_le`,
     with the signatures, degenerate cases and proof routes of §3.6 (the review found them correct;
     §3.6 stays in this note only as S7's input), to `LowRank/Oblivious/EarlyTruncation.lean`,
     with S7's variables `{X : Ω → Matrix n l 𝕜} {Ψ : Ω → Matrix m p 𝕜}`.
   - *What S9 supplies.* C1 and the orientation lemma (item 7), in
     `Sketching/Properties/ProjectionCost.lean`, which S7's file imports. U1's proof becomes
     `hasProjectionCostPreserving_conjTranspose_iff`, then T6
     (`IsProjectionCostPreserving.mul_frobNorm_sub_earlyTruncatedRSVD_sq_le`) under
     `measureReal_mono`, with no double `conjTranspose`. U1 and U2 are implemented after S9's
     file 3 exists, whichever stage runs first; this is the only dependency of S7 on S9.
   - *What S7 provides.* The random-subspace completion tail of Q7, its statement and home (S7's
     file, or `Sketching/Properties/Injection.lean` if stated for a general random subspace); U2
     waits for it.
   - *Docstring changes S7 makes.* U1's sentence "With a family's constants $1 \mp \varepsilon$
     the factor is $(1+\varepsilon)/(1-\varepsilon)$" becomes the bound with the constants in
     place, "with constants $1 \mp \varepsilon$, $(1 - \varepsilon)\|\mathbf{A} -
     \mathsf{earlyTruncatedRSVD}(\mathbf{A}, \mathbf{\Omega}, k)\|_{\mathsf{F}}^2 \le
     (1 + \varepsilon)\|\mathbf{A} - \llbracket\mathbf{A}\rrbracket_k\|_{\mathsf{F}}^2$", with no
     factor named by a sentence; U1's pointer to the structural route names S7's tail form of
     `IsSubspaceInjection.frobNorm_sub_earlyTruncatedRSVD_sq_le`.
   - *What goes with them.* The result id `early-truncation-pcp-bound` (S2b's id for the uniform
     route) and the §5 citation rows of U1 ([CohenElderMuscoMuscoPersu2015, Lemma 3, §7.2]) and
     U2 ([TroppYurtseverUdellCevher2017, §7.3.1]). They are tails, not sample sizes, so rule 3
     asks no asymptotic form of them.
   - *For the orchestrator* (this note does not edit the brief): PORT_LOWRANK §7 needs a one-line
     amendment, S9's Content dropping "the uniform-PCP corollaries for early-truncated RSVD and GN"
     and its Files line dropping `LowRank/Oblivious/EarlyTruncation.lean (extended)`, S7's Content
     gaining them. D7's "the early-truncation corollaries through it" is met in S7.

   S9 then touches only Sketching and two lower-layer files. Q7 becomes internal to S7.
4. **B4 and Q8 decided: (b), one named size, with the family's JL constant as its argument**
   (§3.4, §3.5, Q8). Rule 2: $768$ and $384(16c^2 - 1)$ are proof constants (CEMMP has none), not
   a source's; S6b's inline 900 was the manuscript's own. On inspection the review's
   `projectionCostTailRows d ε δ := 768 (d+1)/(ε^2 δ)` covers G1 and CS1 but leaves SG1's
   $384(16c^2 - 1)$ inline, so a better budget split would still change SG1's statement. All three
   are $384\,v\,(d+1)/(\varepsilon^2\delta)$ with $v/(\lvert k\rvert\varepsilon_J^2)$ the family's
   failure at $p = 2$ (`hasJLMoment_of_hasLaw_gaussianMatrix` and CountSketch's JL moment and AMM
   tail: $v = 2$; `hasJLMoment_of_isSubgaussianVector`: $v = 16c^2 - 1$), since $3 \cdot
   v/(\lvert k\rvert\varepsilon_J^2) \le \delta/2$ at $\varepsilon_J = \varepsilon/(8\sqrt{d+1})$
   is $384\,v\,(d+1) \le \varepsilon^2\delta\lvert k\rvert$. So the size takes $v$ first, as
   `subgaussianEmbeddingDim c d ε δ` takes $c$, and each family passes its own JL constant. In
   `ProjectionCost.lean`, after C7:
   ```lean
   /-- The **tail rows of the head–tail constructor**, at
   present <!-- value projectionCostTailRows v d \varepsilon \delta -->
   $384 \cdot v (d + 1)/(\varepsilon^2 \delta)$: for a sketch whose JL moment at $p = 2$ has
   failure $v/(\lvert k \rvert \varepsilon_J^2)$ at every $\varepsilon_J > 0$ (for CountSketch, also
   its approximate-multiplication tail), at least this many rows make the three tail events of
   `NLAlib.HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasOrthonormalCols` fail with total
   probability at most $\delta/2$ at the budgets $\varepsilon_J = \varepsilon/(8\sqrt{d+1})$ of the
   family statements. The proof's value; [CohenElderMuscoMuscoPersu2015] has no constant.
   Consumers use `NLAlib.projectionCostTailRows_le`. Junk value: $0$ at $\varepsilon = 0$ or
   $\delta = 0$. -/
   noncomputable irreducible_def projectionCostTailRows (v : ℝ) (d : ℕ) (ε δ : ℝ) : ℝ :=
     384 * v * ((d : ℝ) + 1) / (ε ^ 2 * δ)
   theorem projectionCostTailRows_nonneg {v : ℝ} (hv : 0 ≤ v) (d : ℕ) (ε : ℝ) {δ : ℝ}
       (hδ : 0 ≤ δ) : 0 ≤ projectionCostTailRows v d ε δ
   theorem projectionCostTailRows_mono {v v' : ℝ} {d d' : ℕ} {ε ε' δ δ' : ℝ} (hv : 0 ≤ v)
       (hvv' : v ≤ v') (hd : d ≤ d') (hε : 0 < ε) (hεε' : ε ≤ ε') (hδ : 0 < δ) (hδδ' : δ ≤ δ') :
       projectionCostTailRows v d ε' δ' ≤ projectionCostTailRows v' d' ε δ
   /-- The explicit comparison: `NLAlib.projectionCostTailRows v d ε δ` is at
   most <!-- value projectionCostTailRows v d \varepsilon \delta -->
   $384 \cdot v (d + 1)/(\varepsilon^2 \delta)$, the value consumers invert with (at present an
   equality); an improved definition keeps it true. -/
   theorem projectionCostTailRows_le (v : ℝ) (d : ℕ) (ε δ : ℝ) :
       projectionCostTailRows v d ε δ ≤ 384 * v * ((d : ℝ) + 1) / (ε ^ 2 * δ)
   ```
   Registry entry, in the commit that defines it (`body_hash` by `--update`):
   ```toml
   [[constant]]
   name = "NLAlib.projectionCostTailRows"
   kind = "sample size"
   file = "NLAlib/Sketching/Properties/ProjectionCost.lean"
   args = ["v", "d", "ε", "δ"]
   latex = '384 \cdot #1 (#2 + 1)/(#3^2 #4)'
   display = '\frac{384 \cdot #1 (#2 + 1)}{#3^2 #4}'
   lean_body = 'projectionCostTailRows (v : ℝ) (d : ℕ) (ε δ : ℝ) : ℝ := 384 * v * ((d : ℝ) + 1) / (ε ^ 2 * δ)'
   ```
   The `\cdot` keeps the filled value readable at $v = 2$. The families' second size hypotheses
   become `projectionCostTailRows 2 d ε δ ≤ Fintype.card k` (G1, CS1) and
   `projectionCostTailRows (16 * (c : ℝ) ^ 2 - 1) d ε δ ≤ Fintype.card k` (SG1), each docstring
   with the marker and the filled value inline (item 11). Each family inverts with
   `projectionCostTailRows_le` and a few lines of arithmetic; no further public inversion lemma.
   Home: `ProjectionCost.lean`, the file of the constructor whose budget it inverts, imported by all
   three family files. Mathlib has nothing of the kind; not a deviation. About 25 lines.
5. **C1 and Q6 decided: the Rademacher pair is dropped** (§0.2 item 8, §3.4, §4 file 5, §5
   citation row R1, R2 and result id `rademacher-pcp`, Q6). SG2's threshold at $c = 1$ is R2's, so
   R2 is dominated by SG2 (rule 6); a Rademacher sketch meets SG1's hypotheses at $c = 1$ through
   `isSubgaussianVector_of_hasLaw_rademacherVector`, `isIsotropic_of_hasLaw_rademacherVector` and
   `HasLaw.iIndepFun_eval`, exactly as `Rademacher.lean` already uses them
   (`hasJLProperty_of_hasLaw_rademacherMatrix`, checked). Of record, on inspection: in the explicit
   form SG1 at $c = 1$ is weaker than the drafted R1 by constants (tail $384 \cdot 15$ against
   $768$, head `subgaussianEmbeddingDim 1 d` against the `jlDim` form), which is accepted, since
   the tail constants are loose either way and the asymptotic forms coincide. SG1's and SG2's
   docstrings say so (item 11). §6 gains: "*Rademacher PCP statements*: SG1 at $c = 1$, three
   lines; additive." `Rademacher.lean` is not touched. Kept: Gaussian (the round's primary law,
   matched to the maintainer's notes), sub-Gaussian (the general real family) and CountSketch (any
   field, CEMMP's family 2). Saves about 60 lines and two declarations.
6. **A4 and A5, the CountSketch split first, no side files; numbers of record** (§4 file 7, the
   flags, the order paragraph). `Sparse/CountSketch.lean` is 985 lines with 28 public declarations
   (the draft said 957). It is split before file 7 is written, as a pure move (Sonnet), at the
   existing boundary "The Gram error and the embedding" (line 684): `Sparse/CountSketch.lean` keeps
   the law, the integrals, the exact second moment and AMM (lines 1 to 683, about 690 lines with
   its header, 14 public declarations); the new `Sparse/CountSketchEmbedding.lean` takes the Gram
   error, OSE, OSI, JL moment and the sizes (lines 684 to 985, about 310 lines, 14 public
   declarations) and imports the first. The `Haar.lean` and `HaarEmbedding.lean` precedent. CS1
   and CS2 go directly into the embedding half; the side file
   `Sketching/Sparse/CountSketchProjectionCost.lean` is dropped. Likewise the other side files of
   §4 (`ProjectorFrobenius.lean`, `FrobeniusMoment.lean`, `GaussianProjectionCost.lean` and the
   rest): by §4's own order the current owners are finished when S9 reaches those files, so each
   registered file takes S9's statements proved, in place; a side file is opened only if an owner
   is still editing then, named in the note on the day as a dated amendment and flagged. Numbers
   of record: `Gaussian.lean` is 799 lines (the draft said 865) and has 30 public declarations
   (the draft said 27); with G1 and G2 it has 32 at about 870 lines, over the guideline of about
   25 statements. No split is proposed (the topic is one); recorded for the wrap-up, as the draft
   did. `SubGaussian.lean` is 734 lines with 22 public declarations, 24 after SG1, SG2.
7. **B5, B9 and Q1 decided: (a), the name fixed, and the orientation lemma** (§1 §5.3 row, §2
   API, §3.2, Q1). The tail predicate is `HasProjectionCostPreserving S A k a b δ μ` on the sketch,
   sketch first, as §3.2 drafts it. The name is fixed now, with the shape, because both are hard to
   reverse: it is the Is-to-Has form of S2b's proved `IsProjectionCostPreserving`, the library's
   pairing of a deterministic predicate with its tail form (`IsSubspaceEmbedding`,
   `HasSubspaceEmbedding`); a noun form (`HasProjectionCostPreservingSketch`) would break that
   pairing for grammar alone (B9 accepts the name on the same ground). The one cost of (a), a
   double `conjTranspose` in LowRank proofs, is removed by one lemma, in `ProjectionCost.lean`
   after C2:
   ```lean
   /-- A test matrix $\mathbf{\Omega}$ makes $\mathbf{\Omega}^{\mathsf{H}}$ a
   projection-cost-preserving sketch exactly when $\mathbf{A}\mathbf{\Omega}$ fails to be one with
   probability at most
   $\delta$: the form LowRank consumers rewrite with. -/
   theorem hasProjectionCostPreserving_conjTranspose_iff {X : Ω → Matrix n l 𝕜}
       {A : Matrix m n 𝕜} {k : ℕ} {a b δ : ℝ} :
       HasProjectionCostPreserving (fun ω => (X ω)ᴴ) A k a b δ μ ↔
         μ.real {ω | ¬ IsProjectionCostPreserving A (A * X ω) k a b} ≤ δ
   ```
   (one line: unfold and `Matrix.conjTranspose_conjTranspose`; about 8 lines with the docstring).
   §5.3 row, bridge column: `hasProjectionCostPreserving_conjTranspose_iff` (the LowRank
   orientation), beside the two constructors. Its consumers are S7's U1 and U2 (item 3). The
   maintainer confirms (a) and the name with the cut (item 13).
8. **B6, D5 is the first follow-up, with its proof sketch** (§2 "Not introduced", §6 D5). Not
   "no statement needs it": a consumer transporting a PCP along
   `hasLaw_conjTranspose_of_hasLaw_gaussianMatrix` or `hasLaw_conjTranspose_of_hasLaw_haarFrame`
   needs it, and every sibling predicate has the pair. Statements:
   `isClosed_setOf_isProjectionCostPreserving` (for fixed $\mathbf{A}$, $k$, $a$, $b$) and
   `HasLaw.hasProjectionCostPreserving_iff`. Sketch: with $L(\tilde{\mathbf{A}}) =
   \sup_{\mathbf{P}}(a\,\mathrm{cost}(\mathbf{P}) - \|\tilde{\mathbf{A}} -
   \mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2)$ and $U(\tilde{\mathbf{A}}) =
   \inf_{\mathbf{P}}(b\,\mathrm{cost}(\mathbf{P}) - \|\tilde{\mathbf{A}} -
   \mathbf{P}\tilde{\mathbf{A}}\|_{\mathsf{F}}^2)$ over the rank-$k$ projectors, an offset
   $c \ge 0$ exists exactly when $\max\{0, L\} \le U$; $L$ is a supremum of continuous functions
   (lower semicontinuous), $U$ an infimum of continuous functions (upper semicontinuous), so the
   set is closed; the law form follows as for `HasLaw.hasSubspaceEmbedding_iff`, the event being
   the preimage of a measurable set under `fun ω => A * (S ω)ᴴ`. About 50 lines; additive, first
   in line after S9.
9. **B7, proof-route notes** (§3.3, §3.4). C7 at $k > \lvert n\rvert$ takes $\mathbf{Z} =
   \mathbf{I}_n$ and needs `classical` for `DecidableEq n`. G1 derives `[Nonempty k]` (needed by
   `hasJLMoment_of_hasLaw_gaussianMatrix`) from its second size hypothesis by
   `Fintype.card_pos_iff`, since `projectionCostTailRows 2 d ε δ > 0` for $\varepsilon, \delta >
   0$. C6's strict events sit inside the AMM tails' non-strict ones and inside J3's absolute-value
   one, with the set equalities by `Matrix.conjTranspose_conjTranspose` and
   `frobNorm_conjTranspose` (`hw` and `hχ` are written with $\mathbf{E}$ on the left; the AMM tail
   produces $\mathbf{E}^{\mathsf{H}\mathsf{H}}$ there). Added on inspection: SG1 keeps
   `[Nonempty k]` (its second hypothesis is positive only once isotropy gives $c \ge 1$, which
   itself needs a row), and is stated without `[DecidableEq n]` (`omit … in`, `classical` in the
   proof), which `SubGaussian.lean`'s section variable would otherwise add.
10. **B8, C1's citation** (§3.2 C1, §5 citation row C1). C1's docstring cites
    [CohenElderMuscoMuscoPersu2015, Definition 1] for the predicate at each $\omega$ and
    [CohenElderMuscoMuscoPersu2015, Theorem 12] for the form "with probability at least
    $1 - O(\delta)$", there with error $O(\varepsilon)$.
11. **Asymptotic forms and their pairing** (§3.4, §3.5; CONTRIBUTING §5.2 rule 3 and §9's
    `check_refs.py`). Every sample-size result has its asymptotic form: G1 and G2, SG1 and SG2,
    CS1 and CS2 (C5 to C7 and J1 to J3 are not sample sizes). Each explicit docstring ends its
    prose with "Asymptotic form: `NLAlib.exists_forall_…`."; each asymptotic docstring names the
    explicit theorem in a sentence ("Proved from `NLAlib.…_of_le_card` with …"), then the line
    `Asymptotic: NLAlib.…_of_le_card` before `Result:`. G2's drafted "Proved from the size form
    with $C = 768$ … (its first hypothesis is at most $648(d+1)/(\varepsilon^2\delta)$ there)"
    named no theorem and is replaced. No docstring defines a constant by a sentence; values sit in
    the formulas with markers.
    - *G1*: `(hk₂ : projectionCostTailRows 2 d ε δ ≤ Fintype.card k)` for the inline `768`; the
      docstring's "at least $768(d+1)/(\varepsilon^2\delta)$ rows" becomes "at
      least <!-- value projectionCostTailRows 2 d \varepsilon \delta -->
      $384 \cdot 2 (d + 1)/(\varepsilon^2 \delta)$ rows (`projectionCostTailRows 2 d ε δ`)". Rest
      as §3.4.
    - *G2*: signature as §3.4. Docstring: "**$O((d+1)/(\varepsilon^2\delta))$ Gaussian rows
      suffice for a rank-$d$ projection-cost-preserving sketch** with constants
      $1 \mp \varepsilon$ and failure probability $\delta$, for $\varepsilon$ and $\delta$ below
      absolute constants; the constants come before every dimension. Proved from
      `NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card` with $C = 768$,
      $\varepsilon_0 = 1$ and $\delta \le 1/2$. [CohenElderMuscoMuscoPersu2015, Theorem 12].",
      then `Asymptotic: NLAlib.hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card`
      and `Result: gaussian-pcp`.
    - *SG1, SG2*, written out (`SubGaussian.lean`'s variables, `c : ℝ≥0`):
      ```lean
      /-- **A sub-Gaussian sketch is a projection-cost-preserving sketch**, size form: for a
      sketch $\mathbf{X}$ with independent isotropic rows, sub-Gaussian with proxy $c$, for
      $0 < \varepsilon \le 4c$, $\delta > 0$, at least (the OSE size form's marker and value at
      $(\varepsilon/2, \delta/2)$) rows and at
      least <!-- value projectionCostTailRows {(16c^2 - 1)} d \varepsilon \delta -->
      $384 \cdot (16c^2 - 1) (d + 1)/(\varepsilon^2 \delta)$ rows, $\mathbf{S} =
      \lvert k \rvert^{-1/2}\mathbf{X}$ makes $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ a rank-$d$
      projection-cost-preserving sketch of $\mathbf{A}$ with constants $1 \mp \varepsilon$, for
      every $\mathbf{A}$, except with probability $\delta$. A Rademacher sketch is the case
      $c = 1$ (`NLAlib.isSubgaussianVector_of_hasLaw_rademacherVector`,
      `NLAlib.isIsotropic_of_hasLaw_rademacherVector`, `ProbabilityTheory.HasLaw.iIndepFun_eval`),
      CEMMP's family 1. The route of [CohenElderMuscoMuscoPersu2015, proof of Theorem 12]; the
      sub-Gaussian instance is not stated there. Asymptotic form:
      `NLAlib.exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector`.
      Result: subgaussian-pcp -/
      theorem hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card [Nonempty k]
          (hind : iIndepFun (fun i ω => X ω i) μ)
          (hsub : ∀ i, IsSubgaussianVector (fun ω => X ω i) c μ)
          (hiso : ∀ i, IsIsotropic (fun ω => X ω i) μ) (A : Matrix m n ℝ) (d : ℕ) (hε : 0 < ε)
          (hεc : ε ≤ 4 * c) (hδ : 0 < δ)
          (hk₁ : subgaussianEmbeddingDim c d (ε / 2) (δ / 2) ≤ Fintype.card k)
          (hk₂ : projectionCostTailRows (16 * (c : ℝ) ^ 2 - 1) d ε δ ≤ Fintype.card k) :
          HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) A d (1 - ε)
            (1 + ε) δ μ
      /-- **$O(c^2 (d+1)/(\varepsilon^2\delta))$ rows suffice for a sub-Gaussian sketch** with
      independent isotropic rows, sub-Gaussian with proxy $c$, to be a rank-$d$
      projection-cost-preserving sketch with constants $1 \mp \varepsilon$ and failure
      probability $\delta$, for $\varepsilon$ and $\delta$ below absolute constants; the
      constants come before every dimension and the proxy. At $c = 1$ this covers Rademacher
      sketches. Proved from `NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card`
      with $\varepsilon_0 = 1$ and $\delta \le 1/2$; isotropy forces $c \ge 1$ once there is a
      column. [CohenElderMuscoMuscoPersu2015, proof of Theorem 12].
      Asymptotic: NLAlib.hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card
      Result: subgaussian-pcp -/
      theorem exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector :
          ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω k m n : Type} [MeasurableSpace Ω] [Fintype k]
            [Fintype m] [Fintype n] [Nonempty k] (μ : Measure Ω) (X : Ω → Matrix k n ℝ)
            (c : ℝ≥0) (A : Matrix m n ℝ) (d : ℕ) (ε δ : ℝ),
            iIndepFun (fun i ω => X ω i) μ → (∀ i, IsSubgaussianVector (fun ω => X ω i) c μ) →
            (∀ i, IsIsotropic (fun ω => X ω i) μ) → 0 < ε → ε ≤ ε₀ → 0 < δ → δ ≤ 1 / 2 →
            C * ((c : ℝ) ^ 2 * ((d : ℝ) + 1) / (ε ^ 2 * δ)) ≤ Fintype.card k →
            HasProjectionCostPreserving (fun ω => (√(Fintype.card k : ℝ))⁻¹ • X ω) A d (1 - ε)
              (1 + ε) δ μ
      ```
      SG2's docstring states its $C$ once the proof fixes it, as the OSE asymptotic form does.
    - *CS1, CS2*, written out (the embedding half's variables, over `𝕜`):
      ```lean
      /-- **A CountSketch is a projection-cost-preserving sketch**, size form, over any field:
      for $0 < \varepsilon \le 1$, $\delta > 0$, at
      least <!-- value countSketchRows d (\varepsilon/2) (\delta/2) -->
      $(d^2 + d)/((\delta/2) (\varepsilon/2)^2)$ rows (`countSketchRows d (ε / 2) (δ / 2)`) and at
      least <!-- value projectionCostTailRows 2 d \varepsilon \delta -->
      $384 \cdot 2 (d + 1)/(\varepsilon^2 \delta)$ rows (`projectionCostTailRows 2 d ε δ`),
      $\mathbf{A}\mathbf{S}^{\mathsf{H}}$ is a rank-$d$ projection-cost-preserving sketch of
      $\mathbf{A}$ with constants $1 \mp \varepsilon$, for every $\mathbf{A}$, except with
      probability $\delta$. [CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 2],
      $O(k^2/(\varepsilon^2\delta))$ there as here; here any field, explicit. Asymptotic form:
      `NLAlib.exists_forall_hasProjectionCostPreserving_of_hasLaw_countSketch`.
      Result: sparse-pcp -/
      theorem hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card
          (hS : HasLaw S (countSketch k n) μ) (A : Matrix m n 𝕜) (d : ℕ) (hε : 0 < ε)
          (hε1 : ε ≤ 1) (hδ : 0 < δ) (hk₁ : countSketchRows d (ε / 2) (δ / 2) ≤ Fintype.card k)
          (hk₂ : projectionCostTailRows 2 d ε δ ≤ Fintype.card k) :
          HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ
      /-- **$O((d+1)^2/(\varepsilon^2\delta))$ rows suffice for a CountSketch** to be a rank-$d$
      projection-cost-preserving sketch with constants $1 \mp \varepsilon$ and failure
      probability $\delta$, over any field, for $\varepsilon$ below an absolute constant; the
      constants come before every dimension. Proved from
      `NLAlib.hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card` with $C = 768$ and
      $\varepsilon_0 = 1$. [CohenElderMuscoMuscoPersu2015, Theorem 12, Lemma 11 family 2].
      Asymptotic: NLAlib.hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card
      Result: sparse-pcp -/
      theorem exists_forall_hasProjectionCostPreserving_of_hasLaw_countSketch :
          ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧ ∀ {Ω 𝕜 k m n : Type} [MeasurableSpace Ω] [RCLike 𝕜]
            [Fintype k] [Fintype m] [Fintype n] [DecidableEq k] (μ : Measure Ω)
            (S : Ω → Matrix k n 𝕜) (A : Matrix m n 𝕜) (d : ℕ) (ε δ : ℝ),
            HasLaw S (countSketch k n) μ → 0 < ε → ε ≤ ε₀ → 0 < δ →
            C * (((d : ℝ) + 1) ^ 2 / (ε ^ 2 * δ)) ≤ Fintype.card k →
            HasProjectionCostPreserving S A d (1 - ε) (1 + ε) δ μ
      ```
      CS2 needs no bound on $\delta$: the head is $8(d^2 + d)/(\varepsilon^2\delta) \le
      8(d+1)^2/(\varepsilon^2\delta)$ and the tail $768(d+1) \le 768(d+1)^2$.
12. **The other questions and the sequencing** (Q2 to Q9, C3). Q2, Q3 and Q4 stand as
    recommended. Q5 is decided by items 1 and 2; Q6 by items 3 and 5; Q7 is internal to S7
    (item 3); Q8 by item 4. Q9 adds: brief §5.4's "Rademacher" is met through the sub-Gaussian
    statements at $c = 1$; brief §7 S9's sizes are about 720 (item 13). §1's "Used directly" drops
    the Rademacher OSE and JL moment and reads `integral_rpow_sum_le` (public,
    `Probability/Tail.lean`) for the private helper. **Order** (C3, supersedes §4's paragraph): two
    Sonnet passes first, the
    CountSketch split (item 6) and the helper move (item 2); then files 1, 3 and 4 below
    (`Projector.lean`, `JohnsonLindenstrauss.lean`, `ProjectionCost.lean`) as one import chain to
    one proof agent; then files 5 to 7, independent and short, one agent possibly owning two
    (CONTRIBUTING §11). Each registered file takes its statements proved, in place, after its
    current owner has finished (item 6).
13. **The cut, the deferrals, and the files after the amendments** (supersedes §0.2's
    recommendation, the §4 table and its size paragraph; awaits the maintainer's go-ahead).
    **Cut (C2, the review's):** items 1 (five promotions), 2 to 7, 8 at Gaussian and sub-Gaussian
    only, and 9 of §0.2, plus the orientation lemma (item 7) and the named size (item 4). No LowRank
    file. The only new proof of substance is C5 (about 140 lines); J2, C6 and C7 are short; the
    families are inversions. The review's floor, if the maintainer wants less, is Gaussian and
    CountSketch only (CEMMP's families 1 and 2), dropping SG1, SG2 (about 75 lines, two
    declarations; the named size stays, for G1 and CS1); the review advises against it, since
    SG is the cheapest further item and covers Rademacher. C3 to C7 are not cut: they are the
    interface the deferred families plug into. **Deferrals, as §6 with what each needs:**
    - D1, $(k + \log(1/\delta))/\varepsilon^2$: stable-rank spectral AMM for oblivious sketches
      ([CNW14], not in hand) with CEMMP Lemma 10's reduction; or JL moments at
      $p \approx \log(1/\delta)$ for the weaker product form; 600 to 900 lines plus infrastructure.
    - D2, column sampling: a sampling distribution from a frame and the tail, the sampling
      Frobenius identity (about 40 lines), then C6 with the leverage-score embedding and sampling
      AMM (about 300); CEMMP's route needs spectral AMM by sampling (Sketching §6.1 item 3).
    - D3, SRHT at $O(k)$: an SRHT AMM tail (about 150 lines) and the split of `SRHT.lean`
      (1002 lines) first.
    - D4, Haar: a Haar OSE sample-size form (Sketching §6.1 item 5), then about 70 lines.
    - D5, law dependence and closedness: the first follow-up (item 8), about 50 lines.
    - D6, the deterministic SVD-sketch PCPs: a later deterministic stage, about 200 lines.
    - Rademacher: SG1 at $c = 1$ (item 5), additive. The per-family early-truncation corollaries,
      the per-family tail forms, the tail form of P4 and an oblivious predicate stay cut as §6
      and Q1 give them.

    | # | File | Statements | Lines (est.) | Imports (new) |
    |---|---|---|---|---|
    | 1 | `Matrix/Norms/Projector.lean` (registered) | 5 (L1 to L5) | +65, to about 350 | none |
    | 2 | `Probability/Tail.lean` (registered) | 2 (`integrable_rpow_sum`, `integral_rpow_sum_le`) | +55 (45 moved), to about 275 | `Mathlib.Analysis.MeanInequalitiesPow` |
    | 3 | `Sketching/Properties/JohnsonLindenstrauss.lean` (registered) | 3 (J1 to J3) | +80, to about 450 | none |
    | 4 | `Sketching/Properties/ProjectionCost.lean` (S2b's, extended) | 12 (C1, C2, the orientation lemma, C3 to C7, `projectionCostTailRows` and its three API lemmas) | +345, to about 500 | `Sketching/Properties/MatrixMultiplication`, `Matrix/Spectral/LowRank` |
    | 5 | `Sketching/Gaussian/Gaussian.lean` (registered) | 2 (G1, G2) | +70, to about 870 | file 4 |
    | 6 | `Sketching/Gaussian/SubGaussian.lean` (registered) | 2 (SG1, SG2) | +75, to about 810 | file 4 |
    | 7 | `Sketching/Sparse/CountSketchEmbedding.lean` (new by the split, item 6) | 2 (CS1, CS2) | +80, to about 390 | file 4 |

    Edits without new declarations: `MatrixMultiplication.lean` −45 (the helper moved);
    `LowRank/Structural/EarlyTruncation.lean` −50 at the wrap-up (item 1);
    `Sparse/CountSketch.lean` split (to about 690). **28 public declarations** (two definitions,
    `HasProjectionCostPreserving` and `projectionCostTailRows`; 26 theorems), by file 5, 2, 3, 12,
    2, 2, 2; **about 720 lines added**, about 670 net of the deleted privates, the 45 moved lines
    not counted. Against the review's 23 and 640: the review counts neither the named size's three
    API lemmas nor the two Tail statements, and its own subtraction gives about 710 (775 − 60 for
    Rademacher − 55 for U1, U2, + 15 for L5, + 25 for the size, + 8 for the orientation lemma),
    not 640; item 2's split adds about 10. Every file stays under 1000 lines; `Gaussian.lean` is
    over the statement guideline (item 6, flag for the wrap-up). One registry entry
    (`projectionCostTailRows`, item 4). Result ids: `projection-cost-preserving-sketch` (C1),
    `pcp-sufficient-conditions` (C5 to C7), `jl-moment-frobenius` (J2, J3), `gaussian-pcp`,
    `subgaussian-pcp`, `sparse-pcp`; `rademacher-pcp` is dropped and `early-truncation-pcp-bound`
    goes with U1, U2 to S7. Open flags at S9's report: `Gaussian.lean`'s statement count; the
    wrap-up deletion of S2b's four privates; any side file opened under item 6.
14. **Placement, every declaration** (CONTRIBUTING §8 item 5; supersedes §4's placement list).

    | Declaration | Home | Reason |
    |---|---|---|
    | L1 `IsStarProjection.frobNorm_sq_eq_rank` | `Matrix/Norms/Projector.lean` | the Frobenius norm of a star projection; the projector form of `frobNorm_rangeProjector_sq`, beside it |
    | L2 `IsStarProjection.abs_frobInner_le_sqrt_mul_frobNorm` | `Matrix/Norms/Projector.lean` | a star projection of rank $k$ against any matrix in the Frobenius inner product; follows L1 |
    | L3 `IsStarProjection.frobNorm_sub_mul_sq_eq_sub_frobInner` | `Matrix/Norms/Projector.lean` | the squared residual of a star projection; beside `IsStarProjection.frobNorm_sq_eq_add` |
    | L4 `IsStarProjection.frobInner_sub_mul_sub_mul` | `Matrix/Norms/Projector.lean` | the identity-free form of `IsStarProjection.frobInner_mul_one_sub_mul`, beside it |
    | L5 `HasOrthonormalCols.frobNorm_sub_mul_sq_eq_add` | `Matrix/Norms/Projector.lean` | `IsStarProjection.frobNorm_sq_eq_add` at $\mathbf{Z}\mathbf{Z}^{\mathsf{H}}$, transposed; beside it |
    | `integrable_rpow_sum` | `Probability/Tail.lean` | integrability of a power of a sum of real random variables; no matrix or sketch in it |
    | `integral_rpow_sum_le` | `Probability/Tail.lean` | weighted Jensen for moments of a sum of real random variables; used by the JL and AMM files |
    | J1 `HasJLMoment.integrable_abs_frobNorm_mul_sq_sub_rpow` | `Sketching/Properties/JohnsonLindenstrauss.lean` | the matrix twin of `HasJLMoment.integrable_abs_norm_mulVec_sq_sub_rpow`, beside it |
    | J2 `HasJLMoment.integral_abs_frobNorm_mul_sq_sub_rpow_le` | `Sketching/Properties/JohnsonLindenstrauss.lean` | the JL moment property summed over columns; twin of `HasJLMoment.integral_abs_norm_mulVec_sq_sub_rpow_le` |
    | J3 `HasJLMoment.measure_abs_frobNorm_mul_sq_sub_ge_le` | `Sketching/Properties/JohnsonLindenstrauss.lean` | its tail, beside the vector tails of the JL file |
    | C1 `HasProjectionCostPreserving` | `Sketching/Properties/ProjectionCost.lean` | the tail predicate beside S2b's deterministic one (D12) |
    | C2 `HasProjectionCostPreserving.mono` | `Sketching/Properties/ProjectionCost.lean` | API of C1 |
    | `hasProjectionCostPreserving_conjTranspose_iff` | `Sketching/Properties/ProjectionCost.lean` | API of C1, the test-matrix orientation LowRank consumers use |
    | C3 `HasSubspaceEmbedding.hasProjectionCostPreserving` | `Sketching/Properties/ProjectionCost.lean` | a constructor of C1 from a Sketching predicate, any law |
    | C4 `IsObliviousSubspaceEmbedding.hasProjectionCostPreserving` | `Sketching/Properties/ProjectionCost.lean` | the same, oblivious, at dimension $\operatorname{rank}\mathbf{A}$ |
    | C5 `IsSubspaceEmbedding.isProjectionCostPreserving_of_hasOrthonormalCols` | `Sketching/Properties/ProjectionCost.lean` | a deterministic constructor of S2b's predicate, beside P3 |
    | C6 `HasSubspaceEmbedding.hasProjectionCostPreserving_of_hasOrthonormalCols` | `Sketching/Properties/ProjectionCost.lean` | C5 on the event, the constructor for families with their own AMM tails |
    | C7 `IsObliviousSubspaceEmbedding.hasProjectionCostPreserving_of_hasJLMoment` | `Sketching/Properties/ProjectionCost.lean` | a constructor of C1 from two Sketching predicates; real only, still about C1 |
    | `projectionCostTailRows` | `Sketching/Properties/ProjectionCost.lean` | the inversion of C6's and C7's tail budget, shared by three family files that import this one |
    | `projectionCostTailRows_nonneg`, `_mono`, `_le` | `Sketching/Properties/ProjectionCost.lean` | its API (rule 2), beside it |
    | G1 `hasProjectionCostPreserving_of_hasLaw_gaussianMatrix_of_le_card` | `Sketching/Gaussian/Gaussian.lean` | "the Gaussian sketch is a PCP at this size", beside the Gaussian OSE and JL moment it instantiates |
    | G2 `exists_forall_hasProjectionCostPreserving_of_hasLaw_gaussianMatrix` | `Sketching/Gaussian/Gaussian.lean` | G1's asymptotic form, beside it |
    | SG1 `hasProjectionCostPreserving_of_isSubgaussianVector_of_le_card` | `Sketching/Gaussian/SubGaussian.lean` | the sub-Gaussian (and Rademacher) PCP, beside the sub-Gaussian OSE and JL moment |
    | SG2 `exists_forall_hasProjectionCostPreserving_of_isSubgaussianVector` | `Sketching/Gaussian/SubGaussian.lean` | SG1's asymptotic form, beside it |
    | CS1 `hasProjectionCostPreserving_of_hasLaw_countSketch_of_le_card` | `Sketching/Sparse/CountSketchEmbedding.lean` | the CountSketch PCP, beside the CountSketch OSE, JL moment and sizes |
    | CS2 `exists_forall_hasProjectionCostPreserving_of_hasLaw_countSketch` | `Sketching/Sparse/CountSketchEmbedding.lean` | CS1's asymptotic form, beside it |

    Not placed by S9: U1 and U2 (S7's `LowRank/Oblivious/EarlyTruncation.lean`, item 3).

## 9. Implementation amendments (2026-10-16)

Recorded when they happened, by the implementing agent; §8 stands otherwise.

1. **The CountSketch split** (§8 item 6) is done as a pure move at "The Gram error and the
   embedding": `Sparse/CountSketch.lean` (669 lines, 14 public declarations: the law, the hollow
   Gram identity, isotropy, the exact second moment, AMM) and the new
   `Sparse/CountSketchEmbedding.lean` (the Gram error, OSE, OSI, JL moment, the sizes, and now
   CS1, CS2; 16 public declarations), which imports the first. Names are unchanged; the first file
   lost the imports only the second half used (`Matrix/Subspaces/Leverage`,
   `Sketching/Properties/JohnsonLindenstrauss`, `Oblivious`, `TraceMoment`). The registry entry of
   `countSketchRows` names the new file. `NLAlib.lean` is not regenerated here (orchestrator).
2. **Statement changes against §8.** L5 takes `[DecidableEq p]` on the frame's column type
   (`HasOrthonormalCols` needs it; the S2b private had it as a section variable). SG1 and SG2 keep
   `[DecidableEq n]` (item 9 is wrong there: `IsIsotropic` needs it), SG2 among its quantifiers as
   the sub-Gaussian OSE asymptotic form has it. G1 assumes $\varepsilon \le 2$, not $\le 1$ (the
   Gaussian OSE size form at $\varepsilon/2$ needs only that); CS1 has no upper bound on
   $\varepsilon$ (none is used). SG2's constant is $C = 9216$. The family statements take the row
   type of $\mathbf{A}$ as an implicit binder `{m : Type*} [Fintype m]` (the family files have no
   `m` variable).
3. **Privates replaced now, not at the wrap-up.** `LowRank/Structural/EarlyTruncation.lean` uses
   L2 to L5 and its four privates are deleted (the brief asked for L5; the other three would
   otherwise be reported by `scripts/Duplicates.lean`). `MatrixMultiplication.lean` uses the
   public `integrable_rpow_sum` and `integral_rpow_sum_le` and its private copy is deleted.
   `Probability/Tail.lean` imports `Mathlib.Analysis.MeanInequalities` as well
   (`Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg` gives `integrable_rpow_sum` in one step).
4. **Inversions.** The explicit family forms unfold `projectionCostTailRows_def` (they derive the
   failure bound from the rows, as `countSketchRows` does in its own file); the asymptotic forms
   use `projectionCostTailRows_le` only. No side file was opened.
